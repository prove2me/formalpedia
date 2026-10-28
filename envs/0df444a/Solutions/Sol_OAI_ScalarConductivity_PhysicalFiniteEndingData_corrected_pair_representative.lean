-- Prove2me | solution 1 for OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_pair_representative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:04:56.784062+00:00
-- url     : https://prove2.me/submissions/a0d3474c-47cf-42d5-811f-fc73ff99a56d

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C006
import Definitions.Def_OAIQ059C007
import Theorems.Thm_OAI_ScalarConductivity_PhysicalFiniteEndingData_endRepresentative_regular

section
-- module Solutions.OAIQ059_CD.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_KernelParamDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory
open scoped Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E]

theorem convolution_param_hasDerivAt [FiniteDimensional ℝ E]
    [Measure.IsAddHaarMeasure (volume : Measure E)] {f : E → ℝ} (hf : LocallyIntegrable f)
    {K : ℝ → E → ℝ} {S : Set ℝ} {C : Set E} (hS : IsOpen S) (hC : IsCompact C)
    (hK : ContDiffOn ℝ 1 (Function.uncurry K) (S ×ˢ univ))
    (hzero : ∀ s y, s∈S → y∉C → K s y=0)
    {s : ℝ} (hs : s∈S) {D : E → ℝ} (hD : ∀ y, HasDerivAt (fun r => K r y) (D y) s)
    (x : E) :
    HasDerivAt (fun r => (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] K r) x)
      ((f ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] D) x) s := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let J : E → (ℝ × E →L[ℝ] ℝ) := fun y => fderiv ℝ (Function.uncurry K) (s,y)
  have hJ : Continuous J := by
    apply (hK.continuousOn_fderiv_of_isOpen (hS.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro y
    exact ⟨hs,mem_univ _⟩
  have hJzero {y : E} (hy : y∉C) : J y=0 := by
    apply (hasFDerivAt_zero_of_eventually_const 0 ?_).fderiv
    have he : S ×ˢ Cᶜ ∈ 𝓝 (s,y) :=
      (hS.prod hC.isClosed.isOpen_compl).mem_nhds ⟨hs,hy⟩
    filter_upwards [he] with z hz
    exact hzero z.1 z.2 hz.1 hz.2
  have hJc : HasCompactSupport J :=
    HasCompactSupport.of_support_subset_isCompact hC (by
      intro y hy
      by_contra hn
      exact hy (hJzero hn))
  have hi : Integrable (fun y => L.precompR (ℝ × E) (f y) (J (x-y))) :=
    hJc.convolutionExists_right (L.precompR (ℝ × E)) hf hJ x
  have hdiff := hasFDerivAt_convolution_right_with_param L hS hC hzero hf hK (s,x) hs
  have hcurve := ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have hout := hdiff.comp_hasDerivAt s hcurve
  have hJval (y : E) : J y (1,0)=D y := by
    have ha : DifferentiableAt ℝ (Function.uncurry K) (s,y) := (hK.contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hs,mem_univ y⟩)).differentiableAt (by norm_num)
    have he := ha.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
    exact (he.unique (hD y))
  convert hout using 1 <;> try rfl
  change (∫ y, f y*D (x-y))=(∫ y, L.precompR (ℝ × E) (f y) (J (x-y))) (1,0)
  rw [ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by simp [L,hJval])
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RadialLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open InnerProductSpace Laplacian
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radial_fderiv {f g : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (g t) t) (x : E) :
    fderiv ℝ (fun y : E => f (‖y‖^2)) x = (2*g (‖x‖^2)) • innerSL ℝ x := by
  have h := (hf (‖x‖^2)).comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  apply h.fderiv.trans
  ext v
  simp [two_smul,smul_eq_mul,innerSL_apply_apply]
  ring

lemma radial_second {f g h : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y : E => f (‖y‖^2))) x v w =
      4*h (‖x‖^2)*⟪x,v⟫*⟪x,w⟫ + 2*g (‖x‖^2)*⟪v,w⟫ := by
  have he : fderiv ℝ (fun y : E => f (‖y‖^2)) =
      (fun y : E => (2*g (‖y‖^2)) • innerSL ℝ y) := funext (radial_fderiv hf)
  rw [he]
  have hd := (((hg (‖x‖^2)).comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul 2).smul
      ((innerSL ℝ (E := E)).hasFDerivAt (x := x))
  have he' := congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T v w) hd.fderiv
  dsimp only [Pi.smul_apply,Function.comp_apply] at he'
  apply he'.trans
  simp [two_smul,smul_eq_mul,innerSL]
  ring

lemma radial_laplacian [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {f g h : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (x : E) :
    Δ (fun y : E => f (‖y‖^2)) x =
      4*‖x‖^2*h (‖x‖^2) + 2*(Fintype.card ι : ℝ)*g (‖x‖^2) := by
  have hl : Δ (fun y : E => f (‖y‖^2)) x =
      ∑ i, fderiv ℝ (fderiv ℝ (fun y : E => f (‖y‖^2))) x (b i) (b i) := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    apply Finset.sum_congr rfl
    intro i hi
    exact (bilinearIteratedFDerivTwo_eq_iteratedFDeriv (𝕜 := ℝ) _ x (b i) (b i)).symm
  rw [hl]
  simp_rw [radial_second hf hg]
  have hi : ∑ i, ⟪x,b i⟫*⟪x,b i⟫ = ‖x‖^2 := by
    simpa only [real_inner_comm (b _) x,real_inner_self_eq_norm_sq] using b.sum_inner_mul_inner x x
  calc
    _ = 4*h (‖x‖^2)*(∑ i, ⟪x,b i⟫*⟪x,b i⟫) +
        ∑ i, 2*g (‖x‖^2)*⟪b i,b i⟫ := by
      rw [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 4*‖x‖^2*h (‖x‖^2)+2*(Fintype.card ι : ℝ)*g (‖x‖^2) := by
      rw [hi]
      simp only [real_inner_self_eq_norm_sq,b.norm_eq_one,one_pow,mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

end

section
open MeasureTheory Set InnerProductSpace Laplacian
open scoped RealInnerProductSpace

lemma hasDerivAt_radialEta {χ χ' : ℝ → ℝ} (hχ : ∀ t, HasDerivAt χ (χ' t) t)
    {s : ℝ} (hs : s≠0) (x : WeylSpace) :
    HasDerivAt (fun r => radialEta χ r x)
      (-(3*χ (‖x‖^2/s^2)/s^4+2*‖x‖^2*χ' (‖x‖^2/s^2)/s^6)) s := by
  have hd := ((hχ _).comp s ((hasDerivAt_const s (‖x‖^2)).div ((hasDerivAt_id s).pow 2) (pow_ne_zero _ hs))).div
    ((hasDerivAt_id s).pow 3) (pow_ne_zero _ hs)
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try dsimp [radialEta,Function.comp_def]
  all_goals try rfl
  all_goals try field_simp [hs]
  all_goals ring

lemma radialTheta_laplacian {χ χ' Ψ : ℝ → ℝ}
    (hΨ : ∀ t, HasDerivAt Ψ (-χ t) t) (hχ : ∀ t, HasDerivAt χ (χ' t) t)
    {s : ℝ} (hs : s≠0) (x : WeylSpace) :
    Δ (radialTheta Ψ s) x = -(3*χ (‖x‖^2/s^2)/s^4+2*‖x‖^2*χ' (‖x‖^2/s^2)/s^6) := by
  have hf (t : ℝ) : HasDerivAt (fun z => Ψ (z/s^2)/(2*s^2))
      (-χ (t/s^2)/(2*s^4)) t := by
    convert ((hΨ _).comp t ((hasDerivAt_id t).div_const (s^2))).div_const (2*s^2) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try dsimp [Function.comp_def]
    all_goals try field_simp [hs]
  have hg (t : ℝ) : HasDerivAt (fun z => -χ (z/s^2)/(2*s^4))
      (-χ' (t/s^2)/(2*s^6)) t := by
    convert (((hχ _).comp t ((hasDerivAt_id t).div_const (s^2))).neg).div_const (2*s^4) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try dsimp [Function.comp_def]
    all_goals try field_simp [hs]
  have hh := radial_laplacian (EuclideanSpace.basisFun (Fin 3) ℝ) hf hg x
  apply hh.trans
  simp only [Fintype.card_fin,Nat.cast_ofNat]
  field_simp [hs]
  ring

theorem radial_scale_laplacian {χ χ' Ψ : ℝ → ℝ}
    (hΨ : ∀ t, HasDerivAt Ψ (-χ t) t) (hχ : ∀ t, HasDerivAt χ (χ' t) t)
    {s : ℝ} (hs : s≠0) (x : WeylSpace) :
    HasDerivAt (fun r => radialEta χ r x) (Δ (radialTheta Ψ s) x) s := by
  rw [radialTheta_laplacian hΨ hχ hs]
  exact hasDerivAt_radialEta hχ hs x

end

open Set MeasureTheory Filter Topology InnerProductSpace Laplacian
open scoped RealInnerProductSpace

lemma normsq_smooth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : E => ‖x‖^2) := by
  simpa only [id_eq,real_inner_self_eq_norm_sq] using (contDiff_id.inner ℝ contDiff_id :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : E => ⟪x,x⟫))

lemma radialRaw_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) radialRaw :=
  radialOneBump.contDiff.comp normsq_smooth

lemma radialOneBump_zero {t : ℝ} (ht : 1≤t) : radialOneBump t=0 := by
  apply Function.notMem_support.mp
  rw [radialOneBump.support_eq]
  change ¬dist t 0<1
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by linarith)]
  exact not_lt.mpr ht

lemma radialRaw_zero {x : WeylSpace} (hx : 1≤‖x‖) : radialRaw x=0 := by
  apply radialOneBump_zero
  nlinarith [norm_nonneg x]

lemma radialRaw_compact : HasCompactSupport radialRaw := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:WeylSpace) 1)
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (radialRaw_zero hn.le))

lemma radialRaw_zero_value : radialRaw 0=1 := by
  apply radialOneBump.one_of_mem_closedBall
  norm_num [radialOneBump]

lemma radialRaw_nonneg (x : WeylSpace) : 0 ≤ radialRaw x := radialOneBump.nonneg

lemma radialMass_pos : 0 < radialMass := by
  apply (integral_pos_iff_support_of_nonneg radialRaw_nonneg
    (radialRaw_smooth.continuous.integrable_of_hasCompactSupport radialRaw_compact)).2
  exact radialRaw_smooth.continuous.isOpen_support.measure_pos volume
    ⟨0,by rw [Function.mem_support,radialRaw_zero_value]; norm_num⟩

lemma radialProfile_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) radialProfile :=
  radialOneBump.contDiff.div_const _

lemma radialProfile_nonneg (t : ℝ) : 0 ≤ radialProfile t :=
  div_nonneg radialOneBump.nonneg radialMass_pos.le

lemma radialProfile_zero {t : ℝ} (ht : 1≤t) : radialProfile t=0 := by
  simp [radialProfile,radialOneBump_zero ht]

lemma radialProfilePrimitive_deriv (t : ℝ) :
    HasDerivAt radialProfilePrimitive (-radialProfile t) t :=
  intervalIntegral.integral_hasDerivAt_left (radialProfile_smooth.continuous.intervalIntegrable _ _)
    (radialProfile_smooth.continuous.stronglyMeasurableAtFilter _ _) radialProfile_smooth.continuous.continuousAt

lemma radialProfilePrimitive_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) radialProfilePrimitive := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (radialProfilePrimitive_deriv t).differentiableAt,?_⟩
  have he : deriv radialProfilePrimitive = -radialProfile :=
    funext (fun t => (radialProfilePrimitive_deriv t).deriv)
  rw [he]
  exact radialProfile_smooth.neg

lemma radialProfilePrimitive_zero {t : ℝ} (ht : 1≤t) : radialProfilePrimitive t=0 := by
  change (∫ r in t..1, radialProfile r)=0
  rw [←intervalIntegral.integral_zero (a := t) (b := 1) (μ := volume)]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_ge ht] at hr
  exact radialProfile_zero hr.1

lemma radialEta_smooth (s : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (radialEta radialProfile s) :=
  (radialProfile_smooth.comp (normsq_smooth.div_const _)).div_const _

lemma radialTheta_smooth (s : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (radialTheta radialProfilePrimitive s) :=
  (radialProfilePrimitive_smooth.comp (normsq_smooth.div_const _)).div_const _

lemma radialEta_zero {s : ℝ} (hs : 0 < s) {x : WeylSpace} (hx : s≤‖x‖) :
    radialEta radialProfile s x=0 := by
  have h : 1≤‖x‖^2/s^2 := (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by nlinarith [norm_nonneg x])
  simp [radialEta,radialProfile_zero h]

lemma radialTheta_zero {s : ℝ} (hs : 0 < s) {x : WeylSpace} (hx : s≤‖x‖) :
    radialTheta radialProfilePrimitive s x=0 := by
  have h : 1≤‖x‖^2/s^2 := (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by nlinarith [norm_nonneg x])
  simp [radialTheta,radialProfilePrimitive_zero h]

lemma radialEta_compact {s : ℝ} (hs : 0 < s) : HasCompactSupport (radialEta radialProfile s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:WeylSpace) s)
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (radialEta_zero hs hn.le))

lemma radialTheta_compact {s : ℝ} (hs : 0 < s) : HasCompactSupport (radialTheta radialProfilePrimitive s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:WeylSpace) s)
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (radialTheta_zero hs hn.le))

lemma radialEta_nonneg {s : ℝ} (hs : 0 < s) (x : WeylSpace) :
    0 ≤ radialEta radialProfile s x := div_nonneg (radialProfile_nonneg _) (by positivity)

lemma radialEta_integral {s : ℝ} (hs : 0 < s) : (∫ x, radialEta radialProfile s x)=1 := by
  have he : radialEta radialProfile s = fun x => (radialRaw (s⁻¹ • x)/radialMass)/s^3 := by
    ext x
    simp [radialEta,radialProfile,radialRaw,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_eq_mul_inv,mul_comm]
  rw [he,integral_div,integral_div,Measure.integral_comp_smul volume]
  simp only [WeylSpace, finrank_euclideanSpace, Fintype.card_fin,inv_pow,inv_inv,smul_eq_mul]
  rw [abs_of_pos (pow_pos hs 3)]
  change (s^3*radialMass)/radialMass/s^3=1
  field_simp [radialMass_pos.ne',hs.ne']

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RadialWeylScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set Filter Topology MeasureTheory Laplacian InnerProductSpace
open scoped Convolution

lemma radialEta_joint_smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞))
    (Function.uncurry (radialEta radialProfile)) (Ioi 0 ×ˢ univ) := by
  apply ContDiffOn.div
  · exact radialProfile_smooth.comp_contDiffOn
      ((normsq_smooth.comp contDiff_snd).contDiffOn.div
        (contDiff_fst.pow 2).contDiffOn (fun p hp => pow_ne_zero _ (ne_of_gt hp.1)))
  · exact (contDiff_fst.pow 3).contDiffOn
  · intro p hp
    exact pow_ne_zero _ (ne_of_gt hp.1)

lemma laplacian_sub_right (f : WeylSpace → ℝ) (a y : WeylSpace) :
    Δ (fun z => f (z-a)) y=Δ f (y-a) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_comp_sub]

lemma radialTheta_laplacian_sub_left (s : ℝ) (x y : WeylSpace) :
    Δ (fun z => radialTheta radialProfilePrimitive s (x-z)) y=
      Δ (radialTheta radialProfilePrimitive s) (x-y) := by
  have he : (fun z => radialTheta radialProfilePrimitive s (x-z))=
      (fun z => radialTheta radialProfilePrimitive s (z-x)) := by
    ext z
    simp only [radialTheta,norm_sub_rev]
  rw [he,laplacian_sub_right]
  by_cases hs : s=0
  · subst s
    have hz : radialTheta radialProfilePrimitive 0=(fun _ : WeylSpace => (0:ℝ)) := by
      ext z
      simp [radialTheta]
    rw [hz]
    simp only [laplacian_const,Pi.zero_apply]
  · rw [radialTheta_laplacian radialProfilePrimitive_deriv
      (fun t => (radialProfile_smooth.differentiable (by simp) t).hasDerivAt) hs,
      radialTheta_laplacian radialProfilePrimitive_deriv
      (fun t => (radialProfile_smooth.differentiable (by simp) t).hasDerivAt) hs]
    simp only [norm_sub_rev]

lemma radialMollify_smooth {f : WeylSpace → ℝ} (hf : LocallyIntegrable f)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ (↑(⊤ : ℕ∞)) (radialMollify f s) :=
  (radialEta_compact hs).contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hf (radialEta_smooth s)

lemma radialMollify_hasDerivAt {f : WeylSpace → ℝ} (hf : LocallyIntegrable f)
    {s : ℝ} (hs : 0 < s) (x : WeylSpace) :
    HasDerivAt (fun r => radialMollify f r x)
      (∫ y, f y*Δ (radialTheta radialProfilePrimitive s) (x-y)) s := by
  apply convolution_param_hasDerivAt hf isOpen_Ioo (isCompact_closedBall (0:WeylSpace) (2*s))
    (S := Ioo (s/2) (2*s))
  · apply (radialEta_joint_smooth.of_le (by simp)).mono
    rintro ⟨r,y⟩ ⟨⟨hr₁,hr₂⟩,_⟩
    exact ⟨(half_pos hs).trans hr₁,mem_univ _⟩
  · intro r y hr hy
    apply radialEta_zero (by linarith [hr.1])
    have hn : 2*s<‖y‖ := by simpa [Metric.mem_closedBall,dist_zero_right] using hy
    exact hr.2.le.trans hn.le
  · constructor <;> linarith
  · intro y
    exact radial_scale_laplacian radialProfilePrimitive_deriv
      (fun t => (radialProfile_smooth.differentiable (by simp) t).hasDerivAt) hs.ne' y

lemma radialMollify_hasDerivAt_zero {f : WeylSpace → ℝ} (hf : LocallyIntegrable f)
    {U : Set WeylSpace} (hw : WeaklyHarmonicOn f U)
    {s : ℝ} (hs : 0 < s) {x : WeylSpace} (hx : Metric.closedBall x s⊆U) :
    HasDerivAt (fun r => radialMollify f r x) 0 s := by
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => radialTheta radialProfilePrimitive s (x-y)) :=
    (radialTheta_smooth s).comp (contDiff_const.sub contDiff_id)
  have hc : HasCompactSupport (fun y => radialTheta radialProfilePrimitive s (x-y)) :=
    (radialTheta_compact hs).comp_homeomorph (Homeomorph.subLeft x)
  have hv : tsupport (fun y => radialTheta radialProfilePrimitive s (x-y))⊆Metric.closedBall x s := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    rw [Metric.mem_closedBall,dist_eq_norm]
    by_contra hn
    exact hy (radialTheta_zero hs (by simpa only [norm_sub_rev] using (not_le.mp hn).le))
  have he := hw _ hψ hc (hv.trans hx)
  simp_rw [radialTheta_laplacian_sub_left] at he
  simpa only [he] using radialMollify_hasDerivAt hf hs x

theorem radialMollify_scale_independent {f : WeylSpace → ℝ} (hf : LocallyIntegrable f)
    {U : Set WeylSpace} (hw : WeaklyHarmonicOn f U) {x : WeylSpace}
    {R : ℝ} (hR : Metric.closedBall x R⊆U) {s t : ℝ}
    (hs : 0 < s ∧ s<R) (ht : 0<t ∧ t<R) : radialMollify f s x=radialMollify f t x := by
  have hd (r : ℝ) (hr : r∈Ioo 0 R) : HasDerivAt (fun a => radialMollify f a x) 0 r :=
    radialMollify_hasDerivAt_zero hf hw hr.1
      ((Metric.closedBall_subset_closedBall hr.2.le).trans hR)
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0:ℝ) R).isPreconnected
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs ht

end

open Set MeasureTheory

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_L2TranslationAverage
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

open Set MeasureTheory Filter Topology
open scoped Convolution

lemma radialProbability_probability {s : ℝ} (hs : 0 < s) : IsProbabilityMeasure (radialProbability s) where
  measure_univ := by
    rw [radialProbability,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ←ofReal_integral_eq_lintegral_ofReal
        ((radialEta_smooth s).continuous.integrable_of_hasCompactSupport (radialEta_compact hs))
        (ae_of_all _ (radialEta_nonneg hs)),radialEta_integral hs]
    simp

lemma radialProbability_integral {s : ℝ} (hs : 0 < s) (f : WeylSpace → ℝ) :
    (∫ y, f y ∂radialProbability s)=∫ y, radialEta radialProfile s y*f y := by
  rw [radialProbability,integral_withDensity_eq_integral_toReal_smul
    (radialEta_smooth s).continuous.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (radialEta_nonneg hs _),smul_eq_mul]

lemma radialProbability_ball {s : ℝ} (hs : 0 < s) :
    ∀ᵐ y ∂radialProbability s, ‖y‖ < s := by
  rw [radialProbability,ae_withDensity_iff (radialEta_smooth s).continuous.measurable.ennreal_ofReal]
  filter_upwards with y hy
  by_contra hn
  have he := radialEta_zero hs (not_lt.mp hn)
  exact hy (by rw [he]; simp)

lemma radialMollify_eq_average {s : ℝ} (hs : 0 < s) (f : WeylSpace → ℝ) (x : WeylSpace) :
    radialMollify f s x=∫ y, f (x-y) ∂radialProbability s := by
  rw [radialProbability_integral hs,radialMollify,convolution_eq_swap]
  congr 1
  ext y
  simp [mul_comm]

lemma radialMollify_sub {s : ℝ} (hs : 0 < s) (f : WholeL2) (x : WeylSpace) :
    radialMollify f s x-f x=∫ y, (f (x-y)-f x) ∂radialProbability s := by
  rw [radialProbability_integral hs]
  simp_rw [mul_sub]
  have hi : Integrable (fun y => radialEta radialProfile s y*f (x-y)) :=
    (radialEta_compact hs).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (radialEta_smooth s).continuous ((Lp.memLp f).locallyIntegrable (by norm_num)) x
  rw [integral_sub hi (((radialEta_smooth s).continuous.integrable_of_hasCompactSupport
    (radialEta_compact hs)).mul_const _),integral_mul_const,radialEta_integral hs,one_mul]
  rw [radialMollify_eq_average hs,radialProbability_integral hs]

lemma radialMollify_memLp {s : ℝ} (hs : 0 < s) (f : WholeL2) :
    MemLp (radialMollify f s) 2 volume := by
  let := radialProbability_probability hs
  obtain ⟨hm,_⟩ := memLp_probability_average (whole_translation_memLp (μ := radialProbability s) f)
  exact MemLp.ae_eq (ae_of_all _ (fun x => (radialMollify_eq_average hs f x).symm)) hm

theorem radialMollify_approx (f : WholeL2) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ s : ℝ, 0 < s → s≤δ →
      (∫ x, (radialMollify f s x-f x)^2) ≤ ε := by
  obtain ⟨δ,hδ,hd⟩ := small_translation_radius f hε
  refine ⟨δ,hδ,fun s hs hsd => ?_⟩
  let := radialProbability_probability hs
  obtain ⟨_,he⟩ := translation_average_sq_le (μ := radialProbability s) f
    (show ∀ᵐ y ∂radialProbability s, ‖translateL2 y f-f‖^2≤ε from by
      filter_upwards [radialProbability_ball hs] with y hy
      exact (hd y (hy.trans_le hsd)).le)
  simpa only [radialMollify_sub hs] using he

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactDepthReductionTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma TwoFieldRankRegular.mono {u : Coord3 → Fin 2 → ℝ} {O W : Set Coord3}
    (h : TwoFieldRankRegular u O) (hW : W ⊆ O) : TwoFieldRankRegular u W := by
  rcases h with h | h | ⟨κ, hκ⟩
  · exact Or.inl (fun x hx => h x (hW hx))
  · obtain ⟨v, l, κ, hv, hl, hd, he⟩ := h
    exact Or.inr (Or.inl ⟨v, l, κ, hv.mono hW, hl, fun x hx => hd x (hW hx),
      fun x hx => he x (hW hx)⟩)
  · exact Or.inr (Or.inr ⟨κ, fun x hx => hκ x (hW hx)⟩)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPatch
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma TwoFieldRankRegular.congr {u v : Coord3 → Fin 2 → ℝ} {O : Set Coord3}
    (hO : IsOpen O) (h : TwoFieldRankRegular u O) (he : EqOn v u O) :
    TwoFieldRankRegular v O := by
  rcases h with h | h | ⟨κ,hκ⟩
  · left
    intro x hx
    rw [fderiv_eq_of_eqOn_open hO he hx]
    exact h x hx
  · right; left
    obtain ⟨w,l,κ,hw,hl,hwd,hrel⟩ := h
    exact ⟨w,l,κ,hw,hl,hwd,fun x hx j => by rw [he hx]; exact hrel x hx j⟩
  · exact Or.inr (Or.inr ⟨κ,fun x hx => (he hx).trans (hκ x hx)⟩)

lemma RegularPatch.mono {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {O W : Set Coord3} (h : RegularPatch u A O) (hW : IsOpen W) (hWO : W ⊆ O) :
    RegularPatch u A W :=
  ⟨hW,h.2.1.mono hWO,h.2.2.1.mono hWO,h.2.2.2.mono hWO⟩

lemma RegularPatch.congr {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    {O : Set Coord3} (h : RegularPatch u A O) (hu : EqOn v u O) (hA : EqOn B A O) :
    RegularPatch v B O := by
  exact ⟨h.1,h.2.1.congr hu,h.2.2.1.congr (fun x hx => congrArg Subtype.val (hA hx)),
    h.2.2.2.congr h.1 hu⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPatchTranslation
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma mem_regularRegion_congr_nhds {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    {V U : Set Coord3} {x : Coord3} (h : x∈regularRegion u A V)
    (hu : v =ᶠ[𝓝 x] u) (hA : B =ᶠ[𝓝 x] A) (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion v B U := by
  obtain ⟨O,hOV,hO,hxO⟩ := mem_regularRegion_iff.mp h
  have hh : {y | y∈O ∧ y∈U ∧ v y=u y ∧ B y=A y}∈𝓝 x := by
    filter_upwards [hO.1.mem_nhds hxO,hU.mem_nhds hx,hu,hA] with y hy0 hyU hyu hyA
    exact ⟨hy0,hyU,hyu,hyA⟩
  obtain ⟨W,hWsub,hW,hxW⟩ := mem_nhds_iff.mp hh
  refine mem_regularRegion_iff.mpr ⟨W,fun y hy => (hWsub hy).2.1,?_,hxW⟩
  exact (hO.mono hW (fun y hy => (hWsub hy).1)).congr
    (fun y hy => (hWsub hy).2.2.1) (fun y hy => (hWsub hy).2.2.2)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFaceUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma squareFace_interior_unique (i k : Fin 4) {a b : ℝ} (ha : |a|<1)
    (he : squareFace i a=squareFace k b) : i=k := by
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have ha₁ := (abs_lt.mp ha).1
  have ha₂ := (abs_lt.mp ha).2
  fin_cases i <;> fin_cases k <;>
    simp [squareFace,squareFaceBase,squareFaceDirection] at h0 h1 ⊢ <;> linarith

lemma sourceCollarPiece_open_unique (i j k l : Fin 4) {x z : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox)
    (hz : z∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (he : sourceCollarPiece i j x=sourceCollarPiece k l z) : i=k ∧ j=l := by
  obtain ⟨hzt,hza,hzb⟩ := mem_sourceExtendedBox.mp hz
  have hx' := sourceCollarOpenBox_subset hx
  obtain ⟨hxt,hxa,hxb⟩ := mem_sourceExtendedBox.mp hx'
  have hxR : 0 < sourceCollarRadius j (x 0) (x 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended j hxt hxb).1
  have hzR : 0 < sourceCollarRadius l (z 0) (z 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended l hzt hzb).1
  have hR : sourceCollarRadius j (x 0) (x 2)=sourceCollarRadius l (z 0) (z 2) := by
    have hh := congrArg sourceRadial he
    rwa [sourceCollarPiece_radial_pos i j hxR.le hxa,
      sourceCollarPiece_radial_pos k l hzR.le hza] at hh
  have ht : x 0=z 0 := by
    have hh := congrArg sourceCollarTime he
    rwa [sourceCollarPiece_time_pos i j hxR.le (by linarith [hxt.2]) hxa hxb,
      sourceCollarPiece_time_pos k l hzR.le (by linarith [hzt.2]) hza hzb] at hh
  constructor
  · apply squareFace_interior_unique i k hx.2.1
    have hh := congrArg (fun y : Fin 3 → ℝ => ![y 0/sourceLength,y 1]) he
    rw [sourceCollarPiece_angular,sourceCollarPiece_angular,←hR] at hh
    exact smul_right_injective (Fin 2 → ℝ) hxR.ne' hh
  · apply squareFace_interior_unique j l hx.2.2
    have hh := congrArg sourceCrossCoordinates he
    rw [sourceCollarPiece_cross_pos i j hxR.le hxa,
      sourceCollarPiece_cross_pos k l hzR.le hza,←ht] at hh
    exact smul_right_injective (Fin 2 → ℝ) (by linarith [hxt.2] : 1-x 0≠0) hh

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTestEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceExtendedBox_open_ae {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x∈sourceCollarOpenBox := by
  let B := sourceExtendedBox (-(1:ℝ)/100) (1/100)
  have hB : volume (frontier B)=0 := (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier B := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc),
    ae_restrict_of_ae hn] with x hx hn
  have hxB : x∈B := by
    obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp hx
    exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,hi,hj⟩
  rw [sourceCollarOpenBox_eq_interior]
  by_contra h
  exact hn ⟨subset_closure hxB,h⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullWeakEndEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceCollarClosedPiece_measurable (l r : ℝ) (i j : Fin 4) :
    MeasurableSet (sourceCollarPiece i j '' sourceExtendedBox l r) :=
  (isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous).measurableSet

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullEndClosedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceExtendedBox_interior_axial {l r : ℝ} {x : Fin 3 → ℝ}
    (hx : x∈interior (sourceExtendedBox l r)) : x 0∈Ioo l r := by
  have hbox : sourceExtendedBox l r=
      (univ : Set (Fin 3)).pi (fun k => Icc (![l,-1,-1] k) (![r,1,1] k)) := by
    ext x
    simp only [sourceExtendedBox,mem_Icc,Set.mem_pi,mem_univ,true_implies,Pi.le_def]
    simp only [forall_and]
  rw [hbox,interior_pi_set (finite_univ)] at hx
  have ht := hx 0 (mem_univ 0)
  simpa only [interior_Icc,Matrix.cons_val_zero] using ht

lemma sourceExtendedBox_axial_strict_ae (l r : ℝ) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x 0∈Ioo l r := by
  have hB : volume (frontier (sourceExtendedBox l r))=0 :=
    (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier (sourceExtendedBox l r) := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_of_ae hn,
    ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc)] with x hx hm
  apply sourceExtendedBox_interior_axial
  by_contra hi
  exact hx ⟨subset_closure hm,hi⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WeakWeyl
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma closedBall_near_subset {a x : WeylSpace} {R : ℝ} (hR : 0<R)
    (hx : x∈Metric.ball a (R/4)) : Metric.closedBall x (R/2)⊆Metric.closedBall a R := by
  intro y hy
  rw [Metric.mem_closedBall] at hy ⊢
  have hxa : dist x a<R/4 := hx
  exact (dist_triangle y x a).trans (by linarith)

theorem weakWeyl_local {f : WholeL2} {U : Set WeylSpace}
    (hw : WeaklyHarmonicOn f U) {a : WeylSpace} {R : ℝ} (hR : 0<R)
    (hball : Metric.closedBall a R⊆U) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (radialMollify f (R/4)) ∧
    (f : WeylSpace → ℝ) =ᵐ[volume.restrict (Metric.ball a (R/4))] radialMollify f (R/4) := by
  have hf : LocallyIntegrable (f : WeylSpace → ℝ) := (Lp.memLp f).locallyIntegrable (by norm_num)
  have hs : 0<R/4 := by linarith
  refine ⟨radialMollify_smooth hf hs,?_⟩
  let V := Metric.ball a (R/4)
  let g := radialMollify f (R/4)
  have he (r : ℝ) (hr : 0 < r ∧ r<R/2) (x : WeylSpace) (hx : x∈V) :
      g x=radialMollify f r x :=
    radialMollify_scale_independent hf hw ((closedBall_near_subset hR hx).trans hball)
      ⟨hs,by linarith⟩ hr
  have hi : Integrable (fun x => (g x-f x)^2) :=
    ((radialMollify_memLp hs f).sub (Lp.memLp f)).integrable_sq
  have hbound (ε : ℝ) (hε : 0<ε) : (∫ x in V, (g x-f x)^2)≤ε := by
    obtain ⟨δ,hδ,hd⟩ := radialMollify_approx f hε
    let r := min δ (R/4)/2
    have hr : 0 < r := by dsimp [r]; positivity
    have hrδ : r≤δ := by dsimp [r]; have := min_le_left δ (R/4); linarith [lt_min hδ hs]
    have hrR : r<R/2 := by dsimp [r]; have := min_le_right δ (R/4); linarith
    have heq : (∫ x in V, (g x-f x)^2)=∫ x in V, (radialMollify f r x-f x)^2 := by
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro x hx
      change (g x-f x)^2=(radialMollify f r x-f x)^2
      rw [he r ⟨hr,hrR⟩ x hx]
    rw [heq]
    exact (setIntegral_le_integral ((radialMollify_memLp hr f).sub (Lp.memLp f)).integrable_sq
      (ae_of_all _ (fun x => sq_nonneg _))).trans (hd r hr hrδ)
  have hz : (∫ x in V, (g x-f x)^2)=0 := by
    apply le_antisymm _ (integral_nonneg (fun x => sq_nonneg _))
    by_contra hn
    have hp : 0<(∫ x in V, (g x-f x)^2) := lt_of_not_ge hn
    have hh := hbound ((∫ x in V, (g x-f x)^2)/2) (by linarith)
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun x => sq_nonneg (g x-f x)))
    hi.restrict).mp hz
  filter_upwards [hae] with x hx
  exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hx)).symm

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped Convolution

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F]

lemma radialAverageF_fderiv {f : WeylSpace → F} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) {s : ℝ} (_ : 0 < s) (x : WeylSpace) :
    fderiv ℝ (radialAverageF f s) x=radialAverageF (fderiv ℝ f) s x := by
  have hd := hc.hasFDerivAt_convolution_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    (radialEta_smooth s).continuous.locallyIntegrable (hf.of_le (by simp)) x
  unfold radialAverageF
  rw [hd.fderiv]
  congr 1

lemma RadialMeanOn.derivative {f : WeylSpace → F} {a : WeylSpace} {R : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) : RadialMeanOn (fderiv ℝ f) a R := by
  intro s hs x hx
  have he : f =ᶠ[𝓝 x] radialAverageF f s := by
    have ho : IsOpen {y : WeylSpace | dist y a+s<R} := isOpen_lt (by fun_prop) continuous_const
    filter_upwards [ho.mem_nhds hx] with y hy
    exact hm s hs y hy
  rw [he.fderiv_eq,radialAverageF_fderiv hf hc hs]

lemma RadialMeanOn.derivative_bound {f : WeylSpace → F} {a x : WeylSpace} {R s M : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hs : 0 < s) (hx : dist x a+s<R) (_ : 0≤M)
    (hb : ∀ y∈Metric.closedBall x s, ‖f y‖≤M) :
    ‖fderiv ℝ f x‖≤M*(∫ y, ‖fderiv ℝ (radialEta radialProfile s) y‖) := by
  have he : f =ᶠ[𝓝 x] radialAverageF f s := by
    have ho : IsOpen {y : WeylSpace | dist y a+s<R} := isOpen_lt (by fun_prop) continuous_const
    filter_upwards [ho.mem_nhds hx] with y hy
    exact hm s hs y hy
  have hd := (radialEta_compact hs).hasFDerivAt_convolution_left (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ) ((radialEta_smooth s).of_le (by simp))
    hf.continuous.locallyIntegrable x
  rw [he.fderiv_eq]
  unfold radialAverageF
  rw [hd.fderiv]
  let L : (WeylSpace →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] (WeylSpace →L[ℝ] F) := (ContinuousLinearMap.lsmul ℝ ℝ).precompL WeylSpace
  have hi := ((radialEta_compact hs).fderiv ℝ).convolutionExists_left (μ := volume) L
    ((radialEta_smooth s).continuous_fderiv (by simp)) hf.continuous.locallyIntegrable x
  have hn : Integrable (fun y => M*‖fderiv ℝ (radialEta radialProfile s) y‖) :=
    (((radialEta_smooth s).continuous_fderiv (by simp)).integrable_of_hasCompactSupport
      ((radialEta_compact hs).fderiv ℝ)).norm.const_mul M
  calc
    _ ≤ ∫ y, ‖L (fderiv ℝ (radialEta radialProfile s) y) (f (x-y))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, M*‖fderiv ℝ (radialEta radialProfile s) y‖ := by
      apply integral_mono_ae hi.norm hn
      filter_upwards with y
      by_cases hy : ‖y‖ ≤ s
      · have hb' : ‖f (x-y)‖≤M := hb _ (by simpa [Metric.mem_closedBall,dist_eq_norm] using hy)
        change ‖(fderiv ℝ (radialEta radialProfile s) y).smulRight (f (x-y))‖ ≤ _
        rw [ContinuousLinearMap.norm_smulRight_apply]
        exact (mul_le_mul_of_nonneg_left hb' (norm_nonneg _)).trans_eq (mul_comm _ _)
      · have hz : fderiv ℝ (radialEta radialProfile s) y=0 := by
          apply Function.notMem_support.mp
          intro hd
          have ht := support_fderiv_subset ℝ hd
          revert ht
          intro ht
          have hsub : tsupport (radialEta radialProfile s)⊆Metric.closedBall (0:WeylSpace) s := by
            apply closure_minimal _ Metric.isClosed_closedBall
            intro z hz
            rw [Metric.mem_closedBall,dist_zero_right]
            exact le_of_not_gt (fun hh => hz (radialEta_zero hs hh.le))
          exact hy (by simpa [Metric.mem_closedBall,dist_zero_right] using hsub ht)
        simp [hz,L]
    _ = M*(∫ y, ‖fderiv ℝ (radialEta radialProfile s) y‖) := integral_const_mul _ _

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WeakHarmonicMean
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace
open scoped Convolution

lemma WeaklyHarmonicOn.congr_ae {f g : WeylSpace → ℝ} {U : Set WeylSpace}
    (he : f =ᵐ[volume] g) (hf : WeaklyHarmonicOn f U) : WeaklyHarmonicOn g U := by
  intro ψ hψ hc hs
  rw [←hf ψ hψ hc hs]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

lemma laplacian_zero_off_support {ψ : WeylSpace → ℝ} {x : WeylSpace}
    (hx : x∉tsupport ψ) : Δ ψ x=0 := by
  have he : ψ =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [(laplacian_congr_nhds he).eq_of_nhds]
  simp

lemma WeaklyHarmonicOn.congr_restrict {f g : WeylSpace → ℝ} {U : Set WeylSpace}
    (hU : MeasurableSet U) (he : f =ᵐ[volume.restrict U] g)
    (hf : WeaklyHarmonicOn f U) : WeaklyHarmonicOn g U := by
  intro ψ hψ hc hs
  rw [←hf ψ hψ hc hs]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU).mp he] with x hx
  by_cases h : x∈U
  · rw [hx h]
  · have he : Δ ψ x=0 := laplacian_zero_off_support (fun hy => h (hs hy))
    simp [he]

lemma weaklyHarmonic_smooth_mean {f : WeylSpace → ℝ} {a : WeylSpace} {R : ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hc : HasCompactSupport f)
    (hw : WeaklyHarmonicOn f (Metric.ball a R)) : RadialMeanOn f a (R/4) := by
  have hm : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hc
  let fl : WholeL2 := hm.toLp f
  have hw' : WeaklyHarmonicOn fl (Metric.ball a R) := .congr_ae hm.coeFn_toLp.symm hw
  intro s hs x hx
  have hball : Metric.closedBall x (4*s)⊆Metric.ball a R := by
    intro y hy
    have hy' : dist y x ≤ 4*s := hy
    have hd := dist_triangle y x a
    change dist y a<R
    have hx' : 0≤dist x a := dist_nonneg
    linarith
  obtain ⟨hsm,he⟩ := weakWeyl_local hw' (by positivity : 0<4*s) hball
  have hcvg : radialMollify fl s=radialMollify f s :=
    convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) hm.coeFn_toLp Filter.EventuallyEq.rfl
  have he' : f =ᵐ[volume.restrict (Metric.ball x s)] radialMollify f s := by
    have hh : f =ᵐ[volume.restrict (Metric.ball x (4*s/4))] fl :=
      ae_restrict_of_ae hm.coeFn_toLp.symm
    have h := hh.trans he
    have hs4 : 4*s/4=s := by ring
    simpa only [hs4,hcvg] using h
  have hp := Measure.eqOn_open_of_ae_eq he' Metric.isOpen_ball hf.continuous.continuousOn
    (radialMollify_smooth hf.continuous.locallyIntegrable hs).continuous.continuousOn (Metric.mem_ball_self hs)
  rw [hp,radialMollify_eq_average hs,radialProbability_integral hs]
  rfl

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma radialEta_as_scale {s : ℝ} (_ : 0 < s) :
    radialEta radialProfile s = fun x => s⁻¹^3 * radialEta radialProfile 1 (s⁻¹ • x) := by
  ext x
  simp [radialEta,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_eq_mul_inv,mul_comm]

lemma radialEta_fderiv_scale {s : ℝ} (hs : 0 < s) (x : WeylSpace) :
    fderiv ℝ (radialEta radialProfile s) x =
      s⁻¹^4 • fderiv ℝ (radialEta radialProfile 1) (s⁻¹ • x) := by
  have hd := (((radialEta_smooth 1).differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul s⁻¹)).const_smul (s⁻¹^3)
  rw [radialEta_as_scale hs]
  refine hd.fderiv.trans ?_
  ext v
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_smul]
  congr 1

lemma radialGradientMass_nonneg : 0 ≤ radialGradientMass := integral_nonneg (fun _ => norm_nonneg _)

lemma radialEta_gradient_integral {s : ℝ} (hs : 0 < s) :
    (∫ x, ‖fderiv ℝ (radialEta radialProfile s) x‖)=radialGradientMass/s := by
  simp_rw [radialEta_fderiv_scale hs,norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ s⁻¹^4)]
  rw [integral_const_mul,Measure.integral_comp_smul volume (fun x : WeylSpace => ‖fderiv ℝ (radialEta radialProfile 1) x‖)]
  simp only [WeylSpace,finrank_euclideanSpace,Fintype.card_fin,inv_pow,inv_inv,smul_eq_mul]
  rw [abs_of_pos (pow_pos hs 3)]
  change (s^4)⁻¹ * (s^3*radialGradientMass)=radialGradientMass/s
  field_simp [hs.ne']

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AnalyticDerivativeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology
open scoped NNReal ENNReal

theorem analyticAt_of_factorial_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {a : E} {R M C : ℝ} (hR : 0<R) (hM : 0≤M) (hC : 0<C)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞)) f (Metric.ball a R))
    (hb : ∀ n : ℕ, ∀ x∈Metric.ball a R,
      ‖iteratedFDeriv ℝ n f x‖≤M*C^n*(n.factorial : ℝ)) : AnalyticAt ℝ f a := by
  let p : FormalMultilinearSeries ℝ E F := fun n => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n f a
  let r : ℝ≥0 := ⟨min R (1/C)/2,by positivity⟩
  have hr : 0<(r : ℝ) := by change 0 < min R (1/C)/2; positivity
  have hrR : (r : ℝ)<R := by
    change min R (1/C)/2<R
    have := min_le_left R (1/C)
    linarith
  have hrC : (r : ℝ)<1/C := by
    change min R (1/C)/2<1/C
    have := min_le_right R (1/C)
    have : 0<1/C := by positivity
    linarith
  have hp (n : ℕ) : ‖p n‖≤M*C^n := by
    dsimp [p]
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (n.factorial : ℝ)⁻¹*(M*C^n*(n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hb n a (by simpa using hR)) (by positivity)
      _ = M*C^n := by
        have hn : (n.factorial : ℝ)≠0 := by positivity
        field_simp
  have hrad : (r : ℝ≥0∞)≤p.radius := by
    apply p.le_radius_of_bound M
    intro n
    calc
      ‖p n‖*(r : ℝ)^n ≤ M*C^n*(r : ℝ)^n := mul_le_mul_of_nonneg_right (hp n) (by positivity)
      _ = M*(C*(r : ℝ))^n := by rw [mul_pow]; ring
      _ ≤ M*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity)
        (by nlinarith [(lt_div_iff₀ hC).mp hrC])) hM
      _ = M := mul_one _
  refine ⟨p,⟨r,⟨hrad,by exact_mod_cast hr,?_⟩⟩⟩
  intro y hy
  have hyr : ‖y‖<(r : ℝ) := by
    rw [Metric.eball_coe] at hy
    simpa using hy
  have hyR : ‖y‖<R := hyr.trans hrR
  have hyC : C*‖y‖<1 := by nlinarith [(lt_div_iff₀ hC).mp hrC]
  have hseg (t : ℝ) (ht : t∈Icc 0 1) : a+t•y∈Metric.ball a R := by
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hyR
  have hdiff (n : ℕ) (t : ℝ) (ht : t∈Icc 0 1) : ContDiffAt ℝ (n+1) f (a+t•y) :=
    ((hf _ (hseg t ht)).contDiffAt (Metric.isOpen_ball.mem_nhds (hseg t ht))).of_le (by exact_mod_cast (show (↑n+1 : ℕ∞)≤⊤ from le_top))
  have he (n : ℕ) :
      ‖f (a+y)-∑ k∈Finset.range (n+1), p k (fun _ => y)‖≤
        M*((n+1 : ℕ) : ℝ)*(C*‖y‖)^(n+1) := by
    rw [map_add_eq_sum_add_integral_iteratedFDeriv (hdiff n)]
    simp only [p,smul_apply,add_sub_cancel_left]
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    have hi : ‖∫ t in (0:ℝ)..1, (1-t)^n •
        iteratedFDeriv ℝ (n+1) f (a+t•y) (fun _ => y)‖≤
        M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1)) ?_).trans (by simp)
      intro t ht
      have ht' : t∈Icc (0:ℝ) 1 := by
        simp only [uIoc_of_le zero_le_one,mem_Ioc] at ht
        exact ⟨ht.1.le,ht.2⟩
      rw [norm_smul,Real.norm_of_nonneg (pow_nonneg (by linarith [ht'.2]) _)]
      calc
          _ ≤ 1*(‖iteratedFDeriv ℝ (n+1) f (a+t•y)‖*‖y‖^(n+1)) :=
            mul_le_mul (pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1]))
              (by simpa using (iteratedFDeriv ℝ (n+1) f (a+t•y)).le_opNorm (fun _ => y))
              (norm_nonneg _) (by positivity)
          _ ≤ M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb (n+1) _ (hseg t ht')) (by positivity : 0≤‖y‖^(n+1))
    calc
      _ ≤ (n.factorial : ℝ)⁻¹*(M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1)) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by
        rw [Nat.factorial_succ,Nat.cast_mul,mul_pow]
        have hn : (n.factorial : ℝ)≠0 := by positivity
        field_simp
  have ht : Tendsto (fun n : ℕ => M*((n+1 : ℕ) : ℝ)*(C*‖y‖)^(n+1)) atTop (𝓝 0) := by
    have hh := (tendsto_self_mul_const_pow_of_lt_one (show 0≤C*‖y‖ by positivity) hyC).comp
      (tendsto_add_atTop_nat 1)
    simpa only [mul_zero,mul_assoc,Function.comp_apply] using hh.const_mul M
  have hlim : Tendsto (fun n : ℕ => ∑ k∈Finset.range (n+1), p k (fun _ => y)) atTop (𝓝 (f (a+y))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp_rw [norm_sub_rev]
    exact squeeze_zero (fun _ => norm_nonneg _) he ht
  apply (hasSum_iff_tendsto_nat_of_summable_norm ?_).mpr
  · exact (tendsto_add_atTop_iff_nat 1).mp hlim
  · apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_geometric_of_lt_one (show 0≤C*‖y‖ by positivity) hyC).mul_left M)
    calc
      ‖p n (fun _ => y)‖≤‖p n‖*‖y‖^n := by simpa using (p n).le_opNorm (fun _ => y)
      _≤M*C^n*‖y‖^n := mul_le_mul_of_nonneg_right (hp n) (by positivity)
      _=M*(C*‖y‖)^n := by rw [mul_pow]; ring

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped Convolution

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

lemma RadialMeanOn.linearIsometry {f : WeylSpace → F} {a : WeylSpace} {R : ℝ}
    (hm : RadialMeanOn f a R) (L : F →ₗᵢ[ℝ] G) : RadialMeanOn (L ∘ f) a R := by
  intro s hs x hx
  change L (f x)=∫ y, (radialEta radialProfile s y) • L (f (x-y))
  simp_rw [←L.map_smul]
  rw [L.integral_comp_comm]
  exact congrArg L (hm s hs x hx)

lemma RadialMeanOn.iterated {f : WeylSpace → F} {a : WeylSpace} {R : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (n : ℕ) : RadialMeanOn (iteratedFDeriv ℝ n f) a R := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact hm.linearIsometry (continuousMultilinearCurryFin0 ℝ WeylSpace F).symm.toLinearIsometry
  | succ n ih =>
    have : CompleteSpace (WeylSpace →L[ℝ] WeylSpace [×n]→L[ℝ] F) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => WeylSpace) F).symm.toIsometryEquiv.completeSpace
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact (ih.derivative (hf.iteratedFDeriv_right (by exact_mod_cast (show (⊤ : ℕ∞)+n≤⊤ from le_top))) (hc.iteratedFDeriv n)).linearIsometry
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => WeylSpace) F).symm.toLinearIsometry

lemma RadialMeanOn.iterated_bound {f : WeylSpace → F} {a : WeylSpace} {R M s : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (hM : 0≤M) (hs : 0 < s)
    (hb : ∀ x∈Metric.ball a R, ‖f x‖≤M) (n : ℕ) :
    ∀ x : WeylSpace, dist x a+(n : ℝ)*s<R →
      ‖iteratedFDeriv ℝ n f x‖≤M*(radialGradientMass/s)^n := by
  induction n with
  | zero =>
    intro x hx
    simp only [Nat.cast_zero,zero_mul,add_zero] at hx
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hb x hx
  | succ n ih =>
    intro x hx
    have hx' : dist x a+s<R := by
      have hn : 0≤(n : ℝ)*s := mul_nonneg (Nat.cast_nonneg _) hs.le
      push_cast at hx
      nlinarith
    rw [←norm_fderiv_iteratedFDeriv]
    have he := (hm.iterated hf hc n).derivative_bound
      (hf.iteratedFDeriv_right (by exact_mod_cast (show (⊤ : ℕ∞)+n≤⊤ from le_top))) hs hx'
      (mul_nonneg hM (pow_nonneg (div_nonneg radialGradientMass_nonneg hs.le) n)) (fun y hy => by
        apply ih
        have hh : dist y x ≤ s := hy
        have ht := dist_triangle y x a
        push_cast at hx
        nlinarith)
    rw [radialEta_gradient_integral hs] at he
    simpa only [pow_succ,mul_assoc] using he

lemma RadialMeanOn.factorial_bound {f : WeylSpace → F} {a x : WeylSpace} {R M : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (hR : 0<R) (hM : 0≤M)
    (hb : ∀ y∈Metric.ball a R, ‖f y‖≤M) (hx : x∈Metric.ball a (R/2)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖≤M*(2*Real.exp 1*(radialGradientMass+1)/R)^n*(n.factorial : ℝ) := by
  rcases n with _ | n
  · simpa using hb x (Metric.ball_subset_ball (by linarith) hx)
  let N : ℕ := n+1
  have hN : 0<(N : ℝ) := by dsimp [N]; positivity
  let s := R/(2*(N : ℝ))
  have hs : 0 < s := by dsimp [s]; positivity
  have he := hm.iterated_bound hf hc hM hs hb N x (by
    have hn : (N : ℝ)*s=R/2 := by dsimp [s]; field_simp
    rw [hn]
    have hx' : dist x a<R/2 := hx
    linarith)
  have hn : (N : ℝ)^N≤(Real.exp 1)^N*(N.factorial : ℝ) := by
    have hh := Real.pow_div_factorial_le_exp (N : ℝ) hN.le N
    rw [div_le_iff₀ (by positivity : 0<(N.factorial : ℝ))] at hh
    simpa only [←Real.exp_nat_mul, mul_one] using hh
  have hbase : radialGradientMass/s≤(2*(radialGradientMass+1)/R)*(N : ℝ) := by
    dsimp [s]
    field_simp
    nlinarith [radialGradientMass_nonneg]
  calc
    _ ≤ M*(radialGradientMass/s)^N := he
    _ ≤ M*((2*(radialGradientMass+1)/R)*(N : ℝ))^N := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity [radialGradientMass_nonneg]) hbase _) hM
    _ = M*(2*(radialGradientMass+1)/R)^N*(N : ℝ)^N := by rw [mul_pow]; ring
    _ ≤ M*(2*(radialGradientMass+1)/R)^N*((Real.exp 1)^N*(N.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hn (by positivity [radialGradientMass_nonneg])
    _ = _ := by
      have heq : 2*Real.exp 1*(radialGradientMass+1)/R = (2*(radialGradientMass+1)/R)*Real.exp 1 := by ring
      rw [heq,mul_pow]
      dsimp [N]
      ring

lemma RadialMeanOn.analyticAt {f : WeylSpace → F} {a : WeylSpace} {R : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (hR : 0<R) : AnalyticAt ℝ f a := by
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hf.continuous
  have hM' : 0≤M := (norm_nonneg (f a)).trans (hM a)
  refine analyticAt_of_factorial_bound (R := R/2) (M := M)
    (C := 2*Real.exp 1*(radialGradientMass+1)/R) (by positivity) hM'
    (by positivity [radialGradientMass_nonneg]) hf.contDiffOn ?_
  intro n x hx
  exact hm.factorial_bound hf hc hR hM' (fun y _ => hM y) hx n

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SmoothHarmonicAnalytic
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

lemma WeaklyHarmonicOn.mono {f : WeylSpace → ℝ} {U V : Set WeylSpace}
    (hw : WeaklyHarmonicOn f U) (hV : V⊆U) : WeaklyHarmonicOn f V := by
  intro ψ hψ hc hs
  exact hw ψ hψ hc (hs.trans hV)

theorem smooth_weak_harmonic_analyticAt {f : WeylSpace → ℝ} {U : Set WeylSpace}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hw : WeaklyHarmonicOn f U)
    (hU : IsOpen U) {a : WeylSpace} (ha : a∈U) : AnalyticAt ℝ f a := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let b : ContDiffBump a := {
    rIn := r/2, rOut := r, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let g : WeylSpace → ℝ := fun x => b x*f x
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := b.contDiff.mul hf
  have hc : HasCompactSupport g := b.hasCompactSupport.mul_right
  have he : EqOn f g (Metric.ball a (r/2)) := by
    intro x hx
    have hb : b x=1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [g,hb]
  have hwg : WeaklyHarmonicOn g (Metric.ball a (r/2)) :=
    .congr_restrict Metric.isOpen_ball.measurableSet
      ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr (ae_of_all _ he))
      (hw.mono ((Metric.ball_subset_ball (by linarith)).trans hsub))
  have hgA : AnalyticAt ℝ g a :=
    (weaklyHarmonic_smooth_mean hg hc hwg).analyticAt hg hc (by positivity)
  apply hgA.congr
  filter_upwards [Metric.ball_mem_nhds a (by positivity : 0 < r/2)] with x hx
  exact (he hx).symm

theorem weakWeyl_analytic_local {f : WholeL2} {U : Set WeylSpace}
    (hw : WeaklyHarmonicOn f U) {a : WeylSpace} {R : ℝ} (hR : 0<R)
    (hball : Metric.closedBall a R⊆U) :
    AnalyticOnNhd ℝ (radialMollify f (R/4)) (Metric.ball a (R/4)) ∧
    (f : WeylSpace → ℝ) =ᵐ[volume.restrict (Metric.ball a (R/4))] radialMollify f (R/4) := by
  obtain ⟨hg,he⟩ := weakWeyl_local hw hR hball
  refine ⟨?_,he⟩
  have hb : Metric.ball a (R/4)⊆U :=
    ((Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall).trans hball
  have hwg := WeaklyHarmonicOn.congr_restrict Metric.isOpen_ball.measurableSet he (hw.mono hb)
  intro x hx
  exact smooth_weak_harmonic_analyticAt hg hwg Metric.isOpen_ball hx

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AnalyticNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter MeasureTheory Topology

section LocalNull
variable {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] (μ : Measure E)

lemma measure_inter_zero_of_local {U Z : Set E}
    (h : ∀ x ∈ U, ∃ V : Set E, x ∈ V ∧ IsOpen V ∧ μ (V ∩ Z) = 0) :
    μ (U ∩ Z) = 0 := by
  choose V hmem hopen hnull using (fun x : U => h x x.property)
  obtain ⟨I,hIc,hcov⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    V hopen (by intro x hx; exact mem_iUnion.mpr ⟨⟨x,hx⟩,hmem ⟨x,hx⟩⟩)
  apply measure_mono_null (t := ⋃ x ∈ I, V x ∩ Z)
  · intro x hx
    rcases mem_iUnion₂.mp (hcov hx.1) with ⟨y,hy,hxy⟩
    exact mem_iUnion₂.mpr ⟨y,hy,hxy,hx.2⟩
  · exact (measure_biUnion_null_iff hIc).mpr (fun x _ => hnull x)
end LocalNull

lemma analyticNull_real : AnalyticNullProperty ℝ volume := by
  intro U f hU hc hf ⟨x,hx,hfx⟩
  have hd : IsDiscrete (f ⁻¹' {0} ∩ U) := isDiscrete_of_codiscreteWithin
    (by simpa only [preimage_compl] using
      hf.preimage_zero_mem_codiscreteWithin hfx hx ⟨⟨x,hx⟩,hc⟩)
  rw [inter_comm]
  exact ((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd).measure_zero volume

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]

omit [SecondCountableTopology E] in
lemma analytic_zero_measurable {U : Set E} {f : E → ℝ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℝ f U) :
    MeasurableSet (U ∩ f ⁻¹' {0}) := by
  have ho := hf.continuousOn.isOpen_inter_preimage hU (isClosed_singleton.isOpen_compl : IsOpen ({0}ᶜ : Set ℝ))
  convert hU.measurableSet.diff ho.measurableSet using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,Set.mem_sdiff,mem_compl_iff]
  tauto

omit [SecondCountableTopology E] in
lemma analytic_null_rectangle (μ : Measure E) (ν : Measure F) [SFinite ν]
    (hE : AnalyticNullProperty E μ) (hF : AnalyticNullProperty F ν)
    {U : Set E} {V : Set F} {f : E × F → ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hcU : IsPreconnected U) (hcV : IsPreconnected V)
    (hf : AnalyticOnNhd ℝ f (U ×ˢ V)) (hx : ∃ x ∈ U ×ˢ V, f x ≠ 0) :
    μ.prod ν ((U ×ˢ V) ∩ f ⁻¹' {0}) = 0 := by
  obtain ⟨⟨x₀,y₀⟩,hxy,hfxy⟩ := hx
  have ha : AnalyticOnNhd ℝ (fun x => f (x,y₀)) U := by
    intro x hx
    have hg : AnalyticAt ℝ (fun t : E => (t,y₀)) x := analyticAt_id.prod analyticAt_const
    exact (hf (x,y₀) ⟨hx,hxy.2⟩).comp (f := fun t : E => (t,y₀)) hg
  have hn := hE U (fun x => f (x,y₀)) hU hcU ha ⟨x₀,hxy.1,hfxy⟩
  apply Measure.measure_prod_null_of_ae_null (analytic_zero_measurable (hU.prod hV) hf)
  filter_upwards [compl_mem_ae_iff.mpr hn] with x hx
  by_cases hxU : x ∈ U
  · have hfx : f (x,y₀) ≠ 0 := by simpa [hxU] using hx
    have hb : AnalyticOnNhd ℝ (fun y => f (x,y)) V := by
      intro y hy
      have hg : AnalyticAt ℝ (fun t : F => (x,t)) y := analyticAt_const.prod analyticAt_id
      exact (hf (x,y) ⟨hxU,hy⟩).comp (f := fun t : F => (x,t)) hg
    change ν (Prod.mk x ⁻¹' ((U ×ˢ V) ∩ f ⁻¹' {0})) = 0
    have he : Prod.mk x ⁻¹' ((U ×ˢ V) ∩ f ⁻¹' {0}) =
        V ∩ (fun y => f (x,y)) ⁻¹' {0} := by ext y; simp [hxU]
    rw [he]
    exact hF V (fun y => f (x,y)) hV hcV hb ⟨y₀,hxy.2,hfx⟩
  · simp [hxU]

lemma analyticNull_prod (μ : Measure E) (ν : Measure F) [SFinite ν]
    (hE : AnalyticNullProperty E μ) (hF : AnalyticNullProperty F ν) :
    AnalyticNullProperty (E × F) (μ.prod ν) := by
  intro U f hU hc hf ⟨x₀,hx₀,hfx₀⟩
  apply measure_inter_zero_of_local
  intro p hp
  obtain ⟨ε,hε,hsub⟩ := Metric.isOpen_iff.mp hU p hp
  let V := Metric.ball p.1 ε ×ˢ Metric.ball p.2 ε
  have hVm : p ∈ V := ⟨Metric.mem_ball_self hε,Metric.mem_ball_self hε⟩
  have hVo : IsOpen V := Metric.isOpen_ball.prod Metric.isOpen_ball
  have hVU : V ⊆ U := by
    intro q hq
    apply hsub
    rw [Metric.mem_ball,Prod.dist_eq]
    exact max_lt hq.1 hq.2
  have hne : ∃ x ∈ V, f x ≠ 0 := by
    by_contra! hn
    have he : f =ᶠ[𝓝 p] 0 := by
      filter_upwards [hVo.mem_nhds hVm] with x hx
      exact hn x hx
    exact hfx₀ (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hp he hx₀)
  refine ⟨V,hVm,hVo,?_⟩
  exact analytic_null_rectangle μ ν hE hF Metric.isOpen_ball Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (convex_ball _ _).isPreconnected (hf.mono hVU) hne

end ScalarConductivity



namespace ScalarConductivity
open Set Filter MeasureTheory Topology

section Transfer
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]

omit [BorelSpace E] [SecondCountableTopology E] [SecondCountableTopology F] in
lemma analyticNull_of_equiv (μ : Measure E) (ν : Measure F) (e : E ≃L[ℝ] F)
    (he : MeasurePreserving e μ ν) (hF : AnalyticNullProperty F ν) :
    AnalyticNullProperty E μ := by
  intro U f hU hc hf ⟨x,hx,hfx⟩
  let V := e '' U
  have hVo : IsOpen V := e.toHomeomorph.isOpenMap _ hU
  have hg : AnalyticOnNhd ℝ (fun y => f (e.symm y)) V := by
    rintro y ⟨z,hz,rfl⟩
    apply (hf z hz).comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply z)
  have hn := hF V (fun y => f (e.symm y)) hVo
    (hc.image e e.continuous.continuousOn) hg ⟨e x,mem_image_of_mem _ hx,by simpa using hfx⟩
  rw [←he.measure_preimage (analytic_zero_measurable hVo hg).nullMeasurableSet] at hn
  have hs : U ∩ f ⁻¹' {0} = e ⁻¹' (V ∩ (fun y => f (e.symm y)) ⁻¹' {0}) := by
    ext z
    simp [V]
  rw [hs]
  exact hn
end Transfer

lemma splitFinCLE_measurePreserving (n : ℕ) :
    MeasurePreserving (splitFinCLE n) volume volume :=
  volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0

theorem analyticNull_fin (n : ℕ) : AnalyticNullProperty (Fin n → ℝ) volume := by
  induction n with
  | zero =>
    intro U f hU hc hf ⟨x,hx,hfx⟩
    have h : U ∩ f ⁻¹' {0} = ∅ := by
      apply eq_empty_of_forall_notMem
      intro y hy
      exact hfx (by simpa only [Subsingleton.elim y x, mem_preimage, mem_singleton_iff] using hy.2)
    rw [h,measure_empty]
  | succ n ih =>
    exact analyticNull_of_equiv volume volume (splitFinCLE n) (splitFinCLE_measurePreserving n)
      (analyticNull_prod volume volume analyticNull_real ih)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AnalyticNullEuclidean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma analyticNull_euclidean (n : ℕ) : AnalyticNullProperty (EuclideanSpace ℝ (Fin n)) volume :=
  analyticNull_of_equiv volume volume
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ))
    (PiLp.volume_preserving_ofLp (Fin n)) (analyticNull_fin n)

lemma analytic_directional_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {U : Set E} (hf : AnalyticOnNhd ℝ f U) (w : E) :
    AnalyticOnNhd ℝ (fun x => fderiv ℝ f x w) U :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp_analyticOnNhd hf.fderiv

lemma analytic_gradient_minor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E → ℝ} {U : Set E} (hu : AnalyticOnNhd ℝ u U)
    (hv : AnalyticOnNhd ℝ v U) (p q : E) :
    AnalyticOnNhd ℝ (fun x => fderiv ℝ u x p*fderiv ℝ v x q-
      fderiv ℝ u x q*fderiv ℝ v x p) U :=
  ((analytic_directional_fderiv hu p).mul (analytic_directional_fderiv hv q)).sub
    ((analytic_directional_fderiv hu q).mul (analytic_directional_fderiv hv p))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_HarmonicRankAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Laplacian InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

lemma laplacian_trace_fderiv (b : OrthonormalBasis ι ℝ E) (f : E → ℝ) (x : E) :
    Δ f x = ∑ i, fderiv ℝ (fderiv ℝ f) x (b i) (b i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  apply Finset.sum_congr rfl
  intro i hi
  exact (bilinearIteratedFDerivTwo_eq_iteratedFDeriv (𝕜 := ℝ) _ x (b i) (b i)).symm

omit [FiniteDimensional ℝ E] in
lemma clm_sum_sq_positive (b : OrthonormalBasis ι ℝ E) (L : E →L[ℝ] ℝ)
    {w : E} (hw : L w ≠ 0) : 0 < ∑ i, (L (b i))^2 := by
  have hnon : 0 ≤ ∑ i, (L (b i))^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  apply lt_of_le_of_ne hnon
  intro hz
  have he : ∀ i, L (b i)=0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i∈Finset.univ) => sq_nonneg (L (b i)))).mp hz.symm i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp this
  apply hw
  rw [←b.sum_repr w,map_sum]
  simp [he]

theorem harmonic_gradient_multiplier_fderiv_zero (b : OrthonormalBasis ι ℝ E)
    {u v lam : E → ℝ} {x w : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x)
    (hlam : DifferentiableAt ℝ lam x)
    (he : (fun y => fderiv ℝ v y) =ᶠ[𝓝 x] (fun y => lam y • fderiv ℝ u y))
    (hlu : Δ u x=0) (hlv : Δ v x=0) (hw : fderiv ℝ u x w ≠ 0) :
    fderiv ℝ lam x=0 := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (by norm_num)).differentiableAt one_ne_zero
  have hdv : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hv.fderiv_right (by norm_num)).differentiableAt one_ne_zero
  have hh (p q : E) :
      fderiv ℝ (fderiv ℝ v) x p q =
        fderiv ℝ lam x p * fderiv ℝ u x q +
        lam x * fderiv ℝ (fderiv ℝ u) x p q := by
    have hd := (hlam.hasFDerivAt.smul hdu.hasFDerivAt).congr_of_eventuallyEq he
    have hp := congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T p q) hd.fderiv
    simpa only [add_apply,ContinuousLinearMap.smulRight_apply,
      smul_apply,smul_eq_mul,add_comm] using hp
  have hs (p q : E) :
      fderiv ℝ lam x p * fderiv ℝ u x q = fderiv ℝ lam x q * fderiv ℝ u x p := by
    have huv := hv.isSymmSndFDerivAt (by norm_num) p q
    have huu := hu.isSymmSndFDerivAt (by norm_num) p q
    change fderiv ℝ (fderiv ℝ v) x p q = fderiv ℝ (fderiv ℝ v) x q p at huv
    change fderiv ℝ (fderiv ℝ u) x p q = fderiv ℝ (fderiv ℝ u) x q p at huu
    rw [hh,hh,huu] at huv
    linarith
  let k := fderiv ℝ lam x w / fderiv ℝ u x w
  have hk (p : E) : fderiv ℝ lam x p = k*fderiv ℝ u x p := by
    dsimp [k]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hw).2
    simpa only [div_mul_eq_mul_div] using hs p w
  have htrace : Δ v x = k*(∑ i, (fderiv ℝ u x (b i))^2)+lam x*Δ u x := by
    simp_rw [laplacian_trace_fderiv b,hh,hk]
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hk0 : k=0 := by
    rw [hlu,hlv,mul_zero,add_zero] at htrace
    exact (mul_eq_zero.mp htrace.symm).resolve_right
      (ne_of_gt (clm_sum_sq_positive b (fderiv ℝ u x) hw))
  ext p
  simp [hk,hk0]

theorem harmonic_rank_one_affine (b : OrthonormalBasis ι ℝ E)
    {u v : E → ℝ} {U : Set E} {w : E}
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hlu : ∀ x∈U, Δ u x=0) (hlv : ∀ x∈U, Δ v x=0)
    (hw : ∀ x∈U, fderiv ℝ u x w ≠ 0)
    (hr : ∀ x∈U, ∀ p q, fderiv ℝ u x p*fderiv ℝ v x q =
      fderiv ℝ u x q*fderiv ℝ v x p) :
    ∃ α β : ℝ, ∀ x∈U, v x=α*u x+β := by
  let lam : E → ℝ := fun x => fderiv ℝ v x w / fderiv ℝ u x w
  have hua (x : E) (hx : x∈U) : ContDiffAt ℝ 2 u x :=
    (hu x hx).contDiffAt (hU.mem_nhds hx)
  have hva (x : E) (hx : x∈U) : ContDiffAt ℝ 2 v x :=
    (hv x hx).contDiffAt (hU.mem_nhds hx)
  have hdlam (x : E) (hx : x∈U) : DifferentiableAt ℝ lam x := by
    have hn : DifferentiableAt ℝ (fun y => fderiv ℝ v y w) x :=
      ((hva x hx).fderiv_right (by norm_num) |>.differentiableAt one_ne_zero).clm_apply (differentiableAt_const w)
    have hd : DifferentiableAt ℝ (fun y => fderiv ℝ u y w) x :=
      ((hua x hx).fderiv_right (by norm_num) |>.differentiableAt one_ne_zero).clm_apply (differentiableAt_const w)
    simpa only [lam,div_eq_mul_inv,Pi.mul_def,Function.comp_def] using
      hn.mul ((hasDerivAt_inv (hw x hx)).differentiableAt.comp x hd)
  have hprop (x : E) (hx : x∈U) : fderiv ℝ v x=lam x • fderiv ℝ u x := by
    ext p
    simp only [smul_apply,smul_eq_mul,lam,div_mul_eq_mul_div]
    apply (eq_div_iff (hw x hx)).2
    nlinarith [hr x hx p w]
  have hzero : EqOn (fderiv ℝ lam) 0 U := by
    intro x hx
    apply harmonic_gradient_multiplier_fderiv_zero b (hua x hx) (hva x hx) (hdlam x hx)
      _ (hlu x hx) (hlv x hx) (hw x hx)
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hprop y hy
  obtain ⟨α,hα⟩ := hU.exists_is_const_of_fderiv_eq_zero hc
    (fun x hx => (hdlam x hx).differentiableWithinAt) hzero
  obtain ⟨β,hβ⟩ := hU.exists_eq_add_of_fderiv_eq hc
    (hv.differentiableOn (by norm_num))
    ((hu.differentiableOn (by norm_num)).const_mul α) (by
      intro x hx
      rw [hprop x hx,hα x hx]
      simpa using (((hua x hx).differentiableAt (by norm_num)).hasFDerivAt.const_mul α).fderiv.symm)
  exact ⟨α,β,hβ⟩

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

omit [MeasurableSpace E] [BorelSpace E] in
lemma noncritical_harmonic_rank_patch (b : OrthonormalBasis ι ℝ E)
    {u v : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hu : AnalyticOnNhd ℝ u U) (hv : AnalyticOnNhd ℝ v U)
    (hlu : ∀ x∈U, Δ u x=0) (hlv : ∀ x∈U, Δ v x=0)
    (hr : ∀ x∈U, ∀ p q, fderiv ℝ u x p*fderiv ℝ v x q=
      fderiv ℝ u x q*fderiv ℝ v x p)
    {x w : E} (hx : x∈U) (hw : fderiv ℝ u x w ≠ 0) :
    ∃ r>0, Metric.ball x r⊆U ∧ ∃ α β : ℝ,
      ∀ y∈Metric.ball x r, fderiv ℝ u y w ≠ 0 ∧ v y=α*u y+β := by
  have hn := ((analytic_directional_fderiv hu w) x hx).continuousAt.eventually_ne hw
  obtain ⟨r,hr0,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) hn)
  have hbU : Metric.ball x r⊆U := fun y hy => (hball hy).1
  have hbn : ∀ y∈Metric.ball x r, fderiv ℝ u y w ≠ 0 := fun y hy => (hball hy).2
  obtain ⟨α,β,he⟩ := harmonic_rank_one_affine b Metric.isOpen_ball
    (convex_ball x r).isPreconnected (hu.contDiffOn_of_completeSpace.mono hbU) (hv.contDiffOn_of_completeSpace.mono hbU)
    (fun y hy => hlu y (hbU hy)) (fun y hy => hlv y (hbU hy)) hbn
    (fun y hy => hr y (hbU hy))
  exact ⟨r,hr0,hbU,α,β,fun y hy => ⟨hbn y hy,he y hy⟩⟩

omit [BorelSpace E] in
theorem analytic_harmonic_ae_regular (b : OrthonormalBasis ι ℝ E)
    (μ : Measure E) (hnull : AnalyticNullProperty E μ)
    {u v : E → ℝ} {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    (hu : AnalyticOnNhd ℝ u U) (hv : AnalyticOnNhd ℝ v U)
    (hlu : ∀ x∈U, Δ u x=0) (hlv : ∀ x∈U, Δ v x=0) :
    ∀ᵐ x∂μ, x∈U → ∃ r>0, Metric.ball x r⊆U ∧
      HarmonicPairRegularOn u v (Metric.ball x r) := by
  classical
  by_cases hminor : ∃ x∈U, ∃ p q : E,
    fderiv ℝ u x p*fderiv ℝ v x q-fderiv ℝ u x q*fderiv ℝ v x p ≠ 0
  · obtain ⟨a,ha,p,q,hne⟩ := hminor
    let M : E → ℝ := fun x => fderiv ℝ u x p*fderiv ℝ v x q-
      fderiv ℝ u x q*fderiv ℝ v x p
    have hM : AnalyticOnNhd ℝ M U := analytic_gradient_minor hu hv p q
    have hz := hnull U M hU hc hM ⟨a,ha,hne⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hMx : M x ≠ 0 := by simpa [hxu] using hx
    have hn := (hM x hxu).continuousAt.eventually_ne hMx
    obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hxu) hn)
    exact ⟨r,hr,fun y hy => (hb hy).1,Or.inl ⟨p,q,fun y hy => (hb hy).2⟩⟩
  have hr : ∀ x∈U, ∀ p q, fderiv ℝ u x p*fderiv ℝ v x q=
      fderiv ℝ u x q*fderiv ℝ v x p := by
    intro x hx p q
    by_contra hn
    exact hminor ⟨x,hx,p,q,sub_ne_zero.mpr hn⟩
  by_cases hdu : ∃ x∈U, ∃ w, fderiv ℝ u x w ≠ 0
  · obtain ⟨a,ha,w,hw⟩ := hdu
    have hz := hnull U (fun x => fderiv ℝ u x w) hU hc
      (analytic_directional_fderiv hu w) ⟨a,ha,hw⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hn : fderiv ℝ u x w ≠ 0 := by simpa [hxu] using hx
    obtain ⟨r,hr0,hb,α,β,he⟩ := noncritical_harmonic_rank_patch b hU hu hv hlu hlv hr hxu hn
    exact ⟨r,hr0,hb,Or.inr (Or.inl ⟨w,α,β,he⟩)⟩
  by_cases hdv : ∃ x∈U, ∃ w, fderiv ℝ v x w ≠ 0
  · obtain ⟨a,ha,w,hw⟩ := hdv
    have hz := hnull U (fun x => fderiv ℝ v x w) hU hc
      (analytic_directional_fderiv hv w) ⟨a,ha,hw⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hn : fderiv ℝ v x w ≠ 0 := by simpa [hxu] using hx
    have hr' : ∀ x∈U, ∀ p q, fderiv ℝ v x p*fderiv ℝ u x q=
        fderiv ℝ v x q*fderiv ℝ u x p := by
      intro x hx p q
      nlinarith [hr x hx p q]
    obtain ⟨r,hr0,hb,α,β,he⟩ := noncritical_harmonic_rank_patch b hU hv hu hlv hlu hr' hxu hn
    exact ⟨r,hr0,hb,Or.inr (Or.inr (Or.inl ⟨w,α,β,he⟩))⟩
  have hdu0 : EqOn (fderiv ℝ u) 0 U := by
    intro x hx
    ext w
    by_contra hn
    exact hdu ⟨x,hx,w,hn⟩
  have hdv0 : EqOn (fderiv ℝ v) 0 U := by
    intro x hx
    ext w
    by_contra hn
    exact hdv ⟨x,hx,w,hn⟩
  obtain ⟨α,hα⟩ := hU.exists_is_const_of_fderiv_eq_zero hc hu.differentiableOn hdu0
  obtain ⟨β,hβ⟩ := hU.exists_is_const_of_fderiv_eq_zero hc hv.differentiableOn hdv0
  exact ae_of_all μ (fun x hx => by
    obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    exact ⟨r,hr,hb,Or.inr (Or.inr (Or.inr ⟨α,β,fun y hy => ⟨hα y (hb hy),hβ y (hb hy)⟩⟩))⟩)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WeakHarmonicClassical
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

lemma compact_weak_harmonic_laplacian {f : WeylSpace → ℝ} {U : Set WeylSpace}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hc : HasCompactSupport f)
    (hw : WeaklyHarmonicOn f U) (hU : IsOpen U) {x : WeylSpace} (hx : x∈U) :
    Δ f x=0 := by
  let F := hc.toSchwartzMap hf
  have hcont : Continuous (Δ f) := by
    change Continuous (fun y => Δ (F : WeylSpace → ℝ) y)
    simpa only [←SchwartzMap.laplacian_apply] using (Δ F).continuous
  have hz : ∀ᵐ y∂volume, y∈U → Δ f y=0 :=
    hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hcont.locallyIntegrable.locallyIntegrableOn U) (by
      intro ψ hψ hcψ hs
      let G := hcψ.toSchwartzMap hψ
      have he := SchwartzMap.integral_mul_laplacian_right_eq_left (μ := volume) F G
      have hwψ := hw ψ hψ hcψ hs
      have he' : (∫ y, f y*Δ ψ y)=(∫ y, Δ f y*ψ y) := by
        have hF : (F : WeylSpace → ℝ) = f := rfl
        have hG : (G : WeylSpace → ℝ) = ψ := rfl
        simp only [SchwartzMap.laplacian_apply] at he
        rw [hF, hG] at he
        exact he
      simpa only [smul_eq_mul,mul_comm] using he'.symm.trans hwψ)
  have he : (fun y => Δ f y) =ᵐ[volume.restrict U] (fun _ => (0:ℝ)) :=
    (ae_restrict_iff' hU.measurableSet).mpr hz
  exact Measure.eqOn_open_of_ae_eq he hU hcont.continuousOn continuous_const.continuousOn hx

lemma smooth_weak_harmonic_laplacian {f : WeylSpace → ℝ} {U : Set WeylSpace}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hw : WeaklyHarmonicOn f U)
    (hU : IsOpen U) {x : WeylSpace} (hx : x∈U) : Δ f x=0 := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let b : ContDiffBump x := {
    rIn := r/2, rOut := r, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let g : WeylSpace → ℝ := fun y => b y*f y
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := b.contDiff.mul hf
  have hc : HasCompactSupport g := b.hasCompactSupport.mul_right
  have he : EqOn f g (Metric.ball x (r/2)) := by
    intro y hy
    have hb : b y=1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simp [g,hb]
  have hwg : WeaklyHarmonicOn g (Metric.ball x (r/2)) :=
    .congr_restrict Metric.isOpen_ball.measurableSet
      ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr (ae_of_all _ he))
      (hw.mono ((Metric.ball_subset_ball (by linarith)).trans hsub))
  have hh := compact_weak_harmonic_laplacian hg hc hwg Metric.isOpen_ball
    (Metric.mem_ball_self (by positivity : 0 < r/2))
  have he' : f =ᶠ[𝓝 x] g := by
    filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < r/2)] with y hy
    exact he hy
  rw [(laplacian_congr_nhds he').eq_of_nhds]
  exact hh

theorem weakWeyl_pair_ae_regular {f g : WholeL2} {U : Set WeylSpace}
    (hf : WeaklyHarmonicOn f U) (hg : WeaklyHarmonicOn g U)
    {a : WeylSpace} {R : ℝ} (hR : 0<R) (hball : Metric.closedBall a R⊆U) :
    ∀ᵐ x∂volume, x∈Metric.ball a (R/4) → ∃ r>0,
      Metric.ball x r⊆Metric.ball a (R/4) ∧
      HarmonicPairRegularOn (radialMollify f (R/4)) (radialMollify g (R/4)) (Metric.ball x r) := by
  obtain ⟨hfA,hfe⟩ := weakWeyl_analytic_local hf hR hball
  obtain ⟨hgA,hge⟩ := weakWeyl_analytic_local hg hR hball
  have hb : Metric.ball a (R/4)⊆U :=
    ((Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall).trans hball
  have hfw := WeaklyHarmonicOn.congr_restrict Metric.isOpen_ball.measurableSet hfe (hf.mono hb)
  have hgw := WeaklyHarmonicOn.congr_restrict Metric.isOpen_ball.measurableSet hge (hg.mono hb)
  exact analytic_harmonic_ae_regular (EuclideanSpace.basisFun (Fin 3) ℝ) volume
    (analyticNull_euclidean 3) Metric.isOpen_ball (convex_ball _ _).isPreconnected hfA hgA
    (fun x hx => smooth_weak_harmonic_laplacian (weakWeyl_local hf hR hball).1 hfw Metric.isOpen_ball hx)
    (fun x hx => smooth_weak_harmonic_laplacian (weakWeyl_local hg hR hball).1 hgw Metric.isOpen_ball hx)

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevDistribution
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma smooth_ball_integration_by_parts {f ψ : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆ball) (v : R3) :
    (∫ x, ψ x*fderiv ℝ f x v ∂ballMeasure)=
      -(∫ x, fderiv ℝ ψ x v*f x ∂ballMeasure) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := ψ) (g := f) (v := v)
    ((hdψ.mul hf.continuous).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_right)
    ((hψ.continuous.mul hdf).integrable_of_hasCompactSupport hc.mul_right)
    ((hψ.continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_right)
    (fun x _ => hψ.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)
  have hl : (∫ x, ψ x*fderiv ℝ f x v ∂ballMeasure)=∫ x, ψ x*fderiv ℝ f x v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh)),zero_mul]
  have hr : (∫ x, fderiv ℝ ψ x v*f x ∂ballMeasure)=∫ x, fderiv ℝ ψ x v*f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun hh => hx (hs hh))]
    simp
  rw [hl,hr]; exact he

lemma weak_integration_by_parts (u : H1) {ψ : R3 → ℝ}
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆ball) (v : R3) :
    inner ℝ (weakValueL (smoothH1 ψ hψ)) (weakDirectionL v u)=
      -inner ℝ (weakDirectionL v (smoothH1 ψ hψ)) (weakValueL u) := by
  have hd {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
      (weakDirectionL v (smoothH1 f hf) : R3 → ℝ) =ᵐ[ballMeasure]
        fun x => fderiv ℝ f x v := by
    filter_upwards [weakDirectionL_apply_ae (smoothH1 f hf) v,smoothH1_gradient f hf]
      with x hx hy
    simp only [hx,hy,inner_gradient_right,RCLike.conj_to_real]
  have hv {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
      (weakValueL (smoothH1 f hf) : R3 → ℝ) =ᵐ[ballMeasure] f :=
    (weakValueL_apply_ae _).trans (smoothH1_value f hf)
  have hsmooth : {z : H1 | z.val∈smoothJets} ⊆
      {z | inner ℝ (weakValueL (smoothH1 ψ hψ)) (weakDirectionL v z)=
        -inner ℝ (weakDirectionL v (smoothH1 ψ hψ)) (weakValueL z)} := by
    rintro z ⟨f,hf,hm,he⟩
    have hz : z=smoothH1 f hf := Subtype.ext he
    change inner ℝ (weakValueL (smoothH1 ψ hψ)) (weakDirectionL v z)=
      -inner ℝ (weakDirectionL v (smoothH1 ψ hψ)) (weakValueL z)
    rw [hz,L2.inner_def,L2.inner_def]
    have hl : (∫ x, inner ℝ (weakValueL (smoothH1 ψ hψ) x)
        (weakDirectionL v (smoothH1 f hf) x) ∂ballMeasure)=
        ∫ x, ψ x*fderiv ℝ f x v ∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [hv hψ,hd hf] with x hx hy
      simp only [hx,hy,Real.inner_apply]
    have hr : (∫ x, inner ℝ (weakDirectionL v (smoothH1 ψ hψ) x)
        (weakValueL (smoothH1 f hf) x) ∂ballMeasure)=
        ∫ x, fderiv ℝ ψ x v*f x ∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [hd hψ,hv hf] with x hx hy
      simp only [hx,hy,Real.inner_apply]
    rw [hl,hr]
    exact smooth_ball_integration_by_parts hf hψ hc hs v

  exact (closure_minimal hsmooth (isClosed_eq
    (continuous_const.inner (weakDirectionL v).continuous)
    ((continuous_const.inner weakValueL.continuous).neg))) (smoothH1_dense u)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusSmoothModeJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal

lemma torusAngles_shift (n : Fin 2 → ℤ) (x : Coord3) :
    torusAngles (x+angularShift (2*Real.pi) n)=torusAngles x := by
  have hπ : 2*Real.pi≠0 := by positivity
  ext i
  fin_cases i <;> simp [torusAngles,angularShift,add_div,hπ,mul_div_cancel_left₀]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusAffineField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma torusAffineField_periodic (s : Fin 3 → ℝ) (κ : ℝ) (f : TorusL2) :
    AngularPeriodic (2*Real.pi) (torusAffineField s κ f) := by
  intro n x
  simp only [torusAffineField,torusRealContinuation,torusAngles_shift]
  simp [angularShift]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_AxialExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma axialZeroExtension_periodic {T d e : ℝ} {f : Coord3 → E}
    (hf : AngularPeriodic T f) : AngularPeriodic T (axialZeroExtension d e f) := by
  intro n x
  change (if d+e/2<x 0+0 then f (x+angularShift T n) else 0)=_
  rw [add_zero,hf n x]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_TorusEndingCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma torusEndingCorrection_periodic {T d e : ℝ} {v f : Coord3 → ℝ}
    (hv : AngularPeriodic T v) (hf : AngularPeriodic T f) :
    AngularPeriodic T (torusEndingCorrection d e v f) := by
  apply axialZeroExtension_periodic
  intro n x
  change v (x+angularShift T n)-f (x+angularShift T n)=v x-f x
  rw [hv n x,hf n x]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FiniteEndPhysicalDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

lemma sourceRealFlat_angles (y : Coord3) :
    torusAngles (sourceRealFlat y)=sourcePhysicalAngles y := by
  ext i
  fin_cases i <;> rfl

lemma physicalPeriodicField_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    physicalPeriodicField f (sourceCollarPiece i j x)=f (sourceFaceAngles i j x) := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  rw [←sourceFaceAngles_physical i j ha hb]
  apply hp.eq_of_angles
  · exact sourceAngular_time ht _
  · rw [sourceRealFlat_angles]
    exact congrArg Prod.snd (sourcePhysicalCoordinates_angular ht _)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusSpectralContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma torusSpectralSynthesis_coeff (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (h : Fin 2 → ℤ) :
    mFourierCoeff (torusSpectralSynthesis s f) h=f.val 0 h := by
  rw [←mFourierBasis_repr]
  change (mFourierBasis (d:=Fin 2)).repr ((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0)) h=_
  rw [LinearIsometryEquiv.apply_symm_apply]

lemma torusRealContinuation_spectral {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (torusSpectralSynthesis s f) x=
      (endPoissonField s f 0 (x 0,torusAngles x)).re := by
  unfold torusRealContinuation
  congr 1
  rw [torusPoissonContinuous_apply hs hx]
  unfold endPoissonField
  apply tsum_congr
  intro h
  simp [endPoissonModeField,endModeCoefficient,torusSpectralSynthesis_coeff]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralEuclideanBridge
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

lemma centralWholeL2_ae (f : CentralL2) : centralWholeL2 f=ᵐ[volume] centralZeroExtension f :=
  (centralZeroExtension_memLp f).coeFn_toLp

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_BranchFiniteEnding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma branchFinitePair_v {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) (x : Coord3) :
    (branchFinitePair i z).v x=branchNormalize i (z.w.v x) := by
  simp [branchFinitePair]

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i f))

lemma branchFinitePair_periodic_v : AngularPeriodic (2*Real.pi) (branchFinitePair i z).v := by
  intro n x
  simp only [branchFinitePair_v,z.periodic_v n x]

lemma branchCorrection_periodic (j : Fin 2) :
    AngularPeriodic (2*Real.pi) (branchCorrection i z j) := by
  exact torusEndingCorrection_periodic
    (fun n x => congrFun (branchFinitePair_periodic_v i z n x) j)
    (torusAffineField_periodic _ _ _)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma physicalBlockRegion_compact : IsCompact physicalBlockRegion :=
  centralPhysical_compact.union (isCompact_iUnion physicalEndRegion_compact)

lemma physicalBlockRegion_subset_ball {y : Fin 3 → ℝ} (hy : y∈physicalBlockRegion) :
    WithLp.toLp 2 y∈ball := by
  rcases hy with hc|he
  · exact centralPhysical_subset_ball hc
  · obtain ⟨i,hi⟩ := mem_iUnion.mp he
    exact physicalEndRegion_subset_ball i hi

lemma physicalEndRegion_mem_block (i : Fin 3) : physicalEndRegion i⊆physicalBlockRegion :=
  fun _ hy => Or.inr (mem_iUnion.mpr ⟨i,hy⟩)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FacePasting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix

variable {E : Type*}

lemma sourceFacePasteList_local (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (y : Coord3)
    (hy : ∃ k∈ks,y∈sourceFlatPatch k.1 k.2) :
    ∃ k∈ks,y∈sourceFlatPatch k.1 k.2 ∧ sourceFacePasteList B v ks y=B k.1 k.2 y := by
  classical
  induction ks with
  | nil => simp at hy
  | cons k ks ih =>
    by_cases hk : y∈sourceFlatPatch k.1 k.2
    · exact ⟨k,List.mem_cons_self,hk,by rw [sourceFacePasteList_cons,ite_eq_left hk]⟩
    · obtain ⟨l,hl,hly⟩ := hy
      have hl' : l∈ks := (List.mem_cons.mp hl).resolve_left (by rintro rfl; exact hk hly)
      obtain ⟨l,hl,hly,he⟩ := ih ⟨l,hl',hly⟩
      exact ⟨l,List.mem_cons_of_mem _ hl,hly,by rw [sourceFacePasteList_cons,ite_eq_right hk,he]⟩

lemma sourceFacePasteList_open (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (hk : (i,j)∈ks) :
    sourceFacePasteList B v ks (sourceCollarPiece i j x)=B i j (sourceCollarPiece i j x) := by
  obtain ⟨k,_,hy,he⟩ := sourceFacePasteList_local B v ks _
    ⟨(i,j),hk,⟨x,sourceCollarOpenBox_subset hx,rfl⟩⟩
  obtain ⟨z,hz,hze⟩ := hy
  obtain ⟨hi,hj⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx hz hze.symm
  simpa only [←hi,←hj] using he

lemma sourceFacePaste_open (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    sourceFacePaste B v (sourceCollarPiece i j x)=B i j (sourceCollarPiece i j x) :=
  sourceFacePasteList_open B v _ i j hx (by simp)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFaceSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceExtendedBox_mono {l r l' r' : ℝ} (hl : l'≤l) (hr : r ≤ r') :
    sourceExtendedBox l r ⊆ sourceExtendedBox l' r' := by
  intro x hx
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,ha,hb⟩

lemma sourceCollarPieces_aedisjoint {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    Pairwise (fun k m : Fin 4 × Fin 4 => AEDisjoint volume
      (sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r)
      (sourceCollarPiece m.1 m.2 '' sourceExtendedBox l r)) := by
  intro k m hkm
  have hn : ∀ᵐ y : Fin 3 → ℝ, y∉
      (sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r) ∩
      (sourceCollarPiece m.1 m.2 '' sourceExtendedBox l r) := by
    filter_upwards [sourceCollar_open_charts_ae] with y hy hm
    obtain ⟨⟨z,hz,hzy⟩,w,hw,hwy⟩ := hm
    have hyb := sourceCollarClosedPiece_subset (l:=-(1:ℝ)/100) (r:=1/100)
      le_rfl le_rfl k.1 k.2 ⟨z,sourceExtendedBox_mono hl hr hz,hzy⟩
    obtain ⟨i,j,x,hx,hxy⟩ := hy hyb
    obtain ⟨hik,hjk⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx
      (sourceExtendedBox_mono hl hr hz) (hxy.trans hzy.symm)
    obtain ⟨him,hjm⟩ := sourceCollarPiece_open_unique i j m.1 m.2 hx
      (sourceExtendedBox_mono hl hr hw) (hxy.trans hwy.symm)
    exact hkm (Prod.ext (hik.symm.trans him) (hjk.symm.trans hjm))
  simpa only [AEDisjoint,ae_iff,not_not,Set.ofPred_mem_eq] using hn

theorem sourceClosedCollarBand_measure_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    volume.restrict (sourceClosedCollarBand l r)=
      ∑ i : Fin 4,∑ j : Fin 4,
        volume.restrict (sourceCollarPiece i j '' sourceExtendedBox l r) := by
  rw [sourceClosedCollarBand_eq l r hl hr]
  have he : (⋃ i : Fin 4,⋃ j : Fin 4,sourceCollarPiece i j '' sourceExtendedBox l r)=
      ⋃ k : Fin 4 × Fin 4,sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r := by
    ext x
    simp
  rw [he,Measure.restrict_iUnion_ae (sourceCollarPieces_aedisjoint hl hr)
    (fun k => (sourceCollarClosedPiece_measurable l r k.1 k.2).nullMeasurableSet),
    Measure.sum_fintype,Fintype.sum_prod_type]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalNullTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma ae_image_of_differentiable {f : Coord3 → Coord3} {S : Set Coord3}
    (hS : MeasurableSet S) (hI : MeasurableSet (f '' S)) (hf : DifferentiableOn ℝ f S) {P : Coord3 → Prop}
    (hP : ∀ᵐ x ∂volume.restrict S,P (f x)) :
    ∀ᵐ y ∂volume.restrict (f '' S),P y := by
  have hn : volume {x | x∈S ∧ ¬ P (f x)}=0 := by
    rw [ae_restrict_iff' hS,ae_iff] at hP
    simpa using hP
  have hn' := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (hf.mono (show {x | x∈S ∧ ¬ P (f x)}⊆S from fun x hx => hx.1)) hn
  rw [ae_iff,Measure.restrict_apply' hI]
  apply le_antisymm _ bot_le
  have he : {y | ¬P y} ∩ f '' S ⊆ f '' {x | x∈S ∧ ¬P (f x)} := by
    rintro y ⟨hy,x,hx,rfl⟩
    exact ⟨x,⟨hx,hy⟩,rfl⟩
  exact (measure_mono he).trans hn'.le

lemma sourceClosedCollarBand_ae_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {P : Coord3 → Prop}
    (hP : ∀ i j : Fin 4,∀ᵐ x ∂volume.restrict (sourceExtendedBox l r),
      P (sourceCollarPiece i j x)) :
    ∀ᵐ y ∂volume.restrict (sourceClosedCollarBand l r),P y := by
  rw [sourceClosedCollarBand_measure_faces hl hr]
  simp only [ae_finsetSum_measure_iff,Finset.mem_univ,true_implies]
  intro i j
  exact ae_image_of_differentiable measurableSet_Icc (sourceCollarClosedPiece_measurable l r i j)
    (fun x _ => (sourceCollarPiece_hasFDeriv i j x).differentiableAt.differentiableWithinAt)
    (hP i j)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma variableCollarField_open (u : Coord3 → Fin 2 → ℝ) (a b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    variableCollarField u a b (sourceCollarPiece i j x)=
      u (flatEndCoordinates a b (sourceFaceAngles i j x)) := by
  rw [variableCollarField,sourceFacePaste_open _ _ i j hx]
  simp only [variableFaceField,sourceCollarInverse_point i j hx]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_FiniteEndPhysicalH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma flatEndCoordinates_shift (a b T : ℝ) (n : Fin 2 → ℤ) (x : Coord3) :
    flatEndCoordinates a b (x+angularShift T n)=flatEndCoordinates a b x+angularShift T n := by
  ext i
  fin_cases i <;> simp [flatEndCoordinates,angularShift]

lemma AngularPeriodic.flatEnd {E : Type*} {f : Coord3 → E} {T : ℝ}
    (hp : AngularPeriodic T f) (a b : ℝ) :
    AngularPeriodic T (fun x => f (flatEndCoordinates a b x)) := by
  intro n x
  change f (flatEndCoordinates a b (x+angularShift T n))=f (flatEndCoordinates a b x)
  rw [flatEndCoordinates_shift,hp n (flatEndCoordinates a b x)]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFourierAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma pairCLM_surjective_of_minor (D : Coord3 →L[ℝ] (Fin 2 → ℝ)) (p q : Coord3)
    (hn : D p 0*D q 1-D p 1*D q 0≠0) : Function.Surjective D := by
  intro y
  refine ⟨((y 0*D q 1-y 1*D q 0)/(D p 0*D q 1-D p 1*D q 0)) • p+
    ((D p 0*y 1-D p 1*y 0)/(D p 0*D q 1-D p 1*D q 0)) • q,?_⟩
  ext j
  fin_cases j <;> simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  · change ((y 0*D q 1-y 1*D q 0)/(D p 0*D q 1-D p 1*D q 0))*D p 0+
      ((D p 0*y 1-D p 1*y 0)/(D p 0*D q 1-D p 1*D q 0))*D q 0=y 0
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,←add_div,div_eq_iff hn]
    ring
  · change ((y 0*D q 1-y 1*D q 0)/(D p 0*D q 1-D p 1*D q 0))*D p 1+
      ((D p 0*y 1-D p 1*y 0)/(D p 0*D q 1-D p 1*D q 0))*D q 1=y 1
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,←add_div,div_eq_iff hn]
    ring

lemma potential_component_fderivAt {u : Coord3 → Fin 2 → ℝ} {x : Coord3}
    (hu : DifferentiableAt ℝ u x) (j : Fin 2) (v : Coord3) :
    fderiv ℝ (fun y => u y j) x v=fderiv ℝ u x v j := by
  rw [(hasFDerivAt_pi'.mp hu.hasFDerivAt j).fderiv]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPhysicalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma centralPhysicalWholeCLM_ae (f : CentralL2) :
    centralPhysicalWholeCLM f=ᵐ[volume]
      (fun y => centralPhysical.indicator (fun y => f (sourcePairCoordinates y)) y) := by
  apply (Lp.coeFn_compMeasurePreserving _ sourcePair_volume).trans
  have he := sourcePair_volume.quasiMeasurePreserving.ae_eq_comp
    (lpZeroExtensionCLM_ae centralClosed_compact.measurableSet f)
  apply he.trans
  filter_upwards [] with y
  by_cases h : sourcePairCoordinates y∈centralClosed <;>
    simp [sourcePairMeasurable_apply,centralPhysical,h]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralAffineCovector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma torusRealContinuation_spectral_eventually {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (torusSpectralSynthesis s f)=ᶠ[𝓝 x]
      (fun y => (endFlatPoisson s f y).re) := by
  filter_upwards [(axial_halfspace_open 0).mem_nhds hx] with y hy
  rw [torusRealContinuation_spectral hs f hy,endFlatPoisson_eq]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralEuclideanJets
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma weak_partial_of_smooth_representative (f F : WholeL2) {U : Set R3}
    (hU : IsOpen U) (v : R3) (g : R3 → ℝ)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (heq : (f : R3 → ℝ)=ᵐ[volume.restrict U] g)
    (hweak : ∀ ψ : R3 → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ⊆U → (∫ x,F x*ψ x)=-(∫ x,f x*fderiv ℝ ψ x v)) :
    ∀ᵐ x∂volume,x∈U → F x=fderiv ℝ g x v := by
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hloc := ((Lp.memLp F).locallyIntegrable (by norm_num : (1:ℝ≥0∞)≤2)).sub hdg.locallyIntegrable
  have heq' := (ae_restrict_iff' hU.measurableSet).mp heq
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc.locallyIntegrableOn U) (by
    intro ψ hψ hc hsp
    have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψF : Integrable (fun x => ψ x*F x) :=
      (hψ.continuous.memLp_of_hasCompactSupport (p := 2) hc).integrable_mul (Lp.memLp F)
    have hψg : Integrable (fun x => ψ x*fderiv ℝ g x v) :=
      (hψ.continuous.mul hdg).integrable_of_hasCompactSupport hc.mul_right
    have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := ψ) (g := g) (v := v)
      ((hdψ.mul hg.continuous).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_right)
      hψg ((hψ.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_right)
      (fun x _ => hψ.differentiable (by simp) x)
      (fun x _ => hg.differentiable (by simp) x)
    have hreplace : (∫ x,f x*fderiv ℝ ψ x v)=(∫ x,g x*fderiv ℝ ψ x v) := by
      apply integral_congr_ae
      filter_upwards [heq'] with x hx
      by_cases hxu : x∈U
      · rw [hx hxu]
      · have hzero := fderiv_of_notMem_tsupport ℝ (fun hh => hxu (hsp hh))
        rw [hzero]
        simp
    have hw := hweak ψ hψ hc hsp
    simp only [smul_eq_mul,Pi.sub_apply,mul_sub]
    rw [integral_sub hψF hψg]
    have hswap : (∫ x,ψ x*F x)=∫ x,F x*ψ x := by simp only [mul_comm]
    rw [hswap,hw,hreplace,he]
    simp only [mul_comm,sub_self])
  filter_upwards [hz] with x hx hxu
  exact sub_eq_zero.mp (hx hxu)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothRepresentativeGluing
attribute [-instance] _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory MeasureTheory.Measure Filter Topology
open TopologicalSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure E) [IsOpenPosMeasure μ]

omit [NormedSpace ℝ E] [BorelSpace E] [IsOpenPosMeasure μ] in
lemma ae_on_open_cover {ι : Type*} (O : ι → Set E) (hO : ∀ i,IsOpen (O i))
    (P : E → Prop) (hP : ∀ i,∀ᵐ x∂μ.restrict (O i),P x) :
    ∀ᵐ x∂μ.restrict (⋃ i,O i),P x := by
  obtain ⟨T,hT,he⟩ := isOpen_iUnion_countable O hO
  rw [←he]
  exact (ae_restrict_biUnion_iff O hT P).mpr (fun i _ => hP i)

theorem smooth_representatives_glue {ι : Type*} (O : ι → Set E) (hO : ∀ i,IsOpen (O i))
    (f : E → F) (g : ι → E → F) {n : WithTop ℕ∞}
    (hg : ∀ i,ContDiffOn ℝ n (g i) (O i))
    (he : ∀ i,f=ᵐ[μ.restrict (O i)] g i) :
    ∃ v : E → F,(∀ i,EqOn v (g i) (O i)) ∧
      f=ᵐ[μ.restrict (⋃ i,O i)] v ∧ ContDiffOn ℝ n v (⋃ i,O i) := by
  classical
  have hc (i j : ι) : EqOn (g i) (g j) (O i∩O j) := by
    apply eqOn_open_of_ae_eq (μ := μ) ?_ ((hO i).inter (hO j))
      ((hg i).continuousOn.mono inter_subset_left) ((hg j).continuousOn.mono inter_subset_right)
    have hi : f=ᵐ[μ.restrict (O i∩O j)] g i :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (he i)
    have hj : f=ᵐ[μ.restrict (O i∩O j)] g j :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (he j)
    exact hi.symm.trans hj
  let chooseIndex (x : E) (hx : x∈⋃ i,O i) : ι := (mem_iUnion.mp hx).choose
  have hchoose (x : E) (hx : x∈⋃ i,O i) : x∈O (chooseIndex x hx) :=
    (mem_iUnion.mp hx).choose_spec
  let v : E → F := fun x => if hx : x∈⋃ i,O i then g (chooseIndex x hx) x else f x
  have hv (i : ι) : EqOn v (g i) (O i) := by
    intro x hx
    have hxU : x∈⋃ i,O i := mem_iUnion.mpr ⟨i,hx⟩
    dsimp only [v]
    rw [dite_eq_left hxU]
    exact hc _ i ⟨hchoose x hxU,hx⟩
  refine ⟨v,hv,?_,?_⟩
  · apply ae_on_open_cover μ O hO (fun x => f x=v x)
    intro i
    filter_upwards [he i,ae_restrict_mem (hO i).measurableSet] with x hx hxi
    exact hx.trans (hv i hxi).symm
  · intro x hx
    obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
    have hi : ContDiffOn ℝ n v (O i) := (hg i).congr (hv i)
    exact (hi x hxi).contDiffAt ((hO i).mem_nhds hxi) |>.contDiffWithinAt

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma HarmonicPairRegularOn.toCartesian {g : Fin 2 → R3 → ℝ} {O : Set R3}
    (hO : IsOpen O) (hg : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (g j) O)
    (h : HarmonicPairRegularOn (g 0) (g 1) O) :
    TwoFieldRankRegular (fun y : Coord3 => fun j => g j (WithLp.toLp 2 y))
      ((WithLp.toLp 2 : Coord3 → R3) ⁻¹' O) := by
  let P : Coord3 ≃L[ℝ] R3 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  let V : Set Coord3 := P ⁻¹' O
  let u : Coord3 → Fin 2 → ℝ := fun y j => g j (P y)
  have hV : IsOpen V := hO.preimage P.continuous
  have hus : ContDiffOn ℝ (↑(⊤:ℕ∞)) u V := by
    apply contDiffOn_pi.mpr
    intro j
    exact (hg j).comp P.contDiff.contDiffOn (fun _ hx => hx)
  have hud (x) (hx : x∈V) :=
    (hus.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx)
  have hd (j : Fin 2) (x : Coord3) (hx : x∈V) (v : R3) :
      fderiv ℝ u x (P.symm v) j=fderiv ℝ (g j) (P x) v := by
    rw [←potential_component_fderivAt (hud x hx)]
    change fderiv ℝ (g j ∘ P) x (P.symm v)=_
    rw [fderiv_comp _ ((hg j (P x) hx).contDiffAt (hO.mem_nhds hx) |>.differentiableAt (by simp))
      P.differentiableAt]
    simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
  change TwoFieldRankRegular u V
  rcases h with h|h|h|h
  · obtain ⟨p,q,hm⟩ := h
    left
    intro x hx
    apply gradientColumns_rank
    apply pairCLM_surjective_of_minor _ (P.symm p) (P.symm q)
    simp only [hd 0 x hx,hd 1 x hx]
    simpa only [mul_comm] using hm (P x) hx
  · obtain ⟨v,α,β,hm⟩ := h
    right; left
    refine ⟨fun x => u x 0,![1,α],![0,β],?_,⟨0,by simp⟩,?_,?_⟩
    · exact (hg 0).comp P.contDiff.contDiffOn (fun _ hx => hx)
    · intro x hx hz
      have he := congrArg (fun D : Coord3 →L[ℝ] ℝ => D (P.symm v)) hz
      rw [potential_component_fderivAt (hud x hx),hd 0 x hx] at he
      exact (hm (P x) hx).1 he
    · intro x hx j
      fin_cases j
      · simp [u]
      · simpa [u] using (hm (P x) hx).2
  · obtain ⟨v,α,β,hm⟩ := h
    right; left
    refine ⟨fun x => u x 1,![α,1],![β,0],?_,⟨1,by simp⟩,?_,?_⟩
    · exact (hg 1).comp P.contDiff.contDiffOn (fun _ hx => hx)
    · intro x hx hz
      have he := congrArg (fun D : Coord3 →L[ℝ] ℝ => D (P.symm v)) hz
      rw [potential_component_fderivAt (hud x hx),hd 1 x hx] at he
      exact (hm (P x) hx).1 he
    · intro x hx j
      fin_cases j
      · simpa [u] using (hm (P x) hx).2
      · simp [u]
  · obtain ⟨α,β,hm⟩ := h
    right; right
    refine ⟨![α,β],?_⟩
    intro x hx
    ext j
    fin_cases j
    · exact (hm (P x) hx).1
    · exact (hm (P x) hx).2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_LocalSmoothWeakDerivative
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma contDiffOn_local_global {g : R3 → ℝ} {U : Set R3}
    (hU : IsOpen U) (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g U) {x : R3} (hx : x∈U) :
    ∃ (V : Set R3) (G : R3 → ℝ),IsOpen V ∧ x∈V ∧ V⊆U ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) G ∧ EqOn G g V := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  obtain ⟨χ,hχ,_,hχs,_,hχone⟩ := exists_smooth_core_cutoff isCompact_singleton
    Metric.isOpen_ball (Metric.isBounded_ball (x := x) (r := r))
    (singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  have he : (fun y => χ y*g y)=ᶠ[𝓝 x] g := by
    filter_upwards [hχone x (mem_singleton x)] with y hy
    simp only [hy,one_mul]
  obtain ⟨V,hVs,hV,hxV⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) he)
  exact ⟨V,fun y => χ y*g y,hV,hxV,fun _ hy => (hVs hy).1,
    smooth_mul_of_support_in_open hU hg hχ (hχs.trans hball),fun _ hy => (hVs hy).2⟩

theorem weak_partial_of_contDiffOn_representative (f F : WholeL2) {U : Set R3}
    (hU : IsOpen U) (v : R3) (g : R3 → ℝ)
    (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g U)
    (heq : (f : R3 → ℝ)=ᵐ[volume.restrict U] g)
    (hweak : ∀ ψ : R3 → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ⊆U → (∫ x,F x*ψ x)=-(∫ x,f x*fderiv ℝ ψ x v)) :
    ∀ᵐ x∂volume,x∈U → F x=fderiv ℝ g x v := by
  classical
  have hlocal (x : U) := contDiffOn_local_global hU hg x.property
  choose V G hV hxV hVU hG he using hlocal
  have hcover : (⋃ x : U,V x)=U := by
    apply Subset.antisymm (iUnion_subset (fun x => hVU x))
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
  have hp (x : U) : ∀ᵐ y∂volume.restrict (V x),F y=fderiv ℝ g y v := by
    have heq' : (f : R3 → ℝ)=ᵐ[volume.restrict (V x)] G x := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (hVU x) heq,
        ae_restrict_mem (hV x).measurableSet] with y hy hyV
      exact hy.trans (he x hyV).symm
    have hw := weak_partial_of_smooth_representative f F (hV x) v (G x) (hG x) heq'
      (fun ψ hψ hc hsp => hweak ψ hψ hc (hsp.trans (hVU x)))
    filter_upwards [ae_restrict_of_ae hw,ae_restrict_mem (hV x).measurableSet] with y hy hyV
    rw [hy hyV]
    exact congrArg (fun D : R3 →L[ℝ] ℝ => D v)
      ((show G x=ᶠ[𝓝 y] g from Filter.Eventually.mono ((hV x).mem_nhds hyV) (fun t ht => he x ht)).fderiv_eq)
  have hh := ae_on_open_cover volume V hV (fun y => F y=fderiv ℝ g y v) hp
  rw [hcover] at hh
  exact (ae_restrict_iff' hU.measurableSet).mp hh

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma original_zero_pairing (f : Lp ℝ 2 ballMeasure) (ψ : R3 → ℝ) :
    (∫ x,lpZeroExtensionCLM (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) f x*ψ x)=
      ∫ x,f x*ψ x∂ballMeasure := by
  change _ = ∫ x in ball,f x*ψ x
  rw [←integral_indicator (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)]
  apply integral_congr_ae
  filter_upwards [lpZeroExtensionCLM_ae (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) f] with x hx
  rw [hx]
  by_cases h : x∈ball
  · simp only [indicator_of_mem h]
    rfl
  · simp only [indicator_of_notMem h,zero_mul]

lemma originalWholeValue_ae (u : H1) : originalWholeValue u=ᵐ[volume] ball.indicator (weakValue u) :=
  lpZeroExtensionCLM_ae_of_ae _ _ (weakValueL_apply_ae u)

lemma originalWholeDirection_ae (u : H1) (v : R3) :
    originalWholeDirection u v=ᵐ[volume] ball.indicator (fun x => inner ℝ v (weakGradient u x)) :=
  lpZeroExtensionCLM_ae_of_ae _ _ (weakDirectionL_apply_ae u v)

lemma originalWhole_weak_partial (u : H1) (v : R3) (ψ : R3 → ℝ)
    (hψ : ContDiff ℝ (↑(⊤:ℕ∞)) ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆ball) :
    (∫ x,originalWholeDirection u v x*ψ x)=
      -(∫ x,originalWholeValue u x*fderiv ℝ ψ x v) := by
  have he := weak_integration_by_parts u hψ hc hs v
  rw [L2.inner_def,L2.inner_def] at he
  change (∫ x,lpZeroExtensionCLM _ (weakDirectionL v u) x*ψ x)=
    -(∫ x,lpZeroExtensionCLM _ (weakValueL u) x*fderiv ℝ ψ x v)
  rw [original_zero_pairing,original_zero_pairing]
  have hv := (weakValueL_apply_ae (smoothH1 ψ hψ)).trans (smoothH1_value ψ hψ)
  have hd : (weakDirectionL v (smoothH1 ψ hψ) : R3 → ℝ)=ᵐ[ballMeasure]
      (fun x => fderiv ℝ ψ x v) := by
    filter_upwards [weakDirectionL_apply_ae (smoothH1 ψ hψ) v,smoothH1_gradient ψ hψ] with x hx hy
    simp only [hx,hy,inner_gradient_right,RCLike.conj_to_real]
  calc
    _ = ∫ x,inner ℝ (weakValueL (smoothH1 ψ hψ) x) (weakDirectionL v u x)∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      simp only [hx,Real.inner_apply,mul_comm]
    _ = _ := he
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hd] with x hx
      simp only [hx,Real.inner_apply,mul_comm]

theorem original_contDiffOn_representative_gradient (u : H1) {U : Set R3}
    (hU : IsOpen U) (hUb : U⊆ball) (g : R3 → ℝ)
    (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g U)
    (heq : weakValue u=ᵐ[volume.restrict U] g) :
    ∀ᵐ x∂volume,x∈U → weakGradient u x=gradient g x := by
  have hf : (originalWholeValue u : R3 → ℝ)=ᵐ[volume.restrict U] g := by
    filter_upwards [ae_restrict_of_ae (originalWholeValue_ae u),heq,ae_restrict_mem hU.measurableSet] with x hx he hxU
    rw [hx,indicator_of_mem (hUb hxU),he]
  have hi (i : Fin 3) := weak_partial_of_contDiffOn_representative
    (originalWholeValue u) (originalWholeDirection u (EuclideanSpace.single i 1)) hU
    (EuclideanSpace.single i 1) g hg hf
    (fun ψ hψ hc hsp => originalWhole_weak_partial u _ ψ hψ hc (hsp.trans hUb))
  have hd (i : Fin 3) := originalWholeDirection_ae u (EuclideanSpace.single i 1)
  filter_upwards [ae_all_iff.mpr hi,ae_all_iff.mpr hd] with x hx hd hxU
  ext i
  have he := hx i hxU
  rw [hd i,indicator_of_mem (hUb hxU)] at he
  have hgr : inner ℝ (EuclideanSpace.single i 1) (gradient g x)=fderiv ℝ g x (EuclideanSpace.single i 1) := by
    simp only [inner_gradient_right,RCLike.conj_to_real]
  rw [←hgr] at he
  simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] using he

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalRepresentativeGluing
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma original_cartesian_representative_gradient (w : H1) {U : Set Coord3}
    (hU : IsOpen U) (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball)
    (v : Coord3 → ℝ) (hv : ContDiffOn ℝ (↑(⊤:ℕ∞)) v U)
    (he : (fun y => weakValue w (WithLp.toLp 2 y))=ᵐ[volume.restrict U] v) :
    ∀ᵐ y : Coord3,y∈U → ∀ i : Fin 3,
      weakGradient w (WithLp.toLp 2 y) i=fderiv ℝ v y (Pi.single i 1) := by
  let Q : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hV : IsOpen (Q ⁻¹' U) := hU.preimage Q.continuous
  have hv' : ContDiffOn ℝ (↑(⊤:ℕ∞)) (v ∘ Q) (Q ⁻¹' U) :=
    hv.comp Q.contDiff.contDiffOn (fun _ hx => hx)
  have he' : weakValue w=ᵐ[volume.restrict (Q ⁻¹' U)] v ∘ Q := by
    apply (ae_restrict_iff' hV.measurableSet).mpr
    have hh := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      ((ae_restrict_iff' hU.measurableSet).mp he)
    filter_upwards [hh] with x hx hxU
    exact hx hxU
  have hh := original_contDiffOn_representative_gradient w hV (fun x hx => hUb _ hx)
    (v ∘ Q) hv' he'
  have hh' := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae hh
  filter_upwards [hh'] with y hy hyU i
  rw [hy hyU]
  have hd : DifferentiableAt ℝ v y := (hv.differentiableOn (by simp) y hyU).differentiableAt
    (hU.mem_nhds hyU)
  have hg : (gradient (v ∘ Q) (WithLp.toLp 2 y)) i=
      fderiv ℝ (v ∘ Q) (WithLp.toLp 2 y) (EuclideanSpace.single i 1) := by
    simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] using
      (inner_gradient_right (f:=v ∘ Q) (x:=EuclideanSpace.single i 1) (y:=WithLp.toLp 2 y))
  rw [hg,fderiv_comp _ hd Q.differentiableAt,Q.fderiv]
  rfl

theorem physical_representative_glue {ι : Type*} (O : ι → Set Coord3)
    (hO : ∀ i,IsOpen (O i)) {U : Set Coord3} (hUm : MeasurableSet U)
    (hOU : ∀ i,O i⊆U) (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball)
    (hcover : ∀ᵐ y : Coord3,y∈U → y∈⋃ i,O i)
    (w : Fin 2 → H1) (g : ι → Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (hreg : ∀ i,RegularPatch (g i) A (O i))
    (he : ∀ i,(fun y j => weakValue (w j) (WithLp.toLp 2 y))=ᵐ[volume.restrict (O i)] g i) :
    ∃ v : Coord3 → Fin 2 → ℝ,
      (∀ᵐ y : Coord3,y∈U → v y=fun j => weakValue (w j) (WithLp.toLp 2 y)) ∧
      (∀ᵐ y : Coord3,y∈U → ∀ i : Fin 3,∀ j : Fin 2,
        fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i) ∧
      volume (U \ regularRegion v A U)=0 := by
  obtain ⟨v,hvg,hve,hvs⟩ := smooth_representatives_glue volume O hO
    (fun y j => weakValue (w j) (WithLp.toLp 2 y)) g (fun i => (hreg i).2.1) he
  have hV : IsOpen (⋃ i,O i) := isOpen_iUnion hO
  have hVU : (⋃ i,O i)⊆U := iUnion_subset hOU
  have hve' := (ae_restrict_iff' hV.measurableSet).mp hve
  have hd (j : Fin 2) := original_cartesian_representative_gradient (w j) hV
    (fun y hy => hUb y (hVU hy)) (fun y => v y j)
    ((contDiffOn_pi.mp hvs) j) (hve.mono (fun y hy => congrFun hy j))
  refine ⟨v,?_,?_,?_⟩
  · filter_upwards [hcover,hve'] with y hc he hy
    exact (he (hc hy)).symm
  · filter_upwards [hcover,ae_all_iff.mpr hd] with y hc hd hy i j
    exact (hd j (hc hy) i).symm
  · have hmem : ∀ᵐ y : Coord3 ∂volume.restrict U,y∈regularRegion v A U := by
      filter_upwards [ae_restrict_of_ae hcover,ae_restrict_mem hUm] with y hc hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hc hy)
      exact mem_regularRegion_iff.mpr ⟨O i,hOU i,
        (hreg i).congr (hvg i) (fun _ _ => rfl),hi⟩
    have he : {y : Coord3 | ¬(y∈U → y∈regularRegion v A U)}=U \ regularRegion v A U := by
      ext y
      simp only [mem_ofPred_eq,Set.mem_sdiff,Classical.not_imp]
    rw [←he]
    exact ae_iff.mp ((ae_restrict_iff' hUm).mp hmem)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalRegionGluing
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

theorem physical_region_glue {ι : Type*} [Countable ι]
    (O : ι → Set Coord3) (hO : ∀ i,IsOpen (O i))
    {U : Set Coord3} (hUm : MeasurableSet U) (hOU : ∀ i,O i⊆U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball)
    (hcover : ∀ᵐ y : Coord3,y∈U → y∈⋃ i,O i)
    (w : Fin 2 → H1) (g : ι → Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (hreg : ∀ i,∀ᵐ y : Coord3,y∈O i → y∈regularRegion (g i) A (O i))
    (he : ∀ i,(fun y j => weakValue (w j) (WithLp.toLp 2 y))=ᵐ[volume.restrict (O i)] g i) :
    ∃ v : Coord3 → Fin 2 → ℝ,
      (∀ᵐ y : Coord3,y∈U → v y=fun j => weakValue (w j) (WithLp.toLp 2 y)) ∧
      (∀ᵐ y : Coord3,y∈U → ∀ i : Fin 3,∀ j : Fin 2,
        fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i) ∧
      volume (U \ regularRegion v A U)=0 := by
  let I := Σ i : ι,{V : Set Coord3 // V⊆O i ∧ RegularPatch (g i) A V}
  let V : I → Set Coord3 := fun i => i.2.val
  let f : I → Coord3 → Fin 2 → ℝ := fun i => g i.1
  have hV : ∀ i,IsOpen (V i) := fun i => i.2.property.2.1
  have hVU : ∀ i,V i⊆U := fun i => i.2.property.1.trans (hOU i.1)
  have hVR : ∀ i,RegularPatch (f i) A (V i) := fun i => i.2.property.2
  have hc : ∀ᵐ y : Coord3,y∈U → y∈⋃ i,V i := by
    filter_upwards [hcover,ae_all_iff.mpr hreg] with y hc hr hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hc hy)
    obtain ⟨W,hWO,hW,hyW⟩ := mem_regularRegion_iff.mp (hr i hi)
    exact mem_iUnion.mpr ⟨⟨i,⟨W,hWO,hW⟩⟩,hyW⟩
  have he' : ∀ i,(fun y j => weakValue (w j) (WithLp.toLp 2 y))=ᵐ[volume.restrict (V i)] f i := by
    intro index
    apply (ae_restrict_iff' (hV index).measurableSet).mpr
    filter_upwards [(ae_restrict_iff' (hO index.1).measurableSet).mp (he index.1)] with point equality membership
    exact equality (index.2.property.1 membership)
  exact physical_representative_glue V hV hUm hVU hUb hc w f A hVR he'

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_WeylPairGluing
attribute [-instance] _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

theorem weakWeyl_pair_cartesian_representative (f : Fin 2 → WholeL2) {U : Set R3}
    (hU : IsOpen U) (hf : ∀ j,WeaklyHarmonicOn (f j) U) :
    ∃ u : Coord3 → Fin 2 → ℝ,
      ContDiffOn ℝ (↑(⊤:ℕ∞)) u ((WithLp.toLp 2 : Coord3 → R3) ⁻¹' U) ∧
      (∀ᵐ y : Coord3,y∈(WithLp.toLp 2 : Coord3 → R3) ⁻¹' U →
        u y=fun j => f j (WithLp.toLp 2 y)) ∧
      ∀ᵐ y : Coord3,y∈(WithLp.toLp 2 : Coord3 → R3) ⁻¹' U →
        y∈regularRegion u (fun _ => ⟨1,Matrix.transpose_one⟩)
          ((WithLp.toLp 2 : Coord3 → R3) ⁻¹' U) := by
  classical
  let I := {p : R3×ℝ // 0<p.2 ∧ Metric.closedBall p.1 p.2⊆U}
  let O : I → Set R3 := fun i => Metric.ball i.val.1 (i.val.2/4)
  let g : I → R3 → Fin 2 → ℝ := fun i x j => radialMollify (f j) (i.val.2/4) x
  have hO (i : I) : IsOpen (O i) := Metric.isOpen_ball
  have hOU (i : I) : O i⊆U := by
    have hh : i.val.2 / 4 ≤ i.val.2 := by linarith [i.property.1]
    exact ((Metric.ball_subset_ball hh).trans Metric.ball_subset_closedBall).trans i.property.2
  have hcover : (⋃ i : I,O i)=U := by
    apply Subset.antisymm (iUnion_subset hOU)
    intro x hx
    obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
    exact mem_iUnion.mpr ⟨⟨(x,r),hr,hball⟩,Metric.mem_ball_self (by change 0 < r/4; positivity)⟩
  have hgs (i : I) : ContDiff ℝ (↑(⊤:ℕ∞)) (g i) := by
    apply contDiff_pi.mpr
    intro j
    exact (weakWeyl_local (hf j) i.property.1 i.property.2).1
  have hge (i : I) : (fun x j => f j x)=ᵐ[volume.restrict (O i)] g i := by
    have hh (j : Fin 2) := (weakWeyl_local (hf j) i.property.1 i.property.2).2
    filter_upwards [ae_all_iff.mpr hh] with x hx
    exact funext hx
  obtain ⟨v,hvg,hve,hvs⟩ := smooth_representatives_glue volume O hO
    (fun x j => f j x) g (fun i => (hgs i).contDiffOn) hge
  rw [hcover] at hve hvs
  let P : Coord3 ≃L[ℝ] R3 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  let V : Set Coord3 := P ⁻¹' U
  let u : Coord3 → Fin 2 → ℝ := v ∘ P
  have hus : ContDiffOn ℝ (↑(⊤:ℕ∞)) u V :=
    hvs.comp P.contDiff.contDiffOn (fun _ hx => hx)
  have he : ∀ᵐ y : Coord3,y∈V → u y=fun j => f j (P y) := by
    have hh := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
      ((ae_restrict_iff' hU.measurableSet).mp hve)
    filter_upwards [hh] with y hy hyV
    exact (hy hyV).symm
  refine ⟨u,hus,he,?_⟩
  let A : Coord3 → Symmetric3 := fun _ => ⟨1,Matrix.transpose_one⟩
  have hp (i : I) : ∀ᵐ x∂volume.restrict (O i),P.symm x∈regularRegion u A V := by
    have hh := weakWeyl_pair_ae_regular (hf 0) (hf 1) i.property.1 i.property.2
    filter_upwards [ae_restrict_of_ae hh,ae_restrict_mem (hO i).measurableSet] with x hx hxO
    obtain ⟨r,hr,hball,hreg⟩ := hx hxO
    let W : Set Coord3 := P ⁻¹' Metric.ball x r
    have hW : IsOpen W := Metric.isOpen_ball.preimage P.continuous
    have hWV : W⊆V := preimage_mono (hball.trans (hOU i))
    have hg (j : Fin 2) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun x => g i x j) (Metric.ball x r) :=
      ((weakWeyl_local (hf j) i.property.1 i.property.2).1).contDiffOn
    have hrr := HarmonicPairRegularOn.toCartesian Metric.isOpen_ball hg hreg
    have heW : EqOn u (fun y j => g i (P y) j) W := by
      intro y hy
      exact hvg i (hball hy)
    refine mem_regularRegion_iff.mpr ⟨W,hWV,⟨hW,hus.mono hWV,contDiff_const.contDiffOn,
      hrr.congr hW heW⟩,?_⟩
    change P (P.symm x)∈Metric.ball x r
    rw [P.apply_symm_apply]
    exact Metric.mem_ball_self hr
  have hpU := ae_on_open_cover volume O hO
    (fun x => P.symm x∈regularRegion u A V) hp
  rw [hcover] at hpU
  have hh := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU.measurableSet).mp hpU)
  filter_upwards [hh] with y hy hyV
  exact hy hyV

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralHarmonicOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma centralStrict_open : IsOpen centralStrict := by
  have he : {y : Coord3 | ∀ k : Fin 2,
      sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)< -centralThickness} =
      ⋂ k : Fin 2,{y : Coord3 | sourceCollarTime
        ((sourceChildHomeomorph (actualChildSign k)).symm y)< -centralThickness} := by
    ext y
    simp only [mem_iInter,mem_ofPred_eq]
  change IsOpen ({y : Coord3 | centralThickness < sourceCollarTime y} ∩
    {y : Coord3 | ∀ k : Fin 2,sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y)< -centralThickness})
  rw [he]
  apply IsOpen.inter (isOpen_lt continuous_const locallyLipschitz_sourceCollarTime.continuous)
  exact isOpen_iInter_of_finite (fun k : Fin 2 => isOpen_lt
    (locallyLipschitz_sourceCollarTime.continuous.comp
      (sourceChildHomeomorph (actualChildSign k)).symm.continuous) continuous_const)

lemma centralStrict_subset : centralStrict⊆centralPhysical := fun y hy =>
  (centralPhysical_time_iff y).mpr ⟨hy.1.le,fun k => (hy.2 k).le⟩

lemma centralStrict_conull : ∀ᵐ y : Coord3,y∈centralPhysical → y∈centralStrict := by
  have hp := sourceColevel_ae_ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
  have hc (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae
    (sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness]))
  filter_upwards [hp,ae_all_iff.mpr hc] with y hp hc hy
  have ht := (centralPhysical_time_iff y).mp hy
  exact ⟨lt_of_le_of_ne ht.1 hp.symm,fun k => lt_of_le_of_ne (ht.2 k) (hc k)⟩

lemma centralStrict_harmonic : (WithLp.ofLp : R3 → Coord3) ⁻¹' centralStrict⊆centralHarmonicRegion := by
  intro x hx
  refine ⟨centralStrict_subset hx,?_⟩
  intro i θ he
  have hpair : sourcePairCoordinates (WithLp.ofLp x)=centralBoundary i θ := he
  have hinj : Function.Injective sourcePairCoordinates := sourcePairCLE.injective
  fin_cases i
  · have he' : WithLp.ofLp x=sourceAngularCollar centralThickness θ := hinj hpair
    have ht := hx.1
    rw [he',sourceAngular_time (by norm_num [centralThickness])] at ht
    exact lt_irrefl _ ht
  · have he' : WithLp.ofLp x=sourceChildCoordinates 1 (sourceAngularCollar (-centralThickness) θ) := hinj hpair
    have ht := hx.2 0
    change sourceCollarTime ((sourceChildHomeomorph 1).symm (WithLp.ofLp x))< -centralThickness at ht
    rw [he',show sourceChildCoordinates 1=(sourceChildHomeomorph 1) from rfl,
      (sourceChildHomeomorph 1).symm_apply_apply,sourceAngular_time (by norm_num [centralThickness])] at ht
    exact lt_irrefl _ ht
  · have he' : WithLp.ofLp x=sourceChildCoordinates (-1) (sourceAngularCollar (-centralThickness) θ) := hinj hpair
    have ht := hx.2 1
    change sourceCollarTime ((sourceChildHomeomorph (-1)).symm (WithLp.ofLp x))< -centralThickness at ht
    rw [he',show sourceChildCoordinates (-1)=(sourceChildHomeomorph (-1)) from rfl,
      (sourceChildHomeomorph (-1)).symm_apply_apply,sourceAngular_time (by norm_num [centralThickness])] at ht
    exact lt_irrefl _ ht

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralCorrectedRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma H1JetOn.value_cartesian {w : H1} {D : Set Coord3} {f : R3 → JetFiber}
    (hw : H1JetOn w D f) (hDb : ∀ y∈D,WithLp.toLp 2 y∈ball) :
    ∀ᵐ y : Coord3,y∈D → weakValue w (WithLp.toLp 2 y)=f (WithLp.toLp 2 y) 0 := by
  have hh := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).mp hw)
  filter_upwards [hh] with y hy hyD
  exact congrArg (fun z : JetFiber => z 0) (hy (hDb y hyD) hyD)

lemma centralFullJet_value_ae (s : Fin 3 → ℝ) (p : CentralAmbient s) :
    ∀ᵐ y : Coord3,y∈centralPhysical → centralFullJetCLM s p (WithLp.toLp 2 y) 0=
      centralWholeL2 (centralAmbientComponent s 0 p) (WithLp.toLp 2 y) := by
  have hh := physicalFourJetCLM_ae (fun i => centralPhysicalWholeCLM (centralAmbientComponent s i p))
  have hh' := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).mp hh)
  have hr := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    (centralWholeL2_ae (centralAmbientComponent s 0 p))
  filter_upwards [hh',hr,centralPhysicalWholeCLM_ae (centralAmbientComponent s 0 p)] with y hy hr hc hyC
  change physicalFourJetCLM (fun i => centralPhysicalWholeCLM (centralAmbientComponent s i p))
    (WithLp.toLp 2 y) 0=_
  rw [hy (centralPhysical_subset_ball hyC),hr]
  change centralPhysicalWholeCLM (centralAmbientComponent s 0 p) y=_
  rw [hc]
  change centralPhysical.indicator (fun y => centralAmbientComponent s 0 p (sourcePairCoordinates y)) y=
    centralClosed.indicator (centralAmbientComponent s 0 p) (centralEuclideanCLE (WithLp.toLp 2 y))
  rw [indicator_of_mem hyC,indicator_of_mem (show centralEuclideanCLE (WithLp.toLp 2 y)∈centralClosed from hyC)]
  rfl

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma central_representative {w : Fin 2 → H1}
    (hw : ∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val)) :
    ∃ u : Coord3 → Fin 2 → ℝ,
      ContDiffOn ℝ (↑(⊤:ℕ∞)) u centralStrict ∧
      (∀ᵐ y : Coord3,y∈centralStrict → u y=fun j => weakValue (w j) (WithLp.toLp 2 y)) ∧
      ∀ᵐ y : Coord3,y∈centralStrict → y∈regularRegion u
        (fun _ => ⟨1,Matrix.transpose_one⟩) centralStrict := by
  let U : Set R3 := (WithLp.ofLp : R3 → Coord3) ⁻¹' centralStrict
  have hU : IsOpen U := centralStrict_open.preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous
  obtain ⟨u,hs,he,hr⟩ := weakWeyl_pair_cartesian_representative
    (fun j => centralWholeL2 (centralAmbientComponent s 0 (z.p j).val)) hU
    (fun j => (z.harmonic j).mono centralStrict_harmonic)
  refine ⟨u,hs,?_,hr⟩
  have hj (j : Fin 2) : ∀ᵐ y : Coord3,y∈centralPhysical →
      weakValue (w j) (WithLp.toLp 2 y)=centralWholeL2 (centralAmbientComponent s 0 (z.p j).val) (WithLp.toLp 2 y) := by
    filter_upwards [(hw j).value_cartesian (fun _ => centralPhysical_subset_ball),
      centralFullJet_value_ae s (z.p j).val] with y hw hv hy
    exact (hw hy).trans (hv hy)
  filter_upwards [he,ae_all_iff.mpr hj] with y he hw hy
  rw [he hy]
  funext j
  exact (hw j (centralStrict_subset hy)).symm

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma correctedEndValue_face {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) (a b : ℝ) (m n : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    fullAttachedEndValue s (f j) a b (centralBasisSlopes j i) (sourceCollarPiece m n x)+
      attachedPeriodicField (branchCorrection i z j) a b (sourceCollarPiece m n x)=
      variableCollarField (fun y j => branchSplicedField i z j y) a b (sourceCollarPiece m n x) j := by
  rw [variableCollarField_open _ a b m n hx]
  change (attachedEndPoissonField s (f j) a b 0 (sourceCollarPiece m n x)).re+
    (centralBasisSlopes j i)*(a*(sourceCollarTime (sourceCollarPiece m n x)-b))+
    physicalPeriodicField (fun y => branchCorrection i z j (flatEndCoordinates a b y)) (sourceCollarPiece m n x)=_
  rw [attachedEndPoissonField_piece _ _ _ _ _ _ (sourceCollarOpenBox_subset hx),
    physicalPeriodicField_piece ((branchCorrection_periodic i z j).flatEnd a b) m n
      (sourceCollarOpenBox_subset hx),sourceCollarPiece_time_open hx]
  unfold branchSplicedField torusAffineField
  rw [(torusRealContinuation_spectral_eventually hs (f j)
    (show 0<(flatEndCoordinates a b (sourceFaceAngles m n x)) 0 from ht)).eq_of_nhds]
  change _+_+_= (centralBasisSlopes j i)*(a*(x 0-b))+
    (endFlatPoisson s (f j) (endAxialAffine a b (sourceFaceAngles m n x))).re+_
  ring

lemma correctedEndValue_band {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) (a b : ℝ) {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Ioo l r,0<a*(t-b)) :
    ∀ᵐ y∂volume.restrict (sourceClosedCollarBand l r),
      fullAttachedEndValue s (f j) a b (centralBasisSlopes j i) y+
        attachedPeriodicField (branchCorrection i z j) a b y=
        variableCollarField (fun y j => branchSplicedField i z j y) a b y j := by
  apply sourceClosedCollarBand_ae_faces hl hr
  intro m n
  filter_upwards [sourceExtendedBox_open_ae hl hr,sourceExtendedBox_axial_strict_ae l r]
    with x hxo hxt
  exact correctedEndValue_face hs f i z j a b m n hxo (hT _ hxt)

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma parent_open_time {t : ℝ} (ht : t∈Ioo 0 centralThickness) :
    0<z.compression 0*(t-centralThickness) := mul_pos_of_neg_of_neg z.compression_parent (sub_neg.mpr ht.2)
lemma child_open_time (k : Fin 2) {t : ℝ} (ht : t∈Ioo (-centralThickness) 0) :
    0<z.compression k.succ*(t-(-centralThickness)) := mul_pos (z.compression_child k) (sub_pos.mpr ht.1)

lemma endRepresentative_value
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (i : Fin 3) (j : Fin 2) :
    ∀ᵐ y : Coord3,y∈physicalEndRegion i → z.correctedEndJet j i (WithLp.toLp 2 y) 0=z.endRepresentative i y j := by
  refine Fin.cases ?_ (fun k => ?_) i
  · have hh := correctedEndValue_band hs (fun j => centralT s 0 (z.p j)) 0 (z.ending 0) j
      (z.compression 0) centralThickness (by norm_num : -(1:ℝ)/100≤0)
      (by norm_num [centralThickness] : centralThickness≤(1:ℝ)/100) (fun t => z.parent_open_time)
    exact (ae_restrict_iff' (physicalEndRegion_compact 0).measurableSet).mp hh
  · have hh := correctedEndValue_band hs (fun j => centralT s k.succ (z.p j)) k.succ (z.ending k.succ) j
      (z.compression k.succ) (-centralThickness) (by norm_num [centralThickness] : -(1:ℝ)/100≤-centralThickness)
      (by norm_num : (0:ℝ)≤1/100) (fun t => z.child_open_time k)
    exact (sourceChildInverse_quasi (actualChildSign k)).ae
      ((ae_restrict_iff' childEndBand_measurable).mp hh)

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalEndOpen
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma physicalEndOpen_open (i : Fin 3) : IsOpen (physicalEndOpen i) := by
  refine Fin.cases ?_ (fun k => ?_) i
  · exact isOpen_Ioo.preimage locallyLipschitz_sourceCollarTime.continuous
  · exact isOpen_Ioo.preimage (locallyLipschitz_sourceCollarTime.continuous.comp
      (sourceChildHomeomorph (actualChildSign k)).symm.continuous)

lemma physicalEndOpen_subset (i : Fin 3) : physicalEndOpen i⊆physicalEndRegion i := by
  refine Fin.cases ?_ (fun k => ?_) i <;> exact fun y hy => ⟨hy.1.le,hy.2.le⟩

lemma physicalEndOpen_conull (i : Fin 3) :
    ∀ᵐ y : Coord3,y∈physicalEndRegion i → y∈physicalEndOpen i := by
  have hn (t : ℝ) (ht : t∈Icc (-(1:ℝ)/100) (1/100)) := sourceColevel_ae_ne ht
  refine Fin.cases ?_ (fun k => ?_) i
  · filter_upwards [hn 0 (by norm_num),hn centralThickness (by norm_num [centralThickness])]
      with y h0 hct hy
    exact ⟨lt_of_le_of_ne hy.1 h0.symm,lt_of_le_of_ne hy.2 hct⟩
  · have hh := (sourceChildInverse_quasi (actualChildSign k))
    filter_upwards [hh.ae (hn 0 (by norm_num)),
      hh.ae (hn (-centralThickness) (by norm_num [centralThickness]))] with y h0 hct hy
    exact ⟨lt_of_le_of_ne hy.1 hct.symm,lt_of_le_of_ne hy.2 h0⟩

lemma centralStrict_no_end {y : Coord3} (hy : y∈centralStrict) (i : Fin 3) :
    y∉physicalEndRegion i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · exact fun he => (not_le.mpr hy.1) he.2
  · exact fun he => (not_le.mpr (hy.2 k)) he.1

lemma variableBlockTensor_centralStrict (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    {y : Coord3} (hy : y∈centralStrict) : variableBlockTensor K a y=1 :=
  variableBlockTensorList_outside K a _ (fun i _ => centralStrict_no_end hy i)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

attribute [local instance] OAI.ScalarConductivity.physicalBlockRepresentativeMeasurableSpace
theorem corrected_pair_representative_oai
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (w : Fin 2 → H1)
    (hwc : ∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val))
    (hwe : ∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i)) :
    ∃ v : Coord3 → Fin 2 → ℝ,
      (∀ᵐ y : Coord3,y∈physicalBlockRegion → v y=fun j => weakValue (w j) (WithLp.toLp 2 y)) ∧
      (∀ᵐ y : Coord3,y∈physicalBlockRegion → ∀ i : Fin 3,∀ j : Fin 2,
        fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i) ∧
      volume (physicalBlockRegion \ regularRegion v (z.cartesianTensor hs) physicalBlockRegion)=0 := by
  obtain ⟨u,hu,he,hr⟩ := z.central_representative hwc
  let O : Option (Fin 3) → Set Coord3 := fun i => i.elim centralStrict physicalEndOpen
  let g : Option (Fin 3) → Coord3 → Fin 2 → ℝ := fun i => i.elim u z.endRepresentative
  have hO : ∀ i,IsOpen (O i) := by
    intro i
    cases i with
    | none => exact centralStrict_open
    | some i => exact physicalEndOpen_open i
  have hOU : ∀ i,O i⊆physicalBlockRegion := by
    intro i
    cases i with
    | none => exact fun _ hy => Or.inl (centralStrict_subset hy)
    | some i => exact (physicalEndOpen_subset i).trans (physicalEndRegion_mem_block i)
  have hc : ∀ᵐ y : Coord3,y∈physicalBlockRegion → y∈⋃ i,O i := by
    filter_upwards [centralStrict_conull,ae_all_iff.mpr physicalEndOpen_conull] with y hcc hce hy
    rcases hy with hc|he
    · exact mem_iUnion.mpr ⟨none,hcc hc⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp he
      exact mem_iUnion.mpr ⟨some i,hce i hi⟩
  have hES (i : Fin 3) (y : Coord3) : (variableEndTensor z.flatTensor z.compression i y).IsSymm :=
    (variableEndTensor_properties z.flatTensor z.compression (z.flatTensor_properties hs) z.compression_ne i).2.1 y
  have hreg : ∀ i,∀ᵐ y : Coord3,y∈O i → y∈regularRegion (g i) (z.cartesianTensor hs) (O i) := by
    intro i
    cases i with
    | none =>
      filter_upwards [hr] with y hy hyO
      apply mem_regularRegion_congr_nhds (hy hyO) Filter.EventuallyEq.rfl ?_ centralStrict_open hyO
      filter_upwards [centralStrict_open.mem_nhds hyO] with x hx
      exact Subtype.ext (variableBlockTensor_centralStrict z.flatTensor z.compression hx)
    | some i =>
      filter_upwards [z.endRepresentative_regular hs hES i] with y hy hyO
      apply mem_regularRegion_congr_nhds (hy (physicalEndOpen_subset i hyO)) Filter.EventuallyEq.rfl ?_
        (physicalEndOpen_open i) hyO
      filter_upwards [(physicalEndOpen_open i).mem_nhds hyO] with x hx
      exact Subtype.ext (variableBlockTensor_local z.flatTensor z.compression i (physicalEndOpen_subset i hx))
  have he' : ∀ i,(fun y j => weakValue (w j) (WithLp.toLp 2 y))=ᵐ[volume.restrict (O i)] g i := by
    intro i
    apply (ae_restrict_iff' (hO i).measurableSet).mpr
    cases i with
    | none =>
      filter_upwards [he] with y hy hyO
      exact (hy hyO).symm
    | some i =>
      have hv (j : Fin 2) := z.endRepresentative_value hs i j
      have hw (j : Fin 2) := (hwe j i).value_cartesian (fun _ => physicalEndRegion_subset_ball i)
      filter_upwards [ae_all_iff.mpr hv,ae_all_iff.mpr hw] with y hv hw hyO
      funext j
      exact (hw j (physicalEndOpen_subset i hyO)).trans (hv j (physicalEndOpen_subset i hyO))
  exact physical_region_glue O hO physicalBlockRegion_compact.measurableSet hOU
    (fun _ => physicalBlockRegion_subset_ball) hc w g (z.cartesianTensor hs) hreg he'

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_pair_representative_oai := @OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_pair_representative_oai
