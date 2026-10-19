-- Prove2me | solution 1 for OAI.PettyProjection.FixedPoint.no_C1_retraction_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:08:59.963988+00:00
-- url     : https://prove2.me/submissions/27509713-d829-4573-a4a8-2212b7b919f2

import Mathlib
import Definitions.Def_OAIQWPP000

section
-- module Solutions.OAIQW_PettyProjection.FixedPointCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX uι uα

noncomputable section
open Set MeasureTheory Polynomial
open scoped BigOperators
namespace PettyProjection.FixedPoint

variable {X : Type uX} [TopologicalSpace X]

lemma continuousCoeffs_C {f : X → ℝ} (hf : Continuous f) :
    ContinuousCoeffs (fun x => Polynomial.C (f x)) := by
  intro k
  by_cases hk : k = 0
  · subst k; simpa only [coeff_C_zero] using hf
  · simpa only [coeff_C, ite_eq_right hk] using (continuous_const : Continuous (fun _ : X => (0 : ℝ)))

lemma ContinuousCoeffs.add {p q : X → Polynomial ℝ}
    (hp : ContinuousCoeffs p) (hq : ContinuousCoeffs q) :
    ContinuousCoeffs (fun x => p x + q x) := by
  intro k
  simp only [coeff_add]
  exact continuous_add.comp ((hp k).prodMk (hq k))

lemma eval_integralPolynomial {α : Type uα} [MeasurableSpace α] (μ : Measure α)
    (p : α → Polynomial ℝ) (d : ℕ) (hp : ∀ x, (p x).natDegree ≤ d)
    (hi : ∀ k ≤ d, Integrable (fun x => (p x).coeff k) μ) (t : ℝ) :
    (integralPolynomial μ p d).eval t = ∫ x, (p x).eval t ∂μ := by
  have he (x : α) : (p x).eval t = ∑ k ∈ Finset.range (d+1), (p x).coeff k*t^k := by
    exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hp x)) t
  simp only [integralPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    exact (integral_mul_const _ _).symm
  · intro k hk
    exact (hi k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).mul_const _

lemma exists_integralOn_det_polynomial {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {α : Type uα} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [T2Space α]
    (μ : Measure α) [IsFiniteMeasureOnCompacts μ] {s : Set α} (hs : IsCompact s)
    (A B : α → Matrix ι ι ℝ) (hA : ContinuousOn A s) (hB : ContinuousOn B s) :
    ∃ p : Polynomial ℝ, ∀ t : ℝ,
      p.eval t = ∫ x in s, (t • A x + B x).det ∂μ := by
  let q : α → Polynomial ℝ := fun x =>
    Matrix.det ((Polynomial.X : Polynomial ℝ) • (A x).map Polynomial.C + (B x).map Polynomial.C)
  have hq : ContinuousCoeffs (fun x : s => q x) := by
    apply ContinuousCoeffs.det
    intro i j
    apply ContinuousCoeffs.add
    · exact (continuousCoeffs_const Polynomial.X).mul
        (continuousCoeffs_C ((continuous_apply j).comp ((continuous_apply i).comp
          (continuousOn_iff_continuous_domRestrict.mp hA))))
    · exact continuousCoeffs_C ((continuous_apply j).comp ((continuous_apply i).comp
        (continuousOn_iff_continuous_domRestrict.mp hB)))
  have hdeg (x : α) : (q x).natDegree ≤ Fintype.card ι :=
    Polynomial.natDegree_det_X_add_C_le (A x) (B x)
  refine ⟨integralPolynomial (μ.restrict s) q (Fintype.card ι), fun t => ?_⟩
  rw [eval_integralPolynomial (μ.restrict s) q _ hdeg
    (fun k _ => ContinuousOn.integrableOn_compact hs
      (continuousOn_iff_continuous_domRestrict.mpr (hq k)))]
  apply integral_congr_ae
  filter_upwards with x
  change (Polynomial.evalRingHom t) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, map_add, Polynomial.coe_evalRingHom, eval_mul, eval_X, eval_C]

lemma exists_integralOn_clm_det_polynomial
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {α : Type uα} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [T2Space α]
    (μ : Measure α) [IsFiniteMeasureOnCompacts μ] {s : Set α} (hs : IsCompact s)
    (A B : α → (E →L[ℝ] E)) (hA : ContinuousOn A s) (hB : ContinuousOn B s) :
    ∃ p : Polynomial ℝ, ∀ t : ℝ,
      p.eval t = ∫ x in s, (t • A x + B x).det ∂μ := by
  classical
  let b := Module.finBasis ℝ E
  let M := (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
  have hM := M.continuous_of_finiteDimensional
  obtain ⟨p,hp⟩ := exists_integralOn_det_polynomial μ hs
    (fun x => M (A x)) (fun x => M (B x)) (hM.comp_continuousOn hA) (hM.comp_continuousOn hB)
  refine ⟨p,fun t => (hp t).trans ?_⟩
  apply integral_congr_ae
  filter_upwards with x
  rw [← map_smul M,← map_add M]
  exact LinearMap.det_toMatrix b _

end PettyProjection.FixedPoint
end

noncomputable section
open Set Metric Function
open scoped NNReal
namespace PettyProjection.FixedPoint
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma bijective_add_small {z : E → E} {C : ℝ≥0} (hz : LipschitzWith C z)
    {t : ℝ} (ht : ‖t‖₊*C<1) : Bijective (fun x => x+t • z x) := by
  have hc (y : E) : ContractingWith (‖t‖₊*C) (fun x => y-t • z x) := by
    refine ⟨ht, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x w
    simp only [dist_sub_left, dist_smul₀, NNReal.coe_mul, coe_nnnorm]
    calc
      ‖t‖ * dist (z x) (z w) ≤ ‖t‖ * (C * dist x w) :=
        mul_le_mul_of_nonneg_left (hz.dist_le_mul x w) (norm_nonneg t)
      _ = _ := by ring
  constructor
  · intro x y hxy
    apply (hc (x+t • z x)).fixedPoint_unique'
    · change x+t • z x-t • z x=x
      abel
    · change x+t • z x-t • z y=y
      change x+t • z x=y+t • z y at hxy
      rw [hxy]
      abel
  · intro y
    obtain ⟨x,hx,-⟩ := (hc y).exists_fixedPoint (0:E) (edist_ne_top _ _)
    refine ⟨x,?_⟩
    change y-t • z x=x at hx
    exact eq_sub_iff_add_eq.mp hx.symm

lemma image_closedBall_add_small {z : E → E} {C : ℝ≥0} (hz : LipschitzWith C z)
    (hzero : ∀ x, 1≤‖x‖ → z x=0) {t : ℝ} (ht : ‖t‖₊*C<1) :
    (fun x => x+t • z x) '' closedBall (0:E) 1 = closedBall (0:E) 1 := by
  have hbi := bijective_add_small hz ht
  have hout (x : E) (hx : x∉closedBall (0:E) 1) : x+t • z x=x := by
    have hxn : 1<‖x‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hx
    rw [hzero x hxn.le,smul_zero,add_zero]
  apply Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    by_contra hy
    have he : x+t • z x=x := hbi.1 (hout (x+t • z x) hy)
    exact hy (by change x+t • z x∈_; rw [he]; exact hx)
  · intro y hy
    obtain ⟨x,hxy⟩ := hbi.2 y
    refine ⟨x,?_,hxy⟩
    by_contra hx
    change x+t • z x=y at hxy
    rw [hout x hx] at hxy
    exact hx (hxy.symm ▸ hy)

end PettyProjection.FixedPoint
end

noncomputable section
open Set Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.FixedPoint

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma nearest_unique {K : Set E} {x p q : E}
    (hp : ∀ z ∈ K, ⟪x-p,z-p⟫ ≤ 0) (hq : ∀ z ∈ K, ⟪x-q,z-q⟫ ≤ 0)
    (hpK : p∈K) (hqK : q∈K) : p=q := by
  have h1 := hp q hqK
  have h2 := hq p hpK
  have he : ⟪x-p,q-p⟫+⟪x-q,p-q⟫ = ‖p-q‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hn : ‖p-q‖^2 ≤ 0 := by linarith
  have hz : ‖p-q‖=0 := by nlinarith [norm_nonneg (p-q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma nearest_mem (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hc : Convex ℝ K) (x : E) : nearest K hne hcomplete hc x∈K :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hcomplete hc x)).1

lemma nearest_inner (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hc : Convex ℝ K) (x : E) :
    ∀ z∈K, ⟪x-nearest K hne hcomplete hc x,z-nearest K hne hcomplete hc x⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hc (nearest_mem K hne hcomplete hc x)).mp
    (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hcomplete hc x)).2

lemma nearest_eq_of_mem (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hc : Convex ℝ K) {x : E} (hx : x∈K) : nearest K hne hcomplete hc x=x := by
  apply nearest_unique (nearest_inner K hne hcomplete hc x) _
    (nearest_mem K hne hcomplete hc x) hx
  intro z hz
  simp only [sub_self,inner_zero_left,le_refl]

lemma nearest_eq_of_inner (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hc : Convex ℝ K) {x p : E} (hp : p∈K)
    (hi : ∀ z∈K,⟪x-p,z-p⟫≤0) : nearest K hne hcomplete hc x=p :=
  nearest_unique (nearest_inner K hne hcomplete hc x) hi
    (nearest_mem K hne hcomplete hc x) hp

lemma nearest_lipschitz (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hc : Convex ℝ K) : LipschitzWith 1 (nearest K hne hcomplete hc) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let p := nearest K hne hcomplete hc x
  let q := nearest K hne hcomplete hc y
  have h1 := nearest_inner K hne hcomplete hc x q (nearest_mem K hne hcomplete hc y)
  have h2 := nearest_inner K hne hcomplete hc y p (nearest_mem K hne hcomplete hc x)
  change ⟪x-p,q-p⟫≤0 at h1
  change ⟪y-q,p-q⟫≤0 at h2
  have he : ⟪x-p,q-p⟫+⟪y-q,p-q⟫ = ‖p-q‖^2-⟪x-y,p-q⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right]
    ring
  have hle : ‖p-q‖^2 ≤ ‖x-y‖*‖p-q‖ := by
    have hcs := real_inner_le_norm (x-y) (p-q)
    linarith
  change dist p q ≤ (1:ℝ)*dist x y
  simp only [one_mul,dist_eq_norm]
  by_cases hz : ‖p-q‖=0
  · rw [hz]; exact norm_nonneg _
  · nlinarith [lt_of_le_of_ne (norm_nonneg (p-q)) (Ne.symm hz)]

variable [CompleteSpace E]

lemma ballNearest_mem (x : E) : ballNearest x∈closedBall (0:E) 1 :=
  nearest_mem _ _ _ _ x

lemma ballNearest_eq {x : E} (hx : ‖x‖≤1) : ballNearest x=x :=
  nearest_eq_of_mem _ _ _ _ (by simpa only [mem_closedBall,dist_zero_right] using hx)

lemma ballNearest_lipschitz : LipschitzWith 1 (ballNearest : E → E) :=
  nearest_lipschitz (closedBall (0:E) 1)
    (nonempty_closedBall.mpr (by norm_num)) isClosed_closedBall.isComplete (convex_closedBall _ _)

lemma ballNearest_norm {x : E} (hx : 1≤‖x‖) : ‖ballNearest x‖=1 := by
  have hx0 : ‖x‖≠0 := by linarith
  let p : E := ‖x‖⁻¹ • x
  have hp : ‖p‖=1 := by simp [p,norm_smul,hx0]
  have hxp : x=‖x‖ • p := by simp [p,hx0]
  have he : ballNearest x=p := by
    apply nearest_eq_of_inner (closedBall (0:E) 1) _ _ _
    · simpa only [mem_closedBall,dist_zero_right,hp] using le_rfl (a := (1:ℝ))
    · intro z hz
      have hsub : x-p=(‖x‖-1) • p := by rw [sub_smul,one_smul,← hxp]
      rw [hsub,inner_smul_left,inner_sub_right,real_inner_self_eq_norm_sq,hp]
      have hcs := real_inner_le_norm p z
      have hzn : ‖z‖≤1 := by simpa only [mem_closedBall,dist_zero_right] using hz
      have hi : ⟪p,z⟫-1≤0 := by rw [hp,one_mul] at hcs; linarith
      simpa using mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx) hi
  rw [he,hp]

end PettyProjection.FixedPoint
end

noncomputable section
open Set Metric Filter Topology MeasureTheory
open scoped RealInnerProductSpace NNReal
namespace PettyProjection.FixedPoint
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma ball_uniqueDiff : UniqueDiffOn ℝ (closedBall (0:E) 1) := by
  apply uniqueDiffOn_convex (convex_closedBall _ _)
  rw [interior_closedBall (0:E) (by norm_num : (1:ℝ)≠0)]
  exact nonempty_ball.mpr (by norm_num)

lemma sphere_derivative_det_zero {r : E → E} {r' : E → E →L[ℝ] E}
    (hd : ∀ x∈closedBall (0:E) 1, HasFDerivWithinAt r (r' x) (closedBall (0:E) 1) x)
    (hnorm : ∀ x∈closedBall (0:E) 1, ‖r x‖=1) {x : E} (hx : x∈closedBall (0:E) 1) :
    (r' x).det=0 := by
  have hi := (hd x hx).inner ℝ (hd x hx)
  have hc : HasFDerivWithinAt (fun y => ⟪r y,r y⟫) (0 : E →L[ℝ] ℝ)
      (closedBall (0:E) 1) x := by
    apply (hasFDerivWithinAt_const (1:ℝ) x (closedBall (0:E) 1)).congr
    · intro y hy
      change ⟪r y,r y⟫=1
      rw [real_inner_self_eq_norm_sq,hnorm y hy,one_pow]
    · rw [real_inner_self_eq_norm_sq,hnorm x hx,one_pow]
  have he := (ball_uniqueDiff x hx).eq hi hc
  have hort (v : E) : ⟪r x,r' x v⟫=0 := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L v) he
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply,zero_apply] at h
    have hsymm := real_inner_comm (r x) (r' x v)
    linarith
  change ((r' x) : E →ₗ[ℝ] E).det=0
  apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
  intro hker
  have hsurj := (LinearMap.injective_iff_surjective).mp (LinearMap.ker_eq_bot.mp hker)
  obtain ⟨v,hv⟩ := hsurj (r x)
  change r' x v=r x at hv
  have hz := hort v
  rw [hv,real_inner_self_eq_norm_sq,hnorm x hx] at hz
  norm_num at hz

lemma retraction_extension {r : E → E} {r' : E → E →L[ℝ] E}
    (hd : ∀ x∈closedBall (0:E) 1, HasFDerivWithinAt r (r' x) (closedBall (0:E) 1) x)
    (hc : ContinuousOn r' (closedBall (0:E) 1))
    (hb : ∀ x : E, ‖x‖=1 → r x=x) :
    ∃ (z : E → E) (C : ℝ≥0), LipschitzWith C z ∧
      (∀ x∈closedBall (0:E) 1, z x=r x-x) ∧ (∀ x,1≤‖x‖ → z x=0) := by
  have hcN := hc.nnnorm
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E) 1).bddAbove_image hcN
  have hr : LipschitzOnWith C r (closedBall (0:E) 1) :=
    (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hd
      (fun x hx => hC (mem_image_of_mem _ hx))
  let z : E → E := fun x => r (ballNearest x)-ballNearest x
  refine ⟨z,C+1,?_,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (z x) (z y) ≤ dist (r (ballNearest x)) (r (ballNearest y)) +
          dist (ballNearest x) (ballNearest y) := dist_sub_sub_le _ _ _ _
      _ ≤ C * dist (ballNearest x) (ballNearest y) + dist (ballNearest x) (ballNearest y) :=
        add_le_add (hr.dist_le_mul _ (ballNearest_mem x) _ (ballNearest_mem y)) le_rfl
      _ = (C+1:ℝ) * dist (ballNearest x) (ballNearest y) := by ring
      _ ≤ (C+1:ℝ) * dist x y := by
        gcongr
        simpa only [NNReal.coe_one,one_mul] using ballNearest_lipschitz.dist_le_mul x y
      _ = _ := by simp only [NNReal.coe_add,NNReal.coe_one]
  · intro x hx
    have he : ballNearest x=x := ballNearest_eq (by simpa only [mem_closedBall,dist_zero_right] using hx)
    simp only [z,he]
  · intro x hx
    simp only [z,hb _ (ballNearest_norm hx),sub_self]

end PettyProjection.FixedPoint
end

noncomputable section
open Set Metric Filter Topology MeasureTheory
open scoped RealInnerProductSpace NNReal
namespace PettyProjection.FixedPoint
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma eventually_pos_det_homotopy {A : E → E →L[ℝ] E} {K : Set E}
    (hK : IsCompact K) (hA : ContinuousOn A K) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ x∈K, 0<(t • A x+ContinuousLinearMap.id ℝ E).det := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hAc : Continuous (fun x : K => A x) := continuousOn_iff_continuous_domRestrict.mp hA
  have hL : Continuous (fun z : ℝ × K => z.1 • A z.2+ContinuousLinearMap.id ℝ E) := by
    exact continuous_add.comp ((continuous_smul.comp
      (continuous_fst.prodMk (hAc.comp continuous_snd))).prodMk continuous_const)
  have hD := ContinuousLinearMap.continuous_det.comp hL
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ x:K, 0<(t • A x+ContinuousLinearMap.id ℝ E).det := by
    have hh := (isCompact_univ : IsCompact (univ : Set K)).eventually_forall_of_forall_eventually
      (x₀ := (0:ℝ)) (P := fun t x => 0<(t • A x+ContinuousLinearMap.id ℝ E).det)
    apply Filter.Eventually.mono (hh ?_)
    · intro t ht x
      exact ht x (mem_univ x)
    · intro x hx
      apply (hD.continuousAt (x := (0,x))).eventually
      apply Ioi_mem_nhds
      simp [ContinuousLinearMap.det]
  filter_upwards [he] with t ht x hx
  exact ht ⟨x,hx⟩

/-- Milnor's elementary determinant-polynomial obstruction to a differentiable
retraction of a ball onto its sphere. Only Jacobian change of variables and the
Banach contraction principle are needed. -/
lemma no_smooth_retraction (μ : Measure E) [μ.IsAddHaarMeasure]
    {r : E → E} {r' : E → E →L[ℝ] E}
    (hd : ∀ x∈closedBall (0:E) 1, HasFDerivWithinAt r (r' x) (closedBall (0:E) 1) x)
    (hc : ContinuousOn r' (closedBall (0:E) 1))
    (hnorm : ∀ x∈closedBall (0:E) 1, ‖r x‖=1)
    (hb : ∀ x : E, ‖x‖=1 → r x=x) : False := by
  let K := closedBall (0:E) 1
  let I : E →L[ℝ] E := ContinuousLinearMap.id ℝ E
  obtain ⟨z,C,hz,hzK,hzout⟩ := retraction_extension hd hc hb
  have hzD (x : E) (hx : x∈K) : HasFDerivWithinAt z (r' x-I) K x := by
    apply ((hd x hx).sub (hasFDerivWithinAt_id x K)).congr
    · intro y hy
      exact hzK y hy
    · exact hzK x hx
  have hA : ContinuousOn (fun x => r' x-I) K := hc.sub continuousOn_const
  obtain ⟨p,hp⟩ := exists_integralOn_clm_det_polynomial μ (isCompact_closedBall (0:E) 1)
    (fun x => r' x-I) (fun _ => I) hA continuousOn_const
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖t‖₊*C<1 := by
    have hh : Continuous (fun t : ℝ => ‖t‖₊*C) := by fun_prop
    exact (hh.continuousAt (x := 0)).eventually (Iio_mem_nhds (by simp))
  have hpos := eventually_pos_det_homotopy (isCompact_closedBall (0:E) 1) hA
  have he : ∀ᶠ t : ℝ in 𝓝 0, p.eval t=μ.real K := by
    filter_upwards [hsmall,hpos] with t ht hpt
    rw [hp]
    have hFD (x : E) (hx : x∈K) :
        HasFDerivWithinAt (fun x => x+t • z x) (t • (r' x-I)+I) K x := by
      convert ((hzD x hx).const_smul t).add (hasFDerivWithinAt_id x K) using 1
      ext y
      simp only [Pi.add_apply,Pi.smul_apply,id_eq,add_comm]
    have hJac := integral_image_eq_integral_abs_det_fderiv_smul μ isClosed_closedBall.measurableSet
      hFD (bijective_add_small hz ht).1.injOn (fun _ : E => (1:ℝ))
    rw [image_closedBall_add_small hz hzout ht] at hJac
    have heq : (∫ x in K, |(t • (r' x-I)+I).det| • (1:ℝ) ∂μ) =
        ∫ x in K, (t • (r' x-I)+I).det ∂μ := by
      apply setIntegral_congr_fun isClosed_closedBall.measurableSet
      intro x hx
      change |(t • (r' x-I)+I).det| • (1:ℝ)=(t • (r' x-I)+I).det
      rw [abs_of_pos (hpt x hx)]
      simp only [smul_eq_mul,mul_one,I]
    rw [heq] at hJac
    simpa only [integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ,K] using hJac.symm
  have hpoly : p=Polynomial.C (μ.real K) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply infinite_of_mem_nhds (0:ℝ)
    change {t | p.eval t=μ.real K}∈𝓝 (0:ℝ) at he
    simpa only [Polynomial.eval_C] using he
  have hzero : p.eval 1=0 := by
    rw [hp]
    calc
      (∫ x in closedBall (0:E) 1, ((1:ℝ) • (r' x-I)+I).det ∂μ) =
          ∫ _ in closedBall (0:E) 1, (0:ℝ) ∂μ := by
        apply setIntegral_congr_fun isClosed_closedBall.measurableSet
        intro x hx
        change ((1:ℝ) • (r' x-I)+I).det=0
        simp only [one_smul,sub_add_cancel]
        exact sphere_derivative_det_zero hd hnorm hx
      _ = 0 := integral_zero _ _
  rw [hpoly,Polynomial.eval_C] at hzero
  have hpositive : 0<μ.real K := by
    exact ENNReal.toReal_pos (ne_of_gt (measure_closedBall_pos μ (0:E) zero_lt_one))
      (measure_closedBall_lt_top.ne)
  linarith

end PettyProjection.FixedPoint
end

noncomputable section
open Set Metric MeasureTheory
namespace PettyProjection.FixedPoint

/-- There is no retraction `r` of the closed unit ball of a finite-dimensional real inner product
space onto its unit sphere that is differentiable within the ball, with derivative `r'`
continuous on the ball. -/
theorem no_C1_retraction_closedBall_oai {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {r : E → E} {r' : E → E →L[ℝ] E}
    (hd : ∀ x ∈ closedBall (0:E) 1, HasFDerivWithinAt r (r' x) (closedBall (0:E) 1) x)
    (hc : ContinuousOn r' (closedBall (0:E) 1))
    (hnorm : ∀ x ∈ closedBall (0:E) 1, ‖r x‖ = 1)
    (hb : ∀ x : E, ‖x‖ = 1 → r x = x) : False := by
  borelize E
  exact no_smooth_retraction (Measure.addHaar : Measure E) hd hc hnorm hb

end PettyProjection.FixedPoint
end

end OAI
end

theorem solution.{uE} : type_of% @OAI.PettyProjection.FixedPoint.no_C1_retraction_closedBall_oai.{uE} := @OAI.PettyProjection.FixedPoint.no_C1_retraction_closedBall_oai.{uE}
