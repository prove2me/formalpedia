-- Prove2me | solution 1 for OAI.RVM.maxwell_timeContinuousL2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:36:26.475247+00:00
-- url     : https://prove2.me/submissions/cbde4d89-f883-4ac8-a471-d4342b31b62f

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_constructed_maxwell_equations

section
-- module Solutions.OAIQ073_VM.Compat
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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ExtendedLorentz
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma contDiff_cross {k : ℕ∞ω} : ContDiff ℝ k (fun z : Vec × Vec => cross z.1 z.2) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 1 * z.2 2 - z.1 2 * z.2 1)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 2 * z.2 0 - z.1 0 * z.2 2)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 0 * z.2 1 - z.1 1 * z.2 0)
    fun_prop

lemma sum_basis (v : Vec) : ∑ i : Fin 3, v i • basis i = v := by
  ext j
  simp [basis, Pi.single_apply]

lemma clm_sum_basis (L : Vec →L[ℝ] ℝ) (v : Vec) :
    L v = ∑ i : Fin 3, v i * L (basis i) := by
  conv_lhs => rw [← sum_basis v]
  simp only [map_sum, map_smul, smul_eq_mul]

lemma poynting_norm_le_energy (E B : Vec) :
    ‖cross E B‖ ≤ (‖E‖^2+‖B‖^2)/2 := by
  have h := norm_cross_le E B
  nlinarith [sq_nonneg (‖E‖-‖B‖)]

lemma spatialPartial_mul {f g : Vec → ℝ} {x : Vec}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialPartial (fun y => f y*g y) x i =
      f x*spatialPartial g x i+g x*spatialPartial f x i := by
  change fderiv ℝ (f*g) x (basis i) = _
  rw [fderiv_mul hf hg]
  rfl

lemma spatialPartial_sub {f g : Vec → ℝ} {x : Vec}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialPartial (fun y => f y-g y) x i =
      spatialPartial f x i-spatialPartial g x i := by
  change fderiv ℝ (f-g) x (basis i) = _
  rw [fderiv_sub hf hg]
  rfl

lemma divergence_cross {F G : Vec → Vec} {x : Vec}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => cross (F y) (G y)) x =
      dot (G x) (curl F x) - dot (F x) (curl G x) := by
  have hf (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hF
  have hg (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hG
  simp only [divergence, Fin.sum_univ_succ]
  change spatialPartial (fun y => F y 1 * G y 2 - F y 2 * G y 1) x 0 +
    (spatialPartial (fun y => F y 2 * G y 0 - F y 0 * G y 2) x 1 +
    (spatialPartial (fun y => F y 0 * G y 1 - F y 1 * G y 0) x 2+0)) = _
  have hm (i j k : Fin 3) :
      spatialPartial ((fun y => F y i) * (fun y => G y j)) x k =
        F x i * spatialPartial (fun y => G y j) x k +
        G x j * spatialPartial (fun y => F y i) x k :=
    spatialPartial_mul (hf i) (hg j) k
  have hs (i j k l r : Fin 3) := spatialPartial_sub ((hf i).mul (hg j)) ((hf k).mul (hg l)) r
  simp only [Pi.mul_apply] at hs
  simp only [hs, hm]
  simp [dot, curl, Fin.sum_univ_succ]
  ring

lemma hasDerivAt_field_energy {E B : ℝ → Vec} {e b : Vec} {t : ℝ}
    (he : HasDerivAt E e t) (hb : HasDerivAt B b t) :
    HasDerivAt (fun s => (‖E s‖^2+‖B s‖^2)/2)
      (dot (E t) e + dot (B t) b) t := by
  convert (he.norm_sq.add hb.norm_sq).div_const 2 using 1
  all_goals try with_reducible_and_instances rfl
  rw [← dot_eq_inner, ← dot_eq_inner]
  ring

lemma maxwell_energy_balance {E B : Field} {j : Vec} {t : ℝ} {x : Vec}
    (hE : DifferentiableAt ℝ E (t,x)) (hB : DifferentiableAt ℝ B (t,x))
    (he : deriv (fun s => E (s,x)) t - curl (fun y => B (t,y)) x = -j)
    (hb : deriv (fun s => B (s,x)) t + curl (fun y => E (t,y)) x = 0) :
    deriv (fun s => (‖E (s,x)‖^2+‖B (s,x)‖^2)/2) t +
      divergence (fun y => cross (E (t,y)) (B (t,y))) x = -dot (E (t,x)) j := by
  have heT : DifferentiableAt ℝ (fun s => E (s,x)) t :=
    hE.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hbT : DifferentiableAt ℝ (fun s => B (s,x)) t :=
    hB.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have heX : DifferentiableAt ℝ (fun y => E (t,y)) x :=
    hE.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hbX : DifferentiableAt ℝ (fun y => B (t,y)) x :=
    hB.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  rw [(hasDerivAt_field_energy heT.hasDerivAt hbT.hasDerivAt).deriv,
    divergence_cross heX hbX]
  have he' : deriv (fun s => E (s,x)) t = curl (fun y => B (t,y)) x-j := by
    apply sub_eq_iff_eq_add.mp at he
    simpa only [sub_eq_add_neg, add_comm] using he
  have hb' : deriv (fun s => B (s,x)) t = -curl (fun y => E (t,y)) x :=
    eq_neg_of_add_eq_zero_left hb
  rw [he', hb']
  simp only [dot, PiLp.sub_apply, PiLp.neg_apply, mul_sub, mul_neg,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleBySpacetime
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma integral_mul_spatialPartial {F g : Vec → ℝ}
    (hF : ContDiff ℝ 1 F) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (i : Fin 3) :
    (∫ v, F v * spatialPartial g v i) =
      -(∫ v, spatialPartial F v i * g v) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hF.continuous.mul
      ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (basis i)).mul_left
  · exact (hF.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact fun x _ => hF.differentiable (by simp) x
  · exact fun x _ => hg.differentiable (by simp) x

lemma hasFDerivAt_integral_uniform_support
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    HasFDerivAt (fun x => ∫ v : Vec, F (x,v))
      ((∫ v : Vec, fderiv ℝ F (p,v)).comp (ContinuousLinearMap.inl ℝ H Vec)) p := by
  have h := hasFDerivAt_convolution_right_with_param
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (g := fun x v => F (x,v)) hU hK (fun x v hx hv => hzero x hx v hv)
    (locallyIntegrable_const (1 : ℝ)) hF (p,0) hp
  have hi : HasFDerivAt (fun x : H => (x,(0 : Vec)))
      (ContinuousLinearMap.inl ℝ H Vec) p := by
    convert (hasFDerivAt_id p).prodMk (hasFDerivAt_const (0 : Vec) p) using 1 <;> rfl
  have hc := h.comp p hi
  have hls : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W) 1 =
      ContinuousLinearMap.id ℝ W := by ext w; simp
  change HasFDerivAt (fun x => convolution (fun _ => (1 : ℝ)) (fun v => F (x,v))
    (ContinuousLinearMap.lsmul ℝ ℝ) volume 0)
    ((convolution (fun _ => (1 : ℝ)) (fun v => fderiv ℝ F (p,v))
      (ContinuousLinearMap.precompR (H × Vec) (ContinuousLinearMap.lsmul ℝ ℝ)) volume 0).comp
      (ContinuousLinearMap.inl ℝ H Vec)) p at hc
  simp only [convolution_def, zero_sub, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply, hls,
    ContinuousLinearMap.id_comp] at hc
  have hn (x : H) : (∫ v : Vec, F (x,-v)) = ∫ v : Vec, F (x,v) :=
    integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  have hn' : (∫ v : Vec, fderiv ℝ F (p,-v)) = ∫ v : Vec, fderiv ℝ F (p,v) :=
    integral_neg_eq_self (fun v : Vec => fderiv ℝ F (p,v)) volume
  simpa only [hn, hn'] using hc

lemma compactSupport_of_zero_off {W : Type*} [Zero W]
    {K : Set Vec} {g : Vec → W} (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v = 0) : HasCompactSupport g := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro v hv
  by_contra hn
  exact hv (hz v hn)

lemma compactSupport_param_fderiv
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    HasCompactSupport (fun v : Vec => fderiv ℝ F (p,v)) := by
  apply compactSupport_of_zero_off hK
  intro v hv
  have hn : U ×ˢ Kᶜ ∈ 𝓝 (p,v) :=
    (hU.prod hK.isClosed.isOpen_compl).mem_nhds ⟨hp,hv⟩
  have hz : F =ᶠ[𝓝 (p,v)] (fun _ => 0) := by
    filter_upwards [hn] with y hy
    exact hzero y.1 hy.1 y.2 hy.2
  simpa only [fderiv_const_apply] using hz.fderiv_eq (𝕜 := ℝ)

lemma integrable_param_fderiv
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    Integrable (fun v : Vec => fderiv ℝ F (p,v)) := by
  have hc : Continuous (fun v : Vec => fderiv ℝ F (p,v)) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (compactSupport_param_fderiv hU hK hp hzero)

lemma fderiv_integral_uniform_support_apply
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) (b : H) :
    fderiv ℝ (fun x => ∫ v : Vec, F (x,v)) p b =
      ∫ v : Vec, fderiv ℝ F (p,v) (b,0) := by
  rw [(hasFDerivAt_integral_uniform_support hU hK hp hF hzero).fderiv]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using
    (ContinuousLinearMap.integral_apply (integrable_param_fderiv hU hK hp hF hzero) (b,0))

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_EnergyBump
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma deriv_time_slice {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {G : ℝ × Vec → W} {t : ℝ} {x : Vec} (hG : DifferentiableAt ℝ G (t,x)) :
    deriv (fun r => G (r,x)) t = fderiv ℝ G (t,x) (1,0) :=
  (hG.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

lemma spatialPartial_time_slice {G : ℝ × Vec → ℝ} {t : ℝ} {x : Vec}
    (hG : DifferentiableAt ℝ G (t,x)) (i : Fin 3) :
    spatialPartial (fun y => G (t,y)) x i = fderiv ℝ G (t,x) (0,basis i) := by
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i))
    (hG.hasFDerivAt.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))).fderiv

lemma continuousOn_integral_uniform_support
    {H W : Type*} [TopologicalSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W}
    (hK : IsCompact K) (hF : ContinuousOn F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    ContinuousOn (fun x => ∫ v : Vec, F (x,v)) U := by
  have h := continuousOn_convolution_right_with_param_comp
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (v := fun _ : H => (0 : Vec)) continuousOn_const (g := fun x v => F (x,v))
    hK (fun x v hx hv => hzero x hx v hv) (locallyIntegrable_const (1 : ℝ)) hF
  have hn (x : H) : convolution (fun _ : Vec => (1 : ℝ)) (fun v => F (x,v))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 = ∫ v : Vec, F (x,v) := by
    simp only [convolution_def, zero_sub, ContinuousLinearMap.lsmul_apply, one_smul]
    exact integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  simpa only [hn] using h

lemma integral_mul_divergence {F : Vec → Vec} {g : Vec → ℝ}
    (hF : ContDiff ℝ 1 F) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    (∫ x, g x * divergence F x) = -(∫ x, fderiv ℝ g x (F x)) := by
  have hFi (i : Fin 3) : ContDiff ℝ 1 (fun x => F x i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF
  have hI (i : Fin 3) : Integrable (fun x => g x * spatialPartial (fun y => F y i) x i) :=
    (hg.continuous.mul (((hFi i).continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport hc.mul_right
  have hJ (i : Fin 3) : Integrable (fun x => F x i * spatialPartial g x i) :=
    ((hFi i).continuous.mul ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (basis i)).mul_left
  simp only [divergence, Finset.mul_sum]
  conv_rhs => enter [1,2,x]; rw [clm_sum_basis]
  change (∫ x, ∑ i : Fin 3, g x * spatialPartial (fun y => F y i) x i) =
    -(∫ x, ∑ i : Fin 3, F x i * spatialPartial g x i)
  rw [integral_finsetSum _ (fun i _ => hI i), integral_finsetSum _ (fun i _ => hJ i)]
  simp_rw [mul_comm (g _) (spatialPartial _ _ _)]
  have he (i : Fin 3) : (∫ x, spatialPartial (fun y => F y i) x i * g x) =
      -(∫ x, F x i * spatialPartial g x i) := by
    have hh := integral_mul_spatialPartial (hFi i) hg hc i
    linarith
  simp only [he, Finset.sum_neg_distrib]

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM

lemma continuous_divergence {F : Vec → Vec} (hF : ContDiff ℝ 1 F) :
    Continuous (divergence F) := by
  unfold divergence spatialPartial
  apply continuous_finsetSum
  intro i _
  have hi : ContDiff ℝ 1 (fun x => F x i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF
  exact (hi.continuous_fderiv (by simp)).clm_apply continuous_const

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeArgument
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma contDiff_coneArgument (T ε : ℝ) (x₀ : Vec) {k : ℕ∞} :
    ContDiff ℝ k (coneArgument T ε x₀) :=
  ((contDiff_const.sub contDiff_fst).pow 2 |>.sub
    ((contDiff_snd.sub contDiff_const).norm_sq ℝ)).div_const ε

lemma contDiff_coneCutoff (T ε : ℝ) (x₀ : Vec) {k : ℕ∞} :
    ContDiff ℝ k (coneCutoff T ε x₀) :=
  Real.smoothTransition.contDiff.comp (contDiff_coneArgument T ε x₀)

lemma deriv_transition_nonneg (u : ℝ) : 0 ≤ deriv Real.smoothTransition u :=
  Real.smoothTransition.monotone.deriv_nonneg

lemma deriv_transition_zero_neg {u : ℝ} (hu : u < 0) :
    deriv Real.smoothTransition u = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    filter_upwards [gt_mem_nhds hu] with v hv
    exact Real.smoothTransition.zero_of_nonpos hv.le
  rw [he.deriv_eq,deriv_const]

lemma coneArgument_fderiv (T ε : ℝ) (x₀ : Vec) (p v : ℝ × Vec) :
    fderiv ℝ (coneArgument T ε x₀) p v =
      (-2*(T-p.1)*v.1 - 2*⟪p.2-x₀,v.2⟫)/ε := by
  have hd := (((hasFDerivAt_const T p).sub (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).pow 2).sub
    (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).sub (hasFDerivAt_const x₀ p)).norm_sq)
  have hh := hd.const_smul ε⁻¹
  have he : (fun y => ε⁻¹ • (((T-y.1)^2)-‖y.2-x₀‖^2)) = coneArgument T ε x₀ := by
    ext y
    simp [coneArgument,div_eq_mul_inv,mul_comm]
  change HasFDerivAt (fun y => ε⁻¹ • ((T-y.1)^2-‖y.2-x₀‖^2)) _ p at hh
  rw [he] at hh
  rw [hh.fderiv]
  simp [smul_eq_mul, div_eq_mul_inv, inner_sub_left]
  ring

lemma coneCutoff_fderiv (T ε : ℝ) (x₀ : Vec) (p v : ℝ × Vec) :
    fderiv ℝ (coneCutoff T ε x₀) p v =
      deriv Real.smoothTransition (coneArgument T ε x₀ p) *
        ((-2*(T-p.1)*v.1-2*⟪p.2-x₀,v.2⟫)/ε) := by
  have hθ := (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  have hg := (contDiff_coneArgument T ε x₀ (k := 1)).differentiable (by simp)
  have hh := (hθ (coneArgument T ε x₀ p)).hasDerivAt.comp_hasFDerivAt p (hg p).hasFDerivAt
  change HasFDerivAt (coneCutoff T ε x₀) _ p at hh
  rw [hh.fderiv]
  simpa [smul_eq_mul] using congrArg
    (fun c : ℝ => deriv Real.smoothTransition (coneArgument T ε x₀ p) * c)
    (coneArgument_fderiv T ε x₀ p v)

lemma coneArgument_neg_outside {T ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Icc 0 T)
    {x x₀ : Vec} (hx : x ∉ closedBall x₀ T) : coneArgument T ε x₀ (t,x) < 0 := by
  have hr : T < ‖x-x₀‖ := by simpa [mem_closedBall,dist_eq_norm] using hx
  dsimp [coneArgument]
  apply div_neg_of_neg_of_pos _ hε
  have hR : 0 ≤ T-t := sub_nonneg.mpr ht.2
  have he : T-t < ‖x-x₀‖ := lt_of_le_of_lt (sub_le_self _ ht.1) hr
  nlinarith [sq_lt_sq₀ hR (norm_nonneg (x-x₀)) |>.mpr he]

lemma coneCutoff_zero_outside {T ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Icc 0 T)
    {x x₀ : Vec} (hx : x ∉ closedBall x₀ T) : coneCutoff T ε x₀ (t,x) = 0 :=
  Real.smoothTransition.zero_of_nonpos (coneArgument_neg_outside hε ht hx).le

lemma sphere_norm (n : Sphere) : ‖n.1‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using n.2

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_BallCutoff
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma hasFDerivAt_integral_sphere
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} (hF : ContDiff ℝ 1 F) (p : H) :
    HasFDerivAt (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure)
      (∫ n : Sphere, (fderiv ℝ F (p,n.1)).comp (ContinuousLinearMap.inl ℝ H Vec)
        ∂sphereMeasure) p := by
  let D : H × Sphere → H →L[ℝ] W := fun z =>
    (fderiv ℝ F (z.1,z.2.1)).comp (ContinuousLinearMap.inl ℝ H Vec)
  have hD : Continuous D := by
    exact ((hF.continuous_fderiv (by simp)).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod isCompact_univ).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s:=closedBall p 1) (bound:=fun _ => C) (F':=fun x n => D (x,n))
    (closedBall_mem_nhds p (by norm_num))
  · exact Eventually.of_forall (fun x => (hF.continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun n x hx => hC _ ⟨(x,n),⟨hx,mem_univ n⟩,rfl⟩)
  · exact integrable_const _
  · exact ae_of_all _ (fun n x _ => (hF.differentiable (by simp) (x,n.1)).hasFDerivAt.comp x
      (by convert (hasFDerivAt_id x).prodMk (hasFDerivAt_const n.1 x) using 1 <;> rfl))

lemma continuous_integral_sphere
    {H W : Type*} [TopologicalSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : H × Vec → W} (hF : Continuous F) :
    Continuous (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) := by
  have hc : Continuous (fun p : H × Sphere => F (p.1,p.2.1)) :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hc.continuousOn
  intro x n _ hn
  exact (hn (mem_univ n)).elim

lemma contDiff_integral_sphere_nat
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    (k : ℕ) : ∀ {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W}, ContDiff ℝ k F →
      ContDiff ℝ k (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) := by
  induction k with
  | zero =>
    intro W _ _ _ F hF
    exact contDiff_zero.mpr (continuous_integral_sphere hF.continuous)
  | succ k ih =>
    intro W _ _ _ F hF
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast Nat.succ_pos k)
    let D : H × Vec → H →L[ℝ] W := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ H Vec)
    have hD : ContDiff ℝ k D :=
      ((contDiff_succ_iff_fderiv.mp hF).2.2).clm_comp contDiff_const
    have he : fderiv ℝ (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) =
        (fun x => ∫ n : Sphere, D (x,n.1) ∂sphereMeasure) := by
      funext x
      exact (hasFDerivAt_integral_sphere hF1 x).fderiv
    rw [show (↑(k+1) : ℕ∞ω) = ↑k+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_integral_sphere hF1 x).differentiableAt,?_,?_⟩
    · simp
    · rw [he]
      exact ih hD

lemma contDiff_integral_sphere
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) := by
  rw [contDiff_infty]
  intro k
  exact contDiff_integral_sphere_nat k (contDiff_infty.mp hF k)

lemma contDiff_sphereSum {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (sphereSum g) := by
  apply contDiff_integral_sphere (F:=fun p : (ℝ × Vec) × Vec => g (p.1.2+p.1.1 • p.2))
  exact hg.comp ((contDiff_snd.comp contDiff_fst).add
    ((contDiff_fst.comp contDiff_fst).smul contDiff_snd))

lemma sphereSum_radial_deriv {g : Vec → ℝ} (hg : ContDiff ℝ 1 g) (x : Vec) (r : ℝ) :
    HasDerivAt (fun t => sphereSum g (t,x))
      (∫ n : Sphere, fderiv ℝ g (x+r • n.1) n.1 ∂sphereMeasure) r := by
  let F : ℝ × Vec → ℝ := fun p => g (x+p.1 • p.2)
  have hF : ContDiff ℝ 1 F := hg.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))
  have hd := (hasFDerivAt_integral_sphere hF r).hasDerivAt
  have hDa (n : Sphere) : ((fderiv ℝ F (r,n.1)).comp
      (ContinuousLinearMap.inl ℝ ℝ Vec)) 1 = fderiv ℝ g (x+r • n.1) n.1 := by
    have hfst : HasFDerivAt (fun p : ℝ × Vec => p.1)
        (ContinuousLinearMap.fst ℝ ℝ Vec) (r,n.1) := hasFDerivAt_fst
    have hsnd : HasFDerivAt (fun p : ℝ × Vec => p.2)
        (ContinuousLinearMap.snd ℝ ℝ Vec) (r,n.1) := hasFDerivAt_snd
    have hi := (hasFDerivAt_const x (r,n.1)).add (hfst.smul hsnd)
    have he := ((hg.differentiable (by simp)) (x+r • n.1)).hasFDerivAt.comp (r,n.1) hi
    change HasFDerivAt F _ (r,n.1) at he
    rw [he.fderiv]
    simp
  have hc : Continuous (fun n : Sphere => (fderiv ℝ F (r,n.1)).comp
      (ContinuousLinearMap.inl ℝ ℝ Vec)) :=
    ((hF.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_subtype_val)).clm_comp continuous_const
  rw [ContinuousLinearMap.integral_apply (hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) 1] at hd
  simp_rw [hDa] at hd
  exact hd

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_WaveK
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiff_spatialPartial {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => spatialPartial g x i) :=
  ((contDiff_infty_iff_fderiv.mp hg).2).clm_apply contDiff_const

lemma sphere_area : sphereMeasure.real univ = 4*Real.pi := by
  rw [sphereMeasure,Measure.toSphere_real_apply_univ]
  simp only [Vec,finrank_euclideanSpace,Measure.real,EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3)]
  norm_num
  ring

lemma contDiff_waveK {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (waveK g) :=
  contDiff_const.mul (contDiff_fst.mul (contDiff_sphereSum hg))

lemma waveK_zero (g : Vec → ℝ) (x : Vec) : waveK g (0,x)=0 := by simp [waveK]

lemma waveK_initial_velocity {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec) :
    deriv (fun t => waveK g (t,x)) 0 = g x := by
  have hd := ((hasDerivAt_id (0:ℝ)).mul
    (sphereSum_radial_deriv (hg.of_le (by simp)) x 0)).const_mul ((4*Real.pi)⁻¹)
  change HasDerivAt (fun t => waveK g (t,x)) _ 0 at hd
  rw [hd.deriv]
  simp only [id_eq,one_mul,zero_mul,add_zero,sphereSum,zero_smul,add_zero,integral_const,
    smul_eq_mul,sphere_area]
  field_simp

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_ParamPrimitive
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma hasFDerivAt_intervalIntegral
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W} (hF : ContDiff ℝ 1 F) (a b : ℝ) (p : H) :
    HasFDerivAt (fun x => ∫ s in a..b, F (x,s))
      (∫ s in a..b, (fderiv ℝ F (p,s)).comp (ContinuousLinearMap.inl ℝ H ℝ)) p := by
  let D : H × ℝ → H →L[ℝ] W := fun z =>
    (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ H ℝ)
  have hD : Continuous D := (hF.continuous_fderiv (by simp)).clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod isCompact_uIcc).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s:=closedBall p 1) (bound:=fun _ => C) (F':=fun x s => D (x,s))
    (closedBall_mem_nhds p (by norm_num))
  · exact Eventually.of_forall (fun x => (hF.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    intro x hx
    exact hC _ ⟨(x,s),⟨hx,uIoc_subset_uIcc hs⟩,rfl⟩
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun s x _ => (hF.differentiable (by simp) (x,s)).hasFDerivAt.comp x
      (by convert (hasFDerivAt_id x).prodMk (hasFDerivAt_const s x) using 1 <;> rfl))

lemma contDiff_intervalIntegral_nat
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    (k : ℕ) : ∀ {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W}, ContDiff ℝ ∞ F → ∀ a b,
      ContDiff ℝ k (fun x => ∫ s in a..b, F (x,s)) := by
  induction k with
  | zero =>
    intro W _ _ _ F hF a b
    have hd : Differentiable ℝ (fun x => ∫ s in a..b, F (x,s)) :=
      fun x => (hasFDerivAt_intervalIntegral (hF.of_le (by simp)) a b x).differentiableAt
    exact contDiff_zero.mpr hd.continuous
  | succ k ih =>
    intro W _ _ _ F hF a b
    let D : H × ℝ → H →L[ℝ] W := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ H ℝ)
    have hD : ContDiff ℝ ∞ D :=
      (contDiff_infty_iff_fderiv.mp hF).2.clm_comp contDiff_const
    have he : fderiv ℝ (fun x => ∫ s in a..b, F (x,s)) =
        (fun x => ∫ s in a..b, D (x,s)) := by
      funext x
      exact (hasFDerivAt_intervalIntegral (hF.of_le (by simp)) a b x).fderiv
    rw [show (↑(k+1) : ℕ∞ω) = ↑k+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_intervalIntegral (hF.of_le (by simp)) a b x).differentiableAt,?_,?_⟩
    · simp
    · rw [he]
      exact ih hD a b

lemma contDiff_intervalIntegral
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ s in a..b, F (x,s)) := by
  rw [contDiff_infty]
  intro k
  exact contDiff_intervalIntegral_nat k hF a b

lemma paramPrimitive_scale {H W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : H × ℝ → W) (p : ℝ × H) :
    paramPrimitive F p = p.1 • ∫ u in (0:ℝ)..1, F (p.2,p.1*u) := by
  simpa [paramPrimitive] using (intervalIntegral.smul_integral_comp_mul_left (fun s => F (p.2,s)) p.1
    (a:=0) (b:=1)).symm

lemma contDiff_paramPrimitive
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (paramPrimitive F) := by
  have he : paramPrimitive F = fun p => p.1 • ∫ u in (0:ℝ)..1, F (p.2,p.1*u) :=
    funext (paramPrimitive_scale F)
  rw [he]
  apply contDiff_fst.smul
  apply contDiff_intervalIntegral (F:=fun z : (ℝ × H) × ℝ => F (z.1.2,z.1.1*z.2))
  exact hF.comp ((contDiff_snd.comp contDiff_fst).prodMk
    ((contDiff_fst.comp contDiff_fst).mul contDiff_snd))

lemma contDiff_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : H → W}
    (hF : ContDiff ℝ ∞ F) (e : H) : ContDiff ℝ ∞ (dirD F e) :=
  (contDiff_infty_iff_fderiv.mp hF).2.clm_apply contDiff_const

lemma deriv_slice_eq_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ × H → W}
    (hF : Differentiable ℝ F) (t : ℝ) (x : H) :
    deriv (fun r => F (r,x)) t = dirD F (1,0) (t,x) := by
  exact ((hF (t,x)).hasFDerivAt.comp t
    ((hasFDerivAt_id (𝕜:=ℝ) t).prodMk (hasFDerivAt_const (𝕜:=ℝ) x t))).hasDerivAt.deriv

lemma contDiff_volterra {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    {F : (ℝ × H) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (volterra F) :=
  (contDiff_paramPrimitive hF).comp (contDiff_fst.prodMk contDiff_id)

lemma contDiff_sourceWaveKernel {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (sourceWaveKernel ρ) := by
  have hF : ContDiff ℝ ∞ (fun z : ((ℝ × Vec) × ℝ) × Vec =>
      ρ (z.1.2,z.1.1.2+(z.1.1.1-z.1.2) • z.2)) := by
    apply hρ.comp
    apply (contDiff_snd.comp contDiff_fst).prodMk
    apply (contDiff_snd.comp (contDiff_fst.comp contDiff_fst)).add
    exact ((contDiff_fst.comp (contDiff_fst.comp contDiff_fst)).sub
      (contDiff_snd.comp contDiff_fst)).smul contDiff_snd
  exact contDiff_const.mul (((contDiff_fst.comp contDiff_fst).sub contDiff_snd).mul
    (contDiff_integral_sphere hF))

lemma contDiff_sourceWave {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (sourceWave ρ) := contDiff_volterra (contDiff_sourceWaveKernel hρ)

lemma sourceWave_initial_value (ρ : ℝ × Vec → ℝ) (x : Vec) :
    sourceWave ρ (0,x) = 0 := by simp [sourceWave,volterra]

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace


lemma contDiff_component {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → Vec} (hF : ContDiff ℝ ∞ F) (i : Fin 3) : ContDiff ℝ ∞ (fun x => F x i) :=
  (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF

lemma contDiff_divergence {F : Vec → Vec} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (divergence F) := by
  exact ContDiff.sum (fun i _ => contDiff_spatialPartial (contDiff_component hF i) i)

lemma contDiff_curl {F : Vec → Vec} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (curl F) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> exact (contDiff_spatialPartial (contDiff_component hF _) _).sub
    (contDiff_spatialPartial (contDiff_component hF _) _)

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace


lemma deriv_moving_local_energy {e : ℝ × Vec → ℝ} {S : ℝ × Vec → Vec}
    {U : Set ℝ} (hU : IsOpen U)
    (he : ContDiffOn ℝ 1 e (U ×ˢ (univ : Set Vec)))
    (hSg : ContDiffOn ℝ 1 S (U ×ˢ (univ : Set Vec)))
    (hcons : ∀ t ∈ U, ∀ x, deriv (fun r => e (r,x)) t + divergence (fun y => S (t,y)) x = 0)
    {g : ℝ × Vec → ℝ} {K : Set Vec} (hK : IsCompact K)
    (hg : ContDiffOn ℝ 1 g (U ×ˢ (univ : Set Vec)))
    (hz : ∀ r ∈ U, ∀ x ∉ K, g (r,x)=0)
    {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (fun r => ∫ x : Vec, g (r,x) * e (r,x))
      (∫ x : Vec, fderiv ℝ g (t,x) (1,0) * e (t,x) +
        fderiv ℝ g (t,x) (0,S (t,x))) t := by
  have hE := he
  have hF : ContDiffOn ℝ 1 (fun p => g p * e p)
      (U ×ˢ (univ : Set Vec)) := hg.mul hE
  have hzF : ∀ r ∈ U, ∀ x ∉ K, g (r,x)*e (r,x)=0 := by
    intro r hr x hx
    rw [hz r hr x hx,zero_mul]
  have hd := hasFDerivAt_integral_uniform_support hU hK ht hF hzF
  have hi := fderiv_integral_uniform_support_apply hU hK ht hF hzF (1:ℝ)
  have hgg : ContDiff ℝ 1 (fun x => g (t,x)) := by
    apply ContDiffOn.comp_contDiff hg (contDiff_const.prodMk contDiff_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hS : ContDiff ℝ 1 (fun x => S (t,x)) := by
    apply ContDiffOn.comp_contDiff hSg
      (contDiff_const.prodMk contDiff_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hEc : Continuous (fun x => e (t,x)) := by
    apply hE.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hgD : Continuous (fun x => fderiv ℝ g (t,x)) := by
    apply (hg.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) (by simp)).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hDc : HasCompactSupport (fun x => fderiv ℝ g (t,x)) :=
    compactSupport_param_fderiv hU hK ht hz
  have hgC : HasCompactSupport (fun x => g (t,x)) :=
    compactSupport_of_zero_off hK (hz t ht)
  have hgDapply (v : ℝ × Vec) : HasCompactSupport (fun x => fderiv ℝ g (t,x) v) := by
    apply compactSupport_of_zero_off hDc
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_apply]
  have hIt : Integrable (fun x => fderiv ℝ g (t,x) (1,0) * e (t,x)) :=
    ((hgD.clm_apply continuous_const).mul hEc).integrable_of_hasCompactSupport
      (hgDapply (1,0)).mul_right
  have hIa : Integrable (fun x => g (t,x) * divergence (fun y => S (t,y)) x) :=
    (hgg.continuous.mul (continuous_divergence hS)).integrable_of_hasCompactSupport hgC.mul_right
  have hIs : Integrable (fun x => fderiv ℝ (fun y => g (t,y)) x (S (t,x))) :=
    ((hgg.continuous_fderiv (by simp)).clm_apply hS.continuous).integrable_of_hasCompactSupport
      (compactSupport_of_zero_off (hgC.fderiv ℝ) (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx,zero_apply]))
  have heq : ∀ x : Vec,
      fderiv ℝ (fun p => g p * e p) (t,x) (1,0) =
        fderiv ℝ g (t,x) (1,0) * e (t,x) -
          g (t,x) * divergence (fun y => S (t,y)) x := by
    intro x
    have hn : U ×ˢ (univ : Set Vec) ∈ 𝓝 (t,x) :=
      (hU.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩
    have hg' := (hg.contDiffAt hn).differentiableAt (by simp)
    have hE' := (hE.contDiffAt hn).differentiableAt (by simp)
    change fderiv ℝ (g * e) (t,x) (1,0) = _
    rw [fderiv_mul hg' hE',add_apply,
      smul_apply,smul_apply,
      smul_eq_mul,smul_eq_mul,← deriv_time_slice hE']
    have hl := hcons t ht x
    rw [show deriv (fun r => e (r,x)) t =
      -divergence (fun y => S (t,y)) x by linarith]
    ring
  have hxder (x v : Vec) : fderiv ℝ (fun y => g (t,y)) x v = fderiv ℝ g (t,x) (0,v) := by
    have hn : U ×ˢ (univ : Set Vec) ∈ 𝓝 (t,x) :=
      (hU.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩
    have hh := ((hg.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    change HasFDerivAt (fun y => g (t,y)) _ x at hh
    rw [hh.fderiv]
    simp
  have hh : deriv (fun r => ∫ x : Vec, g (r,x) * e (r,x)) t =
      ∫ x : Vec, fderiv ℝ g (t,x) (1,0) * e (t,x) +
        fderiv ℝ g (t,x) (0,S (t,x)) := by
    change fderiv ℝ (fun r => ∫ x : Vec, g (r,x) * e (r,x)) t 1 = _
    rw [hi]
    simp only [heq]
    rw [integral_sub hIt hIa,integral_mul_divergence hS hgg hgC,sub_neg_eq_add]
    simp_rw [← hxder]
    exact (integral_add hIt hIs).symm
  exact hh ▸ hd.differentiableAt.hasDerivAt
lemma cone_energy_integrand_nonpos {R ε t : ℝ} {e : ℝ} {S : Vec}
    (hε : 0 < ε) (ht : t ≤ R) (he : 0 ≤ e) (hS : ‖S‖ ≤ e) (x x₀ : Vec) :
    fderiv ℝ (coneCutoff R ε x₀) (t,x) (1,0) * e +
      fderiv ℝ (coneCutoff R ε x₀) (t,x) (0,S) ≤ 0 := by
  rw [coneCutoff_fderiv,coneCutoff_fderiv]
  simp only [inner_zero_right,mul_zero,mul_one,sub_zero,zero_sub]
  have heq : deriv Real.smoothTransition (coneArgument R ε x₀ (t,x)) *
      ((-2*(R-t))/ε) * e + deriv Real.smoothTransition (coneArgument R ε x₀ (t,x)) *
      (-(2*⟪x-x₀,S⟫)/ε) =
      -((2/ε)*deriv Real.smoothTransition (coneArgument R ε x₀ (t,x)) *
      ((R-t)*e+⟪x-x₀,S⟫)) := by ring
  rw [heq]
  apply neg_nonpos.mpr
  by_cases hr : ‖x-x₀‖ ≤ R-t
  · apply mul_nonneg (mul_nonneg (by positivity) (deriv_transition_nonneg _))
    have hc := real_inner_le_norm (-(x-x₀)) S
    simp only [inner_neg_left,norm_neg] at hc
    nlinarith [mul_le_mul_of_nonneg_left hS (norm_nonneg (x-x₀)),
      mul_le_mul_of_nonneg_right hr he]
  · have hn : coneArgument R ε x₀ (t,x) < 0 := by
      dsimp [coneArgument]
      apply div_neg_of_neg_of_pos _ hε
      have hR : 0 ≤ R-t := sub_nonneg.mpr ht
      push Not at hr
      nlinarith [sq_lt_sq₀ hR (norm_nonneg (x-x₀)) |>.mpr hr]
    simp [deriv_transition_zero_neg hn]

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_WaveGradient
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma dirD_component {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → Vec} (hF : Differentiable ℝ F) (p e : H) (i : Fin 3) :
    dirD (fun z => F z i) e p = dirD F e p i := by
  have h := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp p (hF p).hasFDerivAt
  change HasFDerivAt (fun z => F z i) _ p at h
  unfold dirD
  rw [h.fderiv]
  rfl

lemma contDiff_waveGradient {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (waveGradient u) := by
  apply contDiff_euclidean.mpr
  intro i
  exact contDiff_dirD hu (0,basis i)

lemma contDiff_freeWave {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (freeWave g h) :=
  (contDiff_dirD (contDiff_waveK hg) (1,0)).add (contDiff_waveK hh)

lemma freeWave_initial {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec) :
    freeWave g h (0,x)=g x := by
  rw [freeWave,← deriv_slice_eq_dirD ((contDiff_waveK hg).differentiable (by simp)),
    waveK_initial_velocity hg,waveK_zero,add_zero]

lemma spaceCurl_apply (F : Field) (p : ℝ × Vec) (i : Fin 3) :
    spaceCurl F p i = dirD F (0,basis (curlA i)) p (curlB i) -
      dirD F (0,basis (curlB i)) p (curlA i) := rfl

lemma contDiff_spaceCurl {F : Field} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (spaceCurl F) := by
  apply contDiff_euclidean.mpr
  intro i
  exact (contDiff_component (contDiff_dirD hF _) _).sub
    (contDiff_component (contDiff_dirD hF _) _)

lemma spaceCurl_slice {F : Field} (hF : Differentiable ℝ F) (t : ℝ) (x : Vec) :
    spaceCurl F (t,x) = curl (fun y => F (t,y)) x := by
  have hc (i : Fin 3) : Differentiable ℝ (fun p => F p i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiable.comp hF
  have hh (i j : Fin 3) : spatialPartial (fun y => F (t,y) i) x j =
      dirD F (0,basis j) (t,x) i := by
    rw [spatialPartial_time_slice (hc i (t,x))]
    exact dirD_component hF (t,x) (0,basis j) i
  ext i
  fin_cases i <;> simp [spaceCurl_apply,curl,curlA,curlB,hh]

lemma contDiff_field_slice {F : Field} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => F (t,x)) := hF.comp (contDiff_const.prodMk contDiff_id)

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_SpaceDiv
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma contDiff_freeField {G H : Vec → Vec}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (freeField G H) := by
  apply contDiff_euclidean.mpr
  intro i
  exact contDiff_freeWave (contDiff_component hG i) (contDiff_component hH i)

lemma freeField_initial {G H : Vec → Vec} (hG : ContDiff ℝ ∞ G) (x : Vec) :
    freeField G H (0,x)=G x := by
  ext i
  exact freeWave_initial (contDiff_component hG i) x

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceField
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma contDiff_sourceField {J : Field} (hJ : ContDiff ℝ ∞ J) :
    ContDiff ℝ ∞ (sourceField J) := by
  apply contDiff_euclidean.mpr
  intro i
  exact contDiff_sourceWave (contDiff_component hJ i)

lemma sourceField_initial (J : Field) (x : Vec) : sourceField J (0,x)=0 := by
  ext i
  exact sourceWave_initial_value (fun p => J p i) x

lemma contDiff_maxwellElectric {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j) :
    ContDiff ℝ ∞ (maxwellElectric E₀ B₀ ρ j) :=
  (contDiff_freeField hE ((contDiff_curl hB).sub (contDiff_field_slice hj 0))).add
    (contDiff_sourceField ((contDiff_waveGradient hρ).neg.sub (contDiff_dirD hj _)))

lemma contDiff_maxwellMagnetic {E₀ B₀ : Vec → Vec} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀) (hj : ContDiff ℝ ∞ j) :
    ContDiff ℝ ∞ (maxwellMagnetic E₀ B₀ j) :=
  (contDiff_freeField hB (contDiff_curl hE).neg).add
    (contDiff_sourceField (contDiff_spaceCurl hj))

lemma maxwellElectric_initial {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (x : Vec) : maxwellElectric E₀ B₀ ρ j (0,x)=E₀ x := by
  simp only [maxwellElectric,freeField_initial hE,sourceField_initial,add_zero]

lemma maxwellMagnetic_initial {E₀ B₀ : Vec → Vec} {j : Field}
    (hB : ContDiff ℝ ∞ B₀) (x : Vec) : maxwellMagnetic E₀ B₀ j (0,x)=B₀ x := by
  simp only [maxwellMagnetic,freeField_initial hB,sourceField_initial,add_zero]

lemma causal_local_energy_bound {e : ℝ × Vec → ℝ} {S : Field} {T R ε : ℝ}
    (he : ContDiff ℝ ∞ e) (hS : ContDiff ℝ ∞ S)
    (hT : 0 ≤ T) (hR : T ≤ R) (hε : 0<ε)
    (he0 : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ e (t,x))
    (hflux : ∀ t ∈ Ioo 0 T, ∀ x, ‖S (t,x)‖ ≤ e (t,x))
    (hcons : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun r => e (r,x)) t+divergence (fun y => S (t,y)) x=0)
    (x₀ : Vec) :
    (∫ x : Vec, coneCutoff R ε x₀ (T,x)*e (T,x))  ≤
      ∫ x : Vec, coneCutoff R ε x₀ (0,x)*e (0,x) := by
  let g := coneCutoff R ε x₀
  let G : ℝ → ℝ := fun t => ∫ x : Vec, g (t,x)*e (t,x)
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 R := fun t ht => ⟨ht.1,ht.2.trans hR⟩
  have hgc : ContDiff ℝ 1 g := contDiff_coneCutoff R ε x₀
  have hgz : ∀ t ∈ Icc 0 T, ∀ x ∉ closedBall x₀ R, g (t,x)=0 := by
    intro t ht x hx
    exact coneCutoff_zero_outside hε (hsub ht) hx
  have hGc : ContinuousOn G (Icc 0 T) := by
    apply continuousOn_integral_uniform_support (isCompact_closedBall x₀ R)
      (hgc.continuous.continuousOn.mul he.continuous.continuousOn)
    intro t ht x hx
    change g (t,x)*e (t,x)=0
    rw [hgz t ht x hx,zero_mul]
  have hder (t : ℝ) (ht : t ∈ Ioo 0 T) :=
    deriv_moving_local_energy isOpen_Ioo (he.of_le (by simp)).contDiffOn
      (hS.of_le (by simp)).contDiffOn hcons (isCompact_closedBall x₀ R) hgc.contDiffOn
      (fun r hr x hx => hgz r ⟨hr.1.le,hr.2.le⟩ x hx) ht
  have hanti : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hGc
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hder t ht).deriv]
      apply integral_nonpos
      intro x
      exact cone_energy_integrand_nonpos hε (hsub ⟨ht.1.le,ht.2.le⟩).2
        (he0 t ⟨ht.1.le,ht.2.le⟩ x) (hflux t ht x) x x₀
  exact hanti ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT

lemma coneCutoff_one_on_ball {T r : ℝ} (hr : 0 ≤ r) {x : Vec}
    (hx : x ∈ closedBall (0:Vec) r) : coneCutoff (T+r+1) 1 0 (T,x)=1 := by
  apply Real.smoothTransition.one_of_one_le
  have hn : ‖x‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
  dsimp [coneArgument]
  simp only [sub_zero,div_one]
  nlinarith [sq_le_sq₀ (norm_nonneg x) hr |>.mpr hn]

lemma causal_energy_integrable {e : ℝ × Vec → ℝ} {S : Field} {T : ℝ}
    (he : ContDiff ℝ ∞ e) (hS : ContDiff ℝ ∞ S) (hT : 0 ≤ T)
    (he0 : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ e (t,x))
    (hflux : ∀ t ∈ Ioo 0 T, ∀ x, ‖S (t,x)‖ ≤ e (t,x))
    (hcons : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun r => e (r,x)) t+divergence (fun y => S (t,y)) x=0)
    (hinit : Integrable (fun x => e (0,x))) :
    Integrable (fun x => e (T,x)) ∧ (∫ x : Vec, e (T,x)) ≤ ∫ x : Vec, e (0,x) := by
  have hball (n : ℕ) : (∫ x in closedBall (0:Vec) (n:ℝ), e (T,x))  ≤  ∫ x : Vec, e (0,x) := by
    let R : ℝ := T+(n:ℝ)+1
    let g := coneCutoff R 1 (0:Vec)
    have hR : T ≤ R := by dsimp [R]; linarith [Nat.cast_nonneg (α:=ℝ) n]
    have hgC (t : ℝ) (ht : t∈Icc 0 T) : HasCompactSupport (fun x => g (t,x)) :=
      compactSupport_of_zero_off (isCompact_closedBall (0:Vec) R)
        (fun x hx => coneCutoff_zero_outside (by norm_num) ⟨ht.1,ht.2.trans hR⟩ hx)
    have hgc (t : ℝ) : Continuous (fun x => g (t,x)) :=
      (contDiff_coneCutoff R 1 (0:Vec) (k:=1)).continuous.comp (continuous_const.prodMk continuous_id)
    have hI (t : ℝ) (ht : t∈Icc 0 T) : Integrable (fun x => g (t,x)*e (t,x)) :=
      ((hgc t).mul (he.continuous.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
        (hgC t ht).mul_right
    calc
      _ = ∫ x in closedBall (0:Vec) (n:ℝ), g (T,x)*e (T,x) := by
        apply setIntegral_congr_fun isClosed_closedBall.measurableSet
        intro x hx
        change e (T,x)=g (T,x)*e (T,x)
        rw [show g (T,x)=1 from coneCutoff_one_on_ball (Nat.cast_nonneg n) hx,one_mul]
      _  ≤  ∫ x : Vec, g (T,x)*e (T,x) :=
        setIntegral_le_integral (hI T ⟨hT,le_rfl⟩) (ae_of_all _ (fun x =>
          mul_nonneg (Real.smoothTransition.nonneg _) (he0 T ⟨hT,le_rfl⟩ x)))
      _  ≤  ∫ x : Vec, g (0,x)*e (0,x) :=
        causal_local_energy_bound he hS hT hR (by norm_num) he0 hflux hcons 0
      _  ≤  ∫ x : Vec, e (0,x) := by
        apply integral_mono (hI 0 ⟨le_rfl,hT⟩) hinit
        intro x
        exact mul_le_of_le_one_left (he0 0 ⟨le_rfl,hT⟩ x) (Real.smoothTransition.le_one _)
  have hcov : AECover (volume : Measure Vec) atTop (fun n : ℕ => closedBall (0:Vec) (n:ℝ)) :=
    aecover_closedBall tendsto_natCast_atTop_atTop
  have hIt : Integrable (fun x => e (T,x)) :=
    hcov.integrable_of_integral_bounded_of_nonneg_ae (∫ x : Vec, e (0,x))
      (fun _ => (he.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)) (ae_of_all _ (he0 T ⟨hT,le_rfl⟩)) (Eventually.of_forall hball)
  exact ⟨hIt,le_of_tendsto (hcov.integral_tendsto_of_countably_generated hIt) (Eventually.of_forall hball)⟩

lemma divergence_neg (F : Vec → Vec) (x : Vec) :
    divergence (fun y => -F y) x= -divergence F x := by
  simp only [divergence,PiLp.neg_apply,spatialPartial,fderiv_fun_neg,neg_apply,
    Finset.sum_neg_distrib]

lemma causal_energy_conserved {e : ℝ × Vec → ℝ} {S : Field} {T : ℝ}
    (he : ContDiff ℝ ∞ e) (hS : ContDiff ℝ ∞ S) (hT : 0 ≤ T)
    (he0 : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ e (t,x))
    (hflux : ∀ t ∈ Ioo 0 T, ∀ x, ‖S (t,x)‖ ≤ e (t,x))
    (hcons : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun r => e (r,x)) t+divergence (fun y => S (t,y)) x=0)
    (hinit : Integrable (fun x => e (0,x))) :
    Integrable (fun x => e (T,x)) ∧ (∫ x : Vec, e (T,x))=∫ x : Vec, e (0,x) := by
  obtain ⟨hIt,hle⟩ := causal_energy_integrable he hS hT he0 hflux hcons hinit
  let R : ℝ × Vec → ℝ × Vec := fun p => (T-p.1,p.2)
  have hR : ContDiff ℝ ∞ R := (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  have hrev : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun r => e (T-r,x)) t+divergence (fun y => -S (T-t,y)) x=0 := by
    intro t ht x
    have hdt := ((he.differentiable (by simp)).comp
      (differentiable_id.prodMk (differentiable_const x)) (T-t)).hasDerivAt
    have hh := hdt.comp t ((hasDerivAt_id t).const_sub T)
    change HasDerivAt (fun r => e (T-r,x)) (deriv (fun r => e (r,x)) (T-t) * (-1)) t at hh
    rw [hh.deriv,divergence_neg]
    have hhcons := hcons (T-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩ x
    dsimp only [Function.comp_def] at *
    linarith
  have hrevi : Integrable (fun x => e (T-(0:ℝ),x)) := by simpa using hIt
  have hy := causal_energy_integrable (he.comp hR) (hS.comp hR).neg hT
    (fun t ht x => he0 (T-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩ x)
    (fun t ht x => by
      simpa only [Function.comp_def,R,norm_neg] using
        (hflux (T-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩ x))
    hrev hrevi
  refine ⟨hIt,le_antisymm hle ?_⟩
  simpa only [Function.comp_def,R,sub_self,sub_zero] using hy.2

lemma contDiff_maxwellEnergy {E B : Field} (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (maxwellEnergy E B) := ((hE.norm_sq ℝ).add (hB.norm_sq ℝ)).div_const 2

lemma contDiff_maxwellFlux {E B : Field} (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (maxwellFlux E B) := contDiff_cross.comp (hE.prodMk hB)

lemma maxwellEnergy_nonneg (E B : Field) (p : ℝ × Vec) : 0  ≤  maxwellEnergy E B p := by
  unfold maxwellEnergy; positivity

lemma maxwellFlux_le (E B : Field) (p : ℝ × Vec) : ‖maxwellFlux E B p‖  ≤  maxwellEnergy E B p :=
  poynting_norm_le_energy (E p) (B p)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_DifferenceFieldEnergy
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM
lemma vacuum_energy_conservation {E B : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hfirst : ∀ t, 0 ≤ t → ∀ x, dirD E (1,0) (t,x)=spaceCurl B (t,x) ∧
      dirD B (1,0) (t,x)= -spaceCurl E (t,x))
    (hE0 : MemLp (fun x => E (0,x)) 2 volume) (hB0 : MemLp (fun x => B (0,x)) 2 volume)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => maxwellEnergy E B (t,x)) ∧
    (∫ x : Vec, maxwellEnergy E B (t,x))=∫ x : Vec, maxwellEnergy E B (0,x) := by
  apply causal_energy_conserved (contDiff_maxwellEnergy hE hB) (contDiff_maxwellFlux hE hB) ht
    (fun _ _ _ => maxwellEnergy_nonneg _ _ _)
    (fun _ _ _ => maxwellFlux_le _ _ _) (fun r hr x => ?_)
    (((memLp_two_iff_integrable_sq_norm hE0.aestronglyMeasurable).mp hE0).add
      ((memLp_two_iff_integrable_sq_norm hB0.aestronglyMeasurable).mp hB0) |>.div_const 2)
  have h1 := (hfirst r hr.1.le x).1
  have h2 := (hfirst r hr.1.le x).2
  have hh := maxwell_energy_balance (hE.differentiable (by simp) (r,x))
    (hB.differentiable (by simp) (r,x)) (j:=0) (by
      rw [deriv_slice_eq_dirD (hE.differentiable (by simp)),
        ← spaceCurl_slice (hB.differentiable (by simp)),h1,sub_self,neg_zero]) (by
      rw [deriv_slice_eq_dirD (hB.differentiable (by simp)),
        ← spaceCurl_slice (hE.differentiable (by simp)),h2,neg_add_cancel])
  simpa only [maxwellEnergy,maxwellFlux,dot,PiLp.zero_apply,mul_zero,Finset.sum_const_zero,neg_zero] using hh

lemma vacuum_memLp {E B : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hfirst : ∀ t, 0 ≤ t → ∀ x, dirD E (1,0) (t,x)=spaceCurl B (t,x) ∧
      dirD B (1,0) (t,x)= -spaceCurl E (t,x))
    (hE0 : MemLp (fun x => E (0,x)) 2 volume) (hB0 : MemLp (fun x => B (0,x)) 2 volume)
    {t : ℝ} (ht : 0 ≤ t) : MemLp (fun x => E (t,x)) 2 volume ∧ MemLp (fun x => B (t,x)) 2 volume := by
  have hI := ((vacuum_energy_conservation hE hB hfirst hE0 hB0 ht).1).const_mul 2
  have hEc : Continuous (fun x : Vec => E (t,x)) :=
    hE.continuous.comp (continuous_const.prodMk continuous_id)
  have hBc : Continuous (fun x : Vec => B (t,x)) :=
    hB.continuous.comp (continuous_const.prodMk continuous_id)
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hEc.aestronglyMeasurable).mpr
    apply hI.mono_nonneg (hEc.norm.pow 2).aestronglyMeasurable (ae_of_all _ (fun x => sq_nonneg _))
    filter_upwards with x
    simp only [Pi.pow_apply]
    dsimp only [maxwellEnergy]
    nlinarith [sq_nonneg ‖B (t,x)‖]
  · apply (memLp_two_iff_integrable_sq_norm hBc.aestronglyMeasurable).mpr
    apply hI.mono_nonneg (hBc.norm.pow 2).aestronglyMeasurable (ae_of_all _ (fun x => sq_nonneg _))
    filter_upwards with x
    simp only [Pi.pow_apply]
    dsimp only [maxwellEnergy]
    nlinarith [sq_nonneg ‖E (t,x)‖]

lemma norm_sub_sq_le_twice (x y : Vec) :
    ‖x-y‖^2  ≤  2*‖x‖^2+2*‖y‖^2 := by
  have h := norm_sub_le x y
  nlinarith [norm_nonneg (x-y),norm_nonneg x,norm_nonneg y,sq_nonneg (‖x‖-‖y‖)]

lemma pair_sq_difference_tendsto {E B : Field}
    (hE : Continuous E) (hB : Continuous B)
    (hLp : ∀ t, 0 ≤ t → MemLp (fun x => E (t,x)) 2 volume ∧
      MemLp (fun x => B (t,x)) 2 volume)
    (henergy : ContinuousOn (fun t => ∫ x : Vec, ‖E (t,x)‖^2+‖B (t,x)‖^2) (Ici 0))
    {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t => ∫ x : Vec, ‖E (t,x)-E (s,x)‖^2+‖B (t,x)-B (s,x)‖^2)
      (𝓝[Ici 0] s) (𝓝 0) := by
  let e : ℝ → Vec → ℝ := fun t x => ‖E (t,x)‖^2+‖B (t,x)‖^2
  let D : ℝ → Vec → ℝ := fun t x => ‖E (t,x)-E (s,x)‖^2+‖B (t,x)-B (s,x)‖^2
  let g : ℝ → Vec → ℝ := fun t x => min (4*e s x) (2*e t x+2*e s x-D t x)
  have heI (t : ℝ) (ht : 0 ≤ t) : Integrable (e t) :=
    ((memLp_two_iff_integrable_sq_norm (hLp t ht).1.aestronglyMeasurable).mp (hLp t ht).1).add
      ((memLp_two_iff_integrable_sq_norm (hLp t ht).2.aestronglyMeasurable).mp (hLp t ht).2)
  have hDI (t : ℝ) (ht : 0 ≤ t) : Integrable (D t) := by
    have hEt := (hLp t ht).1.sub (hLp s hs).1
    have hBt := (hLp t ht).2.sub (hLp s hs).2
    exact ((memLp_two_iff_integrable_sq_norm hEt.aestronglyMeasurable).mp hEt).add
      ((memLp_two_iff_integrable_sq_norm hBt.aestronglyMeasurable).mp hBt)
  have hD0 (t : ℝ) (x : Vec) : 0 ≤ D t x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have he0 (t : ℝ) (x : Vec) : 0 ≤ e t x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hDle (t : ℝ) (x : Vec) : D t x ≤ 2*e t x+2*e s x := by
    have h1 := norm_sub_sq_le_twice (E (t,x)) (E (s,x))
    have h2 := norm_sub_sq_le_twice (B (t,x)) (B (s,x))
    dsimp only [D,e]
    linarith
  have hg0 (t : ℝ) (x : Vec) : 0 ≤ g t x :=
    le_min (mul_nonneg (by norm_num) (he0 s x)) (sub_nonneg.mpr (hDle t x))
  have hgI (t : ℝ) (ht : 0 ≤ t) : Integrable (g t) :=
    ((heI s hs).const_mul 4).inf (((heI t ht).const_mul 2).add ((heI s hs).const_mul 2) |>.sub (hDI t ht))
  have hgc (x : Vec) : Continuous (fun t => g t x) := by
    apply continuous_const.min
    exact ((((hE.comp (continuous_id.prodMk continuous_const)).norm.pow 2).add
      ((hB.comp (continuous_id.prodMk continuous_const)).norm.pow 2)).const_mul 2 |>.add continuous_const |>.sub
      ((((hE.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow 2).add
        (((hB.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow 2)))
  have hgs (x : Vec) : g s x=4*e s x := by
    dsimp only [g,D]
    simp only [sub_self,norm_zero,zero_pow (by norm_num : 2≠0),add_zero,sub_zero]
    rw [show 2*e s x+2*e s x=4*e s x by ring,min_self]
  have hglim : Tendsto (fun t => ∫ x : Vec, g t x) (𝓝[Ici 0] s) (𝓝 (4*∫ x : Vec, e s x)) := by
    rw [← integral_const_mul]
    apply tendsto_integral_filter_of_dominated_convergence (fun x => 4*e s x)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hgI t ht).aestronglyMeasurable
    · exact Eventually.of_forall (fun t => ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (hg0 t x)]
        exact min_le_left _ _))
    · exact (heI s hs).const_mul 4
    · exact ae_of_all _ (fun x => by
        simpa only [hgs] using
          ((hgc x).continuousAt (x:=s)).continuousWithinAt (s:=Ici 0) |>.tendsto)
  have hlim : Tendsto (fun t => 2*(∫ x : Vec, e t x)+2*(∫ x : Vec, e s x)-∫ x : Vec, g t x)
      (𝓝[Ici 0] s) (𝓝 0) := by
    have hh := (((henergy s hs).tendsto.const_mul 2).add_const (2*∫ x : Vec, e s x)).sub hglim
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [e]
    congr 1
    ring
  apply squeeze_zero' (Eventually.of_forall (fun t => integral_nonneg (hD0 t))) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hm : (∫ x : Vec, g t x) ≤ ∫ x : Vec, 2*e t x+2*e s x-D t x :=
    integral_mono (hgI t ht) (((heI t ht).const_mul 2).add ((heI s hs).const_mul 2) |>.sub (hDI t ht))
      (fun x => min_le_right _ _)
  have hsum : Integrable (fun x => 2*e t x+2*e s x) :=
    ((heI t ht).const_mul 2).add ((heI s hs).const_mul 2)
  rw [integral_sub hsum (hDI t ht),
    integral_add ((heI t ht).const_mul 2) ((heI s hs).const_mul 2),integral_const_mul,integral_const_mul] at hm
  linarith

lemma L2_norm_sub_sq_eq_integral {u v : Lp Vec 2 (volume : Measure Vec)}
    {f g : Vec → Vec} (hu : (u : Vec → Vec) =ᵐ[volume] f)
    (hv : (v : Vec → Vec) =ᵐ[volume] g) :
    ‖u-v‖^2=∫ x : Vec, ‖f x-g x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u v,hu,hv] with x hsub hf hg
  rw [hsub]
  simp only [Pi.sub_apply,hf,hg,real_inner_self_eq_norm_sq]

lemma timeContinuousL2_of_continuous_energy {E B : Field}
    (hE : Continuous E) (hB : Continuous B)
    (hLp : ∀ t, 0 ≤ t → MemLp (fun x => E (t,x)) 2 volume ∧
      MemLp (fun x => B (t,x)) 2 volume)
    (henergy : ContinuousOn (fun t => ∫ x : Vec, ‖E (t,x)‖^2+‖B (t,x)‖^2) (Ici 0)) :
    TimeContinuousL2 E ∧ TimeContinuousL2 B := by
  classical
  let E₂ : ℝ → Lp Vec 2 (volume : Measure Vec) := fun t =>
    if ht : 0 ≤ t then (hLp t ht).1.toLp (fun x => E (t,x)) else 0
  let B₂ : ℝ → Lp Vec 2 (volume : Measure Vec) := fun t =>
    if ht : 0 ≤ t then (hLp t ht).2.toLp (fun x => B (t,x)) else 0
  have hEe (t : ℝ) (ht : 0 ≤ t) : (E₂ t : Vec → Vec) =ᵐ[volume] (fun x => E (t,x)) := by
    dsimp only [E₂]; rw [dite_eq_left ht]; exact MemLp.coeFn_toLp _
  have hBe (t : ℝ) (ht : 0 ≤ t) : (B₂ t : Vec → Vec) =ᵐ[volume] (fun x => B (t,x)) := by
    dsimp only [B₂]; rw [dite_eq_left ht]; exact MemLp.coeFn_toLp _
  have hlim (s : ℝ) (hs : 0 ≤ s) :
      Tendsto (fun t => ‖E₂ t-E₂ s‖^2+‖B₂ t-B₂ s‖^2) (𝓝[Ici 0] s) (𝓝 0) := by
    apply (pair_sq_difference_tendsto hE hB hLp henergy hs).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [L2_norm_sub_sq_eq_integral (hEe t ht) (hEe s hs),
      L2_norm_sub_sq_eq_integral (hBe t ht) (hBe s hs)]
    have hEt := (hLp t ht).1.sub (hLp s hs).1
    have hBt := (hLp t ht).2.sub (hLp s hs).2
    exact (integral_add
      ((memLp_two_iff_integrable_sq_norm hEt.aestronglyMeasurable).mp hEt)
      ((memLp_two_iff_integrable_sq_norm hBt.aestronglyMeasurable).mp hBt))
  have hEc : ContinuousOn E₂ (Ici 0) := by
    intro s hs
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsq := squeeze_zero' (Eventually.of_forall (fun t : ℝ => sq_nonneg ‖E₂ t-E₂ s‖))
      (Eventually.of_forall (fun t : ℝ => le_add_of_nonneg_right (sq_nonneg ‖B₂ t-B₂ s‖))) (hlim s hs)
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)
  have hBc : ContinuousOn B₂ (Ici 0) := by
    intro s hs
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsq := squeeze_zero' (Eventually.of_forall (fun t : ℝ => sq_nonneg ‖B₂ t-B₂ s‖))
      (Eventually.of_forall (fun t : ℝ => le_add_of_nonneg_left (sq_nonneg ‖E₂ t-E₂ s‖))) (hlim s hs)
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)
  exact ⟨⟨E₂,hEc,hEe⟩,⟨B₂,hBc,hBe⟩⟩

theorem vacuum_timeContinuousL2 {E B : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hfirst : ∀ t, 0 ≤ t → ∀ x, dirD E (1,0) (t,x)=spaceCurl B (t,x) ∧
      dirD B (1,0) (t,x)= -spaceCurl E (t,x))
    (hE0 : MemLp (fun x => E (0,x)) 2 volume) (hB0 : MemLp (fun x => B (0,x)) 2 volume) :
    TimeContinuousL2 E ∧ TimeContinuousL2 B := by
  apply timeContinuousL2_of_continuous_energy hE.continuous hB.continuous
    (fun t ht => vacuum_memLp hE hB hfirst hE0 hB0 ht)
  have heq (t : ℝ) (ht : t∈Ici 0) :
      (∫ x : Vec, ‖E (t,x)‖^2+‖B (t,x)‖^2)=2*∫ x : Vec, maxwellEnergy E B (0,x) := by
    calc
      _ = 2*∫ x : Vec, maxwellEnergy E B (t,x) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by dsimp only [maxwellEnergy]; ring)
      _ = _ := congrArg (fun y : ℝ => 2*y) (vacuum_energy_conservation hE hB hfirst hE0 hB0 ht).2
  exact continuousOn_const.congr (fun t ht => heq t ht)

lemma initialCharge_conserved {E₀ : Vec → Vec} (hE : ContDiff ℝ ∞ E₀)
    (p : ℝ × Vec) :
    dirD (fun z : ℝ × Vec => divergence E₀ z.2) (1,0) p+spaceDiv (0:Field) p=0 := by
  rcases p with ⟨t,x⟩
  have hρ : ContDiff ℝ ∞ (fun z : ℝ × Vec => divergence E₀ z.2) :=
    (contDiff_divergence hE).comp contDiff_snd
  rw [← deriv_slice_eq_dirD (hρ.differentiable (by simp))]
  simp [spaceDiv,dirD]

lemma freeMaxwell_equations {E₀ B₀ : Vec → Vec}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hDB : ∀ x, divergence B₀ x=0) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    dirD (freeMaxwellElectric E₀ B₀) (1,0) (t,x)=spaceCurl (freeMaxwellMagnetic E₀ B₀) (t,x) ∧
    dirD (freeMaxwellMagnetic E₀ B₀) (1,0) (t,x)= -spaceCurl (freeMaxwellElectric E₀ B₀) (t,x) ∧
    spaceDiv (freeMaxwellElectric E₀ B₀) (t,x)=divergence E₀ x ∧
    spaceDiv (freeMaxwellMagnetic E₀ B₀) (t,x)=0 := by
  have hh := constructed_maxwell_equations (j:=0) hE hB
    ((contDiff_divergence hE).comp contDiff_snd) (contDiff_const : ContDiff ℝ ∞ (0:Field))
    (fun t _ x => initialCharge_conserved hE (t,x)) (fun _ => rfl) hDB ht x
  change dirD (freeMaxwellElectric E₀ B₀) (1,0) (t,x)=spaceCurl (freeMaxwellMagnetic E₀ B₀) (t,x)-(0:Vec) ∧
    dirD (freeMaxwellMagnetic E₀ B₀) (1,0) (t,x)= -spaceCurl (freeMaxwellElectric E₀ B₀) (t,x) ∧
    spaceDiv (freeMaxwellElectric E₀ B₀) (t,x)=divergence E₀ x ∧
    spaceDiv (freeMaxwellMagnetic E₀ B₀) (t,x)=0 at hh
  simpa only [sub_zero] using hh

theorem freeMaxwell_evolution {E₀ B₀ : Vec → Vec}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hE0 : MemLp E₀ 2 volume) (hB0 : MemLp B₀ 2 volume)
    (hDB : ∀ x, divergence B₀ x=0) :
    let E := freeMaxwellElectric E₀ B₀
    let B := freeMaxwellMagnetic E₀ B₀
    ContDiff ℝ ∞ E ∧ ContDiff ℝ ∞ B ∧
    (∀ x, E (0,x)=E₀ x ∧ B (0,x)=B₀ x) ∧
    TimeContinuousL2 E ∧ TimeContinuousL2 B ∧
    (∀ t, 0 ≤ t → ∀ x,
      dirD E (1,0) (t,x)=spaceCurl B (t,x) ∧
      dirD B (1,0) (t,x)= -spaceCurl E (t,x) ∧
      spaceDiv E (t,x)=divergence E₀ x ∧ spaceDiv B (t,x)=0) := by
  have hEc : ContDiff ℝ ∞ (freeMaxwellElectric E₀ B₀) :=
    contDiff_maxwellElectric hE hB ((contDiff_divergence hE).comp contDiff_snd) contDiff_const
  have hBc : ContDiff ℝ ∞ (freeMaxwellMagnetic E₀ B₀) :=
    contDiff_maxwellMagnetic hE hB contDiff_const
  have hEi (x : Vec) : freeMaxwellElectric E₀ B₀ (0,x)=E₀ x := maxwellElectric_initial hE x
  have hBi (x : Vec) : freeMaxwellMagnetic E₀ B₀ (0,x)=B₀ x := maxwellMagnetic_initial hB x
  have hfirst (t : ℝ) (ht : 0 ≤ t) (x : Vec) := freeMaxwell_equations hE hB hDB ht x
  have hEI : MemLp (fun x => freeMaxwellElectric E₀ B₀ (0,x)) 2 volume := by
    simpa only [hEi] using hE0
  have hBI : MemLp (fun x => freeMaxwellMagnetic E₀ B₀ (0,x)) 2 volume := by
    simpa only [hBi] using hB0
  obtain ⟨hEl2,hBl2⟩ := vacuum_timeContinuousL2 hEc hBc
    (fun t ht x => ⟨(hfirst t ht x).1,(hfirst t ht x).2.1⟩) hEI hBI
  exact ⟨hEc,hBc,(fun x => ⟨hEi x,hBi x⟩),hEl2,hBl2,hfirst⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_VlasovConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma waveK_congr_sphere {g h : Vec → ℝ} (t : ℝ) (x : Vec)
    (he : ∀ n : Sphere, g (x+t • n.1)=h (x+t • n.1)) :
    waveK g (t,x)=waveK h (t,x) := by
  simp only [waveK,sphereSum]
  congr 2
  exact integral_congr_ae (ae_of_all _ he)

lemma waveK_zero_of_sphere {g : Vec → ℝ} (t : ℝ) (x : Vec)
    (hz : ∀ n : Sphere, g (x+t • n.1)=0) : waveK g (t,x)=0 := by
  rw [waveK_congr_sphere (h:=fun _ => 0) t x hz]
  simp [waveK,sphereSum]

lemma norm_sub_radius_le (x : Vec) (r : ℝ) (n : Sphere) :
    ‖x‖-|r| ≤ ‖x+r • n.1‖ := by
  have hh := norm_sub_le (x+r • n.1) (r • n.1)
  rw [add_sub_cancel_right,norm_smul,Real.norm_eq_abs,sphere_norm,mul_one] at hh
  linarith

lemma waveK_zero_outside {g : Vec → ℝ} {R t : ℝ} {x : Vec}
    (hz : ∀ y : Vec, R < ‖y‖ → g y=0) (hx : R+|t|<‖x‖) :
    waveK g (t,x)=0 :=
  waveK_zero_of_sphere t x (fun n => hz _ (by linarith [norm_sub_radius_le x t n]))

lemma sourceWave_zero_outside {ρ : ℝ × Vec → ℝ} {R T t : ℝ} {x : Vec}
    (ht : t∈Icc 0 T) (hz : ∀ s∈Icc 0 T, ∀ y : Vec, R<‖y‖ → ρ (s,y)=0)
    (hx : R+T<‖x‖) : sourceWave ρ (t,x)=0 := by
  unfold sourceWave volterra
  rw [intervalIntegral.integral_of_le ht.1]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hs' : s∈Icc 0 t := ⟨hs.1.le,hs.2⟩
  apply waveK_zero_outside (hz s ⟨hs'.1,hs'.2.trans ht.2⟩)
  rw [abs_of_nonneg (sub_nonneg.mpr hs'.2)]
  change R+(t-s)<‖x‖
  linarith [ht.2,hs'.1]

lemma sourceField_zero_outside {J : Field} {R T t : ℝ} {x : Vec}
    (ht : t∈Icc 0 T) (hz : ∀ s∈Icc 0 T, ∀ y : Vec, R<‖y‖ → J (s,y)=0)
    (hx : R+T<‖x‖) : sourceField J (t,x)=0 := by
  ext i
  apply sourceWave_zero_outside ht (fun s hs y hy => ?_) hx
  simp only [hz s hs y hy,PiLp.zero_apply]

lemma freeField_velocity_congr {G H H' : Vec → Vec} (t : ℝ) (x : Vec)
    (he : ∀ n : Sphere, H (x+t • n.1)=H' (x+t • n.1)) :
    freeField G H (t,x)=freeField G H' (t,x) := by
  ext i
  change freeWave (fun y => G y i) (fun y => H y i) (t,x)=
    freeWave (fun y => G y i) (fun y => H' y i) (t,x)
  unfold freeWave
  rw [waveK_congr_sphere (h:=fun y => H' y i) t x (fun n => congrArg (fun v : Vec => v i) (he n))]

lemma fderiv_zero_outside_spatial {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × Vec → W} {a b R t : ℝ} {x : Vec}
    (hz : ∀ s∈Icc a b, ∀ y : Vec, R<‖y‖ → F (s,y)=0)
    (ht : t∈Ioo a b) (hx : R<‖x‖) : fderiv ℝ F (t,x)=0 := by
  have he : F =ᶠ[𝓝 (t,x)] fun _ => (0:W) := by
    have hu : IsOpen {p : ℝ × Vec | p.1∈Ioo a b ∧ R<‖p.2‖} :=
      (isOpen_Ioo.preimage continuous_fst).inter (isOpen_lt continuous_const continuous_snd.norm)
    filter_upwards [hu.mem_nhds ⟨ht,hx⟩] with p hp
    exact hz p.1 (Ioo_subset_Icc_self hp.1) p.2 hp.2
  rw [he.fderiv_eq]
  exact fderiv_const_apply (0:W)

lemma waveGradient_zero_outside {ρ : ℝ × Vec → ℝ} {a b R t : ℝ} {x : Vec}
    (hz : ∀ s∈Icc a b, ∀ y : Vec, R<‖y‖ → ρ (s,y)=0)
    (ht : t∈Ioo a b) (hx : R<‖x‖) : waveGradient ρ (t,x)=0 := by
  ext i
  change dirD ρ (0,basis i) (t,x)=0
  simp [dirD,fderiv_zero_outside_spatial hz ht hx]

lemma spaceCurl_zero_outside {J : Field} {a b R t : ℝ} {x : Vec}
    (hz : ∀ s∈Icc a b, ∀ y : Vec, R<‖y‖ → J (s,y)=0)
    (ht : t∈Ioo a b) (hx : R<‖x‖) : spaceCurl J (t,x)=0 := by
  ext i
  simp [spaceCurl,dirD,fderiv_zero_outside_spatial hz ht hx]

lemma maxwell_perturbation_zero_outside {E₀ B₀ : Vec → Vec}
    {ρ : ℝ × Vec → ℝ} {j : Field} {R T t : ℝ} {x : Vec}
    (hDE : ∀ y, divergence E₀ y=ρ (0,y))
    (hz : ∀ s∈Icc (-1) (T+1), ∀ y : Vec, R<‖y‖ → ρ (s,y)=0 ∧ j (s,y)=0)
    (ht : t∈Icc 0 T) (hx : R+T<‖x‖) :
    maxwellElectric E₀ B₀ ρ j (t,x)=freeMaxwellElectric E₀ B₀ (t,x) ∧
    maxwellMagnetic E₀ B₀ j (t,x)=freeMaxwellMagnetic E₀ B₀ (t,x) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0 : (0:ℝ)∈Icc (-1) (T+1) := ⟨by norm_num,by linarith⟩
  have hρz := fun s hs y hy => (hz s hs y hy).1
  have hjz := fun s hs y hy => (hz s hs y hy).2
  have hEz : sourceField (fun q => -waveGradient ρ q-dirD j (1,0) q) (t,x)=0 := by
    apply sourceField_zero_outside ht _ hx
    intro s hs y hy
    have hi : s∈Ioo (-1) (T+1) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
    simp only [waveGradient_zero_outside hρz hi hy,neg_zero,dirD,
      fderiv_zero_outside_spatial hjz hi hy,zero_apply,sub_self]
  have hEz' : sourceField (fun q =>
      -waveGradient (fun p : ℝ × Vec => divergence E₀ p.2) q-dirD (0:Field) (1,0) q) (t,x)=0 := by
    apply sourceField_zero_outside ht _ hx
    intro s hs y hy
    have hi : s∈Ioo (-1) (T+1) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have hstat : ∀ r∈Icc (-1) (T+1), ∀ z : Vec, R<‖z‖ →
        (fun p : ℝ × Vec => divergence E₀ p.2) (r,z)=0 := by
      intro r hr z hz'
      exact (hDE z).trans (hρz 0 h0 z hz')
    rw [waveGradient_zero_outside hstat hi hy]
    simp [dirD]
  have hBz : sourceField (spaceCurl j) (t,x)=0 := by
    apply sourceField_zero_outside ht _ hx
    intro s hs y hy
    exact spaceCurl_zero_outside hjz ⟨by linarith [hs.1],by linarith [hs.2]⟩ hy
  have hBz' : sourceField (spaceCurl (0:Field)) (t,x)=0 := by
    apply sourceField_zero_outside ht _ hx
    intro s hs y hy
    exact spaceCurl_zero_outside (a:=(-1)) (b:=T+1) (R:=R)
      (fun _ _ _ _ => rfl) ⟨by linarith [hs.1],by linarith [hs.2]⟩ hy
  constructor
  · simp only [maxwellElectric,freeMaxwellElectric,hEz,hEz',add_zero]
    apply freeField_velocity_congr
    intro n
    have hn : R<‖x+t • n.1‖ := by
      have hh := norm_sub_radius_le x t n
      rw [abs_of_nonneg ht.1] at hh
      linarith [ht.2]
    simp only [hjz 0 h0 _ hn,Pi.zero_apply,sub_zero]
  · simp only [maxwellMagnetic,freeMaxwellMagnetic,hBz,hBz',add_zero]

lemma TimeContinuousL2.add {F G : Field} (hF : TimeContinuousL2 F) (hG : TimeContinuousL2 G) :
    TimeContinuousL2 (fun p => F p+G p) := by
  obtain ⟨F₂,hFc,hFe⟩ := hF
  obtain ⟨G₂,hGc,hGe⟩ := hG
  refine ⟨fun t => F₂ t+G₂ t,hFc.add hGc,?_⟩
  intro t ht
  filter_upwards [Lp.coeFn_add (F₂ t) (G₂ t),hFe t ht,hGe t ht] with x he hf hg
  simpa only [Pi.add_apply,hf,hg] using he

lemma timeContinuousL2_congr {F G : Field} (hF : TimeContinuousL2 F)
    (he : ∀ t, 0 ≤ t → ∀ x, F (t,x)=G (t,x)) : TimeContinuousL2 G := by
  obtain ⟨F₂,hFc,hFe⟩ := hF
  refine ⟨F₂,hFc,fun t ht => (hFe t ht).trans ?_⟩
  exact ae_of_all _ (he t ht)

lemma timeContinuousL2_compact {F : Field} (hF : Continuous F)
    (hK : ∀ T, 0 ≤ T → ∃ K : Set Vec, IsCompact K ∧
      ∀ t∈Icc 0 T, ∀ x∉K, F (t,x)=0) : TimeContinuousL2 F := by
  have hLp (t : ℝ) (ht : 0 ≤ t) : MemLp (fun x => F (t,x)) 2 volume := by
    obtain ⟨K,hK,hz⟩ := hK t ht
    exact (hF.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
      (compactSupport_of_zero_off hK (hz t ⟨ht,le_rfl⟩))
  have he : ContinuousOn (fun t => ∫ x : Vec, ‖F (t,x)‖^2) (Ici 0) := by
    intro s hs
    change 0 ≤ s at hs
    obtain ⟨K,hK,hz⟩ := hK (s+1) (by linarith : 0 ≤ s+1)
    have hc : ContinuousOn (fun t => ∫ x : Vec, ‖F (t,x)‖^2) (Icc 0 (s+1)) :=
      continuousOn_integral_uniform_support hK (hF.norm.pow 2).continuousOn
        (fun t ht x hx => by change ‖F (t,x)‖^2=0; rw [hz t ht x hx]; simp)
    apply (hc s ⟨hs,by linarith⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_add_one s))] with t ht ht'
    exact ⟨ht,ht'.le⟩
  have hh := timeContinuousL2_of_continuous_energy (B:=0) hF continuous_const
    (fun t ht => ⟨hLp t ht,MemLp.zero⟩) (by simpa using he)
  exact hh.1

lemma maxwell_timeContinuousL2_oai {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j)
    (hE0 : MemLp E₀ 2 volume) (hB0 : MemLp B₀ 2 volume)
    (hDE : ∀ x, divergence E₀ x=ρ (0,x)) (hDB : ∀ x, divergence B₀ x=0)
    (hK : ∀ T, 0 ≤ T → ∃ R : ℝ, ∀ s∈Icc (-1) (T+1), ∀ y : Vec,
      R<‖y‖ → ρ (s,y)=0 ∧ j (s,y)=0) :
    TimeContinuousL2 (maxwellElectric E₀ B₀ ρ j) ∧
    TimeContinuousL2 (maxwellMagnetic E₀ B₀ j) := by
  have hh := freeMaxwell_evolution hE hB hE0 hB0 hDB
  have hEc := contDiff_maxwellElectric hE hB hρ hj
  have hBc := contDiff_maxwellMagnetic hE hB hj
  have hδEc := hEc.continuous.sub hh.1.continuous
  have hδBc := hBc.continuous.sub hh.2.1.continuous
  have hδK (T : ℝ) (hT : 0 ≤ T) : ∃ K : Set Vec, IsCompact K ∧
      ∀ t∈Icc 0 T, ∀ x∉K,
      (maxwellElectric E₀ B₀ ρ j (t,x)-freeMaxwellElectric E₀ B₀ (t,x)=0) ∧
      (maxwellMagnetic E₀ B₀ j (t,x)-freeMaxwellMagnetic E₀ B₀ (t,x)=0) := by
    obtain ⟨R,hR⟩ := hK T hT
    refine ⟨closedBall (0:Vec) (R+T),isCompact_closedBall _ _,?_⟩
    intro t ht x hx
    have hn : R+T<‖x‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hx
    obtain ⟨he,hb⟩ := maxwell_perturbation_zero_outside hDE hR ht hn
    exact ⟨sub_eq_zero.mpr he,sub_eq_zero.mpr hb⟩
  have hδE := timeContinuousL2_compact hδEc (fun T hT => by
    obtain ⟨K,hK,hz⟩ := hδK T hT
    exact ⟨K,hK,fun t ht x hx => (hz t ht x hx).1⟩)
  have hδB := timeContinuousL2_compact hδBc (fun T hT => by
    obtain ⟨K,hK,hz⟩ := hδK T hT
    exact ⟨K,hK,fun t ht x hx => (hz t ht x hx).2⟩)
  constructor
  · exact timeContinuousL2_congr (hh.2.2.2.1.add hδE) (fun _ _ _ => add_sub_cancel _ _)
  · exact timeContinuousL2_congr (hh.2.2.2.2.1.add hδB) (fun _ _ _ => add_sub_cancel _ _)

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.maxwell_timeContinuousL2_oai := @OAI.RVM.maxwell_timeContinuousL2_oai
