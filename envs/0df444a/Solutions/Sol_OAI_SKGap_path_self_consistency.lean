-- Prove2me | solution 1 for OAI.SKGap.path_self_consistency
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:46:58.878662+00:00
-- url     : https://prove2.me/submissions/25ca2262-5d9a-43dc-b5ac-b65f5c9d4a91

import Mathlib
import Definitions.Def_OAIQ072A000

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Quadratic
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace SKGap.ComplexSpectral
variable {ι : Type*} [Fintype ι]

lemma continuous_quadratic :
    Continuous (fun p : Matrix ι ι ℂ × EuclideanSpace ℂ ι => quadratic p.1 p.2) := by
  unfold quadratic dotProduct mulVec
  fun_prop

lemma compact_unitSphere : IsCompact (unitSphere ι) := isCompact_sphere _ _

lemma continuous_lowerRayleigh : Continuous (lowerRayleigh (ι := ι)) :=
  compact_unitSphere.continuous_sInf continuous_quadratic

lemma quadratic_neg (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    quadratic (-M) x = -quadratic M x := by simp [quadratic,Matrix.neg_mulVec,dotProduct_neg]

lemma lowerRayleigh_le (M : Matrix ι ι ℂ) {x : EuclideanSpace ℂ ι}
    (hx : x ∈ unitSphere ι) : lowerRayleigh M ≤ quadratic M x := by
  have hb : BddBelow (quadratic M '' unitSphere ι) :=
    (compact_unitSphere.image (continuous_quadratic.comp (continuous_const.prodMk continuous_id))).bddBelow
  exact csInf_le hb ⟨x,hx,rfl⟩

variable [DecidableEq ι]

lemma quadratic_eigenvector {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (i : ι) :
    quadratic M (hM.eigenvectorBasis i) = hM.eigenvalues i := by
  exact (hM.eigenvalues_eq i).symm

lemma eigenvalue_lower_bound {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (i : ι) :
    lowerRayleigh M ≤ hM.eigenvalues i := by
  rw [← quadratic_eigenvector hM i]
  apply lowerRayleigh_le
  simpa only [unitSphere,Metric.mem_sphere,dist_zero_right] using hM.eigenvectorBasis.orthonormal.1 i

lemma eigenvalue_upper_bound {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (i : ι) :
    hM.eigenvalues i ≤ -lowerRayleigh (-M) := by
  have hh := lowerRayleigh_le (-M) (x := hM.eigenvectorBasis i)
    (by simpa only [unitSphere,Metric.mem_sphere,dist_zero_right] using hM.eigenvectorBasis.orthonormal.1 i)
  rw [quadratic_neg,quadratic_eigenvector] at hh
  linarith

end SKGap.ComplexSpectral

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_StandardGaussianProduct
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal

open Filter
open scoped Topology
namespace SKGap
lemma tendsto_gaussianPDFReal_atTop (d : ℝ) {s : ℝ≥0} (hs : 0 < s) :
    Filter.Tendsto (gaussianPDFReal d s) Filter.atTop (𝓝 0) := by
  have hsp : (0:ℝ) < s := hs
  have hshift : Tendsto (fun x : ℝ => x-d) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b+d)] with x hx
    linarith
  have hpow : Filter.Tendsto (fun x : ℝ => (x-d)^2) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp hshift
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpow.atTop_div_const (by positivity : 0 < 2*(s:ℝ)))
  rw [gaussianPDFReal_def]
  simpa only [neg_div, mul_zero,one_div,Function.comp_apply] using hexp.const_mul (1/sqrt (2*Real.pi*(s:ℝ)))

lemma tendsto_gaussianPDFReal_neg_atTop (d : ℝ) {s : ℝ≥0} (hs : 0 < s) :
    Filter.Tendsto (fun x => gaussianPDFReal d s (-x)) Filter.atTop (𝓝 0) := by
  have he : (fun x => gaussianPDFReal d s (-x)) = gaussianPDFReal (-d) s := by
    funext x
    unfold gaussianPDFReal
    congr 2
    ring
  rw [he]
  exact tendsto_gaussianPDFReal_atTop (-d) hs

theorem gaussian_lipschitz_IBP {f : ℝ → ℝ} {L : ℝ≥0} {C d : ℝ} {s : ℝ≥0}
    (hs : 0 < s) (hL : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ y, (y-d)*f y ∂gaussianReal d s) = (s:ℝ)*(∫ y, deriv f y ∂gaussianReal d s) := by
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hdf : Integrable (deriv f) (gaussianReal d s) :=
    Integrable.of_bound (measurable_deriv f).aestronglyMeasurable (L:ℝ)
      (ae_of_all _ (fun _ => norm_deriv_le_of_lipschitz hL))
  have hyf : Integrable (fun y => (y-d)*f y) (gaussianReal d s) := by
    have hh := ((IsGaussian.integrable_id (μ := gaussianReal d s)).sub (integrable_const d)).bdd_mul
      (f := f) hL.continuous.aestronglyMeasurable (ae_of_all _ hC)
    simpa only [mul_comm,Pi.sub_apply,id_eq] using hh
  let p := gaussianPDFReal d s
  have hpi : Integrable (fun y => p y*deriv f y) := (integrable_gaussian_iff hs.ne').mp hdf
  have hxi : Integrable (fun y => p y*((y-d)*f y)) := (integrable_gaussian_iff hs.ne').mp hyf
  let g : ℝ → ℝ := fun y => p y*deriv f y-(p y*((y-d)*f y))/(s:ℝ)
  have hgi : Integrable g := hpi.sub (hxi.div_const _)
  have hpd (y : ℝ) : deriv p y = -(y-d)/(s:ℝ)*p y := (hasDerivAt_gaussianPDFReal d hs.ne' y).deriv
  have hpac (a b : ℝ) : AbsolutelyContinuousOnInterval p a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    have hh : ContDiff ℝ 1 p := by
      change ContDiff ℝ 1 (fun x : ℝ => (sqrt (2 * π * (s : ℝ)))⁻¹ * exp (-(x-d)^2/(2*(s:ℝ))))
      fun_prop
    exact hh.contDiffOn
  have hfac (a b : ℝ) : AbsolutelyContinuousOnInterval f a b := hL.lipschitzOnWith.absolutelyContinuousOnInterval
  have hftc (a b : ℝ) : (∫ y in a..b, g y) = p b*f b-p a*f a := by
    rw [← (hpac a b).integral_deriv_mul_eq_sub (hfac a b)]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp [g]
    rw [hpd]
    ring
  have hbd (u : ℝ → ℝ) (hp : Filter.Tendsto (fun x => p (u x)) Filter.atTop (𝓝 0)) :
      Filter.Tendsto (fun x => p (u x)*f (u x)) Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun x => ?_) (by simpa only [zero_mul] using hp.mul_const C)
    rw [norm_mul, Real.norm_eq_abs (p (u x)),abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact mul_le_mul_of_nonneg_left (hC _) (gaussianPDFReal_nonneg _ _ _)
  have htop := hbd id (tendsto_gaussianPDFReal_atTop d hs)
  have hbot := hbd Neg.neg (tendsto_gaussianPDFReal_neg_atTop d hs)
  have hlim := intervalIntegral_tendsto_integral hgi Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  simp only [hftc] at hlim
  have hz : (∫ y, g y) = 0 := by
    simpa only [id_eq,sub_zero] using tendsto_nhds_unique hlim (htop.sub hbot)
  dsimp [g] at hz
  rw [integral_sub hpi (hxi.div_const _),integral_div] at hz
  rw [integral_gaussianReal_eq_integral_smul hs.ne',integral_gaussianReal_eq_integral_smul hs.ne']
  simp only [smul_eq_mul]
  have hh : (∫ y, p y*((y-d)*f y))/(s:ℝ) = ∫ y, p y*deriv f y := by linarith
  have hm := (div_eq_iff (ne_of_gt (show (0:ℝ) < s from hs))).mp hh
  dsimp [p] at hm
  nlinarith only [hm]

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CoordinateDeriv
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.instIsProbabilityMeasureForallFinRealStandardGaussianProduct_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
namespace SKGap

lemma lipschitz_insertNth {n : ℕ} (i : Fin (n+1)) (u : Fin n → ℝ) :
    LipschitzWith 1 (fun z : ℝ => i.insertNth (α := fun _ => ℝ) z u) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff dist_nonneg).2
  refine i.forall_iff_succAbove.mpr ⟨?_,?_⟩
  · simp only [Fin.insertNth_apply_same,le_refl]
  · intro k
    simp only [Fin.insertNth_apply_succAbove,dist_self]
    exact dist_nonneg

lemma continuous_insertNth_uncurry {n : ℕ} (i : Fin (n+1)) :
    Continuous (fun p : (Fin n → ℝ) × ℝ => i.insertNth (α := fun _ => ℝ) p.2 p.1) := by
  apply continuous_pi
  refine i.forall_iff_succAbove.mpr ⟨?_,?_⟩
  · simpa only [Fin.insertNth_apply_same] using (continuous_snd : Continuous (fun p : (Fin n → ℝ) × ℝ => p.2))
  · intro k
    simpa only [Fin.insertNth_apply_succAbove,Function.comp_def] using (continuous_apply k).comp continuous_fst

lemma measurable_coordinateDeriv {n : ℕ} (i : Fin (n+1)) {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : Continuous f) : Measurable (coordinateDeriv i f) := by
  have h := measurable_deriv_with_param (f := fun u z => f (i.insertNth z u))
    (hf.comp (continuous_insertNth_uncurry i))
  have hc : Continuous (fun x : Fin (n+1) → ℝ => (i.removeNth x,x i)) := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro k
      exact continuous_apply (i.succAbove k)
    · exact continuous_apply i
  exact h.comp hc.measurable

lemma norm_coordinateDeriv_le {n : ℕ} (i : Fin (n+1)) {f : (Fin (n+1) → ℝ) → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) (x : Fin (n+1) → ℝ) :
    ‖coordinateDeriv i f x‖ ≤ L := by
  have hl := hf.comp (lipschitz_insertNth i (i.removeNth x))
  simpa only [mul_one,coordinateDeriv,Function.comp_def] using norm_deriv_le_of_lipschitz hl (x₀ := x i)

theorem gaussianProduct_lipschitz_IBP {n : ℕ} (i : Fin (n+1))
    {f : (Fin (n+1) → ℝ) → ℝ} {L : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, x i * f x ∂standardGaussianProduct (n+1)) =
      ∫ x, coordinateDeriv i f x ∂standardGaussianProduct (n+1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hp : MeasurePreserving e.symm
      ((gaussianReal 0 1).prod (standardGaussianProduct n))
      (standardGaussianProduct (n+1)) :=
    (measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) i).symm
  have hi : Integrable (fun x : Fin (n+1) → ℝ => x i * f x)
      (standardGaussianProduct (n+1)) := by
    simpa only [mul_comm,standardGaussianProduct] using
      (integrable_eval (i := i) IsGaussian.integrable_id).bdd_mul
        hf.continuous.aestronglyMeasurable (ae_of_all _ hC)
  have hi' : Integrable (coordinateDeriv i f) (standardGaussianProduct (n+1)) :=
    Integrable.of_bound (measurable_coordinateDeriv i hf.continuous).aestronglyMeasurable (L:ℝ)
      (ae_of_all _ (norm_coordinateDeriv_le i hf))
  have hsplit (g : (Fin (n+1) → ℝ) → ℝ) (hg : Integrable g (standardGaussianProduct (n+1))) :
      (∫ x, g x ∂standardGaussianProduct (n+1)) =
        ∫ u, ∫ z, g (i.insertNth (α := fun _ => ℝ) z u) ∂gaussianReal 0 1 ∂standardGaussianProduct n := by
    have hi2 : Integrable (fun x => g (e.symm x))
        ((gaussianReal 0 1).prod (standardGaussianProduct n)) := hp.integrable_comp_of_integrable hg
    rw [← hp.integral_comp' g,integral_prod _ hi2,integral_integral_swap hi2]
    rfl
  rw [hsplit _ hi,hsplit _ hi']
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [coordinateDeriv,Fin.insertNth_apply_same,Fin.removeNth_insertNth]
  simpa only [sub_zero,NNReal.coe_one,one_mul,Function.comp_def] using
    gaussian_lipschitz_IBP (d := 0) (s := 1) (by norm_num)
      (hf.comp (lipschitz_insertNth i u)) (fun z => hC (i.insertNth (α := fun _ => ℝ) z u))

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma lipschitz_coordinate_update (i : κ) (x : κ → ℝ) :
    LipschitzWith 1 (fun z : ℝ => Function.update x i z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff dist_nonneg).2
  intro k
  by_cases h : k = i
  · subst k; simp
  · simp only [Function.update_of_ne h,dist_self]; exact dist_nonneg

lemma measurable_finiteCoordinateDeriv (i : κ) {f : (κ → ℝ) → ℝ}
    (hf : Continuous f) : Measurable (finiteCoordinateDeriv i f) := by
  have h := measurable_deriv_with_param (f := fun x z => f (Function.update x i z))
    (hf.comp (continuous_update i))
  exact h.comp ((continuous_id.prodMk (continuous_apply i)).measurable)

lemma norm_finiteCoordinateDeriv_le (i : κ) {f : (κ → ℝ) → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) (x : κ → ℝ) :
    ‖finiteCoordinateDeriv i f x‖ ≤ L := by
  simpa only [finiteCoordinateDeriv,Function.comp_def,mul_one] using
    norm_deriv_le_of_lipschitz (hf.comp (lipschitz_coordinate_update i x)) (x₀ := x i)

lemma gaussianFinite_lipschitz_IBP_equiv {n : ℕ} (e : Fin (n+1) ≃ κ) (i : κ)
    {f : (κ → ℝ) → ℝ} {L : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, x i*f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) =
      ∫ x, finiteCoordinateDeriv i f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  have he (x : Fin (n+1) → ℝ) (k : κ) : E x k = x (e.symm k) := by
    simp [E,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have hl : LipschitzWith 1 E := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one,one_mul]
    apply (dist_pi_le_iff dist_nonneg).2
    intro k
    simpa only [he] using dist_le_pi_dist x y (e.symm k)
  have hp := measurePreserving_piCongrLeft (fun _ : κ => gaussianReal 0 1) e
  have hh := gaussianProduct_lipschitz_IBP (e.symm i)
    (by simpa only [mul_one,Function.comp_def] using hf.comp hl) (fun x => hC (E x))
  have hu (x : Fin (n+1) → ℝ) (z : ℝ) :
      E ((e.symm i).insertNth z ((e.symm i).removeNth x)) =
        Function.update (E x) i z := by
    rw [Fin.insertNth_removeNth]
    ext k
    simp only [he]
    by_cases h : k = i
    · subst k; simp
    · simp [he,Function.update_of_ne h,show e.symm k ≠ e.symm i from fun h' => h (e.symm.injective h')]
  have hd (x : Fin (n+1) → ℝ) :
      coordinateDeriv (e.symm i) (f ∘ E) x = finiteCoordinateDeriv i f (E x) := by
    simp only [coordinateDeriv,finiteCoordinateDeriv,Function.comp_def,hu,he]
  rw [← hp.integral_comp' (fun x => x i*f x),
    ← hp.integral_comp' (finiteCoordinateDeriv i f)]
  change (∫ x, E x i*f (E x) ∂standardGaussianProduct (n+1)) =
    ∫ x, finiteCoordinateDeriv i f (E x) ∂standardGaussianProduct (n+1)
  simpa only [← hd,he,Function.comp_def] using hh

theorem gaussianFinite_lipschitz_IBP (i : κ)
    {f : (κ → ℝ) → ℝ} {L : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, x i*f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) =
      ∫ x, finiteCoordinateDeriv i f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  have hn : Fintype.card κ ≠ 0 := by
    let : Nonempty κ := ⟨i⟩
    exact Fintype.card_ne_zero
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let e : κ ≃ Fin (n+1) := (Fintype.equivFin κ).trans (Equiv.cast (congrArg Fin hn))
  exact gaussianFinite_lipschitz_IBP_equiv e.symm i hf hC

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianFiniteIBPError
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
namespace SKGap
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem gaussianFinite_IBP_error (i : κ)
    {f d : (κ → ℝ) → ℝ} {L : ℝ≥0} {C D : ℝ} {s : Set (κ → ℝ)}
    (hf : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C)
    (hd : Measurable d) (hD : ∀ x, ‖d x‖ ≤ D) (hs : MeasurableSet s)
    (hder : ∀ x ∈ s, HasDerivAt (fun z => f (Function.update x i z)) (d x) (x i)) :
    |(∫ x, x i*f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1))-
      ∫ x, d x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)| ≤
      ((L:ℝ)+D)*(Measure.pi (fun _ : κ => gaussianReal 0 1)).real sᶜ := by
  let μ := Measure.pi (fun _ : κ => gaussianReal 0 1)
  have hi : Integrable (finiteCoordinateDeriv i f) μ :=
    Integrable.of_bound (measurable_finiteCoordinateDeriv i hf.continuous).aestronglyMeasurable
      (L:ℝ) (ae_of_all _ (norm_finiteCoordinateDeriv_le i hf))
  have hid : Integrable d μ := Integrable.of_bound hd.aestronglyMeasurable D (ae_of_all _ hD)
  rw [gaussianFinite_lipschitz_IBP i hf hC,← integral_sub hi hid]
  have he : (fun x => finiteCoordinateDeriv i f x-d x) =
      sᶜ.indicator (fun x => finiteCoordinateDeriv i f x-d x) := by
    funext x
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_notMem (show x ∉ sᶜ by simpa using hx),finiteCoordinateDeriv]
      rw [(hder x hx).deriv,sub_self]
    · rw [Set.indicator_of_mem hx]
  rw [he,integral_indicator hs.compl]
  exact norm_setIntegral_le_of_norm_le_const (measure_lt_top μ sᶜ) (fun x _ =>
    (norm_sub_le _ _).trans (add_le_add (norm_finiteCoordinateDeriv_le i hf x) (hD x)))

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixCoordinates
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap

variable {ι : Type*}

variable [Fintype ι]

lemma rawCoordinateMatrix_norm (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖rawCoordinateMatrix g‖ ≤ ‖g‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← sq]
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow,Real.sq_sqrt (by positivity),
    EuclideanSpace.norm_sq_eq]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,Fintype.sum_sum_type,Fintype.sum_prod_type,
    rawCoordinateMatrix]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma goeMatrix_norm (r : ℝ) (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖goeMatrix r g‖ ≤ sqrt (2*r)*‖g‖ := by
  have he : goeMatrix r g = (sqrt (2*r)/2) •
      (rawCoordinateMatrix g+(rawCoordinateMatrix g)ᵀ) := by ext; rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (sqrt (2*r)/2)*(‖rawCoordinateMatrix g‖+‖(rawCoordinateMatrix g)ᵀ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = sqrt (2*r)*‖rawCoordinateMatrix g‖ := by rw [Matrix.frobenius_norm_transpose]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (rawCoordinateMatrix_norm g) (sqrt_nonneg _)

omit [Fintype ι] in
lemma goeMatrix_sub (r : ℝ) (g h : MatrixCoordinates ι → ℝ) :
    goeMatrix r (g-h) = goeMatrix r g-goeMatrix r h := by
  ext i k; simp only [goeMatrix,Pi.sub_apply,Matrix.sub_apply]; ring

lemma goeMatrix_L2_lipschitz (r : ℝ) :
    LipschitzWith ⟨sqrt (2*r),sqrt_nonneg _⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => goeMatrix r g) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  simpa only [dist_eq_norm,← goeMatrix_sub] using! goeMatrix_norm r (g-h)

lemma goeMatrix_pi_lipschitz (r : ℝ) :
    LipschitzWith (⟨sqrt (2*r),sqrt_nonneg _⟩ *
      (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
      (goeMatrix (ι := ι) r) := by
  exact (goeMatrix_L2_lipschitz (ι := ι) r).comp
    (PiLp.lipschitzWith_toLp 2 (fun _ : MatrixCoordinates ι => ℝ))

variable [DecidableEq ι]

omit [Fintype ι] in
lemma goeMatrix_update (r : ℝ) (g : MatrixCoordinates ι → ℝ) (a b : ι) (t : ℝ) :
    goeMatrix r (Function.update g (.inl (a,b)) t) =
      goeMatrix r g + ((sqrt (2*r)/2)*(t-g (.inl (a,b)))) • symmetricElementary a b := by
  ext i k
  simp only [goeMatrix,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,symmetricElementary,
    Matrix.single_apply]
  by_cases hi : i=a <;> by_cases hk : k=b <;> by_cases hi' : i=b <;> by_cases hk' : k=a <;>
    simp_all [Function.update_apply,Prod.ext_iff,eq_comm] <;> ring

lemma symmetricElementary_norm_le (a b : ι) : ‖symmetricElementary a b‖ ≤ 2 := by
  unfold symmetricElementary
  exact (norm_add_le _ _).trans (by simpa [Matrix.frobenius_norm_def,Matrix.single_apply,ite_and] using (show (1:ℝ)+1 ≤ 2 by norm_num))

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SymmetricElementaryComm
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma symmetricElementary_comm (a b : ι) : symmetricElementary a b = symmetricElementary b a :=
  add_comm _ _

omit [Fintype ι] in
lemma goeMatrix_updated_observable_derivative {r : ℝ}
    {H : Matrix ι ι ℝ → ℝ} {g : MatrixCoordinates ι → ℝ} {a b : ι} {d : ℝ}
    (hd : HasDerivAt (fun t : ℝ => H (goeMatrix r g+t • symmetricElementary a b)) d 0) :
    HasDerivAt (fun t => H (goeMatrix r (Function.update g (.inl (a,b)) t)))
      ((sqrt (2*r)/2)*d) (g (.inl (a,b))) := by
  have ha := ((hasDerivAt_id (g (.inl (a,b)))).sub_const (g (.inl (a,b)))).const_mul (sqrt (2*r)/2)
  have ho : HasDerivAt (fun t : ℝ => H (goeMatrix r g+t • symmetricElementary a b)) d
      ((fun y : ℝ => (sqrt (2*r)/2)*(y-g (.inl (a,b)))) (g (.inl (a,b)))) := by simpa using hd
  have hh := ho.comp (g (.inl (a,b))) ha
  simpa only [Function.comp_def,goeMatrix_update,mul_one,one_mul,mul_comm,id_eq] using! hh

theorem goe_IBP_error {r : ℝ} (hr : 0 ≤ r) (a b : ι)
    {H : Matrix ι ι ℝ → ℝ} {d : (MatrixCoordinates ι → ℝ) → ℝ}
    {L : ℝ≥0} {C D : ℝ} {s : Set (MatrixCoordinates ι → ℝ)}
    (hf : LipschitzWith L (fun g => H (goeMatrix r g)))
    (hC : ∀ g, ‖H (goeMatrix r g)‖ ≤ C)
    (hd : Measurable d) (hD : ∀ g, ‖d g‖ ≤ D) (hs : MeasurableSet s)
    (hder : ∀ g ∈ s, HasDerivAt (fun t : ℝ => H (goeMatrix r g+t • symmetricElementary a b)) (d g) 0) :
    |(∫ g, goeMatrix r g a b * H (goeMatrix r g)
        ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) -
      r*(∫ g, d g ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))| ≤
      (sqrt (2*r)*(L:ℝ)+r*D)*
        (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real sᶜ := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  let c : ℝ := sqrt (2*r)/2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc2 : 2*c^2 = r := by
    dsimp [c]; rw [div_pow,Real.sq_sqrt (by positivity)]; ring
  have hD' : ∀ g, ‖c*d g‖ ≤ c*D := fun g => by
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (hD g) hc
  have h₁ := gaussianFinite_IBP_error (.inl (a,b)) hf hC (hd.const_mul c) hD' hs
    (fun g hg => goeMatrix_updated_observable_derivative (hder g hg))
  have h₂ := gaussianFinite_IBP_error (.inl (b,a)) hf hC (hd.const_mul c) hD' hs
    (fun g hg => goeMatrix_updated_observable_derivative (by
      simpa only [symmetricElementary_comm b a] using hder g hg))
  rw [integral_const_mul] at h₁ h₂
  have hi (i : MatrixCoordinates ι) : Integrable (fun g : MatrixCoordinates ι → ℝ =>
      g i*H (goeMatrix r g)) μ := by
    simpa only [mul_comm] using (integrable_eval (i := i) IsGaussian.integrable_id).bdd_mul
      hf.continuous.aestronglyMeasurable (ae_of_all _ hC)
  have he : (∫ g, goeMatrix r g a b*H (goeMatrix r g) ∂μ) =
      c*((∫ g, g (.inl (a,b))*H (goeMatrix r g) ∂μ)+
        ∫ g, g (.inl (b,a))*H (goeMatrix r g) ∂μ) := by
    simp_rw [goeMatrix,mul_assoc,add_mul]
    rw [integral_const_mul,integral_add (hi _) (hi _)]
  change |(∫ g, goeMatrix r g a b*H (goeMatrix r g) ∂μ)-r*(∫ g, d g ∂μ)| ≤ _
  rw [he]
  have he' : c*((∫ g, g (.inl (a,b))*H (goeMatrix r g) ∂μ)+
        ∫ g, g (.inl (b,a))*H (goeMatrix r g) ∂μ)-r*(∫ g, d g ∂μ) =
      c*(((∫ g, g (.inl (a,b))*H (goeMatrix r g) ∂μ)-c*(∫ g, d g ∂μ))+
        ((∫ g, g (.inl (b,a))*H (goeMatrix r g) ∂μ)-c*(∫ g, d g ∂μ))) := by
    rw [← hc2]; ring
  rw [he',abs_mul,abs_of_nonneg hc]
  calc
    _ ≤ c*(|((∫ g, g (.inl (a,b))*H (goeMatrix r g) ∂μ)-c*(∫ g, d g ∂μ))|+
        |((∫ g, g (.inl (b,a))*H (goeMatrix r g) ∂μ)-c*(∫ g, d g ∂μ))|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hc
    _ ≤ c*(((L:ℝ)+c*D)*μ.real sᶜ+((L:ℝ)+c*D)*μ.real sᶜ) :=
      mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hc
    _ = _ := by
      change _ = (sqrt (2*r)*(L:ℝ)+r*D)*μ.real sᶜ
      have hec : sqrt (2*r) = 2*c := by dsimp [c]; ring
      rw [hec,← hc2]; ring

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNorm
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mul_symmetricElementary_mul (P Q : Matrix ι ι ℝ) (a b i k : ι) :
    (P*symmetricElementary a b*Q) i k = P i a*Q b k+P i b*Q a k := by
  simp [symmetricElementary,Matrix.mul_add,
    Matrix.mul_apply,Matrix.single_apply,ite_and,add_mul,Finset.sum_add_distrib,ite_mul]

lemma goe_inverse_contraction (K B : Matrix ι ι ℝ) (i : ι) :
    (∑ b, (K*B*symmetricElementary i b*K) b i) =
      (Matrix.trace (K*B))*K i i+∑ b, (K*B) b i*K b i := by
  simp_rw [mul_symmetricElementary_mul]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,Matrix.trace]
  exact add_comm _ _

lemma colVec_eq (M : Matrix ι ι ℝ) (k : ι) :
    colVec M k = M.toEuclideanLin.toContinuousLinearMap (EuclideanSpace.single k (1:ℝ)) := by
  ext i
  simp [colVec,Matrix.toLpLin_apply]

lemma colVec_norm_le (M : Matrix ι ι ℝ) (k : ι) : ‖colVec M k‖ ≤ opNorm M := by
  rw [colVec_eq]
  simpa only [PiLp.norm_single,norm_one,mul_one,opNorm] using!
    M.toEuclideanLin.toContinuousLinearMap.le_opNorm (EuclideanSpace.single k (1:ℝ))

lemma matrix_entry_le_opNorm (M : Matrix ι ι ℝ) (i k : ι) : |M i k| ≤ opNorm M := by
  have h : |M i k| ≤ ‖colVec M k‖ := by
    simpa only [colVec,Real.norm_eq_abs] using (PiLp.norm_apply_le (colVec M k) i)
  exact h.trans (colVec_norm_le M k)

lemma opNorm_mul (M N : Matrix ι ι ℝ) : opNorm (M*N) ≤ opNorm M*opNorm N := by
  have he : (M*N).toEuclideanLin.toContinuousLinearMap =
      M.toEuclideanLin.toContinuousLinearMap * N.toEuclideanLin.toContinuousLinearMap := by
    ext x i
    exact congrFun (congrArg (fun T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι => (T x).ofLp)
      (Matrix.toLpLin_mul 2 2 2 M N)) i
  exact (congrArg norm he).le.trans (norm_mul_le _ _)

lemma goe_cross_contraction_bound (K B : Matrix ι ι ℝ) (i : ι) :
    |∑ b, (K*B) b i*K b i| ≤ opNorm K*opNorm B*opNorm K := by
  have hh := abs_real_inner_le_norm (colVec (K*B) i) (colVec K i)
  change |∑ b, K b i*(K*B) b i| ≤ _ at hh
  simp_rw [mul_comm (K _ _)] at hh
  apply hh.trans
  calc
    ‖colVec (K*B) i‖*‖colVec K i‖ ≤ opNorm (K*B)*opNorm K :=
      mul_le_mul (colVec_norm_le _ _) (colVec_norm_le _ _) (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (opNorm_mul _ _) (norm_nonneg _)

theorem goe_inverse_loop_raw {r : ℝ} (hr : 0 ≤ r) (B : Matrix ι ι ℝ) (i : ι)
    {K : Matrix ι ι ℝ → Matrix ι ι ℝ} {L : ℝ≥0} {C D : ℝ}
    {s : Set (MatrixCoordinates ι → ℝ)}
    (hf : ∀ a b, LipschitzWith L (fun g => K (goeMatrix r g) a b))
    (hC : ∀ g a b, ‖K (goeMatrix r g) a b‖ ≤ C)
    (hD : ∀ g b, ‖(K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i‖ ≤ D)
    (hs : MeasurableSet s)
    (hder : ∀ g ∈ s, ∀ b, HasDerivAt
      (fun t : ℝ => K (goeMatrix r g+t • symmetricElementary i b) b i)
      ((K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i) 0) :
    |(∫ g, (goeMatrix r g*K (goeMatrix r g)) i i
        ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) -
      r*(∫ g, Matrix.trace (K (goeMatrix r g)*B)*K (goeMatrix r g) i i+
        ∑ b, (K (goeMatrix r g)*B) b i*K (goeMatrix r g) b i
        ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))| ≤
      (Fintype.card ι:ℝ)*(sqrt (2*r)*(L:ℝ)+r*D)*
        (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real sᶜ := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  let d (b : ι) (g : MatrixCoordinates ι → ℝ) :=
    (K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i
  have hK : Continuous (fun g => K (goeMatrix r g)) :=
    continuous_pi (fun a => continuous_pi (fun b => (hf a b).continuous))
  have hd (b : ι) : Continuous (d b) := by
    exact ((hK.mul continuous_const).mul continuous_const |>.mul hK).matrix_elem b i
  have hdint (b : ι) : Integrable (d b) μ :=
    Integrable.mono' (integrable_const D) (hd b).aestronglyMeasurable (ae_of_all _ (fun g => hD g b))
  have hwint (b : ι) : Integrable (fun g => goeMatrix r g i b*K (goeMatrix r g) b i) μ := by
    have he (a : MatrixCoordinates ι) : Integrable (fun g : MatrixCoordinates ι → ℝ => g a) μ :=
      integrable_eval (i := a) IsGaussian.integrable_id
    have hw : Integrable (fun g => goeMatrix r g i b) μ :=
      ((he (.inl (i,b))).add (he (.inl (b,i)))).const_mul _
    simpa only [mul_comm] using hw.bdd_mul (hf b i).continuous.aestronglyMeasurable
      (ae_of_all _ (fun g => hC g b i))
  have hb (b : ι) := goe_IBP_error hr i b (H := fun M => K M b i) (d := d b) (hf b i) (fun g => hC g b i)
    (hd b).measurable (fun g => hD g b) hs (fun g hg => hder g hg b)
  have he : (∫ g, Matrix.trace (K (goeMatrix r g)*B)*K (goeMatrix r g) i i+
        ∑ b, (K (goeMatrix r g)*B) b i*K (goeMatrix r g) b i ∂μ) =
      ∑ b, ∫ g, d b g ∂μ := by
    simp_rw [← goe_inverse_contraction]
    exact integral_finsetSum Finset.univ (fun b _ => hdint b)
  change |(∫ g, (goeMatrix r g*K (goeMatrix r g)) i i ∂μ)-r*(_)| ≤ _
  rw [he]
  simp_rw [Matrix.mul_apply]
  rw [integral_finsetSum Finset.univ (fun b _ => hwint b),Finset.mul_sum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ b, |(∫ g, goeMatrix r g i b*K (goeMatrix r g) b i ∂μ)-r*(∫ g, d b g ∂μ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : ι, (sqrt (2*r)*(L:ℝ)+r*D)*μ.real sᶜ :=
      Finset.sum_le_sum (fun b _ => hb b)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FrobeniusSq
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobenius_col_sq (M : Matrix ι ι ℝ) : ‖M‖^2 = ∑ k, ‖colVec M k‖^2 := by
  rw [frobenius_sq,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [EuclideanSpace.norm_sq_eq]
  simp [colVec,Real.norm_eq_abs,sq_abs]

lemma colVec_mul (M N : Matrix ι ι ℝ) (k : ι) :
    colVec (M*N) k = M.toEuclideanLin.toContinuousLinearMap (colVec N k) := by
  ext i
  rfl

lemma frobenius_mul_le_opNorm (M N : Matrix ι ι ℝ) : ‖M*N‖ ≤ opNorm M * ‖N‖ := by
  have hp : 0 ≤ opNorm M := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hp (norm_nonneg N))
  simp only [← sq]
  rw [frobenius_col_sq,mul_pow,frobenius_col_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [colVec_mul]
  have hh := M.toEuclideanLin.toContinuousLinearMap.le_opNorm (colVec N k)
  change ‖M.toEuclideanLin.toContinuousLinearMap (colVec N k)‖ ≤ opNorm M * ‖colVec N k‖ at hh
  nlinarith only [hh, norm_nonneg (M.toEuclideanLin.toContinuousLinearMap (colVec N k)),
    mul_nonneg hp (norm_nonneg (colVec N k))]

lemma opNorm_transpose (M : Matrix ι ι ℝ) : opNorm Mᵀ = opNorm M := by
  change ‖Mᵀ.toEuclideanLin.toContinuousLinearMap‖ = ‖M.toEuclideanLin.toContinuousLinearMap‖
  have he : Mᵀ.toEuclideanLin.toContinuousLinearMap =
      ContinuousLinearMap.adjoint M.toEuclideanLin.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_right]
    change (∑ i, (∑ k, M k i*x k)*y i) = ∑ i, x i * (∑ k, M i k*y k)
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,ContinuousLinearMap.adjoint.norm_map]

lemma frobenius_mul_le_opNorm_right (M N : Matrix ι ι ℝ) : ‖M*N‖ ≤ ‖M‖ * opNorm N := by
  rw [← Matrix.frobenius_norm_transpose (M*N),Matrix.transpose_mul]
  exact (frobenius_mul_le_opNorm Nᵀ Mᵀ).trans_eq (by rw [opNorm_transpose,Matrix.frobenius_norm_transpose,mul_comm])

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ExpDuhamel
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
namespace SKGap
section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]

lemma exp_duhamel (a b : A) :
    exp a - exp b = ∫ u : ℝ in (0 : ℝ)..1, exp ((1-u) • a) * (a-b) * exp (u • b) := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => exp ((1-u) • a) * exp (u • b))
      (-(exp ((1-u) • a) * (a-b) * exp (u • b))) u := by
    have h₁ := (hasDerivAt_exp_smul_const a (1-u)).scomp u ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u))
    have h₂ := hasDerivAt_exp_smul_const' b u
    convert h₁.mul h₂ using 1 <;> (try simp only [zero_sub, neg_smul, one_smul]) <;> noncomm_ring
  have hc : Continuous (fun u : ℝ => -(exp ((1-u) • a) * (a-b) * exp (u • b))) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hc.intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_neg, sub_self, zero_smul, NormedSpace.exp_zero, one_mul,
    sub_zero, one_smul, mul_one, neg_neg, neg_sub] using congrArg Neg.neg hh.symm

end Algebra

end SKGap

open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap
namespace ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobenius_mul_le_opNorm (M N : Matrix ι ι ℂ) : ‖M*N‖ ≤ opNorm M * ‖N‖ := by
  have hp : 0 ≤ opNorm M := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hp (norm_nonneg N))
  simp only [← sq]
  rw [frobenius_col_sq,mul_pow,frobenius_col_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [colVec_mul]
  have hh := (lin M).le_opNorm (colVec N k)
  change ‖lin M (colVec N k)‖ ≤ opNorm M * ‖colVec N k‖ at hh
  nlinarith only [hh,norm_nonneg (lin M (colVec N k)),mul_nonneg hp (norm_nonneg (colVec N k))]

lemma opNorm_adjoint (M : Matrix ι ι ℂ) : opNorm Mᴴ = opNorm M := by
  rw [opNorm,lin_adjoint,ContinuousLinearMap.adjoint.norm_map]
  rfl

lemma frobenius_mul_le_opNorm_right (M N : Matrix ι ι ℂ) : ‖M*N‖ ≤ ‖M‖ * opNorm N := by
  rw [← Matrix.frobenius_norm_conjTranspose (M*N),Matrix.conjTranspose_mul]
  exact (frobenius_mul_le_opNorm Nᴴ Mᴴ).trans_eq (by rw [opNorm_adjoint,Matrix.frobenius_norm_conjTranspose,mul_comm])

end ComplexMatrix
end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LinSub
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

section
open MeasureTheory Set NormedSpace
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma unitary_exp_smul (M : Matrix ι ι ℂ) (hM : Mᴴ = -M) (u : ℝ) :
    exp (u • M) ∈ unitary (Matrix ι ι ℂ) := by
  apply exp_mem_unitary_of_mem_skewAdjoint
  change (u • M)ᴴ = -(u • M)
  simp [hM]

lemma frobenius_exp_sub (M N : Matrix ι ι ℂ) (hM : Mᴴ = -M) (hN : Nᴴ = -N) :
    ‖exp M-exp N‖ ≤ ‖M-N‖ := by
  rw [show exp M-exp N = _ from SKGap.exp_duhamel M N]
  have hh (u : ℝ) : ‖exp ((1-u) • M) * (M-N) * exp (u • N)‖ = ‖M-N‖ := by
    rw [frobenius_mul_unitary _ _ (unitary_exp_smul N hN u),
      frobenius_unitary_mul _ _ (unitary_exp_smul M hM (1-u))]
  calc
    _ ≤ ∫ u : ℝ in (0 : ℝ)..1, ‖exp ((1-u) • M) * (M-N) * exp (u • N)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ‖M-N‖ := by simp only [hh]; simp

end

open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instPseudoMetrizableSpaceMatrixComplex_solutions : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℂ))

lemma lin_csmul (z : ℂ) (M : Matrix ι ι ℂ) : lin (z • M) = z • lin M :=
  (linEquiv (ι := ι)).map_smul z M

omit [Fintype ι] [DecidableEq ι] in
lemma imaginary_skew (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    (imaginary t M)ᴴ = -(imaginary t M) := by
  simp [imaginary,Matrix.conjTranspose_smul,hM,star_mul,mul_comm]

lemma imaginary_norm (t : ℝ) (M : Matrix ι ι ℂ) : ‖imaginary t M‖ = |t| * ‖M‖ := by
  simp [imaginary,norm_smul]

omit [Fintype ι] [DecidableEq ι] in
lemma imaginary_sub (t : ℝ) (M N : Matrix ι ι ℂ) :
    imaginary t (M-N) = imaginary t M-imaginary t N := by simp [imaginary,smul_sub]

lemma imaginary_exp_unitary (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    exp (imaginary t M) ∈ unitary (Matrix ι ι ℂ) := by
  simpa using unitary_exp_smul _ (imaginary_skew t M hM) 1

lemma imaginary_exp_norm (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    ‖exp (imaginary t M)‖ = ‖(1 : Matrix ι ι ℂ)‖ := by
  simpa using frobenius_unitary_mul (exp (imaginary t M)) 1 (imaginary_exp_unitary t M hM)

lemma imaginary_exp_opNorm_le (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    opNorm (exp (imaginary t M)) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [ContinuousLinearMap.norm_map_of_mem_unitary (lin_unitary _ (imaginary_exp_unitary t M hM))]
  simp

attribute [local instance] OAI.SKGap.ComplexMatrix.instContinuousENormMatrixComplex_solutions
lemma kernel_integrable {g : ℝ → ℂ} (hg : Integrable g) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    Integrable (fun t : ℝ => g t • exp (imaginary t M)) := by
  have hc : Continuous (fun t : ℝ => exp (imaginary t M)) := by dsimp [imaginary]; fun_prop
  apply (hg.norm.mul_const ‖(1 : Matrix ι ι ℂ)‖).mono' (hg.aestronglyMeasurable.smul hc.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖g t • exp (imaginary t M)‖ ≤ _
  rw [norm_smul,imaginary_exp_norm t M hM]

lemma kernelMatrix_lipschitz {g : ℝ → ℂ} (hg : Integrable g)
    (hg₁ : Integrable (fun t : ℝ => ‖g t‖*|t|))
    (M N : Matrix ι ι ℂ) (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖kernelMatrix g M-kernelMatrix g N‖ ≤ (∫ t : ℝ, ‖g t‖*|t|) * ‖M-N‖ := by
  rw [kernelMatrix,kernelMatrix,← integral_sub (kernel_integrable hg M hM) (kernel_integrable hg N hN)]
  calc
    _ ≤ ∫ t : ℝ, ‖g t • exp (imaginary t M)-g t • exp (imaginary t N)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (‖g t‖*|t|)*‖M-N‖ := by
      apply integral_mono ((kernel_integrable hg M hM).sub (kernel_integrable hg N hN)).norm (hg₁.mul_const _)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← smul_sub,norm_smul]
      have hh := frobenius_exp_sub _ _ (imaginary_skew t M hM) (imaginary_skew t N hN)
      rw [← imaginary_sub,imaginary_norm] at hh
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
    _ = _ := integral_mul_const _ _

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EntryLM
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

section
open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.SKGap.ComplexMatrix.instContinuousENormMatrixComplex_solutions_1
local instance instPseudoMetrizableSpaceMatrixComplex_solutions_1_r08d288_1 : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℂ))
lemma integral_entry {F : ℝ → Matrix ι ι ℂ} (hF : Integrable F) (i j : ι) :
    (∫ t : ℝ, F t) i j = ∫ t : ℝ, F t i j := by
  exact ((entryCLM i j).integral_comp_comm hF).symm

lemma conjugate_exp (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    conjugate U (exp M) = exp (conjugate U M) := by
  exact NormedSpace.map_exp (conjugate U).toRingHom (conjugateCLM U).continuous M

lemma conjugate_imaginary (U : unitary (Matrix ι ι ℂ)) (t : ℝ) (M : Matrix ι ι ℂ) :
    conjugate U (imaginary t M) = imaginary t (conjugate U M) := by
  exact (conjugate U).map_smul' _ _

lemma kernelMatrix_conjugate {g : ℝ → ℂ} (hg : Integrable g) (U : unitary (Matrix ι ι ℂ))
    (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    kernelMatrix g (conjugate U M) = conjugate U (kernelMatrix g M) := by
  have hi := (conjugateCLM U).integral_comp_comm (kernel_integrable hg M hM)
  change _ = (conjugateCLM U) (∫ t : ℝ, g t • exp (imaginary t M))
  calc
    _ = ∫ t : ℝ, (conjugateCLM U) (g t • exp (imaginary t M)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      change g t • exp (imaginary t (conjugate U M)) = conjugate U (g t • exp (imaginary t M))
      rw [map_smul,conjugate_exp,conjugate_imaginary]
    _ = _ := hi

lemma kernelMatrix_diagonal {g : ℝ → ℂ} (hg : Integrable g) (x : ι → ℝ) :
    kernelMatrix g (diagonal (fun i => (x i : ℂ))) =
      diagonal (fun i => ∫ t : ℝ, g t * Complex.exp ((t : ℂ)*Complex.I*(x i : ℂ))) := by
  have hD : (diagonal (fun i => (x i : ℂ)))ᴴ = diagonal (fun i => (x i : ℂ)) := by
    simp [Matrix.diagonal_conjTranspose]
  ext i j
  rw [kernelMatrix,integral_entry (kernel_integrable hg _ hD)]
  have hexp (t : ℝ) : exp (imaginary t (diagonal (fun i => (x i : ℂ)))) =
      diagonal (fun i => Complex.exp ((t : ℂ)*Complex.I*(x i : ℂ))) := by
    rw [imaginary,← diagonal_smul,Matrix.exp_diagonal]
    congr 1
    ext i
    rw [Pi.coe_exp,← Complex.exp_eq_exp_ℂ]
    rfl
  simp_rw [hexp,Matrix.smul_apply,smul_eq_mul]
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

lemma fourier_scalar_inverse (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∫ t : ℝ, (𝓕 f) t * Complex.exp ((t : ℂ)*Complex.I*((2*Real.pi*x : ℝ) : ℂ))) = f x := by
  have hh := congrArg (fun g : 𝓢(ℝ,ℂ) => g x) (show (𝓕⁻ (𝓕 f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ)) = f from FourierTransform.fourierInv_fourier_eq f)
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq'] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul,Real.inner_apply]
  conv_lhs => rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

lemma schwartzMatrix_diagonal (f : 𝓢(ℝ,ℂ)) (x : ι → ℝ) :
    schwartzMatrix f (diagonal (fun i => (x i : ℂ))) = diagonal (fun i => f (x i)) := by
  rw [schwartzMatrix,← diagonal_smul]
  have heq : (2*Real.pi : ℝ) • (fun i => (x i : ℂ)) = fun i => ((2*Real.pi*x i : ℝ) : ℂ) := by
    ext i; simp
  rw [heq,kernelMatrix_diagonal (𝓕 f).integrable]
  congr 1
  ext i
  exact fourier_scalar_inverse f (x i)

lemma schwartzMatrix_conjugate (f : 𝓢(ℝ,ℂ)) (U : unitary (Matrix ι ι ℂ))
    (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    schwartzMatrix f (conjugate U M) = conjugate U (schwartzMatrix f M) := by
  have heq : (2*Real.pi : ℝ) • conjugate U M = conjugate U ((2*Real.pi : ℝ) • M) := by
    simp [conjugate,Unitary.conjStarAlgAut_apply]
  rw [schwartzMatrix,heq]
  exact kernelMatrix_conjugate (𝓕 f).integrable U _ (by simp [hM])

lemma schwartzMatrix_spectral (f : 𝓢(ℝ,ℂ)) (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    schwartzMatrix f M = conjugate hM.eigenvectorUnitary (diagonal (fun i => f (hM.eigenvalues i))) := by
  conv_lhs => rw [hM.spectral_theorem]
  change schwartzMatrix f (conjugate hM.eigenvectorUnitary (diagonal (fun i => (hM.eigenvalues i : ℂ)))) = _
  rw [schwartzMatrix_conjugate f _ _ (by simp [Matrix.diagonal_conjTranspose]),schwartzMatrix_diagonal]

end

open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_kernelMatrix {g : ℝ → ℂ} (hg : Integrable g)
    (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    opNorm (kernelMatrix g M) ≤ ∫ t : ℝ, ‖g t‖ := by
  let : CompleteSpace (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    ContinuousLinearMap.instCompleteSpace
  have hi := linCLM.integral_comp_comm (kernel_integrable hg M hM)
  change ‖linCLM (∫ t : ℝ, g t • exp (imaginary t M))‖ ≤ _
  calc
    _ = ‖∫ t : ℝ, linCLM (g t • exp (imaginary t M))‖ := congrArg norm hi.symm
    _ ≤ ∫ t : ℝ, ‖linCLM (g t • exp (imaginary t M))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖g t‖ := by
      apply integral_mono (linCLM.integrable_comp (kernel_integrable hg M hM)).norm hg.norm
      intro t
      change ‖lin (g t • exp (imaginary t M))‖ ≤ _
      rw [lin_csmul,norm_smul]
      exact (mul_le_mul_of_nonneg_left (imaginary_exp_opNorm_le t M hM) (norm_nonneg _)).trans_eq (mul_one _)

lemma schwartzMatrix_opNorm (f : 𝓢(ℝ,ℂ)) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    opNorm (schwartzMatrix f M) ≤ ∫ t : ℝ, ‖(𝓕 f) t‖ :=
  opNorm_kernelMatrix (𝓕 f).integrable _ (by simp [hM])

lemma schwartzMatrix_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (hspec : ∀ i, hM.eigenvalues i ∈ Icc lo hi) :
    schwartzMatrix f M = M⁻¹ := by
  rw [schwartzMatrix_spectral f M hM]
  symm
  apply Matrix.inv_eq_left_inv
  conv_lhs => rhs; rw [hM.spectral_theorem]
  change conjugate hM.eigenvectorUnitary (diagonal (fun i => f (hM.eigenvalues i))) *
    conjugate hM.eigenvectorUnitary (diagonal (fun i => (hM.eigenvalues i : ℂ))) = 1
  rw [← map_mul,diagonal_mul_diagonal]
  have hd : diagonal (fun i => f (hM.eigenvalues i) * (hM.eigenvalues i : ℂ)) = (1 : Matrix ι ι ℂ) := by
    have hz (i : ι) : (hM.eigenvalues i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le hlo (hspec i).1)
    simp_rw [hf _ (hspec _),inv_mul_cancel₀ (hz _)]
    exact diagonal_one
  rw [hd,map_one]

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_FourierMoment
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix
open MeasureTheory NormedSpace
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fourierMoment_integrable (f : 𝓢(ℝ,ℂ)) (k : ℕ) :
    Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|^k) := by
  simpa only [Real.norm_eq_abs,mul_comm] using (𝓕 f).integrable_pow_mul volume k

lemma schwartzMatrix_lipschitz (f : 𝓢(ℝ,ℂ)) (M N : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖schwartzMatrix f M-schwartzMatrix f N‖ ≤
      (2*Real.pi*fourierMoment f 1)*‖M-N‖ := by
  have hf₁ : Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|) := by
    simpa only [pow_one] using fourierMoment_integrable f 1
  have hh := kernelMatrix_lipschitz (𝓕 f).integrable hf₁
    ((2*Real.pi:ℝ) • M) ((2*Real.pi:ℝ) • N) (by simp [hM]) (by simp [hN])
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2*Real.pi:ℝ))] at hh
  exact hh.trans_eq (by simp only [fourierMoment,pow_one]; ring)

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNormKernelMatrixSub
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_nonneg (M : Matrix ι ι ℂ) : 0 ≤ opNorm M := norm_nonneg _
lemma opNorm_add (M N : Matrix ι ι ℂ) : opNorm (M+N) ≤ opNorm M+opNorm N := by
  change ‖linEquiv (M+N)‖ ≤ _
  rw [(linEquiv (ι := ι)).map_add]
  exact norm_add_le _ _
lemma opNorm_sub (M N : Matrix ι ι ℂ) : opNorm (M-N) ≤ opNorm M+opNorm N := by
  change ‖lin (M-N)‖ ≤ _
  have hh : lin (M-N) = lin M-lin N := linEquiv.map_sub M N
  rw [hh]
  exact norm_sub_le _ _
lemma opNorm_mul (M N : Matrix ι ι ℂ) : opNorm (M*N) ≤ opNorm M*opNorm N := by
  change ‖lin (M*N)‖ ≤ _
  rw [lin_mul]
  exact norm_mul_le _ _
lemma opNorm_one_le : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  rw [opNorm,lin_one]
  exact ContinuousLinearMap.norm_id_le

lemma sandwich_frobenius (D E : Matrix ι ι ℂ) :
    ‖D*E*D‖ ≤ opNorm D^2*‖E‖ := by
  calc
    _ ≤ ‖D*E‖*opNorm D := frobenius_mul_le_opNorm_right _ _
    _ ≤ (opNorm D*‖E‖)*opNorm D := mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _)
    _ = _ := by ring

lemma sandwich_opNorm (D E : Matrix ι ι ℂ) :
    opNorm (D*E*D) ≤ opNorm D^2*opNorm E := by
  calc
    _ ≤ opNorm (D*E)*opNorm D := opNorm_mul _ _
    _ ≤ (opNorm D*opNorm E)*opNorm D := mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _)
    _ = _ := by ring

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SandShift
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sandShift_sub (B D M N : Matrix ι ι ℂ) :
    sandShift B D M-sandShift B D N = -(D*(M-N)*D) := by dsimp [sandShift]; noncomm_ring

lemma sandShift_lipschitz (B D M N : Matrix ι ι ℂ) :
    ‖sandShift B D M-sandShift B D N‖ ≤ opNorm D^2*‖M-N‖ := by
  rw [sandShift_sub,norm_neg]
  exact sandwich_frobenius _ _

lemma schwartzMatrix_sandShift_lipschitz (f : 𝓢(ℝ,ℂ)) (B D M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖schwartzMatrix f (sandShift B D M)-schwartzMatrix f (sandShift B D N)‖ ≤
      (2*Real.pi*fourierMoment f 1)*opNorm D^2*‖M-N‖ := by
  exact (schwartzMatrix_lipschitz f _ _ (sandShift_hermitian _ _ _ hB hD hM)
    (sandShift_hermitian _ _ _ hB hD hN)).trans
    ((mul_le_mul_of_nonneg_left (sandShift_lipschitz B D M N)
      (by positivity [fourierMoment_nonneg f 1])).trans_eq (by ring))

end SKGap.ComplexMatrix

noncomputable section
open Set Real
open scoped Topology
namespace SKGap
section Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convexProject_mem {K : Set E} (hK : ClosedConvexNonempty K) (x : E) :
    convexProject hK x ∈ K :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)).1

lemma convexProject_minimal {K : Set E} (hK : ClosedConvexNonempty K) (x : E) :
    ‖x-convexProject hK x‖ = ⨅ y : K, ‖x-y‖ :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)).2

lemma convexProject_inner {K : Set E} (hK : ClosedConvexNonempty K) (x : E)
    {y : E} (hy : y ∈ K) :
    inner ℝ (x-convexProject hK x) (y-convexProject hK x) ≤ 0 := by
  exact ((norm_eq_iInf_iff_real_inner_le_zero hK.convex (convexProject_mem hK x)).mp
    (convexProject_minimal hK x)) y hy

lemma convexProject_lipschitz {K : Set E} (hK : ClosedConvexNonempty K) :
    LipschitzWith 1 (convexProject hK) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  let p := convexProject hK x
  let q := convexProject hK y
  have hx := convexProject_inner hK x (convexProject_mem hK y)
  have hy := convexProject_inner hK y (convexProject_mem hK x)
  change inner ℝ (x-p) (q-p) ≤ 0 at hx
  change inner ℝ (y-q) (p-q) ≤ 0 at hy
  have hi : ‖p-q‖^2 ≤ inner ℝ (p-q) (x-y) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right,real_inner_comm] at *
    nlinarith
  have hb := real_inner_le_norm (p-q) (x-y)
  nlinarith [norm_nonneg (p-q),norm_nonneg (x-y)]

lemma convexProject_eq_self {K : Set E} (hK : ClosedConvexNonempty K) {x : E}
    (hx : x ∈ K) : convexProject hK x = x := by
  have hh := convexProject_inner hK x hx
  rw [real_inner_self_eq_norm_sq] at hh
  have hz : ‖x-convexProject hK x‖ = 0 := by nlinarith [norm_nonneg (x-convexProject hK x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end Projection
end SKGap

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Vectorize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
namespace SKGap.ComplexMatrix
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixProject_lipschitz (R : ℝ) (hR : 0 ≤ R) :
    LipschitzWith 1 (matrixProject (ι := ι) R hR) :=
  SKGap.convexProject_lipschitz _

lemma matrixProject_bound (R : ℝ) (hR : 0 ≤ R) (M : Matrix ι ι ℂ) :
    (matrixProject R hR M)ᴴ = matrixProject R hR M ∧ opNorm (matrixProject R hR M) ≤ R :=
  SKGap.convexProject_mem (hermitianBall_good (ι := ι) hR) M

lemma matrixProject_eq_self (R : ℝ) (hR : 0 ≤ R) (M : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hMR : opNorm M ≤ R) : matrixProject R hR M = M :=
  SKGap.convexProject_eq_self _ ⟨hM,hMR⟩

end SKGap.ComplexMatrix

namespace SKGap.ComplexMatrix
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixProject_sub_norm (R : ℝ) (hR : 0 ≤ R) (M N : Matrix ι ι ℂ) :
    ‖matrixProject R hR M-matrixProject R hR N‖ ≤ ‖M-N‖ := by
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using (matrixProject_lipschitz R hR).dist_le_mul M N

lemma truncatedG_opNorm (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (B D M : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) :
    opNorm (truncatedG f R hR B D M) ≤ opNorm D^2*fourierMoment f 0 := by
  have hS := sandShift_hermitian B D (matrixProject R hR M) hB hD (matrixProject_bound R hR M).1
  apply (sandwich_opNorm D _).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  simpa only [fourierMoment,pow_zero,mul_one] using schwartzMatrix_opNorm f _ hS

lemma truncatedG_sub_norm (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (B D M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) :
    ‖truncatedG f R hR B D M-truncatedG f R hR B D N‖ ≤
      (2*Real.pi*fourierMoment f 1)*opNorm D^4*‖M-N‖ := by
  have hL : 0 ≤ 2*Real.pi*fourierMoment f 1 := by have := fourierMoment_nonneg f 1; positivity
  have hM := (matrixProject_bound R hR M).1
  have hN := (matrixProject_bound R hR N).1
  have hl := schwartzMatrix_sandShift_lipschitz f B D (matrixProject R hR M) (matrixProject R hR N) hB hD hM hN
  have he : truncatedG f R hR B D M-truncatedG f R hR B D N =
      D*(schwartzMatrix f (sandShift B D (matrixProject R hR M))-
        schwartzMatrix f (sandShift B D (matrixProject R hR N)))*D := by dsimp [truncatedG]; noncomm_ring
  rw [he]
  calc
    _ ≤ opNorm D^2*‖schwartzMatrix f (sandShift B D (matrixProject R hR M))-
        schwartzMatrix f (sandShift B D (matrixProject R hR N))‖ := sandwich_frobenius _ _
    _ ≤ opNorm D^2*((2*Real.pi*fourierMoment f 1)*opNorm D^2*‖matrixProject R hR M-matrixProject R hR N‖) :=
      mul_le_mul_of_nonneg_left hl (sq_nonneg _)
    _ ≤ opNorm D^2*((2*Real.pi*fourierMoment f 1)*opNorm D^2*‖M-N‖) := by
      gcongr
      exact matrixProject_sub_norm _ _ _ _
    _ = _ := by ring

lemma truncatedG_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    (R : ℝ) (hR : 0 ≤ R) (B D M : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D)
    (hM : Mᴴ = M) (hMR : opNorm M ≤ R)
    (hspec : ∀ i, Matrix.IsHermitian.eigenvalues (sandShift_hermitian B D M hB hD hM) i ∈ Set.Icc lo hi) :
    truncatedG f R hR B D M = D*(sandShift B D M)⁻¹*D := by
  rw [truncatedG,matrixProject_eq_self R hR M hM hMR,
    schwartzMatrix_eq_inverse f hlo hf _ (sandShift_hermitian B D M hB hD hM) hspec]

end SKGap.ComplexMatrix

namespace SKGap.ComplexMatrix
open scoped SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagonalChange_nonneg (D D' : Matrix ι ι ℂ) : 0 ≤ diagonalChange D D' := by
  unfold diagonalChange
  positivity [opNorm_nonneg D,opNorm_nonneg D',opNorm_nonneg (D-D')]
lemma shiftChange_nonneg {R : ℝ} (hR : 0 ≤ R) (B B' D D' : Matrix ι ι ℂ) :
    0 ≤ shiftChange R B B' D D' := by
  unfold shiftChange
  positivity [opNorm_nonneg (B-B'),diagonalChange_nonneg D D']
lemma g_constants_nonneg (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' : Matrix ι ι ℂ) :
    0 ≤ gBound f D ∧ 0 ≤ gLip f D ∧ 0 ≤ gChange f R B B' D D' ∧ 0 ≤ gMixed f R B B' D D' := by
  have h₀ := fourierMoment_nonneg f 0
  have h₁ := (fl_nonneg f).1
  have h₂ := (fl_nonneg f).2
  have hd := diagonalChange_nonneg D D'
  have hs := shiftChange_nonneg hR B B' D D'
  unfold gBound gLip gChange gMixed
  exact ⟨by positivity,by positivity,by positivity,by positivity⟩

lemma projected_sub_bound {R : ℝ} (hR : 0 ≤ R) (M C : Matrix ι ι ℂ) :
    opNorm (matrixProject R hR M-C) ≤ R+opNorm C :=
  (opNorm_sub _ _).trans (add_le_add_left (matrixProject_bound R hR M).2 _)

lemma truncatedK_opNorm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B D C M : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D) :
    opNorm (truncatedK f R hR B D C M) ≤ kBound f R D C := by
  apply (opNorm_add _ _).trans
  apply add_le_add opNorm_one_le
  exact (opNorm_mul _ _).trans
    (mul_le_mul (truncatedG_opNorm _ _ _ _ _ _ hB hD) (projected_sub_bound hR M C)
      (opNorm_nonneg _) (g_constants_nonneg f hR B B D D).1)

lemma truncatedK_sub_norm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B D C M N : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D) :
    ‖truncatedK f R hR B D C M-truncatedK f R hR B D C N‖ ≤
      kLip f R D C*‖M-N‖ := by
  let G := truncatedG f R hR B D
  let P : Matrix ι ι ℂ → Matrix ι ι ℂ := matrixProject R hR
  have he : truncatedK f R hR B D C M-truncatedK f R hR B D C N =
      (G M-G N)*(P M-C)+G N*(P M-P N) := by dsimp [truncatedK,G,P]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(G M-G N)*(P M-C)‖+‖G N*(P M-P N)‖ := norm_add_le _ _
    _ ≤ ‖G M-G N‖*opNorm (P M-C)+opNorm (G N)*‖P M-P N‖ :=
      add_le_add (frobenius_mul_le_opNorm_right _ _) (frobenius_mul_le_opNorm _ _)
    _ ≤ (gLip f D*‖M-N‖)*(R+opNorm C)+gBound f D*‖M-N‖ := by
      apply add_le_add
      · exact mul_le_mul (truncatedG_sub_norm _ _ _ _ _ _ _ hB hD) (projected_sub_bound hR M C)
          (opNorm_nonneg _) (mul_nonneg (g_constants_nonneg f hR B B D D).2.1 (norm_nonneg _))
      · exact mul_le_mul (truncatedG_opNorm _ _ _ _ _ _ hB hD) (matrixProject_sub_norm _ _ _ _)
          (norm_nonneg _) (g_constants_nonneg f hR B B D D).1
    _ = _ := by unfold kLip; ring

end SKGap.ComplexMatrix

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_InverseSubSquareMul
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap.ResolventIdentity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {𝕜 : Type*} [RCLike 𝕜]

lemma inverse_one_sub_square_mul (D V : Matrix ι ι 𝕜)
    (hS : IsUnit (1-D*V*D)) :
    (1-D*D*V)⁻¹ = 1+D*(1-D*V*D)⁻¹*D*V := by
  apply Matrix.inv_eq_right_inv
  have hSS : (1-D*V*D)*(1-D*V*D)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (((1-D*V*D).isUnit_iff_isUnit_det).mp hS)
  calc
    _ = (1-D*D*V)+D*((1-D*V*D)*(1-D*V*D)⁻¹)*D*V := by noncomm_ring
    _ = 1 := by rw [hSS]; noncomm_ring

lemma inverse_one_sub_square_mul_unit (D V : Matrix ι ι 𝕜)
    (hS : IsUnit (1-D*V*D)) : IsUnit (1-D*D*V) := by
  have hSS : (1-D*V*D)*(1-D*V*D)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (((1-D*V*D).isUnit_iff_isUnit_det).mp hS)
  apply ((1-D*D*V).isUnit_iff_isUnit_det).mpr
  have hh : (1-D*D*V)*(1+D*(1-D*V*D)⁻¹*D*V) = 1 := by
    calc
      _ = (1-D*D*V)+D*((1-D*V*D)*(1-D*V*D)⁻¹)*D*V := by noncomm_ring
      _ = 1 := by rw [hSS]; noncomm_ring
  exact Matrix.isUnit_det_of_right_inverse hh

end SKGap.ResolventIdentity

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SandShiftSpecial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap.ComplexMatrix
open scoped SchwartzMap ComplexOrder
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sandShift_special (D C M : Matrix ι ι ℂ) :
    sandShift (1+D*C*D) D M = 1-D*(M-C)*D := by
  dsimp [sandShift]; noncomm_ring

lemma truncatedK_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M : Matrix ι ι ℂ)
    (hD : Dᴴ = D) (hC : Cᴴ = C) (hM : Mᴴ = M) (hMR : opNorm M ≤ R)
    (hspec : ∀ i, Matrix.IsHermitian.eigenvalues (sandShift_hermitian (1+D*C*D) D M
      (by simp [Matrix.conjTranspose_mul,hD,hC,mul_assoc]) hD hM) i ∈ Icc lo hi) :
    truncatedK f R hR (1+D*C*D) D C M = (1-D*D*(M-C))⁻¹ := by
  have hB : (1+D*C*D)ᴴ = 1+D*C*D := by simp [Matrix.conjTranspose_mul,hD,hC,mul_assoc]
  have hS : IsUnit (sandShift (1+D*C*D) D M) :=
    ((Matrix.IsHermitian.posDef_iff_eigenvalues_pos (sandShift_hermitian _ _ _ hB hD hM)).mpr
      (fun i => hlo.trans_le (hspec i).1)).isUnit
  rw [truncatedK,truncatedG_eq_inverse f hlo hf R hR _ _ _ hB hD hM hMR hspec,
    matrixProject_eq_self R hR M hM hMR,sandShift_special]
  exact (SKGap.ResolventIdentity.inverse_one_sub_square_mul D (M-C) (by
    simpa only [sandShift_special] using hS)).symm

end SKGap.ComplexMatrix

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LiftMatrix
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma vec_norm_split (x : EuclideanSpace ℂ ι) :
    ‖x‖^2 = ‖reVec x‖^2+‖imVec x‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change ‖x i‖^2 = ‖(x i).re‖^2+‖(x i).im‖^2
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [Real.norm_eq_abs]
  rw [sq_abs,sq_abs]
  ring

omit [DecidableEq ι] in
lemma norm_liftVec (x : EuclideanSpace ℝ ι) : ‖liftVec x‖ = ‖x‖ := by
  have hh : ‖liftVec x‖^2 = ‖x‖^2 := by simp [EuclideanSpace.norm_sq_eq,liftVec]
  nlinarith [norm_nonneg (liftVec x),norm_nonneg x]

lemma reVec_clin (M : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    reVec (clin (liftMatrix M) x) = rlin M (reVec x) := by
  ext i
  change (∑ j, (M i j : ℂ)*x j).re = ∑ j, M i j*(x j).re
  simp

lemma imVec_clin (M : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    imVec (clin (liftMatrix M) x) = rlin M (imVec x) := by
  ext i
  change (∑ j, (M i j : ℂ)*x j).im = ∑ j, M i j*(x j).im
  simp

lemma clin_liftVec (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    clin (liftMatrix M) (liftVec x) = liftVec (rlin M x) := by
  ext i
  change (∑ j, (M i j : ℂ)*(x j : ℂ)) = ((∑ j, M i j*x j : ℝ) : ℂ)
  simp

lemma operator_norm_lift (M : Matrix ι ι ℝ) : ‖clin (liftMatrix M)‖ = opNorm M := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simp only [← sq]
    change ‖clin (liftMatrix M) x‖^2 ≤ (opNorm M*‖x‖)^2
    rw [vec_norm_split,reVec_clin,imVec_clin,mul_pow,vec_norm_split,mul_add]
    have hr := (rlin M).le_opNorm (reVec x)
    have hi := (rlin M).le_opNorm (imVec x)
    change ‖rlin M (reVec x)‖ ≤ opNorm M*‖reVec x‖ at hr
    change ‖rlin M (imVec x)‖ ≤ opNorm M*‖imVec x‖ at hi
    nlinarith [norm_nonneg (rlin M (reVec x)),norm_nonneg (rlin M (imVec x)),
      mul_nonneg (norm_nonneg (rlin M)) (norm_nonneg (reVec x)),
      mul_nonneg (norm_nonneg (rlin M)) (norm_nonneg (imVec x))]
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have hh := (clin (liftMatrix M)).le_opNorm (liftVec x)
    rwa [clin_liftVec,norm_liftVec,norm_liftVec] at hh

lemma norm_liftMatrix (M : Matrix ι ι ℝ) : ‖liftMatrix M‖ = ‖M‖ :=
  Matrix.frobenius_norm_map_eq M Complex.ofReal (fun x => by simp)

omit [Fintype ι] [DecidableEq ι] in
lemma liftMatrix_sub (M N : Matrix ι ι ℝ) :
    liftMatrix (M-N) = liftMatrix M-liftMatrix N := by ext i j; simp [liftMatrix]
omit [DecidableEq ι] in
lemma liftMatrix_mul (M N : Matrix ι ι ℝ) :
    liftMatrix (M*N) = liftMatrix M*liftMatrix N := by
  exact Matrix.map_mul (f := Complex.ofRealHom)
omit [Fintype ι] in
lemma liftMatrix_one : liftMatrix (1 : Matrix ι ι ℝ) = 1 :=
  Matrix.map_one Complex.ofReal (by simp) (by simp)
omit [Fintype ι] [DecidableEq ι] in
lemma liftMatrix_conjTranspose (M : Matrix ι ι ℝ) :
    (liftMatrix M)ᴴ = liftMatrix Mᵀ := by ext i j; simp [liftMatrix]
omit [Fintype ι] [DecidableEq ι] in
lemma liftMatrix_hermitian (M : Matrix ι ι ℝ) (hM : Mᵀ = M) :
    (liftMatrix M)ᴴ = liftMatrix M := by rw [liftMatrix_conjTranspose,hM]

end SKGap.RealComplex

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RealPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma norm_realPart_le (M : Matrix ι ι ℂ) : ‖realPart M‖ ≤ ‖M‖ := by
  rw [Matrix.frobenius_norm_def,Matrix.frobenius_norm_def]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  simp only [realPart,Matrix.map_apply,Real.rpow_two]
  exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (M i k)) 2

omit [Fintype ι] [DecidableEq ι] in
lemma realPart_sub (M N : Matrix ι ι ℂ) : realPart (M-N) = realPart M-realPart N := by
  ext i k; simp [realPart]
omit [Fintype ι] [DecidableEq ι] in
lemma realPart_liftMatrix (M : Matrix ι ι ℝ) : realPart (liftMatrix M) = M := by
  ext i k; simp [realPart,liftMatrix]

omit [DecidableEq ι] in
lemma reVec_norm_le (x : EuclideanSpace ℂ ι) : ‖reVec x‖ ≤ ‖x‖ := by
  have h := vec_norm_split x
  nlinarith [sq_nonneg ‖imVec x‖,norm_nonneg (reVec x),norm_nonneg x]

lemma realPart_operator (M : Matrix ι ι ℂ) (x : EuclideanSpace ℝ ι) :
    rlin (realPart M) x = reVec (clin M (liftVec x)) := by
  ext i
  change (∑ k, (M i k).re*x k) = (∑ k, M i k*(x k : ℂ)).re
  simp

lemma operator_realPart_le (M : Matrix ι ι ℂ) : opNorm (realPart M) ≤ ‖clin M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [realPart_operator]
  exact (reVec_norm_le _).trans ((clin M).le_opNorm (liftVec x) |>.trans_eq (by rw [norm_liftVec]))

lemma liftMatrix_inverse {M : Matrix ι ι ℝ} (hM : IsUnit M) :
    liftMatrix M⁻¹ = (liftMatrix M)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← liftMatrix_mul,Matrix.mul_nonsing_inv M (M.isUnit_iff_isUnit_det.mp hM),liftMatrix_one]

end SKGap.RealComplex

namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius SchwartzMap ComplexOrder
open SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma liftMatrix_isUnit_iff (M : Matrix ι ι ℝ) : IsUnit (liftMatrix M) ↔ IsUnit M := by
  rw [(liftMatrix M).isUnit_iff_isUnit_det,M.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero,isUnit_iff_ne_zero]
  have he : (liftMatrix M).det = (M.det : ℂ) := (Complex.ofRealHom.map_det M).symm
  rw [he]
  exact not_congr Complex.ofReal_eq_zero

lemma realTruncatedK_sub_norm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (D C M N : Matrix ι ι ℝ) (hD : Dᵀ = D) (hC : Cᵀ = C) :
    ‖realTruncatedK f R hR D C M-realTruncatedK f R hR D C N‖ ≤
      kLip f R (liftMatrix D) (liftMatrix C)*‖M-N‖ := by
  have hD' := liftMatrix_hermitian D hD
  have hC' := liftMatrix_hermitian C hC
  have hB : (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ =
      1+liftMatrix D*liftMatrix C*liftMatrix D := by simp [Matrix.conjTranspose_mul,hD',hC',mul_assoc]
  unfold realTruncatedK
  rw [← realPart_sub]
  apply (norm_realPart_le _).trans
  simpa only [← liftMatrix_sub,norm_liftMatrix] using
    truncatedK_sub_norm f hR _ _ _ (liftMatrix M) (liftMatrix N) hB hD'

lemma realTruncatedK_opNorm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (D C M : Matrix ι ι ℝ) (hD : Dᵀ = D) (hC : Cᵀ = C) :
    SKGap.opNorm (realTruncatedK f R hR D C M) ≤ kBound f R (liftMatrix D) (liftMatrix C) := by
  have hD' := liftMatrix_hermitian D hD
  have hC' := liftMatrix_hermitian C hC
  have hB : (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ =
      1+liftMatrix D*liftMatrix C*liftMatrix D := by simp [Matrix.conjTranspose_mul,hD',hC',mul_assoc]
  exact (operator_realPart_le _).trans (truncatedK_opNorm f hR _ _ _ _ hB hD')

lemma realTruncatedK_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (hM : Mᵀ = M) (hMR : SKGap.opNorm M ≤ R)
    (hl : lo ≤ SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M-C)*D)))
    (hu : -hi ≤ SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M-C)*D))) :
    realTruncatedK f R hR D C M = (1-D*D*(M-C))⁻¹ := by
  have hD' := liftMatrix_hermitian D hD
  have hC' := liftMatrix_hermitian C hC
  have hM' := liftMatrix_hermitian M hM
  have hB : (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ =
      1+liftMatrix D*liftMatrix C*liftMatrix D := by simp [Matrix.conjTranspose_mul,hD',hC',mul_assoc]
  have hid : sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M) =
      liftMatrix (1-D*(M-C)*D) := by
    rw [sandShift_special]; simp only [liftMatrix_sub,liftMatrix_mul,liftMatrix_one]
  have hS : (sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M)).IsHermitian :=
    sandShift_hermitian _ _ _ hB hD' hM'
  have hspec : ∀ i, hS.eigenvalues i ∈ Set.Icc lo hi := by
    intro i
    have hm := SKGap.ComplexSpectral.eigenvalue_lower_bound hS i
    have hp := SKGap.ComplexSpectral.eigenvalue_upper_bound hS i
    have hl' : lo ≤ SKGap.ComplexSpectral.lowerRayleigh
        (sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M)) := by
      simpa only [hid] using hl
    have hu' : -hi ≤ SKGap.ComplexSpectral.lowerRayleigh
        (-sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M)) := by
      simpa only [hid] using hu
    constructor <;> linarith
  have hsunit : IsUnit (1-liftMatrix D*(liftMatrix M-liftMatrix C)*liftMatrix D) := by
    rw [← sandShift_special]
    exact (hS.posDef_iff_eigenvalues_pos.mpr (fun i => hlo.trans_le (hspec i).1)).isUnit
  have hrunit : IsUnit (1-D*D*(M-C)) := by
    apply (liftMatrix_isUnit_iff _).mp
    simpa only [liftMatrix_sub,liftMatrix_mul,liftMatrix_one] using
      SKGap.ResolventIdentity.inverse_one_sub_square_mul_unit (liftMatrix D) (liftMatrix M-liftMatrix C) hsunit
  unfold realTruncatedK
  rw [truncatedK_eq_inverse f hlo hf hR _ _ _ hD' hC' hM'
    (by simpa only [SKGap.ComplexMatrix.opNorm,SKGap.ComplexMatrix.lin,operator_norm_lift] using hMR) hspec]
  rw [← liftMatrix_one,← liftMatrix_mul,← liftMatrix_sub,← liftMatrix_mul,← liftMatrix_sub,
    ← liftMatrix_inverse hrunit,realPart_liftMatrix]

lemma real_matrix_hasDerivAt_inverse {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {t : ℝ}
    (hQ : HasDerivAt Q Q' t) (hunit : IsUnit (Q t)) :
    HasDerivAt (fun s => (Q s)⁻¹) (-(Q t)⁻¹*Q'*(Q t)⁻¹) t := by
  obtain ⟨u,hu⟩ := hunit
  have hfi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hfi
  have hi := hfi.comp_hasDerivAt t hQ
  have hv : (↑u⁻¹ : Matrix ι ι ℝ) = (Q t)⁻¹ := by
    rw [← hu,Matrix.nonsing_inv_eq_ringInverse,Ring.inverse_unit]
  simpa only [Function.comp_def,← Matrix.nonsing_inv_eq_ringInverse,_root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply,hv,neg_mul] using! hi

lemma continuous_realOpNorm : Continuous (SKGap.opNorm : Matrix ι ι ℝ → ℝ) := by
  have h : Continuous (fun M : Matrix ι ι ℝ => liftMatrix M) := by
    dsimp [liftMatrix]; fun_prop
  have hc := SKGap.ComplexMatrix.continuous_lin.norm.comp h
  simpa only [Function.comp_def,SKGap.ComplexMatrix.lin,operator_norm_lift] using hc

lemma realTruncatedK_eventually_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M E : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (hM : Mᵀ = M) (hE : Eᵀ = E)
    (hMR : SKGap.opNorm M < R)
    (hl : lo < SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M-C)*D)))
    (hu : -hi < SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M-C)*D))) :
    (fun t : ℝ => realTruncatedK f R hR D C (M+t • E)) =ᶠ[𝓝 (0:ℝ)]
      (fun t => (1-D*D*(M+t • E-C))⁻¹) := by
  have hcont : Continuous (fun t : ℝ => liftMatrix (1-D*(M+t • E-C)*D)) := by
    dsimp [liftMatrix]; fun_prop
  have hcont' : Continuous (fun t : ℝ => SKGap.opNorm (M+t • E)) :=
    continuous_realOpNorm.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hl' : ∀ᶠ t in 𝓝 (0:ℝ), lo < SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M+t • E-C)*D)) :=
    (SKGap.ComplexSpectral.continuous_lowerRayleigh.comp hcont).continuousAt.eventually
      (lt_mem_nhds (by simpa using hl))
  have hu' : ∀ᶠ t in 𝓝 (0:ℝ), -hi < SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M+t • E-C)*D)) :=
    (SKGap.ComplexSpectral.continuous_lowerRayleigh.comp hcont.neg).continuousAt.eventually
      (lt_mem_nhds (by simpa using hu))
  have hm' : ∀ᶠ t in 𝓝 (0:ℝ), SKGap.opNorm (M+t • E) < R :=
    hcont'.continuousAt.eventually (gt_mem_nhds (by simpa using hMR))
  filter_upwards [hl',hu',hm'] with t ht ht' hm
  exact realTruncatedK_eq_inverse f hlo hf hR D C (M+t • E) hD hC
    (by simp [Matrix.transpose_smul,hM,hE]) hm.le ht.le ht'.le

lemma realTruncatedK_derivative (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M E : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (hM : Mᵀ = M) (hE : Eᵀ = E)
    (hMR : SKGap.opNorm M < R)
    (hl : lo < SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M-C)*D)))
    (hu : -hi < SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M-C)*D))) :
    HasDerivAt (fun t : ℝ => realTruncatedK f R hR D C (M+t • E))
      (realTruncatedK f R hR D C M*(D*D)*E*realTruncatedK f R hR D C M) 0 := by
  have hid := realTruncatedK_eq_inverse f hlo hf hR D C M hD hC hM hMR.le hl.le hu.le
  have he := realTruncatedK_eventually_inverse f hlo hf hR D C M E hD hC hM hE hMR hl hu
  have hunit : IsUnit (1-D*D*(M-C)) := by
    have hSH : (liftMatrix (1-D*(M-C)*D)).IsHermitian :=
      liftMatrix_hermitian _ (by simp [Matrix.transpose_mul,hD,hC,hM,mul_assoc])
    have hp : (liftMatrix (1-D*(M-C)*D)).PosDef := hSH.posDef_iff_eigenvalues_pos.mpr (fun i =>
      hlo.trans (hl.trans_le (SKGap.ComplexSpectral.eigenvalue_lower_bound hSH i)))
    have hS : IsUnit (1-D*(M-C)*D) := (liftMatrix_isUnit_iff _).mp hp.isUnit
    exact SKGap.ResolventIdentity.inverse_one_sub_square_mul_unit D (M-C) hS
  have hm : HasDerivAt (fun t : ℝ => M+t • E-C) E 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const E |>.const_add M).sub_const C using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_smul]
  have hq := (hm.const_mul (D*D)).const_sub 1
  have hi := real_matrix_hasDerivAt_inverse hq (by simpa using hunit)
  rw [hid]
  have hi' : HasDerivAt (fun t : ℝ => (1-D*D*(M+t • E-C))⁻¹)
      ((1-D*D*(M-C))⁻¹*(D*D)*E*(1-D*D*(M-C))⁻¹) 0 := by
    simpa only [zero_smul,add_zero,mul_neg,neg_mul,neg_neg,mul_assoc] using! hi
  exact hi'.congr_of_eventuallyEq he

end SKGap.RealComplex

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LipschitzNormedConvolution
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
namespace SKGap

section Smoothing
open NormedSpace
open scoped Convolution ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem lipschitz_normed_convolution {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (φ : ContDiffBump (0 : E))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    LipschitzWith L (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) := by
  have hcv : ConvolutionExists (φ.normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ :=
    (φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed
      (hf.continuous.locallyIntegrable (μ := μ))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hx : Integrable (fun t => φ.normed μ t * f (x - t)) μ := hcv x
  have hy : Integrable (fun t => φ.normed μ t * f (y - t)) μ := hcv y
  rw [← integral_sub hx hy]
  calc
    _ ≤ ∫ t, φ.normed μ t * ((L : ℝ) * ‖x - y‖) ∂μ := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      filter_upwards [] with t
      rw [← mul_sub, norm_mul, Real.norm_eq_abs (φ.normed μ t),
        abs_of_nonneg (φ.nonneg_normed _)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed _)
      simpa only [sub_sub_sub_cancel_right] using hf.norm_sub_le (x - t) (y - t)
    _ = (L : ℝ) * ‖x - y‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

theorem exists_smooth_lipschitz_approx {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith L g ∧
      ∀ x, dist (g x) (f x) ≤ (L : ℝ) * ε := by
  let μ : Measure E := addHaar
  let φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  let g := φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f
  refine ⟨g, ?_, lipschitz_normed_convolution hf φ μ, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed hf.continuous.locallyIntegrable
  · intro x
    apply ContDiffBump.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
    intro y hy
    apply (hf.dist_le_mul y x).trans
    exact mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le L.coe_nonneg

end Smoothing

section GaussianMoments
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {μ : Measure E} [IsGaussian μ]

theorem gaussian_integrable_exp_norm (a : ℝ) :
    Integrable (fun x : E => exp (a * ‖x‖)) μ := by
  obtain ⟨C, hC, hI⟩ := IsGaussian.exists_integrable_exp_sq μ
  apply (hI.const_mul (exp (a ^ 2 / (4 * C)))).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  apply exp_le_exp.mpr
  have hs := sq_nonneg (‖x‖ - a / (2 * C))
  have hC0 : C ≠ 0 := ne_of_gt hC
  have heq : C * (‖x‖ - a / (2 * C)) ^ 2 =
      C * ‖x‖ ^ 2 - a * ‖x‖ + a ^ 2 / (4 * C) := by field_simp; ring
  nlinarith [mul_nonneg (le_of_lt hC) hs]

end GaussianMoments

section StandardGaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_map_dual (L : StrongDual ℝ E) :
    (stdGaussian E).map L = gaussianReal 0 (Real.toNNReal (‖L‖ ^ 2)) := by
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]

theorem stdGaussian_integral_exp_dual (L : StrongDual ℝ E) (r : ℝ) :
    (∫ x, exp (r * L x) ∂stdGaussian E) = exp (r ^ 2 * ‖L‖ ^ 2 / 2) := by
  have hm := mgf_gaussianReal
    (stdGaussian_map_dual L) r
  simpa [mgf, Real.toNNReal_of_nonneg (sq_nonneg _), mul_div_assoc, mul_comm] using hm

theorem gaussian_integrable_exp_lipschitz {μ : Measure E} [IsGaussian μ]
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (r : ℝ) :
    Integrable (fun x => exp (r * f x)) μ := by
  have hfc := hf.continuous
  have hI := (gaussian_integrable_exp_norm (μ := μ) (|r| * L)).const_mul
    (exp (|r| * |f 0|))
  apply hI.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  apply exp_le_exp.mpr
  have hx : |f x| ≤ |f 0| + L * ‖x‖ := by
    have hh := hf.norm_sub_le x 0
    simp only [sub_zero, Real.norm_eq_abs] at hh
    have ht := abs_add_le (f x - f 0) (f 0)
    rw [sub_add_cancel] at ht
    linarith
  calc
    r * f x ≤ |r * f x| := le_abs_self _
    _ = |r| * |f x| := abs_mul _ _
    _ ≤ |r| * (|f 0| + L * ‖x‖) := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = _ := by ring

theorem gaussian_integrable_lipschitz {μ : Measure E} [IsGaussian μ]
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) : Integrable f μ := by
  have hI := ((IsGaussian.integrable_id (μ := μ)).norm.const_mul (L : ℝ)).add
    (integrable_const |f 0|)
  apply hI.mono' hf.continuous.aestronglyMeasurable
  filter_upwards [] with x
  change |f x| ≤ (L : ℝ) * ‖x‖ + |f 0|
  have hh := hf.norm_sub_le x 0
  simp only [sub_zero, Real.norm_eq_abs] at hh ⊢
  have ht := abs_add_le (f x - f 0) (f 0)
  rw [sub_add_cancel] at ht
  linarith

end StandardGaussian

theorem exp_interval_average_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ}
    (hg : Continuous g) :
    exp (a⁻¹ * ∫ t in (0 : ℝ)..a, g t) ≤
      a⁻¹ * ∫ t in (0 : ℝ)..a, exp (g t) := by
  have h0 : volume (Icc (0 : ℝ) a) ≠ 0 := by
    rw [volume_Icc, sub_zero, ENNReal.ofReal_ne_zero_iff]
    exact ha
  have ht : volume (Icc (0 : ℝ) a) ≠ ∞ := by simp
  have hJ := convexOn_exp.map_set_average_le continuous_exp.continuousOn isClosed_univ
    h0 ht (by filter_upwards [] with x; exact mem_univ _)
    hg.integrableOn_Icc (continuous_exp.comp hg).integrableOn_Icc
  have hvol : volume.real (Icc (0 : ℝ) a) = a := by
    simp [measureReal_def, volume_Icc, ha.le]
  simpa only [setAverage_eq, hvol, smul_eq_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.le] using hJ

section Rotation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rotation_snd_norm_le (θ : ℝ) (p : E × E) :
    ‖(ContinuousLinearMap.rotation θ p).2‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  rw [ContinuousLinearMap.rotation_apply]
  calc
    ‖-sin θ • p.1 + cos θ • p.2‖ ≤ ‖-sin θ • p.1‖ + ‖cos θ • p.2‖ := norm_add_le _ _
    _ = |sin θ| * ‖p.1‖ + |cos θ| * ‖p.2‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * ‖p.1‖ + 1 * ‖p.2‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (abs_sin_le_one _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (abs_cos_le_one _) (norm_nonneg _))
    _ = _ := by ring

theorem hasDerivAt_rotation_fst (θ : ℝ) (p : E × E) :
    HasDerivAt (fun t => (ContinuousLinearMap.rotation t p).1)
      (ContinuousLinearMap.rotation θ p).2 θ := by
  exact ((hasDerivAt_cos θ).smul_const p.1).add
    ((hasDerivAt_sin θ).smul_const p.2)

theorem rotation_fundamental_theorem {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : Continuous df) (p : E × E) :
    (∫ θ in (0 : ℝ)..π / 2,
      df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) =
        f p.2 - f p.1 := by
  have hd : ∀ θ, HasDerivAt (fun t => f (ContinuousLinearMap.rotation t p).1)
      (df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) θ :=
    fun θ => (hf _).comp_hasDerivAt θ (hasDerivAt_rotation_fst θ p)
  have hc : Continuous (fun θ =>
      df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) := by
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    (hc.intervalIntegrable 0 (π / 2))
  simpa [ContinuousLinearMap.rotation_apply] using hi

theorem rotation_exp_difference_le {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : Continuous df) (r : ℝ) (p : E × E) :
    exp (r * (f p.2 - f p.1)) ≤ (π / 2)⁻¹ *
      ∫ θ in (0 : ℝ)..π / 2, exp (r * (π / 2) *
        df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) := by
  have hc : Continuous (fun θ => r * (π / 2) *
      df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) := by
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  have hJ := exp_interval_average_le (half_pos pi_pos) hc
  rw [intervalIntegral.integral_const_mul, rotation_fundamental_theorem hf hdf] at hJ
  convert hJ using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  field_simp

theorem exp_dual_le {L : ℝ≥0} (D : StrongDual ℝ E) (hD : ‖D‖ ≤ L) (r : ℝ) (y : E) :
    exp (r * D y) ≤ exp (|r| * L * ‖y‖) := by
  apply exp_le_exp.mpr
  calc
    r * D y ≤ |r * D y| := le_abs_self _
    _ = |r| * ‖D y‖ := by rw [abs_mul, Real.norm_eq_abs]
    _ ≤ |r| * (‖D‖ * ‖y‖) := mul_le_mul_of_nonneg_left (D.le_opNorm y) (abs_nonneg _)
    _ ≤ |r| * ((L : ℝ) * ‖y‖) := by gcongr
    _ = _ := by ring

theorem rotation_exp_dual_le {L : ℝ≥0} {df : E → StrongDual ℝ E}
    (hdf : ∀ x, ‖df x‖ ≤ L) (r θ : ℝ) (p : E × E) :
    exp (r * df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) ≤
      exp (|r| * L * ‖p.1‖) * exp (|r| * L * ‖p.2‖) := by
  calc
    _ ≤ exp (|r| * L * ‖(ContinuousLinearMap.rotation θ p).2‖) := exp_dual_le _ (hdf _) _ _
    _ ≤ exp (|r| * L * (‖p.1‖ + ‖p.2‖)) := by
      gcongr
      exact rotation_snd_norm_le θ p
    _ = _ := by rw [mul_add, exp_add]

end Rotation

section StandardGaussianRotation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_integrable_variable_dual {df : E → StrongDual ℝ E} (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    Integrable (fun p : E × E => exp (r * df p.1 p.2))
      ((stdGaussian E).prod (stdGaussian E)) := by
  apply ((gaussian_integrable_exp_norm (μ := stdGaussian E) (|r| * L)).comp_snd
    (stdGaussian E)).mono' (by fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_dual_le _ (hdf _) _ _

theorem stdGaussian_integral_variable_dual_le {df : E → StrongDual ℝ E} (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    (∫ p : E × E, exp (r * df p.1 p.2) ∂(stdGaussian E).prod (stdGaussian E)) ≤
      exp (r ^ 2 * (L : ℝ) ^ 2 / 2) := by
  have hi := stdGaussian_integrable_variable_dual hc hdf r
  have hio := hi.integral_prod_left
  simp only [stdGaussian_integral_exp_dual] at hio
  rw [integral_prod _ hi]
  simp only [stdGaussian_integral_exp_dual]
  calc
    _ ≤ ∫ _x : E, exp (r ^ 2 * (L : ℝ) ^ 2 / 2) ∂stdGaussian E := by
      apply integral_mono hio (integrable_const _)
      intro x
      apply exp_le_exp.mpr
      gcongr
      exact hdf x
    _ = _ := by simp

theorem stdGaussian_integral_rotation_variable_dual_le {df : E → StrongDual ℝ E}
    (hc : Continuous df) {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r θ : ℝ) :
    (∫ p : E × E, exp (r * df (ContinuousLinearMap.rotation θ p).1
        (ContinuousLinearMap.rotation θ p).2) ∂(stdGaussian E).prod (stdGaussian E)) ≤
      exp (r ^ 2 * (L : ℝ) ^ 2 / 2) := by
  have hm := IsGaussian.map_rotation_eq_self (μ := stdGaussian E) (by simp) θ
  rw [← integral_map (ContinuousLinearMap.rotation θ).continuous.aemeasurable
    (f := fun p : E × E => exp (r * df p.1 p.2)) (by fun_prop), hm]
  exact stdGaussian_integral_variable_dual_le hc hdf r

theorem stdGaussian_integrable_rotation_variable_dual {df : E → StrongDual ℝ E}
    (hc : Continuous df) {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ)
    (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (fun z : ℝ × (E × E) =>
      exp (r * df (ContinuousLinearMap.rotation z.1 z.2).1
        (ContinuousLinearMap.rotation z.1 z.2).2))
      (ν.prod ((stdGaussian E).prod (stdGaussian E))) := by
  have hI := gaussian_integrable_exp_norm (μ := stdGaussian E) (|r| * L)
  apply ((hI.mul_prod hI).comp_snd ν).mono'
  · simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact rotation_exp_dual_le hdf _ _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem lipschitz_of_bounded_derivative {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) :
    LipschitzWith L f := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hf x).differentiableAt)
  intro x
  rw [(hf x).fderiv]
  exact hdf x

lemma exp_mul_sub (r a b : ℝ) : exp (r * (a - b)) = exp (-r * b) * exp (r * a) := by
  rw [← exp_add]
  congr 1
  ring

theorem stdGaussian_integrable_exp_difference {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (r : ℝ) :
    Integrable (fun p : E × E => exp (r * (f p.2 - f p.1)))
      ((stdGaussian E).prod (stdGaussian E)) := by
  simp_rw [exp_mul_sub]
  exact (gaussian_integrable_exp_lipschitz hf (-r)).mul_prod
    (gaussian_integrable_exp_lipschitz hf r)

theorem stdGaussian_mgf_difference_le {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    (∫ p : E × E, exp (r * (f p.2 - f p.1)) ∂(stdGaussian E).prod (stdGaussian E)) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (π / 2))
  have hν : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  let R := r * (π / 2)
  let G : ℝ → E × E → ℝ := fun θ p => exp (R *
    df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2)
  have hI : Integrable (Function.uncurry G) (ν.prod ((stdGaussian E).prod (stdGaussian E))) :=
    stdGaussian_integrable_rotation_variable_dual hc hdf R ν
  have hD := stdGaussian_integrable_exp_difference (lipschitz_of_bounded_derivative hf hdf) r
  have hpos : 0 < π / 2 := half_pos pi_pos
  have hvol : ν.real univ = π / 2 := by
    simp [ν, measureReal_def, Real.volume_Ioc, hpos.le]
  have hpoint (p : E × E) : exp (r * (f p.2 - f p.1)) ≤
      (π / 2)⁻¹ * ∫ θ, G θ p ∂ν := by
    simpa only [intervalIntegral.integral_of_le hpos.le] using rotation_exp_difference_le hf hc r p
  calc
    _ ≤ ∫ p : E × E, (π / 2)⁻¹ * (∫ θ, G θ p ∂ν)
        ∂(stdGaussian E).prod (stdGaussian E) :=
      integral_mono hD (hI.integral_prod_right.const_mul _) hpoint
    _ = (π / 2)⁻¹ * ∫ θ, (∫ p : E × E, G θ p
        ∂(stdGaussian E).prod (stdGaussian E)) ∂ν := by
      rw [integral_const_mul, ← integral_integral_swap hI]
    _ ≤ (π / 2)⁻¹ * ∫ _θ, exp (R ^ 2 * (L : ℝ) ^ 2 / 2) ∂ν := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpos.le)
      apply integral_mono hI.integral_prod_left (integrable_const _)
      intro θ
      exact stdGaussian_integral_rotation_variable_dual_le hc hdf R θ
    _ = exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
      rw [integral_const, smul_eq_mul, hvol, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      congr 1
      dsimp [R]
      ring

theorem stdGaussian_mgf_centered_le {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  have hLip := lipschitz_of_bounded_derivative hf hdf
  have hF := gaussian_integrable_lipschitz (μ := stdGaussian E) hLip
  have hG := gaussian_integrable_exp_lipschitz (μ := stdGaussian E) hLip (-r)
  have hpair := stdGaussian_integrable_exp_difference hLip (-r)
  have hcenter : Integrable (fun x => exp (r * (f x - ∫ y, f y ∂stdGaussian E)))
      (stdGaussian E) := by
    simp_rw [exp_mul_sub]
    exact (gaussian_integrable_exp_lipschitz hLip r).const_mul _
  have hj (x : E) : exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ≤
      ∫ y, exp (r * (f x - f y)) ∂stdGaussian E := by
    have hsub := ((integrable_const (f x)).sub hF).const_mul r
    have he : Integrable (fun y => exp (r * (f x - f y))) (stdGaussian E) := by
      simp_rw [exp_mul_sub]
      exact hG.mul_const _
    have h := convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
      (by filter_upwards [] with y; exact mem_univ _) hsub he
    simp only [Pi.sub_apply] at h
    simpa only [integral_const_mul, integral_sub (integrable_const _) hF,
      integral_const, probReal_univ, one_smul] using h
  have heq (x y : E) : r * (f x - f y) = -r * (f y - f x) := by ring
  simp_rw [heq] at hj
  calc
    _ ≤ ∫ x, (∫ y, exp (-r * (f y - f x)) ∂stdGaussian E) ∂stdGaussian E :=
      integral_mono hcenter hpair.integral_prod_left hj
    _ = ∫ p : E × E, exp (-r * (f p.2 - f p.1))
        ∂(stdGaussian E).prod (stdGaussian E) := (integral_prod _ hpair).symm
    _ ≤ exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
      simpa using stdGaussian_mgf_difference_le hf hc hdf (-r)

theorem centered_mgf_le_of_uniform_dist {f g : E → ℝ} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g) {δ : ℝ}
    (hfg : ∀ x, dist (f x) (g x) ≤ δ) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (2 * |r| * δ) *
        (∫ x, exp (r * (g x - ∫ y, g y ∂stdGaussian E)) ∂stdGaussian E) := by
  let μ := stdGaussian E
  have hfi : Integrable f μ := gaussian_integrable_lipschitz hf
  have hgi : Integrable g μ := gaussian_integrable_lipschitz hg
  have hmean : |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| ≤ δ := by
    have hi : ‖∫ x, f x - g x ∂μ‖ ≤ δ * μ.real univ :=
      norm_integral_le_of_norm_le_const (μ := μ)
        (Eventually.of_forall (fun x => by simpa only [dist_eq_norm] using hfg x))
    rw [integral_sub hfi hgi] at hi
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hi
  have he (h : E → ℝ) {K : ℝ≥0} (hh : LipschitzWith K h) :
      Integrable (fun x => exp (r * (h x - ∫ y, h y ∂μ))) μ := by
    simp_rw [exp_mul_sub]
    exact (gaussian_integrable_exp_lipschitz hh r).const_mul _
  rw [← integral_const_mul]
  apply integral_mono (he f hf) ((he g hg).const_mul _)
  intro x
  dsimp only
  rw [← exp_add]
  apply exp_le_exp.mpr
  have hdiff : |(f x - ∫ y, f y ∂μ) - (g x - ∫ y, g y ∂μ)| ≤ 2 * δ := by
    have hx : |f x - g x| ≤ δ := by simpa only [Real.dist_eq] using hfg x
    calc
      _ = |(f x - g x) - ((∫ y, f y ∂μ) - ∫ y, g y ∂μ)| := by congr 1; ring
      _ ≤ |f x - g x| + |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le
          (f x - g x) ((∫ y, f y ∂μ) - ∫ y, g y ∂μ)
      _ ≤ 2 * δ := by linarith
  have hh := le_abs_self (r * ((f x - ∫ y, f y ∂μ) - (g x - ∫ y, g y ∂μ)))
  rw [abs_mul] at hh
  have hb := mul_le_mul_of_nonneg_left hdiff (abs_nonneg r)
  dsimp [μ] at *
  nlinarith

end StandardGaussianRotation
end SKGap
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_StdGaussianMgfLipschitz
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
namespace SKGap
section StandardGaussianRotation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_mgf_lipschitz_le {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  have hε (ε : ℝ) (hε : 0 < ε) :
      (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
        exp (2 * |r| * ((L : ℝ) * ε)) * exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
    obtain ⟨g, hgs, hgl, hgf⟩ := exists_smooth_lipschitz_approx hf hε
    have hmg := stdGaussian_mgf_centered_le
      (fun x => (hgs.differentiable (by simp) x).hasFDerivAt)
      (hgs.continuous_fderiv (by simp)) (fun _ => norm_fderiv_le_of_lipschitz ℝ hgl) r
    exact (centered_mgf_le_of_uniform_dist hf hgl
      (fun x => by simpa only [dist_comm] using hgf x) r).trans
        (mul_le_mul_of_nonneg_left hmg (exp_pos _).le)
  have ht : Tendsto (fun ε : ℝ => exp (2 * |r| * ((L : ℝ) * ε)) *
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8)) (𝓝[>] 0)
      (𝓝 (exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8))) := by
    have hc : Continuous (fun ε : ℝ => exp (2 * |r| * ((L : ℝ) * ε)) *
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8)) := by fun_prop
    simpa using ((hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε heps
  exact hε ε heps

end StandardGaussianRotation
end SKGap

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PowExponentialPair
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped Topology
section SubgaussianMoments
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

lemma pow_le_exponential_pair (x : ℝ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    |x|^k ≤ ((k.factorial : ℝ)/r^k) * (exp (r*x)+exp (-r*x)) := by
  have hk : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hh := Real.pow_div_factorial_le_exp (r*|x|) (mul_nonneg hr.le (abs_nonneg x)) k
  have he : exp (r*|x|) ≤ exp (r*x)+exp (-r*x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; exact le_add_of_nonneg_right (exp_nonneg _)
    · rw [abs_of_nonpos hx]; have hid : r * -x = -r*x := by ring
      rw [hid]; exact le_add_of_nonneg_left (exp_nonneg _)
  have hg := hh.trans he
  rw [div_le_iff₀ hk,mul_pow] at hg
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hr k)).mpr
  convert hg using 1 <;> ring

lemma subgaussian_abs_moment {r : ℝ} (hr : 0 < r) (hX : HasSubgaussianMGF X c μ) (k : ℕ) :
    (∫ x, |X x|^k ∂μ) ≤
      2*((k.factorial : ℝ)/r^k)*exp ((c : ℝ)*r^2/2) := by
  let C := (k.factorial : ℝ)/r^k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : Integrable (fun x => C*(exp (r*X x)+exp (-r*X x))) μ :=
    ((hX.integrable_exp_mul r).add (hX.integrable_exp_mul (-r))).const_mul C
  have hp (x : Ω) : |X x|^k ≤ C*(exp (r*X x)+exp (-r*X x)) := pow_le_exponential_pair (X x) hr k
  have hi : Integrable (fun x => |X x|^k) μ := by
    apply he.mono' (hX.integrable.aestronglyMeasurable.norm.pow k)
    filter_upwards [] with x
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,abs_abs] using hp x
  calc
    _ ≤ ∫ x, C*(exp (r*X x)+exp (-r*X x)) ∂μ := integral_mono hi he hp
    _ = C*(mgf X μ r+mgf X μ (-r)) := by
      rw [integral_const_mul,integral_add (hX.integrable_exp_mul r) (hX.integrable_exp_mul (-r))]
      rfl
    _ ≤ C*(exp ((c:ℝ)*r^2/2)+exp ((c:ℝ)*r^2/2)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [neg_sq] using add_le_add (hX.mgf_le r) (hX.mgf_le (-r))
    _ = _ := by dsimp only [C]; ring
end SubgaussianMoments

section GaussianMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_subgaussian_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x-∫ y, f y ∂stdGaussian E)
      ⟨π^2*(L:ℝ)^2/4,by positivity⟩ (stdGaussian E) where
  integrable_exp_mul r := by
    apply gaussian_integrable_exp_lipschitz (L := L) _ r
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  mgf_le r := by
    have hh := stdGaussian_mgf_lipschitz_le hf r
    change (∫ x, exp (r*(f x-∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤ _
    apply hh.trans_eq
    change exp (π^2*r^2*(L:ℝ)^2/8) = exp ((π^2*(L:ℝ)^2/4)*r^2/2)
    congr 1
    ring

lemma stdGaussian_abs_centered_moment {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hL : 0 < L) (k : ℕ) :
    (∫ x, |f x-∫ y, f y ∂stdGaussian E|^k ∂stdGaussian E) ≤
      (2*(k.factorial : ℝ)*exp (π^2/8))*(L:ℝ)^k := by
  have hLr : 0 < (L:ℝ) := hL
  have hh := subgaussian_abs_moment (inv_pos.mpr hLr) (stdGaussian_subgaussian_lipschitz hf) k
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  have he : π^2*(L:ℝ)^2/4*((L:ℝ)⁻¹)^2/2 = π^2/8 := by field_simp [ne_of_gt hLr]; ring
  change 2*(k.factorial : ℝ)*exp (π^2/8)*(L:ℝ)^k =
    2*((k.factorial:ℝ)/(L:ℝ)⁻¹^k)*exp ((π^2*(L:ℝ)^2/4)*(L:ℝ)⁻¹^2/2)
  rw [he,inv_pow,div_inv_eq_mul]
  ring
end GaussianMoments
end SKGap

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianProductIntegral
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped Topology
section ProductMoments
variable {κ : Type*} [Fintype κ]

lemma gaussianProduct_integral (F : EuclideanSpace ℝ κ → ℝ) (hF : Continuous F) :
    (∫ g : κ → ℝ, F (WithLp.toLp 2 g) ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ x, F x ∂stdGaussian (EuclideanSpace ℝ κ) := by
  rw [← map_pi_eq_stdGaussian]
  exact (integral_map (by fun_prop) hF.aestronglyMeasurable).symm

lemma gaussianProduct_integrable_lipschitz {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) :
    Integrable (fun g : κ → ℝ => F (WithLp.toLp 2 g))
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hi := gaussian_integrable_lipschitz (μ := stdGaussian (EuclideanSpace ℝ κ)) hF
  rw [← map_pi_eq_stdGaussian] at hi
  exact hi.comp_measurable (by fun_prop)

lemma gaussianProduct_abs_centered_moment {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) (hL : 0 < L) (k : ℕ) :
    (∫ g : κ → ℝ, |F (WithLp.toLp 2 g)-
      ∫ h : κ → ℝ, F (WithLp.toLp 2 h) ∂Measure.pi (fun _ => gaussianReal 0 1)|^k
        ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      (2*(k.factorial : ℝ)*exp (π^2/8))*(L:ℝ)^k := by
  rw [gaussianProduct_integral F hF.continuous]
  rw [gaussianProduct_integral (fun x => |F x-∫ y, F y ∂stdGaussian _|^k) ((hF.continuous.sub continuous_const).abs.pow k)]
  exact stdGaussian_abs_centered_moment hF hL k

lemma gaussianProduct_centered_L1 {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) (hL : 0 < L) :
    (∫ g : κ → ℝ, |F (WithLp.toLp 2 g)-
      ∫ h : κ → ℝ, F (WithLp.toLp 2 h) ∂Measure.pi (fun _ => gaussianReal 0 1)|
        ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      (2*exp (π^2/8))*(L:ℝ) := by
  simpa using gaussianProduct_abs_centered_moment hF hL 1

end ProductMoments
end SKGap

open MeasureTheory
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_IntegralProductDeviation
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
namespace SKGap
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integral_product_deviation {X Y : Ω → ℝ} {C T : ℝ}
    (hX : Integrable X μ) (hY : AEStronglyMeasurable Y μ)
    (hC : ∀ᵐ x ∂μ, ‖Y x‖ ≤ C)
    (hT : (∫ x, |X x-∫ y, X y ∂μ| ∂μ) ≤ T) :
    |(∫ x, X x*Y x ∂μ)-(∫ x, X x ∂μ)*(∫ x, Y x ∂μ)| ≤ C*T := by
  have hC0 : 0 ≤ C := by
    obtain ⟨x,hx⟩ := hC.exists
    exact (norm_nonneg _).trans hx
  have hYi : Integrable Y μ := (integrable_const C).mono' hY hC
  have hXY : Integrable (fun x => X x*Y x) μ := by
    simpa only [mul_comm] using hX.bdd_mul hY hC
  have hcenter : Integrable (fun x => X x-∫ y, X y ∂μ) μ := hX.sub (integrable_const _)
  have hci : Integrable (fun x => (X x-∫ y, X y ∂μ)*Y x) μ := by
    simpa only [mul_comm] using hcenter.bdd_mul hY hC
  have he : (∫ x, X x*Y x ∂μ)-(∫ x, X x ∂μ)*(∫ x, Y x ∂μ) =
      ∫ x, (X x-∫ y, X y ∂μ)*Y x ∂μ := by
    simp_rw [sub_mul]
    rw [integral_sub hXY (hYi.const_mul _),integral_const_mul]
  rw [he]
  calc
    _ ≤ ∫ x, ‖(X x-∫ y, X y ∂μ)*Y x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C*|X x-∫ y, X y ∂μ| ∂μ := by
      apply integral_mono_ae hci.norm (hcenter.norm.const_mul C)
      filter_upwards [hC] with x hx
      simpa only [norm_mul,Real.norm_eq_abs,mul_comm] using
        mul_le_mul_of_nonneg_left hx (norm_nonneg (X x-∫ y, X y ∂μ))
    _ = C*(∫ x, |X x-∫ y, X y ∂μ| ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hT hC0

lemma integral_loop_deviation {X Y Z V : Ω → ℝ} {r C T B E : ℝ}
    (hr : 0 ≤ r) (hX : Integrable X μ) (hY : AEStronglyMeasurable Y μ)
    (hC : ∀ᵐ x ∂μ, ‖Y x‖ ≤ C)
    (hZ : Integrable Z μ) (hB : ∀ᵐ x ∂μ, ‖Z x‖ ≤ B)
    (hT : (∫ x, |X x-∫ y, X y ∂μ| ∂μ) ≤ T)
    (hE : |(∫ x, V x ∂μ)-r*(∫ x, X x*Y x+Z x ∂μ)| ≤ E) :
    |(∫ x, V x ∂μ)-r*(∫ x, X x ∂μ)*(∫ x, Y x ∂μ)| ≤ E+r*(C*T+B) := by
  have hXY : Integrable (fun x => X x*Y x) μ := by
    simpa only [mul_comm] using hX.bdd_mul hY hC
  have hbound := integral_product_deviation hX hY hC hT
  have hb : |∫ x, Z x ∂μ| ≤ B := by
    exact (norm_integral_le_integral_norm _).trans ((integral_mono_ae hZ.norm (integrable_const B) hB).trans_eq (by simp))
  have he : (∫ x, V x ∂μ)-r*(∫ x, X x ∂μ)*(∫ x, Y x ∂μ) =
      ((∫ x, V x ∂μ)-r*(∫ x, X x*Y x+Z x ∂μ))+
      r*((∫ x, X x*Y x ∂μ)-(∫ x, X x ∂μ)*(∫ x, Y x ∂μ)+(∫ x, Z x ∂μ)) := by
    rw [integral_add hXY hZ]; ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hE (by
    rw [abs_mul,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hbound hb)) hr))

end SKGap

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixEntryCLM
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixEntry_lipschitz (i k : ι) : LipschitzWith 1 (fun M : Matrix ι ι ℝ => M i k) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul,Matrix.sub_apply] using!
    matrix_entry_le_frobenius (M-N) i k

omit [DecidableEq ι] in
lemma matrixEntry_derivative {f : ℝ → Matrix ι ι ℝ} {v : Matrix ι ι ℝ} {t : ℝ}
    (hf : HasDerivAt f v t) (i k : ι) : HasDerivAt (fun s => f s i k) (v i k) t := by
  classical
  exact (matrixEntryCLM i k).hasFDerivAt.comp_hasDerivAt t hf

lemma matrix_inverse_diff_bound (K B E : Matrix ι ι ℝ) :
    ‖K*B*E*K‖ ≤ opNorm K*(opNorm B*‖E‖)*opNorm K := by
  calc
    _ ≤ ‖K*B*E‖*opNorm K := frobenius_mul_le_opNorm_right _ _
    _ = ‖K*(B*E)‖*opNorm K := by rw [mul_assoc K B E]
    _ ≤ (opNorm K*‖B*E‖)*opNorm K :=
      mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (frobenius_mul_le_opNorm _ _) (norm_nonneg _)) (norm_nonneg _)

lemma diagonalVector_norm_le (M : Matrix ι ι ℝ) : ‖diagonalVector M‖ ≤ ‖M‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg M)
  simp only [← sq]
  rw [EuclideanSpace.norm_sq_eq,frobenius_sq]
  apply Finset.sum_le_sum
  intro i _
  simpa only [diagonalVector,Real.norm_eq_abs,sq_abs] using
    (Finset.single_le_sum (fun j _ => sq_nonneg (M i j)) (Finset.mem_univ i))

lemma abs_trace_le_frobenius (M : Matrix ι ι ℝ) :
    |Matrix.trace M| ≤ sqrt (Fintype.card ι)*‖M‖ := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => 1)
  have hv : ‖v‖ = sqrt (Fintype.card ι) := by
    rw [EuclideanSpace.norm_eq]; simp [v]
  have hi := abs_real_inner_le_norm (diagonalVector M) v
  change |∑ i, 1*M i i| ≤ ‖diagonalVector M‖*‖v‖ at hi
  simp only [one_mul,hv] at hi
  change |Matrix.trace M| ≤ ‖diagonalVector M‖*sqrt (Fintype.card ι) at hi
  exact hi.trans ((mul_le_mul_of_nonneg_right (diagonalVector_norm_le M) (sqrt_nonneg _)).trans_eq (mul_comm _ _))

lemma matrixTrace_mul_lipschitz {Ω : Type*} [PseudoMetricSpace Ω]
    {K : Ω → Matrix ι ι ℝ} {L : ℝ≥0} (hK : LipschitzWith L K)
    (B : Matrix ι ι ℝ) :
    LipschitzWith (⟨sqrt (Fintype.card ι)*opNorm B,by exact mul_nonneg (sqrt_nonneg _) (norm_nonneg _)⟩*L)
      (fun x => Matrix.trace (K x*B)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |Matrix.trace (K x*B)-Matrix.trace (K y*B)| ≤
    (sqrt (Fintype.card ι)*opNorm B*(L:ℝ))*dist x y
  rw [← Matrix.trace_sub,← sub_mul]
  calc
    _ ≤ sqrt (Fintype.card ι)*‖(K x-K y)*B‖ := abs_trace_le_frobenius _
    _ ≤ sqrt (Fintype.card ι)*(‖K x-K y‖*opNorm B) :=
      mul_le_mul_of_nonneg_left (frobenius_mul_le_opNorm_right _ _) (sqrt_nonneg _)
    _ ≤ sqrt (Fintype.card ι)*(((L:ℝ)*dist x y)*opNorm B) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by simpa only [dist_eq_norm] using hK.dist_le_mul x y)
          (norm_nonneg _)) (sqrt_nonneg _)
    _ = _ := by ring

end SKGap

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GoeInverseLoopCentered
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem goe_inverse_loop_centered {r : ℝ} (hr : 0 ≤ r) (B : Matrix ι ι ℝ) (i : ι)
    {K : Matrix ι ι ℝ → Matrix ι ι ℝ} {L T : ℝ≥0} {C : ℝ}
    {s : Set (MatrixCoordinates ι → ℝ)}
    (hK : LipschitzWith L K) (hC : ∀ M, opNorm (K M) ≤ C)
    (hT : LipschitzWith T (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) =>
      Matrix.trace (K (goeMatrix r g)*B))) (hT0 : 0 < T)
    (hs : MeasurableSet s)
    (hder : ∀ g ∈ s, ∀ b, HasDerivAt
      (fun t : ℝ => K (goeMatrix r g+t • symmetricElementary i b) b i)
      ((K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i) 0) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
    let Lπ : ℝ≥0 := L*(⟨sqrt (2*r),sqrt_nonneg _⟩ *
      (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
    |(∫ g, (goeMatrix r g*K (goeMatrix r g)) i i ∂μ)-
      r*(∫ g, Matrix.trace (K (goeMatrix r g)*B) ∂μ)*(∫ g, K (goeMatrix r g) i i ∂μ)| ≤
      (Fintype.card ι:ℝ)*(sqrt (2*r)*(Lπ:ℝ)+r*(2*C*opNorm B*C))*μ.real sᶜ+
        r*(C*((2*exp (π^2/8))*(T:ℝ))+C*opNorm B*C) := by
  intro μ Lπ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hcomp : LipschitzWith Lπ (fun g => K (goeMatrix r g)) :=
    hK.comp (goeMatrix_pi_lipschitz r)
  have hf (a b : ι) : LipschitzWith Lπ (fun g => K (goeMatrix r g) a b) := by
    simpa only [one_mul] using! (matrixEntry_lipschitz a b).comp hcomp
  have hc (g : MatrixCoordinates ι → ℝ) (a b : ι) :
      ‖K (goeMatrix r g) a b‖ ≤ C := by
    simpa only [Real.norm_eq_abs] using (matrix_entry_le_opNorm _ a b).trans (hC _)
  have hd (g : MatrixCoordinates ι → ℝ) (b : ι) :
      ‖(K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i‖ ≤
        2*C*opNorm B*C := by
    have he : ‖(K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i‖ ≤
        ‖K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)‖ := by
      simpa only [Real.norm_eq_abs] using!
        matrix_entry_le_frobenius (K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i
    apply he.trans
    apply (matrix_inverse_diff_bound _ _ _).trans
    calc
      _ ≤ C*(opNorm B*2)*C := by
        exact mul_le_mul
          (mul_le_mul (hC _) (mul_le_mul_of_nonneg_left (symmetricElementary_norm_le i b) (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hC0)
          (hC _) (norm_nonneg _) (mul_nonneg hC0 (mul_nonneg (norm_nonneg _) (by norm_num)))
      _ = _ := by ring
  have hz (g : MatrixCoordinates ι → ℝ) :
      ‖∑ b, (K (goeMatrix r g)*B) b i*K (goeMatrix r g) b i‖ ≤ C*opNorm B*C := by
    rw [Real.norm_eq_abs]
    apply (goe_cross_contraction_bound _ _ _).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)) (hC _)
      (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
  have hzi : Integrable (fun g => ∑ b, (K (goeMatrix r g)*B) b i*K (goeMatrix r g) b i) μ :=
    Integrable.mono' (integrable_const (C*opNorm B*C)) (by
      have hc := hcomp.continuous
      exact (continuous_finsetSum _ (fun b _ =>
        ((hc.mul continuous_const).matrix_elem b i).mul (hc.matrix_elem b i))).aestronglyMeasurable)
      (ae_of_all _ hz)
  have hi : Integrable (fun g => Matrix.trace (K (goeMatrix r g)*B)) μ :=
    gaussianProduct_integrable_lipschitz hT
  have ht : (∫ g, |Matrix.trace (K (goeMatrix r g)*B)-
      ∫ h, Matrix.trace (K (goeMatrix r h)*B) ∂μ| ∂μ) ≤ (2*exp (π^2/8))*(T:ℝ) :=
    gaussianProduct_centered_L1 hT hT0
  exact integral_loop_deviation hr hi (hf i i).continuous.aestronglyMeasurable
    (ae_of_all _ (fun g => hc g i i)) hzi (ae_of_all _ hz) ht
    (goe_inverse_loop_raw hr B i hf hc hd hs hder)

end SKGap

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TruncationGoodSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory
open SKGap.RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma truncationGoodSet_measurable (r R lo hi : ℝ) (D C : Matrix ι ι ℝ) :
    MeasurableSet (truncationGoodSet r R lo hi D C) := by
  have hg := (goeMatrix_pi_lipschitz (ι := ι) r).continuous
  have hc : Continuous (fun g => liftMatrix (1-D*(goeMatrix r g-C)*D)) := by
    dsimp [liftMatrix]; fun_prop
  exact (measurableSet_lt (continuous_realOpNorm.comp hg).measurable measurable_const).inter
    ((measurableSet_lt measurable_const (ComplexSpectral.continuous_lowerRayleigh.comp hc).measurable).inter
      (measurableSet_lt measurable_const (ComplexSpectral.continuous_lowerRayleigh.comp hc.neg).measurable))

lemma realTruncatedK_lipschitz (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (D C : Matrix ι ι ℝ) (hD : Dᵀ = D) (hC : Cᵀ = C) :
    LipschitzWith (Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C)))
      (realTruncatedK f R hR D C) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simp only [dist_eq_norm]
  exact (realTruncatedK_sub_norm f hR D C M N hD hC).trans
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))

omit [Fintype ι] [DecidableEq ι] in
lemma goeMatrix_transpose (r : ℝ) (g : MatrixCoordinates ι → ℝ) :
    (goeMatrix r g)ᵀ = goeMatrix r g := by
  ext i k
  simp [goeMatrix,add_comm]

omit [Fintype ι] in
lemma symmetricElementary_transpose (i k : ι) :
    (symmetricElementary i k)ᵀ = symmetricElementary i k := by
  simp [symmetricElementary,Matrix.transpose_add,Matrix.transpose_single,add_comm]

lemma realTruncatedK_goe_derivative (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C : Matrix ι ι ℝ) (r : ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (g : MatrixCoordinates ι → ℝ)
    (hg : g ∈ truncationGoodSet r R lo hi D C) (i b : ι) :
    HasDerivAt (fun t : ℝ => realTruncatedK f R hR D C (goeMatrix r g+t • symmetricElementary i b) b i)
      ((realTruncatedK f R hR D C (goeMatrix r g)*(D*D)*symmetricElementary i b*
        realTruncatedK f R hR D C (goeMatrix r g)) b i) 0 := by
  exact matrixEntry_derivative
    (realTruncatedK_derivative f hlo hf hR D C (goeMatrix r g) (symmetricElementary i b)
      hD hC (goeMatrix_transpose r g) (symmetricElementary_transpose i b) hg.1 hg.2.1 hg.2.2) b i

theorem realTruncatedK_first_loop (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (D C : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (i : ι) :
    let K := realTruncatedK f R hR D C
    let c := ComplexMatrix.kBound f R (liftMatrix D) (liftMatrix C)
    let L := Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C))
    let Lπ : ℝ≥0 := L*(⟨sqrt (2*r),sqrt_nonneg _⟩ *
      (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
    let T : ℝ≥0 := (⟨sqrt (Fintype.card ι)*opNorm (D*D),
      mul_nonneg (sqrt_nonneg _) (norm_nonneg _)⟩*L)*⟨sqrt (2*r),sqrt_nonneg _⟩+1
    let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
    |(∫ g, (goeMatrix r g*K (goeMatrix r g)) i i ∂μ)-
      r*(∫ g, Matrix.trace (K (goeMatrix r g)*(D*D)) ∂μ)*(∫ g, K (goeMatrix r g) i i ∂μ)| ≤
      (Fintype.card ι:ℝ)*(sqrt (2*r)*(Lπ:ℝ)+r*(2*c*opNorm (D*D)*c))*
        μ.real (truncationGoodSet r R lo hi D C)ᶜ+
        r*(c*((2*Real.exp (π^2/8))*(T:ℝ))+c*opNorm (D*D)*c) := by
  intro K c L Lπ T μ
  have hK : LipschitzWith L K := realTruncatedK_lipschitz f hR D C hD hC
  have ht : LipschitzWith T (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) =>
      Matrix.trace (K (goeMatrix r g)*(D*D))) := by
    exact ((matrixTrace_mul_lipschitz hK (D*D)).comp (goeMatrix_L2_lipschitz r)).weaken
      (le_add_of_nonneg_right (by norm_num))
  have ht0 : 0 < T := by dsimp [T]; positivity
  exact goe_inverse_loop_centered hr (D*D) i hK
    (fun M => realTruncatedK_opNorm f hR D C M hD hC) ht ht0
    (truncationGoodSet_measurable r R lo hi D C)
    (fun g hg b => realTruncatedK_goe_derivative f hlo hf hR D C r hD hC g hg i b)

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathBiasBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

noncomputable section
open Real
namespace SKGap

lemma power_exponential_bound (k : ℕ) {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x^k*Real.exp (-c*x) ≤ (k.factorial:ℝ)/c^k := by
  have hfac : (0:ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have h := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (c*x) (mul_nonneg hc.le hx) k)
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-c*x)).le
  have he : Real.exp (c*x)*Real.exp (-c*x)=1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hr : (Real.exp (c*x)*(k.factorial:ℝ))*Real.exp (-c*x) = (k.factorial:ℝ) := by
    calc
      _ = (k.factorial:ℝ)*(Real.exp (c*x)*Real.exp (-c*x)) := by ring
      _ = _ := by rw [he,mul_one]
  rw [hr,mul_pow] at hh
  apply (le_div_iff₀ (pow_pos hc k)).mpr
  nlinarith only [hh]

lemma exponential_tail_absorptions {c n p : ℝ} (hc : 0 < c) (hn : 1 ≤ n)
    (hp : p ≤ 3*Real.exp (-c*n)) :
    p ≤ (3/c)/n ∧ (n^2+n)*p ≤ (36/c^3)/n ∧
      n*sqrt p ≤ (8*sqrt 3/c^2)/n := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have he1 : n*Real.exp (-c*n) ≤ 1/c := by
    simpa only [pow_one,Nat.factorial_one,Nat.cast_one] using power_exponential_bound 1 hc hn0.le
  have he3 : n^3*Real.exp (-c*n) ≤ 6/c^3 := by
    convert power_exponential_bound 3 hc hn0.le using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have he2 : n^2*Real.exp (-(c/2)*n) ≤ 2/(c/2)^2 := by
    convert power_exponential_bound 2 (half_pos hc) hn0.le using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have he : 0 ≤ Real.exp (-c*n) := (Real.exp_pos _).le
  refine ⟨?_,?_,?_⟩
  · apply (le_div_iff₀ hn0).mpr
    have hh := mul_le_mul_of_nonneg_right hp hn0.le
    have hx : (3:ℝ)/c=3*(1/c) := by ring
    rw [hx]
    nlinarith only [hh,he1]
  · apply (le_div_iff₀ hn0).mpr
    have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ (n^2+n)*n by positivity)
    have hnn : (n^2+n)*n ≤ 2*n^3 := by nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hn)]
    have hh' := mul_le_mul_of_nonneg_right hnn (show 0 ≤ 3*Real.exp (-c*n) by positivity)
    have hx : (36:ℝ)/c^3=6*(6/c^3) := by ring
    rw [hx]
    nlinarith only [hh,hh',he3]
  · have hs : sqrt p ≤ sqrt 3*Real.exp (-(c/2)*n) := by
      apply (sqrt_le_sqrt hp).trans_eq
      rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
      congr 1
      rw [← Real.exp_half]
      congr 1
      ring
    apply (le_div_iff₀ hn0).mpr
    have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg n)
    have hh' := mul_le_mul_of_nonneg_left he2 (sqrt_nonneg 3)
    have heq : sqrt 3*(2/(c/2)^2)=8*sqrt 3/c^2 := by field_simp; ring
    rw [heq] at hh'
    nlinarith only [hh,hh']

end SKGap

namespace SKGap
open Real

lemma loopErrorConstants_nonneg (j A B L rate : ℝ)
    (hj : 0 ≤ j) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hc : 0 < rate) :
    0 ≤ loopErrorConstantOne j A B L rate ∧ 0 ≤ loopErrorConstantTwo j A B rate := by
  unfold loopErrorConstantOne loopErrorConstantTwo
  exact ⟨by positivity,by positivity⟩

lemma loop_error_one_absorption {j A B L rate n p : ℝ}
    (hj : 0 ≤ j) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hc : 0 < rate) (hn : 1 ≤ n) (hp : p ≤ 3*Real.exp (-rate*n)) :
    (2*j*L*(n^2+n)+2*j*B*A*B)*p+
      (j/n)*(B*(2*Real.exp (π^2/8))*(A*L*sqrt (2*j)+1)+B*A*B) ≤
      loopErrorConstantOne j A B L rate/n := by
  obtain ⟨h₁,h₂,_⟩ := exponential_tail_absorptions hc hn hp
  calc
    _ = 2*j*L*((n^2+n)*p)+2*j*B*A*B*p+
      (j/n)*(B*(2*Real.exp (π^2/8))*(A*L*sqrt (2*j)+1)+B*A*B) := by ring
    _ ≤ 2*j*L*((36/rate^3)/n)+2*j*B*A*B*((3/rate)/n)+
      (j/n)*(B*(2*Real.exp (π^2/8))*(A*L*sqrt (2*j)+1)+B*A*B) := by gcongr
    _ = _ := by unfold loopErrorConstantOne; ring

lemma loop_error_two_absorption {j A B rate n p : ℝ}
    (hj : 0 ≤ j) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : 0 < rate) (hn : 1 ≤ n) (hp : p ≤ 3*Real.exp (-rate*n)) :
    (B+1+A*(j*A)*B)*p+A*B*n*sqrt (2*j)*sqrt p ≤
      loopErrorConstantTwo j A B rate/n := by
  obtain ⟨h₁,_,h₃⟩ := exponential_tail_absorptions hc hn hp
  calc
    _ = (B+1+A*(j*A)*B)*p+A*B*sqrt (2*j)*(n*sqrt p) := by ring
    _ ≤ (B+1+A*(j*A)*B)*((3/rate)/n)+A*B*sqrt (2*j)*((8*sqrt 3/rate^2)/n) := by gcongr
    _ = _ := by unfold loopErrorConstantTwo; ring
end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNormDiagonal
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_diagonal_eq (d : ι → ℝ) : opNorm (diagonal d) = ‖d‖ :=
  Matrix.l2_opNorm_diagonal d

lemma opNorm_diagonal_le {d : ι → ℝ} {C : ℝ} (hC : 0 ≤ C) (hd : ∀ i, |d i| ≤ C) :
    opNorm (diagonal d) ≤ C := by
  rw [opNorm_diagonal_eq]
  exact (pi_norm_le_iff_of_nonneg hC).mpr (fun i => by simpa only [Real.norm_eq_abs] using hd i)

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex ComplexSpectral
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pathDiagonal_opNorm {a : ι → ℝ} {A z : ℝ} (_hA0 : 0 ≤ A)
    (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1) :
    opNorm (pathDiagonal a z) ≤ sqrt A := by
  apply opNorm_diagonal_le (sqrt_nonneg _)
  intro i
  rw [abs_of_nonneg (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))]
  have hz1 : sqrt z ≤ 1 := by simpa using sqrt_le_sqrt hz.2
  exact (mul_le_mul hz1 (sqrt_le_sqrt (hA i)) (sqrt_nonneg _) (by norm_num)).trans_eq (one_mul _)

lemma pathShift_opNorm {z q : ℝ} (hz : z ∈ Icc (0:ℝ) 1) (hq : 0 ≤ q) :
    opNorm (pathShift (ι := ι) z q) ≤ q := by
  apply opNorm_diagonal_le hq
  intro i
  rw [abs_of_nonneg (mul_nonneg hz.1 hq)]
  exact (mul_le_mul_of_nonneg_right hz.2 hq).trans_eq (one_mul _)

variable [Nonempty ι]
omit [DecidableEq ι] in
lemma diagonal_mean_bounds {j A : ℝ} {a : ι → ℝ} (hj : 0 ≤ j)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) :
    0 ≤ (j/(Fintype.card ι:ℝ))*∑ i, a i ∧
    (j/(Fintype.card ι:ℝ))*∑ i, a i ≤ j*A := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨mul_nonneg (div_nonneg hj hn.le) (Finset.sum_nonneg (fun i _ => ha i)),?_⟩
  have hs : (∑ i, a i) ≤ (Fintype.card ι:ℝ)*A := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hA i)
  calc
    _ ≤ (j/(Fintype.card ι:ℝ))*((Fintype.card ι:ℝ)*A) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hj hn.le)
    _ = _ := by field_simp

end SKGap

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma path_constants_bound (f : 𝓢(ℝ,ℂ)) {R j A z q : ℝ} {a : ι → ℝ}
    (hR : 0 ≤ R) (_hj : 0 ≤ j) (hA0 : 0 ≤ A) (hA : ∀ i, a i ≤ A)
    (hq : 0 ≤ q) (hqA : q ≤ j*A) (hz : z ∈ Icc (0:ℝ) 1) :
    ComplexMatrix.kBound f R (liftMatrix (pathDiagonal a z)) (liftMatrix (pathShift z q)) ≤ pathBound f R j A ∧
    ComplexMatrix.kLip f R (liftMatrix (pathDiagonal a z)) (liftMatrix (pathShift z q)) ≤ pathLip f R j A ∧
    opNorm (pathDiagonal a z*pathDiagonal a z) ≤ A := by
  have hd := pathDiagonal_opNorm hA0 hA hz
  have hc := (pathShift_opNorm (ι := ι) hz hq).trans hqA
  have hd2 : opNorm (pathDiagonal a z)^2 ≤ A := by
    have hh := pow_le_pow_left₀ (show 0 ≤ opNorm (pathDiagonal a z) from norm_nonneg _) hd 2
    rwa [sq_sqrt hA0] at hh
  have hd4 : opNorm (pathDiagonal a z)^4 ≤ A^2 := by
    calc
      _ = (opNorm (pathDiagonal a z)^2)^2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hd2 2
  have h₀ := ComplexMatrix.fourierMoment_nonneg f 0
  have h₁ := (ComplexMatrix.fl_nonneg f).1
  have hc0 : 0 ≤ R+opNorm (pathShift (ι := ι) z q) := add_nonneg hR (norm_nonneg _)
  unfold ComplexMatrix.kBound ComplexMatrix.kLip ComplexMatrix.gBound ComplexMatrix.gLip pathBound pathLip
  simp only [ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift]
  refine ⟨?_,?_,?_⟩
  · gcongr
  · gcongr
  · exact (opNorm_mul _ _).trans (by nlinarith)

variable [Nonempty ι]
omit [DecidableEq ι] in
lemma matrixCoordinates_dimension_bound :
    ((Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal : ℝ≥0) ≤
      (Fintype.card ι:ℝ≥0)^2+Fintype.card ι := by
  have hn : 1 ≤ (Fintype.card (MatrixCoordinates ι) : ℝ≥0) := by
    exact_mod_cast (Fintype.card_pos (α := MatrixCoordinates ι))
  have he : (1/(2:ℝ≥0∞)).toReal = (1/2:ℝ) := by norm_num
  rw [he]
  have h := NNReal.rpow_le_rpow_of_exponent_le hn (show (1/2:ℝ) ≤ 1 by norm_num)
  simpa [MatrixCoordinates,Fintype.card_sum,Fintype.card_prod,pow_two] using h

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianCoordinateMemLp
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
variable {ι : Type*} [Fintype ι]

lemma gaussianCoordinate_memLp (a : MatrixCoordinates ι) :
    MemLp (fun g : MatrixCoordinates ι → ℝ => g a) 2
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  exact (IsGaussian.memLp_id (gaussianReal 0 1) 2 (by norm_num)).comp_measurePreserving
    (measurePreserving_eval (fun _ : MatrixCoordinates ι => gaussianReal 0 1) a)

lemma gaussianCoordinate_integral_sq (a : MatrixCoordinates ι) :
    (∫ g : MatrixCoordinates ι → ℝ, (g a)^2 ∂Measure.pi (fun _ => gaussianReal 0 1)) = 1 := by
  rw [integral_comp_eval (μ := fun _ : MatrixCoordinates ι => gaussianReal 0 1) (i := a) (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^2) (gaussianReal 0 1))]
  have hh := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop),integral_id_gaussianReal] at hh
  simpa only [sub_zero,NNReal.coe_one] using hh

lemma goeEntry_memLp (r : ℝ) (i b : ι) :
    MemLp (fun g => goeMatrix r g i b) 2
      (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) := by
  exact ((gaussianCoordinate_memLp (.inl (i,b))).add
    (gaussianCoordinate_memLp (.inl (b,i)))).const_mul _

lemma goeEntry_integral_sq_le {r : ℝ} (hr : 0 ≤ r) (i b : ι) :
    (∫ g, (goeMatrix r g i b)^2
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) ≤ 2*r := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  have h1 := (gaussianCoordinate_memLp (.inl (i,b))).integrable_sq
  have h2 := (gaussianCoordinate_memLp (.inl (b,i))).integrable_sq
  have hb (g : MatrixCoordinates ι → ℝ) : (goeMatrix r g i b)^2 ≤
      r*((g (.inl (i,b)))^2+(g (.inl (b,i)))^2) := by
    have hx : (g (.inl (i,b))+g (.inl (b,i)))^2 ≤
        2*((g (.inl (i,b)))^2+(g (.inl (b,i)))^2) := by
      nlinarith only [sq_nonneg (g (.inl (i,b))-g (.inl (b,i)))]
    simp only [goeMatrix,mul_pow]
    calc
      _ ≤ (sqrt (2*r)/2)^2*(2*((g (.inl (i,b)))^2+(g (.inl (b,i)))^2)) :=
        mul_le_mul_of_nonneg_left hx (sq_nonneg _)
      _ = _ := by rw [div_pow,sq_sqrt (by positivity)]; ring
  calc
    _ ≤ ∫ g, r*((g (.inl (i,b)))^2+(g (.inl (b,i)))^2) ∂μ :=
      integral_mono (goeEntry_memLp r i b).integrable_sq ((h1.add h2).const_mul r) hb
    _ = 2*r := by
      rw [integral_const_mul,integral_add h1 h2,gaussianCoordinate_integral_sq,
        gaussianCoordinate_integral_sq]
      ring

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_IntegralAbsSet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
namespace SKGap
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integral_abs_on_set_le {F : Ω → ℝ} (hF : MemLp F 2 μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    (∫ x in s, |F x| ∂μ) ≤ sqrt (∫ x, (F x)^2 ∂μ)*sqrt (μ.real s) := by
  have hG : MemLp (s.indicator (fun _ : Ω => (1:ℝ))) 2 μ :=
    memLp_indicator_const 2 hs 1 (Or.inr (measure_ne_top _ _))
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hF) (by simpa using hG)
  have he : (fun x => ‖F x‖*‖s.indicator (fun _ : Ω => (1:ℝ)) x‖) =
      s.indicator (fun x => |F x|) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx,Real.norm_eq_abs]
  have hg : (fun x => ‖s.indicator (fun _ : Ω => (1:ℝ)) x‖^(2:ℝ)) =
      s.indicator (fun _ : Ω => (1:ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [he,hg,integral_indicator hs,integral_indicator hs] at hh
  simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs,← Real.sqrt_eq_rpow,
    integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using hh

omit [IsProbabilityMeasure μ] in
lemma integral_exceptional_equal_bound {F G H : Ω → ℝ} {s : Set Ω}
    (hs : MeasurableSet s) (hF : Integrable F μ) (hG : Integrable G μ)
    (hH : Integrable H μ) (he : ∀ x ∉ s, F x=G x)
    (hb : ∀ x ∈ s, ‖F x-G x‖ ≤ H x) :
    |(∫ x, F x ∂μ)-(∫ x, G x ∂μ)| ≤ ∫ x in s, H x ∂μ := by
  rw [← integral_sub hF hG]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_indicator hs]
  apply integral_mono ((hF.sub hG).norm) (hH.indicator hs)
  intro x
  change ‖F x-G x‖ ≤ s.indicator H x
  by_cases hx : x∈s
  · simpa only [Set.indicator_of_mem hx] using hb x hx
  · simp only [Set.indicator_of_notMem hx,he x hx,sub_self,norm_zero,le_refl]

end SKGap

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma abs_mul_entry_bound (M K : Matrix ι ι ℝ) (C : ℝ) (hK : ∀ a b, |K a b| ≤ C) (i : ι) :
    |(M*K) i i| ≤ C*∑ b, |M i b| := by
  rw [Matrix.mul_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  rw [abs_mul,mul_comm C]
  exact mul_le_mul_of_nonneg_left (hK b i) (abs_nonneg _)

omit [DecidableEq ι] in

theorem goe_diagonal_inverse_loop {r : ℝ} (hr : 0 ≤ r) (a c : ι → ℝ) (i : ι)
    {K : (MatrixCoordinates ι → ℝ) → Matrix ι ι ℝ} {C : ℝ}
    {s : Set (MatrixCoordinates ι → ℝ)} (hK : Continuous K)
    (hC : ∀ g a b, |K g a b| ≤ C) (hs : MeasurableSet s)
    (he : ∀ g ∈ s, K g i i = 1+a i*((goeMatrix r g*K g) i i-c i*K g i i)) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
    |(∫ g, K g i i ∂μ)-
      (1+a i*((∫ g, (goeMatrix r g*K g) i i ∂μ)-c i*(∫ g, K g i i ∂μ)))| ≤
      (C+1+|a i*c i| *C)*μ.real sᶜ+
        (|a i| *C)*(Fintype.card ι:ℝ)*sqrt (2*r)*sqrt (μ.real sᶜ) := by
  intro μ
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 i i)
  have hKi (a b : ι) : Integrable (fun g => K g a b) μ :=
    Integrable.mono' (integrable_const C) (hK.matrix_elem a b).aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hC g a b))
  have hW (b : ι) : Integrable (fun g => goeMatrix r g i b) μ :=
    (goeEntry_memLp r i b).integrable (by norm_num)
  have hWK (b : ι) : Integrable (fun g => goeMatrix r g i b*K g b i) μ := by
    simpa only [mul_comm] using (hW b).bdd_mul (hK.matrix_elem b i).aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hC g b i))
  have hWI : Integrable (fun g => (goeMatrix r g*K g) i i) μ :=
    integrable_finsetSum _ (fun b _ => hWK b)
  let A := C+1+|a i*c i| *C
  let B := |a i| *C
  let H := fun g => A+B*∑ b, |goeMatrix r g i b|
  have hHA : Integrable (fun g => ∑ b, |goeMatrix r g i b|) μ :=
    integrable_finsetSum _ (fun b _ => (hW b).norm)
  have hHI : Integrable H μ := (integrable_const A).add (hHA.const_mul B)
  have hGI : Integrable (fun g => 1+a i*((goeMatrix r g*K g) i i-c i*K g i i)) μ :=
    (integrable_const 1).add ((hWI.sub ((hKi i i).const_mul _)).const_mul _)
  have hb (g : MatrixCoordinates ι → ℝ) :
      ‖K g i i-(1+a i*((goeMatrix r g*K g) i i-c i*K g i i))‖ ≤ H g := by
    rw [Real.norm_eq_abs]
    have hid : K g i i-(1+a i*((goeMatrix r g*K g) i i-c i*K g i i)) =
        (K g i i-1)+(a i*c i)*K g i i+(-a i)*(goeMatrix r g*K g) i i := by ring
    rw [hid]
    apply (abs_add_le _ _).trans
    apply (add_le_add (abs_add_le _ _) le_rfl).trans
    have hk1 : |K g i i-1| ≤ C+1 := (abs_sub _ _).trans (by simpa using add_le_add_right (hC g i i) 1)
    have hk2 : |(a i*c i)*K g i i| ≤ |a i*c i| *C := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC g i i) (abs_nonneg _)
    have hk3 : |(-a i)*(goeMatrix r g*K g) i i| ≤ |a i| *(C*∑ b, |goeMatrix r g i b|) := by
      rw [abs_mul,abs_neg]
      exact mul_le_mul_of_nonneg_left (abs_mul_entry_bound _ _ C (hC g) i) (abs_nonneg _)
    exact (add_le_add (add_le_add hk1 hk2) hk3).trans_eq (by dsimp [H,A,B]; ring)
  have hraw := integral_exceptional_equal_bound hs.compl (hKi i i) hGI hHI
    (fun g hg => he g (by simpa using hg)) (fun g _ => hb g)
  have hbad (b : ι) : (∫ g in sᶜ, |goeMatrix r g i b| ∂μ) ≤
      sqrt (2*r)*sqrt (μ.real sᶜ) := by
    apply (integral_abs_on_set_le (goeEntry_memLp r i b) hs.compl).trans
    exact mul_le_mul_of_nonneg_right (sqrt_le_sqrt (goeEntry_integral_sq_le hr i b)) (sqrt_nonneg _)
  have hHr : (∫ g in sᶜ, H g ∂μ) ≤ A*μ.real sᶜ+B*(Fintype.card ι:ℝ)*sqrt (2*r)*sqrt (μ.real sᶜ) := by
    rw [show H = fun g => A+B*∑ b, |goeMatrix r g i b| from rfl,
      integral_add (integrable_const A) ((hHA.const_mul B).mono_measure Measure.restrict_le_self),
      integral_const,integral_const_mul]
    have hWa (b : ι) : Integrable (fun g => |goeMatrix r g i b|) (μ.restrict sᶜ) := by
      simpa only [Real.norm_eq_abs] using (hW b).norm.mono_measure Measure.restrict_le_self
    rw [integral_finsetSum _ (fun b _ => hWa b)]
    simp only [measureReal_restrict_apply_univ,smul_eq_mul]
    calc
      _ ≤ μ.real sᶜ*A+B*(∑ _b : ι, sqrt (2*r)*sqrt (μ.real sᶜ)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => hbad b))
          (mul_nonneg (abs_nonneg _) hC0))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have heI : (∫ g, 1+a i*((goeMatrix r g*K g) i i-c i*K g i i) ∂μ) =
      1+a i*((∫ g, (goeMatrix r g*K g) i i ∂μ)-c i*(∫ g, K g i i ∂μ)) := by
    have ht := integral_add (integrable_const (1:ℝ))
      ((hWI.sub ((hKi i i).const_mul (c i))).const_mul (a i))
    change (∫ g, 1+a i*((goeMatrix r g*K g) i i-c i*K g i i) ∂μ) = _ at ht
    rw [ht,integral_const_mul]
    simp only [Pi.sub_apply]
    rw [integral_sub hWI ((hKi i i).const_mul (c i)),integral_const_mul]
    simp
  rw [heI] at hraw
  exact hraw.trans hHr

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_RealSymmetricResolventUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
namespace SKGap
open RealComplex ComplexSpectral
open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma real_symmetric_resolvent_isUnit (D C M : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (hM : Mᵀ = M)
    (hl : 0 < _root_.OAI.SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M-C)*D))) :
    IsUnit (1-D*D*(M-C)) := by
  have hs : (liftMatrix (1-D*(M-C)*D)).IsHermitian := by
    rw [liftMatrix_sub,liftMatrix_one,liftMatrix_mul,liftMatrix_mul,liftMatrix_sub]
    change (1-liftMatrix D*(liftMatrix M-liftMatrix C)*liftMatrix D)ᴴ = _
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_mul,
      liftMatrix_hermitian D hD,liftMatrix_hermitian C hC,liftMatrix_hermitian M hM,mul_assoc]
  have hsu : IsUnit (liftMatrix (1-D*(M-C)*D)) :=
    (hs.posDef_iff_eigenvalues_pos.mpr (fun i => hl.trans_le (eigenvalue_lower_bound hs i))).isUnit
  have hrs := (liftMatrix_isUnit_iff _).mp hsu
  exact ResolventIdentity.inverse_one_sub_square_mul_unit D (M-C) hrs

lemma diagonal_resolvent_identity (d c : ι → ℝ) (M K : Matrix ι ι ℝ)
    (hK : (1-diagonal d*diagonal d*(M-diagonal c))*K=1) (i : ι) :
    K i i = 1+(d i)^2*((M*K) i i-c i*K i i) := by
  have he : (1-diagonal d*diagonal d*(M-diagonal c))*K =
      K-diagonal (fun a => (d a)^2)*(M*K-diagonal c*K) := by
    have hd : diagonal d*diagonal d = diagonal (fun a => (d a)^2) := by
      rw [Matrix.diagonal_mul_diagonal]; congr 1; ext a; simp only [pow_two]
    rw [hd]
    noncomm_ring
  rw [he] at hK
  have hh := congrFun (congrFun hK i) i
  simp only [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.one_apply_eq] at hh
  nlinarith only [hh]

theorem realTruncatedK_second_loop (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (d c : ι → ℝ) (i : ι) :
    let D := diagonal d
    let C := diagonal c
    let K := realTruncatedK f R hR D C
    let b := ComplexMatrix.kBound f R (liftMatrix D) (liftMatrix C)
    let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
    let s := truncationGoodSet r R lo hi D C
    |(∫ g, K (goeMatrix r g) i i ∂μ)-
      (1+(d i)^2*((∫ g, (goeMatrix r g*K (goeMatrix r g)) i i ∂μ)-
        c i*(∫ g, K (goeMatrix r g) i i ∂μ)))| ≤
      (b+1+|(d i)^2*c i| *b)*μ.real sᶜ+
        (|(d i)^2| *b)*(Fintype.card ι:ℝ)*sqrt (2*r)*sqrt (μ.real sᶜ) := by
  intro D C K b μ s
  have hD : Dᵀ=D := Matrix.diagonal_transpose _
  have hC : Cᵀ=C := Matrix.diagonal_transpose _
  have hKL := realTruncatedK_lipschitz f hR D C hD hC
  apply goe_diagonal_inverse_loop hr (fun a => (d a)^2) c i
    (hKL.continuous.comp (goeMatrix_pi_lipschitz r).continuous)
    (fun g a b => (matrix_entry_le_opNorm _ a b).trans
      (realTruncatedK_opNorm f hR D C _ hD hC))
    (truncationGoodSet_measurable r R lo hi D C)
  intro g hg
  apply diagonal_resolvent_identity d c (goeMatrix r g) (K (goeMatrix r g))
  have hunit := real_symmetric_resolvent_isUnit D C (goeMatrix r g) hD hC
    (goeMatrix_transpose r g) (hlo.trans hg.2.1)
  have hid := realTruncatedK_eq_inverse f hlo hf hR D C (goeMatrix r g) hD hC
    (goeMatrix_transpose r g) hg.1.le hg.2.1.le hg.2.2.le
  change (1-D*D*(goeMatrix r g-C))*K (goeMatrix r g)=1
  rw [show K (goeMatrix r g) = _ from hid]
  exact Matrix.mul_nonsing_inv _ (((1-D*D*(goeMatrix r g-C)).isUnit_iff_isUnit_det).mp hunit)

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ExpectedCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integrated_diagonal_trace (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (d c : ι → ℝ) (r : ℝ) :
    (∫ g, trace (realTruncatedK f R hR (diagonal d) (diagonal c) (goeMatrix r g)*
      (diagonal d*diagonal d))
      ∂(Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))) =
      ∑ b, (d b)^2*expectedCutoff f R hR (diagonal d) (diagonal c) r b := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  let K := fun g => realTruncatedK f R hR (diagonal d) (diagonal c) (goeMatrix r g)
  let B := ComplexMatrix.kBound f R (liftMatrix (diagonal d)) (liftMatrix (diagonal c))
  have hc : Continuous K := (realTruncatedK_lipschitz f hR _ _ (diagonal_transpose _) (diagonal_transpose _)).continuous.comp
    (goeMatrix_pi_lipschitz r).continuous
  have hi (b : ι) : Integrable (fun g => K g b b) μ :=
    Integrable.mono' (integrable_const B) (hc.matrix_elem b b).aestronglyMeasurable
      (ae_of_all _ (fun g => by
        rw [Real.norm_eq_abs]
        exact (matrix_entry_le_opNorm _ b b).trans
          (realTruncatedK_opNorm f hR _ _ _ (diagonal_transpose _) (diagonal_transpose _))))
  have he (g : MatrixCoordinates ι → ℝ) : trace (K g*(diagonal d*diagonal d)) =
      ∑ b, (d b)^2*K g b b := by
    rw [diagonal_mul_diagonal]
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_diagonal]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [show (fun g => trace (realTruncatedK f R hR (diagonal d) (diagonal c) (goeMatrix r g)*
    (diagonal d*diagonal d))) = (fun g => ∑ b, (d b)^2*K g b b) from funext he]
  rw [integral_finsetSum _ (fun b _ => (hi b).const_mul _)]
  simp only [integral_const_mul,expectedCutoff,K,μ]

omit [Fintype ι] [DecidableEq ι] in
lemma combine_resolvent_loops {k w r a c t e₁ e₂ : ℝ}
    (h₁ : |w-r*t*k| ≤ e₁) (h₂ : |k-(1+a*(w-c*k))| ≤ e₂) :
    |k-1-a*(r*t-c)*k| ≤ e₂+|a| *e₁ := by
  have he : k-1-a*(r*t-c)*k = (k-(1+a*(w-c*k)))+a*(w-r*t*k) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add h₂ (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)))

theorem actual_cutoff_self_consistency (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (d c : ι → ℝ) (i : ι) :
    let k := expectedCutoff f R hR (diagonal d) (diagonal c) r
    |k i-1-(d i)^2*(r*(∑ b, (d b)^2*k b)-c i)*k i| ≤
      cutoffErrorTwo f r R lo hi d c i+
        |(d i)^2| *cutoffErrorOne f r R lo hi (diagonal d) (diagonal c) := by
  intro k
  have h₁ := realTruncatedK_first_loop f hlo hf hR hr (diagonal d) (diagonal c)
    (diagonal_transpose _) (diagonal_transpose _) i
  have h₂ := realTruncatedK_second_loop f hlo hf hR hr d c i
  dsimp only at h₁ h₂
  rw [integrated_diagonal_trace f hR d c r] at h₁
  exact combine_resolvent_loops h₁ h₂

end SKGap

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma cutoffErrorOne_bound (f : 𝓢(ℝ,ℂ)) {j R lo hi A B L p : ℝ}
    (D C : Matrix ι ι ℝ) (hj : 0 ≤ j) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hb : ComplexMatrix.kBound f R (liftMatrix D) (liftMatrix C) ≤ B)
    (hl : ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C) ≤ L)
    (hd : opNorm (D*D) ≤ A)
    (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet (j/(Fintype.card ι:ℝ)) R lo hi D C)ᶜ ≤ p) :
    cutoffErrorOne f (j/(Fintype.card ι:ℝ)) R lo hi D C ≤
      (2*j*L*((Fintype.card ι:ℝ)^2+Fintype.card ι)+2*j*B*A*B)*p+
      (j/(Fintype.card ι:ℝ))*(B*(2*Real.exp (π^2/8))*(A*L*sqrt (2*j)+1)+B*A*B) := by
  let n : ℝ := Fintype.card ι
  let r := j/n
  let b := ComplexMatrix.kBound f R (liftMatrix D) (liftMatrix C)
  let ℓ : ℝ := (Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C)) : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hr : 0 ≤ r := div_nonneg hj hn.le
  have hd0 : 0 ≤ opNorm (D*D) := norm_nonneg _
  have hb0 : 0 ≤ b := by
    have hh := (ComplexMatrix.g_constants_nonneg f hR 1 1 (liftMatrix D) (liftMatrix D)).1
    dsimp [b,ComplexMatrix.kBound]
    exact add_nonneg zero_le_one (mul_nonneg hh (add_nonneg hR (norm_nonneg _)))
  have hl0 : 0 ≤ ℓ := NNReal.coe_nonneg _
  have hl' : ℓ ≤ L := by
    have hh : Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C)) ≤ (⟨L,hL⟩ : ℝ≥0) := Real.toNNReal_le_iff_le_coe.mpr hl
    exact_mod_cast hh
  have hp0 : 0 ≤ p := (measureReal_nonneg).trans hp
  have hnr : n*r = j := by dsimp [r]; field_simp
  have hs : sqrt n*sqrt (2*r)=sqrt (2*j) := by
    rw [← sqrt_mul hn.le]
    congr 1
    nlinarith [hnr]
  have hT : sqrt n*opNorm (D*D)*ℓ*sqrt (2*r)+1 ≤ A*L*sqrt (2*j)+1 := by
    calc
      _ = opNorm (D*D)*ℓ*(sqrt n*sqrt (2*r))+1 := by ring
      _ ≤ _ := by rw [hs]; gcongr
  have hdim : (((Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^
      (1/(2:ℝ≥0∞)).toReal : ℝ≥0) : ℝ) ≤ n^2+n := by
    have hh := NNReal.coe_le_coe.mpr (matrixCoordinates_dimension_bound (ι := ι))
    simpa only [NNReal.coe_add,NNReal.coe_pow,NNReal.coe_natCast,n] using hh
  have hfirst : n*(sqrt (2*r)*(ℓ*(sqrt (2*r)*
      (((Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal : ℝ≥0) : ℝ)))+
      r*(2*b*opNorm (D*D)*b)) ≤ 2*j*L*(n^2+n)+2*j*B*A*B := by
    calc
      _ ≤ n*(sqrt (2*r)*(L*(sqrt (2*r)*(n^2+n)))+r*(2*B*A*B)) := by gcongr
      _ = _ := by
        have hh := sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hr)
        calc
          _ = n*(L*(n^2+n)*(sqrt (2*r)^2)+r*(2*B*A*B)) := by ring
          _ = 2*(n*r)*L*(n^2+n)+2*(n*r)*B*A*B := by rw [hh]; ring
          _ = _ := by rw [hnr]
  unfold cutoffErrorOne
  dsimp only
  simp only [NNReal.coe_mul,NNReal.coe_add,NNReal.coe_one]
  change n*(sqrt (2*r)*(ℓ*(sqrt (2*r)*_))+r*(2*b*opNorm (D*D)*b))*_+
    r*(b*((2*Real.exp (π^2/8))*(sqrt n*opNorm (D*D)*ℓ*sqrt (2*r)+1))+b*opNorm (D*D)*b) ≤ _
  apply add_le_add
  · exact mul_le_mul hfirst hp measureReal_nonneg (by positivity)
  · apply mul_le_mul_of_nonneg_left _ hr
    apply add_le_add
    · rw [← mul_assoc]
      gcongr
    · gcongr

lemma cutoffErrorTwo_bound (f : 𝓢(ℝ,ℂ)) {j R lo hi A B p : ℝ}
    (d c : ι → ℝ) (i : ι) (hj : 0 ≤ j) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hb : ComplexMatrix.kBound f R (liftMatrix (diagonal d)) (liftMatrix (diagonal c)) ≤ B)
    (hd : (d i)^2 ≤ A) (hc : |c i| ≤ j*A)
    (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet (j/(Fintype.card ι:ℝ)) R lo hi (diagonal d) (diagonal c))ᶜ ≤ p) :
    cutoffErrorTwo f (j/(Fintype.card ι:ℝ)) R lo hi d c i ≤
      (B+1+A*(j*A)*B)*p+A*B*(Fintype.card ι:ℝ)*sqrt (2*j)*sqrt p := by
  have hn : (1:ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hr : j/(Fintype.card ι:ℝ) ≤ j := by
    exact div_le_self hj hn
  have hb0 : 0 ≤ ComplexMatrix.kBound f R (liftMatrix (diagonal d)) (liftMatrix (diagonal c)) := by
    have hh := (ComplexMatrix.g_constants_nonneg f hR 1 1 (liftMatrix (diagonal d)) (liftMatrix (diagonal d))).1
    exact add_nonneg zero_le_one (mul_nonneg hh (add_nonneg hR (norm_nonneg _)))
  have hdc : |(d i)^2*c i| ≤ A*(j*A) := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul hd hc (abs_nonneg _) hA
  have hp0 : 0 ≤ p := measureReal_nonneg.trans hp
  unfold cutoffErrorTwo
  dsimp only
  rw [abs_of_nonneg (sq_nonneg (d i))]
  gcongr
end SKGap
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma path_self_consistency_oai (f : 𝓢(ℝ,ℂ)) {lo hi R j A rate z : ℝ} {a : ι → ℝ}
    (hlo : 0 < lo) (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA0 : 0 ≤ A) (hrate : 0 < rate)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1)
    (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet (j/(Fintype.card ι:ℝ)) R lo hi (pathDiagonal a z)
        (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)))ᶜ ≤
          3*Real.exp (-rate*(Fintype.card ι:ℝ))) (i : ι) :
    let k := pathExpected f R hR j a z
    let B := pathBound f R j A
    let L := pathLip f R j A
    |k i-1-z^2*j*a i*(∑ b, (1/(Fintype.card ι:ℝ))*a b*(k b-1))*k i| ≤
      (loopErrorConstantTwo j A B rate+A*loopErrorConstantOne j A B L rate)/(Fintype.card ι:ℝ) := by
  intro k B L
  let n : ℝ := Fintype.card ι
  let q := (j/n)*∑ b, a b
  let d : ι → ℝ := fun b => sqrt z*sqrt (a b)
  let c : ι → ℝ := fun _ => z*q
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hn1 : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos (α := ι)
  have hq := diagonal_mean_bounds hj ha hA
  have hcst := path_constants_bound f hR hj hA0 hA hq.1 hq.2 hz
  have hconst := path_constants_nonneg f hR hj hA0
  have hd (b : ι) : (d b)^2=z*a b := by
    dsimp [d]; rw [mul_pow,sq_sqrt hz.1,sq_sqrt (ha b)]
  have hdi : (d i)^2 ≤ A := by rw [hd]; exact (mul_le_of_le_one_left (ha i) hz.2).trans (hA i)
  have hci : |c i| ≤ j*A := by
    rw [abs_of_nonneg (mul_nonneg hz.1 hq.1)]
    exact (mul_le_of_le_one_left hq.1 hz.2).trans hq.2
  have he1 := (cutoffErrorOne_bound f (pathDiagonal a z) (pathShift z q) hj hA0 hconst.1 hconst.2 hR
    hcst.1 hcst.2.1 hcst.2.2 (le_refl _)).trans
      (loop_error_one_absorption hj hA0 hconst.1 hconst.2 hrate hn1 hp)
  have he2 := (cutoffErrorTwo_bound f d c i hj hA0 hconst.1 hR hcst.1 hdi hci (le_refl _)).trans
      (loop_error_two_absorption hj hA0 hconst.1 hrate hn1 hp)
  have he := actual_cutoff_self_consistency f hlo hf hR (div_nonneg hj hn.le) d c i
  dsimp only at he
  have hs : (j/n)*(∑ b, (d b)^2*k b)-c i =
      z*j*(∑ b, (1/n)*a b*(k b-1)) := by
    dsimp only [c,q]
    simp_rw [hd,Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have heq : (d i)^2*((j/n)*(∑ b, (d b)^2*k b)-c i)*k i =
      z^2*j*a i*(∑ b, (1/n)*a b*(k b-1))*k i := by rw [hs,hd]; ring
  change |k i-1-(d i)^2*((j/n)*(∑ b, (d b)^2*k b)-c i)*k i| ≤ _ at he
  rw [heq] at he
  apply he.trans
  calc
    _ ≤ loopErrorConstantTwo j A B rate/n+A*(loopErrorConstantOne j A B L rate/n) := by
      apply add_le_add he2
      rw [abs_of_nonneg (sq_nonneg _)]
      apply (mul_le_mul_of_nonneg_left he1 (sq_nonneg _)).trans
      exact mul_le_mul_of_nonneg_right hdi (div_nonneg
        (loopErrorConstants_nonneg j A B L rate hj hA0 hconst.1 hconst.2 hrate).1 hn.le)
    _ = _ := by ring
end SKGap
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SKGap.path_self_consistency_oai.{u_1} := @OAI.SKGap.path_self_consistency_oai.{u_1}
