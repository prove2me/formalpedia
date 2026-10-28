-- Prove2me | solution 1 for OAI.SKGap.actualWord_loop
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:29:46.996946+00:00
-- url     : https://prove2.me/submissions/f52a1fb0-a74c-48a2-be04-252cd914af3f

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
local instance instPseudoMetrizableSpaceMatrixComplex_solutions_1_rc4eb7b_1 : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
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

end SKGap

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

omit [Fintype ι] [DecidableEq ι] in
lemma goeMatrix_transpose (r : ℝ) (g : MatrixCoordinates ι → ℝ) :
    (goeMatrix r g)ᵀ = goeMatrix r g := by
  ext i k
  simp [goeMatrix,add_comm]

omit [Fintype ι] in
lemma symmetricElementary_transpose (i k : ι) :
    (symmetricElementary i k)ᵀ = symmetricElementary i k := by
  simp [symmetricElementary,Matrix.transpose_add,Matrix.transpose_single,add_comm]

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

lemma opNorm_one_le : opNorm (1 : Matrix ι ι ℝ) ≤ 1 := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (1 : Matrix ι ι ℝ)‖ ≤ _
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_ProjectedReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma realProject_opNorm {R : ℝ} (hR : 0 ≤ R) (M : Matrix ι ι ℝ) :
    opNorm (realProject R hR M) ≤ R :=
  (operator_realPart_le _).trans (ComplexMatrix.matrixProject_bound R hR (liftMatrix M)).2

lemma realProject_sub_norm {R : ℝ} (hR : 0 ≤ R) (M N : Matrix ι ι ℝ) :
    ‖realProject R hR M-realProject R hR N‖ ≤ ‖M-N‖ := by
  unfold realProject
  rw [← realPart_sub]
  apply (norm_realPart_le _).trans
  simpa only [← liftMatrix_sub,norm_liftMatrix] using
    ComplexMatrix.matrixProject_sub_norm R hR (liftMatrix M) (liftMatrix N)

lemma realProject_eq_self {R : ℝ} (hR : 0 ≤ R) (M : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hMR : opNorm M ≤ R) : realProject R hR M=M := by
  unfold realProject
  rw [ComplexMatrix.matrixProject_eq_self R hR (liftMatrix M) (liftMatrix_hermitian M hM)
    (by simpa only [ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using hMR)]
  ext i k
  simp [RealComplex.realPart,liftMatrix]

lemma realProject_lipschitz {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 1 (realProject (ι := ι) R hR) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using realProject_sub_norm hR M N

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pathK_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A z : ℝ} (hR : 0 ≤ R) (hj : 0 ≤ j)
    (hA : 0 ≤ A) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hz : z ∈ Icc (0:ℝ) 1) :
    (∀ M, opNorm (pathK f R hR j a z M) ≤ pathBound f R j A) ∧
    (∀ M N, ‖pathK f R hR j a z M-pathK f R hR j a z N‖ ≤ pathLip f R j A*‖M-N‖) := by
  have hq := diagonal_mean_bounds hj ha haA
  have hc := path_constants_bound f hR hj hA haA hq.1 hq.2 hz
  constructor
  · intro M
    exact (realTruncatedK_opNorm f hR _ _ M (diagonal_transpose _) (diagonal_transpose _)).trans hc.1
  · intro M N
    exact (realTruncatedK_sub_norm f hR _ _ M N (diagonal_transpose _) (diagonal_transpose _)).trans
      (mul_le_mul_of_nonneg_right hc.2.1 (norm_nonneg _))

lemma pathK_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A z : ℝ} (hR : 0 ≤ R) (hj : 0 ≤ j)
    (hA : 0 ≤ A) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hz : z ∈ Icc (0:ℝ) 1) : Continuous (pathK f R hR j a z) := by
  apply LipschitzWith.continuous (K := ⟨pathLip f R j A,(path_constants_nonneg f hR hj hA).2⟩)
  apply LipschitzWith.of_dist_le_mul
  intro M N
  change ‖pathK f R hR j a z M-pathK f R hR j a z N‖ ≤ pathLip f R j A*‖M-N‖
  exact (pathK_bounds f hR hj hA ha haA hz).2 M N

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Bilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma operator_le_frobenius (M : Matrix ι ι ℝ) : opNorm M ≤ ‖M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hh := Matrix.frobenius_norm_mul M (Matrix.replicateCol Unit (fun i => x i))
  rw [← Matrix.replicateCol_mulVec,Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol] at hh
  exact hh

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixWordRegularity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
lemma matrixFactorProduct_opNorm (F : List (X→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ x,opNorm (f x) ≤ R) (x : X) :
    opNorm (matrixFactorProduct F x) ≤ (R:ℝ)^F.length := by
  induction F with
  | nil => simpa using opNorm_one_le (ι:=ι)
  | cons f F ih =>
    rw [matrixFactorProduct_cons,List.length_cons,pow_succ']
    exact (opNorm_mul _ _).trans (mul_le_mul (hF f (List.mem_cons_self) x)
      (ih (fun p hp=>hF p (List.mem_cons_of_mem f hp))) (show 0 ≤ opNorm (matrixFactorProduct F x) from norm_nonneg _) R.coe_nonneg)

theorem matrixFactorProduct_lipschitz (F : List (X→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ x,opNorm (f x) ≤ R)
    (hL : ∀ f∈F,LipschitzWith R f) :
    LipschitzWith ((F.length:NNReal)*R^F.length) (matrixFactorProduct F) := by
  induction F with
  | nil => simp [matrixFactorProduct]
  | cons f F ih =>
    have hFt : ∀ p∈F,∀ x,opNorm (p x) ≤ R := fun p hp=>hF p (List.mem_cons_of_mem f hp)
    have hLt : ∀ p∈F,LipschitzWith R p := fun p hp=>hL p (List.mem_cons_of_mem f hp)
    have ht := ih hFt hLt
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,matrixFactorProduct_cons,matrixFactorProduct_cons]
    have he : f x*matrixFactorProduct F x-f y*matrixFactorProduct F y=
        f x*(matrixFactorProduct F x-matrixFactorProduct F y)+(f x-f y)*matrixFactorProduct F y := by noncomm_ring
    rw [he]
    apply (norm_add_le _ _).trans
    apply (add_le_add (frobenius_mul_le_opNorm _ _) (frobenius_mul_le_opNorm_right _ _)).trans
    have hd : ‖matrixFactorProduct F x-matrixFactorProduct F y‖ ≤ ((F.length:ℝ)*(R:ℝ)^F.length)*dist x y := by
      simpa only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow] using ht.dist_le_mul x y
    have hf : ‖f x-f y‖ ≤ (R:ℝ)*dist x y := by
      simpa only [dist_eq_norm] using (hL f List.mem_cons_self).dist_le_mul x y
    have hb := matrixFactorProduct_opNorm F hFt y
    have hp := hF f List.mem_cons_self x
    have h1 := mul_le_mul hp hd (norm_nonneg _) R.coe_nonneg
    have h2 := mul_le_mul hf hb (show 0 ≤ opNorm (matrixFactorProduct F y) from norm_nonneg _) (mul_nonneg R.coe_nonneg dist_nonneg)
    apply (add_le_add h1 h2).trans_eq
    norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow,List.length_cons,Nat.cast_add,Nat.cast_one,NNReal.coe_add,NNReal.coe_one,pow_succ]
    ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixWordIncrement
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
lemma word_opNorm_add (M N : Matrix ι ι ℝ) : opNorm (M+N) ≤ opNorm M+opNorm N := by
  unfold opNorm
  rw [map_add,map_add]
  exact norm_add_le _ _

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_Word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma WordLetter.eval_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (l : WordLetter ι) (hl : l.bounded D) :
    (∀ M,opNorm (l.eval f R hR j a z M) ≤ actualWordBound f R j A D) ∧
    LipschitzWith ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
      (l.eval f R hR j a z) := by
  have hconst := path_constants_nonneg f hR hj hA
  have hD' : D ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have hR' : R ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have h1 : 1 ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have hB : pathBound f R j A ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have hL : pathLip f R j A ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  cases l with
  | diag d =>
    constructor
    · intro M;exact (opNorm_diagonal_le hD hl).trans hD'
    · exact (LipschitzWith.const (diagonal d)).weaken (show (0:NNReal) ≤ _ from zero_le)
  | noise =>
    constructor
    · intro M;exact (realProject_opNorm hR M).trans hR'
    · exact (realProject_lipschitz hR).weaken h1
  | inverse =>
    have hh := pathK_bounds f hR hj hA ha haA hz
    constructor
    · intro M;exact (hh.1 M).trans hB
    · apply LipschitzWith.of_dist_le_mul
      intro M N
      change ‖pathK f R hR j a z M-pathK f R hR j a z N‖ ≤ actualWordBound f R j A D*‖M-N‖
      exact (hh.2 M N).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

theorem actualWord_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) :
    (∀ M,opNorm (actualWord f R hR j a z F M) ≤ (actualWordBound f R j A D)^F.length) ∧
    LipschitzWith ((F.length:NNReal)*⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩^F.length)
      (actualWord f R hR j a z F) := by
  let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
  let G := F.map (WordLetter.eval f R hR j a z)
  have hGb : ∀ p∈G,∀ M,opNorm (p M) ≤ B := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact (l.eval_bounds f hR hj hA hD ha haA hz (hF l hl)).1
  have hGl : ∀ p∈G,LipschitzWith B p := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact (l.eval_bounds f hR hj hA hD ha haA hz (hF l hl)).2
  constructor
  · intro M
    simpa only [G,B,actualWord,List.length_map,NNReal.coe_mk] using! matrixFactorProduct_opNorm G hGb M
  · simpa only [G,B,actualWord,List.length_map] using! (@matrixFactorProduct_lipschitz ι (Matrix ι ι ℝ) _ _ (inferInstance : MetricSpace (Matrix ι ι ℝ)).toPseudoMetricSpace G B hGb hGl)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pathDiagonal_square_all {a : ι→ℝ} (ha : ∀ i,0≤a i) {z : ℝ} (hz : 0≤z) :
    pathDiagonal a z*pathDiagonal a z=z • diagonal a := by
  simp only [pathDiagonal,diagonal_mul_diagonal]
  ext i k
  by_cases h : i=k
  · subst k
    simp only [Matrix.smul_apply,diagonal_apply_eq,smul_eq_mul]
    calc
      (sqrt z*sqrt (a i))*(sqrt z*sqrt (a i)) = (sqrt z*sqrt z)*(sqrt (a i)*sqrt (a i)) := by ring
      _ = z*a i := by rw [mul_self_sqrt hz,mul_self_sqrt (ha i)]
  · simp [h]

lemma realProject_hasDerivAt {R : ℝ} (hR : 0≤R) (M E : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hE : Eᵀ=E) (hMR : opNorm M<R) :
    HasDerivAt (fun t : ℝ=>realProject R hR (M+t • E)) E 0 := by
  have hc : Continuous (fun t : ℝ=>opNorm (M+t • E)) :=
    continuous_realOpNorm.comp (continuous_const.add (continuous_id.smul continuous_const))
  have he : (fun t : ℝ=>realProject R hR (M+t • E)) =ᶠ[𝓝 (0:ℝ)] (fun t=>M+t • E) := by
    have hn : ∀ᶠ t in 𝓝 (0:ℝ),opNorm (M+t • E)<R := hc.continuousAt.eventually (gt_mem_nhds (by simpa using hMR))
    filter_upwards [hn] with t ht
    exact realProject_eq_self hR (M+t • E) (by simp [transpose_smul,hM,hE]) ht.le
  have hh : HasDerivAt (fun t : ℝ=>M+t • E) E 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0:ℝ)).smul_const E).const_add M
  exact hh.congr_of_eventuallyEq he

lemma WordLetter.hasDerivAt [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0<lo)
    (hf : ∀ x∈Icc lo hi,f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0≤R) (j : ℝ)
    {a : ι→ℝ} (ha : ∀ i,0≤a i) {z : ℝ} (hz : 0≤z) (M E : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hE : Eᵀ=E) (hMR : opNorm M<R)
    (hl : lo<ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z)))
    (hu : -hi<ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z)))
    (l : WordLetter ι) : HasDerivAt (fun t : ℝ=>l.eval f R hR j a z (M+t • E))
      (l.direction f R hR j a z M E) 0 := by
  cases l with
  | diag d => exact hasDerivAt_const _ _
  | noise => exact realProject_hasDerivAt hR M E hM hE hMR
  | inverse =>
    have hh := realTruncatedK_derivative f hlo hf hR (pathDiagonal a z)
      (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b)) M E (diagonal_transpose _)
      (diagonal_transpose _) hM hE hMR hl hu
    simpa only [WordLetter.eval,WordLetter.direction,pathK,pathDiagonal_square_all ha hz,Matrix.mul_smul,Matrix.smul_mul] using! hh

theorem actualWord_hasDerivAt [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0<lo)
    (hf : ∀ x∈Icc lo hi,f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0≤R) (j : ℝ)
    {a : ι→ℝ} (ha : ∀ i,0≤a i) {z : ℝ} (hz : 0≤z) (M E : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hE : Eᵀ=E) (hMR : opNorm M<R)
    (hl : lo<ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z)))
    (hu : -hi<ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z)))
    (F : List (WordLetter ι)) : HasDerivAt
      (fun t : ℝ=>actualWord f R hR j a z F (M+t • E)) (actualWordDirection f R hR j a z M E F) 0 := by
  induction F with
  | nil => exact hasDerivAt_const _ _
  | cons l F ih =>
    have hh := (l.hasDerivAt f hlo hf hR j ha hz M E hM hE hMR hl hu).mul ih
    simpa only [actualWord,actualWordDirection,List.map_cons,matrixFactorProduct_cons,zero_smul,add_zero] using! hh
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma word_opNorm_smul (r : ℝ) (M : Matrix ι ι ℝ) : opNorm (r • M)=|r| *opNorm M := by
  unfold opNorm
  rw [map_smul,map_smul,norm_smul,Real.norm_eq_abs]

lemma WordLetter.direction_bound [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (M E : Matrix ι ι ℝ) (l : WordLetter ι) :
    opNorm (l.direction f R hR j a z M E) ≤
      (1+|z| *A*(actualWordBound f R j A D)^2)*opNorm E := by
  have hB := (actualWordBound_pos f hR hj hA hD).le
  have hn : 0≤opNorm E := norm_nonneg _
  have hh : 0≤|z| *A*(actualWordBound f R j A D)^2 := by positivity
  cases l with
  | diag d => simp only [WordLetter.direction,opNorm,map_zero,norm_zero];positivity
  | noise => change opNorm E ≤ _;nlinarith
  | inverse =>
    have hk : opNorm (pathK f R hR j a z M)≤actualWordBound f R j A D :=
      (WordLetter.eval_bounds f hR hj hA hD ha haA hz .inverse trivial).1 M
    have hd := opNorm_diagonal_le hA (fun i=>by rw [abs_of_nonneg (ha i)];exact haA i)
    rw [WordLetter.direction,word_opNorm_smul]
    have hprod : opNorm (pathK f R hR j a z M*diagonal a*E*pathK f R hR j a z M)≤
        actualWordBound f R j A D*A*opNorm E*actualWordBound f R j A D := by
      apply (opNorm_mul _ _).trans
      apply mul_le_mul _ hk (norm_nonneg _) (by positivity)
      apply (opNorm_mul _ _).trans
      apply mul_le_mul_of_nonneg_right _ hn
      exact (opNorm_mul _ _).trans (mul_le_mul hk hd (norm_nonneg _) hB)
    apply (mul_le_mul_of_nonneg_left hprod (abs_nonneg z)).trans
    nlinarith

theorem actualWordDirection_bound [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) (M E : Matrix ι ι ℝ) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    opNorm (actualWordDirection f R hR j a z M E F) ≤
      (1+|z| *A*(B:ℝ)^2)*(wordParameterCoeff B F.length:ℝ)*opNorm E := by
  intro B
  have hB : 0≤(B:ℝ) := B.coe_nonneg
  have hC : 0≤1+|z| *A*(B:ℝ)^2 := by positivity
  have hE : 0≤opNorm E := norm_nonneg _
  induction F with
  | nil => simp [actualWordDirection,wordParameterCoeff,opNorm]
  | cons l F ih =>
    have hFt : ∀ p∈F,p.bounded D := fun p hp=>hF p (List.mem_cons_of_mem l hp)
    have hd := l.direction_bound f hR hj hA hD ha haA hz M E
    have ht := (actualWord_bounds f hR hj hA hD ha haA hz F hFt).1 M
    have hl := (l.eval_bounds f hR hj hA hD ha haA hz (hF l List.mem_cons_self)).1 M
    have hi := ih hFt
    change opNorm (l.direction f R hR j a z M E)≤(1+|z| *A*(B:ℝ)^2)*opNorm E at hd
    change opNorm (actualWord f R hR j a z F M)≤(B:ℝ)^F.length at ht
    change opNorm (l.eval f R hR j a z M)≤(B:ℝ) at hl
    rw [actualWordDirection]
    apply (word_opNorm_add _ _).trans
    apply (add_le_add (opNorm_mul _ _) (opNorm_mul _ _)).trans
    have h1 := mul_le_mul hd ht (norm_nonneg _) (mul_nonneg hC hE)
    have h2 := mul_le_mul hl hi (norm_nonneg _) hB
    apply (add_le_add h1 h2).trans_eq
    simp only [List.length_cons,wordParameterCoeff,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_pow]
    ring

lemma WordLetter.direction_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (E : Matrix ι ι ℝ) (l : WordLetter ι) : Continuous (fun M=>l.direction f R hR j a z M E) := by
  cases l with
  | diag d => exact continuous_const
  | noise => exact continuous_const
  | inverse =>
    have hk := pathK_continuous f hR hj hA ha haA hz
    exact ((hk.matrix_mul continuous_const).matrix_mul continuous_const).matrix_mul hk |>.const_smul z

lemma actualWordDirection_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) (E : Matrix ι ι ℝ) :
    Continuous (fun M=>actualWordDirection f R hR j a z M E F) := by
  induction F with
  | nil => exact continuous_const
  | cons l F ih =>
    have hFt : ∀ p∈F,p.bounded D := fun p hp=>hF p (List.mem_cons_of_mem l hp)
    have hl := (l.eval_bounds f hR hj hA hD ha haA hz (hF l List.mem_cons_self)).2.continuous
    have ht := (actualWord_bounds f hR hj hA hD ha haA hz F hFt).2.continuous
    exact ((l.direction_continuous f hR hj hA ha haA hz E).matrix_mul ht).add (hl.matrix_mul (ih hFt))
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MarkedWordIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma matrix_marked_expand (U W Q : Matrix ι ι ℝ) (i : ι) :
    (U*W*Q) i i=∑ a,∑ b,W a b*(U i a*Q b i) := by
  simp only [Matrix.mul_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _;apply Finset.sum_congr rfl
  intro b _;ring

theorem goe_marked_sum_IBP {r : ℝ} (hr : 0 ≤ r)
    (H : ι→ι→Matrix ι ι ℝ→ℝ) (d : ι→ι→(MatrixCoordinates ι→ℝ)→ℝ)
    {L : NNReal} {C D : ℝ} {s : Set (MatrixCoordinates ι→ℝ)}
    (hL : ∀ a b,LipschitzWith L (fun g=>H a b (goeMatrix r g)))
    (hC : ∀ a b g,‖H a b (goeMatrix r g)‖≤C)
    (hd : ∀ a b,Measurable (d a b)) (hD : ∀ a b g,‖d a b g‖≤D)
    (hs : MeasurableSet s)
    (hder : ∀ a b g,g∈s→HasDerivAt (fun t : ℝ=>H a b (goeMatrix r g+t • symmetricElementary a b)) (d a b g) 0) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1)
    |(∫ g,∑ a,∑ b,goeMatrix r g a b*H a b (goeMatrix r g) ∂μ)-
      r*(∫ g,∑ a,∑ b,d a b g ∂μ)|≤
      (Fintype.card ι:ℝ)^2*(sqrt (2*r)*(L:ℝ)+r*D)*μ.real sᶜ := by
  intro μ
  have hWi (a b : ι) : Integrable (fun g=>goeMatrix r g a b*H a b (goeMatrix r g)) μ := by
    simpa only [mul_comm] using ((goeEntry_memLp r a b).integrable (by norm_num)).bdd_mul
      (hL a b).continuous.aestronglyMeasurable (ae_of_all _ (hC a b))
  have hdi (a b : ι) : Integrable (d a b) μ :=
    (integrable_const D).mono' (hd a b).aestronglyMeasurable (ae_of_all _ (hD a b))
  rw [integral_finsetSum _ (fun a _=>integrable_finsetSum _ (fun b _=>hWi a b)),
    integral_finsetSum _ (fun a _=>integrable_finsetSum _ (fun b _=>hdi a b))]
  simp_rw [integral_finsetSum _ (fun b _=>hWi _ b),integral_finsetSum _ (fun b _=>hdi _ b),
    Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a : ι,∑ b : ι,(sqrt (2*r)*(L:ℝ)+r*D)*μ.real sᶜ := by
      apply Finset.sum_le_sum
      intro a _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun b _=>goe_IBP_error hr a b (hL a b) (hC a b)
        (hd a b) (hD a b) hs (hder a b))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

lemma actualWord_append (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (F G : List (WordLetter ι)) (M : Matrix ι ι ℝ) :
    actualWord f R hR j a z (F++G) M=actualWord f R hR j a z F M*actualWord f R hR j a z G M := by
  simp only [actualWord,matrixFactorProduct,List.map_append,List.prod_append]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_word_contraction (U V Q : Matrix ι ι ℝ) (i : ι) :
    (∑ a,∑ b,U i a*(V*symmetricElementary a b*Q) b i) =
      (U*Q) i i*trace V+(U*Vᵀ*Q) i i := by
  simp_rw [mul_symmetricElementary_mul,mul_add]
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ a,∑ b,U i a*(V b a*Q b i))=(U*Vᵀ*Q) i i := by
    simp only [Matrix.mul_apply,transpose_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _;apply Finset.sum_congr rfl
    intro a _;ring
  have h2 : (∑ a,∑ b,U i a*(V b b*Q a i))=(U*Q) i i*trace V := by
    simp only [Matrix.mul_apply,Matrix.trace,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _;apply Finset.sum_congr rfl
    intro b _;dsimp only [Matrix.diag];ring
  rw [h1,h2,add_comm]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

variable {ι : Type*}

variable [Fintype ι] [DecidableEq ι]

lemma actualWord_nil (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M : Matrix ι ι ℝ) : actualWord f R hR j a z [] M=1 := rfl
lemma actualWord_cons (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M : Matrix ι ι ℝ) (l : WordLetter ι) (F : List (WordLetter ι)) :
    actualWord f R hR j a z (l::F) M=l.eval f R hR j a z M*actualWord f R hR j a z F M := rfl

lemma WordCut.value_prepend (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M E : Matrix ι ι ℝ) (l : WordLetter ι) (c : WordCut ι) :
    (c.prepend l).value f hR j a z M E=l.eval f R hR j a z M*c.value f hR j a z M E := by
  simp only [WordCut.value,WordCut.prepend,actualWord_cons,Matrix.mul_smul,mul_assoc]
  rfl

theorem actualWordDirection_partners (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (M E : Matrix ι ι ℝ) (F : List (WordLetter ι)) :
    actualWordDirection f R hR j a z M E F=
      ((wordPartners a F).map (WordCut.value f hR j a z M E)).sum := by
  induction F with
  | nil => rfl
  | cons l F ih =>
    rw [actualWordDirection,ih]
    rw [wordPartners_cons a l F,List.map_append,List.sum_append]
    have hm : (((wordPartners a F).map (WordCut.prepend l)).map (WordCut.value f hR j a z M E)).sum=
        l.eval f R hR j a z M*((wordPartners a F).map (WordCut.value f hR j a z M E)).sum := by
      simp only [List.map_map,Function.comp_def,WordCut.value_prepend,List.sum_map_mul_left]
    rw [hm]
    congr 1
    cases l with
    | diag d => simp [WordLetter.direction]
    | noise => simp [WordLetter.direction,WordCut.value,actualWord_nil]
    | inverse =>
      simp only [WordLetter.direction,WordCut.value,ite_true,List.map_cons,
        List.map_nil,List.sum_cons,List.sum_nil,add_zero,actualWord_cons,actualWord_nil,
        WordLetter.eval,mul_one,Matrix.smul_mul,mul_assoc]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_MarkedProductIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

lemma scalar_bounded_product_lipschitz {X : Type*} [PseudoMetricSpace X]
    {u v : X→ℝ} {L K B C : NNReal} (hu : LipschitzWith L u) (hv : LipschitzWith K v)
    (hB : ∀ x,‖u x‖≤B) (hC : ∀ x,‖v x‖≤C) :
    LipschitzWith (L*C+B*K) (fun x=>u x*v x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have he : u x*v x-u y*v y=(u x-u y)*v x+u y*(v x-v y) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  have hut := hu.dist_le_mul x y
  have hvt := hv.dist_le_mul x y
  rw [dist_eq_norm] at hut hvt
  have hh := mul_le_mul hut (hC x) (norm_nonneg _) (mul_nonneg L.coe_nonneg dist_nonneg)
  have hh' := mul_le_mul (hB y) hvt (norm_nonneg _) B.coe_nonneg
  apply (add_le_add hh hh').trans_eq
  simp only [NNReal.coe_add,NNReal.coe_mul]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem goe_marked_product_IBP {r : ℝ} (hr : 0 ≤ r)
    (U Q : Matrix ι ι ℝ→Matrix ι ι ℝ)
    (DU DQ : ι→ι→Matrix ι ι ℝ→Matrix ι ι ℝ)
    {L K B C : NNReal} {D E : ℝ}
    (hU : LipschitzWith L U) (hQ : LipschitzWith K Q)
    (hB : ∀ M,opNorm (U M)≤B) (hC : ∀ M,opNorm (Q M)≤C)
    (hDU : ∀ a b,Continuous (DU a b)) (hDQ : ∀ a b,Continuous (DQ a b))
    (hD : ∀ a b M,opNorm (DU a b M)≤D) (hE : ∀ a b M,opNorm (DQ a b M)≤E)
    {s : Set (MatrixCoordinates ι→ℝ)} (hs : MeasurableSet s)
    (hUd : ∀ a b g,g∈s→HasDerivAt (fun t : ℝ=>U (goeMatrix r g+t • symmetricElementary a b)) (DU a b (goeMatrix r g)) 0)
    (hQd : ∀ a b g,g∈s→HasDerivAt (fun t : ℝ=>Q (goeMatrix r g+t • symmetricElementary a b)) (DQ a b (goeMatrix r g)) 0)
    (i : ι) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1)
    |(∫ g,(U (goeMatrix r g)*goeMatrix r g*Q (goeMatrix r g)) i i ∂μ)-
      r*(∫ g,∑ a,∑ b,(DU a b (goeMatrix r g) i a*Q (goeMatrix r g) b i+
        U (goeMatrix r g) i a*DQ a b (goeMatrix r g) b i) ∂μ)|≤
      (Fintype.card ι:ℝ)^2*(sqrt (2*r)*((L*C+B*K:NNReal)*(⟨sqrt (2*r),sqrt_nonneg _⟩*(Fintype.card (MatrixCoordinates ι):NNReal)^(1/(2:ℝ≥0∞)).toReal):NNReal)+
        r*(D*C+B*E))*μ.real sᶜ := by
  intro μ
  let H := fun a b M=>(U M) i a*(Q M) b i
  let d := fun a b g=>(DU a b (goeMatrix r g)) i a*(Q (goeMatrix r g)) b i+
    (U (goeMatrix r g)) i a*(DQ a b (goeMatrix r g)) b i
  have hG := (goeMatrix_pi_lipschitz (ι:=ι) r)
  have hu (a : ι) : LipschitzWith L (fun M=>(U M) i a) := by
    simpa only [one_mul,Function.comp_def] using! (matrixEntry_lipschitz i a).comp hU
  have hq (b : ι) : LipschitzWith K (fun M=>(Q M) b i) := by
    simpa only [one_mul,Function.comp_def] using! (matrixEntry_lipschitz b i).comp hQ
  have hub (M : Matrix ι ι ℝ) (a : ι) : ‖(U M) i a‖≤(B:ℝ) :=
    (matrix_entry_le_opNorm _ i a).trans (hB M)
  have hqb (M : Matrix ι ι ℝ) (b : ι) : ‖(Q M) b i‖≤(C:ℝ) :=
    (matrix_entry_le_opNorm _ b i).trans (hC M)
  have hdh (a b : ι) : Measurable (d a b) := by
    exact (((hDU a b).comp hG.continuous).matrix_elem i a |>.mul ((hQ.continuous.comp hG.continuous).matrix_elem b i) |>.add
      (((hU.continuous.comp hG.continuous).matrix_elem i a).mul (((hDQ a b).comp hG.continuous).matrix_elem b i))).measurable
  have hdb (a b : ι) (g : MatrixCoordinates ι→ℝ) : ‖d a b g‖≤D*C+B*E := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    exact add_le_add (mul_le_mul ((matrix_entry_le_opNorm _ i a).trans (hD a b _)) (hqb _ b) (norm_nonneg _)
      (le_trans (show 0≤opNorm (DU a b (goeMatrix r g)) from norm_nonneg _) (hD a b _)))
      (mul_le_mul (hub _ a) ((matrix_entry_le_opNorm _ b i).trans (hE a b _)) (norm_nonneg _) B.coe_nonneg)
  have hh := goe_marked_sum_IBP hr H d
    (fun a b=>(scalar_bounded_product_lipschitz (hu a) (hq b) (fun M=>hub M a) (fun M=>hqb M b)).comp hG)
    (C:=(B:ℝ)*C) (fun a b g=>by rw [norm_mul];exact mul_le_mul (hub _ a) (hqb _ b) (norm_nonneg _) B.coe_nonneg)
    hdh hdb hs (fun a b g hg=>by
      have ha := matrixEntry_derivative (hUd a b g hg) i a
      have hb := matrixEntry_derivative (hQd a b g hg) b i
      simpa only [H,d,zero_smul,add_zero] using! ha.fun_mul hb)
  simpa only [H,d,← matrix_marked_expand,μ] using! hh
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma marked_entry_bound (U W Q : Matrix ι ι ℝ) {B C : ℝ} (hB : 0≤B) ( _hC : 0≤C)
    (hU : opNorm U≤B) (hQ : opNorm Q≤C) (i : ι) :
    |(U*W*Q) i i|≤B*C*(∑ a,∑ b,|W a b|) := by
  rw [matrix_marked_expand]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [abs_mul,abs_mul]
  have hh := mul_le_mul ((matrix_entry_le_opNorm _ i a).trans hU)
    ((matrix_entry_le_opNorm _ b i).trans hQ) (abs_nonneg _) hB
  nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (W a b))]

theorem projected_marked_expectation_error {r R B C : ℝ} (hr : 0 ≤ r) (hR : 0≤R)
    (hB : 0≤B) (hC : 0≤C) (U Q : Matrix ι ι ℝ→Matrix ι ι ℝ)
    (hU : Continuous U) (hQ : Continuous Q) (hUb : ∀ M,opNorm (U M)≤B) (hQb : ∀ M,opNorm (Q M)≤C)
    {s : Set (MatrixCoordinates ι→ℝ)} (hs : MeasurableSet s)
    (hgood : ∀ g∈s,opNorm (goeMatrix r g)≤R) (i : ι) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1)
    |(∫ g,(U (goeMatrix r g)*realProject R hR (goeMatrix r g)*Q (goeMatrix r g)) i i ∂μ)-
      (∫ g,(U (goeMatrix r g)*goeMatrix r g*Q (goeMatrix r g)) i i ∂μ)|≤
      B*R*C*μ.real sᶜ+B*C*(Fintype.card ι:ℝ)^2*sqrt (2*r)*sqrt (μ.real sᶜ) := by
  intro μ
  let W := goeMatrix (ι:=ι) r
  have hWc := (goeMatrix_pi_lipschitz (ι:=ι) r).continuous
  have hUc := hU.comp hWc
  have hQc := hQ.comp hWc
  have hPc := (realProject_lipschitz hR).continuous.comp hWc
  have hpb (g : MatrixCoordinates ι→ℝ) : ‖(U (W g)*realProject R hR (W g)*Q (W g)) i i‖≤B*R*C := by
    exact (matrix_entry_le_opNorm _ i i).trans ((opNorm_mul _ _).trans
      (mul_le_mul ((opNorm_mul _ _).trans (mul_le_mul (hUb _) (realProject_opNorm hR _) (norm_nonneg _) hB))
        (hQb _) (norm_nonneg _) (mul_nonneg hB hR)))
  have hpi : Integrable (fun g=>(U (W g)*realProject R hR (W g)*Q (W g)) i i) μ :=
    (integrable_const (B*R*C)).mono' (((hUc.matrix_mul hPc).matrix_mul hQc).matrix_elem i i).aestronglyMeasurable (ae_of_all _ hpb)
  have hwa (a b : ι) : Integrable (fun g=>|W g a b|) μ := by
    exact ((goeEntry_memLp r a b).integrable (by norm_num)).norm
  have hwai : Integrable (fun g=>∑ a,∑ b,|W g a b|) μ :=
    integrable_finsetSum _ (fun a _=>integrable_finsetSum _ (fun b _=>hwa a b))
  have hwb (g : MatrixCoordinates ι→ℝ) : ‖(U (W g)*W g*Q (W g)) i i‖≤B*C*(∑ a,∑ b,|W g a b|) :=
    marked_entry_bound _ _ _ hB hC (hUb _) (hQb _) i
  have hwi : Integrable (fun g=>(U (W g)*W g*Q (W g)) i i) μ :=
    (hwai.const_mul (B*C)).mono' (((hUc.matrix_mul hWc).matrix_mul hQc).matrix_elem i i).aestronglyMeasurable (ae_of_all _ hwb)
  have herr := integral_exceptional_equal_bound hs.compl hpi hwi
    ((integrable_const (B*R*C)).add (hwai.const_mul (B*C)))
    (fun g hg=>by rw [realProject_eq_self hR _ (goeMatrix_transpose r g) (hgood g (by simpa using hg))])
    (fun g _=>(norm_sub_le _ _).trans (add_le_add (hpb g) (hwb g)))
  apply herr.trans
  have hwas (a b : ι) : Integrable (fun g=>|W g a b|) (μ.restrict sᶜ) := (hwa a b).mono_measure Measure.restrict_le_self
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const _) ((hwai.const_mul (B*C)).mono_measure Measure.restrict_le_self),integral_const,integral_const_mul]
  rw [integral_finsetSum _ (fun a _=>integrable_finsetSum _ (fun b _=>hwas a b))]
  simp_rw [integral_finsetSum _ (fun b _=>hwas _ b)]
  have hbad (a b : ι) : (∫ g in sᶜ,|W g a b| ∂μ)≤ sqrt (2*r)*sqrt (μ.real sᶜ) :=
    (integral_abs_on_set_le (goeEntry_memLp r a b) hs.compl).trans
      (mul_le_mul_of_nonneg_right (sqrt_le_sqrt (goeEntry_integral_sq_le hr a b)) (sqrt_nonneg _))
  simp only [measureReal_restrict_apply_univ,smul_eq_mul]
  calc
    _ ≤ μ.real sᶜ*(B*R*C)+B*C*(∑ a : ι,∑ b : ι,sqrt (2*r)*sqrt (μ.real sᶜ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hbad a b))) (mul_nonneg hB hC))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ProjectedMarkedIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem projected_marked_product_IBP {r R : ℝ} (hr : 0 ≤ r) (hR : 0≤R)
    (U Q : Matrix ι ι ℝ→Matrix ι ι ℝ)
    (DU DQ : ι→ι→Matrix ι ι ℝ→Matrix ι ι ℝ)
    {L K B C : NNReal} {D E : ℝ}
    (hU : LipschitzWith L U) (hQ : LipschitzWith K Q)
    (hB : ∀ M,opNorm (U M)≤B) (hC : ∀ M,opNorm (Q M)≤C)
    (hDU : ∀ a b,Continuous (DU a b)) (hDQ : ∀ a b,Continuous (DQ a b))
    (hD : ∀ a b M,opNorm (DU a b M)≤D) (hE : ∀ a b M,opNorm (DQ a b M)≤E)
    {s : Set (MatrixCoordinates ι→ℝ)} (hs : MeasurableSet s)
    (hgood : ∀ g∈s,opNorm (goeMatrix r g)≤R)
    (hUd : ∀ a b g,g∈s→HasDerivAt (fun t : ℝ=>U (goeMatrix r g+t • symmetricElementary a b)) (DU a b (goeMatrix r g)) 0)
    (hQd : ∀ a b g,g∈s→HasDerivAt (fun t : ℝ=>Q (goeMatrix r g+t • symmetricElementary a b)) (DQ a b (goeMatrix r g)) 0)
    (i : ι) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1)
    |(∫ g,(U (goeMatrix r g)*realProject R hR (goeMatrix r g)*Q (goeMatrix r g)) i i ∂μ)-
      r*(∫ g,∑ a,∑ b,(DU a b (goeMatrix r g) i a*Q (goeMatrix r g) b i+
        U (goeMatrix r g) i a*DQ a b (goeMatrix r g) b i) ∂μ)|≤
      markedError (ι:=ι) r R L K B C D E (μ.real sᶜ) := by
  intro μ
  have h1 := projected_marked_expectation_error hr hR B.coe_nonneg C.coe_nonneg U Q
    hU.continuous hQ.continuous hB hC hs hgood i
  have h2 := goe_marked_product_IBP hr U Q DU DQ hU hQ hB hC hDU hDQ hD hE hs hUd hQd i
  exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordPartnerContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_word_contraction_left (U V Q : Matrix ι ι ℝ) (i : ι) :
    (∑ a,∑ b,(U*symmetricElementary a b*V) i a*Q b i)=
      (U*Q) i i*trace V+(U*Vᵀ*Q) i i := by
  simp_rw [mul_symmetricElementary_mul,add_mul]
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ a,∑ b,(U i a*V b a)*Q b i)=(U*Vᵀ*Q) i i := by
    simp only [Matrix.mul_apply,transpose_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
  have h2 : (∑ a,∑ b,(U i b*V a a)*Q b i)=(U*Q) i i*trace V := by
    simp only [Matrix.mul_apply,Matrix.trace,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _;apply Finset.sum_congr rfl
    intro b _;dsimp only [Matrix.diag];ring
  rw [h1,h2,add_comm]

lemma WordCut.leftContraction_eq (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M Q : Matrix ι ι ℝ) (i : ι) (c : WordCut ι) :
    (∑ u,∑ v,(c.value f hR j a z M (symmetricElementary u v)) i u*Q v i)=
      c.leftContraction f hR j a z M Q i := by
  have hh : (∑ u,∑ v,(c.value f hR j a z M (symmetricElementary u v)) i u*Q v i)=
      (if c.inversePartner then z else 1)*(∑ u,∑ v,
        (actualWord f R hR j a z c.left M*symmetricElementary u v*
          actualWord f R hR j a z c.right M) i u*Q v i) := by
    simp only [WordCut.value,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _;apply Finset.sum_congr rfl
    intro v _;ring
  rw [hh,matrix_word_contraction_left]
  rfl

lemma WordCut.rightContraction_eq (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M U : Matrix ι ι ℝ) (i : ι) (c : WordCut ι) :
    (∑ u,∑ v,U i u*(c.value f hR j a z M (symmetricElementary u v)) v i)=
      c.rightContraction f hR j a z M U i := by
  have hh : (∑ u,∑ v,U i u*(c.value f hR j a z M (symmetricElementary u v)) v i)=
      (if c.inversePartner then z else 1)*(∑ u,∑ v,
        U i u*(actualWord f R hR j a z c.left M*symmetricElementary u v*
          actualWord f R hR j a z c.right M) v i) := by
    simp only [WordCut.value,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _;apply Finset.sum_congr rfl
    intro v _;ring
  rw [hh,matrix_word_contraction]
  rfl

lemma partnerList_leftContract (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M Q : Matrix ι ι ℝ) (i : ι) (C : List (WordCut ι)) :
    (∑ u,∑ v,((C.map (WordCut.value f hR j a z M (symmetricElementary u v))).sum) i u*Q v i)=
      (C.map (WordCut.leftContraction f hR j a z M Q i)).sum := by
  induction C with
  | nil => simp
  | cons c C ih =>
    simp only [List.map_cons,List.sum_cons,Matrix.add_apply,add_mul,Finset.sum_add_distrib]
    rw [WordCut.leftContraction_eq,ih]

lemma partnerList_rightContract (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M U : Matrix ι ι ℝ) (i : ι) (C : List (WordCut ι)) :
    (∑ u,∑ v,U i u*((C.map (WordCut.value f hR j a z M (symmetricElementary u v))).sum) v i)=
      (C.map (WordCut.rightContraction f hR j a z M U i)).sum := by
  induction C with
  | nil => simp
  | cons c C ih =>
    simp only [List.map_cons,List.sum_cons,Matrix.add_apply,mul_add,Finset.sum_add_distrib]
    rw [WordCut.rightContraction_eq,ih]

theorem actualWord_partner_contractions (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (M : Matrix ι ι ℝ) (P Q : List (WordLetter ι)) (i : ι) :
    (∑ u,∑ v,((actualWordDirection f R hR j a z M (symmetricElementary u v) P) i u*
      actualWord f R hR j a z Q M v i+actualWord f R hR j a z P M i u*
        (actualWordDirection f R hR j a z M (symmetricElementary u v) Q) v i))=
    ((wordPartners a P).map (WordCut.leftContraction f hR j a z M (actualWord f R hR j a z Q M) i)).sum+
    ((wordPartners a Q).map (WordCut.rightContraction f hR j a z M (actualWord f R hR j a z P M) i)).sum := by
  simp only [Finset.sum_add_distrib,actualWordDirection_partners,partnerList_leftContract,partnerList_rightContract]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actualWord_elementary_bound [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) (M : Matrix ι ι ℝ) (u v : ι) :
    opNorm (actualWordDirection f R hR j a z M (symmetricElementary u v) F)≤
      wordDifferentialBound ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩ A z F.length := by
  apply (actualWordDirection_bound f hR hj hA hD ha haA hz F hF M (symmetricElementary u v)).trans
  apply mul_le_mul_of_nonneg_left ((operator_le_frobenius _).trans (symmetricElementary_norm_le u v))
  positivity

theorem actualWord_loop_oai [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0<lo)
    (hf : ∀ x∈Icc lo hi,f x=(x:ℂ)⁻¹) {R j A D z r : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) (hr : 0 ≤ r) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (P Q : List (WordLetter ι)) (hP : ∀ l∈P,l.bounded D) (hQ : ∀ l∈Q,l.bounded D) (i : ι) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let μ := Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1)
    let s := truncationGoodSet r R lo hi (pathDiagonal a z) (pathShift z ((j/(Fintype.card ι:ℝ))*∑ k,a k))
    |(∫ g,actualWord f R hR j a z (P++(.noise::Q)) (goeMatrix r g) i i ∂μ)-
      r*(∫ g,actualWordLoop f hR j a z P Q (goeMatrix r g) i ∂μ)|≤
      markedError (ι:=ι) r R ((P.length:NNReal)*B^P.length) ((Q.length:NNReal)*B^Q.length)
        (B^P.length) (B^Q.length) (wordDifferentialBound B A z P.length)
          (wordDifferentialBound B A z Q.length) (μ.real sᶜ) := by
  intro B μ s
  let U := actualWord f R hR j a z P
  let V := actualWord f R hR j a z Q
  let DU := fun u v M=>actualWordDirection f R hR j a z M (symmetricElementary u v) P
  let DV := fun u v M=>actualWordDirection f R hR j a z M (symmetricElementary u v) Q
  have hu := actualWord_bounds f hR hj hA hD ha haA hz P hP
  have hv := actualWord_bounds f hR hj hA hD ha haA hz Q hQ
  have hu' : ∀ M,opNorm (U M)≤(B^P.length:NNReal) := by simpa only [B,NNReal.coe_pow,NNReal.coe_mk] using! hu.1
  have hv' : ∀ M,opNorm (V M)≤(B^Q.length:NNReal) := by simpa only [B,NNReal.coe_pow,NNReal.coe_mk] using! hv.1
  have hdu (u v : ι) : Continuous (DU u v) := actualWordDirection_continuous f hR hj hA hD ha haA hz P hP _
  have hdv (u v : ι) : Continuous (DV u v) := actualWordDirection_continuous f hR hj hA hD ha haA hz Q hQ _
  have hdub (u v : ι) (M : Matrix ι ι ℝ) : opNorm (DU u v M)≤wordDifferentialBound B A z P.length :=
    actualWord_elementary_bound f hR hj hA hD ha haA hz P hP M u v
  have hdvb (u v : ι) (M : Matrix ι ι ℝ) : opNorm (DV u v M)≤wordDifferentialBound B A z Q.length :=
    actualWord_elementary_bound f hR hj hA hD ha haA hz Q hQ M u v
  have hpd (F : List (WordLetter ι)) (u v : ι) (g : MatrixCoordinates ι→ℝ) (hg : g∈s) :
      HasDerivAt (fun t : ℝ=>actualWord f R hR j a z F (goeMatrix r g+t • symmetricElementary u v))
        (actualWordDirection f R hR j a z (goeMatrix r g) (symmetricElementary u v) F) 0 :=
    actualWord_hasDerivAt f hlo hf hR j ha hz.1 _ _ (goeMatrix_transpose _ _) (symmetricElementary_transpose _ _)
      hg.1 hg.2.1 hg.2.2 F
  have hh := projected_marked_product_IBP hr hR U V DU DV hu.2 hv.2 hu' hv' hdu hdv hdub hdvb
    (truncationGoodSet_measurable r R lo hi _ _) (fun g (hg : g∈s)=>hg.1.le) (hpd P) (hpd Q) i
  simpa only [U,V,DU,DV,actualWord_append,actualWord_cons,WordLetter.eval,mul_assoc,
    actualWord_partner_contractions,actualWordLoop] using! hh
end SKGap
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SKGap.actualWord_loop_oai.{u_1} := @OAI.SKGap.actualWord_loop_oai.{u_1}
