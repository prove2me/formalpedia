-- Prove2me | solution 1 for OAI.SKRatio.Bins.random_binForm_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:19:04.704989+00:00
-- url     : https://prove2.me/submissions/c45ced4a-b4f1-4eb7-88ef-68524a1cb60a

import Mathlib
import Definitions.Def_OAIQ024S008
import Definitions.Def_OAIQ024S010

section
-- module Solutions.OAIQ024_SK.Compat
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_StandardGaussianProduct
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instIsProbabilityMeasureForallFinRealStandardGaussianProduct_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKRatioGaussian

theorem hasDerivAt_gaussianPDFReal (d : ℝ) {s : ℝ≥0} (hs : s ≠ 0) (y : ℝ) :
    HasDerivAt (gaussianPDFReal d s)
      (-(y - d) / (s : ℝ) * gaussianPDFReal d s y) y := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  unfold gaussianPDFReal
  convert! (((((hasDerivAt_id y).sub_const d).pow 2).neg.div_const
    (2 * (s : ℝ))).exp).const_mul (1 / sqrt (2 * π * (s : ℝ))) using 1
  · ext x
    simp only [one_div, Pi.neg_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
    norm_num
    ring

theorem integrable_gaussian_iff {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0) {f : ℝ → ℝ} :
    Integrable f (gaussianReal d s) ↔ Integrable (fun y => gaussianPDFReal d s y * f y) := by
  rw [gaussianReal_of_var_ne_zero d hs,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF d s)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF, smul_eq_mul]

theorem gaussian_integration_by_parts {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0)
    {f f' : ℝ → ℝ} (hd : ∀ y, HasDerivAt f (f' y) y)
    (hf : Integrable f (gaussianReal d s)) (hf' : Integrable f' (gaussianReal d s))
    (hyf : Integrable (fun y => (y - d) * f y) (gaussianReal d s)) :
    (∫ y, (y - d) * f y ∂gaussianReal d s) =
      (s : ℝ) * (∫ y, f' y ∂gaussianReal d s) := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hfg := (integrable_gaussian_iff hs).mp hf
  have hf'g := (integrable_gaussian_iff hs).mp hf'
  have hyfg := (integrable_gaussian_iff hs).mp hyf
  have hder (y : ℝ) : HasDerivAt (fun y => gaussianPDFReal d s y * f y)
      (gaussianPDFReal d s y * f' y -
        (gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ)) y := by
    convert! (hasDerivAt_gaussianPDFReal d hs y).mul (hd y) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hii : Integrable (fun y => gaussianPDFReal d s y * f' y -
      (gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ)) :=
    hf'g.sub (hyfg.div_const _)
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hder hii hfg
  rw [integral_sub hf'g (hyfg.div_const (s : ℝ)), integral_div] at hz
  rw [integral_gaussianReal_eq_integral_smul hs,
    integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  have he : (∫ y, gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ) =
      ∫ y, gaussianPDFReal d s y * f' y := by linarith
  have hm := (div_eq_iff hsp.ne').mp he
  nlinarith only [hm]

theorem continuous_insertNth {n : ℕ} (i : Fin (n + 1)) (u : Fin n → ℝ) :
    Continuous (fun z : ℝ => i.insertNth (α := fun _ => ℝ) z u) := by
  apply continuous_pi
  refine i.forall_iff_succAbove.mpr ⟨?_, ?_⟩
  · simp only [Fin.insertNth_apply_same]
    convert! (continuous_id : Continuous (fun x : ℝ => x)) using 1
  · intro k
    simpa only [Fin.insertNth_apply_succAbove] using
      (continuous_const : Continuous (fun _ : ℝ => u k))

theorem gaussianProduct_coordinate_IBP {n : ℕ} (i : Fin (n + 1))
    {f df : (Fin (n + 1) → ℝ) → ℝ} {C D : ℝ}
    (hf : Continuous f) (hdf : Continuous df)
    (hfbound : ∀ x, ‖f x‖ ≤ C) (hdfbound : ∀ x, ‖df x‖ ≤ D)
    (hder : ∀ (u : Fin n → ℝ) (z : ℝ),
      HasDerivAt (fun z => f (i.insertNth z u)) (df (i.insertNth z u)) z) :
    (∫ x, x i * f x ∂standardGaussianProduct (n + 1)) =
      ∫ x, df x ∂standardGaussianProduct (n + 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hp : MeasurePreserving e.symm
      ((gaussianReal 0 1).prod (standardGaussianProduct n))
      (standardGaussianProduct (n + 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) i).symm
  have hi : Integrable (fun x : Fin (n + 1) → ℝ => x i * f x)
      (standardGaussianProduct (n + 1)) := by
    simpa only [mul_comm, standardGaussianProduct] using
      (integrable_eval (i := i) IsGaussian.integrable_id).bdd_mul
        hf.aestronglyMeasurable (ae_of_all _ hfbound)
  have hi' : Integrable df (standardGaussianProduct (n + 1)) :=
    Integrable.of_bound hdf.aestronglyMeasurable D (ae_of_all _ hdfbound)
  have hsplit (g : (Fin (n + 1) → ℝ) → ℝ)
      (hg : Integrable g (standardGaussianProduct (n + 1))) :
      (∫ x, g x ∂standardGaussianProduct (n + 1)) =
        ∫ u, ∫ z, g (i.insertNth z u) ∂gaussianReal 0 1 ∂standardGaussianProduct n := by
    have hi2 : Integrable (fun x => g (e.symm x))
        ((gaussianReal 0 1).prod (standardGaussianProduct n)) :=
      hp.integrable_comp_of_integrable hg
    rw [← hp.integral_comp' g, integral_prod _ hi2]
    rw [integral_integral_swap hi2]
    rfl
  rw [hsplit _ hi, hsplit _ hi']
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [Fin.insertNth_apply_same]
  have hfu : Integrable (fun z => f (i.insertNth z u)) (gaussianReal 0 1) :=
    Integrable.of_bound (hf.comp (continuous_insertNth i u)).aestronglyMeasurable C
      (ae_of_all _ (fun z => hfbound _))
  have hdfu : Integrable (fun z => df (i.insertNth z u)) (gaussianReal 0 1) :=
    Integrable.of_bound (hdf.comp (continuous_insertNth i u)).aestronglyMeasurable D
      (ae_of_all _ (fun z => hdfbound _))
  have hzfu : Integrable (fun z => z * f (i.insertNth z u)) (gaussianReal 0 1) := by
    simpa only [mul_comm, id_eq, Function.comp_def] using (IsGaussian.integrable_id (μ := gaussianReal 0 1)).bdd_mul
      (hf.comp (continuous_insertNth i u)).aestronglyMeasurable
      (ae_of_all _ (fun z => hfbound _))
  simpa only [NNReal.coe_one, sub_zero, one_mul] using
    gaussian_integration_by_parts (d := 0) (s := 1) one_ne_zero (hder u) hfu hdfu
      (by simpa only [sub_zero] using hzfu)

end SKRatioGaussian

open Filter
open scoped Topology

end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_ExpSum
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
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
namespace SKRatioGaussian

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem expSum_pos (κ : ℝ) (x : ι → ℝ) : 0 < expSum κ x := by
  exact Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty

theorem softWeight_pos (κ : ℝ) (x : ι → ℝ) (i : ι) : 0 < softWeight κ x i :=
  div_pos (exp_pos _) (expSum_pos κ x)

theorem sum_softWeight (κ : ℝ) (x : ι → ℝ) : ∑ i, softWeight κ x i = 1 := by
  simp only [softWeight, ← Finset.sum_div]
  exact div_self (expSum_pos κ x).ne'

theorem softWeight_le_one (κ : ℝ) (x : ι → ℝ) (i : ι) : softWeight κ x i ≤ 1 := by
  rw [← sum_softWeight κ x]
  exact Finset.single_le_sum (fun j _ => (softWeight_pos κ x j).le) (Finset.mem_univ i)

theorem continuous_softWeight (κ : ℝ) (i : ι) : Continuous (fun x : ι → ℝ => softWeight κ x i) := by
  apply Continuous.div
  · exact continuous_exp.comp (continuous_const.mul (continuous_apply i))
  · exact continuous_finsetSum _ (fun j _ => continuous_exp.comp (continuous_const.mul (continuous_apply j)))
  · exact fun x => (expSum_pos κ x).ne'

theorem continuous_smoothMax (κ : ℝ) : Continuous (smoothMax κ : (ι → ℝ) → ℝ) := by
  apply Continuous.div_const
  exact (continuous_finsetSum _ (fun j _ => continuous_exp.comp (continuous_const.mul (continuous_apply j)))).log
    (fun x => (expSum_pos κ x).ne')

omit [Nonempty ι] in
theorem hasDerivAt_expSum {κ t : ℝ} {f : ι → ℝ → ℝ} {df : ι → ℝ}
    (hf : ∀ i, HasDerivAt (f i) (df i) t) :
    HasDerivAt (fun s => expSum κ (fun i => f i s))
      (∑ i, Real.exp (κ * f i t) * (κ * df i)) t := by
  convert! HasDerivAt.fun_sum (fun i _ => ((hf i).const_mul κ).exp) using 1
  all_goals try with_reducible_and_instances rfl

theorem hasDerivAt_smoothMax {κ t : ℝ} (hκ : κ ≠ 0) {f : ι → ℝ → ℝ} {df : ι → ℝ}
    (hf : ∀ i, HasDerivAt (f i) (df i) t) :
    HasDerivAt (fun s => smoothMax κ (fun i => f i s))
      (∑ i, softWeight κ (fun j => f j t) i * df i) t := by
  convert! ((hasDerivAt_expSum hf).log (expSum_pos κ (fun j => f j t)).ne').div_const κ using 1
  all_goals try with_reducible_and_instances rfl
  simp only [softWeight]
  have hs : (∑ i, Real.exp (κ * f i t) * (κ * df i)) =
      κ * ∑ i, Real.exp (κ * f i t) * df i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp [hκ, (expSum_pos κ (fun j => f j t)).ne']

theorem hasDerivAt_softWeight {κ t : ℝ} {f : ι → ℝ → ℝ} {df : ι → ℝ}
    (hf : ∀ i, HasDerivAt (f i) (df i) t) (i : ι) :
    HasDerivAt (fun s => softWeight κ (fun j => f j s) i)
      (κ * softWeight κ (fun j => f j t) i *
        (df i - ∑ j, softWeight κ (fun k => f k t) j * df j)) t := by
  convert! (((hf i).const_mul κ).exp).div (hasDerivAt_expSum hf)
    (expSum_pos κ (fun j => f j t)).ne' using 1
  all_goals try with_reducible_and_instances rfl
  simp only [softWeight]
  have hs : (∑ j, Real.exp (κ * f j t) * (κ * df j)) =
      κ * ∑ j, Real.exp (κ * f j t) * df j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp [(expSum_pos κ (fun j => f j t)).ne']

theorem weighted_abs_le (κ : ℝ) (x v : ι → ℝ) :
    |∑ i, softWeight κ x i * v i| ≤ ∑ i, |v i| := by
  calc
    _ ≤ ∑ i, |softWeight κ x i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |v i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_pos (softWeight_pos κ x i)]
      exact mul_le_of_le_one_left (abs_nonneg _) (softWeight_le_one κ x i)

omit [Nonempty ι] in
theorem smoothMax_ge {κ : ℝ} (hκ : 0 < κ) (x : ι → ℝ) (i : ι) :
    x i ≤ smoothMax κ x := by
  rw [smoothMax, le_div_iff₀ hκ]
  calc
    x i * κ = log (Real.exp (κ * x i)) := by rw [log_exp]; ring
    _ ≤ log (expSum κ x) := log_le_log (exp_pos _) <|
      Finset.single_le_sum (fun j _ => (exp_pos (κ * x j)).le) (Finset.mem_univ i)

theorem smoothMax_le {κ : ℝ} (hκ : 0 < κ) (x : ι → ℝ) {b : ℝ}
    (hb : ∀ i, x i ≤ b) : smoothMax κ x ≤ b + log (Fintype.card ι) / κ := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [smoothMax, div_le_iff₀ hκ]
  calc
    log (expSum κ x) ≤ log ((Fintype.card ι : ℝ) * Real.exp (κ * b)) := by
      apply log_le_log (expSum_pos _ _)
      calc
        _ ≤ ∑ _ : ι, Real.exp (κ * b) := Finset.sum_le_sum (fun i _ => exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hb i) hκ.le))
        _ = _ := by simp
    _ = _ := by rw [log_mul hn.ne' (exp_pos _).ne', log_exp]; field_simp; ring

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Fintype ι] [Nonempty ι] in
theorem continuous_affineProcess {n : ℕ} (m : ι → ℝ) (a : ι → Fin n → ℝ) :
    Continuous (affineProcess m a) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_apply k)))

omit [Fintype ι] [Nonempty ι] in
theorem affineProcess_coordinate_hasDerivAt {n : ℕ} (m : ι → ℝ)
    (a : ι → Fin (n + 1) → ℝ) (i : ι) (k : Fin (n + 1)) (u : Fin n → ℝ) (z : ℝ) :
    HasDerivAt (fun z => affineProcess m a (k.insertNth z u) i) (a i k) z := by
  have he (z : ℝ) : affineProcess m a (k.insertNth z u) i =
      a i k * z + (m i + ∑ l, a i (k.succAbove l) * u l) := by
    rw [affineProcess, Fin.sum_univ_succAbove _ k]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    ring
  simp_rw [he]
  convert! ((hasDerivAt_id z).const_mul (a i k)).add_const (m i + ∑ l, a i (k.succAbove l) * u l) using 1
  all_goals try with_reducible_and_instances rfl
  simp

theorem affine_softWeight_coordinate_IBP {n : ℕ} (κ : ℝ) (m : ι → ℝ)
    (a : ι → Fin (n + 1) → ℝ) (i : ι) (k : Fin (n + 1)) :
    (∫ z, z k * softWeight κ (affineProcess m a z) i ∂standardGaussianProduct (n + 1)) =
      ∫ z, κ * softWeight κ (affineProcess m a z) i *
        (a i k - ∑ j, softWeight κ (affineProcess m a z) j * a j k)
        ∂standardGaussianProduct (n + 1) := by
  apply gaussianProduct_coordinate_IBP (C := 1) (D := |κ| * (|a i k| + ∑ j, |a j k|)) k
  · exact (continuous_softWeight κ i).comp (continuous_affineProcess m a)
  · exact (continuous_const.mul ((continuous_softWeight κ i).comp (continuous_affineProcess m a))).mul
      (continuous_const.sub (continuous_finsetSum _ (fun j _ =>
        ((continuous_softWeight κ j).comp (continuous_affineProcess m a)).mul continuous_const)))
  · intro z
    rw [Real.norm_eq_abs, abs_of_pos (softWeight_pos _ _ _)]
    exact softWeight_le_one _ _ _
  · intro z
    rw [norm_mul, norm_mul, Real.norm_eq_abs κ,
      Real.norm_eq_abs (softWeight _ _ _), abs_of_pos (softWeight_pos _ _ _), Real.norm_eq_abs]
    apply mul_le_mul
    · exact mul_le_of_le_one_right (abs_nonneg κ) (softWeight_le_one _ _ _)
    · exact (abs_sub _ _).trans (add_le_add_right (weighted_abs_le κ _ (fun j => a j k)) _)
    · positivity
    · positivity
  · intro u z
    exact hasDerivAt_softWeight (fun j => affineProcess_coordinate_hasDerivAt m a j k u z) i

omit [Nonempty ι] in
theorem weighted_covariance_identity (p u v : ι → ℝ) (hp : ∑ i, p i = 1) :
    (∑ i, p i * u i * v i) - (∑ i, p i * u i) * (∑ i, p i * v i) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, p i * p j * (u i - u j) * (v i - v j) := by
  have he (i j : ι) : p i * p j * (u i - u j) * (v i - v j) =
      (p i * u i * v i) * p j + p i * (p j * u j * v j) -
        (p i * u i) * (p j * v j) - (p i * v i) * (p j * u j) := by ring
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hp]
  ring

theorem smoothMax_norm_le {κ : ℝ} (hκ : 0 < κ) (x : ι → ℝ) :
    ‖smoothMax κ x‖ ≤ ∑ i, |x i| + log (Fintype.card ι) / κ := by
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlog : 0 ≤ log (Fintype.card ι) / κ := div_nonneg (log_nonneg hn) hκ.le
  have hb (i : ι) : |x i| ≤ ∑ j, |x j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · let i : ι := Classical.choice inferInstance
    have hlo := smoothMax_ge hκ x i
    have ha := (abs_le.mp (hb i)).1
    linarith
  · exact smoothMax_le hκ x (fun i => (le_abs_self _).trans (hb i))

omit [Fintype ι] [Nonempty ι] in
theorem interpolatedCoeff_abs_le {n : ℕ} (a b : ι → Fin n → ℝ) (t : ℝ) (i : ι) (k : Fin n) :
    |interpolatedCoeff a b t i k| ≤ |a i k| + |b i k| := by
  calc
    _ ≤ |sin t * a i k| + |cos t * b i k| := abs_add_le _ _
    _ ≤ 1 * |a i k| + 1 * |b i k| := by
      simp only [abs_mul]
      gcongr
      · exact abs_sin_le_one t
      · exact abs_cos_le_one t
    _ = _ := by ring

omit [Fintype ι] [Nonempty ι] in
theorem interpolatedCoeffDeriv_abs_le {n : ℕ} (a b : ι → Fin n → ℝ) (t : ℝ) (i : ι) (k : Fin n) :
    |interpolatedCoeffDeriv a b t i k| ≤ |a i k| + |b i k| := by
  calc
    _ ≤ |cos t * a i k| + |sin t * b i k| := abs_sub _ _
    _ ≤ 1 * |a i k| + 1 * |b i k| := by
      simp only [abs_mul]
      gcongr
      · exact abs_cos_le_one t
      · exact abs_sin_le_one t
    _ = _ := by ring

omit [Nonempty ι] in
theorem integrable_processBound {n : ℕ} (a b : ι → Fin n → ℝ) :
    Integrable (processBound a b) (standardGaussianProduct n) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro k _
  exact ((integrable_eval (i := k) IsGaussian.integrable_id).norm).const_mul _

omit [Fintype ι] [Nonempty ι] in
theorem interpolated_affine_hasDerivAt {n : ℕ} (m : ι → ℝ) (a b : ι → Fin n → ℝ)
    (z : Fin n → ℝ) (t : ℝ) (i : ι) :
    HasDerivAt (fun t => affineProcess m (interpolatedCoeff a b t) z i)
      (∑ k, interpolatedCoeffDeriv a b t i k * z k) t := by
  convert! (HasDerivAt.fun_sum (fun k _ =>
    (((Real.hasDerivAt_sin t).mul_const (a i k)).add
      ((Real.hasDerivAt_cos t).mul_const (b i k))).mul_const (z k))).const_add (m i) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro k _
  dsimp [interpolatedCoeffDeriv]
  ring

theorem interpolationDerivative_norm_le {n : ℕ} (κ : ℝ) (m : ι → ℝ)
    (a b : ι → Fin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    ‖interpolationDerivative κ m a b t z‖ ≤ processBound a b z := by
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ i, |∑ k, interpolatedCoeffDeriv a b t i k * z k| := weighted_abs_le _ _ _
    _ ≤ ∑ i, ∑ k, (|a i k| + |b i k|) * |z k| := by
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (interpolatedCoeffDeriv_abs_le a b t i k) (abs_nonneg _)

theorem interpolated_smoothMax_norm_le {n : ℕ} {κ : ℝ} (hκ : 0 < κ) (m : ι → ℝ)
    (a b : ι → Fin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    ‖smoothMax κ (affineProcess m (interpolatedCoeff a b t) z)‖ ≤
      (∑ i, |m i|) + processBound a b z + log (Fintype.card ι) / κ := by
  apply (smoothMax_norm_le hκ _).trans
  gcongr
  rw [processBound, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply (abs_add_le _ _).trans
  gcongr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (interpolatedCoeff_abs_le a b t i k) (abs_nonneg _)

theorem interpolation_hasDerivAt {n : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (m : ι → ℝ) (a b : ι → Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun t => ∫ z, smoothMax κ (affineProcess m (interpolatedCoeff a b t) z)
      ∂standardGaussianProduct n)
      (∫ z, interpolationDerivative κ m a b t z ∂standardGaussianProduct n) t := by
  have hp (t : ℝ) (i : ι) :
      Continuous (fun z => softWeight κ (affineProcess m (interpolatedCoeff a b t) z) i) :=
    (continuous_softWeight κ i).comp (continuous_affineProcess m _)
  have hf (t : ℝ) : Continuous (fun z => smoothMax κ (affineProcess m (interpolatedCoeff a b t) z)) :=
    (continuous_smoothMax κ).comp (continuous_affineProcess m _)
  have hdf (t : ℝ) : Continuous (interpolationDerivative κ m a b t) := by
    apply continuous_finsetSum
    intro i _
    exact (hp t i).mul (continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_apply k)))
  have hb : Integrable (fun z => (∑ i, |m i|) + processBound a b z + log (Fintype.card ι) / κ)
      (standardGaussianProduct n) :=
    ((integrable_const _).add (integrable_processBound a b)).add (integrable_const _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := standardGaussianProduct n) (s := univ) (x₀ := t)
    (F := fun t z => smoothMax κ (affineProcess m (interpolatedCoeff a b t) z))
    (F' := fun t z => interpolationDerivative κ m a b t z)
    (bound := processBound a b)
    Filter.univ_mem (Filter.Eventually.of_forall (fun t => (hf t).aestronglyMeasurable))
    (hb.mono' (hf t).aestronglyMeasurable (ae_of_all _ (interpolated_smoothMax_norm_le hκ m a b t)))
    (hdf t).aestronglyMeasurable
    (ae_of_all _ (fun z t _ => interpolationDerivative_norm_le κ m a b t z))
    (integrable_processBound a b)
    (ae_of_all _ (fun z t _ => hasDerivAt_smoothMax hκ.ne'
      (fun i => interpolated_affine_hasDerivAt m a b z t i)))).2

theorem integrable_affine_weight {n : ℕ} (κ : ℝ) (m : ι → ℝ) (a : ι → Fin n → ℝ) (i : ι) :
    Integrable (fun z => softWeight κ (affineProcess m a z) i) (standardGaussianProduct n) := by
  apply Integrable.of_bound ((continuous_softWeight κ i).comp (continuous_affineProcess m a)).aestronglyMeasurable 1
  exact ae_of_all _ (fun z => by
    simp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_pos (softWeight_pos _ _ _)]
    exact softWeight_le_one _ _ _)

theorem integrable_coordinate_weight {n : ℕ} (κ : ℝ) (m : ι → ℝ)
    (a : ι → Fin n → ℝ) (i : ι) (k : Fin n) :
    Integrable (fun z => z k * softWeight κ (affineProcess m a z) i) (standardGaussianProduct n) := by
  apply Integrable.mul_bdd (integrable_eval (i := k) IsGaussian.integrable_id)
    ((continuous_softWeight κ i).comp (continuous_affineProcess m a)).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    simp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_pos (softWeight_pos _ _ _)]
    exact softWeight_le_one _ _ _)

theorem integrable_weight_covariance {n : ℕ} (κ : ℝ) (m : ι → ℝ)
    (a : ι → Fin n → ℝ) (i : ι) (k : Fin n) :
    Integrable (fun z => κ * softWeight κ (affineProcess m a z) i *
      (a i k - ∑ j, softWeight κ (affineProcess m a z) j * a j k))
      (standardGaussianProduct n) := by
  have hi : Integrable (fun z => a i k - ∑ j, softWeight κ (affineProcess m a z) j * a j k)
      (standardGaussianProduct n) := by
    apply (integrable_const _).sub
    exact integrable_finsetSum _ (fun j _ => (integrable_affine_weight κ m a j).mul_const _)
  have hm := hi.bdd_mul ((continuous_softWeight κ i).comp (continuous_affineProcess m a)).aestronglyMeasurable
    (ae_of_all _ (fun z => by
      simp only [Function.comp_def]
      rw [Real.norm_eq_abs, abs_of_pos (softWeight_pos κ (affineProcess m a z) i)]
      exact softWeight_le_one _ _ _))
  convert! hm.const_mul κ using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [Function.comp_def]
  ring

omit [Nonempty ι] in
theorem weighted_matrix_covariance_identity {n : ℕ} (p : ι → ℝ) (a d : ι → Fin n → ℝ)
    (hp : ∑ i, p i = 1) :
    (∑ i, ∑ k, d i k * p i * (a i k - ∑ j, p j * a j k)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, p i * p j * ∑ k, (d i k - d j k) * (a i k - a j k) := by
  have hk (k : Fin n) :
      (∑ i, d i k * p i * (a i k - ∑ j, p j * a j k)) =
        (1/2:ℝ) * ∑ i, ∑ j, p i * p j * (d i k - d j k) * (a i k - a j k) := by
    rw [← weighted_covariance_identity p (fun i => d i k) (fun i => a i k) hp]
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [Finset.sum_comm]
  simp_rw [hk, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem gaussian_linear_weight_IBP {n : ℕ} (κ : ℝ) (m : ι → ℝ)
    (a d : ι → Fin (n + 1) → ℝ) :
    (∫ z, ∑ i, softWeight κ (affineProcess m a z) i * ∑ k, d i k * z k
      ∂standardGaussianProduct (n + 1)) =
      (κ / 2) * ∫ z, ∑ i, ∑ j,
        softWeight κ (affineProcess m a z) i * softWeight κ (affineProcess m a z) j *
        ∑ k, (d i k - d j k) * (a i k - a j k)
        ∂standardGaussianProduct (n + 1) := by
  let p := fun z i => softWeight κ (affineProcess m a z) i
  have hi (i : ι) (k : Fin (n + 1)) : Integrable (fun z => d i k * (z k * p z i))
      (standardGaussianProduct (n + 1)) := (integrable_coordinate_weight κ m a i k).const_mul _
  have hr (i : ι) (k : Fin (n + 1)) : Integrable (fun z => d i k *
      (κ * p z i * (a i k - ∑ j, p z j * a j k))) (standardGaussianProduct (n + 1)) :=
    (integrable_weight_covariance κ m a i k).const_mul _
  calc
    _ = ∫ z, ∑ i, ∑ k, d i k * (z k * p z i) ∂standardGaussianProduct (n + 1) := by
      apply integral_congr_ae
      filter_upwards [] with z
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [p]
      ring
    _ = ∑ i, ∑ k, d i k * ∫ z, z k * p z i ∂standardGaussianProduct (n + 1) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hi i k))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun k _ => hi i k)]
      simp only [integral_const_mul]
    _ = ∑ i, ∑ k, d i k * ∫ z, κ * p z i * (a i k - ∑ j, p z j * a j k)
        ∂standardGaussianProduct (n + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [affine_softWeight_coordinate_IBP]
    _ = ∫ z, ∑ i, ∑ k, d i k * (κ * p z i * (a i k - ∑ j, p z j * a j k))
        ∂standardGaussianProduct (n + 1) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hr i k))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun k _ => hr i k)]
      simp only [integral_const_mul]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      have he := weighted_matrix_covariance_identity (p z) a d (sum_softWeight κ _)
      calc
        _ = κ * ∑ i, ∑ k, d i k * p z i * (a i k - ∑ j, p z j * a j k) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by rw [he]; dsimp [p]; ring

end SKRatioGaussian
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
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_FiniteMax
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
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
namespace SKRatioGaussian
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
omit [Fintype ι] [Nonempty ι] in
theorem interpolation_increment_identity {n : ℕ} (a b : ι → Fin n → ℝ) (i j : ι) (t : ℝ)
    (horth : ∑ k, (a i k - a j k) * (b i k - b j k) = 0) :
    (∑ k, (interpolatedCoeffDeriv a b t i k - interpolatedCoeffDeriv a b t j k) *
      (interpolatedCoeff a b t i k - interpolatedCoeff a b t j k)) =
      sin t * cos t * ((∑ k, (a i k - a j k) ^ 2) - ∑ k, (b i k - b j k) ^ 2) := by
  have he (k : Fin n) :
      (interpolatedCoeffDeriv a b t i k - interpolatedCoeffDeriv a b t j k) *
        (interpolatedCoeff a b t i k - interpolatedCoeff a b t j k) =
      sin t * cos t * (a i k - a j k)^2 - sin t * cos t * (b i k - b j k)^2 +
        (cos t ^ 2 - sin t ^ 2) * ((a i k - a j k) * (b i k - b j k)) := by
    dsimp [interpolatedCoeff, interpolatedCoeffDeriv]
    ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [horth]
  ring

theorem interpolation_derivative_nonneg {n : ℕ} {κ : ℝ} (hκ : 0 ≤ κ)
    (m : ι → ℝ) (a b : ι → Fin (n + 1) → ℝ)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2)
    {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) :
    0 ≤ ∫ z, interpolationDerivative κ m a b t z ∂standardGaussianProduct (n + 1) := by
  have hs : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [pi_pos, ht.2])
  have hc : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, ht.1], ht.2⟩
  rw [show (fun z => interpolationDerivative κ m a b t z) =
      (fun z => ∑ i, softWeight κ (affineProcess m (interpolatedCoeff a b t) z) i *
        ∑ k, interpolatedCoeffDeriv a b t i k * z k) from rfl,
    gaussian_linear_weight_IBP]
  apply mul_nonneg (div_nonneg hκ (by norm_num))
  apply integral_nonneg
  intro z
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (mul_nonneg (softWeight_pos _ _ _).le (softWeight_pos _ _ _).le)
  rw [interpolation_increment_identity a b i j t (horth i j)]
  exact mul_nonneg (mul_nonneg hs hc) (sub_nonneg.mpr (hinc i j))

theorem gaussian_smoothMax_comparison {n : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (m : ι → ℝ) (a b : ι → Fin (n + 1) → ℝ)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2) :
    (∫ z, smoothMax κ (affineProcess m b z) ∂standardGaussianProduct (n + 1)) ≤
      ∫ z, smoothMax κ (affineProcess m a z) ∂standardGaussianProduct (n + 1) := by
  let f := fun t => ∫ z, smoothMax κ (affineProcess m (interpolatedCoeff a b t) z)
    ∂standardGaussianProduct (n + 1)
  have hmono : MonotoneOn f (Icc 0 (π / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun t => (interpolation_hasDerivAt hκ m a b t).continuousAt)).continuousOn
      (fun t _ => (interpolation_hasDerivAt hκ m a b t).hasDerivWithinAt)
    intro t ht
    exact interpolation_derivative_nonneg hκ.le m a b horth hinc (interior_subset ht)
  have hle := hmono (show (0:ℝ) ∈ Icc 0 (π/2) from ⟨le_refl _, by positivity⟩)
    (show π/2 ∈ Icc (0:ℝ) (π/2) from ⟨by positivity, le_refl _⟩) (by positivity)
  have h0 : interpolatedCoeff a b 0 = b := by
    funext i k
    simp [interpolatedCoeff]
  have h1 : interpolatedCoeff a b (π/2) = a := by
    funext i k
    simp [interpolatedCoeff]
  simpa only [f, h0, h1] using hle

theorem le_finiteMax (x : ι → ℝ) (i : ι) : x i ≤ finiteMax x :=
  Finset.le_sup' x (Finset.mem_univ i)

theorem finiteMax_le {x : ι → ℝ} {b : ℝ} (hb : ∀ i, x i ≤ b) : finiteMax x ≤ b :=
  Finset.sup'_le _ _ (fun i _ => hb i)

theorem continuous_finiteMax : Continuous (finiteMax : (ι → ℝ) → ℝ) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => continuous_apply i)

theorem finiteMax_norm_le (x : ι → ℝ) : ‖finiteMax x‖ ≤ ∑ i, |x i| := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  change ‖Finset.univ.sup' Finset.univ_nonempty x‖ ≤ _
  rw [hi, Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

omit [Fintype ι] [Nonempty ι] in
theorem integrable_affineProcess {n : ℕ} (m : ι → ℝ) (a : ι → Fin n → ℝ) (i : ι) :
    Integrable (fun z => affineProcess m a z i) (standardGaussianProduct n) := by
  apply (integrable_const _).add
  exact integrable_finsetSum _ (fun k _ => (integrable_eval (i := k) IsGaussian.integrable_id).const_mul _)

theorem integrable_finiteMax_affine {n : ℕ} (m : ι → ℝ) (a : ι → Fin n → ℝ) :
    Integrable (fun z => finiteMax (affineProcess m a z)) (standardGaussianProduct n) := by
  apply (integrable_finsetSum _ (fun i _ => (integrable_affineProcess m a i).norm)).mono'
    (continuous_finiteMax.comp (continuous_affineProcess m a)).aestronglyMeasurable
  exact ae_of_all _ (fun z => finiteMax_norm_le _)

theorem integrable_smoothMax_affine {n : ℕ} {κ : ℝ} (hκ : 0 < κ) (m : ι → ℝ) (a : ι → Fin n → ℝ) :
    Integrable (fun z => smoothMax κ (affineProcess m a z)) (standardGaussianProduct n) := by
  apply ((integrable_finsetSum _ (fun i _ => (integrable_affineProcess m a i).norm)).add
    (integrable_const (log (Fintype.card ι) / κ))).mono'
    ((continuous_smoothMax κ).comp (continuous_affineProcess m a)).aestronglyMeasurable
  exact ae_of_all _ (fun z => smoothMax_norm_le hκ _)

theorem gaussian_finiteMax_comparison {n : ℕ}
    (m : ι → ℝ) (a b : ι → Fin (n + 1) → ℝ)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2) :
    (∫ z, finiteMax (affineProcess m b z) ∂standardGaussianProduct (n + 1)) ≤
      ∫ z, finiteMax (affineProcess m a z) ∂standardGaussianProduct (n + 1) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hlog : 0 ≤ log (Fintype.card ι) := log_nonneg (by exact_mod_cast Fintype.card_pos)
  let κ := (log (Fintype.card ι) + 1) / ε
  have hκ : 0 < κ := div_pos (by linarith) hε
  have herr : log (Fintype.card ι) / κ ≤ ε := by
    apply (div_le_iff₀ hκ).mpr
    dsimp [κ]
    rw [mul_div_cancel₀ _ hε.ne']
    linarith
  calc
    _ ≤ ∫ z, smoothMax κ (affineProcess m b z) ∂standardGaussianProduct (n + 1) := by
      apply integral_mono (integrable_finiteMax_affine m b) (integrable_smoothMax_affine hκ m b)
      intro z
      exact finiteMax_le (fun i => smoothMax_ge hκ _ i)
    _ ≤ ∫ z, smoothMax κ (affineProcess m a z) ∂standardGaussianProduct (n + 1) :=
      gaussian_smoothMax_comparison hκ m a b horth hinc
    _ ≤ (∫ z, finiteMax (affineProcess m a z) ∂standardGaussianProduct (n + 1)) + ε := by
      calc
        _ ≤ ∫ z, finiteMax (affineProcess m a z) + log (Fintype.card ι) / κ
            ∂standardGaussianProduct (n + 1) := by
          apply integral_mono (integrable_smoothMax_affine hκ m a)
            ((integrable_finiteMax_affine m a).add (integrable_const _))
          intro z
          exact smoothMax_le hκ _ (fun i => le_finiteMax _ i)
        _ = (∫ z, finiteMax (affineProcess m a z) ∂standardGaussianProduct (n + 1)) +
            log (Fintype.card ι) / κ := by
          rw [integral_add (integrable_finiteMax_affine m a) (integrable_const _)]
          simp
        _ ≤ _ := add_le_add (le_refl _) herr

section CompactIndex
variable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]

omit [CompactSpace I] [Nonempty I] in
theorem continuous_affine_index {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : Fin n → ℝ) :
    Continuous (affineProcess m a z) := by
  exact hm.add (continuous_finsetSum _ (fun k _ => ((continuous_apply k).comp ha).mul continuous_const))

theorem supProcess_attained {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : Fin n → ℝ) :
    ∃ i, supProcess m a z = affineProcess m a z i ∧
      ∀ j, affineProcess m a z j ≤ affineProcess m a z i := by
  obtain ⟨i, _, he, hi⟩ := isCompact_univ.exists_sSup_image_eq_and_ge
    Set.univ_nonempty (continuous_affine_index hm ha z).continuousOn
  exact ⟨i, by simpa [supProcess] using he, fun j => hi j (Set.mem_univ _)⟩

theorem affine_le_supProcess {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : Fin n → ℝ) (i : I) :
    affineProcess m a z i ≤ supProcess m a z := by
  obtain ⟨j, he, hj⟩ := supProcess_attained hm ha z
  rw [he]
  exact hj i

theorem supProcess_le {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : Fin n → ℝ) {c : ℝ}
    (hc : ∀ i, affineProcess m a z i ≤ c) : supProcess m a z ≤ c := by
  obtain ⟨i, he, _⟩ := supProcess_attained hm ha z
  rw [he]
  exact hc i

omit [Nonempty I] in
theorem continuous_supProcess {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) : Continuous (supProcess m a) := by
  have hc : Continuous (fun p : (Fin n → ℝ) × I => affineProcess m a p.1 p.2) := by
    exact (hm.comp continuous_snd).add (continuous_finsetSum _ (fun k _ =>
      (((continuous_apply k).comp ha).comp continuous_snd).mul
        ((continuous_apply k).comp continuous_fst)))
  change Continuous (fun z => sSup (Set.range (affineProcess m a z)))
  simpa only [Set.image_univ] using isCompact_univ.continuous_sSup hc

omit [TopologicalSpace I] [CompactSpace I] [Nonempty I] in
 theorem affineProcess_abs_le {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    {M A : ℝ} (hm : ∀ i, |m i| ≤ M) (ha : ∀ i k, |a i k| ≤ A)
    (z : Fin n → ℝ) (i : I) :
    |affineProcess m a z i| ≤ M + A * ∑ k, |z k| := by
  calc
    _ ≤ |m i| + |∑ k, a i k * z k| := abs_add_le _ _
    _ ≤ M + ∑ k, |a i k * z k| := add_le_add (hm i) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ M + ∑ k, A * |z k| := by
      gcongr with k
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (ha i k) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem integrable_supProcess {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) :
    Integrable (supProcess m a) (standardGaussianProduct n) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hm.continuousOn
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
  have hMb : ∀ i, |m i| ≤ M := fun i => by simpa only [Real.norm_eq_abs] using hM i (Set.mem_univ _)
  have hAb : ∀ i k, |a i k| ≤ A := by
    intro i k
    have hk : |a i k| ≤ ‖a i‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (a i) k
    exact hk.trans (hA i (Set.mem_univ _))
  apply ((integrable_const M).add ((integrable_finsetSum _ (fun k _ =>
    ((integrable_eval (i := k) IsGaussian.integrable_id).norm))).const_mul A)).mono'
    (continuous_supProcess hm ha).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨i, he, _⟩ := supProcess_attained hm ha z
  rw [he, Real.norm_eq_abs]
  exact affineProcess_abs_le hMb hAb z i

theorem exists_finite_affine_net {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset I, t.Nonempty ∧ ∀ j, ∃ i ∈ t,
      |m j - m i| ≤ ε ∧ ∀ k, |a j k - a i k| ≤ ε := by
  let U : I → Set I := fun i => m ⁻¹' Metric.ball (m i) ε ∩ a ⁻¹' Metric.ball (a i) ε
  have ho (i : I) : IsOpen (U i) :=
    (Metric.isOpen_ball.preimage hm).inter (Metric.isOpen_ball.preimage ha)
  have hu : Set.univ ⊆ ⋃ i, U i := by
    intro j _
    apply Set.mem_iUnion.mpr
    exact ⟨j, by simp [U, hε]⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U ho hu
  have hcover (j : I) : ∃ i ∈ t, j ∈ U i := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ j))
    obtain ⟨hit, hji⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hit, hji⟩
  have hne : t.Nonempty := by
    obtain ⟨i, hi, _⟩ := hcover (Classical.choice inferInstance)
    exact ⟨i, hi⟩
  refine ⟨t, hne, fun j => ?_⟩
  obtain ⟨i, hi, hj⟩ := hcover j
  refine ⟨i, hi, ?_, fun k => ?_⟩
  · have hd : dist (m j) (m i) < ε := hj.1
    simpa only [Real.dist_eq] using hd.le
  · have hb : dist (a j) (a i) < ε := hj.2
    have hk := (dist_le_pi_dist (a j) (a i) k).trans_lt hb
    simpa only [Real.dist_eq] using hk.le

omit [TopologicalSpace I] [CompactSpace I] [Nonempty I] in
 theorem affineProcess_difference_abs_le {n : ℕ} (m : I → ℝ) (a : I → Fin n → ℝ)
    {ε : ℝ} {i j : I} (hm : |m i - m j| ≤ ε)
    (ha : ∀ k, |a i k - a j k| ≤ ε) (z : Fin n → ℝ) :
    |affineProcess m a z i - affineProcess m a z j| ≤ ε * (1 + ∑ k, |z k|) := by
  have he : affineProcess m a z i - affineProcess m a z j =
      (m i - m j) + ∑ k, (a i k - a j k) * z k := by
    simp only [affineProcess, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ |m i - m j| + |∑ k, (a i k - a j k) * z k| := abs_add_le _ _
    _ ≤ ε + ∑ k, |(a i k - a j k) * z k| :=
      add_le_add hm (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ε + ∑ k, ε * |z k| := by
      gcongr with k
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (ha k) (abs_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem gaussian_supProcess_comparison {n : ℕ}
    {m : I → ℝ} {a b : I → Fin (n + 1) → ℝ}
    (hm : Continuous m) (ha : Continuous a) (hb : Continuous b)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2) :
    (∫ z, supProcess m b z ∂standardGaussianProduct (n + 1)) ≤
      ∫ z, supProcess m a z ∂standardGaussianProduct (n + 1) := by
  let μ := standardGaussianProduct (n + 1)
  let Z : (Fin (n + 1) → ℝ) → ℝ := fun z => 1 + ∑ k, |z k|
  have hZI : Integrable Z μ := (integrable_const 1).add
    (integrable_finsetSum _ (fun k _ => by
      have hi : Integrable (fun z : Fin (n + 1) → ℝ => z k) μ :=
        integrable_eval (i := k) IsGaussian.integrable_id
      simpa only [Real.norm_eq_abs] using hi.norm))
  have hZ : 0 ≤ ∫ z, Z z ∂μ := integral_nonneg (fun z => by dsimp [Z]; positivity)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / ((∫ z, Z z ∂μ) + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδε : δ * (∫ z, Z z ∂μ) ≤ ε := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by linarith : 0 < (∫ z, Z z ∂μ) + 1)).mpr
    nlinarith
  obtain ⟨t, ht, hnet⟩ := exists_finite_affine_net hm hb hδ
  have : Nonempty t := ht.to_subtype
  let mf : t → ℝ := fun i => m i
  let af : t → Fin (n + 1) → ℝ := fun i => a i
  let bf : t → Fin (n + 1) → ℝ := fun i => b i
  have hfinite := gaussian_finiteMax_comparison mf af bf
    (fun i j => horth i j) (fun i j => hinc i j)
  calc
    _ ≤ ∫ z, finiteMax (affineProcess mf bf z) + δ * Z z ∂μ := by
      apply integral_mono (integrable_supProcess hm hb)
        ((integrable_finiteMax_affine mf bf).add (hZI.const_mul δ))
      intro z
      apply supProcess_le hm hb
      intro j
      obtain ⟨i, hi, hmj, hbj⟩ := hnet j
      have hd := (le_abs_self _).trans (affineProcess_difference_abs_le m b hmj hbj z)
      have hmax := le_finiteMax (affineProcess mf bf z) (⟨i, hi⟩ : t)
      change affineProcess m b z i ≤ _ at hmax
      change affineProcess m b z j ≤ finiteMax (affineProcess mf bf z) + δ * (1 + ∑ k, |z k|)
      linarith
    _ = (∫ z, finiteMax (affineProcess mf bf z) ∂μ) + δ * ∫ z, Z z ∂μ := by
      rw [integral_add (integrable_finiteMax_affine mf bf) (hZI.const_mul δ), integral_const_mul]
    _ ≤ (∫ z, finiteMax (affineProcess mf af z) ∂μ) + ε := add_le_add hfinite hδε
    _ ≤ (∫ z, supProcess m a z ∂μ) + ε := by
      refine add_le_add ?_ le_rfl
      apply integral_mono (integrable_finiteMax_affine mf af) (integrable_supProcess hm ha)
      intro z
      apply finiteMax_le
      intro i
      exact affine_le_supProcess hm ha z i

end CompactIndex
end SKRatioGaussian

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
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GOERegression
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise

namespace SKRatioClock.Regression

lemma coordinate_hasLaw {ι : Type*} [Fintype ι] (i : ι) :
    HasLaw (fun g : ι → ℝ => g i) (gaussianReal 0 1) (standardArrayLaw ι) :=
  (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw

lemma coordinates_independent {ι : Type*} [Fintype ι] :
    iIndepFun (fun i (g : ι → ℝ) => g i) (standardArrayLaw ι) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

lemma coordinates_gaussian {ι : Type*} [Fintype ι] :
    HasGaussianLaw (fun g : ι → ℝ => g) (standardArrayLaw ι) :=
  coordinates_independent.hasGaussianLaw (fun i => (coordinate_hasLaw i).hasGaussianLaw)

lemma coordinate_covariance {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    cov[fun g : ι → ℝ => g i, fun g => g j; standardArrayLaw ι] = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    rw [covariance_self (coordinate_hasLaw i).aemeasurable,
      (coordinate_hasLaw i).variance_eq, variance_id_gaussianReal]
    simp
  · rw [ite_eq_right h]
    exact (coordinates_independent.indepFun h).covariance_eq_zero
      ((coordinate_hasLaw i).hasGaussianLaw.memLp_two)
      ((coordinate_hasLaw j).hasGaussianLaw.memLp_two)

attribute [local instance] OAI.SKRatioClock.Regression.matrixMeasurable
local instance matrixBorel_r949a04_1 {n m : ℕ} : BorelSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin m → ℝ))
lemma goe_gaussian (n : ℕ) :
    HasGaussianLaw (fun g : (Fin n × Fin n) → ℝ => goe g)
      (standardArrayLaw (Fin n × Fin n)) := by
  have h := coordinates_gaussian.map_fun
    (show ((Fin n × Fin n) → ℝ) →L[ℝ] (Fin n → Fin n → ℝ) from goeCLM n)
  exact h.congr (Filter.Eventually.of_forall (goeCLM_apply n))

lemma goe_entry_memLp {n : ℕ} (i j : Fin n) :
    MemLp (fun g : (Fin n × Fin n) → ℝ => goe g i j) 2 (standardArrayLaw (Fin n × Fin n)) :=
  ((goe_gaussian n).eval i |>.eval j).memLp_two

lemma goe_entry_covariance {n : ℕ} (hn : 0 < n) (i j k l : Fin n) :
    cov[fun g : (Fin n × Fin n) → ℝ => goe g i j, fun g => goe g k l;
        standardArrayLaw (Fin n × Fin n)] =
      ((if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) / n := by
  have hLp (a : Fin n × Fin n) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  simp only [goe, covariance_fun_div_left, covariance_fun_div_right]
  change cov[(fun g => g (i,j)) + (fun g => g (j,i)),
    (fun g => g (k,l)) + (fun g => g (l,k)); standardArrayLaw (Fin n × Fin n)] /
      Real.sqrt (2*n) / Real.sqrt (2*n) = _
  rw [covariance_add_left (hLp _) (hLp _) ((hLp _).add (hLp _)),
    covariance_add_right (hLp _) (hLp _) (hLp _),
    covariance_add_right (hLp _) (hLp _) (hLp _)]
  simp only [coordinate_covariance, Prod.mk.injEq]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (2*n) ^ 2 = 2*n := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2*(n : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  rw [div_div, ← pow_two]
  rw [hs]
  have ha : (j = k ∧ i = l) ↔ (i = l ∧ j = k) := and_comm
  have hb : (j = l ∧ i = k) ↔ (i = k ∧ j = l) := and_comm
  simp only [ha, hb]
  ring

lemma residualProjection_symmetric {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) :
    (residualProjection U)ᵀ = residualProjection U := by
  simp [residualProjection]

lemma residualProjection_mul {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) :
    residualProjection U * U = 0 := by
  simp [residualProjection, Matrix.sub_mul, Matrix.mul_assoc, hU]

lemma goe_entry_sandwich_covariance {n a b : ℕ} (hn : 0 < n)
    (C : Matrix (Fin a) (Fin n) ℝ) (D : Matrix (Fin n) (Fin b) ℝ)
    (i j : Fin n) (k : Fin a) (l : Fin b) :
    cov[fun g : (Fin n × Fin n) → ℝ => goe g i j,
        fun g => (C * goe g * D) k l; standardArrayLaw (Fin n × Fin n)] =
      (C k i * D j l + C k j * D i l) / n := by
  have hterm (p q : Fin n) : MemLp (fun g : (Fin n × Fin n) → ℝ =>
      C k q * goe g q p * D p l) 2 (standardArrayLaw (Fin n × Fin n)) :=
    ((goe_entry_memLp q p).const_mul _).mul_const _
  have hsum (p : Fin n) := memLp_finsetSum Finset.univ (fun q _ => hterm p q)
  have he (g : (Fin n × Fin n) → ℝ) : (C * goe g * D) k l =
      ∑ p, ∑ q, C k q * goe g q p * D p l := by
    simp [Matrix.mul_apply, Finset.sum_mul]
  simp_rw [he]
  rw [covariance_fun_sum_right hsum (goe_entry_memLp i j)]
  simp_rw [covariance_fun_sum_right (fun q => hterm _ q) (goe_entry_memLp i j),
    covariance_mul_const_right, covariance_const_mul_right, goe_entry_covariance hn]
  simp only [ite_and, add_div, mul_add, add_mul, Finset.sum_add_distrib,
    ite_div, mul_ite, ite_mul, zero_div, mul_zero, zero_mul]
  simp
  ring

lemma goe_sandwich_covariance {n a b c d : ℕ} (hn : 0 < n)
    (A : Matrix (Fin a) (Fin n) ℝ) (B : Matrix (Fin n) (Fin b) ℝ)
    (C : Matrix (Fin c) (Fin n) ℝ) (D : Matrix (Fin n) (Fin d) ℝ)
    (i : Fin a) (j : Fin b) (k : Fin c) (l : Fin d) :
    cov[fun g : (Fin n × Fin n) → ℝ => (A * goe g * B) i j,
        fun g => (C * goe g * D) k l; standardArrayLaw (Fin n × Fin n)] =
      ((Bᵀ * D) j l * (A * Cᵀ) i k + (C * B) k j * (A * D) i l) / n := by
  have hterm (p q : Fin n) : MemLp (fun g : (Fin n × Fin n) → ℝ =>
      A i q * goe g q p * B p j) 2 (standardArrayLaw (Fin n × Fin n)) :=
    ((goe_entry_memLp q p).const_mul _).mul_const _
  have hsum (p : Fin n) := memLp_finsetSum Finset.univ (fun q _ => hterm p q)
  have hCD : MemLp (fun g : (Fin n × Fin n) → ℝ => (C * goe g * D) k l)
      2 (standardArrayLaw (Fin n × Fin n)) := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    exact memLp_finsetSum _ (fun p _ => memLp_finsetSum _
      (fun q _ => ((goe_entry_memLp q p).const_mul _).mul_const _))
  have he (g : (Fin n × Fin n) → ℝ) : (A * goe g * B) i j =
      ∑ p, ∑ q, A i q * goe g q p * B p j := by
    simp [Matrix.mul_apply, Finset.sum_mul]
  simp_rw [he]
  rw [covariance_fun_sum_left hsum hCD]
  simp_rw [covariance_fun_sum_left (fun q => hterm _ q) hCD,
    covariance_mul_const_left, covariance_const_mul_left, goe_entry_sandwich_covariance hn]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [← mul_div_assoc, div_mul_eq_mul_div, ← Finset.sum_div]
  apply congrArg (fun x : ℝ => x / n)
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma residual_answer_covariance {n r : ℕ} (hn : 0 < n)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (i j k : Fin n) (l : Fin r) :
    cov[fun g : (Fin n × Fin n) → ℝ =>
        (residualProjection U * goe g * residualProjection U) i j,
      fun g => (goe g * U) k l; standardArrayLaw (Fin n × Fin n)] = 0 := by
  have h := goe_sandwich_covariance hn (residualProjection U) (residualProjection U)
    (1 : Matrix (Fin n) (Fin n) ℝ) U i j k l
  simpa [residualProjection_symmetric, residualProjection_mul U hU] using h

lemma regressionCLM_apply {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (g : (Fin n × Fin n) → ℝ) :
    regressionCLM U g =
      (fun p : Fin n × Fin n => (residualProjection U * goe g * residualProjection U) p.1 p.2,
       fun p : Fin n × Fin r => (goe g * U) p.1 p.2) := by
  change (fun p : Fin n × Fin n =>
      (residualProjection U * (goeCLM n) g * residualProjection U) p.1 p.2,
    fun p : Fin n × Fin r => ((1 : Matrix (Fin n) (Fin n) ℝ) * (goeCLM n) g * U) p.1 p.2) = _
  rw [goeCLM_apply, Matrix.one_mul]

lemma residual_answer_independent {n r : ℕ} (hn : 0 < n)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) :
    IndepFun (fun g : (Fin n × Fin n) → ℝ => fun p : Fin n × Fin n =>
      (residualProjection U * goe g * residualProjection U) p.1 p.2)
      (fun g => fun p : Fin n × Fin r => (goe g * U) p.1 p.2)
      (standardArrayLaw (Fin n × Fin n)) := by
  have hXY := (coordinates_gaussian.map_fun (regressionCLM U)).congr
    (Filter.Eventually.of_forall (regressionCLM_apply U))
  exact hXY.indepFun_of_covariance_eval (fun p q =>
    residual_answer_covariance hn U hU p.1 p.2 q.1 q.2)

lemma coordinate_mean {ι : Type*} [Fintype ι] (i : ι) :
    (∫ g : ι → ℝ, g i ∂standardArrayLaw ι) = 0 := by
  rw [(coordinate_hasLaw i).integral_eq, integral_id_gaussianReal]

lemma queryColumn_unit {n : ℕ} (q : Fin n → ℝ) (hq : ∑ i, q i ^ 2 = 1) :
    (queryColumn q)ᵀ * queryColumn q = 1 := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i; subst j
  simpa [Matrix.mul_apply, queryColumn, pow_two] using hq

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianCoordinates
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
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
namespace SKRatioGaussian
section ArbitraryCoordinates
variable {I κ : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]
  [Fintype κ]

omit [CompactSpace I] [Nonempty I] in
 theorem continuous_gaussianAffine {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : κ → ℝ) :
    Continuous (gaussianAffine m a z) :=
  hm.add (continuous_finsetSum _ (fun k _ =>
    ((continuous_apply k).comp ha).mul continuous_const))

theorem gaussianSup_attained {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : κ → ℝ) :
    ∃ i, gaussianSup m a z = gaussianAffine m a z i ∧
      ∀ j, gaussianAffine m a z j ≤ gaussianAffine m a z i := by
  obtain ⟨i, _, he, hi⟩ := isCompact_univ.exists_sSup_image_eq_and_ge
    Set.univ_nonempty (continuous_gaussianAffine hm ha z).continuousOn
  exact ⟨i, by simpa [gaussianSup] using he, fun j => hi j (Set.mem_univ _)⟩

theorem gaussianSup_le {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : κ → ℝ) {c : ℝ}
    (hc : ∀ i, gaussianAffine m a z i ≤ c) : gaussianSup m a z ≤ c := by
  obtain ⟨i, he, _⟩ := gaussianSup_attained hm ha z
  rw [he]
  exact hc i

omit [Nonempty I] in
 theorem continuous_gaussianSup {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) : Continuous (gaussianSup m a) := by
  have hc : Continuous (fun p : (κ → ℝ) × I => gaussianAffine m a p.1 p.2) := by
    exact (hm.comp continuous_snd).add (continuous_finsetSum _ (fun k _ =>
      (((continuous_apply k).comp ha).comp continuous_snd).mul
        ((continuous_apply k).comp continuous_fst)))
  change Continuous (fun z => sSup (Set.range (gaussianAffine m a z)))
  simpa only [Set.image_univ] using isCompact_univ.continuous_sSup hc

theorem integrable_gaussianSup {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) :
    Integrable (gaussianSup m a) (gaussianCoordinates κ) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hm.continuousOn
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
  have hMb : ∀ i, |m i| ≤ M := fun i => by
    simpa only [Real.norm_eq_abs] using hM i (Set.mem_univ _)
  have hAb : ∀ i k, |a i k| ≤ A := by
    intro i k
    have hk : |a i k| ≤ ‖a i‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (a i) k
    exact hk.trans (hA i (Set.mem_univ _))
  apply ((integrable_const M).add ((integrable_finsetSum (Finset.univ : Finset κ) (fun k _ =>
    ((integrable_eval (i := k) IsGaussian.integrable_id).norm))).const_mul A)).mono'
    (continuous_gaussianSup hm ha).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨i, he, _⟩ := gaussianSup_attained hm ha z
  rw [he, Real.norm_eq_abs]
  change |gaussianAffine m a z i| ≤ M + A * ∑ k, |z k|
  calc
    _ ≤ |m i| + |∑ k, a i k * z k| := abs_add_le _ _
    _ ≤ M + ∑ k, |a i k * z k| :=
      add_le_add (hMb i) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ M + ∑ k, A * |z k| := by
      gcongr with k
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hAb i k) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem gaussianSup_comparison [Nonempty κ] {m : I → ℝ} {a b : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (hb : Continuous b)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2) :
    (∫ z, gaussianSup m b z ∂gaussianCoordinates κ) ≤
      ∫ z, gaussianSup m a z ∂gaussianCoordinates κ := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := κ))
  let e : Fin (n + 1) ≃ κ := (finCongr hn.symm).trans (Fintype.equivFin κ).symm
  let E := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let a' : I → Fin (n + 1) → ℝ := fun i k => a i (e k)
  let b' : I → Fin (n + 1) → ℝ := fun i k => b i (e k)
  have ha' : Continuous a' := continuous_pi (fun k => (continuous_apply (e k)).comp ha)
  have hb' : Continuous b' := continuous_pi (fun k => (continuous_apply (e k)).comp hb)
  have he (f : κ → ℝ) : ∑ k : Fin (n + 1), f (e k) = ∑ k : κ, f k := e.sum_comp f
  have horth' (i j : I) : ∑ k, (a' i k - a' j k) * (b' i k - b' j k) = 0 := by
    dsimp [a', b']
    rw [he (fun k => (a i k - a j k) * (b i k - b j k))]
    exact horth i j
  have hinc' (i j : I) : (∑ k, (b' i k - b' j k)^2) ≤ ∑ k, (a' i k - a' j k)^2 := by
    dsimp [a', b']
    rw [he (fun k => (b i k - b j k)^2), he (fun k => (a i k - a j k)^2)]
    exact hinc i j
  have hpres : MeasurePreserving E (standardGaussianProduct (n + 1)) (gaussianCoordinates κ) :=
    measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) e
  have hpoint (c : I → κ → ℝ) (z : Fin (n + 1) → ℝ) :
      gaussianSup m c (E z) = supProcess m (fun i k => c i (e k)) z := by
    unfold gaussianSup supProcess
    congr 1
    congr 1
    funext i
    dsimp [gaussianAffine, affineProcess]
    rw [← he (fun k => c i k * E z k)]
    simp [E, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  rw [← hpres.integral_comp' (gaussianSup m b), ← hpres.integral_comp' (gaussianSup m a)]
  simp_rw [hpoint]
  exact gaussian_supProcess_comparison hm ha' hb' horth' hinc'

end ArbitraryCoordinates
end SKRatioGaussian

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
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianAffineGaussianSup
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
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
namespace SKRatioGaussian
section SupLipschitz
variable {I κ : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I] [Fintype κ]

lemma gaussianAffine_le_gaussianSup {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (x : κ → ℝ) (i : I) :
    gaussianAffine m a x i ≤ gaussianSup m a x := by
  obtain ⟨j, hj, hmax⟩ := gaussianSup_attained hm ha x
  rw [hj]
  exact hmax i

lemma gaussianSup_sub_le {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) {L : ℝ}
    (hL : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) (x y : EuclideanSpace ℝ κ) :
    gaussianSup m a x.ofLp - gaussianSup m a y.ofLp ≤ L * ‖x-y‖ := by
  obtain ⟨i, hi, _⟩ := gaussianSup_attained hm ha x.ofLp
  calc
    _ ≤ gaussianAffine m a x.ofLp i - gaussianAffine m a y.ofLp i := by
      rw [hi]
      exact sub_le_sub_left (gaussianAffine_le_gaussianSup hm ha y.ofLp i) _
    _ = inner ℝ (WithLp.toLp 2 (a i)) (x-y) := by
      simp only [gaussianAffine, PiLp.inner_apply, WithLp.ofLp_sub,
        Pi.sub_apply, RCLike.inner_apply, conj_trivial]
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ ‖WithLp.toLp 2 (a i)‖ * ‖x-y‖ := real_inner_le_norm _ _
    _ ≤ L * ‖x-y‖ := mul_le_mul_of_nonneg_right (hL i) (norm_nonneg _)

theorem gaussianSup_lipschitz {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) {L : ℝ≥0}
    (hL : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ (L : ℝ)) :
    LipschitzWith L (fun x : EuclideanSpace ℝ κ => gaussianSup m a x.ofLp) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := gaussianSup_sub_le hm ha hL y x
    rw [norm_sub_rev] at h
    linarith
  · exact gaussianSup_sub_le hm ha hL x y

end SupLipschitz
end SKRatioGaussian

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
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_LipschitzNormedConvolution
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
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
namespace SKRatioGaussian

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
end SKRatioGaussian
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_StdGaussianMgfLipschitz
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
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
namespace SKRatioGaussian
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

theorem stdGaussian_upper_tail_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {x | u ≤ f x - ∫ y, f y ∂stdGaussian E} ≤
      exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) := by
  let t : ℝ := 4 * u / (π ^ 2 * (L : ℝ) ^ 2)
  have hLr : 0 < (L : ℝ) := hL
  have hden : 0 < π ^ 2 * (L : ℝ) ^ 2 := mul_pos (sq_pos_of_pos pi_pos) (sq_pos_of_pos hLr)
  have ht : 0 ≤ t := div_nonneg (mul_nonneg (by norm_num) hu) hden.le
  have hi : Integrable (fun x => exp (t * (f x - ∫ y, f y ∂stdGaussian E)))
      (stdGaussian E) := by
    simp_rw [exp_mul_sub]
    exact (gaussian_integrable_exp_lipschitz hf t).const_mul _
  calc
    _ ≤ exp (-t * u) * ∫ x, exp (t * (f x - ∫ y, f y ∂stdGaussian E))
        ∂stdGaussian E := measure_ge_le_exp_mul_mgf u ht hi
    _ ≤ exp (-t * u) * exp (π ^ 2 * t ^ 2 * (L : ℝ) ^ 2 / 8) :=
      mul_le_mul_of_nonneg_left (stdGaussian_mgf_lipschitz_le hf t) (exp_pos _).le
    _ = exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) := by
      rw [← exp_add]
      congr 1
      dsimp [t]
      field_simp
      ring

end StandardGaussianRotation
end SKRatioGaussian

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianProductUpperTailLipschitz
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
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
namespace SKRatioGaussian
section ProductGaussianConcentration
variable {κ : Type*} [Fintype κ]

theorem gaussianProduct_upper_tail_lipschitz {f : (κ → ℝ) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ κ => f x.ofLp))
    (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).real
      {x | u ≤ f x - ∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)} ≤
      Real.exp (-2*u^2/(π^2*(L:ℝ)^2)) := by
  let e : (κ → ℝ) ≃ᵐ EuclideanSpace ℝ κ := MeasurableEquiv.toLp 2 _
  have hp : MeasurePreserving e (Measure.pi (fun _ : κ => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨e.measurable, map_pi_eq_stdGaussian⟩
  have hi := hp.integral_comp' (fun x : EuclideanSpace ℝ κ => f x.ofLp)
  change (∫ x, f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) = _ at hi
  have h := stdGaussian_upper_tail_lipschitz hf hL hu
  rw [← hi] at h
  have hs : MeasurableSet {x : EuclideanSpace ℝ κ |
      u ≤ f x.ofLp - ∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)} :=
    measurableSet_le measurable_const (hf.continuous.measurable.sub_const _)
  have he := hp.measure_preimage hs.nullMeasurableSet
  have her := congrArg ENNReal.toReal he
  change (Measure.pi (fun _ : κ => gaussianReal 0 1)).real
      {x | u ≤ f x - ∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)} = _ at her
  rw [her]
  exact h

end ProductGaussianConcentration
end SKRatioGaussian

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
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianQuadratic
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
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
namespace SKRatioGaussian
open scoped BigOperators

lemma gaussian_integral_sq : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at h
  simpa only [sub_zero, NNReal.coe_one] using h

section Fluctuation
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma memLp_sqrt_of_nonneg {f : Ω → ℝ} (hf : Integrable f μ)
    (hpos : ∀ x, 0 ≤ f x) : MemLp (fun x => sqrt (f x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)).mpr
  exact hf.congr (Filter.Eventually.of_forall (fun x => (sq_sqrt (hpos x)).symm))

lemma integral_abs_le_sqrt_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ sqrt (∫ x, (f x)^2 ∂μ) := by
  have h0 := ProbabilityTheory.variance_nonneg (fun x => ‖f x‖) μ
  rw [variance_eq_sub hf.norm] at h0
  have hsq : (∫ x, |f x| ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
    simpa only [Real.norm_eq_abs, Pi.pow_apply, sq_abs, sub_nonneg] using h0
  have hi : 0 ≤ ∫ x, (f x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hh := sq_sqrt hi
  have hp := sqrt_nonneg (∫ x, (f x)^2 ∂μ)
  nlinarith [sq_nonneg ((∫ x, |f x| ∂μ) - sqrt (∫ x, (f x)^2 ∂μ))]

end Fluctuation
end SKRatioGaussian

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
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_PlantedGOE
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma constantDirection_unit (hn : 0 < n) :
    ∑ i : Fin n, constantDirection n i^2 = 1 := by
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp [constantDirection,inv_pow,sq_sqrt (Nat.cast_nonneg n),hn0]

lemma constantColumn_unit (hn : 0 < n) :
    (queryColumn (constantDirection n))ᵀ * queryColumn (constantDirection n) = 1 :=
  queryColumn_unit _ (constantDirection_unit hn)

lemma augmentedField_query (hn : 0 < n) (β : ℝ) (g : (Fin n × Fin n) → ℝ) (i : Fin n) :
    augmentedField β g i = sqrt n*β*(goe g*queryColumn (constantDirection n)) i 0+β^2 := by
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hs0 : sqrt (n:ℝ) ≠ 0 := (sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  simp only [augmentedField,augmented,Finset.sum_add_distrib,←Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Matrix.mul_apply,queryColumn,constantDirection,←Finset.sum_mul]
  field_simp

theorem field_residual_independent (hn : 0 < n) (β : ℝ) :
    IndepFun (fun g : (Fin n × Fin n) → ℝ => fun p : Fin n × Fin n =>
      (fieldProjection n*(β • goe g)*fieldProjection n) p.1 p.2)
      (augmentedField β) (standardArrayLaw (Fin n × Fin n)) := by
  have h := residual_answer_independent hn (queryColumn (constantDirection n)) (constantColumn_unit hn)
  have hc := h.comp
    (φ := fun x : (Fin n × Fin n) → ℝ => fun p => β*x p)
    (ψ := fun y : (Fin n × Fin 1) → ℝ => fun i => sqrt n*β*y (i,0)+β^2)
    (by fun_prop) (by fun_prop)
  convert! hc using 1
  · funext g p
    simp [fieldProjection]
  · funext g i
    exact augmentedField_query hn β g i

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_RandomMatrixNet
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
namespace SKRatio.MatrixNet

lemma matrix_opNorm_le_schur {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ i, ∑ j, |A i j| ≤ R) (hc : ∀ j, ∑ i, |A i j| ≤ R) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hR
  intro x y hx hy
  change inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A x) y ≤ R
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  change (∑ i, y i * ∑ j, A i j*x j) ≤ R
  simp only [Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, |A i j| * ((y i)^2 + (x j)^2)/2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hab : 2*|y i| *|x j| ≤ (y i)^2+(x j)^2 := by
        nlinarith [sq_nonneg (|y i|-|x j|), sq_abs (y i), sq_abs (x j)]
      have hp := mul_le_mul_of_nonneg_left hab (abs_nonneg (A i j))
      have hh : y i*(A i j*x j) ≤ |y i| *|A i j| *|x j| := by
        simpa only [abs_mul, mul_assoc] using le_abs_self (y i*(A i j*x j))
      nlinarith
    _ = ((∑ i, (y i)^2 * ∑ j, |A i j|) + ∑ j, (x j)^2 * ∑ i, |A i j|)/2 := by
      simp only [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
      rw [Finset.sum_comm (f := fun i j => |A i j| * (x j)^2)]
      simp only [← Finset.sum_mul]
      congr 2 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ ≤ ((∑ i, (y i)^2 * R) + ∑ j, (x j)^2*R)/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact add_le_add
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hr i) (sq_nonneg _)))
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hc i) (sq_nonneg _)))
    _ = R := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← EuclideanSpace.real_norm_sq_eq,
        ← EuclideanSpace.real_norm_sq_eq, hx, hy]
      ring

lemma matrix_diagonal_opNorm_le {n : ℕ} (d : Fin n → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hd : ∀ i, |d i| ≤ R) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal d)‖ ≤ R := by
  apply matrix_opNorm_le_schur _ R hR
  · intro i
    simpa [Matrix.diagonal, apply_ite, abs_zero] using hd i
  · intro i
    simpa [Matrix.diagonal, apply_ite, abs_zero] using hd i

end SKRatio.MatrixNet

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma sum_weighted (σ : ι → α) (f : ι → ℝ) (c : α → ℝ) :
    ∑ i, f i*c (σ i) = ∑ a, sum σ f a*c a := by
  rw [←sum_fibers σ (fun i => f i*c (σ i))]
  apply Finset.sum_congr rfl
  intro a _
  unfold sum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  change f i*c (σ i)=f i*c a
  rw [(Finset.mem_filter.mp hi).2]

lemma zero_sum_weighted {σ : ι → α} {u : ι → ℝ} (hu : ZeroSum σ u) (c : α → ℝ) :
    (∑ i, u i*c (σ i)) = 0 := by
  rw [sum_weighted]
  simp only [show ∀ a, sum σ u a=0 from hu,zero_mul,Finset.sum_const_zero]

lemma zero_sum_bilinear {σ : ι → α} {u : ι → ℝ} (hu : ZeroSum σ u)
    (z : ι → ℝ) (K : α → α → ℝ) :
    (∑ i, ∑ j, u i*z j*K (σ i) (σ j)) = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  simpa only [mul_assoc] using zero_sum_weighted hu (fun a => z j*K a (σ j))

omit [Fintype α] in
lemma overlap_le {σ : ι → α} {u z : ι → ℝ} {s : α → ℝ}
    (hu : overlap σ u u = s) (hz : overlap σ z z = s) (a : α) :
    overlap σ u z a ≤ s a := by
  have h : 0 ≤ ∑ i with σ i=a, (u i-z i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (∑ i with σ i=a, (u i-z i)^2) =
      overlap σ u u a+overlap σ z z a-2*overlap σ u z a := by
    unfold overlap sum
    simp only [Finset.mul_sum]
    rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,hu,hz] at h
  linarith

omit [Fintype α] [DecidableEq α] in
lemma overlap_product_bound {s q : α → ℝ} (hq : ∀ a, q a ≤ s a) (a d : α) :
    s a*s d-q a*q d ≤ s a*(s d-q d)+s d*(s a-q a) := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr (hq a)) (sub_nonneg.mpr (hq d))]

lemma double_weighted (σ : ι → α) (f g : ι → ℝ) (K : α → α → ℝ) :
    (∑ i, ∑ j, f i*g j*K (σ i) (σ j)) =
      ∑ a, ∑ d, sum σ f a*sum σ g d*K a d := by
  simp_rw [mul_assoc,←Finset.mul_sum,sum_weighted σ g]
  rw [sum_weighted σ f (fun a => ∑ d, sum σ g d*K a d)]

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

lemma matrixInner_symm (A B : Matrix ι ι ℝ) : matrixInner A B=matrixInner B A := by
  simp only [matrixInner,mul_comm]

lemma matrixInner_add_left (A B C : Matrix ι ι ℝ) :
    matrixInner (A+B) C=matrixInner A C+matrixInner B C := by
  simp [matrixInner,add_mul,Finset.sum_add_distrib]

lemma matrixInner_add_right (A B C : Matrix ι ι ℝ) :
    matrixInner A (B+C)=matrixInner A B+matrixInner A C := by
  simp [matrixInner,mul_add,Finset.sum_add_distrib]

lemma matrixInner_transpose (A B : Matrix ι ι ℝ) :
    matrixInner Aᵀ Bᵀ=matrixInner A B := by
  unfold matrixInner
  exact Finset.sum_comm

lemma matrixInner_transpose_left (A B : Matrix ι ι ℝ) :
    matrixInner Aᵀ B=matrixInner A Bᵀ := by
  simpa only [Matrix.transpose_transpose] using matrixInner_transpose A Bᵀ

lemma matrixInner_sq_sub (A B : Matrix ι ι ℝ) :
    (∑ i, ∑ j, (A i j-B i j)^2)=matrixInner A A+matrixInner B B-2*matrixInner A B := by
  simp only [matrixInner,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype α] [DecidableEq α] in
lemma binVariance_nonneg (σ : ι → α) (C : α → α → ℝ) (a : α) :
    0 ≤ binVariance σ C a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma linearMatrix_inner (σ : ι → α) (C : α → α → ℝ) (u z : ι → ℝ) :
    matrixInner (linearMatrix σ C u) (linearMatrix σ C z) =
      ∑ a, overlap σ u z a*binVariance σ C a := by
  unfold matrixInner linearMatrix
  have he (i j : ι) : u i*C (σ i) (σ j)*(z i*C (σ i) (σ j)) =
      (u i*z i)*C (σ i) (σ j)^2 := by ring
  simp_rw [he,←Finset.mul_sum]
  exact sum_weighted σ (fun i => u i*z i) (binVariance σ C)

lemma linearMatrix_cross_zero {σ : ι → α} (C : α → α → ℝ) {u : ι → ℝ}
    (hu : ZeroSum σ u) (z : ι → ℝ) :
    matrixInner (linearMatrix σ C u) (linearMatrix σ C z)ᵀ=0 := by
  unfold matrixInner linearMatrix
  change (∑ i, ∑ j, u i*C (σ i) (σ j)*(z j*C (σ j) (σ i)))=0
  convert zero_sum_bilinear hu z (fun a d => C a d*C d a) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma quadraticMatrix_transpose (σ : ι → α) (K : α → α → ℝ)
    (hK : ∀ a d, K a d=K d a) (u : ι → ℝ) : (quadraticMatrix σ K u)ᵀ=quadraticMatrix σ K u := by
  ext i j
  simp only [quadraticMatrix,Matrix.transpose_apply,hK (σ j) (σ i)]
  ring

lemma linear_quadratic_inner_zero {σ : ι → α} (C K : α → α → ℝ) (u : ι → ℝ)
    {z : ι → ℝ} (hz : ZeroSum σ z) :
    matrixInner (linearMatrix σ C u) (quadraticMatrix σ K z)=0 := by
  unfold matrixInner linearMatrix quadraticMatrix
  apply Finset.sum_eq_zero
  intro i _
  convert zero_sum_weighted hz (fun d => u i*z i*C (σ i) d*K (σ i) d) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadraticMatrix_inner (σ : ι → α) (K : α → α → ℝ) (u z : ι → ℝ) :
    matrixInner (quadraticMatrix σ K u) (quadraticMatrix σ K z)=
      ∑ a, ∑ d, K a d^2*overlap σ u z a*overlap σ u z d := by
  have he (i j : ι) : (K (σ i) (σ j)*u i*u j)*(K (σ i) (σ j)*z i*z j)=
      (u i*z i)*(u j*z j)*K (σ i) (σ j)^2 := by ring
  unfold matrixInner quadraticMatrix
  simp_rw [he]
  rw [double_weighted σ (fun i => u i*z i) (fun i => u i*z i) (fun a d => K a d^2)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  change overlap σ u z a*overlap σ u z d*K a d^2= _
  ring

lemma residualMatrix_inner {σ : ι → α} (C K : α → α → ℝ)
    (hK : ∀ a d, K a d=K d a) {u z : ι → ℝ}
    (hu : ZeroSum σ u) (hz : ZeroSum σ z) :
    matrixInner (residualMatrix σ C K u) (residualMatrix σ C K z)=
      2*(∑ a, overlap σ u z a*binVariance σ C a)+
        ∑ a, ∑ d, K a d^2*overlap σ u z a*overlap σ u z d := by
  unfold residualMatrix
  simp only [matrixInner_add_left,matrixInner_add_right]
  rw [matrixInner_transpose_left _ (quadraticMatrix σ K z),quadraticMatrix_transpose σ K hK z]
  rw [matrixInner_symm (quadraticMatrix σ K u) _,matrixInner_symm (quadraticMatrix σ K u) _]
  rw [matrixInner_transpose_left _ (quadraticMatrix σ K u),quadraticMatrix_transpose σ K hK u]
  simp only [linearMatrix_cross_zero C hu,linear_quadratic_inner_zero C K u hz,
    linear_quadratic_inner_zero C K z hu,matrixInner_transpose_left,Matrix.transpose_transpose,
    linearMatrix_inner,quadraticMatrix_inner,add_zero,zero_add]
  ring

lemma residualMatrix_increment {σ : ι → α} (C K : α → α → ℝ)
    (hK : ∀ a d, K a d=K d a) {u z : ι → ℝ} {s : α → ℝ}
    (hu : ZeroSum σ u) (hz : ZeroSum σ z)
    (hus : overlap σ u u=s) (hzs : overlap σ z z=s) :
    (∑ i, ∑ j, (residualMatrix σ C K u i j-residualMatrix σ C K z i j)^2) ≤
      4*∑ a, (s a-overlap σ u z a)*(binVariance σ C a+∑ d, K a d^2*s d) := by
  rw [matrixInner_sq_sub,residualMatrix_inner C K hK hu hu,
    residualMatrix_inner C K hK hz hz,residualMatrix_inner C K hK hu hz,hus,hzs]
  let q := overlap σ u z
  have hq : ∀ a, q a ≤ s a := overlap_le hus hzs
  have hineq : (∑ a, ∑ d, K a d^2*(s a*s d-q a*q d)) ≤
      ∑ a, ∑ d, K a d^2*(s a*(s d-q d)+s d*(s a-q a)) := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro d _
    exact mul_le_mul_of_nonneg_left (overlap_product_bound hq a d) (sq_nonneg _)
  have he : (∑ a, ∑ d, K a d^2*(s a*(s d-q d)+s d*(s a-q a))) =
      2*∑ a, (s a-q a)*(∑ d, K a d^2*s d) := by
    simp only [mul_add,Finset.sum_add_distrib]
    have hs : (∑ a, ∑ d, K a d^2*(s a*(s d-q d))) =
        ∑ a, ∑ d, K a d^2*(s d*(s a-q a)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro d _
      rw [hK d a]
    rw [hs]
    rw [two_mul]
    congr 1 <;> apply Finset.sum_congr rfl
    all_goals
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
  rw [he] at hineq
  have he1 : (∑ a, ∑ d, K a d^2*(s a*s d-q a*q d)) =
      (∑ a, ∑ d, K a d^2*s a*s d)-(∑ a, ∑ d, K a d^2*q a*q d) := by
    simp only [mul_sub,Finset.sum_sub_distrib,mul_assoc]
  have he2 : (∑ a, (s a-q a)*(binVariance σ C a+∑ d, K a d^2*s d)) =
      (∑ a, s a*binVariance σ C a)-(∑ a, q a*binVariance σ C a)+
        ∑ a, (s a-q a)*(∑ d, K a d^2*s d) := by
    simp only [mul_add,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [he1] at hineq
  change _ ≤ 4*∑ a, (s a-q a)*(binVariance σ C a+∑ d, K a d^2*s d)
  rw [he2]
  dsimp only [q] at hineq
  dsimp only [q]
  linarith only [hineq]

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinParameters
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [DecidableEq α]
attribute [local instance] Classical.propDecidable

variable [Fintype α]

omit [DecidableEq α] in
lemma parameterSet_compact : IsCompact (ParameterSet α) := by
  have hc : IsClosed {z : ParameterSpace α | ∀ a, 0≤z (.inr a)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    exact isClosed_le continuous_const (EuclideanSpace.proj (Sum.inr a : α ⊕ α)).continuous
  simpa only [ParameterSet,Metric.sphere,dist_zero_right,Set.ofPred_and] using
    (isCompact_sphere (0 : ParameterSpace α) 1).inter_right hc

instance instCompactSpaceParameters : CompactSpace (Parameters α) := isCompact_iff_compactSpace.mp parameterSet_compact

omit [DecidableEq α] in
lemma paramR_nonneg (z : Parameters α) (a : α) : 0≤paramR z a := z.property.2 a

omit [DecidableEq α] in
lemma param_sum_sq (z : Parameters α) : (∑ a, ((paramB z a)^2+(paramR z a)^2))=1 := by
  have hh := EuclideanSpace.real_norm_sq_eq z.val
  rw [z.property.1] at hh
  simpa only [one_pow,Fintype.sum_sum_type,Finset.sum_add_distrib,paramB,paramR] using hh.symm

omit [DecidableEq α] in
theorem parameters_finite_net {η : ℝ} (hη : 0<η) :
    ∃ F : Finset (Parameters α), ∀ z : Parameters α,
      ∃ z' ∈ F, ‖z.val-z'.val‖<η := by
  have hcover : (Set.univ : Set (Parameters α)) ⊆ ⋃ z : Parameters α, Metric.ball z η := by
    intro z _
    exact Set.mem_iUnion.mpr ⟨z,by simpa using hη⟩
  obtain ⟨s,hs,hsfin,hscov⟩ := isCompact_univ.elim_finite_subcover_image
    (b := (Set.univ : Set (Parameters α))) (c := fun z => Metric.ball z η)
    (fun z _ => Metric.isOpen_ball) (by simpa using hcover)
  refine ⟨hsfin.toFinset,fun z => ?_⟩
  have hz := hscov (Set.mem_univ z)
  obtain ⟨z',hz',hd⟩ := Set.mem_iUnion₂.mp hz
  exact ⟨z',by simpa using hz',by simpa only [Metric.mem_ball,Subtype.dist_eq,dist_eq_norm] using hd⟩

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinDirections
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma sum_scale_bin (σ : ι → α) (c : α → ℝ) (u : ι → ℝ) (a : α) :
    sum σ (fun i => c (σ i)*u i) a = c a*sum σ u a := by
  unfold sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only []
  rw [(Finset.mem_filter.mp hi).2]

lemma zeroSum_scale_bin {σ : ι → α} (c : α → ℝ) {u : ι → ℝ} (hu : ZeroSum σ u) :
    ZeroSum σ (fun i => c (σ i)*u i) := by
  intro a
  rw [sum_scale_bin,hu a,mul_zero]

lemma overlap_scale_bin (σ : ι → α) (c : α → ℝ) (u : ι → ℝ) (a : α) :
    overlap σ (fun i => c (σ i)*u i) (fun i => c (σ i)*u i) a =
      c a^2*overlap σ u u a := by
  have he : (fun i => (c (σ i)*u i)*(c (σ i)*u i)) =
      fun i => c (σ i)^2*(u i*u i) := by ext i; ring
  rw [overlap,he,sum_scale_bin σ (fun a => c a^2)]
  rfl

lemma directions_zeroSum {σ : ι → α} (u : Directions σ) : ZeroSum σ u.val :=
  fun a => (u.property a).1

lemma directions_overlap {σ : ι → α} (u : Directions σ) (a : α) :
    overlap σ u.val u.val a=1 := (u.property a).2

variable [Fintype α]

lemma directions_norm_sq {σ : ι → α} (u : Directions σ) : ‖u.val‖^2=(Fintype.card α:ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq,←sum_fibers σ]
  have he (a : α) : sum σ (fun i => u.val i^2) a=1 := by
    simpa only [pow_two,overlap] using directions_overlap u a
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

omit [Fintype α] in
lemma directionSet_closed (σ : ι → α) : IsClosed (DirectionSet σ) := by
  simp only [DirectionSet,Set.ofPred_forall,Set.ofPred_and]
  apply isClosed_iInter
  intro a
  apply IsClosed.inter <;> apply isClosed_eq _ continuous_const
  · exact continuous_finsetSum _ (fun i _ => (EuclideanSpace.proj i).continuous)
  · exact continuous_finsetSum _ (fun i _ => (EuclideanSpace.proj i).continuous.mul
      (EuclideanSpace.proj i).continuous)

lemma directionSet_compact (σ : ι → α) : IsCompact (DirectionSet σ) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ ι) (sqrt (Fintype.card α))).of_isClosed_subset
    (directionSet_closed σ)
  intro u hu
  simp only [Metric.mem_closedBall,dist_zero_right]
  have hs := directions_norm_sq (⟨u,hu⟩ : Directions σ)
  exact (le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)).mpr hs.le

instance instCompactSpaceDirections (σ : ι → α) : CompactSpace (Directions σ) := isCompact_iff_compactSpace.mp (directionSet_compact σ)

omit [Fintype α] in
lemma two_sites_of_count {σ : ι → α} (hcount : ∀ a, 2 ≤ count σ a) (a : α) :
    ∃ i j : ι, σ i=a ∧ σ j=a ∧ i≠j := by
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (show 1<(Finset.univ.filter (fun i => σ i=a)).card from hcount a)
  exact ⟨i,j,(Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hj).2,hij⟩

omit [Fintype α] in
lemma directions_nonempty {σ : ι → α} (hcount : ∀ a, 2 ≤ count σ a) : Nonempty (Directions σ) := by
  choose i j hi hj hij using two_sites_of_count hcount
  let u : ι → ℝ := fun k => (if k=i (σ k) then 1/sqrt 2 else 0)-
    (if k=j (σ k) then 1/sqrt 2 else 0)
  refine ⟨⟨WithLp.toLp 2 u,fun a => ?_⟩⟩
  have himem : i a∈Finset.univ.filter (fun k => σ k=a) := by simp only [Finset.mem_filter,Finset.mem_univ,true_and,hi]
  have hjmem : j a∈Finset.univ.filter (fun k => σ k=a) := by simp only [Finset.mem_filter,Finset.mem_univ,true_and,hj]
  have hue (k : ι) (hk : k∈Finset.univ.filter (fun k => σ k=a)) :
      u k = (if k=i a then 1/sqrt 2 else 0)-(if k=j a then 1/sqrt 2 else 0) := by
    dsimp only [u]
    rw [(Finset.mem_filter.mp hk).2]
  constructor
  · change (∑ k with σ k=a, u k)=0
    rw [Finset.sum_congr rfl hue,Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq',himem,hjmem,ite_true, if_true,sub_self]
  · change (∑ k with σ k=a, u k*u k)=1
    have hh (k : ι) (hk : k∈Finset.univ.filter (fun k => σ k=a)) :
        u k*u k=(if k=i a then (1:ℝ)/2 else 0)+(if k=j a then (1:ℝ)/2 else 0) := by
      rw [hue k hk]
      split_ifs with hki hkj
      · exact False.elim (hij a (hki.symm.trans hkj))
      · simp only [sub_zero,←pow_two,div_pow,one_pow,sq_sqrt (show (0:ℝ)≤2 by norm_num),add_zero]
      · simp only [zero_sub,←pow_two,neg_sq,div_pow,one_pow,sq_sqrt (show (0:ℝ)≤2 by norm_num),zero_add]
      · ring
    rw [Finset.sum_congr rfl hh,Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',himem,hjmem,ite_true, if_true]
    norm_num

lemma vectorOf_unit {σ : ι → α} (hcount : ∀ a, 0 < count σ a)
    (z : Parameters α) (u : Directions σ) : ∑ i, vectorOf z u i^2=1 := by
  rw [←sum_fibers σ]
  have he (a : α) : sum σ (fun i => vectorOf z u i^2) a =
      (paramB z a)^2+(paramR z a)^2 := by
    simp only [vectorOf]
    rw [bin_orthogonal_decomposition (zeroSum_scale_bin (paramR z) (directions_zeroSum u))
      (fun a => paramB z a/sqrt (count σ a:ℝ)) a,
      overlap_scale_bin,directions_overlap,mul_one,div_pow,sq_sqrt (Nat.cast_nonneg _)]
    congr 1
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (hcount a).ne')
  simp only [he,param_sum_sq]

lemma vectorOf_continuous {σ : ι → α} (z : Parameters α) :
    Continuous (fun u : Directions σ => vectorOf z u) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (((EuclideanSpace.proj i).continuous.comp continuous_subtype_val).const_mul _)

lemma scaled_directions_continuous {σ : ι → α} (z : Parameters α) :
    Continuous (fun u : Directions σ => fun i => paramR z (σ i)*u.val i) := by
  apply continuous_pi
  intro i
  exact ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val).const_mul _

lemma vectorOf_difference {σ : ι → α} (hcount : ∀ a, 0 < count σ a)
    (z z' : Parameters α) (u : Directions σ) :
    ‖WithLp.toLp 2 (fun i => vectorOf z u i-vectorOf z' u i)‖=‖z.val-z'.val‖ := by
  have he (i : ι) : vectorOf z u i-vectorOf z' u i=
      (paramB z (σ i)-paramB z' (σ i))/sqrt (count σ (σ i):ℝ)+
      (paramR z (σ i)-paramR z' (σ i))*u.val i := by unfold vectorOf; ring
  have hs : ‖WithLp.toLp 2 (fun i => vectorOf z u i-vectorOf z' u i)‖^2=‖z.val-z'.val‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    simp only [he,←sum_fibers σ]
    have hh (a : α) : sum σ (fun i =>
        ((paramB z (σ i)-paramB z' (σ i))/sqrt (count σ (σ i):ℝ)+
        (paramR z (σ i)-paramR z' (σ i))*u.val i)^2) a=
        (paramB z a-paramB z' a)^2+(paramR z a-paramR z' a)^2 := by
      rw [bin_orthogonal_decomposition (zeroSum_scale_bin (fun a => paramR z a-paramR z' a) (directions_zeroSum u))
        (fun a => (paramB z a-paramB z' a)/sqrt (count σ a:ℝ)) a,
        overlap_scale_bin σ (fun a => paramR z a-paramR z' a),directions_overlap,mul_one,div_pow,sq_sqrt (Nat.cast_nonneg _)]
      congr 1
      exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (hcount a).ne')
    conv_lhs =>
      arg 2
      intro a
      rw [hh a]
    simp only [Finset.sum_add_distrib,Fintype.sum_sum_type,PiLp.sub_apply,paramB,paramR]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

omit [Fintype α] in
lemma fiber_sq_le (σ : ι → α) (u : ι → ℝ) (i : ι) :
    u i^2≤overlap σ u u (σ i) := by
  simpa only [overlap,sum,pow_two] using
    Finset.single_le_sum (s := Finset.univ.filter (fun k => σ k=σ i))
      (f := fun k => u k^2) (fun k _ => sq_nonneg (u k)) (by simp)

omit [Fintype α] in
lemma fiber_zero_of_sqrt_zero {σ : ι → α} {u : ι → ℝ} {i : ι}
    (h : sqrt (overlap σ u u (σ i))=0) : u i=0 := by
  have ht : overlap σ u u (σ i)=0 := by
    simpa only [h,zero_pow (by decide : (2:ℕ)≠0)] using (sq_sqrt (overlap_self_nonneg σ u (σ i))).symm
  have hs := fiber_sq_le σ u i
  rw [ht] at hs
  exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))

theorem vectorOf_surjective {σ : ι → α} (hcount : ∀ a, 2 ≤ count σ a)
    (p : ι → ℝ) (hp : ∑ i, p i^2=1) :
    ∃ u : Directions σ, vectorOf (parametersOf σ p hp) u=p := by
  obtain ⟨u₀⟩ := directions_nonempty hcount
  let q := binCentered σ p
  let r := fun a => sqrt (overlap σ q q a)
  let u : ι → ℝ := fun i => if r (σ i)=0 then u₀.val i else (r (σ i))⁻¹*q i
  have hu : WithLp.toLp 2 u ∈ DirectionSet σ := by
    intro a
    by_cases hr : r a=0
    · have he : ∀ i∈Finset.univ.filter (fun i => σ i=a), u i=u₀.val i := by
        intro i hi
        dsimp only [u]
        rw [(Finset.mem_filter.mp hi).2,ite_eq_left hr]
      constructor
      · exact (Finset.sum_congr rfl he).trans (directions_zeroSum u₀ a)
      · exact (Finset.sum_congr rfl (fun i hi => congrArg (fun t : ℝ => t*t) (he i hi))).trans
          (directions_overlap u₀ a)
    · have he : ∀ i∈Finset.univ.filter (fun i => σ i=a), u i=(r a)⁻¹*q i := by
        intro i hi
        dsimp only [u]
        rw [(Finset.mem_filter.mp hi).2,ite_eq_right hr]
      constructor
      · change (∑ i with σ i=a, u i)=0
        rw [Finset.sum_congr rfl he,←Finset.mul_sum]
        change (r a)⁻¹*sum σ q a=0
        rw [binCentered_zeroSum σ p a,mul_zero]
      · change (∑ i with σ i=a, u i*u i)=1
        have hs (i : ι) (hi : i∈Finset.univ.filter (fun i => σ i=a)) :
            u i*u i=((r a)⁻¹)^2*(q i*q i) := by rw [he i hi]; ring
        rw [Finset.sum_congr rfl hs,←Finset.mul_sum]
        change ((r a)⁻¹)^2*overlap σ q q a=1
        rw [←sq_sqrt (overlap_self_nonneg σ q a)]
        change (r a)⁻¹^2*r a^2=1
        simpa only [inv_pow] using inv_mul_cancel₀ (pow_ne_zero 2 hr)
  refine ⟨⟨WithLp.toLp 2 u,hu⟩,?_⟩
  funext i
  simp only [vectorOf,parametersOf_B,parametersOf_R]
  have hpos : sqrt (count σ (σ i):ℝ)≠0 := (sqrt_pos.mpr (Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num) (hcount (σ i))))).ne'
  rw [mul_div_cancel_left₀ _ hpos]
  change binMean σ p (σ i)+r (σ i)*u i=p i
  rw [binCentered_decomp σ p i]
  congr 1
  by_cases hr : r (σ i)=0
  · have hqi : q i=0 := fiber_zero_of_sqrt_zero hr
    rw [hr,zero_mul]
    exact hqi.symm
  · simp only [u,ite_eq_right hr,←mul_assoc,mul_inv_cancel₀ hr,one_mul,q]

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinGaussian
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
attribute [-simp] _root_.OAI.SKRatio.Bins.parametersOf_R
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

omit [DecidableEq α] in
lemma radicalSq_nonneg (σ : ι → α) (C K : α → α → ℝ) {s : α → ℝ}
    (hs : ∀ a, 0 ≤ s a) (a : α) : 0 ≤ radicalSq σ C K s a :=
  add_nonneg (binVariance_nonneg _ _ _) (Finset.sum_nonneg (fun d _ => mul_nonneg (sq_nonneg _) (hs d)))

omit [DecidableEq α] in
lemma coeff_orthogonal (σ : ι → α) (C K : α → α → ℝ) (s : α → ℝ) (δ : ℝ)
    (u z : ι → ℝ) :
    (∑ k, (comparisonCoeff σ C K s δ u k-comparisonCoeff σ C K s δ z k)*
      (residualCoeff σ C K δ u k-residualCoeff σ C K δ z k))=0 := by
  simp [Fintype.sum_sum_type,residualCoeff,comparisonCoeff]

lemma comparisonCoeff_increment (σ : ι → α) (C K : α → α → ℝ) (δ : ℝ)
    {s : α → ℝ} (hs : ∀ a, 0 ≤ s a) {u z : ι → ℝ}
    (hu : overlap σ u u=s) (hz : overlap σ z z=s) :
    (∑ k, (comparisonCoeff σ C K s δ u k-comparisonCoeff σ C K s δ z k)^2)=
      2*δ^2*∑ a, (s a-overlap σ u z a)*radicalSq σ C K s a := by
  simp only [Fintype.sum_sum_type,comparisonCoeff,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero,zero_add]
  have he (i : ι) : (δ*sqrt (radicalSq σ C K s (σ i))*u i-δ*sqrt (radicalSq σ C K s (σ i))*z i)^2 =
      δ^2*(u i-z i)^2*radicalSq σ C K s (σ i) := by
    rw [←mul_sub,mul_pow,mul_pow,sq_sqrt (radicalSq_nonneg σ C K hs _)]
    ring
  simp_rw [he]
  rw [sum_weighted σ (fun i => δ^2*(u i-z i)^2) (radicalSq σ C K s),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hf : sum σ (fun i => δ^2*(u i-z i)^2) a =
      δ^2*(overlap σ u u a+overlap σ z z a-2*overlap σ u z a) := by
    unfold overlap sum
    simp only [mul_sub,mul_add,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hf,hu,hz]
  ring

lemma coeff_increment_le {σ : ι → α} (C K : α → α → ℝ)
    (hK : ∀ a d, K a d=K d a) (δ : ℝ) {u z : ι → ℝ} {s : α → ℝ}
    (hu : ZeroSum σ u) (hz : ZeroSum σ z)
    (hus : overlap σ u u=s) (hzs : overlap σ z z=s) :
    (∑ k, (residualCoeff σ C K δ u k-residualCoeff σ C K δ z k)^2) ≤
      ∑ k, (comparisonCoeff σ C K s δ u k-comparisonCoeff σ C K s δ z k)^2 := by
  have hs : ∀ a, 0 ≤ s a := fun a => hus ▸ overlap_self_nonneg σ u a
  rw [comparisonCoeff_increment σ C K δ hs hus hzs]
  simp only [Fintype.sum_sum_type,residualCoeff,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero,add_zero,Fintype.sum_prod_type]
  have hex : (∑ i, ∑ j, (δ/sqrt 2*residualMatrix σ C K u i j-δ/sqrt 2*residualMatrix σ C K z i j)^2) =
      (δ^2/2)*(∑ i, ∑ j, (residualMatrix σ C K u i j-residualMatrix σ C K z i j)^2) := by
    simp only [←mul_sub,mul_pow,div_pow,sq_sqrt (by norm_num : (0:ℝ)≤2),Finset.mul_sum]
  rw [hex]
  have hh := mul_le_mul_of_nonneg_left (residualMatrix_increment C K hK hu hz hus hzs)
    (show 0≤δ^2/2 by positivity)
  dsimp only [radicalSq]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma continuous_residualCoeff (σ : ι → α) (C K : α → α → ℝ) (δ : ℝ) :
    Continuous (residualCoeff σ C K δ) := by
  apply continuous_pi
  intro k
  cases k with
  | inl ij =>
    dsimp [residualCoeff,residualMatrix,linearMatrix,quadraticMatrix]
    fun_prop
  | inr i => exact continuous_const

omit [DecidableEq α] in
lemma continuous_comparisonCoeff (σ : ι → α) (C K : α → α → ℝ) (s : α → ℝ) (δ : ℝ) :
    Continuous (comparisonCoeff σ C K s δ) := by
  apply continuous_pi
  intro k
  cases k with
  | inl ij => exact continuous_const
  | inr i => exact continuous_const.mul (continuous_apply i)

omit [Fintype α] in
lemma blockNorm_memLp (σ : ι → α) (a : α) :
    MemLp (blockNorm σ a) 2 (SKRatioGaussian.gaussianCoordinates (Coordinates ι)) := by
  apply SKRatioGaussian.memLp_sqrt_of_nonneg
  · apply integrable_finsetSum
    intro i _
    exact (SKRatioClock.Regression.coordinate_hasLaw (Sum.inr i : Coordinates ι)).hasGaussianLaw.memLp_two.integrable_sq
  · intro g
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [Fintype α] in
lemma blockNorm_mean_le (σ : ι → α) (a : α) :
    (∫ g, blockNorm σ a g ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι)) ≤
      sqrt ((Finset.univ.filter (fun i => σ i=a)).card : ℝ) := by
  have h := SKRatioGaussian.integral_abs_le_sqrt_sq (blockNorm_memLp σ a)
  have he (g : Coordinates ι → ℝ) : blockNorm σ a g^2=sum σ (fun i => g (.inr i)^2) a :=
    sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  simp_rw [he,abs_of_nonneg (show 0≤blockNorm σ a _ from sqrt_nonneg _)] at h
  have hm : (∫ g, sum σ (fun i => g (.inr i)^2) a ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι)) =
      (Finset.univ.filter (fun i => σ i=a)).card := by
    change (∫ g, ∑ i with σ i=a, g (.inr i)^2 ∂SKRatioClock.Regression.standardArrayLaw (Coordinates ι)) = _
    rw [integral_finsetSum _ (fun i _ =>
      (SKRatioClock.Regression.coordinate_hasLaw (Sum.inr i : Coordinates ι)).hasGaussianLaw.memLp_two.integrable_sq)]
    have hint (i : ι) : (∫ g, g (.inr i)^2 ∂SKRatioClock.Regression.standardArrayLaw (Coordinates ι))=1 := by
      calc
        _ = ∫ x : ℝ, x^2 ∂gaussianReal 0 1 :=
          (SKRatioClock.Regression.coordinate_hasLaw (Sum.inr i : Coordinates ι)).integral_comp (by fun_prop)
        _ = 1 := SKRatioGaussian.gaussian_integral_sq
    simp only [hint,Finset.sum_const, nsmul_eq_mul,mul_one]
  rwa [hm] at h

lemma comparison_pointwise {σ : ι → α} (C K : α → α → ℝ)
    {s : α → ℝ} {δ : ℝ} (hδ : 0≤δ) {u : ι → ℝ} (hu : overlap σ u u=s)
    (g : Coordinates ι → ℝ) :
    (∑ k, comparisonCoeff σ C K s δ u k*g k) ≤
      ∑ a, δ*sqrt (radicalSq σ C K s a)*sqrt (s a)*blockNorm σ a g := by
  simp only [Fintype.sum_sum_type,comparisonCoeff,zero_mul,Finset.sum_const_zero,zero_add]
  have he : (∑ i, δ*sqrt (radicalSq σ C K s (σ i))*u i*g (.inr i)) =
      ∑ a, δ*sqrt (radicalSq σ C K s a)*sum σ (fun i => u i*g (.inr i)) a := by
    convert sum_weighted σ (fun i => u i*g (.inr i)) (fun a => δ*sqrt (radicalSq σ C K s a)) using 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · apply Finset.sum_congr rfl
      intro a _
      ring
  rw [he]
  apply Finset.sum_le_sum
  intro a _
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ.filter (fun i => σ i=a)) u (fun i => g (.inr i))
  have hsq : (∑ i with σ i=a, u i^2)=s a := by
    simpa only [overlap,sum,←pow_two] using congrFun hu a
  rw [hsq] at h
  exact (mul_le_mul_of_nonneg_left h (mul_nonneg hδ (sqrt_nonneg _))).trans_eq (by
    change δ*sqrt _*(sqrt _*blockNorm σ a g)=_
    ring)

variable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]

theorem residual_sup_expectation_le [Nonempty ι] (σ : ι → α) (C K : α → α → ℝ)
    (hK : ∀ a d, K a d=K d a) {s : α → ℝ} {δ : ℝ} (hδ : 0≤δ)
    {u : I → ι → ℝ} (huc : Continuous u) (hu0 : ∀ t, ZeroSum σ (u t))
    (hus : ∀ t, overlap σ (u t) (u t)=s) :
    (∫ g, SKRatioGaussian.gaussianSup (fun _ : I => 0) (fun t => residualCoeff σ C K δ (u t)) g
      ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι)) ≤
      ∑ a, δ*sqrt (radicalSq σ C K s a)*sqrt (s a)*
        sqrt ((Finset.univ.filter (fun i => σ i=a)).card : ℝ) := by
  let X := fun t => residualCoeff σ C K δ (u t)
  let Y := fun t => comparisonCoeff σ C K s δ (u t)
  have hX : Continuous X := (continuous_residualCoeff σ C K δ).comp huc
  have hY : Continuous Y := (continuous_comparisonCoeff σ C K s δ).comp huc
  have hcomp := SKRatioGaussian.gaussianSup_comparison (m := fun _ : I => 0)
    continuous_const hY hX (fun t r => coeff_orthogonal σ C K s δ (u t) (u r))
      (fun t r => coeff_increment_le C K hK δ (hu0 t) (hu0 r) (hus t) (hus r))
  apply hcomp.trans
  have hbound : ∀ g, SKRatioGaussian.gaussianSup (fun _ : I => 0) Y g ≤
      ∑ a, δ*sqrt (radicalSq σ C K s a)*sqrt (s a)*blockNorm σ a g := by
    intro g
    apply SKRatioGaussian.gaussianSup_le continuous_const hY
    intro t
    simpa only [SKRatioGaussian.gaussianAffine,zero_add] using comparison_pointwise C K hδ (hus t) g
  have hib : Integrable (fun g => ∑ a, δ*sqrt (radicalSq σ C K s a)*sqrt (s a)*blockNorm σ a g)
      (SKRatioGaussian.gaussianCoordinates (Coordinates ι)) := integrable_finsetSum _ (fun a _ =>
        ((blockNorm_memLp σ a).integrable (by norm_num)).const_mul _)
  apply (integral_mono (SKRatioGaussian.integrable_gaussianSup continuous_const hY) hib hbound).trans
  rw [integral_finsetSum _ (fun a _ => ((blockNorm_memLp σ a).integrable (by norm_num)).const_mul _)]
  simp only [integral_const_mul]
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (blockNorm_mean_le σ a) (by positivity)

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinProcess
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Bins.parametersOf_R
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Nonempty ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

omit [Nonempty ι] in
lemma average_add (p q : ι → ℝ) : average (fun i => p i+q i)=average p+average q := by
  simp only [average,Finset.sum_add_distrib,add_div]
omit [Nonempty ι] in
lemma average_mul (p : ι → ℝ) (c : ℝ) : average (fun i => c*p i)=c*average p := by
  simp only [average,←Finset.mul_sum,mul_div_assoc]
omit [Nonempty ι] in
lemma average_zeroSum {σ : ι → α} {u : ι → ℝ} (hu : ZeroSum σ u) : average u=0 := by
  have h := zero_sum_weighted hu (fun _ => 1)
  simpa only [mul_one, average, zero_div] using congrArg (fun z : ℝ => z/(Fintype.card ι:ℝ)) h

lemma centered_sq (p : ι → ℝ) : (∑ i, centered p i^2)=(∑ i, p i^2)-
    (Fintype.card ι:ℝ)*average p^2 := by
  have hn : (Fintype.card ι:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (∑ i, p i)=(Fintype.card ι:ℝ)*average p := by
    dsimp [average]
    field_simp
  simp only [centered,sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ←Finset.sum_mul,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [hsum]
  ring
lemma centered_sq_le (p : ι → ℝ) : (∑ i, centered p i^2)≤∑ i, p i^2 := by
  rw [centered_sq]
  exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

omit [Nonempty ι] in
lemma continuous_centered : Continuous (centered (ι := ι)) := by
  apply continuous_pi
  intro i
  exact (continuous_apply i).sub ((continuous_finsetSum _ (fun j _ => continuous_apply j)).div_const _)

omit [Nonempty ι] in
lemma continuous_fullCoeff (v : ι → ℝ) (δ : ℝ) : Continuous (fun p => fullCoeff v p δ) := by
  apply continuous_pi
  intro k
  cases k with
  | inr i => exact continuous_const
  | inl ij =>
    change Continuous (fun p => δ/sqrt 2*(centered p ij.1*centered (fun k => v k*p k) ij.2+
      centered p ij.2*centered (fun k => v k*p k) ij.1))
    have hm : Continuous (fun p : ι → ℝ => fun k => v k*p k) := by fun_prop
    exact (((continuous_apply ij.1).comp continuous_centered |>.mul
      ((continuous_apply ij.2).comp (continuous_centered.comp hm))).add
      (((continuous_apply ij.2).comp continuous_centered).mul
      ((continuous_apply ij.1).comp (continuous_centered.comp hm)))).const_mul _

omit [Nonempty ι] [Fintype α] [DecidableEq α] in
lemma crossCoeff_eq (σ : ι → α) (v b : α → ℝ) (a : α) (j : ι) :
    crossCoeff σ v b a (σ j)=centered (fun i => v (σ i)*b (σ i)) j+
      v a*centered (fun i => b (σ i)) j := by
  have he : (fun i => (v a+v (σ i))*b (σ i))=
      (fun i => v a*b (σ i)+v (σ i)*b (σ i)) := by ext i; ring
  rw [crossCoeff,he,average_add,average_mul]
  dsimp only [centered]
  ring

omit [Nonempty ι] in
lemma centered_add_zeroSum {σ : ι → α} (b : α → ℝ) {u : ι → ℝ} (hu : ZeroSum σ u) :
    centered (fun i => b (σ i)+u i)=fun i => centered (fun k => b (σ k)) i+u i := by
  ext i
  simp only [centered,average_add,average_zeroSum hu,add_zero]
  ring

omit [Nonempty ι] [Fintype α] in
lemma zeroSum_mul {σ : ι → α} (v : α → ℝ) {u : ι → ℝ} (hu : ZeroSum σ u) :
    ZeroSum σ (fun i => v (σ i)*u i) := by
  intro a
  have he : sum σ (fun i => v (σ i)*u i) a = v a*sum σ u a := by
    unfold sum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change v (σ i)*u i=v a*u i
    rw [(Finset.mem_filter.mp hi).2]
  rw [he,hu a,mul_zero]

omit [Nonempty ι] in
lemma fullCoeff_decomposition {σ : ι → α} (v b : α → ℝ) (δ : ℝ) {u : ι → ℝ}
    (hu : ZeroSum σ u) :
    fullCoeff (fun i => v (σ i)) (fun i => b (σ i)+u i) δ =
      fun k => fullCoeff (fun i => v (σ i)) (fun i => b (σ i)) δ k+
        residualCoeff σ (crossCoeff σ v b) (fun a d => v a+v d) δ u k := by
  have he : (fun i => v (σ i)*(b (σ i)+u i))=
      fun i => v (σ i)*b (σ i)+v (σ i)*u i := by ext i; ring
  have hcen := centered_add_zeroSum (fun a => v a*b a) (zeroSum_mul v hu)
  ext k
  cases k with
  | inr i => simp [fullCoeff,residualCoeff]
  | inl ij =>
    rcases ij with ⟨i,j⟩
    simp only [fullCoeff,residualCoeff,centered_add_zeroSum b hu,he,hcen,residualMatrix,
      Matrix.add_apply,Matrix.transpose_apply,linearMatrix,quadraticMatrix,crossCoeff_eq]
    ring

lemma fullCoeff_sq_le {v p : ι → ℝ} (hv : ∀ i, |v i|≤1) (δ : ℝ) :
    (∑ k, fullCoeff v p δ k^2) ≤ 2*δ^2*(∑ i, p i^2)^2 := by
  let x := centered p
  let y := centered (fun i => v i*p i)
  have hx : (∑ i, x i^2)≤∑ i, p i^2 := centered_sq_le p
  have hy : (∑ i, y i^2)≤∑ i, p i^2 := (centered_sq_le _).trans (by
    apply Finset.sum_le_sum
    intro i _
    have hvi : v i^2≤1 := (sq_le_one_iff_abs_le_one (v i)).mpr (hv i)
    simpa only [mul_pow,one_mul] using mul_le_mul_of_nonneg_right hvi (sq_nonneg (p i)))
  have hprod : (∑ i, x i^2)*(∑ j, y j^2)≤(∑ i, p i^2)^2 := by
    rw [pow_two]
    exact mul_le_mul hx hy (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hsq : (∑ i, ∑ j, (x i*y j+x j*y i)^2)≤4*((∑ i, x i^2)*(∑ j, y j^2)) := by
    calc
      _ ≤ ∑ i, ∑ j, 2*((x i*y j)^2+(x j*y i)^2) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        nlinarith only [sq_nonneg (x i*y j-x j*y i)]
      _ = _ := by
        simp only [mul_add,mul_pow,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
        ring
  simp only [Fintype.sum_sum_type,fullCoeff,zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero,add_zero,Fintype.sum_prod_type,mul_pow,div_pow,
    sq_sqrt (by norm_num : (0:ℝ)≤2),←Finset.mul_sum]
  change δ^2/2*(∑ i, ∑ j, (x i*y j+x j*y i)^2)≤_
  have h := mul_le_mul_of_nonneg_left (hsq.trans (mul_le_mul_of_nonneg_left hprod (by norm_num)))
    (show 0≤δ^2/2 by positivity)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

lemma fullCoeff_norm_le {v p : ι → ℝ} (hv : ∀ i, |v i|≤1) {δ : ℝ} (hδ : 0≤δ)
    (hp : ∑ i, p i^2=1) : ‖WithLp.toLp 2 (fullCoeff v p δ)‖≤ sqrt 2*δ := by
  have h := fullCoeff_sq_le (p := p) hv δ
  rw [hp] at h
  have he : ‖WithLp.toLp 2 (fullCoeff v p δ)‖^2=∑ k, fullCoeff v p δ k^2 := by
    simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  have hs := sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hpos : 0≤ sqrt 2*δ := mul_nonneg (sqrt_nonneg _) hδ
  apply (sq_le_sq₀ (norm_nonneg _) hpos).mp
  rw [mul_pow,hs,he]
  simpa only [one_pow,mul_one] using h

section Translation
variable {κ I : Type*} [Fintype κ] [TopologicalSpace I] [CompactSpace I] [Nonempty I]

lemma gaussianSup_add_common {a : I → κ → ℝ} (ha : Continuous a) (c : κ → ℝ)
    (g : κ → ℝ) :
    SKRatioGaussian.gaussianSup (fun _ : I => 0) (fun t k => c k+a t k) g =
      (∑ k, c k*g k)+SKRatioGaussian.gaussianSup (fun _ : I => 0) a g := by
  have hac : Continuous (fun t k => c k+a t k) := continuous_const.add ha
  have he (t : I) : SKRatioGaussian.gaussianAffine (fun _ : I => 0) (fun t k => c k+a t k) g t =
      (∑ k, c k*g k)+SKRatioGaussian.gaussianAffine (fun _ : I => 0) a g t := by
    simp only [SKRatioGaussian.gaussianAffine,add_mul,Finset.sum_add_distrib,zero_add]
  apply le_antisymm
  · apply SKRatioGaussian.gaussianSup_le continuous_const hac
    intro t
    rw [he]
    exact add_le_add le_rfl (SKRatioGaussian.gaussianAffine_le_gaussianSup continuous_const ha g t)
  · obtain ⟨t, ht, _⟩ := SKRatioGaussian.gaussianSup_attained continuous_const ha g
    rw [ht,←he]
    exact SKRatioGaussian.gaussianAffine_le_gaussianSup continuous_const hac g t

lemma integral_gaussianSup_add_common {a : I → κ → ℝ} (ha : Continuous a) (c : κ → ℝ) :
    (∫ g, SKRatioGaussian.gaussianSup (fun _ : I => 0) (fun t k => c k+a t k) g
      ∂SKRatioGaussian.gaussianCoordinates κ) =
      ∫ g, SKRatioGaussian.gaussianSup (fun _ : I => 0) a g ∂SKRatioGaussian.gaussianCoordinates κ := by
  have hi (k : κ) : Integrable (fun g : κ → ℝ => c k*g k) (SKRatioGaussian.gaussianCoordinates κ) :=
    ((SKRatioClock.Regression.coordinate_hasLaw k).hasGaussianLaw.integrable).const_mul _
  simp_rw [gaussianSup_add_common ha c]
  rw [integral_add (integrable_finsetSum _ (fun k _ => hi k))
    (SKRatioGaussian.integrable_gaussianSup continuous_const ha),
    integral_finsetSum _ (fun k _ => hi k)]
  have hm (k : κ) : (∫ g : κ → ℝ, c k*g k ∂SKRatioGaussian.gaussianCoordinates κ)=0 := by
    rw [integral_const_mul]
    change c k*(∫ g : κ → ℝ, g k ∂SKRatioClock.Regression.standardArrayLaw κ)=0
    rw [SKRatioClock.Regression.coordinate_mean,mul_zero]
  simp only [hm,Finset.sum_const_zero,zero_add]
end Translation

variable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]

theorem full_sup_expectation_le (σ : ι → α) (v b : α → ℝ)
    {s : α → ℝ} {δ : ℝ} (hδ : 0≤δ) {u : I → ι → ℝ}
    (huc : Continuous u) (hu0 : ∀ t, ZeroSum σ (u t))
    (hus : ∀ t, overlap σ (u t) (u t)=s) :
    (∫ g, SKRatioGaussian.gaussianSup (fun _ : I => 0)
      (fun t => fullCoeff (fun i => v (σ i)) (fun i => b (σ i)+u t i) δ) g
      ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι)) ≤
      ∑ a, δ*sqrt (radicalSq σ (crossCoeff σ v b) (fun a d => v a+v d) s a)*
        sqrt (s a)*sqrt ((Finset.univ.filter (fun i => σ i=a)).card : ℝ) := by
  have hd (t : I) := fullCoeff_decomposition v b δ (hu0 t)
  simp_rw [hd]
  have hi := integral_gaussianSup_add_common
    ((continuous_residualCoeff σ (crossCoeff σ v b) (fun a d => v a+v d) δ).comp huc)
    (fullCoeff (fun i => v (σ i)) (fun i => b (σ i)) δ)
  exact hi.trans_le (residual_sup_expectation_le σ _ _ (fun a d => add_comm _ _) hδ huc hu0 hus)

theorem full_sup_lipschitz (v : ι → ℝ) (hv : ∀ i, |v i|≤1)
    {δ : ℝ} (hδ : 0≤δ) {p : I → ι → ℝ} (hpc : Continuous p)
    (hp : ∀ t, ∑ i, p t i^2=1) :
    LipschitzWith ⟨sqrt 2*δ,by positivity⟩
      (fun g : EuclideanSpace ℝ (Coordinates ι) =>
        SKRatioGaussian.gaussianSup (fun _ : I => 0) (fun t => fullCoeff v (p t) δ) g.ofLp) := by
  apply SKRatioGaussian.gaussianSup_lipschitz continuous_const ((continuous_fullCoeff v δ).comp hpc)
  intro t
  exact fullCoeff_norm_le hv hδ (hp t)

theorem full_sup_tail (σ : ι → α) (v b : α → ℝ) (hv : ∀ a, |v a|≤1)
    {s : α → ℝ} {δ : ℝ} (hδ : 0<δ) {u : I → ι → ℝ}
    (huc : Continuous u) (hu0 : ∀ t, ZeroSum σ (u t))
    (hus : ∀ t, overlap σ (u t) (u t)=s)
    (hp : ∀ t, ∑ i, (b (σ i)+u t i)^2=1) {a : ℝ} (ha : 0≤a) :
    (SKRatioGaussian.gaussianCoordinates (Coordinates ι)).real {g |
      (∑ d, δ*sqrt (radicalSq σ (crossCoeff σ v b) (fun a d => v a+v d) s d)*
        sqrt (s d)*sqrt ((Finset.univ.filter (fun i => σ i=d)).card : ℝ))+a ≤
      SKRatioGaussian.gaussianSup (fun _ : I => 0)
        (fun t => fullCoeff (fun i => v (σ i)) (fun i => b (σ i)+u t i) δ) g} ≤
      exp (-a^2/(π^2*δ^2)) := by
  let p : I → ι → ℝ := fun t i => b (σ i)+u t i
  have hpc : Continuous p := continuous_const.add huc
  let f := SKRatioGaussian.gaussianSup (fun _ : I => 0)
    (fun t => fullCoeff (fun i => v (σ i)) (p t) δ)
  have hL : (0:ℝ≥0) < ⟨sqrt 2*δ,by positivity⟩ := by
    change (0:ℝ) < sqrt 2*δ
    positivity
  have hc := SKRatioGaussian.gaussianProduct_upper_tail_lipschitz
    (full_sup_lipschitz _ (fun i => hv (σ i)) hδ.le hpc hp) hL ha
  have he := full_sup_expectation_le σ v b hδ.le huc hu0 hus
  have hsub : {g | (∑ d, δ*sqrt (radicalSq σ (crossCoeff σ v b) (fun a d => v a+v d) s d)*
        sqrt (s d)*sqrt ((Finset.univ.filter (fun i => σ i=d)).card : ℝ))+a ≤ f g} ⊆
      {g | a ≤ f g-∫ y, f y ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι)} := by
    intro g hg
    change _+a≤f g at hg
    change (∫ y, f y ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι))≤_ at he
    change a≤f g-(∫ y, f y ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι))
    linarith only [hg,he]
  have hcont : Continuous f := SKRatioGaussian.continuous_gaussianSup continuous_const
    ((continuous_fullCoeff _ _).comp hpc)
  apply (measureReal_mono hsub).trans
  convert hc using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  apply congrArg Real.exp
  change -a^2/(π^2*δ^2) = -2*a^2/(π^2*(sqrt 2*δ)^2)
  rw [mul_pow,sq_sqrt (by norm_num : (0:ℝ)≤2)]
  ring

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma v_pos (h : ℝ) : 0 < v h := sub_pos.mpr (tanh_sq_lt_one h)
lemma v_le_one (h : ℝ) : v h ≤ 1 := by dsimp [v]; nlinarith [sq_nonneg (m h)]
end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_CompactField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus

lemma compactV_weight (h : ℝ) : compactV (compactWeight h) = v h := by
  unfold compactV compactWeight w v
  dsimp
  ring

lemma compactF_weight (h t : ℝ) : compactF (compactWeight h,compactWeight t) =
    v t^2/(w h+w t) := by
  unfold compactF
  simp only [compactWeight_coe,←mul_pow]
  rw [show w t*(2-w t)=v t from compactV_weight t]

lemma compactK_weight (h t : ℝ) : compactK (compactWeight h,compactWeight t) =
    kernel h t := by
  unfold compactK kernel
  rw [compactV_weight,compactV_weight]
  rfl

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_FormAlgebra
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma quadratic_inner (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    quadratic A p = inner ℝ (WithLp.toLp 2 p)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A (WithLp.toLp 2 p)) := by
  rw [Matrix.inner_toEuclideanCLM]
  simp only [quadratic,dotProduct,Matrix.mulVec,Finset.mul_sum]
  congr 1
  ext i
  apply Finset.sum_congr rfl
  intro j _
  ring

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinProjected
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Bins.parametersOf_R
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression Scalar
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma fieldProjection_apply (i j : Fin n) :
    fieldProjection n i j = (if i=j then 1 else 0)-(n:ℝ)⁻¹ := by
  simp only [fieldProjection,residualProjection,Matrix.sub_apply,Matrix.one_apply,
    Matrix.mul_apply,Matrix.transpose_apply,queryColumn,constantDirection,Fin.sum_univ_one]
  congr 1
  rw [←mul_inv_rev,←pow_two,sq_sqrt (Nat.cast_nonneg n)]

lemma fieldProjection_symmetric : (fieldProjection n)ᵀ=fieldProjection n := by
  ext i j
  simp only [Matrix.transpose_apply,fieldProjection_apply,eq_comm]

lemma fieldProjection_mulVec (p : Fin n → ℝ) :
    fieldProjection n *ᵥ p = Bins.centered p := by
  ext i
  simp only [Matrix.mulVec,dotProduct,fieldProjection_apply,sub_mul,Finset.sum_sub_distrib,
    ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true,
    ←Finset.mul_sum,Bins.centered,Bins.average,Fintype.card_fin,div_eq_mul_inv]
  ring

lemma fieldProjection_vecMul (p : Fin n → ℝ) :
    p ᵥ* fieldProjection n = Bins.centered p := by
  rw [←fieldProjection_symmetric,Matrix.vecMul_transpose,fieldProjection_mulVec]

lemma projected_bilinear (M : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n → ℝ) :
    p ⬝ᵥ ((fieldProjection n*M*fieldProjection n)*ᵥ q) =
      Bins.centered p ⬝ᵥ (M*ᵥ Bins.centered q) := by
  rw [←Matrix.mulVec_mulVec,fieldProjection_mulVec,←Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec,fieldProjection_vecMul]

lemma fullCoeff_goe (β : ℝ) (v p : Fin n → ℝ)
    (g : Bins.Coordinates (Fin n) → ℝ) :
    (∑ k, Bins.fullCoeff v p (β/sqrt n) k*g k) =
      p ⬝ᵥ ((fieldProjection n*(β • goe (fun ij => g (.inl ij)))*fieldProjection n)*ᵥ
        (fun i => v i*p i)) := by
  rw [projected_bilinear]
  simp only [Fintype.sum_sum_type,Bins.fullCoeff,zero_mul,Finset.sum_const_zero,add_zero,
    Fintype.sum_prod_type,dotProduct,Matrix.mulVec,Matrix.smul_apply,smul_eq_mul,goe,
    Finset.mul_sum]
  have hs : sqrt (2*(n:ℝ))=sqrt 2*sqrt n := sqrt_mul (by norm_num) _
  rw [hs]
  let x := Bins.centered p
  let y := Bins.centered (fun i => v i*p i)
  change (∑ i, ∑ j, β/sqrt n/sqrt 2*(x i*y j+x j*y i)*g (.inl (i,j))) =
    ∑ i, ∑ j, x i*(β*((g (.inl (i,j))+g (.inl (j,i)))/(sqrt 2*sqrt n))*y j)
  have he (i j : Fin n) : β/sqrt n/sqrt 2*(x i*y j+x j*y i)*g (.inl (i,j)) =
      β/(sqrt 2*sqrt n)*(x i*y j*g (.inl (i,j))+x j*y i*g (.inl (i,j))) := by ring
  simp_rw [he,mul_add,Finset.sum_add_distrib,←Finset.mul_sum]
  have hswap : (∑ i, ∑ j, x j*y i*g (.inl (i,j)))=
      ∑ i, ∑ j, x i*y j*g (.inl (j,i)) := Finset.sum_comm
  rw [hswap]
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end SKRatio.Planted

namespace SKRatio.Bins
open SKRatioClock.Regression Planted
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]

lemma inl_array_hasLaw :
    HasLaw (fun g : Coordinates (Fin n) → ℝ => fun ij : Fin n × Fin n => g (.inl ij))
      (standardArrayLaw (Fin n × Fin n)) (SKRatioGaussian.gaussianCoordinates (Coordinates (Fin n))) := by
  exact iIndepFun.hasLaw_pi (fun ij => coordinate_hasLaw (Sum.inl ij : Coordinates (Fin n)))
    (iIndepFun.precomp Sum.inl_injective coordinates_independent)

omit [TopologicalSpace I] [CompactSpace I] [Nonempty I] in
lemma projectedSup_eq (β : ℝ) (v : Fin n → ℝ) (p : I → Fin n → ℝ)
    (g : Coordinates (Fin n) → ℝ) :
    projectedSup β v p (fun ij => g (.inl ij)) =
      SKRatioGaussian.gaussianSup (fun _ : I => 0) (fun t => fullCoeff v (p t) (β/sqrt n)) g := by
  unfold projectedSup SKRatioGaussian.gaussianSup
  congr 2
  funext t
  simp only [SKRatioGaussian.gaussianAffine,zero_add,fullCoeff_goe]

omit [Nonempty I] in
lemma projectedSup_continuous [Nonempty (Fin n)] (β : ℝ) (v : Fin n → ℝ)
    {p : I → Fin n → ℝ} (hp : Continuous p) : Continuous (projectedSup β v p) := by
  have he : projectedSup β v p = fun g =>
      SKRatioGaussian.gaussianSup (fun _ : I => 0) (fun t => fullCoeff v (p t) (β/sqrt n))
        (Sum.elim g (fun _ => 0)) := by
    ext g
    exact projectedSup_eq β v p (Sum.elim g (fun _ => 0))
  rw [he]
  apply (SKRatioGaussian.continuous_gaussianSup continuous_const ((continuous_fullCoeff v _).comp hp)).comp
  apply continuous_pi
  intro k
  cases k with
  | inl ij => exact continuous_apply ij
  | inr i => exact continuous_const

lemma le_projectedSup [Nonempty (Fin n)] (β : ℝ) (v : Fin n → ℝ) {p : I → Fin n → ℝ}
    (hp : Continuous p) (g : (Fin n × Fin n) → ℝ) (t : I) :
    p t ⬝ᵥ ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ (fun i => v i*p t i)) ≤
      projectedSup β v p g := by
  have hh := SKRatioGaussian.gaussianAffine_le_gaussianSup (m := fun _ : I => 0) continuous_const
    ((continuous_fullCoeff v (β/sqrt n)).comp hp) (Sum.elim g (fun _ => 0)) t
  simpa only [SKRatioGaussian.gaussianAffine,Function.comp_def,zero_add,fullCoeff_goe,←projectedSup_eq,Sum.elim_inl] using hh

theorem projectedSup_tail (hn : 0<n) (σ : Fin n → α) (v b : α → ℝ)
    (hv : ∀ a, |v a|≤1) {s : α → ℝ} {β : ℝ} (hβ : 0<β)
    {u : I → Fin n → ℝ} (huc : Continuous u) (hu0 : ∀ t, ZeroSum σ (u t))
    (hus : ∀ t, overlap σ (u t) (u t)=s)
    (hp : ∀ t, ∑ i, (b (σ i)+u t i)^2=1) {a : ℝ} (ha : 0≤a) :
    (standardArrayLaw (Fin n × Fin n)).real {g |
      (∑ d, β/sqrt n*sqrt (radicalSq σ (crossCoeff σ v b) (fun a d => v a+v d) s d)*
        sqrt (s d)*sqrt ((Finset.univ.filter (fun i => σ i=d)).card : ℝ))+a ≤
      projectedSup β (fun i => v (σ i)) (fun t i => b (σ i)+u t i) g} ≤
      exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hδ : 0<β/sqrt (n:ℝ) := div_pos hβ (sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hsup := full_sup_tail σ v b hv hδ huc hu0 hus hp ha
  have hmeas : MeasurableSet {g |
      (∑ d, β/sqrt n*sqrt (radicalSq σ (crossCoeff σ v b) (fun a d => v a+v d) s d)*
        sqrt (s d)*sqrt ((Finset.univ.filter (fun i => σ i=d)).card : ℝ))+a ≤
      projectedSup β (fun i => v (σ i)) (fun t i => b (σ i)+u t i) g} :=
    measurableSet_le measurable_const
      (projectedSup_continuous β _ (continuous_const.add huc)).measurable
  rw [←inl_array_hasLaw.measureReal_eq hmeas]
  simp_rw [projectedSup_eq]
  convert hsup using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg Real.exp
  rw [div_pow,sq_sqrt (Nat.cast_nonneg n)]
  field_simp

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinFunctional
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

omit [DecidableEq ι] [Fintype α] in
lemma sqrt_count_mul_div {σ : ι → α} (hcount : ∀ a, 0 < count σ a) (B : α → ℝ) (a : α) :
    (count σ a:ℝ)*(B a/sqrt (count σ a:ℝ))=sqrt (count σ a:ℝ)*B a := by
  have hc : sqrt (count σ a:ℝ)≠0 := (sqrt_pos.mpr (Nat.cast_pos.mpr (hcount a))).ne'
  field_simp
  rw [sq_sqrt (Nat.cast_nonneg _)]; ring

omit [DecidableEq ι] in
lemma vectorOf_sum {σ : ι → α} (hcount : ∀ a, 0 < count σ a)
    (z : Parameters α) (u : Directions σ) (a : α) :
    sum σ (vectorOf z u) a=sqrt (count σ a:ℝ)*paramB z a := by
  unfold vectorOf
  rw [sum_add_bin,sum_const_bin σ (fun a => paramB z a/sqrt (count σ a:ℝ)),
    zeroSum_scale_bin (paramR z) (directions_zeroSum u) a,add_zero]
  exact sqrt_count_mul_div hcount (paramB z) a

omit [DecidableEq ι] in
lemma vectorOf_sq_sum {σ : ι → α} (hcount : ∀ a, 0 < count σ a)
    (z : Parameters α) (u : Directions σ) (a : α) :
    sum σ (fun i => vectorOf z u i^2) a=(paramB z a)^2+(paramR z a)^2 := by
  simp only [vectorOf]
  rw [bin_orthogonal_decomposition (zeroSum_scale_bin (paramR z) (directions_zeroSum u))
      (fun a => paramB z a/sqrt (count σ a:ℝ)) a,
    overlap_scale_bin,directions_overlap,mul_one,div_pow,sq_sqrt (Nat.cast_nonneg _)]
  congr 1
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (hcount a).ne')

omit [DecidableEq ι] in
lemma vectorOf_moment {σ : ι → α} (hcount : ∀ a, 0 < count σ a)
    (z : Parameters α) (u : Directions σ) (f : α → ℝ) :
    (∑ i, vectorOf z u i*f (σ i))/sqrt (Fintype.card ι:ℝ)=
      moment (binT σ) (paramB z) f := by
  rw [sum_weighted,Finset.sum_div]
  simp only [vectorOf_sum hcount, moment,binT]
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [DecidableEq ι] in
lemma binVariance_normalized [Nonempty ι] {σ : ι → α} (hcount : ∀ a, 0 < count σ a)
    (v B : α → ℝ) (a : α) :
    binVariance σ (crossCoeff σ v (fun d => B d/sqrt (count σ d:ℝ))) a=
      (∑ d, (v a+v d)^2*B d^2)-(moment (binT σ) B (fun d => v a+v d))^2 := by
  let f : ι → ℝ := fun i => (v a+v (σ i))*(B (σ i)/sqrt (count σ (σ i):ℝ))
  have he : binVariance σ (crossCoeff σ v (fun d => B d/sqrt (count σ d:ℝ))) a =
      ∑ i, centered f i^2 := rfl
  rw [he,centered_sq]
  have hsum : (∑ i, f i)=sqrt (Fintype.card ι:ℝ)*moment (binT σ) B (fun d => v a+v d) := by
    rw [←sum_fibers σ]
    have hf (d : α) : sum σ f d=sqrt (count σ d:ℝ)*B d*(v a+v d) := by
      change sum σ (fun i => (fun d => (v a+v d)*(B d/sqrt (count σ d:ℝ))) (σ i)) d=_
      rw [sum_const_bin σ (fun d => (v a+v d)*(B d/sqrt (count σ d:ℝ)))]
      rw [show (count σ d:ℝ)*((v a+v d)*(B d/sqrt (count σ d:ℝ)))=
        ((count σ d:ℝ)*(B d/sqrt (count σ d:ℝ)))*(v a+v d) by ring,
        sqrt_count_mul_div hcount]
    simp only [hf,moment,Finset.mul_sum,binT]
    apply Finset.sum_congr rfl
    intro d _
    have hn : sqrt (Fintype.card ι:ℝ)≠0 := (sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)).ne'
    field_simp
  have hsq : (∑ i, f i^2)=∑ d, (v a+v d)^2*B d^2 := by
    rw [←sum_fibers σ]
    apply Finset.sum_congr rfl
    intro d _
    change sum σ (fun i => (fun d => ((v a+v d)*(B d/sqrt (count σ d:ℝ)))^2) (σ i)) d=_
    rw [sum_const_bin σ (fun d => ((v a+v d)*(B d/sqrt (count σ d:ℝ)))^2),mul_pow,div_pow,sq_sqrt (Nat.cast_nonneg _)]
    have hc : (count σ d:ℝ)≠0 := Nat.cast_ne_zero.mpr (hcount d).ne'
    field_simp
  rw [hsq,average,hsum]
  have hn : (Fintype.card ι:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [div_pow,mul_pow,sq_sqrt (Nat.cast_nonneg _)]
  field_simp

omit [DecidableEq ι] in
lemma radicalSq_normalized [Nonempty ι] {σ : ι → α} (hcount : ∀ a, 0 < count σ a)
    (v : α → ℝ) (z : Parameters α) (a : α) :
    radicalSq σ (crossCoeff σ v (fun d => paramB z d/sqrt (count σ d:ℝ)))
      (fun a d => v a+v d) (fun d => (paramR z d)^2) a=
      finiteRadicalSq (binT σ) v z a := by
  rw [radicalSq,binVariance_normalized hcount]
  simp only [finiteRadicalSq,mul_add,Finset.sum_add_distrib]
  ring

theorem normalized_projected_tail {n : ℕ} (hn : 0<n) {σ : Fin n → α}
    (hcount : ∀ a, 2 ≤ count σ a) (v : α → ℝ) (hv : ∀ a, |v a|≤1)
    {β : ℝ} (hβ : 0<β) (z : Parameters α) {a : ℝ} (ha : 0≤a) :
    (standardArrayLaw (Fin n × Fin n)).real {g |
      finiteGaussian β (binT σ) v z+a≤
        projectedSup β (fun i => v (σ i)) (vectorOf z : Directions σ → Fin n → ℝ) g}≤
      exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have : Nonempty (Directions σ) := directions_nonempty hcount
  have hc : ∀ a, 0 < count σ a := fun a => lt_of_lt_of_le (by norm_num) (hcount a)
  have hh := projectedSup_tail hn σ v (fun a => paramB z a/sqrt (count σ a:ℝ)) hv hβ
    (scaled_directions_continuous z)
    (fun u => zeroSum_scale_bin (paramR z) (directions_zeroSum u))
    (show ∀ u : Directions σ, overlap σ (fun i => paramR z (σ i)*u.val i)
      (fun i => paramR z (σ i)*u.val i)=(fun a => (paramR z a)^2) from by
      intro u
      ext a
      rw [overlap_scale_bin,directions_overlap,mul_one])
    (fun u => vectorOf_unit hc z u) ha
  have he : (∑ d, β/sqrt n*sqrt (radicalSq σ
        (crossCoeff σ v (fun a => paramB z a/sqrt (count σ a:ℝ)))
        (fun a d => v a+v d) (fun a => (paramR z a)^2) d)*
      sqrt ((paramR z d)^2)*sqrt ((Finset.univ.filter (fun i => σ i=d)).card : ℝ))=
      finiteGaussian β (binT σ) v z := by
    simp_rw [radicalSq_normalized hc,sqrt_sq (paramR_nonneg z _)]
    unfold finiteGaussian binT
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    simp only [count,Fintype.card_fin]
    ring
  rw [he] at hh
  exact hh

omit [DecidableEq α]

lemma continuous_paramB (a : α) : Continuous (fun z : Parameters α => paramB z a) :=
  (EuclideanSpace.proj (Sum.inl a : α ⊕ α)).continuous.comp continuous_subtype_val
lemma continuous_paramR (a : α) : Continuous (fun z : Parameters α => paramR z a) :=
  (EuclideanSpace.proj (Sum.inr a : α ⊕ α)).continuous.comp continuous_subtype_val

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma siteMoment_bin {σ : Fin n → α} (hcount : ∀ a, 0 < count σ a)
    (z : Parameters α) (u : Directions σ) (f : α → ℝ) :
    siteMoment (vectorOf z u) (fun i => f (σ i)) = moment (binT σ) (paramB z) f := by
  simpa only [siteMoment,Fintype.card_fin] using vectorOf_moment hcount z u f

lemma diagonalForm_bin {σ : Fin n → α} (hcount : ∀ a, 0 < count σ a)
    (β : ℝ) (h : α → ℝ) (z : Parameters α) (u : Directions σ) :
    diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF
        (fun i => compactWeight (h (σ i))) (vectorOf z u) =
      β^2*(∑ a, ∑ d, binT σ d^2*(v (h d)^2/(w (h a)+w (h d)))*
        ((paramB z a)^2+(paramR z a)^2)) := by
  let p := vectorOf z u
  let K : α → α → ℝ := fun a d => v (h d)^2/(w (h a)+w (h d))
  have he : diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF
      (fun i => compactWeight (h (σ i))) p =
      β^2/(n:ℝ)*(∑ i, ∑ j, p i^2*(1:ℝ)*K (σ i) (σ j)) := by
    simp only [diagonalForm,compactF_weight,Finset.sum_mul,Finset.mul_sum,K,mul_one]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,double_weighted σ (fun i => p i^2) (fun _ => 1) K]
  simp only [p,vectorOf_sq_sum hcount,sum_const_bin σ (fun _ => 1),mul_one,
    binT_sq,Fintype.card_fin,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  dsimp [K]
  ring

lemma weightedForm_bin {σ : Fin n → α} (hcount : ∀ a, 0 < count σ a)
    (β : ℝ) (h : α → ℝ) (z : Parameters α) (u : Directions σ) :
    weightedForm (fun _ _ => β^2/(n:ℝ)) compactK
        (fun i => compactWeight (h (σ i))) (vectorOf z u) =
      β^2*(∑ a, ∑ d, binT σ a*paramB z a*kernel (h a) (h d)*(binT σ d*paramB z d)) := by
  let p := vectorOf z u
  have he : weightedForm (fun _ _ => β^2/(n:ℝ)) compactK
      (fun i => compactWeight (h (σ i))) p =
      β^2/(n:ℝ)*(∑ i, ∑ j, p i*p j*kernel (h (σ i)) (h (σ j))) := by
    simp only [weightedForm,quadratic,compactK_weight,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,double_weighted σ p p (fun a d => kernel (h a) (h d))]
  simp only [p,vectorOf_sum hcount,binT,Fintype.card_fin,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  rw [show sqrt (count σ a:ℝ)/sqrt (n:ℝ)*paramB z a*kernel (h a) (h d)*
      (sqrt (count σ d:ℝ)/sqrt (n:ℝ)*paramB z d) =
    (sqrt (count σ a:ℝ)*paramB z a*sqrt (count σ d:ℝ)*paramB z d*kernel (h a) (h d))/
      (sqrt (n:ℝ))^2 by ring,
    sq_sqrt (Nat.cast_nonneg n)]
  ring

theorem correctedForm_bin {σ : Fin n → α} (hcount : ∀ a, 0 < count σ a)
    (β : ℝ) (h : α → ℝ) (z : Parameters α) (u : Directions σ) :
    correctedForm β (fun i => h (σ i)) (vectorOf z u) = finiteA β (binT σ) h z := by
  unfold correctedForm
  rw [diagonalForm_bin hcount,weightedForm_bin hcount]
  simp only [siteMoment_bin hcount z u h,siteMoment_bin hcount z u (fun a => v (h a)),
    siteMoment_bin hcount z u (fun _ => 1),siteMoment_bin hcount z u (fun a => h a*v (h a)),
    siteMoment_bin hcount z u (fun a => m (h a)*v (h a))]
  rfl

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinNet
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma norm_of_sum_sq_one {p : Fin n → ℝ} (hp : ∑ i, p i^2=1) :
    ‖WithLp.toLp 2 p‖=1 := by
  have he := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 p)
  simp only [hp] at he
  nlinarith only [he,norm_nonneg (WithLp.toLp 2 p)]

lemma quadratic_vector_difference (M : Matrix (Fin n) (Fin n) ℝ)
    {p q : Fin n → ℝ} (hp : ∑ i, p i^2=1) (hq : ∑ i, q i^2=1) :
    |quadratic M p-quadratic M q| ≤
      2*euclideanOpNorm M*‖WithLp.toLp 2 (fun i => p i-q i)‖ := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) M
  let P : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 p
  let Q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 q
  have hP : ‖P‖=1 := norm_of_sum_sq_one hp
  have hQ : ‖Q‖=1 := norm_of_sum_sq_one hq
  have he : inner ℝ P (A P)-inner ℝ Q (A Q) =
      inner ℝ (P-Q) (A P)+inner ℝ Q (A (P-Q)) := by
    simp only [map_sub,inner_sub_left,inner_sub_right]
    ring
  rw [quadratic_inner,quadratic_inner]
  change |inner ℝ P (A P)-inner ℝ Q (A Q)|≤_
  rw [he]
  have h1 := (abs_real_inner_le_norm (P-Q) (A P)).trans
    (mul_le_mul_of_nonneg_left (A.le_opNorm P) (norm_nonneg _))
  have h2 := (abs_real_inner_le_norm Q (A (P-Q))).trans
    (mul_le_mul_of_nonneg_left (A.le_opNorm (P-Q)) (norm_nonneg _))
  rw [hP] at h1
  rw [hQ] at h2
  have ht := abs_add_le (inner ℝ (P-Q) (A P)) (inner ℝ Q (A (P-Q)))
  change |inner ℝ (P-Q) (A P)+inner ℝ Q (A (P-Q))|≤2*‖A‖*‖P-Q‖
  nlinarith only [ht,h1,h2]

lemma variance_bilinear_difference (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : ∀ i, |v i|≤1)
    {p q : Fin n → ℝ} (hp : ∑ i, p i^2=1) (hq : ∑ i, q i^2=1) :
    |p ⬝ᵥ (M*ᵥ(fun i => v i*p i))-q ⬝ᵥ (M*ᵥ(fun i => v i*q i))|≤
      2*euclideanOpNorm M*‖WithLp.toLp 2 (fun i => p i-q i)‖ := by
  have he (p : Fin n → ℝ) : p ⬝ᵥ (M*ᵥ(fun i => v i*p i))=
      quadratic (M*Matrix.diagonal v) p := by
    simp only [quadratic,Matrix.mul_diagonal,dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,he]
  apply (quadratic_vector_difference _ hp hq).trans
  have hd := matrix_diagonal_opNorm_le v 1 (by norm_num) hv
  have hn : euclideanOpNorm (M*Matrix.diagonal v)≤euclideanOpNorm M := by
    unfold euclideanOpNorm
    rw [map_mul]
    exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans_eq (mul_one _))
  gcongr

omit [DecidableEq α] in
lemma finiteA_parameter_tolerance (β : ℝ) (h : α → ℝ) {a : ℝ} (ha : 0<a) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (t : WeightBox α) (z z' : Parameters α),
      ‖z.val-z'.val‖<δ →
      |finiteA β (fun d => t d) h z-finiteA β (fun d => t d) h z'|<a := by
  have hc : Continuous (fun q : WeightBox α × Parameters α =>
      finiteA β (fun d => q.1 d) h q.2) := by
    unfold finiteA moment
    have hb (d : α) := (continuous_paramB d).comp (continuous_snd (X := WeightBox α))
    have hr (d : α) := (continuous_paramR d).comp (continuous_snd (X := WeightBox α))
    have ht (d : α) : Continuous (fun q : WeightBox α × Parameters α => (q.1 d:ℝ)) :=
      continuous_subtype_val.comp ((continuous_apply d).comp continuous_fst)
    fun_prop
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) a ha
  refine ⟨δ,hδ,fun t z z' hh => ?_⟩
  apply hcont (a := (t,z)) (b := (t,z'))
  simp only [Prod.dist_eq,dist_self,Subtype.dist_eq,dist_eq_norm,max_lt_iff]
  exact ⟨hδ,hh⟩

theorem binForm_finite_net (β : ℝ) (h : α → ℝ) {K a : ℝ} (hK : 0≤K) (ha : 0<a) :
    ∃ F : Finset (Parameters α), ∀ {n : ℕ} (_ : 0<n) (σ : Fin n → α),
      (∀ d, 2 ≤ count σ d) → ∀ M : Matrix (Fin n) (Fin n) ℝ,
      euclideanOpNorm M≤K → ∀ (z : Parameters α) (u : Directions σ),
      ∃ z' ∈ F,
        (vectorOf z u) ⬝ᵥ (M*ᵥ(fun i => v (h (σ i))*vectorOf z u i))+
            finiteA β (binT σ) h z ≤
          (vectorOf z' u) ⬝ᵥ (M*ᵥ(fun i => v (h (σ i))*vectorOf z' u i))+
            finiteA β (binT σ) h z'+a := by
  obtain ⟨δ,hδ,hA⟩ := finiteA_parameter_tolerance β h (show 0<a/2 by positivity)
  let η := min δ (a/(4*K+1))
  have hη : 0<η := lt_min hδ (by positivity)
  obtain ⟨F,hF⟩ := parameters_finite_net (α := α) hη
  refine ⟨F,?_⟩
  intro n hn σ hc M hM z u
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hc' : ∀ d, 0 < count σ d := fun d => lt_of_lt_of_le (by norm_num) (hc d)
  obtain ⟨z',hz',hnear⟩ := hF z
  refine ⟨z',hz',?_⟩
  have hA' := (le_abs_self _).trans (hA (binBox σ) z z' (hnear.trans_le (min_le_left _ _))).le
  have hdiff := variance_bilinear_difference M (fun i => v (h (σ i)))
    (fun i => by rw [abs_of_nonneg (v_pos _).le]; exact v_le_one _)
    (vectorOf_unit hc' z u) (vectorOf_unit hc' z' u)
  rw [vectorOf_difference hc'] at hdiff
  have hkd := mul_le_mul_of_nonneg_right hM (norm_nonneg (z.val-z'.val))
  have hηd := (lt_div_iff₀ (by positivity : 0<4*K+1)).mp (hnear.trans_le (min_le_right _ _))
  have habs := le_abs_self ((vectorOf z u) ⬝ᵥ (M*ᵥ (fun i => v (h (σ i))*vectorOf z u i))-
    (vectorOf z' u) ⬝ᵥ (M*ᵥ (fun i => v (h (σ i))*vectorOf z' u i)))
  change finiteA β (binT σ) h z-finiteA β (binT σ) h z'≤a/2 at hA'
  nlinarith only [habs,hdiff,hkd,hηd,hA',norm_nonneg (z.val-z'.val)]

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinTail
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

theorem binForm_tail {β K a : ℝ} (hβ : 0<β) (hK : 0≤K) (ha : 0<a)
    (h : α → ℝ) :
    ∃ N : ℕ, ∀ {n : ℕ} (_hn : 0<n) (σ : Fin n → α),
      (∀ d, 2 ≤ count σ d) → ∀ C : ℝ,
      (∀ z : Parameters α, finiteV β (binT σ) h z≤C) →
      (standardArrayLaw (Fin n × Fin n)).real (binFormBad β h σ K (C+2*a)) ≤
        N*exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
  obtain ⟨F,hF⟩ := binForm_finite_net β h hK ha
  refine ⟨F.card,?_⟩
  intro n hn σ hc C hC
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have : Nonempty (Directions σ) := directions_nonempty hc
  let E := fun z : Parameters α => {g : (Fin n × Fin n) → ℝ |
    finiteGaussian β (binT σ) (fun d => v (h d)) z+a ≤
      projectedSup β (fun i => v (h (σ i))) (vectorOf z : Directions σ → Fin n → ℝ) g}
  have hsub : binFormBad β h σ K (C+2*a) ⊆ ⋃ z∈F, E z := by
    intro g hg
    obtain ⟨hM,p,hp,hbad⟩ := hg
    obtain ⟨u,hu⟩ := vectorOf_surjective hc p hp
    let z := parametersOf σ p hp
    obtain ⟨z',hz',hnet⟩ := hF hn σ hc _ hM z u
    have he : correctedForm β (fun i => h (σ i)) p=finiteA β (binT σ) h z := by
      rw [←hu]
      exact correctedForm_bin (fun d => lt_of_lt_of_le (by norm_num) (hc d)) β h z u
    change vectorOf z u=p at hu
    rw [hu] at hnet
    rw [he] at hbad
    have hsup := le_projectedSup β (fun i => v (h (σ i)))
      (vectorOf_continuous z') g u
    have hCZ := hC z'
    dsimp only [finiteV] at hCZ
    have htail : g∈E z' := by
      change finiteGaussian β (binT σ) (fun d => v (h d)) z'+a ≤
        projectedSup β (fun i => v (h (σ i))) (vectorOf z' : Directions σ → Fin n → ℝ) g
      have hS : (vectorOf z' u ⬝ᵥ
          ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ
            (fun i => v (h (σ i))*vectorOf z' u i))) ≤
          projectedSup β (fun i => v (h (σ i)))
            (vectorOf z' : Directions σ → Fin n → ℝ) g := hsup
      have hT := hbad.trans_le hnet
      have hU := _root_.add_le_add_left (_root_.add_le_add_left hS (finiteA β (binT σ) h z')) a
      have hV := hT.trans_le hU
      linarith only [hV,hCZ]
    exact Set.mem_iUnion.mpr ⟨z',Set.mem_iUnion.mpr ⟨hz',htail⟩⟩
  calc
    _ ≤ (standardArrayLaw (Fin n × Fin n)).real (⋃ z∈F, E z) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ z∈F, (standardArrayLaw (Fin n × Fin n)).real (E z) := measureReal_biUnion_finset_le F E
    _ ≤ ∑ _z∈F, exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
      apply Finset.sum_le_sum
      intro z _
      exact normalized_projected_tail hn hc (fun d => v (h d))
        (fun d => by rw [abs_of_nonneg (v_pos _).le]; exact v_le_one _) hβ z ha.le
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_ConditionalBins
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix ENNReal
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
attribute [local instance] Classical.propDecidable

lemma independent_finite_selection_bound
    {Ω A D : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {R : Ω → A} {X : Ω → D}
    (hX : Measurable X) (hRX : IndepFun R X μ)
    (E : D → Set A) (hE : ∀ d, MeasurableSet (E d))
    {B : ℝ} (hB : ∀ d, μ.real (R ⁻¹' E d) ≤ B) :
    μ.real {ω | R ω ∈ E (X ω)} ≤ B := by
  have hall : (⋃ d : D, X ⁻¹' {d}) = Set.univ := by
    ext ω
    simp
  have hdis : Pairwise (Function.onFun Disjoint (fun d : D => X ⁻¹' {d})) := by
    intro d e hde
    exact Set.disjoint_left.mpr (fun ω hd he => hde ((Set.mem_singleton_iff.mp hd).symm.trans
      (Set.mem_singleton_iff.mp he)))
  have hsum : (∑ d, μ.real (X ⁻¹' {d})) = 1 := by
    rw [←measureReal_iUnion_fintype hdis (fun d => (MeasurableSet.singleton d).preimage hX),hall]
    simp [Measure.real]
  have hb (d : D) : μ.real (R ⁻¹' E d ∩ X ⁻¹' {d}) ≤ B*μ.real (X ⁻¹' {d}) := by
    have hi := hRX.measure_inter_preimage_eq_mul (E d) {d} (hE d) (MeasurableSet.singleton d)
    change (μ _).toReal ≤ _
    rw [hi,ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_right (hB d) ENNReal.toReal_nonneg
  calc
    _ ≤ μ.real (⋃ d : D, R ⁻¹' E d ∩ X ⁻¹' {d}) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      exact Set.mem_iUnion.mpr ⟨X ω,hω,rfl⟩
    _ ≤ ∑ d, μ.real (R ⁻¹' E d ∩ X ⁻¹' {d}) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ d, B*μ.real (X ⁻¹' {d}) := Finset.sum_le_sum (fun d _ => hb d)
    _ = B := by rw [←Finset.mul_sum,hsum,mul_one]

lemma residualFormBad_measurable {α : Type*} {n : ℕ}
    (β : ℝ) (h : α → ℝ) (σ : Fin n → α) (K C : ℝ) :
    MeasurableSet (residualFormBad β h σ K C) := by
  have hc : Continuous (fun M : (Fin n × Fin n) → ℝ =>
      euclideanOpNorm (fun i j => M (i,j))) := by
    have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n)) :=
      IsBoundedSMul.continuousSMul
    have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
      ContinuousLinearMap.continuousSMul
    exact continuous_norm.comp
      (((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp
        (by fun_prop))
  have ho : IsOpen {M : (Fin n × Fin n) → ℝ |
      ∃ p : Fin n → ℝ, (∑ i, p i^2)=1 ∧ C <
        p ⬝ᵥ ((fun i j => M (i,j))*ᵥ (fun i => v (h (σ i))*p i))+
          correctedForm β (fun i => h (σ i)) p} := by
    have he : {M : (Fin n × Fin n) → ℝ | ∃ p : Fin n → ℝ, (∑ i, p i^2)=1 ∧ C <
        p ⬝ᵥ ((fun i j => M (i,j))*ᵥ (fun i => v (h (σ i))*p i))+
          correctedForm β (fun i => h (σ i)) p} =
        ⋃ p : {p : Fin n → ℝ // (∑ i, p i^2)=1}, {M | C <
        p.val ⬝ᵥ ((fun i j => M (i,j))*ᵥ (fun i => v (h (σ i))*p.val i))+
          correctedForm β (fun i => h (σ i)) p.val} := by
      ext M
      simp
    rw [he]
    apply isOpen_iUnion
    intro p
    apply isOpen_lt continuous_const
    unfold dotProduct Matrix.mulVec
    fun_prop
  exact (measurableSet_le hc.measurable measurable_const).inter ho.measurableSet

theorem random_binForm_tail_oai {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {β K a C : ℝ} (hβ : 0<β) (hK : 0≤K) (ha : 0<a)
    (h : α → ℝ) (q : ℝ → α) (hq : Measurable q) :
    ∃ N : ℕ, ∀ {n : ℕ} (_hn : 0<n),
      (standardArrayLaw (Fin n × Fin n)).real {g |
        (∀ d, 2 ≤ count (fun i => q (augmentedField β g i)) d) ∧
        (∀ z : Parameters α, finiteV β (binT (fun i => q (augmentedField β g i))) h z≤C) ∧
        g ∈ binFormBad β h (fun i => q (augmentedField β g i)) K (C+2*a)} ≤
      N*exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
  obtain ⟨N,hN⟩ := binForm_tail hβ hK ha h
  refine ⟨N,?_⟩
  intro n hn
  let μ := standardArrayLaw (Fin n × Fin n)
  let R := fun g : (Fin n × Fin n) → ℝ => fun p : Fin n × Fin n =>
    (fieldProjection n*(β • goe g)*fieldProjection n) p.1 p.2
  let X := fun g : (Fin n × Fin n) → ℝ => fun i => q (augmentedField β g i)
  let good := fun σ : Fin n → α => (∀ d, 2 ≤ count σ d) ∧
    (∀ z : Parameters α, finiteV β (binT σ) h z≤C)
  let E := fun σ : Fin n → α => if good σ then residualFormBad β h σ K (C+2*a) else ∅
  have hX : Measurable X := by
    apply Measurable.of_eval
    intro i
    apply hq.comp
    unfold augmentedField augmented goe
    fun_prop
  have hi : IndepFun R X μ := by
    have ht := (field_residual_independent hn β).comp measurable_id
      (show Measurable (fun H : Fin n → ℝ => fun i => q (H i)) from
        Measurable.of_eval (fun i => hq.comp (measurable_pi_apply i)))
    exact ht
  have hE (σ : Fin n → α) : MeasurableSet (E σ) := by
    dsimp only [E]
    split_ifs
    · exact residualFormBad_measurable β h σ K (C+2*a)
    · exact MeasurableSet.empty
  have hb (σ : Fin n → α) : μ.real (R ⁻¹' E σ) ≤
      N*exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
    dsimp only [E]
    split_ifs with hg
    · exact hN hn σ hg.1 C hg.2
    · simp only [Set.preimage_empty,measureReal_empty]
      positivity
  apply (measureReal_mono ?_ (measure_ne_top μ _)).trans
    (independent_finite_selection_bound hX hi E hE hb)
  intro g hg
  change R g ∈ E (X g)
  dsimp only [E]
  rw [ite_eq_left (show good (X g) from ⟨hg.1,hg.2.1⟩)]
  exact hg.2.2

end SKRatio.Bins

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SKRatio.Bins.random_binForm_tail_oai.{u_1} := @OAI.SKRatio.Bins.random_binForm_tail_oai.{u_1}
