-- Prove2me | solution 1 for OAI.IndependentProducts.independent_centered_sum_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:15:46.240411+00:00
-- url     : https://prove2.me/submissions/0ab7f78e-159e-47e8-b833-89c76f3dffe2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/RandomSigns.lean:L219-L250
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.independent_centered_sum_abs_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns

-- ---- from OAI.Analysis.ProductSpaces.RandomSigns ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

lemma euclidSize_nonneg {ι : Type uι} [Fintype ι] (a : ι → ℝ) : 0 ≤ euclidSize a := Real.sqrt_nonneg _

lemma euclidSize_sq {ι : Type uι} [Fintype ι] (a : ι → ℝ) : euclidSize a ^ 2 = ∑ i, a i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma euclidSize_le_sum_abs {ι : Type uι} [Fintype ι] (a : ι → ℝ) :
    euclidSize a ≤ ∑ i, |a i| := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (a i))
  simp only [sq_abs] at h
  have hsum : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith [euclidSize_sq a, euclidSize_nonneg a]

lemma integrable_euclidSize {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} (X : ι → Ω → ℝ) (hX : ∀ i, Integrable (X i) P) :
    Integrable (fun ω => euclidSize (fun i => X i ω)) P := by
  apply Integrable.mono' (integrable_finsetSum _ (fun i _ => (hX i).abs))
  · unfold euclidSize
    fun_prop
  · exact ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (euclidSize_nonneg _)]
      exact euclidSize_le_sum_abs _)

lemma integral_abs_le_sqrt_sq {Ω : Type uΩ} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ ω, |X ω| ∂P) ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂P) := by
  have hXA : MemLp (fun ω => |X ω|) 2 P := by simpa only [Real.norm_eq_abs] using hX.norm
  have hv := variance_nonneg (X := fun ω => |X ω|) (μ := P)
  rw [variance_eq_sub hXA] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  have hpos : 0 ≤ ∫ ω, X ω ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  nlinarith [Real.sq_sqrt hpos, Real.sqrt_nonneg (∫ ω, X ω ^ 2 ∂P)]

lemma measurable_randomSign : Measurable randomSign := measurable_of_countable _

lemma randomSign_abs (b : Bool) : |randomSign b| = 1 := by cases b <;> norm_num [randomSign]

lemma randomSign_memLp : MemLp randomSign 2 signLaw :=
  MemLp.of_bound measurable_randomSign.aestronglyMeasurable 1
    (ae_of_all _ (fun b => by simp [Real.norm_eq_abs, randomSign_abs]))

lemma integral_signLaw (f : Bool → ℝ) : (∫ b, f b ∂signLaw) = (f false + f true) / 2 := by
  rw [signLaw, integral_bernoulliMeasure]
  norm_num
  ring

lemma integral_randomSign : (∫ b, randomSign b ∂signLaw) = 0 := by
  rw [integral_signLaw]; norm_num [randomSign]

lemma variance_randomSign : Var[randomSign; signLaw] = 1 := by
  rw [variance_eq_sub randomSign_memLp, integral_randomSign, integral_signLaw]
  norm_num [Pi.pow_apply, randomSign]

section SignVector
variable {ι : Type uι} [Fintype ι]

lemma sign_vector_memLp (a : ι → ℝ) :
    MemLp (fun ε : ι → Bool => ∑ i, a i * randomSign (ε i)) 2 signVector := by
  apply memLp_finsetSum
  intro i _
  exact (randomSign_memLp.const_mul _).comp_measurePreserving
    (measurePreserving_eval (fun _ => signLaw) i)

lemma sign_vector_mean (a : ι → ℝ) :
    (∫ ε : ι → Bool, ∑ i, a i * randomSign (ε i) ∂signVector) = 0 := by
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    have he := (measurePreserving_eval (fun _ : ι => signLaw) i).hasLaw.integral_comp
      (f := fun b => a i * randomSign b) ((randomSign_memLp.const_mul (a i)).aestronglyMeasurable)
    exact he.trans (by rw [integral_const_mul, integral_randomSign, mul_zero])
  · intro i _
    exact ((randomSign_memLp.const_mul _).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => signLaw) i)).integrable (by norm_num)

lemma sign_vector_second_moment (a : ι → ℝ) :
    (∫ ε : ι → Bool, (∑ i, a i * randomSign (ε i)) ^ 2 ∂signVector) = ∑ i, a i ^ 2 := by
  have hv := variance_sum_pi (fun i : ι => randomSign_memLp.const_mul (a i))
  simp only [variance_const_mul, variance_randomSign, mul_one] at hv
  rw [Finset.sum_fn] at hv
  change Var[fun ε : ι → Bool => ∑ i, a i * randomSign (ε i); signVector] = _ at hv
  rw [variance_eq_sub (sign_vector_memLp a), sign_vector_mean] at hv
  simpa only [Pi.pow_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] using hv

lemma sign_vector_abs_le (a : ι → ℝ) :
    (∫ ε : ι → Bool, |∑ i, a i * randomSign (ε i)| ∂signVector) ≤ euclidSize a := by
  have h := integral_abs_le_sqrt_sq (sign_vector_memLp a)
  rwa [sign_vector_second_moment] at h

end SignVector
end IndependentProducts

namespace IndependentProducts
section Symmetrization
variable {ι : Type uι} [Fintype ι]

lemma measurePreserving_selectivelySwap (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (ε : ι → Bool) : MeasurePreserving (selectivelySwap ε)
      ((Measure.pi ν).prod (Measure.pi ν)) ((Measure.pi ν).prod (Measure.pi ν)) := by
  let f : ι → (ℝ × ℝ) → (ℝ × ℝ) := fun i z => if ε i then z else z.swap
  have hp : ∀ i, MeasurePreserving (f i) ((ν i).prod (ν i)) ((ν i).prod (ν i)) := by
    intro i
    dsimp [f]
    split
    · exact MeasurePreserving.id _
    · exact Measure.measurePreserving_swap
  have hpi := measurePreserving_pi (fun i => (ν i).prod (ν i)) (fun i => (ν i).prod (ν i)) hp
  have hs := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι ν ν
  convert hs.comp (hpi.comp hs.symm) using 1
  ext z : 1
  apply Prod.ext <;> funext i <;> cases he : ε i <;>
    simp [selectivelySwap, f, he, MeasurableEquiv.arrowProdEquivProdArrow]

lemma selectivelySwap_difference (ε : ι → Bool) (z : (ι → ℝ) × (ι → ℝ)) :
    (∑ i, ((selectivelySwap ε z).1 i - (selectivelySwap ε z).2 i)) =
      ∑ i, (z.1 i - z.2 i) * randomSign (ε i) := by
  apply Finset.sum_congr rfl
  intro i _
  cases he : ε i <;> simp [selectivelySwap, randomSign, he]

lemma sign_vector_difference_abs_le (x y : ι → ℝ) :
    (∫ ε : ι → Bool, |∑ i, (x i - y i) * randomSign (ε i)| ∂signVector) ≤
      euclidSize x + euclidSize y := by
  calc
    _ ≤ ∫ ε : ι → Bool,
      |∑ i, x i * randomSign (ε i)| + |∑ i, y i * randomSign (ε i)| ∂signVector := by
      apply integral_mono ((sign_vector_memLp (fun i => x i - y i)).integrable (by norm_num)).abs
        (((sign_vector_memLp x).integrable (by norm_num)).abs.add
          ((sign_vector_memLp y).integrable (by norm_num)).abs)
      intro ε
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      exact abs_sub _ _
    _ = (∫ ε : ι → Bool, |∑ i, x i * randomSign (ε i)| ∂signVector) +
        ∫ ε : ι → Bool, |∑ i, y i * randomSign (ε i)| ∂signVector :=
      integral_add ((sign_vector_memLp x).integrable (by norm_num)).abs
        ((sign_vector_memLp y).integrable (by norm_num)).abs
    _ ≤ _ := add_le_add (sign_vector_abs_le x) (sign_vector_abs_le y)

lemma integrable_signed_sum {Ω : Type uΩ} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ι → Ω → ℝ) (hX : ∀ i, Integrable (X i) P) :
    Integrable (fun z : (ι → Bool) × Ω => ∑ i, X i z.2 * randomSign (z.1 i)) (signVector.prod P) := by
  classical
  have hmap : Measurable (fun ε : ι → Bool => P.map (Prod.mk ε)) :=
    measurable_of_finite _
  rw [Measure.prod, ← Measure.sum_smul_dirac (signVector (ι := ι)),
    Measure.bind_sum _ _ hmap.aemeasurable]
  simp_rw [Measure.bind_smul, Measure.dirac_bind hmap]
  rw [Measure.sum_fintype, integrable_finsetSum_measure]
  intro ε _
  apply Integrable.smul_measure ?_ (measure_ne_top _ _)
  rw [(measurableEmbedding_prodMk_left ε).integrable_map_iff]
  exact integrable_finsetSum _ fun i _ => (hX i).mul_const (randomSign (ε i))

lemma independent_difference_abs_le (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, Integrable (fun x : ℝ => x) (ν i)) :
    (∫ z : (ι → ℝ) × (ι → ℝ), |∑ i, (z.1 i - z.2 i)| ∂(Measure.pi ν).prod (Measure.pi ν)) ≤
      2 * ∫ x : ι → ℝ, euclidSize x ∂Measure.pi ν := by
  let P := Measure.pi ν
  have hi : ∀ i, Integrable (fun x : ι → ℝ => x i) P := by
    intro i
    exact (measurePreserving_eval ν i).integrable_comp (by fun_prop) |>.mpr (hν i)
  have hsigma : Integrable (fun x : ι → ℝ => euclidSize x) P := integrable_euclidSize _ hi
  have hdiff : ∀ i, Integrable (fun z : (ι → ℝ) × (ι → ℝ) => z.1 i - z.2 i) (P.prod P) :=
    fun i => ((hi i).comp_fst P).sub ((hi i).comp_snd P)
  have hprod := (integrable_signed_sum _ hdiff).abs
  have he : ∀ ε : ι → Bool,
      (∫ z : (ι → ℝ) × (ι → ℝ), |∑ i, (z.1 i - z.2 i) * randomSign (ε i)| ∂P.prod P) =
      ∫ z : (ι → ℝ) × (ι → ℝ), |∑ i, (z.1 i - z.2 i)| ∂P.prod P := by
    intro ε
    have hh := (measurePreserving_selectivelySwap ν ε).hasLaw.integral_comp
      (f := fun z : (ι → ℝ) × (ι → ℝ) => |∑ i, (z.1 i - z.2 i)|)
      ((by fun_prop : Continuous (fun z : (ι → ℝ) × (ι → ℝ) => |∑ i, (z.1 i - z.2 i)|)).aestronglyMeasurable)
    simpa only [Function.comp_apply, selectivelySwap_difference] using hh
  calc
    _ = ∫ ε : ι → Bool, ∫ z : (ι → ℝ) × (ι → ℝ),
        |∑ i, (z.1 i - z.2 i) * randomSign (ε i)| ∂P.prod P ∂signVector := by
      simp_rw [he]
      simp [P]
    _ = ∫ z : (ι → ℝ) × (ι → ℝ), ∫ ε : ι → Bool,
        |∑ i, (z.1 i - z.2 i) * randomSign (ε i)| ∂signVector ∂P.prod P :=
      integral_integral_swap hprod
    _ ≤ ∫ z : (ι → ℝ) × (ι → ℝ), euclidSize z.1 + euclidSize z.2 ∂P.prod P := by
      apply integral_mono hprod.integral_prod_right ((hsigma.comp_fst P).add (hsigma.comp_snd P))
      intro z
      exact sign_vector_difference_abs_le z.1 z.2
    _ = 2 * ∫ x : ι → ℝ, euclidSize x ∂P := by
      rw [integral_add (hsigma.comp_fst P) (hsigma.comp_snd P), integral_fun_fst euclidSize,
        integral_fun_snd euclidSize]
      simp
      ring

lemma independent_centered_sum_abs_le (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, Integrable (fun x : ℝ => x) (ν i)) :
    (∫ x : ι → ℝ, |∑ i, (x i - ∫ z : ℝ, z ∂ν i)| ∂Measure.pi ν) ≤
      2 * ∫ x : ι → ℝ, euclidSize x ∂Measure.pi ν := by
  let P := Measure.pi ν
  have hi : ∀ i, Integrable (fun x : ι → ℝ => x i) P := by
    intro i
    exact (measurePreserving_eval ν i).integrable_comp (by fun_prop) |>.mpr (hν i)
  have hcenter : Integrable (fun x : ι → ℝ => ∑ i, (x i - ∫ z : ℝ, z ∂ν i)) P :=
    integrable_finsetSum _ (fun i _ => (hi i).sub (integrable_const _))
  have hdiff : Integrable (fun z : (ι → ℝ) × (ι → ℝ) => ∑ i, (z.1 i - z.2 i)) (P.prod P) :=
    integrable_finsetSum _ (fun i _ => ((hi i).comp_fst P).sub ((hi i).comp_snd P))
  have hjensen : ∀ x : ι → ℝ, |∑ i, (x i - ∫ z : ℝ, z ∂ν i)| ≤
      ∫ y : ι → ℝ, |∑ i, (x i - y i)| ∂P := by
    intro x
    have he : (∫ y : ι → ℝ, ∑ i, (x i - y i) ∂P) = ∑ i, (x i - ∫ z : ℝ, z ∂ν i) := by
      rw [integral_finsetSum Finset.univ (fun i _ =>
        show Integrable (fun y : ι → ℝ => x i - y i) P from (integrable_const _).sub (hi i))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_sub (integrable_const _) (hi i)]
      have hmap := (measurePreserving_eval ν i).hasLaw.integral_eq
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      exact congrArg (x i - ·) hmap
    rw [← he]
    exact abs_integral_le_integral_abs
  calc
    _ ≤ ∫ x : ι → ℝ, ∫ y : ι → ℝ, |∑ i, (x i - y i)| ∂P ∂P :=
      integral_mono hcenter.abs hdiff.abs.integral_prod_left hjensen
    _ = ∫ z : (ι → ℝ) × (ι → ℝ), |∑ i, (z.1 i - z.2 i)| ∂P.prod P :=
      (integral_prod _ hdiff.abs).symm
    _ ≤ _ := independent_difference_abs_le ν hν

end Symmetrization
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι
variable {ι : Type uι} [Fintype ι]

theorem solution (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, Integrable (fun x : ℝ => x) (ν i)) :
    (∫ x : ι → ℝ, |∑ i, (x i - ∫ z : ℝ, z ∂ν i)| ∂Measure.pi ν) ≤
      2 * ∫ x : ι → ℝ, euclidSize x ∂Measure.pi ν := by
  first
    | exact OAI.IndependentProducts.independent_centered_sum_abs_le ν hν
    | exact OAI.IndependentProducts.independent_centered_sum_abs_le
    | (apply OAI.IndependentProducts.independent_centered_sum_abs_le <;> assumption)
    | (intros; apply OAI.IndependentProducts.independent_centered_sum_abs_le <;> assumption)
