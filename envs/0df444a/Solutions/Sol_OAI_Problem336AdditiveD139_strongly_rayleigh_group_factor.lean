-- Prove2me | solution 1 for OAI.Problem336AdditiveD139.strongly_rayleigh_group_factor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T23:33:34.35998+00:00
-- url     : https://prove2.me/submissions/8a354d28-ee10-4b98-9f22-6cdc1cb8c532

import Mathlib
import Definitions.Def_StronglyRayleighDPP

namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u u_21 u_22 u_23 u_24 u_25 u_26 u_27 u_28 u_29 u_30

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace Problem336AdditiveD139






















end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem336AdditiveD139

theorem bivariate_stable_root_im_nonpos (a b c d : ℂ)
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      a + b * z + c * w + d * z * w ≠ 0)
    (w : ℂ) (hw : 0 < w.im) :
    (-(a + c * w) / (b + d * w)).im ≤ 0 := by
  by_cases hden : b + d * w = 0
  · simp [hden]
  · by_contra h
    have hz : 0 < (-(a + c * w) / (b + d * w)).im := lt_of_not_ge h
    apply hstable (-(a + c * w) / (b + d * w)) w hz hw
    calc
      _ = a + c * w + (-(a + c * w) / (b + d * w)) * (b + d * w) := by ring
      _ = 0 := by rw [div_mul_cancel₀ _ hden]; ring

theorem bivariate_stable_rayleigh (a b c d : ℝ)
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      (a : ℂ) + b * z + c * w + d * z * w ≠ 0) :
    a * d ≤ b * c := by
  by_contra hle
  have hdiff : 0 < a * d - b * c := by linarith
  have hden : 0 < b ^ 2 + d ^ 2 := by
    by_contra hn
    have hb : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg d]
    have hd : d = 0 := by nlinarith [sq_nonneg b, sq_nonneg d]
    simp [hb, hd] at hdiff
  let z : ℂ := ⟨-(a * b + c * d) / (b ^ 2 + d ^ 2),
    (a * d - b * c) / (b ^ 2 + d ^ 2)⟩
  have hz : 0 < z.im := div_pos hdiff hden
  have hzero : (a : ℂ) + b * z + c * Complex.I + d * z * Complex.I = 0 := by
    apply Complex.ext
    · simp [z, Complex.mul_re, Complex.mul_im]
      field_simp
      all_goals ring
    · simp [z, Complex.mul_re, Complex.mul_im]
      field_simp
      all_goals ring
  exact hstable z Complex.I hz (by simp) hzero

theorem bivariate_stable_limit_rayleigh_of_eventually {ι : Type u_1} {l : Filter ι} [l.NeBot]
    (A B C D : ι → ℂ) (a b c d : ℝ)
    (hA : Filter.Tendsto A l (nhds (a : ℂ)))
    (hB : Filter.Tendsto B l (nhds (b : ℂ)))
    (hC : Filter.Tendsto C l (nhds (c : ℂ)))
    (hD : Filter.Tendsto D l (nhds (d : ℂ)))
    (hstable : ∀ᶠ n in l, ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      A n + B n * z + C n * w + D n * z * w ≠ 0) :
    a * d ≤ b * c := by
  by_contra hle
  have hdiff : 0 < a * d - b * c := by linarith
  have hden : (b : ℂ) + d * Complex.I ≠ 0 := by
    intro hz
    have hb : b = 0 := by simpa using congrArg Complex.re hz
    have hd : d = 0 := by simpa using congrArg Complex.im hz
    simp [hb, hd] at hdiff
  have hlim := ((hA.add (hC.mul_const Complex.I)).neg).div
    (hB.add (hD.mul_const Complex.I)) hden
  have him : ( -((a : ℂ) + c * Complex.I) / ((b : ℂ) + d * Complex.I)).im ≤ 0 :=
    le_of_tendsto (Complex.continuous_im.tendsto _ |>.comp hlim)
      (hstable.mono fun n hn =>
        bivariate_stable_root_im_nonpos (A n) (B n) (C n) (D n)
          hn Complex.I (by simp))
  have hn : 0 < Complex.normSq ((b : ℂ) + d * Complex.I) :=
    Complex.normSq_pos.mpr hden
  have hformula : (-((a : ℂ) + c * Complex.I) / ((b : ℂ) + d * Complex.I)).im =
      (a * d - b * c) / Complex.normSq ((b : ℂ) + d * Complex.I) := by
    simp [Complex.div_im]
    ring
  rw [hformula] at him
  exact (not_lt_of_ge him) (div_pos hdiff hn)

theorem bivariate_stable_limit_rayleigh {ι : Type u_2} {l : Filter ι} [l.NeBot]
    (A B C D : ι → ℂ) (a b c d : ℝ)
    (hA : Filter.Tendsto A l (nhds (a : ℂ)))
    (hB : Filter.Tendsto B l (nhds (b : ℂ)))
    (hC : Filter.Tendsto C l (nhds (c : ℂ)))
    (hD : Filter.Tendsto D l (nhds (d : ℂ)))
    (hstable : ∀ n, ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      A n + B n * z + C n * w + D n * z * w ≠ 0) :
    a * d ≤ b * c :=
  bivariate_stable_limit_rayleigh_of_eventually A B C D a b c d hA hB hC hD
    (Filter.Eventually.of_forall hstable)

theorem bivariate_continuous_limit_rayleigh
    (A B C D : ℝ → ℂ) (a b c d : ℝ)
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0)
    (hC : ContinuousAt C 0) (hD : ContinuousAt D 0)
    (hA0 : A 0 = (a : ℂ)) (hB0 : B 0 = (b : ℂ))
    (hC0 : C 0 = (c : ℂ)) (hD0 : D 0 = (d : ℂ))
    (hstable : ∀ t : ℝ, 0 < t → ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      A t + B t * z + C t * w + D t * z * w ≠ 0) :
    a * d ≤ b * c := by
  apply bivariate_stable_limit_rayleigh_of_eventually
    (l := nhdsWithin 0 (Set.Ioi 0)) A B C D a b c d
  · simpa [hA0] using hA.tendsto.mono_left nhdsWithin_le_nhds
  · simpa [hB0] using hB.tendsto.mono_left nhdsWithin_le_nhds
  · simpa [hC0] using hC.tendsto.mono_left nhdsWithin_le_nhds
  · simpa [hD0] using hD.tendsto.mono_left nhdsWithin_le_nhds
  · have hpos : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
    exact hpos.mono fun t ht => hstable t ht

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem336AdditiveD139

def tiltPairMass {F : Type u_1} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ)
    (i j : F) (b c : Bool) : ℝ := by
  classical
  exact ∑ x : F → Bool, if x i = b ∧ x j = c then
    Real.exp (∑ k : F, h k * boolReal (x k)) *
      ((μ : Measure (F → Bool)) {x}).toReal else 0

lemma tiltPairMass_nonneg {F : Type u_2} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ)
    (i j : F) (b c : Bool) : 0 ≤ tiltPairMass μ h i j b c := by
  classical
  unfold tiltPairMass
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg
  · exact le_rfl

lemma tiltPartition_pairMass {F : Type u_3} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) :
    tiltPartition μ h = tiltPairMass μ h i j false false +
      tiltPairMass μ h i j true false + tiltPairMass μ h i j false true +
      tiltPairMass μ h i j true true := by
  classical
  unfold tiltPartition tiltPairMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases hi : x i <;> cases hj : x j <;> simp

lemma tiltMean_pairMass_left {F : Type u_4} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) :
    tiltMean μ h i =
      (tiltPairMass μ h i j true false + tiltPairMass μ h i j true true) /
        tiltPartition μ h := by
  classical
  unfold tiltMean tiltPairMass
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases hi : x i <;> cases hj : x j <;> simp [boolReal]

lemma tiltMean_pairMass_right {F : Type u_5} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) :
    tiltMean μ h j =
      (tiltPairMass μ h i j false true + tiltPairMass μ h i j true true) /
        tiltPartition μ h := by
  classical
  unfold tiltMean tiltPairMass
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases hi : x i <;> cases hj : x j <;> simp [boolReal]

lemma tiltSecondMoment_pairMass {F : Type u_6} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) :
    tiltSecondMoment μ h i j =
      tiltPairMass μ h i j true true / tiltPartition μ h := by
  classical
  unfold tiltSecondMoment tiltPairMass
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  cases hi : x i <;> cases hj : x j <;> simp [boolReal]

lemma tiltCovariance_pairMass {F : Type u_7} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) :
    tiltCovariance μ h i j =
      (tiltPairMass μ h i j false false * tiltPairMass μ h i j true true -
        tiltPairMass μ h i j true false * tiltPairMass μ h i j false true) /
          (tiltPartition μ h)^2 := by
  rw [tiltCovariance, tiltSecondMoment_pairMass, tiltMean_pairMass_left μ h i j,
    tiltMean_pairMass_right μ h i j]
  by_cases hz : tiltPartition μ h = 0
  · simp [hz]
  · field_simp
    rw [tiltPartition_pairMass μ h i j]
    ring

lemma tiltCovariance_nonpos_of_pairMass {F : Type u_8} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F)
    (hneg : tiltPairMass μ h i j false false * tiltPairMass μ h i j true true ≤
      tiltPairMass μ h i j true false * tiltPairMass μ h i j false true) :
    tiltCovariance μ h i j ≤ 0 := by
  rw [tiltCovariance_pairMass]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hneg) (sq_nonneg _)

def pairSlice {F : Type u_9} (i j : F) (z w : ℂ) : F → ℂ := by
  classical
  exact fun k => if k = i then z else if k = j then w else 1

lemma prod_pairSlice {F : Type u_10} [Fintype F] (x : F → Bool)
    (i j : F) (hij : i ≠ j) (z w : ℂ) :
    (∏ k : F, if x k = true then pairSlice i j z w k else 1) =
      (if x i = true then z else 1) * (if x j = true then w else 1) := by
  classical
  rw [Finset.prod_eq_mul_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij]
  · simp [pairSlice, hij.symm]
  · intro k hk hki
    simp [pairSlice, hki.1, hki.2]

open scoped Classical in
lemma tiltPairMass_generating {F : Type u_11} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ)
    (i j : F) (hij : i ≠ j) (z w : ℂ) :
    (∑ x : F → Bool,
      ((Real.exp (∑ k : F, h k * boolReal (x k)) *
        ((μ : Measure (F → Bool)) {x}).toReal : ℝ) : ℂ) *
      ∏ k : F, if x k = true then pairSlice i j z w k else 1) =
      (tiltPairMass μ h i j false false : ℂ) +
      (tiltPairMass μ h i j true false : ℂ) * z +
      (tiltPairMass μ h i j false true : ℂ) * w +
      (tiltPairMass μ h i j true true : ℂ) * z * w := by
  classical
  simp only [tiltPairMass, Complex.ofReal_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [prod_pairSlice x i j hij]
  cases hi : x i <;> cases hj : x j <;> simp [mul_assoc]

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem336AdditiveD139

def twoCoordinateCoefficient {F : Type u_1} [Fintype F]
    (weight : (F → Bool) → ℂ) (i j : F) (r : F → ℂ) (p q : Bool) : ℂ := by
  classical
  exact ∑ x : F → Bool, if x i = p ∧ x j = q then
    weight x * ∏ k ∈ (Finset.univ.erase i).erase j,
      if x k = true then r k else 1
    else 0

lemma binary_pair_sum {X : Type u_2} [Fintype X]
    (u v : X → Bool) (f : X → ℂ) :
    (∑ x, f x) =
      (∑ x, if u x = false ∧ v x = false then f x else 0) +
      (∑ x, if u x = true ∧ v x = false then f x else 0) +
      (∑ x, if u x = false ∧ v x = true then f x else 0) +
      (∑ x, if u x = true ∧ v x = true then f x else 0) := by
  classical
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases u x <;> cases v x <;> simp

def twoCoordinateField {F : Type u_3} (i j : F) (r : F → ℂ) (z w : ℂ) : F → ℂ := by
  classical
  exact fun k => if k = i then z else if k = j then w else r k

lemma monomial_two_coordinates {F : Type u_4} [Fintype F]
    (x : F → Bool) (r : F → ℂ) (i j : F) (hij : i ≠ j) (z w : ℂ) :
    (∏ k : F, if x k = true then twoCoordinateField i j r z w k else 1) =
    (if x i = true then z else 1) * (if x j = true then w else 1) *
      ∏ k ∈ (Finset.univ.erase i).erase j, if x k = true then r k else 1 := by
  classical
  let f : F → ℂ := fun k => if x k = true then twoCoordinateField i j r z w k else 1
  have hi : i ∈ (Finset.univ : Finset F) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ : Finset F).erase i := by simp [hij.symm]
  change (∏ k, f k) = _
  rw [← Finset.mul_prod_erase _ _ hi, ← Finset.mul_prod_erase _ _ hj]
  have hprod : (∏ k ∈ (Finset.univ.erase i).erase j, f k) =
      ∏ k ∈ (Finset.univ.erase i).erase j, if x k = true then r k else 1 := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    simp [f, twoCoordinateField, hki, hkj]
  rw [hprod]
  simp [f, twoCoordinateField, hij.symm, mul_assoc]

lemma weighted_generating_two_coordinates {F : Type u_5} [Fintype F]
    (weight : (F → Bool) → ℂ) (r : F → ℂ) (i j : F) (hij : i ≠ j) (z w : ℂ) :
    (∑ x : F → Bool, weight x *
      ∏ k : F, if x k = true then twoCoordinateField i j r z w k else 1) =
    twoCoordinateCoefficient weight i j r false false +
      twoCoordinateCoefficient weight i j r true false * z +
      twoCoordinateCoefficient weight i j r false true * w +
      twoCoordinateCoefficient weight i j r true true * z * w := by
  classical
  simp only [twoCoordinateCoefficient, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [monomial_two_coordinates x r i j hij z w]
  cases hxi : x i <;> cases hxj : x j <;> simp <;> ring

lemma finiteGeneratingValue_two_coordinates {F : Type u_6} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (r : F → ℂ)
    (i j : F) (hij : i ≠ j) (z w : ℂ) :
    finiteGeneratingValue μ (twoCoordinateField i j r z w) =
    twoCoordinateCoefficient (fun x => (((μ : Measure (F → Bool)) {x}).toReal : ℂ))
        i j r false false +
      twoCoordinateCoefficient (fun x => (((μ : Measure (F → Bool)) {x}).toReal : ℂ))
        i j r true false * z +
      twoCoordinateCoefficient (fun x => (((μ : Measure (F → Bool)) {x}).toReal : ℂ))
        i j r false true * w +
      twoCoordinateCoefficient (fun x => (((μ : Measure (F → Bool)) {x}).toReal : ℂ))
        i j r true true * z * w := by
  classical
  exact weighted_generating_two_coordinates _ r i j hij z w

lemma continuous_twoCoordinateCoefficient {F : Type u_7} [Fintype F]
    (weight : (F → Bool) → ℂ) (i j : F) (p q : Bool) :
    Continuous (fun r : F → ℂ => twoCoordinateCoefficient weight i j r p q) := by
  unfold twoCoordinateCoefficient
  apply continuous_finsetSum
  intro x hx
  split_ifs
  · apply continuous_const.mul
    apply continuous_finsetProd
    intro k hk
    split_ifs <;> fun_prop
  · exact continuous_const

def twoCoordinateWeight {F : Type u_8} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) (p q : Bool) : ℝ :=
  ∑ x : F → Bool, if x i = p ∧ x j = q then weight x else 0

lemma twoCoordinateWeight_total {F : Type u_9} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) :
    (∑ x, weight x) =
      twoCoordinateWeight weight i j false false +
      twoCoordinateWeight weight i j true false +
      twoCoordinateWeight weight i j false true +
      twoCoordinateWeight weight i j true true := by
  simp only [twoCoordinateWeight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> cases x j <;> simp

lemma twoCoordinateWeight_first {F : Type u_10} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) :
    (∑ x, weight x * boolReal (x i)) =
      twoCoordinateWeight weight i j true false +
      twoCoordinateWeight weight i j true true := by
  simp only [twoCoordinateWeight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> cases x j <;> simp [boolReal]

lemma twoCoordinateWeight_second {F : Type u_11} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) :
    (∑ x, weight x * boolReal (x j)) =
      twoCoordinateWeight weight i j false true +
      twoCoordinateWeight weight i j true true := by
  simp only [twoCoordinateWeight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> cases x j <;> simp [boolReal]

lemma twoCoordinateWeight_both {F : Type u_12} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) :
    (∑ x, weight x * boolReal (x i) * boolReal (x j)) =
      twoCoordinateWeight weight i j true true := by
  simp only [twoCoordinateWeight]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> cases x j <;> simp [boolReal]

lemma binary_covariance_eq_pair_determinant {F : Type u_13} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) (hZ : (∑ x, weight x) ≠ 0) :
    (∑ x, weight x * boolReal (x i) * boolReal (x j)) / (∑ x, weight x) -
      ((∑ x, weight x * boolReal (x i)) / (∑ x, weight x)) *
      ((∑ x, weight x * boolReal (x j)) / (∑ x, weight x)) =
    (twoCoordinateWeight weight i j false false * twoCoordinateWeight weight i j true true -
      twoCoordinateWeight weight i j true false * twoCoordinateWeight weight i j false true) /
      (∑ x, weight x) ^ 2 := by
  rw [twoCoordinateWeight_first weight i j, twoCoordinateWeight_second weight i j,
    twoCoordinateWeight_both weight i j]
  have htotal := twoCoordinateWeight_total weight i j
  field_simp
  rw [htotal]
  ring

lemma twoCoordinateWeight_cast_eq_coefficient {F : Type u_14} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) (p q : Bool) :
    (twoCoordinateWeight weight i j p q : ℂ) =
      twoCoordinateCoefficient (fun x => (weight x : ℂ)) i j (fun _ => 1) p q := by
  simp only [twoCoordinateWeight, twoCoordinateCoefficient, Complex.ofReal_sum,
    ite_self, Finset.prod_const_one, mul_one]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem336AdditiveD139

variable {F : Type u_1} [Fintype F]

lemma exp_bool_sum_eq_prod (h : F → ℝ) (x : F → Bool) :
    (Real.exp (∑ i : F, h i * boolReal (x i)) : ℂ) =
      ∏ i : F, if x i = true then (Real.exp (h i) : ℂ) else 1 := by
  classical
  rw [Real.exp_sum, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  cases x i <;> simp [boolReal]

lemma generating_monomial_rescale (h : F → ℝ) (x : F → Bool) (z : F → ℂ) :
    (∏ i : F, if x i = true then (Real.exp (h i) : ℂ) * z i else 1) =
      (Real.exp (∑ i : F, h i * boolReal (x i)) : ℂ) *
        ∏ i : F, if x i = true then z i else 1 := by
  classical
  rw [exp_bool_sum_eq_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases x i <;> simp

lemma finiteGeneratingValue_exp (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) :
    finiteGeneratingValue μ (fun i => (Real.exp (h i) : ℂ)) =
      (tiltPartition μ h : ℂ) := by
  classical
  unfold finiteGeneratingValue tiltPartition
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← exp_bool_sum_eq_prod, Complex.ofReal_mul]
  ring

lemma finiteGeneratingValue_of_tilt_atoms
    (μ ν : ProbabilityMeasure (F → Bool)) (h : F → ℝ)
    (hatom : ∀ x : F → Bool,
      ((ν : Measure (F → Bool)) {x}).toReal =
        Real.exp (∑ i : F, h i * boolReal (x i)) *
          ((μ : Measure (F → Bool)) {x}).toReal / tiltPartition μ h)
    (z : F → ℂ) :
    finiteGeneratingValue ν z =
      finiteGeneratingValue μ (fun i => (Real.exp (h i) : ℂ) * z i) /
        (tiltPartition μ h : ℂ) := by
  classical
  unfold finiteGeneratingValue
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hatom, Complex.ofReal_div, Complex.ofReal_mul,
    generating_monomial_rescale]
  ring

lemma stronglyRayleighFinite_of_tilt_atoms
    (μ ν : ProbabilityMeasure (F → Bool)) (h : F → ℝ)
    (hμ : StronglyRayleighFinite μ) (hZ : tiltPartition μ h ≠ 0)
    (hatom : ∀ x : F → Bool,
      ((ν : Measure (F → Bool)) {x}).toReal =
        Real.exp (∑ i : F, h i * boolReal (x i)) *
          ((μ : Measure (F → Bool)) {x}).toReal / tiltPartition μ h) :
    StronglyRayleighFinite ν := by
  intro z hz
  rw [finiteGeneratingValue_of_tilt_atoms μ ν h hatom z]
  apply div_ne_zero
  · apply hμ
    intro i
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_pos (Real.exp_pos (h i)) (hz i)
  · exact_mod_cast hZ

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336AdditiveD139

theorem StronglyRayleighFinite.tiltCovariance_nonpos
    {F : Type u_1} [Fintype F] {μ : ProbabilityMeasure (F → Bool)}
    (hμ : StronglyRayleighFinite μ) (h : F → ℝ)
    (i j : F) (hij : i ≠ j) : tiltCovariance μ h i j ≤ 0 := by
  classical
  let weight : (F → Bool) → ℝ := fun x =>
    Real.exp (∑ k : F, h k * boolReal (x k)) *
      ((μ : Measure (F → Bool)) {x}).toReal
  let coeff (p q : Bool) (t : ℝ) : ℂ :=
    twoCoordinateCoefficient (fun x => (weight x : ℂ)) i j
      (fun _ => 1 + (t : ℂ) * Complex.I) p q
  have hcont (p q : Bool) : ContinuousAt (coeff p q) 0 := by
    apply Continuous.continuousAt
    exact (continuous_twoCoordinateCoefficient
      (fun x => (weight x : ℂ)) i j p q).comp (by fun_prop)
  have hzero (p q : Bool) : coeff p q 0 = (tiltPairMass μ h i j p q : ℂ) := by
    simpa [coeff, twoCoordinateWeight, tiltPairMass, weight] using
      (twoCoordinateWeight_cast_eq_coefficient weight i j p q).symm
  apply tiltCovariance_nonpos_of_pairMass
  apply bivariate_continuous_limit_rayleigh
    (coeff false false) (coeff true false) (coeff false true) (coeff true true)
    _ _ _ _ (hcont _ _) (hcont _ _) (hcont _ _) (hcont _ _)
    (hzero _ _) (hzero _ _) (hzero _ _) (hzero _ _)
  intro t ht z w hz hw
  let field := twoCoordinateField i j (fun _ : F => 1 + (t : ℂ) * Complex.I) z w
  have hfield (k : F) : 0 < (field k).im := by
    simp only [field, twoCoordinateField]
    split_ifs
    · exact hz
    · exact hw
    · simpa using ht
  have hstable := hμ (fun k => (Real.exp (h k) : ℂ) * field k) (fun k => by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_pos (Real.exp_pos (h k)) (hfield k))
  have hscale : finiteGeneratingValue μ (fun k => (Real.exp (h k) : ℂ) * field k) =
      ∑ x : F → Bool, (weight x : ℂ) *
        ∏ k : F, if x k = true then field k else 1 := by
    unfold finiteGeneratingValue
    apply Finset.sum_congr rfl
    intro x hx
    rw [generating_monomial_rescale]
    simp only [weight, Complex.ofReal_mul]
    ring
  rw [hscale, weighted_generating_two_coordinates _ _ i j hij z w] at hstable
  exact hstable

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Problem336AdditiveD139

variable {F : Type u_1} [Fintype F]

lemma sum_atomMass [DecidableEq F] (μ : ProbabilityMeasure (F → Bool)) :
    ∑ x : F → Bool, ((μ : Measure (F → Bool)) {x}).toReal = 1 := by
  classical
  rw [← ENNReal.toReal_sum]
  · simp
  · intro x hx
    exact measure_ne_top _ _

lemma exists_atomMass_pos (μ : ProbabilityMeasure (F → Bool)) :
    ∃ x : F → Bool, 0 < ((μ : Measure (F → Bool)) {x}).toReal := by
  classical
  have h := sum_atomMass μ
  have hp : 0 < ∑ x : F → Bool, ((μ : Measure (F → Bool)) {x}).toReal := by
    rw [h]
    norm_num
  obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg (fun x hx => ENNReal.toReal_nonneg)).mp hp
  exact ⟨x, hx⟩

lemma tiltPartition_pos (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) :
    0 < tiltPartition μ h := by
  classical
  obtain ⟨x, hx⟩ := exists_atomMass_pos μ
  unfold tiltPartition
  apply Finset.sum_pos'
  · intro y hy
    exact mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  · exact ⟨x, Finset.mem_univ x, mul_pos (Real.exp_pos _) hx⟩

lemma tiltPartition_ne_zero (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) :
    tiltPartition μ h ≠ 0 := ne_of_gt (tiltPartition_pos μ h)

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators ENNReal

namespace Problem336AdditiveD139
namespace GeneratingSlice

variable {F : Type u_1} [Fintype F] [DecidableEq F]

def countExcept (i : F) (x : F → Bool) : ℕ := by
  classical
  exact ∑ j ∈ Finset.univ.erase i, if x j = true then 1 else 0

def weight (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (x : F → Bool) : ℝ :=
  Real.exp (∑ j : F, h j * boolReal (x j)) * ((μ : Measure (F → Bool)) {x}).toReal

def slice (w : (F → Bool) → ℝ) (i : F) (b : Bool) : ℝ[X] := by
  classical
  exact ∑ x : F → Bool, if x i = b then C (w x) * X ^ countExcept i x else 0

omit [DecidableEq F] in
lemma weight_nonneg (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (x : F → Bool) :
    0 ≤ weight μ h x := mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg

lemma countExcept_cast (i : F) (x : F → Bool) :
    (countExcept i x : ℝ) = ∑ j ∈ Finset.univ.erase i, boolReal (x j) := by
  classical
  simp only [countExcept, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  cases x j <;> simp [boolReal]

lemma countExcept_add_bit (i : F) (x : F → Bool) :
    (countExcept i x : ℝ) + boolReal (x i) = ∑ j : F, boolReal (x j) := by
  classical
  rw [countExcept_cast]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

lemma monomial_except (i : F) (x : F → Bool) (z : ℂ) :
    (∏ j ∈ Finset.univ.erase i, if x j = true then z else 1) = z ^ countExcept i x := by
  classical
  unfold countExcept
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j hj
  cases x j <;> simp

lemma monomial_slice (i : F) (x : F → Bool) (z s : ℂ) :
    (∏ j : F, if x j = true then (if j = i then s else z) else 1) =
      (if x i = true then s else 1) * z ^ countExcept i x := by
  classical
  have hs := Finset.prod_erase_mul Finset.univ
    (fun j => if x j = true then (if j = i then s else z) else 1) (Finset.mem_univ i)
  rw [← hs]
  have he : (∏ j ∈ Finset.univ.erase i,
      if x j = true then (if j = i then s else z) else 1) =
      ∏ j ∈ Finset.univ.erase i, if x j = true then z else 1 := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  rw [he, monomial_except]
  simp [mul_comm]

lemma slice_eval (w : (F → Bool) → ℝ) (i : F) (b : Bool) (t : ℝ) :
    (slice w i b).eval t = ∑ x : F → Bool,
      if x i = b then w x * t ^ countExcept i x else 0 := by
  classical
  simp only [slice, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

lemma slice_eval_one (w : (F → Bool) → ℝ) (i : F) (b : Bool) :
    (slice w i b).eval 1 = ∑ x : F → Bool, if x i = b then w x else 0 := by
  simp [slice_eval]

lemma slice_aeval (w : (F → Bool) → ℝ) (i : F) (b : Bool) (z : ℂ) :
    aeval z (slice w i b) = ∑ x : F → Bool,
      if x i = b then (w x : ℂ) * z ^ countExcept i x else 0 := by
  classical
  simp only [slice, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

lemma slice_derivative_eval_one (w : (F → Bool) → ℝ) (i : F) (b : Bool) :
    (slice w i b).derivative.eval 1 = ∑ x : F → Bool,
      if x i = b then w x * (countExcept i x : ℝ) else 0 := by
  classical
  simp only [slice, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp [Polynomial.derivative_mul, Polynomial.derivative_X_pow]

lemma slice_coeff_nonneg (w : (F → Bool) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (i : F) (b : Bool) (n : ℕ) : 0 ≤ (slice w i b).coeff n := by
  classical
  simp only [slice, Polynomial.finsetSum_coeff]
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs <;> simp [hw]
  · simp

lemma slice_eval_one_add (w : (F → Bool) → ℝ) (i : F) :
    (slice w i false).eval 1 + (slice w i true).eval 1 = ∑ x : F → Bool, w x := by
  classical
  rw [slice_eval_one, slice_eval_one, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> simp

lemma slice_generating_identity (μ : ProbabilityMeasure (F → Bool))
    (h : F → ℝ) (i : F) (z s : ℂ) :
    aeval z (slice (weight μ h) i false) + s * aeval z (slice (weight μ h) i true) =
      finiteGeneratingValue μ (fun j => (Real.exp (h j) : ℂ) * (if j = i then s else z)) := by
  classical
  rw [slice_aeval, slice_aeval, Finset.mul_sum, ← Finset.sum_add_distrib]
  unfold finiteGeneratingValue
  apply Finset.sum_congr (by ext x; simp)
  intro x hx
  rw [generating_monomial_rescale, monomial_slice]
  cases x i <;> simp [weight, mul_comm, mul_assoc]

lemma slice_stable (μ : ProbabilityMeasure (F → Bool)) (hμ : StronglyRayleighFinite μ)
    (h : F → ℝ) (i : F) (z s : ℂ) (hz : 0 < z.im) (hs : 0 < s.im) :
    aeval z (slice (weight μ h) i false) + s * aeval z (slice (weight μ h) i true) ≠ 0 := by
  rw [slice_generating_identity]
  apply hμ
  intro j
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  apply mul_pos (Real.exp_pos _)
  split_ifs <;> assumption

lemma slice_true_eval_one (w : (F → Bool) → ℝ) (i : F) :
    (slice w i true).eval 1 = ∑ x : F → Bool, w x * boolReal (x i) := by
  rw [slice_eval_one]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> simp [boolReal]

lemma slice_derivative_add (w : (F → Bool) → ℝ) (i : F) :
    (slice w i false).derivative.eval 1 + (slice w i true).derivative.eval 1 =
      ∑ x : F → Bool, w x * (countExcept i x : ℝ) := by
  rw [slice_derivative_eval_one, slice_derivative_eval_one, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> simp

lemma slice_true_derivative_add (w : (F → Bool) → ℝ) (i : F) :
    (slice w i true).derivative.eval 1 + (slice w i true).eval 1 =
      ∑ x : F → Bool, w x * boolReal (x i) * (∑ j : F, boolReal (x j)) := by
  rw [slice_derivative_eval_one, slice_eval_one, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← countExcept_add_bit i x]
  cases x i <;> simp [boolReal]
  ring

lemma slice_total_derivative_add (w : (F → Bool) → ℝ) (i : F) :
    (slice w i false).derivative.eval 1 + (slice w i true).derivative.eval 1 +
        (slice w i true).eval 1 =
      ∑ x : F → Bool, w x * (∑ j : F, boolReal (x j)) := by
  rw [slice_derivative_add, slice_true_eval_one, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← countExcept_add_bit i x]
  ring

lemma slice_sum_eq_partition (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    (slice (weight μ h) i false).eval 1 + (slice (weight μ h) i true).eval 1 =
      tiltPartition μ h := by
  rw [slice_eval_one_add]
  unfold tiltPartition weight
  apply Finset.sum_congr (by ext; simp)
  intros
  rfl

lemma tiltMean_eq_slice (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    tiltMean μ h i = (slice (weight μ h) i true).eval 1 / tiltPartition μ h := by
  rw [slice_true_eval_one]
  unfold tiltMean weight
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intros
  rfl

lemma sum_tiltMean_eq_slice (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    (∑ j : F, tiltMean μ h j) =
      ((slice (weight μ h) i false).derivative.eval 1 +
        (slice (weight μ h) i true).derivative.eval 1 +
        (slice (weight μ h) i true).eval 1) / tiltPartition μ h := by
  rw [slice_total_derivative_add]
  unfold tiltMean
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro x hx
  simp [weight, Finset.mul_sum]

lemma sum_tiltSecondMoment_eq_slice (μ : ProbabilityMeasure (F → Bool))
    (h : F → ℝ) (i : F) :
    (∑ j : F, tiltSecondMoment μ h i j) =
      ((slice (weight μ h) i true).derivative.eval 1 +
        (slice (weight μ h) i true).eval 1) / tiltPartition μ h := by
  rw [slice_true_derivative_add]
  unfold tiltSecondMoment
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro x hx
  simp [weight, Finset.mul_sum]

theorem covariance_row_eq_slice (μ : ProbabilityMeasure (F → Bool))
    (h : F → ℝ) (i : F) :
    (∑ j : F, tiltCovariance μ h i j) =
      ((slice (weight μ h) i false).eval 1 * (slice (weight μ h) i true).eval 1 +
        (slice (weight μ h) i false).eval 1 * (slice (weight μ h) i true).derivative.eval 1 -
        (slice (weight μ h) i true).eval 1 * (slice (weight μ h) i false).derivative.eval 1) /
      (tiltPartition μ h) ^ 2 := by
  simp only [tiltCovariance, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_tiltSecondMoment_eq_slice, sum_tiltMean_eq_slice μ h i, tiltMean_eq_slice]
  have hZ := tiltPartition_ne_zero μ h
  have heq := slice_sum_eq_partition μ h i
  field_simp
  rw [← heq]
  ring

theorem covariance_row_nonneg_of_slice_bound (μ : ProbabilityMeasure (F → Bool))
    (h : F → ℝ) (i : F)
    (hbound : (slice (weight μ h) i true).eval 1 *
        (slice (weight μ h) i false).derivative.eval 1 -
        (slice (weight μ h) i false).eval 1 * (slice (weight μ h) i true).derivative.eval 1 ≤
        (slice (weight μ h) i false).eval 1 * (slice (weight μ h) i true).eval 1) :
    0 ≤ ∑ j : F, tiltCovariance μ h i j := by
  rw [covariance_row_eq_slice]
  exact div_nonneg (by linarith) (sq_nonneg _)

end GeneratingSlice
end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set Filter Polynomial
open scoped Topology

namespace Problem336AdditiveD139

lemma analytic_eq_zero_of_im_nonpos_of_zero {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U)
    (him : ∀ z ∈ U, (f z).im ≤ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hzero : f z₀ = 0) :
    ∀ z ∈ U, f z = 0 := by
  rcases hf.is_constant_or_isOpen hUc with ⟨c, hc⟩ | hopen
  · have hc0 : c = 0 := (hc z₀ hz₀).symm.trans hzero
    simpa [hc0] using hc
  · have hiopen : IsOpen (f '' U) := hopen U Subset.rfl hU
    have hmem : (0 : ℂ) ∈ f '' U := ⟨z₀, hz₀, hzero⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hiopen.mem_nhds hmem)
    have hpoint : ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ Metric.ball (0 : ℂ) ε := by
      simp only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    obtain ⟨z, hz, heq⟩ := hball hpoint
    have h := him z hz
    rw [heq] at h
    norm_num at h
    linarith

lemma affine_stable_normalized_slope_im_neg (a b : ℂ)
    (hstable : ∀ w : ℂ, 0 < w.im → a + w * b ≠ 0) (hb : b ≠ 0) :
    (b / (a + Complex.I * b)).im < 0 := by
  have hr : 0 ≤ (a / b).im := by
    by_contra! hneg
    have hw : 0 < (-(a / b)).im := by simpa using neg_pos.mpr hneg
    apply hstable (-(a / b)) hw
    rw [neg_mul, div_mul_cancel₀ _ hb]
    ring
  have him : 0 < (a / b + Complex.I).im := by
    simp only [Complex.add_im, Complex.I_im]
    linarith
  have hne : a / b + Complex.I ≠ 0 := by
    intro h
    rw [h] at him
    norm_num at him
  have hid : b / (a + Complex.I * b) = (a / b + Complex.I)⁻¹ := by
    rw [show a / b + Complex.I = (a + Complex.I * b) / b by
      rw [add_div, mul_div_cancel_right₀ _ hb], inv_div]
  rw [hid, Complex.inv_im]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos him) (Complex.normSq_pos.mpr hne)

theorem affine_stable_analytic_slope_zero_or_nonvanishing
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (A B : ℂ → ℂ) (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (hstable : ∀ z ∈ U, ∀ w : ℂ, 0 < w.im → A z + w * B z ≠ 0) :
    (∀ z ∈ U, B z = 0) ∨ (∀ z ∈ U, B z ≠ 0) := by
  classical
  by_cases hzero : ∀ z ∈ U, B z = 0
  · exact Or.inl hzero
  right
  intro z₀ hz₀ hBzero
  let f : ℂ → ℂ := fun z => B z / (A z + Complex.I * B z)
  have hden : ∀ z ∈ U, A z + Complex.I * B z ≠ 0 := by
    intro z hz
    exact hstable z hz Complex.I (by norm_num)
  have hf : AnalyticOnNhd ℂ f U := by
    intro z hz
    exact (hB z hz).div ((hA z hz).add (analyticAt_const.mul (hB z hz))) (hden z hz)
  have him : ∀ z ∈ U, (f z).im ≤ 0 := by
    intro z hz
    by_cases hb : B z = 0
    · simp [f, hb]
    · exact (affine_stable_normalized_slope_im_neg (A z) (B z) (hstable z hz) hb).le
  have hfzero : f z₀ = 0 := by simp [f, hBzero]
  have hfall := analytic_eq_zero_of_im_nonpos_of_zero hU hUc hf him hz₀ hfzero
  apply hzero
  intro z hz
  have h := hfall z hz
  exact (div_eq_zero_iff.mp h).resolve_right (hden z hz)

theorem affine_stable_entire_slope_nonvanishing
    (A B : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A {z : ℂ | 0 < z.im})
    (hB : AnalyticOnNhd ℂ B Set.univ)
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im → A z + w * B z ≠ 0)
    {z₁ : ℂ} (hne : B z₁ ≠ 0) :
    ∀ z : ℂ, 0 < z.im → B z ≠ 0 := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  rcases affine_stable_analytic_slope_zero_or_nonvanishing hU hUc A B hA
    (hB.mono (subset_univ _)) (fun z hz w hw => hstable z w hz hw) with hzero | hnonzero
  · have hevent : ∀ᶠ z in 𝓝 Complex.I, B z = 0 := by
      filter_upwards [hU.mem_nhds (by norm_num : Complex.I ∈ {z : ℂ | 0 < z.im})]
        with z hz using hzero z hz
    have hall := hB.eqOn_of_preconnected_of_eventuallyEq
      (g := fun _ : ℂ => 0) analyticOnNhd_const isPreconnected_univ
      (mem_univ Complex.I) hevent
    exact (hne (hall (mem_univ z₁))).elim
  · exact hnonzero

theorem polynomial_slope_stable_of_affine_stable (p q : ℝ[X]) (hq : q ≠ 0)
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      aeval z p + w * aeval z q ≠ 0) :
    ∀ z : ℂ, 0 < z.im → aeval z q ≠ 0 := by
  have hex : ∃ t : ℝ, q.eval t ≠ 0 := by
    by_contra! h
    apply hq
    apply Polynomial.funext
    intro t
    simpa using h t
  obtain ⟨t, ht⟩ := hex
  apply affine_stable_entire_slope_nonvanishing
    (fun z : ℂ => aeval z p) (fun z : ℂ => aeval z q)
    (fun z _ => analyticAt_id.aeval_polynomial p)
    (fun z _ => analyticAt_id.aeval_polynomial q) hstable (z₁ := (t : ℂ))
  have heq : aeval (t : ℂ) q = ((q.eval t : ℝ) : ℂ) :=
    Polynomial.aeval_ofReal (K := ℂ) q t
  exact heq.trans_ne (by exact_mod_cast ht)

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Polynomial
open scoped ComplexConjugate

namespace Problem336AdditiveD139

theorem aeval_root_im_eq_zero_of_stable (p : ℝ[X])
    (hstable : ∀ z : ℂ, 0 < z.im → aeval z p ≠ 0)
    (z : ℂ) (hz : aeval z p = 0) : z.im = 0 := by
  have hle : z.im ≤ 0 := by
    by_contra! h
    exact hstable z h hz
  have hge : 0 ≤ z.im := by
    by_contra! h
    have hconj : aeval (conj z) p = 0 := by
      rw [Polynomial.aeval_conj, hz, map_zero]
    exact hstable (conj z) (by simpa using neg_pos.mpr h) hconj
  exact le_antisymm hle hge

theorem splits_of_upper_halfplane_stable (p : ℝ[X])
    (hstable : ∀ z : ℂ, 0 < z.im → aeval z p ≠ 0) : p.Splits := by
  apply Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ)
      (IsAlgClosed.splits _)
  intro z hz
  have heval : aeval z p = 0 := by
    simpa only [Polynomial.IsRoot, eval_map, aeval_def, eval₂_at_apply] using
      (Polynomial.isRoot_of_mem_roots hz)
  have him := aeval_root_im_eq_zero_of_stable p hstable z heval
  refine ⟨z.re, ?_⟩
  apply Complex.ext <;> simp [him]

theorem eval_pos_of_nonnegative_coefficients (p : ℝ[X])
    (hp : p ≠ 0) (hcoeff : ∀ n : ℕ, 0 ≤ p.coeff n)
    {t : ℝ} (ht : 0 < t) : 0 < p.eval t := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_pos
  · intro n hn
    exact mul_pos (lt_of_le_of_ne (hcoeff n)
      (Ne.symm (Polynomial.mem_support_iff.mp hn))) (pow_pos ht n)
  · exact Polynomial.support_nonempty.mpr hp

theorem aeval_root_re_nonpos_of_nonnegative_coefficients (p : ℝ[X])
    (hstable : ∀ z : ℂ, 0 < z.im → aeval z p ≠ 0)
    (hcoeff : ∀ n : ℕ, 0 ≤ p.coeff n)
    (z : ℂ) (hz : aeval z p = 0) : z.re ≤ 0 := by
  have hp : p ≠ 0 := by
    intro h
    have := hstable Complex.I (by simp)
    simp [h] at this
  have him := aeval_root_im_eq_zero_of_stable p hstable z hz
  have hreal : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [him]
  by_contra! hpos
  have heval : p.eval z.re = 0 := by
    have hc : ((p.eval z.re : ℝ) : ℂ) = 0 := by
      calc
        ((p.eval z.re : ℝ) : ℂ) = aeval (z.re : ℂ) p :=
          (Polynomial.aeval_ofReal (K := ℂ) p z.re).symm
        _ = 0 := by rw [hreal]; exact hz
    exact_mod_cast hc
  have := eval_pos_of_nonnegative_coefficients p hp hcoeff hpos
  linarith

theorem aeval_ne_zero_on_slitPlane_of_stable (p : ℝ[X])
    (hstable : ∀ z : ℂ, 0 < z.im → aeval z p ≠ 0)
    (hcoeff : ∀ n : ℕ, 0 ≤ p.coeff n)
    {z : ℂ} (hz : z ∈ Complex.slitPlane) : aeval z p ≠ 0 := by
  intro hzero
  rcases hz with hre | him
  · exact (not_lt_of_ge
      (aeval_root_re_nonpos_of_nonnegative_coefficients p hstable hcoeff z hzero)) hre
  · exact him (aeval_root_im_eq_zero_of_stable p hstable z hzero)

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Polynomial
open scoped ComplexConjugate

namespace Problem336AdditiveD139

theorem polynomial_ratio_im_nonneg_of_affine_stable (p q : ℝ[X])
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      aeval z p + w * aeval z q ≠ 0)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (aeval z p / aeval z q).im := by
  by_cases hq : aeval z q = 0
  · simp [hq]
  · by_contra! hneg
    have hw : 0 < (-(aeval z p / aeval z q)).im := by
      simpa using neg_pos.mpr hneg
    apply hstable z (-(aeval z p / aeval z q)) hz hw
    rw [neg_mul, div_mul_cancel₀ _ hq]
    ring

theorem polynomial_ratio_conj (p q : ℝ[X]) (z : ℂ) :
    aeval (conj z) p / aeval (conj z) q =
      conj (aeval z p / aeval z q) := by
  rw [Polynomial.aeval_conj, Polynomial.aeval_conj, map_div₀]

theorem polynomial_ratio_im_nonpos_of_affine_stable (p q : ℝ[X])
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      aeval z p + w * aeval z q ≠ 0)
    {z : ℂ} (hz : z.im < 0) :
    (aeval z p / aeval z q).im ≤ 0 := by
  have h := polynomial_ratio_im_nonneg_of_affine_stable p q hstable
    (z := conj z) (by simpa using neg_pos.mpr hz)
  rw [polynomial_ratio_conj] at h
  change 0 ≤ -(aeval z p / aeval z q).im at h
  linarith

theorem polynomial_ratio_analyticOnNhd_slitPlane (p q : ℝ[X])
    (hstable : ∀ z : ℂ, 0 < z.im → aeval z q ≠ 0)
    (hcoeff : ∀ n : ℕ, 0 ≤ q.coeff n) :
    AnalyticOnNhd ℂ (fun z : ℂ => aeval z p / aeval z q) Complex.slitPlane := by
  intro z hz
  exact (analyticAt_id.aeval_polynomial p).div
    (analyticAt_id.aeval_polynomial q)
    (aeval_ne_zero_on_slitPlane_of_stable q hstable hcoeff hz)

theorem polynomial_ratio_ofReal_pos (p q : ℝ[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpcoeff : ∀ n : ℕ, 0 ≤ p.coeff n)
    (hqcoeff : ∀ n : ℕ, 0 ≤ q.coeff n)
    {t : ℝ} (ht : 0 < t) :
    0 < (aeval (t : ℂ) p / aeval (t : ℂ) q).re := by
  have hpos := div_pos
    (eval_pos_of_nonnegative_coefficients p hp hpcoeff ht)
    (eval_pos_of_nonnegative_coefficients q hq hqcoeff ht)
  have heq : aeval (t : ℂ) p / aeval (t : ℂ) q =
      ((p.eval t / q.eval t : ℝ) : ℂ) := by
    calc
      _ = ((p.eval t : ℝ) : ℂ) / ((q.eval t : ℝ) : ℂ) :=
        congrArg₂ (· / ·) (Polynomial.aeval_ofReal (K := ℂ) p t)
          (Polynomial.aeval_ofReal (K := ℂ) q t)
      _ = _ := by simp
  simpa [heq] using hpos

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open Set Metric

namespace Problem336AdditiveD139

lemma cayley_rightHalfPlane (z : ℂ) (hz : ‖z‖ < 1) :
    0 < ((1 + z) / (1 - z)).re := by
  have hn : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hd : 1 - z ≠ 0 := by
    intro he
    have : z = 1 := by linear_combination -he
    simp [this] at hz
  rw [Complex.div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr hd)
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re,
    Complex.add_im, Complex.one_im, Complex.sub_im, zero_add, zero_sub]
  rw [Complex.normSq_apply] at hn
  nlinarith

lemma cayley_norm_le_one (z : ℂ) (r : ℝ) (hr : 0 < r) (hz : 0 < z.re) :
    ‖(z - r) / (z + r)‖ ≤ 1 := by
  have hd : z + (r : ℂ) ≠ 0 := by
    intro hh
    have := congrArg Complex.re hh
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
    linarith
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hd), one_mul]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, add_zero]
  nlinarith

theorem rightHalfPlane_derivative_bound
    (f : ℂ → ℂ) (f' : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f {z | 0 < z.re})
    (hmap : ∀ z : ℂ, 0 < z.re → 0 < (f z).re)
    (hvalue : f 1 = (r : ℂ)) (hderiv : HasDerivAt f f' 1) :
    ‖f'‖ ≤ r := by
  let T : ℂ → ℂ := fun z => (1 + z) / (1 - z)
  let g : ℂ → ℂ := fun z => (f (T z) - r) / (f (T z) + r)
  have hTmap : MapsTo T (ball 0 1) {z | 0 < z.re} := by
    intro z hz
    exact cayley_rightHalfPlane z (by simpa using hz)
  have hTden : ∀ z ∈ ball (0 : ℂ) 1, 1 - z ≠ 0 := by
    intro z hz he
    have hze : z = 1 := by linear_combination -he
    simp [hze] at hz
  have hTd : DifferentiableOn ℂ T (ball 0 1) := by
    exact (differentiableOn_id.const_add 1).div
      (differentiableOn_id.const_sub 1) hTden
  have hfd : DifferentiableOn ℂ (fun z => f (T z)) (ball 0 1) :=
    hf.comp hTd hTmap
  have hden : ∀ z ∈ ball (0 : ℂ) 1, f (T z) + (r : ℂ) ≠ 0 := by
    intro z hz he
    have hp := hmap (T z) (hTmap hz)
    have he' := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at he'
    linarith
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    (hfd.sub_const _).div (hfd.add_const _) hden
  have hg0 : g 0 = 0 := by simp [g, T, hvalue]
  have hgmap : MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
    intro z hz
    rw [hg0, mem_closedBall_zero_iff]
    exact cayley_norm_le_one (f (T z)) r hr (hmap _ (hTmap hz))
  have hTderiv : HasDerivAt T 2 0 := by
    have hp : HasDerivAt (fun z : ℂ => 1 + z) 1 0 :=
      (hasDerivAt_id (0 : ℂ)).const_add 1
    have hm : HasDerivAt (fun z : ℂ => 1 - z) (-1) 0 :=
      (hasDerivAt_id (0 : ℂ)).const_sub 1
    have hd := hp.div hm (by norm_num : (1 : ℂ) - 0 ≠ 0)
    norm_num at hd
    exact hd
  have hfderiv : HasDerivAt (fun z => f (T z)) (f' * 2) 0 := by
    have hd' : HasDerivAt f f' (T 0) := by simpa [T] using hderiv
    exact hd'.comp 0 hTderiv
  have hgderiv : HasDerivAt g (f' / r) 0 := by
    have hd := (hfderiv.sub_const (r : ℂ)).div (hfderiv.add_const (r : ℂ))
      (hden 0 (by simp))
    have he : (f' * 2 * (f (T 0) + r) - (f (T 0) - r) * (f' * 2)) /
        (f (T 0) + r) ^ 2 = f' / r := by
      simp only [T, add_zero, sub_zero, div_one, hvalue]
      field_simp
      ring
    rw [he] at hd
    exact hd
  have hb := Complex.norm_deriv_le_one_of_mapsTo_ball hgd hgmap (by norm_num : (0 : ℝ) < 1)
  rw [hgderiv.deriv, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hb
  exact (div_le_one hr).mp hb

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open Set

namespace Problem336AdditiveD139

lemma sq_mem_slitPlane_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z ^ 2 ∈ Complex.slitPlane := by
  by_cases hi : z.im = 0
  · left
    simp only [pow_two, Complex.mul_re, hi, mul_zero, sub_zero]
    exact mul_pos hz hz
  · right
    simp only [pow_two, Complex.mul_im]
    rw [mul_comm z.im z.re, ← two_mul]
    exact mul_ne_zero (by norm_num) (mul_ne_zero (ne_of_gt hz) hi)

lemma sqrt_re_pos_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < (Complex.sqrt z).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.2
  apply div_pos _ (by norm_num)
  rcases hz with hr | hi
  · linarith [norm_nonneg z]
  · have hab := Complex.abs_re_lt_norm.mpr hi
    have hneg := neg_abs_le z.re
    linarith

lemma complex_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  rw [Complex.sqrt, ← Complex.cpow_mul_nat]
  norm_num

theorem slitPlane_derivative_bound
    (f : ℂ → ℂ) (f' : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f Complex.slitPlane)
    (hmap : MapsTo f Complex.slitPlane Complex.slitPlane)
    (hvalue : f 1 = (r : ℂ)) (hderiv : HasDerivAt f f' 1) :
    ‖f'‖ ≤ r := by
  let H : ℂ → ℂ := fun z => Complex.sqrt (f (z ^ 2))
  have hsquare : MapsTo (fun z : ℂ => z ^ 2) {z | 0 < z.re}
      Complex.slitPlane := fun _ hz => sq_mem_slitPlane_of_re_pos hz
  have hHd : DifferentiableOn ℂ H {z | 0 < z.re} :=
    Complex.differentiableOn_sqrt.comp
      (hf.comp (differentiableOn_id.pow 2) hsquare)
      (hmap.comp hsquare)
  have hHmap : ∀ z : ℂ, 0 < z.re → 0 < (H z).re := by
    intro z hz
    exact sqrt_re_pos_of_mem_slitPlane (hmap (hsquare hz))
  have hHvalue : H 1 = (Real.sqrt r : ℂ) := by
    dsimp [H]
    rw [one_pow, hvalue]
    exact Complex.sqrt_of_nonneg (by exact_mod_cast hr.le)
  have hone : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by norm_num
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hHderiv := (hHd.differentiableAt (hopen.mem_nhds hone)).hasDerivAt
  have hbound := rightHalfPlane_derivative_bound H (deriv H 1) (Real.sqrt r)
    (Real.sqrt_pos.2 hr) hHd hHmap hHvalue hHderiv
  have hsquarederiv : HasDerivAt (fun z : ℂ => z ^ 2) 2 1 := by
    simpa using (hasDerivAt_pow 2 (1 : ℂ))
  have hcomp : HasDerivAt (fun z : ℂ => f (z ^ 2)) (f' * 2) 1 := by
    have hd : HasDerivAt f f' ((1 : ℂ) ^ 2) := by simpa using hderiv
    exact hd.comp 1 hsquarederiv
  have hprod : HasDerivAt (fun z : ℂ => f (z ^ 2))
      (2 * H 1 * deriv H 1) 1 := by
    have hh := hHderiv.pow 2
    have hfun : H ^ 2 = (fun z : ℂ => f (z ^ 2)) := by
      funext z
      exact complex_sqrt_sq _
    rw [hfun] at hh
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hh
  have heq : (Real.sqrt r : ℂ) * deriv H 1 = f' := by
    have hh := hprod.unique hcomp
    rw [hHvalue] at hh
    linear_combination hh / 2
  rw [← heq, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg r)]
  calc
    Real.sqrt r * ‖deriv H 1‖ ≤ Real.sqrt r * Real.sqrt r :=
      mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg r)
    _ = r := Real.mul_self_sqrt hr.le

theorem weakPick_derivative_re_le
    (f : ℂ → ℂ) (f' : ℂ)
    (hf : DifferentiableOn ℂ f Complex.slitPlane)
    (hupper : ∀ z : ℂ, 0 < z.im → 0 ≤ (f z).im)
    (hlower : ∀ z : ℂ, z.im < 0 → (f z).im ≤ 0)
    (hreal : ∀ x : ℝ, 0 < x →
      0 ≤ (f (x : ℂ)).re ∧ (f (x : ℂ)).im = 0)
    (hderiv : HasDerivAt f f' 1) :
    f'.re ≤ (f 1).re := by
  let g : ℂ → ℂ := fun z => f z + z
  have hmap : MapsTo g Complex.slitPlane Complex.slitPlane := by
    intro z hz
    rcases lt_trichotomy z.im 0 with hi | hi | hi
    · right
      have hfi := hlower z hi
      change (f z).im + z.im ≠ 0
      linarith
    · left
      have hzr : 0 < z.re := hz.resolve_right (not_not.mpr hi)
      have hzreal : (z.re : ℂ) = z := by
        apply Complex.ext <;> simp [hi]
      have hnonneg := (hreal z.re hzr).1
      rw [hzreal] at hnonneg
      change 0 < (f z).re + z.re
      linarith
    · right
      have hfi := hupper z hi
      change (f z).im + z.im ≠ 0
      linarith
  have h1 := hreal 1 (by norm_num)
  have hr : 0 < (f 1).re + 1 := by norm_num at h1 ⊢; linarith [h1.1]
  have hvalue : g 1 = (((f 1).re + 1 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [g]
    · simpa [g] using h1.2
  have hb := slitPlane_derivative_bound g (f' + 1) ((f 1).re + 1) hr
    (hf.add differentiableOn_id) hmap hvalue (hderiv.add (hasDerivAt_id 1))
  have hre := Complex.re_le_norm (f' + 1)
  simp only [Complex.add_re, Complex.one_re] at hre
  linarith

theorem reflectedPick_derivative_re_le
    (f : ℂ → ℂ) (f' : ℂ)
    (hf : DifferentiableOn ℂ f Complex.slitPlane)
    (hupper : ∀ z : ℂ, 0 < z.im → 0 ≤ (f z).im)
    (hconj : ∀ z : ℂ, f (star z) = star (f z))
    (hreal : ∀ x : ℝ, 0 < x → 0 ≤ (f (x : ℂ)).re)
    (hderiv : HasDerivAt f f' 1) :
    f'.re ≤ (f 1).re := by
  apply weakPick_derivative_re_le f f' hf hupper
  · intro z hz
    have hh := hupper (star z) (by simpa using neg_pos.mpr hz)
    rw [hconj] at hh
    simpa using hh
  · intro x hx
    refine ⟨hreal x hx, ?_⟩
    have hh := congrArg Complex.im (hconj (x : ℂ))
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_im] at hh
    linarith
  · exact hderiv

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Polynomial Set
open scoped ComplexConjugate

namespace Problem336AdditiveD139

theorem stable_wronskian_of_denominator_stable (p q : ℝ[X])
    (hpcoeff : ∀ n : ℕ, 0 ≤ p.coeff n)
    (hqcoeff : ∀ n : ℕ, 0 ≤ q.coeff n)
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      aeval z p + w * aeval z q ≠ 0)
    (hqstable : ∀ z : ℂ, 0 < z.im → aeval z q ≠ 0) :
    q.eval 1 * p.derivative.eval 1 - p.eval 1 * q.derivative.eval 1 ≤
      p.eval 1 * q.eval 1 := by
  by_cases hp : p = 0
  · simp [hp]
  have hq : q ≠ 0 := by
    intro hq
    simpa [hq] using hqstable Complex.I (by simp)
  have hqpos : 0 < q.eval 1 :=
    eval_pos_of_nonnegative_coefficients q hq hqcoeff (by norm_num)
  have heval (P : ℝ[X]) : aeval (1 : ℂ) P = ((P.eval 1 : ℝ) : ℂ) := by
    simpa using Polynomial.aeval_ofReal (K := ℂ) P (1 : ℝ)
  have hqne : aeval (1 : ℂ) q ≠ 0 := by
    rw [heval]
    exact_mod_cast ne_of_gt hqpos
  have hderiv := (p.hasDerivAt_aeval (1 : ℂ)).div
    (q.hasDerivAt_aeval (1 : ℂ)) hqne
  have hbound := reflectedPick_derivative_re_le
    (fun z : ℂ => aeval z p / aeval z q) _
    (polynomial_ratio_analyticOnNhd_slitPlane p q hqstable hqcoeff).differentiableOn
    (fun z hz => polynomial_ratio_im_nonneg_of_affine_stable p q hstable hz)
    (fun z => polynomial_ratio_conj p q z)
    (fun t ht => (polynomial_ratio_ofReal_pos p q hp hq hpcoeff hqcoeff ht).le)
    hderiv
  simp only [heval, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re] at hbound
  have hmul := (div_le_iff₀ (sq_pos_of_pos hqpos)).mp hbound
  have hsimp : p.eval 1 / q.eval 1 * q.eval 1 ^ 2 = p.eval 1 * q.eval 1 := by
    field_simp
  rw [hsimp] at hmul
  nlinarith

theorem stable_affine_wronskian_bound (p q : ℝ[X])
    (hpcoeff : ∀ n : ℕ, 0 ≤ p.coeff n)
    (hqcoeff : ∀ n : ℕ, 0 ≤ q.coeff n)
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      aeval z p + w * aeval z q ≠ 0) :
    q.eval 1 * p.derivative.eval 1 - p.eval 1 * q.derivative.eval 1 ≤
      p.eval 1 * q.eval 1 := by
  by_cases hq : q = 0
  · simp [hq]
  exact stable_wronskian_of_denominator_stable p q hpcoeff hqcoeff hstable
    (polynomial_slope_stable_of_affine_stable p q hq hstable)

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate
namespace Problem336AdditiveD139

lemma response_exponent_coordinate {F : Type u_1} [Fintype F]
    (h : F → ℝ) (j : F) (r : ℝ) (x : F → Bool) :
    (∑ k : F, coordinatePerturb h j r k * boolReal (x k)) =
      (∑ k : F, h k * boolReal (x k)) + r * boolReal (x j) := by
  classical
  simp [coordinatePerturb, add_mul, Finset.sum_add_distrib, ite_mul]

lemma hasDerivAt_tiltSum_coordinate {F : Type u_2} [Fintype F] [DecidableEq F]
    (h : F → ℝ) (j : F) (q : (F → Bool) → ℝ) :
    HasDerivAt
      (fun r : ℝ => ∑ x : F → Bool,
        Real.exp (∑ k : F, coordinatePerturb h j r k * boolReal (x k)) * q x)
      (∑ x : F → Bool,
        Real.exp (∑ k : F, h k * boolReal (x k)) * q x * boolReal (x j)) 0 := by
  classical
  simp_rw [response_exponent_coordinate]
  have hd : ∀ x ∈ (Finset.univ : Finset (F → Bool)),
      HasDerivAt (fun r : ℝ =>
        Real.exp ((∑ k : F, h k * boolReal (x k)) + r * boolReal (x j)) * q x)
        (Real.exp (∑ k : F, h k * boolReal (x k)) * q x * boolReal (x j)) 0 := by
    intro x hx
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (boolReal (x j))).const_add
        (∑ k : F, h k * boolReal (x k))) |>.exp.mul_const (q x)
  exact HasDerivAt.fun_sum hd

lemma tiltMean_hasDerivAt_coordinate_of_pos {F : Type u_3} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F)
    (hpos : 0 < tiltPartition μ h) :
    HasDerivAt (fun r : ℝ => tiltMean μ (coordinatePerturb h j r) i)
      (tiltCovariance μ h i j) 0 := by
  classical
  let m : (F → Bool) → ℝ := fun x => ((μ : Measure (F → Bool)) {x}).toReal
  have hnum := hasDerivAt_tiltSum_coordinate h j (fun x => m x * boolReal (x i))
  have hden := hasDerivAt_tiltSum_coordinate h j m
  have hz : (∑ x : F → Bool,
      Real.exp (∑ k : F, coordinatePerturb h j 0 k * boolReal (x k)) * m x) ≠ 0 := by
    simpa [coordinatePerturb, tiltPartition, m] using ne_of_gt hpos
  have hd := hnum.div hden hz
  apply HasDerivAt.congr_of_eventuallyEq (f := fun r =>
      (∑ x : F → Bool, Real.exp (∑ k : F, coordinatePerturb h j r k * boolReal (x k)) *
         (m x * boolReal (x i))) /
      (∑ x : F → Bool, Real.exp (∑ k : F, coordinatePerturb h j r k * boolReal (x k)) * m x))
  · apply hd.congr_deriv
    simp only [tiltMean, tiltPartition, tiltCovariance, tiltSecondMoment,
      coordinatePerturb, ite_self, add_zero, m, mul_assoc]
    have hne : (∑ x : F → Bool,
      Real.exp (∑ k : F, h k * boolReal (x k)) * ((μ : Measure (F → Bool)) {x}).toReal) ≠ 0 :=
      ne_of_gt hpos
    field_simp [hne]
  · filter_upwards [] with r
    simp [tiltMean, tiltPartition, m, mul_assoc]

lemma tiltMean_hasDerivAt_coordinate {F : Type u_4} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) :
    HasDerivAt (fun r : ℝ => tiltMean μ (coordinatePerturb h j r) i)
      (tiltCovariance μ h i j) 0 :=
  tiltMean_hasDerivAt_coordinate_of_pos μ h i j (tiltPartition_pos μ h)

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Problem336AdditiveD139

theorem hasDerivAt_tilt_weighted_sum
    {F : Type u_1} [Fintype F] [DecidableEq F] (μ : ProbabilityMeasure (F → Bool))
    (h v : F → ℝ) (f : (F → Bool) → ℝ) (t : ℝ) :
    HasDerivAt
      (fun r : ℝ => ∑ x : F → Bool,
        Real.exp (∑ k : F, (h k + r * v k) * boolReal (x k)) *
        ((μ : Measure (F → Bool)) {x}).toReal * f x)
      (∑ k : F, (∑ x : F → Bool,
        Real.exp (∑ j : F, (h j + t * v j) * boolReal (x j)) *
        ((μ : Measure (F → Bool)) {x}).toReal * f x * boolReal (x k)) * v k) t := by
  classical
  have hlin (x : F → Bool) :
      HasDerivAt (fun r : ℝ => ∑ k : F, (h k + r * v k) * boolReal (x k))
        (∑ k : F, v k * boolReal (x k)) t := by
    apply HasDerivAt.fun_sum
    intro k hk
    simpa using (((hasDerivAt_id t).mul_const (v k)).const_add (h k)).mul_const
      (boolReal (x k))
  have hw (x : F → Bool) :=
    (((hlin x).exp).mul_const (((μ : Measure (F → Bool)) {x}).toReal)).mul_const (f x)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => hw x)
  refine hs.congr_deriv (Eq.symm ?_)
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro x hx
  ring

private theorem quotient_covariance_sum
    {F : Type u_2} [Fintype F] (Z A : ℝ) (B C v : F → ℝ) (hZ : Z ≠ 0) :
    ((∑ k : F, C k * v k) * Z - A * (∑ k : F, B k * v k)) / Z ^ 2 =
      ∑ k : F, (C k / Z - A / Z * (B k / Z)) * v k := by
  classical
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  field_simp

theorem tiltMean_hasDerivAt_affine_of_ne_zero
    {F : Type u_3} [Fintype F] (μ : ProbabilityMeasure (F → Bool))
    (h v : F → ℝ) (i : F) (t : ℝ)
    (hZ : tiltPartition μ (fun k => h k + t * v k) ≠ 0) :
    HasDerivAt (fun r : ℝ => tiltMean μ (fun k => h k + r * v k) i)
      (∑ k : F, tiltCovariance μ (fun j => h j + t * v j) i k * v k) t := by
  classical
  have hnum := hasDerivAt_tilt_weighted_sum μ h v (fun x => boolReal (x i)) t
  have hden := hasDerivAt_tilt_weighted_sum μ h v (fun _ => 1) t
  simp only [mul_one] at hden
  have hZ' : (∑ x : F → Bool,
      Real.exp (∑ k : F, (h k + t * v k) * boolReal (x k)) *
        ((μ : Measure (F → Bool)) {x}).toReal) ≠ 0 := hZ
  have hquot := hnum.div hden hZ'
  convert hquot using 1 <;> try rfl
  simp only [tiltCovariance, tiltSecondMoment, tiltMean, tiltPartition]
  symm
  exact quotient_covariance_sum _ _ _ _ _ hZ'

theorem tiltMean_hasDerivAt_affine
    {F : Type u_4} [Fintype F] (μ : ProbabilityMeasure (F → Bool))
    (h v : F → ℝ) (i : F) (t : ℝ) :
    HasDerivAt (fun r : ℝ => tiltMean μ (fun k => h k + r * v k) i)
      (∑ k : F, tiltCovariance μ (fun j => h j + t * v j) i k * v k) t :=
  tiltMean_hasDerivAt_affine_of_ne_zero μ h v i t (tiltPartition_ne_zero μ _)

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem336AdditiveD139

theorem covariance_direction_bound {F : Type u_1} [Fintype F]
    (c v : F → ℝ) (D C : ℝ) (hD : 0 ≤ D)
    (hv : ∀ j, |v j| ≤ D) (hc : ∑ j, |c j| ≤ C) :
    |∑ j, c j * v j| ≤ C * D := by
  calc
    |∑ j, c j * v j| ≤ ∑ j, |c j * v j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |c j| * |v j| := by simp only [abs_mul]
    _ ≤ ∑ j, |c j| * D := by
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
    _ = (∑ j, |c j|) * D := by rw [Finset.sum_mul]
    _ ≤ C * D := mul_le_mul_of_nonneg_right hc hD

theorem finite_response_lipschitz_of_directional_deriv
    {F : Type u_2} [Fintype F]
    (f : (F → ℝ) → ℝ) (c : (F → ℝ) → F → ℝ) (C : ℝ)
    (hderiv : ∀ (h v : F → ℝ) (t : ℝ),
      HasDerivAt (fun s : ℝ => f (fun j => h j + s * v j))
        (∑ j, c (fun k => h k + t * v k) j * v j) t)
    (hrow : ∀ h : F → ℝ, ∑ j, |c h j| ≤ C)
    (h h' : F → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hdist : ∀ j, |h j - h' j| ≤ D) :
    |f h - f h'| ≤ C * D := by
  let v : F → ℝ := fun j => h j - h' j
  have hsegment :
      ‖f (fun j => h' j + 1 * v j) - f (fun j => h' j + 0 * v j)‖ ≤ C * D := by
    apply norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t _ => (hderiv h' v t).hasDerivWithinAt)
    intro t _
    rw [Real.norm_eq_abs]
    exact covariance_direction_bound _ v D C hD hdist (hrow _)
  simpa [v, Real.norm_eq_abs] using hsegment

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem336AdditiveD139

theorem sum_abs_row_eq {F : Type u_1} [Fintype F] (c : F → ℝ) (i : F)
    (hdiag : 0 ≤ c i) (hoff : ∀ j, j ≠ i → c j ≤ 0) :
    (∑ j : F, |c j|) = 2 * c i - ∑ j : F, c j := by
  classical
  have hsum := Finset.sum_erase_add Finset.univ c (Finset.mem_univ i)
  have habs := Finset.sum_erase_add Finset.univ (fun j => |c j|) (Finset.mem_univ i)
  have hrest : (∑ j ∈ Finset.univ.erase i, |c j|) =
      -(∑ j ∈ Finset.univ.erase i, c j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact abs_of_nonpos (hoff j (Finset.mem_erase.mp hj).1)
  rw [hrest, abs_of_nonneg hdiag] at habs
  linarith

theorem sum_abs_row_le_twice_diag {F : Type u_2} [Fintype F] (c : F → ℝ) (i : F)
    (hdiag : 0 ≤ c i) (hoff : ∀ j, j ≠ i → c j ≤ 0)
    (hrow : 0 ≤ ∑ j : F, c j) :
    (∑ j : F, |c j|) ≤ 2 * c i := by
  rw [sum_abs_row_eq c i hdiag hoff]
  linarith

theorem row_sum_nonneg_of_dummy {F : Type u_3} {D : Type u_4} [Fintype F] [Fintype D]
    (c : F → ℝ) (d : D → ℝ)
    (hzero : (∑ j : F, c j) + (∑ j : D, d j) = 0)
    (hdummy : ∀ j, d j ≤ 0) : 0 ≤ ∑ j : F, c j := by
  have hle : (∑ j : D, d j) ≤ 0 := Finset.sum_nonpos (fun j _ => hdummy j)
  linarith

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Problem336AdditiveD139

lemma boolReal_nonneg (b : Bool) : 0 ≤ boolReal b := by cases b <;> norm_num [boolReal]
lemma boolReal_le_one (b : Bool) : boolReal b ≤ 1 := by cases b <;> norm_num [boolReal]
lemma boolReal_mul_self (b : Bool) : boolReal b * boolReal b = boolReal b := by
  cases b <;> norm_num [boolReal]

lemma tiltMean_nonneg {F : Type u_1} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    0 ≤ tiltMean μ h i := by
  classical
  apply div_nonneg _ (tiltPartition_pos μ h).le
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
    (boolReal_nonneg _)

lemma tiltMean_le_one {F : Type u_2} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    tiltMean μ h i ≤ 1 := by
  classical
  unfold tiltMean
  apply (div_le_one (tiltPartition_pos μ h)).2
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_of_le_one_right
    (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) (boolReal_le_one _)

lemma tiltSecondMoment_self {F : Type u_3} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    tiltSecondMoment μ h i i = tiltMean μ h i := by
  classical
  simp only [tiltSecondMoment, tiltMean, mul_assoc, boolReal_mul_self]

lemma tiltCovariance_self {F : Type u_4} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    tiltCovariance μ h i i = tiltMean μ h i * (1 - tiltMean μ h i) := by
  rw [tiltCovariance, tiltSecondMoment_self]
  ring

lemma tiltCovariance_self_nonneg {F : Type u_5} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    0 ≤ tiltCovariance μ h i i := by
  rw [tiltCovariance_self]
  exact mul_nonneg (tiltMean_nonneg μ h i) (sub_nonneg.mpr (tiltMean_le_one μ h i))

lemma twice_tilt_variance_le_half {F : Type u_6} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    2 * tiltMean μ h i * (1 - tiltMean μ h i) ≤ (1 : ℝ) / 2 := by
  nlinarith [sq_nonneg (tiltMean μ h i - 1 / 2)]

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Problem336AdditiveD139

theorem finite_response_of_covariance_signs {F : Type u_1} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool))
    (hoff : ∀ (i j : F) (h : F → ℝ), i ≠ j → tiltCovariance μ h i j ≤ 0)
    (hrow : ∀ (i : F) (h : F → ℝ), 0 ≤ ∑ j : F, tiltCovariance μ h i j) :
    (∀ (i j : F) (h : F → ℝ),
      HasDerivAt (fun r : ℝ => tiltMean μ (coordinatePerturb h j r) i)
        (tiltCovariance μ h i j) 0) ∧
    (∀ (i : F) (h : F → ℝ),
      (∑ j : F, |tiltCovariance μ h i j|) ≤
        2 * tiltMean μ h i * (1 - tiltMean μ h i) ∧
      2 * tiltMean μ h i * (1 - tiltMean μ h i) ≤ (1 : ℝ) / 2) ∧
    (∀ (i : F) (h h' : F → ℝ) (D : ℝ), 0 ≤ D →
      (∀ j : F, |h j - h' j| ≤ D) →
      |tiltMean μ h i - tiltMean μ h' i| ≤ D / 2) := by
  have hbound (i : F) (h : F → ℝ) :
      (∑ j : F, |tiltCovariance μ h i j|) ≤
        2 * tiltMean μ h i * (1 - tiltMean μ h i) := by
    have hb := sum_abs_row_le_twice_diag (tiltCovariance μ h i) i
      (tiltCovariance_self_nonneg μ h i)
      (fun j hj => hoff i j h (Ne.symm hj)) (hrow i h)
    simpa only [tiltCovariance_self, mul_assoc] using hb
  refine ⟨fun i j h => tiltMean_hasDerivAt_coordinate μ h i j,
    fun i h => ⟨hbound i h, twice_tilt_variance_le_half μ h i⟩, ?_⟩
  intro i h h' D hD hdist
  have hb := finite_response_lipschitz_of_directional_deriv
    (fun h => tiltMean μ h i) (fun h => tiltCovariance μ h i) ((1 : ℝ) / 2)
    (fun h v t => tiltMean_hasDerivAt_affine μ h v i t)
    (fun h => (hbound i h).trans (twice_tilt_variance_le_half μ h i))
    h h' D hD hdist
  convert hb using 1
  ring

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336AdditiveD139

theorem StronglyRayleighFinite.tiltCovariance_row_nonneg
    {F : Type u_1} [Fintype F] {μ : ProbabilityMeasure (F → Bool)}
    (hμ : StronglyRayleighFinite μ) (h : F → ℝ) (i : F) :
    0 ≤ ∑ j : F, tiltCovariance μ h i j := by
  classical
  apply GeneratingSlice.covariance_row_nonneg_of_slice_bound μ h i
  exact stable_affine_wronskian_bound
    (GeneratingSlice.slice (GeneratingSlice.weight μ h) i false)
    (GeneratingSlice.slice (GeneratingSlice.weight μ h) i true)
    (GeneratingSlice.slice_coeff_nonneg _ (GeneratingSlice.weight_nonneg μ h) i false)
    (GeneratingSlice.slice_coeff_nonneg _ (GeneratingSlice.weight_nonneg μ h) i true)
    (GeneratingSlice.slice_stable μ hμ h i)

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

namespace Problem336AdditiveD139

lemma quadraticForm_eq_dotProduct {F : Type u_1} [Fintype F]
    (K : Matrix F F ℂ) (c : F → ℂ) :
    (∑ i : F, ∑ j : F, conj (c i) * K i j * c j) =
      star c ⬝ᵥ (K *ᵥ c) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma PositiveContractionFinite.isHermitian {F : Type u_2} [Fintype F]
    {K : Matrix F F ℂ} (hK : PositiveContractionFinite K) :
    Matrix.IsHermitian K :=
  Matrix.IsHermitian.ext fun i j => (hK.1 i j).symm

lemma PositiveContractionFinite.posSemidef {F : Type u_3} [Fintype F]
    {K : Matrix F F ℂ} (hK : PositiveContractionFinite K) :
    Matrix.PosSemidef K := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hK.isHermitian, fun c => ?_⟩
  rw [Complex.nonneg_iff]
  constructor
  · simpa only [quadraticForm_eq_dotProduct] using (hK.2 c).1
  · exact (hK.isHermitian.im_star_dotProduct_mulVec_self c).symm

lemma normSq_sum_eq_dotProduct_re {F : Type u_4} [Fintype F] (c : F → ℂ) :
    (∑ i : F, Complex.normSq (c i)) = (star c ⬝ᵥ c).re := by
  simp [dotProduct, Complex.mul_re, Complex.normSq_apply]

lemma PositiveContractionFinite.one_sub_posSemidef {F : Type u_5} [Fintype F]
    [DecidableEq F] {K : Matrix F F ℂ} (hK : PositiveContractionFinite K) :
    Matrix.PosSemidef ((1 : Matrix F F ℂ) - K) := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  have hHerm : Matrix.IsHermitian ((1 : Matrix F F ℂ) - K) := Matrix.isHermitian_one.sub hK.isHermitian
  refine ⟨hHerm, fun c => ?_⟩
  rw [Complex.nonneg_iff]
  constructor
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re]
    apply sub_nonneg.mpr
    simpa only [quadraticForm_eq_dotProduct, normSq_sum_eq_dotProduct_re] using (hK.2 c).2
  · exact (hHerm.im_star_dotProduct_mulVec_self c).symm

lemma positiveContractionFinite_iff_posSemidef {F : Type u_6} [Fintype F]
    [DecidableEq F] (K : Matrix F F ℂ) :
    PositiveContractionFinite K ↔
      Matrix.PosSemidef K ∧ Matrix.PosSemidef ((1 : Matrix F F ℂ) - K) := by
  constructor
  · intro hK
    exact ⟨hK.posSemidef, hK.one_sub_posSemidef⟩
  · rintro ⟨hK, hOne⟩
    refine ⟨fun i j => (hK.isHermitian.apply i j).symm, fun c => ?_⟩
    rw [quadraticForm_eq_dotProduct, normSq_sum_eq_dotProduct_re]
    refine ⟨hK.re_dotProduct_nonneg c, ?_⟩
    have h := hOne.re_dotProduct_nonneg c
    change 0 ≤ (star c ⬝ᵥ (((1 : Matrix F F ℂ) - K) *ᵥ c)).re at h
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re] at h
    exact sub_nonneg.mp h

lemma hermitian_pencil_ker_eq_zero {F : Type u_7} [Fintype F] [DecidableEq F]
    {K : Matrix F F ℂ} (hK : K.IsHermitian) (z : F → ℂ)
    (hz : ∀ i, 0 < (z i).im) (c : F → ℂ)
    (hc : ((1 - K + Matrix.diagonal z * K) : Matrix F F ℂ) *ᵥ c = 0) :
    c = 0 := by
  have hc' : c - K *ᵥ c + Matrix.diagonal z *ᵥ (K *ᵥ c) = 0 := by
    simpa only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec] using hc
  have hcoord (i : F) : c i = (1 - z i) * (K *ᵥ c) i := by
    have hi := congr_fun hc' i
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_diagonal,
      Pi.zero_apply] at hi
    linear_combination hi
  have him : (star c ⬝ᵥ (K *ᵥ c)).im = 0 :=
    hK.im_star_dotProduct_mulVec_self c
  have hsum : (∑ i : F, (z i).im * Complex.normSq ((K *ᵥ c) i)) = 0 := by
    convert him using 1
    simp only [dotProduct, Complex.im_sum, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoord i]
    simp [Complex.mul_im, Complex.mul_re, Complex.normSq_apply]
    ring
  have hy : K *ᵥ c = 0 := by
    funext i
    have hterm : (z i).im * Complex.normSq ((K *ᵥ c) i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (le_of_lt (hz j)) (Complex.normSq_nonneg _))).mp hsum
        i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hz i)))
  funext i
  simpa [hy] using hcoord i

lemma hermitian_pencil_det_ne_zero {F : Type u_8} [Fintype F] [DecidableEq F]
    {K : Matrix F F ℂ} (hK : K.IsHermitian) (z : F → ℂ)
    (hz : ∀ i, 0 < (z i).im) :
    Matrix.det (1 - K + Matrix.diagonal z * K) ≠ 0 := by
  have hu : IsUnit ((1 - K + Matrix.diagonal z * K) : Matrix F F ℂ) := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro a b hab
    have hzero : ((1 - K + Matrix.diagonal z * K) : Matrix F F ℂ) *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub, hab, sub_self]
    exact sub_eq_zero.mp (hermitian_pencil_ker_eq_zero hK z hz (a-b) hzero)
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mp hu).ne_zero

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped ComplexConjugate ComplexOrder Topology

namespace Problem336AdditiveD139

open Matrix

theorem det_fromBlocks_skew_nonneg_of_posDef
    {m : Type u_1} {n : Type u_2} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.PosDef) (hD : D.PosSemidef) :
    0 ≤ (Matrix.fromBlocks A B (-Bᴴ) D).det := by
  let := hA.isUnit.invertible
  rw [Matrix.det_fromBlocks₁₁]
  have hInv : (⅟ A : Matrix m m ℂ) = A⁻¹ := by
    exact Matrix.invOf_eq_nonsing_inv A
  rw [hInv, Matrix.neg_mul, Matrix.neg_mul, sub_neg_eq_add]
  exact mul_nonneg hA.posSemidef.det_nonneg
    (hD.add (hA.posSemidef.inv.conjTranspose_mul_mul_same B)).det_nonneg

theorem det_fromBlocks_skew_nonneg
    {m : Type u_3} {n : Type u_4} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    0 ≤ (Matrix.fromBlocks A B (-Bᴴ) D).det := by
  have hc : Continuous (fun t : ℝ =>
      (Matrix.fromBlocks (A + t • (1 : Matrix m m ℂ)) B (-Bᴴ) D).det) := by
    fun_prop
  have ht : Filter.Tendsto (fun t : ℝ =>
      (Matrix.fromBlocks (A + t • (1 : Matrix m m ℂ)) B (-Bᴴ) D).det)
      (𝓝[>] (0 : ℝ)) (𝓝 (Matrix.fromBlocks A B (-Bᴴ) D).det) := by
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply det_fromBlocks_skew_nonneg_of_posDef _ _ _ _ hD
  exact Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul ht)

def mixedRowMatrix {F : Type u_5} [DecidableEq F]
    (K : Matrix F F ℂ) (x : F → Bool) : Matrix F F ℂ :=
  fun i j => if x i = true then K i j else (1 - K) i j

theorem mixedRowMatrix_det_nonneg
    {F : Type u_6} [Fintype F] [DecidableEq F]
    (K : Matrix F F ℂ) (x : F → Bool)
    (hK : K.PosSemidef) (hIK : (1 - K).PosSemidef) :
    0 ≤ (mixedRowMatrix K x).det := by
  let e := Equiv.sumCompl (fun i : F => x i = true)
  let A := K.submatrix (fun i : {i // x i = true} => i.1) (fun i : {i // x i = true} => i.1)
  let B := K.submatrix (fun i : {i // x i = true} => i.1)
    (fun i : {i // ¬ x i = true} => i.1)
  let D := (1 - K).submatrix (fun i : {i // ¬ x i = true} => i.1) (fun i : {i // ¬ x i = true} => i.1)
  have he : (mixedRowMatrix K x).submatrix e e =
      Matrix.fromBlocks A B (-Bᴴ) D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [mixedRowMatrix, e, A, Matrix.submatrix, i.property]
    · simp [mixedRowMatrix, e, B, Matrix.submatrix, i.property]
    · simp [mixedRowMatrix, e, B, Matrix.submatrix, i.property,
        Matrix.one_apply, hK.isHermitian.apply]
    · simp [mixedRowMatrix, e, D, Matrix.submatrix, i.property, Matrix.one_apply, Subtype.ext_iff]
  rw [← Matrix.det_submatrix_equiv_self e (mixedRowMatrix K x), he]
  exact det_fromBlocks_skew_nonneg A B D (hK.submatrix _) (hIK.submatrix _)

theorem mixedRowMatrix_det_re_nonneg
    {F : Type u_7} [Fintype F] [DecidableEq F]
    (K : Matrix F F ℂ) (x : F → Bool)
    (hK : K.PosSemidef) (hIK : (1 - K).PosSemidef) :
    0 ≤ (mixedRowMatrix K x).det.re :=
  (Complex.nonneg_iff.mp (mixedRowMatrix_det_nonneg K x hK hIK)).1

theorem mixedRowMatrix_det_im
    {F : Type u_8} [Fintype F] [DecidableEq F]
    (K : Matrix F F ℂ) (x : F → Bool)
    (hK : K.PosSemidef) (hIK : (1 - K).PosSemidef) :
    (mixedRowMatrix K x).det.im = 0 :=
  (Complex.nonneg_iff.mp (mixedRowMatrix_det_nonneg K x hK hIK)).2.symm

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder Classical

namespace Problem336AdditiveD139

variable {F : Type u_1} [Fintype F]

def finiteDPPWeight (K : Matrix F F ℂ) (x : F → Bool) : ℂ := by
  classical
  exact Matrix.det (fun i j => if x i = true then K i j else (1 - K) i j)

theorem finiteDPPWeight_sum_inclusion (K : Matrix F F ℂ) (A : Finset F) :
    (∑ x : F → Bool, if (∀ i ∈ A, x i = true) then finiteDPPWeight K x else 0) =
      Matrix.det (fun i j : A => K i.1 j.1) := by
  classical
  let choices : F → Finset Bool := fun i => if i ∈ A then {true} else Finset.univ
  let rows : F → Bool → F → ℂ :=
    fun i b j => if b = true then K i j else (1 - K) i j
  have hchoices : Fintype.piFinset choices =
      Finset.univ.filter (fun x : F → Bool => ∀ i ∈ A, x i = true) := by
    ext x
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx i hi
      simpa [choices, hi] using hx i
    · intro hx i
      by_cases hi : i ∈ A
      · simp [choices, hi, hx i hi]
      · simp [choices, hi]
  have hrows : (fun i => ∑ b ∈ choices i, rows i b) =
      A.piecewise K (1 : Matrix F F ℂ) := by
    funext i j
    by_cases hi : i ∈ A
    · simp [choices, rows, hi, Finset.piecewise]
    · simp [choices, rows, hi, Finset.piecewise, Finset.sum_apply,
        Matrix.sub_apply]
  have hsum := Matrix.detRowAlternating.toMultilinearMap.map_sum_finset rows choices
  rw [hchoices, Finset.sum_filter] at hsum
  rw [hrows] at hsum
  change Matrix.det (A.piecewise K (1 : Matrix F F ℂ)) =
    (∑ x : F → Bool, if (∀ i ∈ A, x i = true) then finiteDPPWeight K x else 0) at hsum
  exact hsum.symm.trans (Matrix.det_piecewise_one_eq_submatrix_det K A)

theorem finiteDPPWeight_sum (K : Matrix F F ℂ) :
    (∑ x : F → Bool, finiteDPPWeight K x) = 1 := by
  classical
  calc
    _ = Matrix.det (fun i j : (∅ : Finset F) => K i.1 j.1) := by
      simpa only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
        ite_true] using finiteDPPWeight_sum_inclusion K ∅
    _ = 1 := Matrix.det_isEmpty

theorem finiteDPP_exists_of_weights_nonneg (K : Matrix F F ℂ)
    (hK : ∀ x : F → Bool, 0 ≤ finiteDPPWeight K x) :
    ∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K := by
  classical
  have hre (x : F → Bool) : 0 ≤ (finiteDPPWeight K x).re :=
    (Complex.nonneg_iff.mp (hK x)).1
  have hreal (x : F → Bool) : ((finiteDPPWeight K x).re : ℂ) = finiteDPPWeight K x := by
    apply Complex.ext
    · simp
    · simpa using (Complex.nonneg_iff.mp (hK x)).2
  have hsum : (∑ x : F → Bool, (finiteDPPWeight K x).re) = 1 := by
    simpa using congrArg Complex.re (finiteDPPWeight_sum K)
  have hmass : (∑ x : F → Bool, ENNReal.ofReal (finiteDPPWeight K x).re) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hre x), hsum]
    simp
  let p : PMF (F → Bool) := PMF.ofFintype
    (fun x => ENNReal.ofReal (finiteDPPWeight K x).re) hmass
  refine ⟨⟨p.toMeasure, inferInstance⟩, ?_⟩
  intro A
  change ((p.toMeasure {x | ∀ i ∈ A, x i = true}).toReal : ℂ) =
    Matrix.det (fun i j : A => K i.1 j.1)
  rw [PMF.toMeasure_apply_fintype]
  have hfinite (x : F → Bool) :
      ({x | ∀ i ∈ A, x i = true}.indicator (⇑p) x) ≠ ∞ := by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp [p]
  rw [ENNReal.toReal_sum (fun x _ => hfinite x)]
  push_cast
  calc
    (∑ x : F → Bool,
        (({x | ∀ i ∈ A, x i = true}.indicator (⇑p) x).toReal : ℂ)) =
        ∑ x : F → Bool, if (∀ i ∈ A, x i = true) then finiteDPPWeight K x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, p, PMF.ofFintype_apply]
      split_ifs <;> simp [ENNReal.toReal_ofReal (hre x), hreal x]
    _ = Matrix.det (fun i j : A => K i.1 j.1) := finiteDPPWeight_sum_inclusion K A

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped ComplexOrder

namespace Problem336AdditiveD139

theorem PositiveContractionFinite.exists_finiteDPP {F : Type u_1} [Fintype F]
    {K : F → F → ℂ} (hK : PositiveContractionFinite K) :
    ∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K := by
  classical
  apply finiteDPP_exists_of_weights_nonneg K
  intro x
  exact mixedRowMatrix_det_nonneg K x hK.posSemidef hK.one_sub_posSemidef

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace Problem336AdditiveD139

theorem det_one_add_eq_sum_principal_minors {F : Type u_1} [Fintype F] [DecidableEq F]
    (K : Matrix F F ℂ) :
    Matrix.det (1 + K) = ∑ A : Finset F,
      Matrix.det (fun i j : A => K i.1 j.1) := by
  let D := (Matrix.detRowAlternating : (F → ℂ) [⋀^F]→ₗ[ℂ] ℂ)
  rw [add_comm]
  change D ((fun i => K i) + (fun i => (1 : Matrix F F ℂ) i)) = _
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro A hA
  exact Matrix.det_piecewise_one_eq_submatrix_det K A

theorem det_one_add_weighted_eq_sum_principal_minors {F : Type u_2} [Fintype F] [DecidableEq F]
    (K : Matrix F F ℂ) (w : F → ℂ) :
    Matrix.det ((1 : Matrix F F ℂ) + Matrix.of (fun i j => w i * K i j)) = ∑ A : Finset F,
      (∏ i ∈ A, w i) * Matrix.det (fun i j : A => K i.1 j.1) := by
  rw [det_one_add_eq_sum_principal_minors]
  apply Finset.sum_congr rfl
  intro A hA
  change Matrix.det (Matrix.of (fun i j : A => w i.1 * K i.1 j.1)) = _
  simpa only [Finset.prod_coe_sort] using
    Matrix.det_mul_column (fun i : A => w i.1) (fun i j : A => K i.1 j.1)

theorem binary_monomial_expansion {F : Type u_3} [Fintype F] [DecidableEq F]
    (x : F → Bool) (z : F → ℂ) :
    (∏ i : F, if x i = true then z i else 1) =
      ∑ A : Finset F, if ∀ i ∈ A, x i = true then ∏ i ∈ A, (z i - 1) else 0 := by
  calc
    _ = ∏ i : F, ((if x i = true then z i - 1 else 0) + 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs <;> simp
    _ = ∑ A : Finset F, ∏ i ∈ A, (if x i = true then z i - 1 else 0) := by
      simpa using Fintype.prod_add (fun i => if x i = true then z i - 1 else 0)
        (fun _ => (1 : ℂ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A hA
      by_cases hx : ∀ i ∈ A, x i = true
      · simp only [ite_eq_left hx]
        apply Finset.prod_congr rfl
        intro i hi
        exact ite_eq_left (hx i hi)
      · rw [ite_eq_right hx]
        push Not at hx
        obtain ⟨i, hi, hxi⟩ := hx
        exact Finset.prod_eq_zero hi (ite_eq_right hxi)

theorem sum_atom_mass_on {F : Type u_4} [Fintype F] [DecidableEq F]
    (μ : ProbabilityMeasure (F → Bool)) (P : (F → Bool) → Prop) [DecidablePred P] :
    (∑ x : F → Bool, if P x then ((μ : Measure (F → Bool)) {x}).toReal else 0) =
      ((μ : Measure (F → Bool)) {x | P x}).toReal := by
  simpa [Measure.real, Finset.sum_filter] using
    (sum_measureReal_singleton (μ := (μ : Measure (F → Bool)))
      (Finset.univ.filter P))

theorem finiteGeneratingValue_eq_inclusion_sum {F : Type u_5} [Fintype F] [DecidableEq F]
    (μ : ProbabilityMeasure (F → Bool)) (z : F → ℂ) :
    finiteGeneratingValue μ z = ∑ A : Finset F,
      (((μ : Measure (F → Bool)) {x | ∀ i ∈ A, x i = true}).toReal : ℂ) *
        ∏ i ∈ A, (z i - 1) := by
  unfold finiteGeneratingValue
  simp_rw [binary_monomial_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  calc
    _ = (∑ x : F → Bool, if ∀ i ∈ A, x i = true then
          (((μ : Measure (F → Bool)) {x}).toReal : ℂ) else 0) *
            ∏ i ∈ A, (z i - 1) := by
      rw [Finset.sum_mul]
      simp only [mul_ite, mul_zero, ite_mul, zero_mul]
      congr!
    _ = _ := by
      congr 1
      simpa only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using congrArg (fun r : ℝ => (r : ℂ))
        (sum_atom_mass_on μ (fun x => ∀ i ∈ A, x i = true))

theorem finiteGeneratingValue_eq_det {F : Type u_6} [Fintype F] [DecidableEq F]
    (μ : ProbabilityMeasure (F → Bool)) (K : F → F → ℂ)
    (hμ : IsFiniteDeterminantalLaw μ K) (z : F → ℂ) :
    finiteGeneratingValue μ z =
      Matrix.det ((1 : Matrix F F ℂ) + Matrix.of (fun i j => (z i - 1) * K i j)) := by
  rw [finiteGeneratingValue_eq_inclusion_sum]
  refine Eq.trans ?_
    (det_one_add_weighted_eq_sum_principal_minors (Matrix.of K) (fun i => z i - 1)).symm
  apply Finset.sum_congr rfl
  intro A hA
  rw [hμ A, mul_comm]
  congr

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate

namespace Problem336AdditiveD139

theorem IsFiniteDeterminantalLaw.stronglyRayleighFinite_of_isHermitian
    {F : Type u_1} [Fintype F] {μ : ProbabilityMeasure (F → Bool)}
    {K : F → F → ℂ} (hμ : IsFiniteDeterminantalLaw μ K)
    (hK : (Matrix.of K).IsHermitian) : StronglyRayleighFinite μ := by
  classical
  intro z hz
  rw [finiteGeneratingValue_eq_det μ K hμ z]
  have heq : ((1 : Matrix F F ℂ) + Matrix.of (fun i j => (z i - 1) * K i j)) =
      1 - Matrix.of K + Matrix.diagonal z * Matrix.of K := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.diagonal_mul]
    ring
  rw [heq]
  exact hermitian_pencil_det_ne_zero hK z hz

theorem IsFiniteDeterminantalLaw.stronglyRayleighFinite
    {F : Type u_2} [Fintype F] {μ : ProbabilityMeasure (F → Bool)}
    {K : F → F → ℂ} (hμ : IsFiniteDeterminantalLaw μ K)
    (hK : PositiveContractionFinite K) : StronglyRayleighFinite μ := by
  exact hμ.stronglyRayleighFinite_of_isHermitian hK.isHermitian

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336AdditiveD139

theorem binary_cylinder_isClosed {I : Type u_1} {s : Set (I → Bool)}
    (hs : s ∈ measurableCylinders (fun _ : I => Bool)) : IsClosed s := by
  obtain ⟨S, t, ht, rfl⟩ := (mem_measurableCylinders s).mp hs
  exact (isClosed_discrete t).preimage S.continuous_restrict

theorem binary_cylinders_eventually_empty {I : Type u_2} {s : ℕ → Set (I → Bool)}
    (hs : ∀ n, s n ∈ measurableCylinders (fun _ : I => Bool))
    (hanti : Antitone s) (hempty : (⋂ n, s n) = ∅) :
    ∃ n, s n = ∅ := by
  by_contra h
  push Not at h
  have hn : ∀ n, (s n).Nonempty := h
  have hc : ∀ n, IsClosed (s n) := fun n => binary_cylinder_isClosed (hs n)
  have hi := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed s
    (fun n => hanti (Nat.le_succ n)) hn (hc 0).isCompact hc
  rw [hempty] at hi
  exact Set.not_nonempty_empty hi

theorem binary_projective_exists {I : Type u_3}
    (P : (S : Finset I) → Measure (S → Bool))
    [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => Bool) P) :
    ∃ μ : ProbabilityMeasure (I → Bool),
      IsProjectiveLimit (α := fun _ : I => Bool) (μ : Measure (I → Bool)) P := by
  let m := projectiveFamilyContent hP
  have htend : ∀ {s : ℕ → Set (I → Bool)},
      (∀ n, s n ∈ measurableCylinders (fun _ : I => Bool)) →
      Antitone s → (⋂ n, s n) = ∅ →
      Tendsto (fun n => m (s n)) atTop (𝓝 0) := by
    intro s hs hanti hempty
    obtain ⟨N, hN⟩ := binary_cylinders_eventually_empty hs hanti hempty
    have heq : (fun n => m (s n)) =ᶠ[atTop] fun _ => 0 := by
      refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have hsub := hanti hn
      rw [hN] at hsub
      have hz : s n = ∅ := Set.eq_empty_of_subset_empty hsub
      simp [hz, m]
    exact tendsto_const_nhds.congr' heq.symm
  have hsig : m.IsSigmaSubadditive := by
    refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
      isSetRing_measurableCylinders (fun f hf hfU hdisj => ?_)
    exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders m
      (fun _ _ => projectiveFamilyContent_ne_top hP) @htend hf hfU hdisj
  let μ := m.measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge hsig
  have hlim : IsProjectiveLimit (α := fun _ : I => Bool) μ P := by
    intro S
    ext t ht
    rw [Measure.map_apply (Finset.measurable_restrict S) ht]
    change μ (cylinder S t) = P S t
    dsimp [μ]
    rw [AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _
      (cylinder_mem_measurableCylinders _ _ ht)]
    exact projectiveFamilyContent_cylinder hP ht
  have : IsProbabilityMeasure μ := hlim.isProbabilityMeasure
  exact ⟨⟨μ, inferInstance⟩, hlim⟩

theorem binary_projective_exists_unique {I : Type u_4}
    (P : (S : Finset I) → Measure (S → Bool))
    [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => Bool) P) :
    ∃! μ : ProbabilityMeasure (I → Bool),
      IsProjectiveLimit (α := fun _ : I => Bool) (μ : Measure (I → Bool)) P := by
  obtain ⟨μ, hμ⟩ := binary_projective_exists P hP
  exact ⟨μ, hμ, fun ν hν => Subtype.ext (hν.unique hμ)⟩

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Set MeasurableSpace

namespace Problem336AdditiveD139

def inclusionEvent {I : Type u_1} (A : Finset I) : Set (I → Bool) :=
  {x | ∀ i ∈ A, x i = true}

@[simp] theorem inclusionEvent_empty {I : Type u_2} :
    inclusionEvent (∅ : Finset I) = Set.univ := by
  ext x
  simp [inclusionEvent]

@[simp] theorem inclusionEvent_singleton {I : Type u_3} (i : I) :
    inclusionEvent ({i} : Finset I) = {x : I → Bool | x i = true} := by
  ext x
  simp [inclusionEvent]

@[simp] theorem inclusionEvent_union {I : Type u_4} [DecidableEq I] (A B : Finset I) :
    inclusionEvent (A ∪ B) = inclusionEvent A ∩ inclusionEvent B := by
  classical
  ext x
  simp [inclusionEvent, or_imp, forall_and]

theorem measurableSet_inclusionEvent {I : Type u_5} (A : Finset I) :
    MeasurableSet (inclusionEvent A) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    have h : inclusionEvent (insert i A) =
        {x : I → Bool | x i = true} ∩ inclusionEvent A := by
      ext x
      simp [inclusionEvent]
    rw [h]
    exact (measurable_pi_apply i (measurableSet_singleton true)).inter ih

theorem isPiSystem_inclusionEvents {I : Type u_6} :
    IsPiSystem (Set.range (@inclusionEvent I)) := by
  classical
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩ _
  exact ⟨A ∪ B, inclusionEvent_union A B⟩

theorem generateFrom_inclusionEvents {I : Type u_7} :
    MeasurableSpace.generateFrom (Set.range (@inclusionEvent I)) =
      (inferInstance : MeasurableSpace (I → Bool)) := by
  classical
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le (by
      rintro _ ⟨A, rfl⟩
      exact measurableSet_inclusionEvent A)
  · change MeasurableSpace.pi ≤ _
    rw [MeasurableSpace.pi]
    refine iSup_le fun i => ?_
    rw [← measurable_iff_comap_le]
    apply measurable_to_bool
    have h : (fun x : I → Bool => x i) ⁻¹' {true} = inclusionEvent {i} := by
      ext x
      simp [inclusionEvent]
    rw [h]
    exact MeasurableSpace.measurableSet_generateFrom ⟨{i}, rfl⟩

theorem probabilityMeasure_eq_of_inclusion_probabilities {I : Type u_8}
    (μ ν : ProbabilityMeasure (I → Bool))
    (h : ∀ A : Finset I,
      (μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true} =
      (ν : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true}) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_generateFrom_of_iUnion
    (Set.range (@inclusionEvent I)) (fun _ : ℕ => Set.univ)
    generateFrom_inclusionEvents.symm isPiSystem_inclusionEvents
  · ext x
    constructor
    · intro _
      trivial
    · intro _
      exact Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩
  · intro n
    exact ⟨∅, inclusionEvent_empty⟩
  · intro n
    exact measure_ne_top _ _
  · rintro _ ⟨A, rfl⟩
    exact h A

theorem probabilityMeasure_eq_of_inclusion_probabilities_toReal {I : Type u_9}
    (μ ν : ProbabilityMeasure (I → Bool))
    (h : ∀ A : Finset I,
      ((μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true}).toReal =
      ((ν : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true}).toReal) : μ = ν := by
  apply probabilityMeasure_eq_of_inclusion_probabilities μ ν
  intro A
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (h A)

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate
namespace Problem336AdditiveD139

def binaryPullbackLaw {A : Type u_1} {B : Type u_2} (μ : ProbabilityMeasure (B → Bool)) (e : A → B) :
    ProbabilityMeasure (A → Bool) :=
  μ.map (f := fun x i => x (e i)) (Measurable.of_eval fun i => measurable_pi_apply (e i)).aemeasurable

lemma binaryPullbackLaw_toMeasure {A : Type u_3} {B : Type u_4}
    (μ : ProbabilityMeasure (B → Bool)) (e : A → B) :
    (binaryPullbackLaw μ e : Measure (A → Bool)) =
      Measure.map (fun x i => x (e i)) (μ : Measure (B → Bool)) := rfl

lemma inclusionDeterminant_map {A : Type u_5} {B : Type u_6} [DecidableEq A] [DecidableEq B] (K : B → B → ℂ)
    (e : A ↪ B) (S : Finset A) :
    Matrix.det (fun i j : S.map e => K i.1 j.1) =
      Matrix.det (fun i j : S => K (e i.1) (e j.1)) := by
  classical
  let f : S ≃ S.map e := Equiv.ofBijective
    (fun i => ⟨e i.1, Finset.mem_map.mpr ⟨i.1, i.2, rfl⟩⟩)
    (by
      constructor
      · intro i j h
        exact Subtype.ext (e.injective (congrArg Subtype.val h))
      · intro j
        obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp j.2
        exact ⟨⟨i, hi⟩, Subtype.ext hij⟩)
  exact (Matrix.det_submatrix_equiv_self f (fun i j : S.map e => K i.1 j.1)).symm

lemma isDeterminantalLaw_binaryPullback {A : Type u_7} {B : Type u_8}
    (μ : ProbabilityMeasure (B → Bool)) (K : B → B → ℂ)
    (hμ : IsDeterminantalLaw μ K) (e : A ↪ B) :
    IsDeterminantalLaw (binaryPullbackLaw μ e) (fun i j => K (e i) (e j)) := by
  classical
  intro S
  rw [binaryPullbackLaw_toMeasure, Measure.map_apply
    (Measurable.of_eval fun i => measurable_pi_apply (e i))
    (measurableSet_inclusionEvent S)]
  have hevent : (fun (x : B → Bool) i => x (e i)) ⁻¹'
      {x : A → Bool | ∀ i ∈ S, x i = true} =
      {x : B → Bool | ∀ j ∈ S.map e, x j = true} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Finset.forall_mem_map]
  rw [hevent, hμ (S.map e), inclusionDeterminant_map]

lemma isFiniteDeterminantalLaw_binaryPullback {A : Type u_9} {B : Type u_10}
    [Fintype A] [Fintype B] (μ : ProbabilityMeasure (B → Bool)) (K : B → B → ℂ)
    (hμ : IsFiniteDeterminantalLaw μ K) (e : A ↪ B) :
    IsFiniteDeterminantalLaw (binaryPullbackLaw μ e) (fun i j => K (e i) (e j)) :=
  isDeterminantalLaw_binaryPullback μ K hμ e

lemma finiteDppFamily_projective {I : Type u_11} (K : I → I → ℂ)
    (P : ∀ S : Finset I, ProbabilityMeasure (S → Bool))
    (hP : ∀ S, IsFiniteDeterminantalLaw (P S) (fun i j : S => K i.1 j.1))
    (hunique : ∀ (S : Finset I) (ν : ProbabilityMeasure (S → Bool)),
      IsFiniteDeterminantalLaw ν (fun i j : S => K i.1 j.1) → ν = P S) :
    IsProjectiveMeasureFamily (α := fun _ : I => Bool) (fun S => (P S : Measure (S → Bool))) := by
  classical
  intro S T hTS
  let e : T ↪ S := ⟨fun i => ⟨i.1, hTS i.2⟩,
    fun a b h => Subtype.ext (congrArg (fun x : S => (x : I)) h)⟩
  have hd : IsFiniteDeterminantalLaw (binaryPullbackLaw (P S) e)
      (fun i j : T => K i.1 j.1) :=
    isFiniteDeterminantalLaw_binaryPullback (P S) (fun i j : S => K i.1 j.1) (hP S) e
  have heq := hunique T (binaryPullbackLaw (P S) e) hd
  exact congrArg (fun ν : ProbabilityMeasure (T → Bool) => (ν : Measure (T → Bool)))
    heq.symm

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory

namespace Problem336AdditiveD139

theorem IsDeterminantalLaw.eq {I : Type u_1}
    {μ ν : ProbabilityMeasure (I → Bool)} {K : I → I → ℂ}
    (hμ : IsDeterminantalLaw μ K) (hν : IsDeterminantalLaw ν K) : μ = ν := by
  apply probabilityMeasure_eq_of_inclusion_probabilities_toReal μ ν
  intro A
  simpa using congrArg Complex.re ((hμ A).trans (hν A).symm)

theorem IsFiniteDeterminantalLaw.eq {F : Type u_2} [Fintype F]
    {μ ν : ProbabilityMeasure (F → Bool)} {K : F → F → ℂ}
    (hμ : IsFiniteDeterminantalLaw μ K) (hν : IsFiniteDeterminantalLaw ν K) : μ = ν :=
  IsDeterminantalLaw.eq hμ hν

theorem existsUnique_determinantalLaw_of_exists {I : Type u_3} (K : I → I → ℂ)
    (h : ∃ μ : ProbabilityMeasure (I → Bool), IsDeterminantalLaw μ K) :
    ∃! μ : ProbabilityMeasure (I → Bool), IsDeterminantalLaw μ K := by
  obtain ⟨μ, hμ⟩ := h
  exact ⟨μ, hμ, fun ν hν => hν.eq hμ⟩

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate


namespace Problem336AdditiveD139

lemma isFiniteDeterminantalLaw_of_isEmpty {F : Type u_1} [Fintype F] [IsEmpty F]
    (μ : ProbabilityMeasure (F → Bool)) (K : F → F → ℂ) :
    IsFiniteDeterminantalLaw μ K := by
  classical
  intro A
  have hA : A = ∅ := Finset.eq_empty_of_isEmpty A
  subst A
  refine Eq.trans ?_
    (Matrix.det_isEmpty (A := Matrix.of (fun i j : (∅ : Finset F) => K i.1 j.1))).symm
  simp

lemma finite_dpp_exists_including_empty
    (finite_exists : ∀ (F : Type u) [Fintype F] [Nonempty F] (K : F → F → ℂ),
      PositiveContractionFinite K →
        ∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K)
    (F : Type u) [Fintype F] (K : F → F → ℂ) (hK : PositiveContractionFinite K) :
    ∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K := by
  cases isEmpty_or_nonempty F with
  | inl h =>
    let μ : ProbabilityMeasure (F → Bool) :=
      ⟨Measure.dirac (fun _ => false), inferInstance⟩
    exact ⟨μ, isFiniteDeterminantalLaw_of_isEmpty μ K⟩
  | inr h => exact finite_exists F K hK

lemma det_finset_univ {F : Type u} [Fintype F] (K : F → F → ℂ) :
    (by
      classical
      exact Matrix.det (fun i j : (Finset.univ : Finset F) => K i.1 j.1) =
        Matrix.det K) := by
  classical
  let e : (Finset.univ : Finset F) ≃ F :=
    { toFun := fun i => i.1
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := fun i => Subtype.ext rfl
      right_inv := fun i => rfl }
  exact Matrix.det_submatrix_equiv_self e K

lemma isDeterminantalLaw_of_projectiveLimit {I : Type u}
    (K : I → I → ℂ) (P : ∀ S : Finset I, ProbabilityMeasure (S → Bool))
    (hP : ∀ S : Finset I,
      IsFiniteDeterminantalLaw (P S) (fun i j : S => K i.1 j.1))
    (μ : ProbabilityMeasure (I → Bool))
    (hμ : IsProjectiveLimit (μ : Measure (I → Bool))
      (fun S => (P S : Measure (S → Bool)))) :
    IsDeterminantalLaw μ K := by
  classical
  intro A
  have hm : (μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true} =
      (P A : Measure (A → Bool)) {x | ∀ i : A, x i = true} := by
    have hμA : Measure.map A.restrict (μ : Measure (I → Bool)) =
        (P A : Measure (A → Bool)) := hμ A
    rw [← hμA, Measure.map_apply]
    · congr 1
      ext x
      simp [Finset.restrict]
    · exact Measurable.of_eval (fun i => measurable_pi_apply i.1)
    · exact (Set.toFinite _).measurableSet
  rw [hm]
  have h := hP A Finset.univ
  simp only [Finset.mem_univ, forall_true_left] at h
  rw [h]
  refine (det_finset_univ (fun i j : A => K i.1 j.1)).trans ?_
  exact congrArg (fun d : DecidableEq A =>
    @Matrix.det A d _ ℂ _ (fun i j : A => K i.1 j.1)) (Subsingleton.elim _ _)

lemma positiveContractionKernel_existsUnique_of_finite_exists
    (finite_exists : ∀ (F : Type u) [Fintype F] [Nonempty F] (K : F → F → ℂ),
      PositiveContractionFinite K →
        ∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K)
    (I : Type u) (K : I → I → ℂ) (hK : PositiveContractionKernel K) :
    ∃! μ : ProbabilityMeasure (I → Bool), IsDeterminantalLaw μ K := by
  classical
  have hex : ∀ S : Finset I, ∃ μ : ProbabilityMeasure (S → Bool),
      IsFiniteDeterminantalLaw μ (fun i j : S => K i.1 j.1) := by
    intro S
    apply finite_dpp_exists_including_empty finite_exists S
    exact ⟨fun i j => hK.1 i.1 j.1, hK.2 S⟩
  choose P hP using hex
  have hproj := finiteDppFamily_projective K P hP
    (fun S ν hν => hν.eq (hP S))
  obtain ⟨μ, hμ⟩ := binary_projective_exists
    (fun S => (P S : Measure (S → Bool))) hproj
  exact existsUnique_determinantalLaw_of_exists K
    ⟨μ, isDeterminantalLaw_of_projectiveLimit K P hP μ hμ⟩

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate
namespace Problem336AdditiveD139

def finiteMarginal {I : Type u_1} (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) :
    ProbabilityMeasure (S → Bool) :=
  μ.map (f := fun a i => a i.1) (Measurable.of_eval (fun i => measurable_pi_apply i.1)).aemeasurable

lemma finiteMarginal_apply_singleton {I : Type u_2} (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (x : S → Bool) :
    ((finiteMarginal μ S : Measure (S → Bool)) {x}).toReal = marginalMass μ S x := by
  classical
  unfold finiteMarginal marginalMass
  rw [ProbabilityMeasure.map_apply' _
    (Measurable.of_eval (fun i => measurable_pi_apply i.1)).aemeasurable
    (measurableSet_singleton x)]
  congr 2
  ext a
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  exact funext_iff

lemma finiteGeneratingValue_finiteMarginal {I : Type u_3}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (z : S → ℂ) :
    finiteGeneratingValue (finiteMarginal μ S) z = marginalGeneratingValue μ S z := by
  classical
  unfold finiteGeneratingValue marginalGeneratingValue
  simp_rw [finiteMarginal_apply_singleton]
  exact Finset.sum_congr (by ext; simp) (by intros; rfl)

lemma positiveContractionFinite_restrict {I : Type u_4} (K : I → I → ℂ)
    (hK : PositiveContractionKernel K) (S : Finset I) :
    PositiveContractionFinite (fun i j : S => K i.1 j.1) := by
  exact ⟨fun i j => hK.1 i.1 j.1, hK.2 S⟩

lemma marginalGeneratingValue_empty {I : Type u_5} (μ : ProbabilityMeasure (I → Bool))
    (z : (∅ : Finset I) → ℂ) : marginalGeneratingValue μ ∅ z = 1 := by
  classical
  simp [marginalGeneratingValue, marginalMass]

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate
namespace Problem336AdditiveD139

lemma finiteMarginal_isDeterminantal {I : Type u_1} {K : I → I → ℂ}
    {μ : ProbabilityMeasure (I → Bool)} (hμ : IsDeterminantalLaw μ K)
    (S : Finset I) :
    IsFiniteDeterminantalLaw (finiteMarginal μ S) (fun i j : S => K i.1 j.1) := by
  classical
  intro A
  let emb : S ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  let T : Finset I := A.map emb
  let e : A ≃ T := Equiv.ofBijective
    (fun i => ⟨i.1.1, Finset.mem_map_of_mem emb i.2⟩)
    (by
      constructor
      · intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : T => (x : I)) hab
      · rintro ⟨i, hi⟩
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact ⟨⟨j, hj⟩, rfl⟩)
  have hs : MeasurableSet {x : S → Bool | ∀ i ∈ A, x i = true} :=
    (Set.toFinite _).measurableSet
  rw [finiteMarginal, ProbabilityMeasure.map_apply' _
    (Measurable.of_eval (fun i => measurable_pi_apply i.1)).aemeasurable hs]
  have hevent : (fun x : I → Bool => fun i : S => x i.1) ⁻¹'
      {x : S → Bool | ∀ i ∈ A, x i = true} =
      {x : I → Bool | ∀ i ∈ T, x i = true} := by
    ext x
    simp [T, emb]
  rw [hevent, hμ T]
  convert (Matrix.det_submatrix_equiv_self e (fun i j : T => K i.1 j.1)).symm using 1
  congr 1

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate
namespace Problem336AdditiveD139

lemma stronglyRayleighCountable_of_finiteMarginal {I : Type u_1}
    (μ : ProbabilityMeasure (I → Bool))
    (h : ∀ S : Finset I, S.Nonempty → StronglyRayleighFinite (finiteMarginal μ S)) :
    StronglyRayleighCountable μ := by
  classical
  intro S z hz
  by_cases hS : S.Nonempty
  · rw [← finiteGeneratingValue_finiteMarginal]
    exact h S hS z hz
  · have hS' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rw [marginalGeneratingValue_empty]
    exact one_ne_zero

lemma stronglyRayleighCountable_iff_finiteMarginal {I : Type u_2}
    (μ : ProbabilityMeasure (I → Bool)) :
    StronglyRayleighCountable μ ↔
      ∀ S : Finset I, StronglyRayleighFinite (finiteMarginal μ S) := by
  constructor
  · intro h S z hz
    rw [finiteGeneratingValue_finiteMarginal]
    exact h S z hz
  · intro h
    exact stronglyRayleighCountable_of_finiteMarginal μ (fun S _ => h S)

lemma isDeterminantalLaw_stronglyRayleighCountable_of_finite
    {I : Type u} (K : I → I → ℂ) (μ : ProbabilityMeasure (I → Bool))
    (hfinite : ∀ (F : Type u) [Fintype F] [Nonempty F] (L : F → F → ℂ),
      PositiveContractionFinite L → ∀ ν : ProbabilityMeasure (F → Bool),
        IsFiniteDeterminantalLaw ν L → StronglyRayleighFinite ν)
    (hK : PositiveContractionKernel K) (hμ : IsDeterminantalLaw μ K) :
    StronglyRayleighCountable μ := by
  apply stronglyRayleighCountable_of_finiteMarginal μ
  intro S hS
  let : Nonempty S := hS.to_subtype
  exact hfinite S (fun i j : S => K i.1 j.1)
    (positiveContractionFinite_restrict K hK S) (finiteMarginal μ S)
    (finiteMarginal_isDeterminantal hμ S)

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate
namespace Problem336AdditiveD139

lemma measurable_leftTranslate {Γ : Type u_1} {α : Type u_2} [Group Γ] [MeasurableSpace α]
    (g : Γ) : Measurable (leftTranslate g : (Γ → α) → (Γ → α)) :=
  Measurable.of_eval (fun h => measurable_pi_apply (g⁻¹ * h))

def translatedLaw {Γ : Type u_3} [Group Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (g : Γ) : ProbabilityMeasure (Γ → Bool) :=
  μ.map (measurable_leftTranslate g).aemeasurable

@[simp] lemma translatedLaw_toMeasure {Γ : Type u_4} [Group Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (g : Γ) :
    (translatedLaw μ g : Measure (Γ → Bool)) =
      Measure.map (leftTranslate g) (μ : Measure (Γ → Bool)) := rfl

lemma measurableSet_inclusion {I : Type u_5} (A : Finset I) :
    MeasurableSet {x : I → Bool | ∀ i ∈ A, x i = true} := by
  classical
  have heq : {x : I → Bool | ∀ i ∈ A, x i = true} =
      ⋂ i : A, {x : I → Bool | x i.1 = true} := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    measurableSet_eq_fun (measurable_pi_apply i.1) measurable_const

lemma translatedLaw_isDeterminantal {Γ : Type u_6} [Group Γ]
    {μ : ProbabilityMeasure (Γ → Bool)} {K : Γ → Γ → ℂ}
    (hμ : IsDeterminantalLaw μ K) (hK : TranslationInvariantKernel K) (g : Γ) :
    IsDeterminantalLaw (translatedLaw μ g) K := by
  classical
  intro A
  let e : Γ ≃ Γ := Equiv.mulLeft g⁻¹
  let B : Finset Γ := A.map e.toEmbedding
  let eA : A ≃ B := Equiv.subtypeEquiv e (by
    intro a
    simp [B])
  have hpre : leftTranslate g ⁻¹' {x : Γ → Bool | ∀ i ∈ A, x i = true} =
      {x : Γ → Bool | ∀ i ∈ B, x i = true} := by
    ext x
    change (∀ i ∈ A, x (g⁻¹ * i) = true) ↔ ∀ i ∈ A.map e.toEmbedding, x i = true
    rw [Finset.forall_mem_map]
    rfl
  rw [translatedLaw_toMeasure, Measure.map_apply (measurable_leftTranslate g)
    (measurableSet_inclusion A), hpre, hμ B]
  have hmatrix : Matrix.submatrix (fun i j : B => K i.1 j.1) eA eA =
      (fun i j : A => K i.1 j.1) := by
    funext i j
    change K (g⁻¹ * i.1) (g⁻¹ * j.1) = K i.1 j.1
    exact hK g⁻¹ i.1 j.1
  rw [← Matrix.det_submatrix_equiv_self eA (fun i j : B => K i.1 j.1), hmatrix]

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory

namespace Problem336AdditiveD139

theorem IsDeterminantalLaw.invariantBinaryLaw
    {Γ : Type u_1} [Group Γ] {K : Γ → Γ → ℂ}
    {μ : ProbabilityMeasure (Γ → Bool)}
    (hμ : IsDeterminantalLaw μ K) (hK : TranslationInvariantKernel K) :
    InvariantBinaryLaw μ := by
  intro g
  have heq : translatedLaw μ g = μ :=
    (translatedLaw_isDeterminantal hμ hK g).eq hμ
  exact congrArg ProbabilityMeasure.toMeasure heq

theorem translationInvariantKernel_factor_of_exists
    {Γ : Type u_2} [Group Γ] [MeasurableSpace Γ] (K : Γ → Γ → ℂ)
    (hK : TranslationInvariantKernel K)
    (hexists : ∃ μ : ProbabilityMeasure (Γ → Bool), IsDeterminantalLaw μ K)
    (hfactor : ∀ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K → InvariantBinaryLaw μ → HasEquivariantIIDFactor μ) :
    ∃ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K ∧ InvariantBinaryLaw μ ∧ HasEquivariantIIDFactor μ := by
  obtain ⟨μ, hμ⟩ := hexists
  have hinv := hμ.invariantBinaryLaw hK
  exact ⟨μ, hμ, hinv, hfactor μ hμ hinv⟩

theorem invariantBinaryLaw_of_unique_determinantal
    {Γ : Type u_3} [Group Γ] {K : Γ → Γ → ℂ}
    (μ : ProbabilityMeasure (Γ → Bool))
    (hunique : ∀ ν : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw ν K → ν = μ)
    (htranslate : ∀ g : Γ, ∃ ν : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw ν K ∧
        Measure.map (leftTranslate g) (μ : Measure (Γ → Bool)) =
          (ν : Measure (Γ → Bool))) :
    InvariantBinaryLaw μ := by
  intro g
  obtain ⟨ν, hν, hmap⟩ := htranslate g
  simpa only [hunique ν hν] using hmap

theorem determinantal_factor_of_existsUnique_of_translate
    {Γ : Type u_4} [Group Γ] [MeasurableSpace Γ] (K : Γ → Γ → ℂ)
    (hexists : ∃! μ : ProbabilityMeasure (Γ → Bool), IsDeterminantalLaw μ K)
    (htranslate : ∀ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K → ∀ g : Γ,
      ∃ ν : ProbabilityMeasure (Γ → Bool), IsDeterminantalLaw ν K ∧
        Measure.map (leftTranslate g) (μ : Measure (Γ → Bool)) =
          (ν : Measure (Γ → Bool)))
    (hfactor : ∀ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K → InvariantBinaryLaw μ → HasEquivariantIIDFactor μ) :
    ∃ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K ∧ InvariantBinaryLaw μ ∧ HasEquivariantIIDFactor μ := by
  obtain ⟨μ, hμ, hunique⟩ := hexists
  have hinv : InvariantBinaryLaw μ :=
    invariantBinaryLaw_of_unique_determinantal μ hunique (htranslate μ hμ)
  exact ⟨μ, hμ, hinv, hfactor μ hμ hinv⟩

theorem translationInvariantKernel_factor_of_existsUnique
    {Γ : Type u_5} [Group Γ] [MeasurableSpace Γ] (K : Γ → Γ → ℂ)
    (hK : TranslationInvariantKernel K)
    (hexists : ∃! μ : ProbabilityMeasure (Γ → Bool), IsDeterminantalLaw μ K)
    (hfactor : ∀ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K → InvariantBinaryLaw μ → HasEquivariantIIDFactor μ) :
    ∃ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K ∧ InvariantBinaryLaw μ ∧ HasEquivariantIIDFactor μ := by
  apply determinantal_factor_of_existsUnique_of_translate K hexists ?_ hfactor
  intro μ hμ g
  exact ⟨translatedLaw μ g, translatedLaw_isDeterminantal hμ hK g, rfl⟩

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem336AdditiveD139

def finiteFieldWeight {I : Type u_1} (S : Finset I) (h : I → ℝ)
    (x : I → Bool) : ℝ :=
  Real.exp (∑ j ∈ S, h j * boolReal (x j))

def finiteFieldMean {I : Type u_2} (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (h : I → ℝ) (i : I) : ℝ :=
  (∫ x, boolReal (x i) * finiteFieldWeight S h x ∂(μ : Measure (I → Bool))) /
    (∫ x, finiteFieldWeight S h x ∂(μ : Measure (I → Bool)))

private theorem measurable_boolReal : Measurable boolReal := by
  exact measurable_of_countable _

theorem measurable_finiteFieldWeight {I : Type u_3} (S : Finset I) (h : I → ℝ) :
    Measurable (finiteFieldWeight S h) := by
  unfold finiteFieldWeight
  apply Measurable.exp
  exact Finset.measurable_sum S (fun j _ => measurable_const.mul
    (measurable_boolReal.comp (measurable_pi_apply j)))

theorem measurable_finiteFieldWeight_joint {I : Type u_4} (S : Finset I) :
    Measurable (fun p : (I → ℝ) × (I → Bool) => finiteFieldWeight S p.1 p.2) := by
  unfold finiteFieldWeight
  apply Measurable.exp
  exact Finset.measurable_sum S (fun j _ =>
    ((measurable_pi_apply j).comp measurable_fst).mul
      (measurable_boolReal.comp ((measurable_pi_apply j).comp measurable_snd)))

theorem finiteFieldWeight_pos {I : Type u_5} (S : Finset I) (h : I → ℝ)
    (x : I → Bool) : 0 < finiteFieldWeight S h x := Real.exp_pos _

theorem integrable_finiteFieldWeight {I : Type u_6}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) :
    Integrable (finiteFieldWeight S h) (μ : Measure (I → Bool)) := by
  apply (integrable_const (Real.exp (∑ j ∈ S, |h j|))).mono'
    (measurable_finiteFieldWeight S h).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (finiteFieldWeight_pos S h x)]
  apply Real.exp_le_exp.mpr
  apply Finset.sum_le_sum
  intro j _
  cases x j <;> simp [boolReal, le_abs_self]

theorem finiteFieldWeight_integral_pos {I : Type u_7}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) :
    0 < ∫ x, finiteFieldWeight S h x ∂(μ : Measure (I → Bool)) := by
  apply (integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (finiteFieldWeight_pos S h x).le)
    (integrable_finiteFieldWeight μ S h)).mpr
  have hs : Function.support (finiteFieldWeight S h) = Set.univ := by
    ext x
    simp [Function.mem_support, ne_of_gt (finiteFieldWeight_pos S h x)]
  rw [hs]
  simp

private theorem finiteField_boolReal_bounds (b : Bool) :
    0 ≤ boolReal b ∧ boolReal b ≤ 1 := by
  cases b <;> simp [boolReal]

theorem integrable_finiteFieldMean_numerator {I : Type u_8}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) (i : I) :
    Integrable (fun x => boolReal (x i) * finiteFieldWeight S h x)
      (μ : Measure (I → Bool)) := by
  apply (integrable_finiteFieldWeight μ S h).mono'
    (((measurable_boolReal.comp (measurable_pi_apply i)).mul
      (measurable_finiteFieldWeight S h)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  have hb := finiteField_boolReal_bounds (x i)
  have hw := (finiteFieldWeight_pos S h x).le
  change ‖boolReal (x i) * finiteFieldWeight S h x‖ ≤ finiteFieldWeight S h x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 hw)]
  exact mul_le_of_le_one_left hw hb.2

theorem finiteFieldMean_mem_unitInterval {I : Type u_9}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) (i : I) :
    finiteFieldMean μ S h i ∈ Set.Icc (0 : ℝ) 1 := by
  have hden := finiteFieldWeight_integral_pos μ S h
  have hnum : 0 ≤ ∫ x, boolReal (x i) * finiteFieldWeight S h x
      ∂(μ : Measure (I → Bool)) :=
    integral_nonneg fun x => mul_nonneg (finiteField_boolReal_bounds (x i)).1
      (finiteFieldWeight_pos S h x).le
  constructor
  · exact div_nonneg hnum hden.le
  · apply (div_le_one hden).mpr
    apply integral_mono (integrable_finiteFieldMean_numerator μ S h i)
      (integrable_finiteFieldWeight μ S h)
    intro x
    exact mul_le_of_le_one_left (finiteFieldWeight_pos S h x).le
      (finiteField_boolReal_bounds (x i)).2

theorem measurable_finiteFieldMean {I : Type u_10}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (i : I) :
    Measurable (fun h : I → ℝ => finiteFieldMean μ S h i) := by
  have hw := measurable_finiteFieldWeight_joint S
  have hn : Measurable (fun p : (I → ℝ) × (I → Bool) =>
      boolReal (p.2 i) * finiteFieldWeight S p.1 p.2) :=
    (measurable_boolReal.comp ((measurable_pi_apply i).comp measurable_snd)).mul hw
  exact hn.stronglyMeasurable.integral_prod_right.measurable.div
    hw.stronglyMeasurable.integral_prod_right.measurable

theorem finiteFieldWeight_translate {Γ : Type u_11} [Group Γ] [DecidableEq Γ]
    (g : Γ) (S : Finset Γ) (h : Γ → ℝ) (x : Γ → Bool) :
    finiteFieldWeight (S.image (fun j => g * j)) (leftTranslate g h)
      (leftTranslate g x) = finiteFieldWeight S h x := by
  classical
  unfold finiteFieldWeight
  congr 1
  rw [Finset.sum_image]
  · simp only [leftTranslate, inv_mul_cancel_left]
  · intro a _ b _ hab
    exact mul_left_cancel hab

theorem integral_leftTranslate_of_invariant {Γ : Type u_12} [Group Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (hμ : InvariantBinaryLaw μ)
    (g : Γ) (f : (Γ → Bool) → ℝ) (hf : Measurable f) :
    (∫ x, f (leftTranslate g x) ∂(μ : Measure (Γ → Bool))) =
      ∫ x, f x ∂(μ : Measure (Γ → Bool)) := by
  have hg : Measurable (leftTranslate g : (Γ → Bool) → (Γ → Bool)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (g⁻¹ * i))
  rw [← integral_map hg.aemeasurable hf.aestronglyMeasurable, hμ g]

theorem finiteFieldMean_translate {Γ : Type u_13} [Group Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (hμ : InvariantBinaryLaw μ)
    (g i : Γ) (S : Finset Γ) (h : Γ → ℝ) :
    finiteFieldMean μ (S.image (fun j => g * j)) (leftTranslate g h) (g * i) =
      finiteFieldMean μ S h i := by
  classical
  unfold finiteFieldMean
  congr 1
  · let f : (Γ → Bool) → ℝ := fun x =>
      boolReal (x (g * i)) * finiteFieldWeight (S.image (fun j => g * j))
        (leftTranslate g h) x
    have hf : Measurable f :=
      (measurable_boolReal.comp (measurable_pi_apply (g * i))).mul
        (measurable_finiteFieldWeight _ _)
    have heq := integral_leftTranslate_of_invariant μ hμ g f hf
    simpa only [f, leftTranslate, inv_mul_cancel_left,
      finiteFieldWeight_translate] using heq.symm
  · have heq := integral_leftTranslate_of_invariant μ hμ g
      (finiteFieldWeight (S.image (fun j => g * j)) (leftTranslate g h))
      (measurable_finiteFieldWeight _ _)
    simpa only [finiteFieldWeight_translate] using heq.symm

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336AdditiveD139

lemma finite_field_sum_restrict {I : Type u_1} [DecidableEq I]
    (S J : Finset I) (hSJ : S ⊆ J) (h : I → ℝ) (x : I → Bool) :
    (∑ j : J, (if j.1 ∈ S then h j.1 else 0) * boolReal (x j.1)) =
      ∑ j ∈ S, h j * boolReal (x j) := by
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_subtype J (fun _ => Iff.rfl)
    (fun j => if j ∈ S then h j * boolReal (x j) else 0), Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hSJ]

lemma integral_finiteMarginal {I : Type u_2} (μ : ProbabilityMeasure (I → Bool))
    (J : Finset I) (f : (J → Bool) → ℝ) :
    (∫ x, f x ∂(finiteMarginal μ J : Measure (J → Bool))) =
      ∫ x, f (fun j : J => x j.1) ∂(μ : Measure (I → Bool)) := by
  rw [finiteMarginal, ProbabilityMeasure.toMeasure_map]
  apply integral_map
  · exact (Measurable.of_eval (fun j => measurable_pi_apply j.1)).aemeasurable
  · exact (measurable_of_countable f).aestronglyMeasurable

theorem finiteFieldMean_eq_tiltMean_finiteMarginal {I : Type u_3} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (S J : Finset I) (hSJ : S ⊆ J)
    (h : I → ℝ) (i : J) :
    finiteFieldMean μ S h i.1 =
      tiltMean (finiteMarginal μ J) (fun j : J => if j.1 ∈ S then h j.1 else 0) i := by
  classical
  let h' : J → ℝ := fun j => if j.1 ∈ S then h j.1 else 0
  let w : (J → Bool) → ℝ := fun x => Real.exp (∑ j : J, h' j * boolReal (x j))
  have hw (x : I → Bool) : w (fun j : J => x j.1) = finiteFieldWeight S h x := by
    unfold w finiteFieldWeight h'
    rw [finite_field_sum_restrict S J hSJ]
  have hden : (∫ x, finiteFieldWeight S h x ∂(μ : Measure (I → Bool))) =
      tiltPartition (finiteMarginal μ J) h' := by
    rw [← show (fun x => w (fun j : J => x j.1)) = finiteFieldWeight S h from funext hw,
      ← integral_finiteMarginal μ J w, integral_fintype Integrable.of_finite]
    unfold tiltPartition
    apply Finset.sum_congr (by ext; simp)
    intro x _
    simp only [smul_eq_mul, w, Measure.real]
    ring
  have hnum : (∫ x, boolReal (x i.1) * finiteFieldWeight S h x
      ∂(μ : Measure (I → Bool))) =
      ∑ x : J → Bool, w x * ((finiteMarginal μ J : Measure (J → Bool)) {x}).toReal *
        boolReal (x i) := by
    have heq : (fun x : I → Bool => boolReal (x i.1) * finiteFieldWeight S h x) =
        fun x => (fun z : J → Bool => boolReal (z i) * w z) (fun j : J => x j.1) := by
      funext x
      change boolReal (x i.1) * finiteFieldWeight S h x =
        boolReal (x i.1) * w (fun j : J => x j.1)
      rw [hw]
    rw [heq, ← integral_finiteMarginal μ J (fun z => boolReal (z i) * w z),
      integral_fintype Integrable.of_finite]
    apply Finset.sum_congr (by ext; simp)
    intro x _
    simp only [smul_eq_mul, Measure.real]
    ring
  unfold finiteFieldMean tiltMean
  rw [hnum, hden]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro x _
  rfl

def finiteObservationField {I : Type u_4} [DecidableEq I]
    (i : I) (S : Finset I) (t : ℝ) (y : I → ℝ) : {j // j ∈ insert i S} → ℝ :=
  fun j => if j.1 ∈ S then y j.1 - t / 2 else 0

def finiteObservationDrift {I : Type u_5} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I)
    (t : ℝ) (y : I → ℝ) : ℝ :=
  tiltMean (finiteMarginal μ (insert i S)) (finiteObservationField i S t y)
    ⟨i, Finset.mem_insert_self i S⟩

theorem finiteObservationDrift_eq_finiteFieldMean {I : Type u_6} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I)
    (t : ℝ) (y : I → ℝ) :
    finiteObservationDrift μ i S t y =
      finiteFieldMean μ S (fun j => y j - t / 2) i := by
  exact (finiteFieldMean_eq_tiltMean_finiteMarginal μ S (insert i S)
    (Finset.subset_insert i S) (fun j => y j - t / 2)
    ⟨i, Finset.mem_insert_self i S⟩).symm

theorem finiteObservationDrift_mem_Icc {I : Type u_7} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I)
    (t : ℝ) (y : I → ℝ) : finiteObservationDrift μ i S t y ∈ Set.Icc (0 : ℝ) 1 := by
  rw [finiteObservationDrift_eq_finiteFieldMean]
  exact finiteFieldMean_mem_unitInterval μ S _ i

theorem measurable_finiteObservationDrift {I : Type u_8} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I) :
    Measurable (fun p : ℝ × (I → ℝ) => finiteObservationDrift μ i S p.1 p.2) := by
  simp_rw [finiteObservationDrift_eq_finiteFieldMean]
  apply (measurable_finiteFieldMean μ S i).comp
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply j).comp measurable_snd).sub (measurable_fst.div_const 2)

theorem finiteObservationDrift_translate {Γ : Type u_9} [Group Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (hμ : InvariantBinaryLaw μ)
    (g i : Γ) (S : Finset Γ) (t : ℝ) (y : Γ → ℝ) :
    finiteObservationDrift μ (g * i) (S.image (fun j => g * j)) t (leftTranslate g y) =
      finiteObservationDrift μ i S t y := by
  simp_rw [finiteObservationDrift_eq_finiteFieldMean]
  exact finiteFieldMean_translate μ hμ g i S (fun j => y j - t / 2)

theorem finiteObservationField_abs_sub_le {I : Type u_10} [DecidableEq I]
    (i : I) (S : Finset I) (t : ℝ) (y y' : I → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hy : ∀ j : I, |y j - y' j| ≤ D) :
    ∀ j : {j // j ∈ insert i S},
      |finiteObservationField i S t y j - finiteObservationField i S t y' j| ≤ D := by
  intro j
  by_cases hj : j.1 ∈ S
  · simpa only [finiteObservationField, hj, ite_true, sub_sub_sub_cancel_right] using hy j.1
  · simpa only [finiteObservationField, hj, ite_false, sub_self, abs_zero] using hD

theorem finiteObservationDrift_response_of_finite_response
    {I : Type u_11} [DecidableEq I] (μ : ProbabilityMeasure (I → Bool))
    (i : I) (S : Finset I)
    (hresponse : ∀ (h h' : {j // j ∈ insert i S} → ℝ) (D : ℝ), 0 ≤ D →
      (∀ j : {j // j ∈ insert i S}, |h j - h' j| ≤ D) →
      |tiltMean (finiteMarginal μ (insert i S)) h ⟨i, Finset.mem_insert_self i S⟩ -
       tiltMean (finiteMarginal μ (insert i S)) h' ⟨i, Finset.mem_insert_self i S⟩| ≤ D / 2)
    (t : ℝ) (y y' : I → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hy : ∀ j : I, |y j - y' j| ≤ D) :
    |finiteObservationDrift μ i S t y - finiteObservationDrift μ i S t y'| ≤ D / 2 := by
  exact hresponse _ _ D hD (finiteObservationField_abs_sub_le i S t y y' D hD hy)

theorem finiteObservationDrift_eq_tiltMean_of_mem {I : Type u_12} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I) (hi : i ∈ S)
    (t : ℝ) (y : I → ℝ) :
    finiteObservationDrift μ i S t y =
      tiltMean (finiteMarginal μ S) (fun j : S => y j.1 - t / 2) ⟨i, hi⟩ := by
  rw [finiteObservationDrift_eq_finiteFieldMean,
    finiteFieldMean_eq_tiltMean_finiteMarginal μ S S (Finset.Subset.refl S)
      (fun j => y j - t / 2) ⟨i, hi⟩]
  congr 1
  funext j
  exact ite_eq_left j.property

@[simp] theorem finiteFieldMean_zero_field {I : Type u_13}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (i : I) :
    finiteFieldMean μ S (fun _ => 0) i =
      ∫ x, boolReal (x i) ∂(μ : Measure (I → Bool)) := by
  simp [finiteFieldMean, finiteFieldWeight]

@[simp] theorem finiteObservationDrift_zero_zero {I : Type u_14} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I) :
    finiteObservationDrift μ i S 0 (fun _ => 0) =
      ∫ x, boolReal (x i) ∂(μ : Measure (I → Bool)) := by
  simp [finiteObservationDrift_eq_finiteFieldMean]

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem336AdditiveD139

variable (Γ : Type u_1) [Group Γ] [Countable Γ]

def groupEnumeration : ℕ → Γ :=
  Classical.choose (exists_surjective_nat Γ)

theorem groupEnumeration_surjective : Function.Surjective (groupEnumeration Γ) :=
  Classical.choose_spec (exists_surjective_nat Γ)

def groupBaseExhaustion (n : ℕ) : Finset Γ := by
  classical
  exact insert 1 ((Finset.range n).image (groupEnumeration Γ))

@[simp] theorem one_mem_groupBaseExhaustion (n : ℕ) :
    (1 : Γ) ∈ groupBaseExhaustion Γ n := by
  classical
  simp [groupBaseExhaustion]

theorem groupBaseExhaustion_monotone : Monotone (groupBaseExhaustion Γ) := by
  classical
  intro n m hnm
  exact Finset.insert_subset_insert 1 (Finset.image_subset_image (Finset.range_mono hnm))

theorem mem_groupBaseExhaustion_eventually (g : Γ) :
    ∃ N : ℕ, ∀ n, N ≤ n → g ∈ groupBaseExhaustion Γ n := by
  classical
  obtain ⟨k, hk⟩ := groupEnumeration_surjective Γ g
  refine ⟨k + 1, fun n hn => ?_⟩
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), hk⟩

def translatedGroupExhaustion (h : Γ) (n : ℕ) : Finset Γ := by
  classical
  exact (groupBaseExhaustion Γ n).image (fun k => h * k)

@[simp] theorem self_mem_translatedGroupExhaustion (h : Γ) (n : ℕ) :
    h ∈ translatedGroupExhaustion Γ h n := by
  classical
  exact Finset.mem_image.mpr ⟨1, one_mem_groupBaseExhaustion Γ n, mul_one h⟩

theorem translatedGroupExhaustion_monotone (h : Γ) :
    Monotone (translatedGroupExhaustion Γ h) := by
  classical
  intro n m hnm
  exact Finset.image_subset_image (groupBaseExhaustion_monotone Γ hnm)

theorem mem_translatedGroupExhaustion_eventually (h g : Γ) :
    ∃ N : ℕ, ∀ n, N ≤ n → g ∈ translatedGroupExhaustion Γ h n := by
  classical
  obtain ⟨N, hN⟩ := mem_groupBaseExhaustion_eventually Γ (h⁻¹ * g)
  refine ⟨N, fun n hn => ?_⟩
  exact Finset.mem_image.mpr ⟨h⁻¹ * g, hN n hn, by simp⟩

theorem subset_translatedGroupExhaustion_eventually (h : Γ) (A : Finset Γ) :
    ∃ N : ℕ, ∀ n, N ≤ n → A ⊆ translatedGroupExhaustion Γ h n := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      exact ⟨0, fun _ _ => Finset.empty_subset _⟩
  | @insert g A hg ih =>
      obtain ⟨N, hN⟩ := mem_translatedGroupExhaustion_eventually Γ h g
      obtain ⟨M, hM⟩ := ih
      refine ⟨max N M, fun n hn => ?_⟩
      exact Finset.insert_subset_iff.mpr
        ⟨hN n (le_trans (le_max_left _ _) hn),
         hM n (le_trans (le_max_right _ _) hn)⟩

theorem translatedGroupExhaustion_equivariant [DecidableEq Γ] (g h : Γ) (n : ℕ) :
    translatedGroupExhaustion Γ (g * h) n =
      (translatedGroupExhaustion Γ h n).image (fun k => g * k) := by
  classical
  ext k
  simp only [translatedGroupExhaustion, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨h * a, ⟨a, ha, rfl⟩, (mul_assoc g h a).symm⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, mul_assoc g h a⟩

theorem iUnion_translatedGroupExhaustion (h : Γ) :
    (⋃ n : ℕ, (translatedGroupExhaustion Γ h n : Set Γ)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨N, hN⟩ := mem_translatedGroupExhaustion_eventually Γ h g
  exact Set.mem_iUnion.mpr ⟨N, hN N le_rfl⟩

def groupExhaustionLimsup {Y : Type u_2} (b : Γ → Finset Γ → Y → ℝ)
    (h : Γ) (y : Y) : ℝ :=
  Filter.limsup (fun n : ℕ => b h (translatedGroupExhaustion Γ h n) y) Filter.atTop

theorem groupExhaustionLimsup_equivariant {Y : Type u_3} [DecidableEq Γ]
    (τ : Γ → Y → Y) (b : Γ → Finset Γ → Y → ℝ)
    (hb : ∀ (g h : Γ) (S : Finset Γ) (y : Y),
      b (g * h) (S.image (fun k => g * k)) (τ g y) = b h S y)
    (g h : Γ) (y : Y) :
    groupExhaustionLimsup Γ b (g * h) (τ g y) =
      groupExhaustionLimsup Γ b h y := by
  apply Filter.limsup_congr
  exact Filter.Eventually.of_forall fun n => by
    rw [translatedGroupExhaustion_equivariant]
    exact hb g h _ y

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Problem336AdditiveD139

private theorem limsup_le_limsup_add_of_unit_bounds
    {a b : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ n, b n ∈ Set.Icc (0 : ℝ) 1)
    (hab : ∀ n, a n ≤ b n + C) :
    limsup a atTop ≤ limsup b atTop + C := by
  have haCob : IsCoboundedUnder (· ≤ ·) atTop a :=
    isCoboundedUnder_le_of_le atTop (fun n => (ha n).1)
  have hbBound : IsBoundedUnder (· ≤ ·) atTop b :=
    isBoundedUnder_of ⟨1, fun n => (hb n).2⟩
  have hbCob : IsCoboundedUnder (· ≤ ·) atTop b :=
    isCoboundedUnder_le_of_le atTop (fun n => (hb n).1)
  have hshift : IsBoundedUnder (· ≤ ·) atTop (fun n => b n + C) :=
    isBoundedUnder_of ⟨1 + C, fun n => by linarith [(hb n).2]⟩
  have h := limsup_le_limsup (Eventually.of_forall hab) haCob hshift
  rwa [limsup_add_const atTop b C hbBound hbCob] at h

theorem abs_limsup_sub_limsup_le_of_unit_bounds
    {a b : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ n, b n ∈ Set.Icc (0 : ℝ) 1)
    (hab : ∀ n, |a n - b n| ≤ C) :
    |limsup a atTop - limsup b atTop| ≤ C := by
  have hab' : limsup a atTop ≤ limsup b atTop + C :=
    limsup_le_limsup_add_of_unit_bounds ha hb (fun n => by
      have h := (abs_le.mp (hab n)).2
      linarith)
  have hba' : limsup b atTop ≤ limsup a atTop + C :=
    limsup_le_limsup_add_of_unit_bounds hb ha (fun n => by
      have h := (abs_le.mp (hab n)).1
      linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def limsupDrift {Ω : Type u_1} {I : Type u_2} (b : ℕ → Ω → I → ℝ) (w : Ω) (i : I) : ℝ :=
  limsup (fun n => b n w i) atTop

theorem limsupDrift_mem_unitInterval {Ω : Type u_3} {I : Type u_4}
    {b : ℕ → Ω → I → ℝ}
    (hb : ∀ n w i, b n w i ∈ Set.Icc (0 : ℝ) 1) (w : Ω) (i : I) :
    limsupDrift b w i ∈ Set.Icc (0 : ℝ) 1 := by
  have hBound : IsBoundedUnder (· ≤ ·) atTop (fun n => b n w i) :=
    isBoundedUnder_of ⟨1, fun n => (hb n w i).2⟩
  have hCob : IsCoboundedUnder (· ≤ ·) atTop (fun n => b n w i) :=
    isCoboundedUnder_le_of_le atTop (fun n => (hb n w i).1)
  constructor
  · apply le_limsup_of_le hBound
    intro c hc
    obtain ⟨n, hn⟩ := hc.exists
    exact (hb n w i).1.trans hn
  · exact limsup_le_of_le hCob (Eventually.of_forall (fun n => (hb n w i).2))

theorem measurable_limsupDrift {Ω : Type u_5} {I : Type u_6} [MeasurableSpace Ω]
    {b : ℕ → Ω → I → ℝ} (hb : ∀ n, Measurable (b n)) :
    Measurable (limsupDrift b) := by
  apply Measurable.of_eval
  intro i
  exact Measurable.limsup (fun n => (measurable_pi_apply i).comp (hb n))

theorem limsupDrift_abs_sub_le {Ω : Type u_7} {I : Type u_8} {b : ℕ → Ω → I → ℝ}
    (hb : ∀ n w i, b n w i ∈ Set.Icc (0 : ℝ) 1)
    {w w' : Ω} {C : ℝ} (h : ∀ n i, |b n w i - b n w' i| ≤ C) (i : I) :
    |limsupDrift b w i - limsupDrift b w' i| ≤ C :=
  abs_limsup_sub_limsup_le_of_unit_bounds
    (fun n => hb n w i) (fun n => hb n w' i) (fun n => h n i)

theorem limsupDrift_reindex {Ω : Type u_9} {I : Type u_10} {b : ℕ → Ω → I → ℝ}
    (A : Ω → Ω) (e : I → I)
    (hb : ∀ n w i, b n (A w) i = b n w (e i)) (w : Ω) (i : I) :
    limsupDrift b (A w) i = limsupDrift b w (e i) := by
  unfold limsupDrift
  congr 1
  funext n
  exact hb n w i

theorem limsupDrift_leftTranslate {Γ : Type u_11} [Group Γ]
    {b : ℕ → (Γ → ℝ) → Γ → ℝ}
    (hb : ∀ n (g : Γ) y, b n (leftTranslate g y) = leftTranslate g (b n y))
    (g : Γ) (y : Γ → ℝ) :
    limsupDrift b (leftTranslate g y) = leftTranslate g (limsupDrift b y) := by
  funext i
  exact limsupDrift_reindex (leftTranslate g) (fun i => g⁻¹ * i)
    (fun n w i => congrFun (hb n g w) i) y i

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Problem336AdditiveD139


def groupDrift {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (t : ℝ) (y : Γ → ℝ) (i : Γ) : ℝ :=
  limsup (fun n : ℕ =>
    finiteObservationDrift μ i (translatedGroupExhaustion Γ i n) t y) atTop

theorem groupDrift_eq_finiteFieldMean_limsup
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (t : ℝ) (y : Γ → ℝ) (i : Γ) :
    groupDrift μ t y i = limsup (fun n : ℕ =>
      finiteFieldMean μ (translatedGroupExhaustion Γ i n) (fun j => y j - t / 2) i) atTop := by
  simp only [groupDrift, finiteObservationDrift_eq_finiteFieldMean]

theorem measurable_groupDrift
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) :
    Measurable (fun p : ℝ × (Γ → ℝ) => groupDrift μ p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  exact Measurable.limsup (fun n =>
    measurable_finiteObservationDrift μ i (translatedGroupExhaustion Γ i n))

theorem groupDrift_mem_Icc
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (t : ℝ) (y : Γ → ℝ) (i : Γ) :
    groupDrift μ t y i ∈ Set.Icc (0 : ℝ) 1 := by
  exact limsupDrift_mem_unitInterval (b := fun n (p : ℝ × (Γ → ℝ)) i =>
    finiteObservationDrift μ i (translatedGroupExhaustion Γ i n) p.1 p.2)
    (fun n p i => finiteObservationDrift_mem_Icc μ i _ p.1 p.2) (t, y) i

theorem groupDrift_response_of_finite_response
    (hresponse : ∀ (F : Type u) [Fintype F] [Nonempty F]
      (ν : ProbabilityMeasure (F → Bool)), StronglyRayleighFinite ν →
      ∀ (i : F) (h h' : F → ℝ) (D : ℝ), 0 ≤ D →
        (∀ j, |h j - h' j| ≤ D) → |tiltMean ν h i - tiltMean ν h' i| ≤ D / 2)
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (hμ : StronglyRayleighCountable μ)
    (t : ℝ) (y y' : Γ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hy : ∀ j, |y j - y' j| ≤ D) (i : Γ) :
    |groupDrift μ t y i - groupDrift μ t y' i| ≤ D / 2 := by
  apply abs_limsup_sub_limsup_le_of_unit_bounds
    (fun n => finiteObservationDrift_mem_Icc μ i _ t y)
    (fun n => finiteObservationDrift_mem_Icc μ i _ t y')
  intro n
  let S := translatedGroupExhaustion Γ i n
  let : Nonempty (insert i S : Finset Γ) := ⟨⟨i, Finset.mem_insert_self i S⟩⟩
  have hSR : StronglyRayleighFinite (finiteMarginal μ (insert i S)) := by
    intro z hz
    rw [finiteGeneratingValue_finiteMarginal]
    exact hμ (insert i S) z hz
  exact finiteObservationDrift_response_of_finite_response μ i S
    (hresponse ↥(insert i S : Finset Γ) (finiteMarginal μ (insert i S)) hSR
      ⟨i, Finset.mem_insert_self i S⟩) t y y' D hD hy

theorem groupDrift_translate
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (hμ : InvariantBinaryLaw μ)
    (g i : Γ) (t : ℝ) (y : Γ → ℝ) :
    groupDrift μ t (leftTranslate g y) (g * i) = groupDrift μ t y i := by
  unfold groupDrift
  apply limsup_congr
  apply Eventually.of_forall
  intro n
  rw [translatedGroupExhaustion_equivariant]
  exact finiteObservationDrift_translate μ hμ g i _ t y

theorem groupDrift_leftTranslate
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (hμ : InvariantBinaryLaw μ)
    (g : Γ) (t : ℝ) (y : Γ → ℝ) :
    groupDrift μ t (leftTranslate g y) = leftTranslate g (groupDrift μ t y) := by
  funext i
  simpa only [leftTranslate, mul_inv_cancel_left] using
    groupDrift_translate μ hμ g (g⁻¹ * i) t y

@[simp] theorem groupDrift_zero_zero
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (i : Γ) :
    groupDrift μ 0 (fun _ => 0) i =
      ∫ x, boolReal (x i) ∂(μ : Measure (Γ → Bool)) := by
  simp [groupDrift]

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped NNReal Topology

namespace Problem336AdditiveD139.PathRealization

abbrev Path := C(ℝ≥0, ℝ)

local instance : MeasurableSpace Path := borel Path
local instance : BorelSpace Path := ⟨rfl⟩

theorem measurableEmbedding_denseEval (d : ℕ → ℝ≥0) (hd : DenseRange d) :
    MeasurableEmbedding (fun f : Path => fun n : ℕ => f (d n)) := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval (fun n => (continuous_eval_const (d n)).measurable)
  · intro f g h
    apply ContinuousMap.coe_injective
    exact hd.equalizer f.continuous g.continuous h

theorem measurable_path_iff {Ω : Type u_1} [MeasurableSpace Ω] {X : Ω → Path} :
    Measurable X ↔ ∀ t : ℝ≥0, Measurable (fun ω => X ω t) := by
  constructor
  · intro h t
    exact (continuous_eval_const t).measurable.comp h
  · intro h
    obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
    apply (measurableEmbedding_denseEval d hd).measurable_comp_iff.mp
    exact Measurable.of_eval (fun n => h (d n))

theorem measurable_bundle {Ω : Type u_2} [MeasurableSpace Ω]
    (X : Ω → ℝ≥0 → ℝ) (hc : ∀ ω, Continuous (X ω))
    (hm : ∀ t, Measurable (fun ω => X ω t)) :
    Measurable (fun ω => (⟨X ω, hc ω⟩ : Path)) := by
  exact measurable_path_iff.mpr hm

theorem measurable_bundle_family {Ω : Type u_3} {I : Type u_4} [MeasurableSpace Ω]
    (X : Ω → I → ℝ≥0 → ℝ) (hc : ∀ ω i, Continuous (X ω i))
    (hm : ∀ i t, Measurable (fun ω => X ω i t)) :
    Measurable (fun ω i => (⟨X ω i, hc ω i⟩ : Path)) := by
  exact Measurable.of_eval (fun i => measurable_bundle (fun ω => X ω i)
    (fun ω => hc ω i) (hm i))

theorem measurable_joint_eval {Ω : Type u_5} [MeasurableSpace Ω]
    {X : Ω → Path} (hm : Measurable X) :
    Measurable (fun p : Ω × ℝ≥0 => X p.1 p.2) := by
  exact continuous_eval.measurable.comp ((hm.comp measurable_fst).prodMk measurable_snd)

theorem measurable_joint_family_eval {Ω : Type u_6} {I : Type u_7} [MeasurableSpace Ω]
    {X : Ω → I → Path} (hm : Measurable X) :
    Measurable (fun p : Ω × ℝ≥0 => fun i => X p.1 i p.2) := by
  exact Measurable.of_eval (fun i =>
    measurable_joint_eval ((measurable_pi_apply i).comp hm))

def observationPath (x : ℝ) (B : Path) : Path :=
  ⟨fun t => (t : ℝ) * x + B t, by fun_prop⟩

theorem measurable_observationPath :
    Measurable (fun p : ℝ × Path => observationPath p.1 p.2) := by
  apply measurable_path_iff.mpr
  intro t
  exact (measurable_const.mul measurable_fst).add
    ((continuous_eval_const t).measurable.comp measurable_snd)

theorem measurable_observationFamily {I : Type u_8} :
    Measurable (fun p : (I → ℝ) × (I → Path) =>
      fun i => observationPath (p.1 i) (p.2 i)) := by
  refine Measurable.of_eval (fun i => ?_)
  apply measurable_path_iff.mpr
  intro t
  change Measurable (fun p : (I → ℝ) × (I → Path) =>
    (t : ℝ) * p.1 i + p.2 i t)
  exact (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).add
    ((continuous_eval_const t).measurable.comp
      ((measurable_pi_apply i).comp measurable_snd))

def driftIntegrand {I : Type u_9} (b : (ℝ≥0 × (I → ℝ)) → I → ℝ)
    (y : I → Path) (i : I) (s : ℝ) : ℝ :=
  b (s.toNNReal, fun j => y j s.toNNReal) i

theorem measurable_driftIntegrand {I : Type u_10}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b) (i : I) :
    Measurable (fun p : (I → Path) × ℝ => driftIntegrand b p.1 i p.2) := by
  apply ((measurable_pi_apply i).comp hb).comp
  refine (continuous_real_toNNReal.measurable.comp measurable_snd).prodMk ?_
  refine Measurable.of_eval (fun j => ?_)
  exact continuous_eval.measurable.comp
    (((measurable_pi_apply j).comp measurable_fst).prodMk
      (continuous_real_toNNReal.measurable.comp measurable_snd))

theorem intervalIntegrable_driftIntegrand {I : Type u_11}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C) (y : I → Path) (i : I) (u v : ℝ) :
    IntervalIntegrable (driftIntegrand b y i) volume u v := by
  apply (intervalIntegrable_const (c := C)).mono_fun'
  · exact ((measurable_driftIntegrand hb i).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards [] with s
    exact hbound (s.toNNReal, fun j => y j s.toNNReal) i

def driftPrimitive {I : Type u_12} (b : (ℝ≥0 × (I → ℝ)) → I → ℝ)
    (hb : Measurable b) (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (y : I → Path) (i : I) : Path :=
  ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), driftIntegrand b y i s,
    (intervalIntegral.continuous_primitive
      (intervalIntegrable_driftIntegrand hb C hbound y i) 0).comp continuous_subtype_val⟩

theorem measurable_driftPrimitive {I : Type u_13}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C) (i : I) :
    Measurable (fun y : I → Path => driftPrimitive b hb C hbound y i) := by
  apply measurable_path_iff.mpr
  intro t
  change Measurable (fun y : I → Path =>
    ∫ s in (0 : ℝ)..(t : ℝ), driftIntegrand b y i s)
  simp only [intervalIntegral]
  exact ((measurable_driftIntegrand hb i).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (0 : ℝ) t))).measurable.sub
    ((measurable_driftIntegrand hb i).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Ioc (t : ℝ) 0))).measurable

def innovation {I : Type u_14} (b : (ℝ≥0 × (I → ℝ)) → I → ℝ)
    (hb : Measurable b) (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (y : I → Path) (i : I) : Path :=
  y i - driftPrimitive b hb C hbound y i

theorem measurable_innovation {I : Type u_15}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C) :
    Measurable (innovation b hb C hbound) := by
  refine Measurable.of_eval (fun i => ?_)
  apply measurable_path_iff.mpr
  intro t
  exact ((continuous_eval_const t).measurable.comp (measurable_pi_apply i)).sub
    ((continuous_eval_const t).measurable.comp (measurable_driftPrimitive hb C hbound i))

theorem innovation_reconstruction {I : Type u_16}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C) (y : I → Path) (i : I) (t : ℝ≥0) :
    y i t = innovation b hb C hbound y i t +
      ∫ s in (0 : ℝ)..(t : ℝ), driftIntegrand b y i s := by
  simp [innovation, driftPrimitive]

theorem driftPrimitive_eq_of_agree {I : Type u_17}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    {y z : I → Path} (t : ℝ≥0)
    (h : ∀ i s, s ≤ t → y i s = z i s) (i : I) :
    driftPrimitive b hb C hbound y i t = driftPrimitive b hb C hbound z i t := by
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Set.Icc (0 : ℝ) (t : ℝ) := by
    simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] using hs
  have hst : s.toNNReal ≤ t := by
    exact_mod_cast (show (s.toNNReal : ℝ) ≤ (t : ℝ) by
      simpa [Real.toNNReal_of_nonneg hs'.1] using hs'.2)
  have heq : (fun j => y j s.toNNReal) = (fun j => z j s.toNNReal) :=
    funext (fun j => h j s.toNNReal hst)
  simp only [driftIntegrand, heq]

theorem innovation_eq_of_agree {I : Type u_18}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    {y z : I → Path} (t : ℝ≥0)
    (h : ∀ i s, s ≤ t → y i s = z i s) (i : I) :
    innovation b hb C hbound y i t = innovation b hb C hbound z i t := by
  change y i t - driftPrimitive b hb C hbound y i t =
    z i t - driftPrimitive b hb C hbound z i t
  rw [h i t le_rfl, driftPrimitive_eq_of_agree hb C hbound t h i]

def stoppedPath (t : ℝ≥0) (y : Path) : Path :=
  ⟨fun s => y (min s t), y.continuous.comp (continuous_id.min continuous_const)⟩

abbrev rawHistory {Ω : Type u_19} {I : Type u_20} (Y : Ω → I → Path) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ i : I, ⨆ s : ℝ≥0, ⨆ (_ : s ≤ t),
    MeasurableSpace.comap (fun ω => Y ω i s) inferInstance

theorem measurable_rawHistory_eval {Ω : Type u_21} {I : Type u_22} (Y : Ω → I → Path)
    (t s : ℝ≥0) (hs : s ≤ t) (i : I) :
    @Measurable Ω ℝ (rawHistory Y t) _ (fun ω => Y ω i s) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le i (le_iSup_of_le s (le_iSup_of_le hs le_rfl))

theorem measurable_stoppedFamily_rawHistory {Ω : Type u_23} {I : Type u_24} (Y : Ω → I → Path)
    (t : ℝ≥0) :
    @Measurable Ω (I → Path) (rawHistory Y t) _
      (fun ω i => stoppedPath t (Y ω i)) := by
  let : MeasurableSpace Ω := rawHistory Y t
  refine Measurable.of_eval (fun i => ?_)
  apply measurable_path_iff.mpr
  intro s
  exact measurable_rawHistory_eval Y t (min s t) (min_le_right _ _) i

theorem rawHistory_mono {Ω : Type u_25} {I : Type u_26} (Y : Ω → I → Path)
    {s t : ℝ≥0} (hst : s ≤ t) : rawHistory Y s ≤ rawHistory Y t := by
  refine iSup_le (fun i => iSup_le (fun u => iSup_le (fun hus => ?_)))
  exact le_iSup_of_le i (le_iSup_of_le u (le_iSup_of_le (hus.trans hst) le_rfl))

theorem rawHistory_le {Ω : Type u_27} {I : Type u_28} [MeasurableSpace Ω]
    {Y : Ω → I → Path} (hY : Measurable Y) (t : ℝ≥0) :
    rawHistory Y t ≤ ‹MeasurableSpace Ω› := by
  refine iSup_le (fun i => iSup_le (fun s => iSup_le (fun _ => ?_)))
  exact ((continuous_eval_const s).measurable.comp
    ((measurable_pi_apply i).comp hY)).comap_le

theorem measurable_innovation_eval_rawHistory {Ω : Type u_29} {I : Type u_30}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (Y : Ω → I → Path) (t : ℝ≥0) (i : I) :
    @Measurable Ω ℝ (rawHistory Y t) _
      (fun ω => innovation b hb C hbound (Y ω) i t) := by
  let : MeasurableSpace Ω := rawHistory Y t
  have hm : Measurable (fun ω =>
      innovation b hb C hbound (fun j => stoppedPath t (Y ω j)) i t) :=
    (measurable_path_iff.mp
      ((measurable_pi_apply i).comp (measurable_innovation hb C hbound)) t).comp
        (measurable_stoppedFamily_rawHistory Y t)
  convert hm using 1
  funext ω
  apply innovation_eq_of_agree hb C hbound t
  intro j s hs
  simp [stoppedPath, min_eq_left hs]

end Problem336AdditiveD139.PathRealization

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace Problem336AdditiveD139.Decoder

def envelope (M L : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  M * L ^ n * t ^ n / (n.factorial : ℝ)

theorem envelope_nonneg {M L t : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (ht : 0 ≤ t) (n : ℕ) : 0 ≤ envelope M L n t := by
  unfold envelope
  positivity

theorem continuous_envelope (M L : ℝ) (n : ℕ) : Continuous (envelope M L n) := by
  unfold envelope
  fun_prop

theorem integral_envelope (M L t : ℝ) (n : ℕ) :
    (∫ s in 0..t, L * envelope M L n s) = envelope M L (n + 1) t := by
  have hfun : (fun s => L * envelope M L n s) =
      (fun s => (L * M * L ^ n / (n.factorial : ℝ)) * s ^ n) := by
    funext s
    unfold envelope
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  simp only [envelope, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, zero_pow (Nat.succ_ne_zero n), sub_zero, pow_succ]
  field_simp

theorem envelope_tendsto_zero (M L t : ℝ) :
    Tendsto (fun n => envelope M L n t) atTop (𝓝 0) := by
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (L * t)).const_mul M
  simpa only [envelope, mul_pow, mul_div_assoc, mul_assoc, mul_zero] using h

theorem uniform_volterra_unique {I : Type u_1} (u : I → ℝ → ℝ)
    (M L T : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hbound : ∀ i t, t ∈ Icc 0 T → |u i t| ≤ M)
    (hresponse : ∀ a : ℝ → ℝ, Continuous a →
      (∀ t ∈ Icc 0 T, 0 ≤ a t) →
      (∀ i t, t ∈ Icc 0 T → |u i t| ≤ a t) →
      ∀ i t, t ∈ Icc 0 T → |u i t| ≤ ∫ s in 0..t, L * a s) :
    ∀ i t, t ∈ Icc 0 T → u i t = 0 := by
  have hn : ∀ n i t, t ∈ Icc 0 T → |u i t| ≤ envelope M L n t := by
    intro n
    induction n with
    | zero => simpa [envelope] using hbound
    | succ n ih =>
      intro i t ht
      have h := hresponse (envelope M L n) (continuous_envelope M L n)
        (fun s hs => envelope_nonneg hM hL hs.1 n) ih i t ht
      simpa only [integral_envelope] using h
  intro i t ht
  have hle : |u i t| ≤ 0 :=
    ge_of_tendsto (envelope_tendsto_zero M L t) (Eventually.of_forall fun n => hn n i t ht)
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

theorem bounded_drift_decoder_unique {I : Type u_2}
    (b : ℝ → (I → ℝ) → I → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ t, 0 ≤ t → ∀ x i, 0 ≤ b t x i ∧ b t x i ≤ 1)
    (hlip : ∀ t, 0 ≤ t → ∀ x y D, 0 ≤ D →
      (∀ i, |x i - y i| ≤ D) → ∀ i, |b t x i - b t y i| ≤ L * D)
    (w z z' : I → ℝ → ℝ)
    (hzint : ∀ i t, 0 ≤ t →
      IntervalIntegrable (fun s => b s (fun j => z j s) i) volume 0 t)
    (hz'int : ∀ i t, 0 ≤ t →
      IntervalIntegrable (fun s => b s (fun j => z' j s) i) volume 0 t)
    (hz : ∀ i t, 0 ≤ t →
      z i t = w i t + ∫ s in 0..t, b s (fun j => z j s) i)
    (hz' : ∀ i t, 0 ≤ t →
      z' i t = w i t + ∫ s in 0..t, b s (fun j => z' j s) i) :
    ∀ i t, 0 ≤ t → z i t = z' i t := by
  let u : I → ℝ → ℝ := fun i t => z i t - z' i t
  have hdiff : ∀ i t, 0 ≤ t → u i t =
      ∫ s in 0..t, b s (fun j => z j s) i - b s (fun j => z' j s) i := by
    intro i t ht
    rw [intervalIntegral.integral_sub (hzint i t ht) (hz'int i t ht)]
    dsimp [u]
    rw [hz i t ht, hz' i t ht]
    ring
  intro i T hT
  have hbound : ∀ j t, t ∈ Icc 0 T → |u j t| ≤ T := by
    intro j t ht
    rw [hdiff j t ht.1]
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := t) (C := (1 : ℝ))
      (f := fun s => b s (fun k => z k s) j - b s (fun k => z' k s) j) (by
        intro s hs
        rw [uIoc_of_le ht.1] at hs
        rw [Real.norm_eq_abs]
        have h₁ := hb s hs.1.le (fun k => z k s) j
        have h₂ := hb s hs.1.le (fun k => z' k s) j
        apply abs_le.mpr
        constructor <;> linarith)
    have hn' : |∫ s in 0..t,
        b s (fun k => z k s) j - b s (fun k => z' k s) j| ≤ t := by
      simpa only [Real.norm_eq_abs, sub_zero, one_mul, abs_of_nonneg ht.1] using hn
    exact hn'.trans ht.2
  have hresponse : ∀ a : ℝ → ℝ, Continuous a →
      (∀ t ∈ Icc 0 T, 0 ≤ a t) →
      (∀ j t, t ∈ Icc 0 T → |u j t| ≤ a t) →
      ∀ j t, t ∈ Icc 0 T → |u j t| ≤ ∫ s in 0..t, L * a s := by
    intro a ha hnon hmajor j t ht
    rw [hdiff j t ht.1, ← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le ht.1
      (Eventually.of_forall ?_) ((continuous_const.mul ha).intervalIntegrable 0 t)
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
    rw [Real.norm_eq_abs]
    exact hlip s hs.1.le (fun k => z k s) (fun k => z' k s) (a s)
      (hnon s hsT) (fun k => hmajor k s hsT) j
  have hzero := uniform_volterra_unique u T L T hT hL hbound hresponse i T ⟨hT, le_rfl⟩
  exact sub_eq_zero.mp hzero

end Problem336AdditiveD139.Decoder

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped NNReal Topology

namespace Problem336AdditiveD139.PathRealization

local instance : MeasurableSpace Path := borel Path
local instance : BorelSpace Path := ⟨rfl⟩

theorem innovation_injective {I : Type u_1}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hunit : ∀ p i, 0 ≤ b p i ∧ b p i ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ t x y D, 0 ≤ D → (∀ i, |x i - y i| ≤ D) →
      ∀ i, |b (t, x) i - b (t, y) i| ≤ L * D) :
    Function.Injective (innovation b hb C hbound) := by
  intro y z heq
  have hu := Decoder.bounded_drift_decoder_unique
    (fun t x => b (t.toNNReal, x)) L hL
    (fun t _ x i => hunit (t.toNNReal, x) i)
    (fun t _ x y D hD hxy i => hlip t.toNNReal x y D hD hxy i)
    (fun i t => innovation b hb C hbound y i t.toNNReal)
    (fun i t => y i t.toNNReal) (fun i t => z i t.toNNReal)
    (fun i t _ => intervalIntegrable_driftIntegrand hb C hbound y i 0 t)
    (fun i t _ => intervalIntegrable_driftIntegrand hb C hbound z i 0 t)
    (fun i t ht => by
      simpa only [Real.toNNReal_of_nonneg ht, NNReal.coe_mk, driftIntegrand] using
        innovation_reconstruction hb C hbound y i t.toNNReal)
    (fun i t ht => by
      rw [heq]
      simpa only [Real.toNNReal_of_nonneg ht, NNReal.coe_mk, driftIntegrand] using
        innovation_reconstruction hb C hbound z i t.toNNReal)
  funext i
  apply ContinuousMap.ext
  intro t
  simpa using hu i (t : ℝ) t.property

theorem innovation_measurableEmbedding {I : Type u_2} [Countable I]
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hunit : ∀ p i, 0 ≤ b p i ∧ b p i ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ t x y D, 0 ≤ D → (∀ i, |x i - y i| ≤ D) →
      ∀ i, |b (t, x) i - b (t, y) i| ≤ L * D) :
    MeasurableEmbedding (innovation b hb C hbound) :=
  (measurable_innovation hb C hbound).measurableEmbedding
    (innovation_injective hb C hbound hunit L hL hlip)

theorem innovation_leftTranslate {Γ : Type u_3} [Group Γ]
    {b : (ℝ≥0 × (Γ → ℝ)) → Γ → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hequiv : ∀ (g : Γ) t x i,
      b (t, leftTranslate g x) i = b (t, x) (g⁻¹ * i))
    (g : Γ) (y : Γ → Path) :
    innovation b hb C hbound (leftTranslate g y) =
      leftTranslate g (innovation b hb C hbound y) := by
  funext i
  apply ContinuousMap.ext
  intro t
  change y (g⁻¹ * i) t - (∫ s in (0 : ℝ)..(t : ℝ),
    b (s.toNNReal, leftTranslate g (fun j => y j s.toNNReal)) i) =
      y (g⁻¹ * i) t - (∫ s in (0 : ℝ)..(t : ℝ),
        b (s.toNNReal, fun j => y j s.toNNReal) (g⁻¹ * i))
  simp_rw [hequiv]

def inverseOnImage {I : Type u_4} {f : (I → Path) → (I → Path)}
    (hf : MeasurableEmbedding f) (w : I → Path) : I → Path := by
  classical
  exact if w ∈ Set.range f then hf.invFun w else 0

theorem measurable_inverseOnImage {I : Type u_5} {f : (I → Path) → (I → Path)}
    (hf : MeasurableEmbedding f) : Measurable (inverseOnImage hf) := by
  classical
  exact Measurable.ite hf.measurableSet_range hf.measurable_invFun measurable_const

@[simp] theorem inverseOnImage_apply {I : Type u_6} {f : (I → Path) → (I → Path)}
    (hf : MeasurableEmbedding f) (y : I → Path) :
    inverseOnImage hf (f y) = y := by
  classical
  rw [inverseOnImage, ite_eq_left (Set.mem_range_self y)]
  exact hf.leftInverse_invFun y

theorem inverseOnImage_leftTranslate {Γ : Type u_7} [Group Γ]
    {f : (Γ → Path) → (Γ → Path)} (hf : MeasurableEmbedding f)
    (hequiv : ∀ g y, f (leftTranslate g y) = leftTranslate g (f y))
    (g : Γ) (w : Γ → Path) :
    inverseOnImage hf (leftTranslate g w) = leftTranslate g (inverseOnImage hf w) := by
  classical
  by_cases hw : w ∈ Set.range f
  · obtain ⟨y, rfl⟩ := hw
    rw [← hequiv, inverseOnImage_apply, inverseOnImage_apply]
  · have hgw : leftTranslate g w ∉ Set.range f := by
      rintro ⟨y, hy⟩
      apply hw
      refine ⟨leftTranslate g⁻¹ y, ?_⟩
      rw [hequiv, hy]
      funext i
      simp [leftTranslate]
    simp only [inverseOnImage, ite_eq_right hgw, ite_eq_right hw]
    rfl

theorem exists_equivariant_innovation_leftInverse
    {Γ : Type u_8} [Group Γ] [Countable Γ]
    {b : (ℝ≥0 × (Γ → ℝ)) → Γ → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hunit : ∀ p i, 0 ≤ b p i ∧ b p i ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ t x y D, 0 ≤ D → (∀ i, |x i - y i| ≤ D) →
      ∀ i, |b (t, x) i - b (t, y) i| ≤ L * D)
    (hequiv : ∀ (g : Γ) t x i,
      b (t, leftTranslate g x) i = b (t, x) (g⁻¹ * i)) :
    ∃ Z : (Γ → Path) → (Γ → Path),
      Measurable Z ∧
      (∀ g w, Z (leftTranslate g w) = leftTranslate g (Z w)) ∧
      Function.LeftInverse Z (innovation b hb C hbound) := by
  let hf := innovation_measurableEmbedding hb C hbound hunit L hL hlip
  refine ⟨inverseOnImage hf, measurable_inverseOnImage hf, ?_, ?_⟩
  · exact inverseOnImage_leftTranslate hf
      (fun g y => innovation_leftTranslate hb C hbound hequiv g y)
  · exact inverseOnImage_apply hf

end Problem336AdditiveD139.PathRealization

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal Topology

namespace Problem336AdditiveD139.GroupInnovation


abbrev Path := PathRealization.Path

local instance : MeasurableSpace Path := borel Path
local instance : BorelSpace Path := ⟨rfl⟩

variable {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]

def drift (μ : ProbabilityMeasure (Γ → Bool))
    (p : ℝ≥0 × (Γ → ℝ)) : Γ → ℝ :=
  groupDrift μ p.1 p.2

theorem measurable_drift (μ : ProbabilityMeasure (Γ → Bool)) :
    Measurable (drift μ) := by
  change Measurable (fun p : ℝ≥0 × (Γ → ℝ) => groupDrift μ (p.1 : ℝ) p.2)
  have htime : Measurable (fun p : ℝ≥0 × (Γ → ℝ) => (p.1 : ℝ)) :=
    measurable_coe_nnreal_real.comp measurable_fst
  have hpair : Measurable (fun p : ℝ≥0 × (Γ → ℝ) => ((p.1 : ℝ), p.2)) :=
    htime.prodMk measurable_snd
  have h := (measurable_groupDrift μ).comp hpair
  exact h

theorem drift_mem_unitInterval (μ : ProbabilityMeasure (Γ → Bool))
    (p : ℝ≥0 × (Γ → ℝ)) (i : Γ) : 0 ≤ drift μ p i ∧ drift μ p i ≤ 1 :=
  groupDrift_mem_Icc μ p.1 p.2 i

theorem abs_drift_le_one (μ : ProbabilityMeasure (Γ → Bool))
    (p : ℝ≥0 × (Γ → ℝ)) (i : Γ) : |drift μ p i| ≤ 1 := by
  rw [abs_of_nonneg (drift_mem_unitInterval μ p i).1]
  exact (drift_mem_unitInterval μ p i).2

def transform (μ : ProbabilityMeasure (Γ → Bool)) : (Γ → Path) → Γ → Path :=
  PathRealization.innovation (drift μ) (measurable_drift μ) 1 (abs_drift_le_one μ)

theorem measurable_transform (μ : ProbabilityMeasure (Γ → Bool)) :
    Measurable (transform μ) :=
  PathRealization.measurable_innovation (measurable_drift μ) 1 (abs_drift_le_one μ)

@[simp] theorem transform_apply (μ : ProbabilityMeasure (Γ → Bool))
    (y : Γ → Path) (i : Γ) (t : ℝ≥0) :
    transform μ y i t = y i t - ∫ s in (0 : ℝ)..(t : ℝ),
      groupDrift μ (s.toNNReal : ℝ) (fun j => y j s.toNNReal) i := by
  rfl

theorem transform_apply_real_time (μ : ProbabilityMeasure (Γ → Bool))
    (y : Γ → Path) (i : Γ) (t : ℝ≥0) :
    transform μ y i t = y i t - ∫ s in (0 : ℝ)..(t : ℝ),
      groupDrift μ s (fun j => y j s.toNNReal) i := by
  rw [transform_apply]
  apply congrArg (fun r : ℝ => y i t - r)
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : (0 : ℝ) ≤ s :=
    (le_min (le_refl (0 : ℝ)) t.property).trans hs.1
  change groupDrift μ (s.toNNReal : ℝ) (fun j => y j s.toNNReal) i =
    groupDrift μ s (fun j => y j s.toNNReal) i
  simp only [Real.toNNReal_of_nonneg hs0, NNReal.coe_mk]

theorem transform_leftTranslate (μ : ProbabilityMeasure (Γ → Bool))
    (hμ : InvariantBinaryLaw μ) (g : Γ) (y : Γ → Path) :
    transform μ (leftTranslate g y) = leftTranslate g (transform μ y) := by
  apply PathRealization.innovation_leftTranslate
  intro g t x i
  exact congrFun (groupDrift_leftTranslate μ hμ g t x) i

theorem exists_equivariant_leftInverse_of_finite_response
    (hresponse : ∀ (F : Type u) [Fintype F] [Nonempty F]
      (ν : ProbabilityMeasure (F → Bool)), StronglyRayleighFinite ν →
      ∀ (i : F) (h h' : F → ℝ) (D : ℝ), 0 ≤ D →
        (∀ j, |h j - h' j| ≤ D) → |tiltMean ν h i - tiltMean ν h' i| ≤ D / 2)
    (μ : ProbabilityMeasure (Γ → Bool))
    (hSR : StronglyRayleighCountable μ) (hInv : InvariantBinaryLaw μ) :
    ∃ Z : (Γ → Path) → (Γ → Path),
      Measurable Z ∧
      (∀ g w, Z (leftTranslate g w) = leftTranslate g (Z w)) ∧
      Function.LeftInverse Z (transform μ) := by
  apply PathRealization.exists_equivariant_innovation_leftInverse
    (measurable_drift μ) 1 (abs_drift_le_one μ) (drift_mem_unitInterval μ)
    ((1 : ℝ) / 2) (by positivity)
  · intro t x y D hD hxy i
    simpa only [drift, div_eq_mul_inv, one_mul, mul_comm] using
      groupDrift_response_of_finite_response hresponse μ hSR t x y D hD hxy i
  · intro g t x i
    exact congrFun (groupDrift_leftTranslate μ hInv g t x) i

end Problem336AdditiveD139.GroupInnovation

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory

namespace Problem336AdditiveD139.IIDAction

variable {Γ : Type u_1} {α : Type u_2} {β : Type u_3} [Group Γ]

@[simp]theorem leftTranslate_one (a : Γ → α) : leftTranslate (1 : Γ) a = a := by
  funext h
  simp [leftTranslate]

theorem leftTranslate_mul (g h : Γ) (a : Γ → α) :
    leftTranslate (g * h) a = leftTranslate g (leftTranslate h a) := by
  funext k
  simp [leftTranslate, mul_assoc]

@[simp]theorem leftTranslate_inv (g : Γ) (a : Γ → α) :
    leftTranslate g⁻¹ (leftTranslate g a) = a := by
  rw [← leftTranslate_mul]
  simp

@[simp]theorem leftTranslate_const (g : Γ) (a : α) :
    leftTranslate g (fun _ : Γ => a) = fun _ => a := rfl

theorem measurable_leftTranslate [MeasurableSpace α] (g : Γ) :
    Measurable (leftTranslate g : (Γ → α) → Γ → α) := by
  exact Measurable.of_eval fun h => measurable_pi_apply (g⁻¹ * h)

theorem coordinateMap_equivariant (f : α → β) (g : Γ) (u : Γ → α) :
    (fun i => f (leftTranslate g u i)) = leftTranslate g (fun i => f (u i)) := rfl

omit [Group Γ] in
theorem measurable_coordinateMap [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) : Measurable (fun u : Γ → α => fun i => f (u i)) := by
  exact Measurable.of_eval fun i => hf.comp (measurable_pi_apply i)

omit [Group Γ] in
theorem isProbabilityMeasure_iidUnitLabels [MeasurableSpace Γ] :
    IsProbabilityMeasure (iidUnitLabels Γ) := by
  unfold iidUnitLabels
  infer_instance

theorem map_leftTranslate_iidUnitLabels [MeasurableSpace Γ] (g : Γ) :
    Measure.map (leftTranslate g) (iidUnitLabels Γ) = iidUnitLabels Γ := by
  unfold iidUnitLabels leftTranslate
  exact Measure.map_infinitePi_infinitePi_of_inj (mul_right_injective g⁻¹)

theorem measurePreserving_leftTranslate_iidUnitLabels [MeasurableSpace Γ] (g : Γ) :
    MeasurePreserving (leftTranslate g) (iidUnitLabels Γ) (iidUnitLabels Γ) :=
  ⟨measurable_leftTranslate g, map_leftTranslate_iidUnitLabels g⟩

omit [Group Γ] in
theorem map_coordinatewise [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure α) [IsProbabilityMeasure ρ] (f : α → β) (hf : Measurable f) :
    Measure.map (fun u : Γ → α => fun i => f (u i))
      (Measure.infinitePi (fun _ : Γ => ρ)) =
        Measure.infinitePi (fun _ : Γ => Measure.map f ρ) := by
  exact Measure.infinitePi_map_pi _ (fun _ => hf)

theorem factor_of_coordinatewise_decoder [MeasurableSpace Γ] [MeasurableSpace α]
    (ρ : Measure α) (f : UnitLabel → α) (hf : Measurable f)
    (hfρ : Measure.map f volume = ρ)
    (μ : ProbabilityMeasure (Γ → Bool))
    (Ψ : (Γ → α) → Γ → Bool) (hΨ : Measurable Ψ)
    (hΨeq : ∀ g u, Ψ (leftTranslate g u) = leftTranslate g (Ψ u))
    (hΨlaw : Measure.map Ψ (Measure.infinitePi (fun _ : Γ => ρ)) =
      (μ : Measure (Γ → Bool))) : HasEquivariantIIDFactor μ := by
  refine ⟨fun u => Ψ (fun i => f (u i)), hΨ.comp (measurable_coordinateMap f hf), ?_, ?_⟩
  · intro g u
    exact hΨeq g (fun i => f (u i))
  · rw [show (fun u : Γ → UnitLabel => Ψ (fun i => f (u i))) =
        Ψ ∘ (fun u : Γ → UnitLabel => fun i => f (u i)) from rfl]
    rw [← Measure.map_map hΨ (measurable_coordinateMap f hf)]
    rw [iidUnitLabels, map_coordinatewise volume f hf, hfρ, hΨlaw]

theorem factor_of_standardBorel_decoder [MeasurableSpace Γ] [MeasurableSpace α]
    [Nonempty α] [StandardBorelSpace α] (ρ : Measure α) [IsProbabilityMeasure ρ]
    (μ : ProbabilityMeasure (Γ → Bool))
    (Ψ : (Γ → α) → Γ → Bool) (hΨ : Measurable Ψ)
    (hΨeq : ∀ g u, Ψ (leftTranslate g u) = leftTranslate g (Ψ u))
    (hΨlaw : Measure.map Ψ (Measure.infinitePi (fun _ : Γ => ρ)) =
      (μ : Measure (Γ → Bool))) : HasEquivariantIIDFactor μ := by
  obtain ⟨f, hf, hfρ⟩ := ρ.exists_measurable_map_eq
  exact factor_of_coordinatewise_decoder ρ f hf hfρ μ Ψ hΨ hΨeq hΨlaw

end Problem336AdditiveD139.IIDAction

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem336AdditiveD139

def binaryReadout (z : ℕ → ℝ) : Bool := by
  classical
  exact if ∀ N : ℕ, ∃ n : ℕ, (1 : ℝ) / 2 < z (N + n) then true else false

def asymptoticReadout {I : Type u_1} (z : ℕ → I → ℝ) : I → Bool :=
  fun i => binaryReadout (fun n => z n i)

theorem measurable_binaryReadout : Measurable binaryReadout := by
  classical
  have hp : MeasurableSet {z : ℕ → ℝ | ∀ N : ℕ, ∃ n : ℕ,
      (1 : ℝ) / 2 < z (N + n)} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
      measurableSet_lt measurable_const (measurable_pi_apply (N + n))
  exact Measurable.ite hp measurable_const measurable_const

theorem binaryReadout_eq_of_tendsto {z : ℕ → ℝ} {b : Bool}
    (h : Tendsto z atTop (𝓝 (boolReal b))) : binaryReadout z = b := by
  classical
  cases b with
  | false =>
    have hz : Tendsto z atTop (𝓝 (0 : ℝ)) := by simpa [boolReal] using h
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hz).2 (1 / 2) (by norm_num))
    have hp : ¬ (∀ N : ℕ, ∃ n : ℕ, (1 : ℝ) / 2 < z (N + n)) := by
      intro hp
      obtain ⟨n, hn⟩ := hp N
      have hh := hN (N + n) (Nat.le_add_right N n)
      linarith
    simp only [binaryReadout, ite_eq_right hp]
  | true =>
    have hz : Tendsto z atTop (𝓝 (1 : ℝ)) := by simpa [boolReal] using h
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hz).1 (1 / 2) (by norm_num))
    have hp : ∀ M : ℕ, ∃ n : ℕ, (1 : ℝ) / 2 < z (M + n) := by
      intro M
      exact ⟨N, hN (M + N) (Nat.le_add_left N M)⟩
    simp only [binaryReadout, ite_eq_left hp]

theorem measurable_asymptoticReadout {I : Type u_2} :
    Measurable (@asymptoticReadout I) := by
  apply Measurable.of_eval
  intro i
  exact measurable_binaryReadout.comp
    (Measurable.of_eval fun n => (measurable_pi_apply i).comp (measurable_pi_apply n))

theorem asymptoticReadout_eq_of_tendsto {I : Type u_3} {z : ℕ → I → ℝ}
    {x : I → Bool} (h : ∀ i, Tendsto (fun n => z n i) atTop (𝓝 (boolReal (x i)))) :
    asymptoticReadout z = x := by
  funext i
  exact binaryReadout_eq_of_tendsto (h i)

theorem asymptoticReadout_leftTranslate {Γ : Type u_4} [Group Γ]
    (g : Γ) (z : ℕ → Γ → ℝ) :
    asymptoticReadout (fun n => leftTranslate g (z n)) =
      leftTranslate g (asymptoticReadout z) := rfl

theorem asymptoticReadout_ae_eq {Ω : Type u_5} {I : Type u_6} [MeasurableSpace Ω] [Countable I]
    (ρ : Measure Ω) (Z : ℕ → Ω → I → ℝ) (X : Ω → I → Bool)
    (h : ∀ i, ∀ᵐ ω ∂ρ, Tendsto (fun n => Z n ω i) atTop (𝓝 (boolReal (X ω i)))) :
    (fun ω => asymptoticReadout (fun n => Z n ω)) =ᵐ[ρ] X := by
  filter_upwards [ae_all_iff.mpr h] with ω hω
  exact asymptoticReadout_eq_of_tendsto hω

theorem map_asymptoticReadout_of_reference
    {Ω : Type u_7} {W : Type u_8} {I : Type u_9} [MeasurableSpace Ω] [MeasurableSpace W] [Countable I]
    (ρ : Measure Ω) (ν : Measure W) (μ : Measure (I → Bool))
    (Z : ℕ → W → I → ℝ) (hZ : ∀ n, Measurable (Z n))
    (W₀ : Ω → W) (hW₀ : Measurable W₀) (hWlaw : Measure.map W₀ ρ = ν)
    (X : Ω → I → Bool) (hXlaw : Measure.map X ρ = μ)
    (hlim : ∀ i, ∀ᵐ ω ∂ρ,
      Tendsto (fun n => Z n (W₀ ω) i) atTop (𝓝 (boolReal (X ω i)))) :
    Measure.map (fun w => asymptoticReadout (fun n => Z n w)) ν = μ := by
  have hreadout : Measurable (fun w => asymptoticReadout (fun n => Z n w)) :=
    measurable_asymptoticReadout.comp (Measurable.of_eval hZ)
  rw [← hWlaw, Measure.map_map hreadout hW₀]
  exact (Measure.map_congr
    (asymptoticReadout_ae_eq ρ (fun n ω => Z n (W₀ ω)) X hlim)).trans hXlaw

theorem hasEquivariantIIDFactor_of_asymptotic_observations
    {Γ : Type u_10} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    (μ : ProbabilityMeasure (Γ → Bool))
    (Z : ℕ → (Γ → UnitLabel) → Γ → ℝ)
    (hZ : ∀ n, Measurable (Z n))
    (heq : ∀ n g u, Z n (leftTranslate g u) = leftTranslate g (Z n u))
    (X : (Γ → UnitLabel) → Γ → Bool)
    (hX : Measure.map X (iidUnitLabels Γ) = (μ : Measure (Γ → Bool)))
    (hlim : ∀ i, ∀ᵐ u ∂iidUnitLabels Γ,
      Tendsto (fun n => Z n u i) atTop (𝓝 (boolReal (X u i)))) :
    HasEquivariantIIDFactor μ := by
  refine ⟨fun u => asymptoticReadout (fun n => Z n u), ?_, ?_, ?_⟩
  · exact measurable_asymptoticReadout.comp (Measurable.of_eval hZ)
  · intro g u
    have hfields : (fun n => Z n (leftTranslate g u)) =
        (fun n => leftTranslate g (Z n u)) := funext (fun n => heq n g u)
    change asymptoticReadout (fun n => Z n (leftTranslate g u)) = _
    rw [hfields, asymptoticReadout_leftTranslate]
  · exact (Measure.map_congr (asymptoticReadout_ae_eq (iidUnitLabels Γ) Z X hlim)).trans hX

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem336AdditiveD139.BrownianSublinear

variable {Ω : Type u_1} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem hasLaw_unit_increment (hB : IsPreBrownianReal B P) (n : ℕ) :
    HasLaw (fun ω => B (n + 1) ω - B n ω) (gaussianReal 0 1) P := by
  convert hB.hasLaw_sub (n + 1) n using 1
  try rfl
  simp [Real.nndist_eq]

theorem tendsto_nat_div_ae (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => B n ω / (n : ℝ)) atTop (𝓝 0) := by
  let X : ℕ → Ω → ℝ := fun n ω => B (n + 1) ω - B n ω
  have hXlaw : ∀ n, HasLaw (X n) (gaussianReal 0 1) P :=
    fun n => hasLaw_unit_increment hB n
  have hXint : Integrable (X 0) P :=
    by simpa [X, Pi.sub_def] using (hB.integrable_eval 1).sub (hB.integrable_eval 0)
  have hXindep : iIndepFun X P := by
    simpa [X] using hB.hasIndepIncrements.nat (t := fun n : ℕ => (n : ℝ≥0))
      (fun a b h => by simpa only using (Nat.cast_le.mpr h : (a : ℝ≥0) ≤ b))
  have hXident : ∀ n, IdentDistrib (X n) (X 0) P P :=
    fun n => (hXlaw n).identDistrib (hXlaw 0)
  have hmean : ∫ ω, X 0 ω ∂P = 0 := by
    rw [(hXlaw 0).integral_eq, integral_id_gaussianReal]
  have hSLLN := strong_law_ae_real X hXint
    (fun _ _ hij => hXindep.indepFun hij) hXident
  filter_upwards [hSLLN, hB.eval_zero_ae_eq_zero] with ω hω hzero
  have hsum : ∀ n, (∑ k ∈ Finset.range n, X k ω) = B n ω := by
    intro n
    simpa [X, hzero] using Finset.sum_range_sub (fun k : ℕ => B k ω) n
  simpa only [hsum, hmean] using hω

theorem tendsto_nat_div_all_ae {I : Type u_2} [Countable I]
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, ∀ i, Tendsto (fun n : ℕ => B i n ω / (n : ℝ)) atTop (𝓝 0) :=
  ae_all_iff.mpr fun i => tendsto_nat_div_ae (hB i)

theorem tendsto_nat_observation_slope_all_ae {I : Type u_3} [Countable I]
    (B : I → ℝ≥0 → Ω → ℝ) (X : I → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, ∀ i, Tendsto
      (fun n : ℕ => ((n : ℝ) * X i ω + B i n ω) / (n : ℝ))
      atTop (𝓝 (X i ω)) := by
  filter_upwards [tendsto_nat_div_all_ae B hB] with ω hω
  intro i
  have hlim : Tendsto (fun n : ℕ => X i ω + B i n ω / (n : ℝ))
      atTop (𝓝 (X i ω)) := by
    simpa using tendsto_const_nhds.add (hω i)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

end Problem336AdditiveD139.BrownianSublinear

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem336AdditiveD139.PathSamplerTransfer

variable {Γ : Type u_1} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

def decoderSlopes (Z : (Γ → C(ℝ≥0, ℝ)) → Γ → C(ℝ≥0, ℝ))
    (n : ℕ) (w : Γ → C(ℝ≥0, ℝ)) (i : Γ) : ℝ :=
  Z w i (n + 1 : ℝ≥0) / ((n : ℝ) + 1)

omit [Group Γ] [Countable Γ] [MeasurableSpace Γ] in
lemma measurable_decoderSlopes
    {Z : (Γ → C(ℝ≥0, ℝ)) → Γ → C(ℝ≥0, ℝ)}
    (hZ : Measurable Z) (n : ℕ) : Measurable (decoderSlopes Z n) := by
  apply Measurable.of_eval
  intro i
  exact (((continuous_eval_const (n + 1 : ℝ≥0)).measurable.comp
    (measurable_pi_apply i)).comp hZ).div_const _

omit [Countable Γ] [MeasurableSpace Γ] [MeasurableSpace C(ℝ≥0, ℝ)]
    [BorelSpace C(ℝ≥0, ℝ)] in
lemma decoderSlopes_equivariant
    {Z : (Γ → C(ℝ≥0, ℝ)) → Γ → C(ℝ≥0, ℝ)}
    (heq : ∀ g w, Z (leftTranslate g w) = leftTranslate g (Z w))
    (n : ℕ) (g : Γ) (w : Γ → C(ℝ≥0, ℝ)) :
    decoderSlopes Z n (leftTranslate g w) = leftTranslate g (decoderSlopes Z n w) := by
  funext i
  simp only [decoderSlopes, heq, leftTranslate]

theorem factor_of_reference_decoder
    {Ω : Type u_2} [MeasurableSpace Ω]
    (P : Measure Ω) (ρ : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure ρ]
    (μ : ProbabilityMeasure (Γ → Bool))
    (Z : (Γ → C(ℝ≥0, ℝ)) → Γ → C(ℝ≥0, ℝ))
    (hZ : Measurable Z)
    (heq : ∀ g w, Z (leftTranslate g w) = leftTranslate g (Z w))
    (W : Ω → Γ → C(ℝ≥0, ℝ)) (hW : Measurable W)
    (hWlaw : P.map W = Measure.infinitePi (fun _ : Γ => ρ))
    (X : Ω → Γ → Bool) (hXlaw : P.map X = (μ : Measure (Γ → Bool)))
    (B : Ω → Γ → ℝ≥0 → ℝ)
    (hdecode : ∀ i, ∀ᵐ ω ∂P, ∀ n : ℕ,
      Z (W ω) i (n + 1 : ℝ≥0) =
        ((n : ℝ) + 1) * boolReal (X ω i) + B ω i (n + 1 : ℝ≥0))
    (hnoise : ∀ i, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => B ω i (n + 1 : ℝ≥0) / ((n : ℝ) + 1))
        atTop (𝓝 0)) :
    HasEquivariantIIDFactor μ := by
  let Ψ : (Γ → C(ℝ≥0, ℝ)) → Γ → Bool :=
    fun w => asymptoticReadout (fun n => decoderSlopes Z n w)
  have hΨ : Measurable Ψ :=
    measurable_asymptoticReadout.comp
      (Measurable.of_eval (measurable_decoderSlopes hZ))
  have hΨeq : ∀ g w, Ψ (leftTranslate g w) = leftTranslate g (Ψ w) := by
    intro g w
    change asymptoticReadout (fun n => decoderSlopes Z n (leftTranslate g w)) = _
    simp_rw [decoderSlopes_equivariant heq]
    exact asymptoticReadout_leftTranslate g _
  apply IIDAction.factor_of_standardBorel_decoder ρ μ Ψ hΨ hΨeq
  apply map_asymptoticReadout_of_reference P _ _ (decoderSlopes Z)
    (measurable_decoderSlopes hZ) W hW hWlaw X hXlaw
  intro i
  filter_upwards [hdecode i, hnoise i] with ω hdec hlim
  have hformula : (fun n => decoderSlopes Z n (W ω) i) =
      (fun n : ℕ => boolReal (X ω i) + B ω i (n + 1 : ℝ≥0) / ((n : ℝ) + 1)) := by
    funext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [decoderSlopes, hdec n, add_div, mul_div_cancel_left₀ _ hn]
  rw [hformula]
  simpa only [add_zero] using tendsto_const_nhds.add hlim

theorem factor_of_brownian_reference_decoder
    {Ω : Type u_3} [MeasurableSpace Ω]
    (P : Measure Ω) (ρ : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure ρ]
    (μ : ProbabilityMeasure (Γ → Bool))
    (Z : (Γ → C(ℝ≥0, ℝ)) → Γ → C(ℝ≥0, ℝ))
    (hZ : Measurable Z)
    (heq : ∀ g w, Z (leftTranslate g w) = leftTranslate g (Z w))
    (W : Ω → Γ → C(ℝ≥0, ℝ)) (hW : Measurable W)
    (hWlaw : P.map W = Measure.infinitePi (fun _ : Γ => ρ))
    (X : Ω → Γ → Bool) (hXlaw : P.map X = (μ : Measure (Γ → Bool)))
    (B : Ω → Γ → ℝ≥0 → ℝ)
    (hdecode : ∀ i, ∀ᵐ ω ∂P, ∀ n : ℕ,
      Z (W ω) i (n + 1 : ℝ≥0) =
        ((n : ℝ) + 1) * boolReal (X ω i) + B ω i (n + 1 : ℝ≥0))
    (hB : ∀ i, ProbabilityTheory.IsPreBrownianReal (fun t ω => B ω i t) P) :
    HasEquivariantIIDFactor μ := by
  apply factor_of_reference_decoder P ρ μ Z hZ heq W hW hWlaw X hXlaw B hdecode
  intro i
  filter_upwards [BrownianSublinear.tendsto_nat_div_ae (hB i)] with ω hω
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    hω.comp (tendsto_add_atTop_nat 1)

end Problem336AdditiveD139.PathSamplerTransfer

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem336AdditiveD139.PathRealization

local instance : MeasurableSpace Path := borel Path
local instance : BorelSpace Path := ⟨rfl⟩

theorem factor_of_reference_innovation
    {Γ : Type u_1} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    {Ω : Type u_2} [MeasurableSpace Ω]
    (P : Measure Ω) (ρ : Measure Path) [IsProbabilityMeasure ρ]
    (μ : ProbabilityMeasure (Γ → Bool))
    {b : (ℝ≥0 × (Γ → ℝ)) → Γ → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hunit : ∀ p i, 0 ≤ b p i ∧ b p i ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ t x y D, 0 ≤ D → (∀ i, |x i - y i| ≤ D) →
      ∀ i, |b (t, x) i - b (t, y) i| ≤ L * D)
    (hequiv : ∀ (g : Γ) t x i,
      b (t, leftTranslate g x) i = b (t, x) (g⁻¹ * i))
    (Y : Ω → Γ → Path) (hY : Measurable Y)
    (hinnovation : P.map (fun ω => innovation b hb C hbound (Y ω)) =
      Measure.infinitePi (fun _ : Γ => ρ))
    (X : Ω → Γ → Bool) (hXlaw : P.map X = (μ : Measure (Γ → Bool)))
    (B : Ω → Γ → ℝ≥0 → ℝ)
    (hobs : ∀ ω i t, Y ω i t = (t : ℝ) * boolReal (X ω i) + B ω i t)
    (hnoise : ∀ i, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => B ω i (n + 1 : ℝ≥0) / ((n : ℝ) + 1))
        atTop (𝓝 0)) :
    HasEquivariantIIDFactor μ := by
  obtain ⟨Z, hZ, hZeq, hleft⟩ := exists_equivariant_innovation_leftInverse
    hb C hbound hunit L hL hlip hequiv
  apply PathSamplerTransfer.factor_of_reference_decoder P ρ μ Z hZ hZeq
    (fun ω => innovation b hb C hbound (Y ω))
    ((measurable_innovation hb C hbound).comp hY) hinnovation X hXlaw B
  · intro i
    filter_upwards [] with ω
    intro n
    rw [hleft (Y ω)]
    simpa using hobs ω i (n + 1 : ℝ≥0)
  · exact hnoise

theorem factor_of_brownian_reference_innovation
    {Γ : Type u_3} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    {Ω : Type u_4} [MeasurableSpace Ω]
    (P : Measure Ω) (ρ : Measure Path) [IsProbabilityMeasure ρ]
    (μ : ProbabilityMeasure (Γ → Bool))
    {b : (ℝ≥0 × (Γ → ℝ)) → Γ → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hunit : ∀ p i, 0 ≤ b p i ∧ b p i ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ t x y D, 0 ≤ D → (∀ i, |x i - y i| ≤ D) →
      ∀ i, |b (t, x) i - b (t, y) i| ≤ L * D)
    (hequiv : ∀ (g : Γ) t x i,
      b (t, leftTranslate g x) i = b (t, x) (g⁻¹ * i))
    (Y : Ω → Γ → Path) (hY : Measurable Y)
    (hinnovation : P.map (fun ω => innovation b hb C hbound (Y ω)) =
      Measure.infinitePi (fun _ : Γ => ρ))
    (X : Ω → Γ → Bool) (hXlaw : P.map X = (μ : Measure (Γ → Bool)))
    (B : Ω → Γ → ℝ≥0 → ℝ)
    (hobs : ∀ ω i t, Y ω i t = (t : ℝ) * boolReal (X ω i) + B ω i t)
    (hBrownian : ∀ i, ProbabilityTheory.IsPreBrownianReal (fun t ω => B ω i t) P) :
    HasEquivariantIIDFactor μ := by
  apply factor_of_reference_innovation P ρ μ hb C hbound hunit L hL hlip
    hequiv Y hY hinnovation X hXlaw B hobs
  intro i
  filter_upwards [BrownianSublinear.tendsto_nat_div_ae (hBrownian i)] with ω hω
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    hω.comp (Filter.tendsto_add_atTop_nat 1)

end Problem336AdditiveD139.PathRealization

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139.ReferenceObservation

variable {I : Type u_1} {W : Type u_2} [MeasurableSpace W]

abbrev Space (I : Type u_3) (W : Type u_4) := (I → Bool) × (I → W)

def law (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure W) :
    Measure (Space I W) :=
  (μ : Measure (I → Bool)).prod (Measure.infinitePi (fun _ : I => (ν : Measure W)))

instance law_isProbabilityMeasure (μ : ProbabilityMeasure (I → Bool))
    (ν : ProbabilityMeasure W) : IsProbabilityMeasure (law μ ν) := by
  unfold law
  infer_instance

variable (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure W)

theorem signal_hasLaw : HasLaw (Prod.fst : Space I W → I → Bool) μ (law μ ν) :=
  measurePreserving_fst.hasLaw

theorem noiseField_hasLaw :
    HasLaw (Prod.snd : Space I W → I → W)
      (Measure.infinitePi (fun _ : I => (ν : Measure W))) (law μ ν) :=
  measurePreserving_snd.hasLaw

theorem noise_hasLaw (i : I) :
    HasLaw (fun ω : Space I W => ω.2 i) ν (law μ ν) :=
  (measurePreserving_eval_infinitePi (fun _ : I => (ν : Measure W)) i).hasLaw.comp
    (noiseField_hasLaw μ ν)

theorem iid_noise : iIndepFun (fun i (ω : Space I W) => ω.2 i) (law μ ν) := by
  exact (iIndepFun_iff_hasLaw_Pi_infinitePi (noise_hasLaw μ ν)
    measurable_snd.aemeasurable).2 (noiseField_hasLaw μ ν)

theorem signal_indep_noiseField :
    IndepFun (Prod.fst : Space I W → I → Bool) Prod.snd (law μ ν) := by
  exact indepFun_prod measurable_id measurable_id

variable (B : ℝ≥0 → W → ℝ)

def noise (i : I) (t : ℝ≥0) (ω : Space I W) : ℝ := B t (ω.2 i)

def observation (i : I) (t : ℝ≥0) (ω : Space I W) : ℝ :=
  (t : ℝ) * boolReal (ω.1 i) + noise B i t ω

theorem noise_projection_measurePreserving (i : I) :
    MeasurePreserving (fun ω : Space I W => ω.2 i) (law μ ν) (ν : Measure W) :=
  (noise_hasLaw μ ν i).measurePreserving (by fun_prop)

theorem noise_isPreBrownian (hB : IsPreBrownianReal B (ν : Measure W)) (i : I) :
    IsPreBrownianReal (noise B i) (law μ ν) where
  hasLaw S := (hB.hasLaw S).comp (noise_hasLaw μ ν i)

theorem noise_isBrownian (hB : IsBrownianReal B (ν : Measure W)) (i : I) :
    IsBrownianReal (noise B i) (law μ ν) where
  toIsPreBrownianReal := noise_isPreBrownian μ ν B hB.toIsPreBrownianReal i
  cont := (noise_projection_measurePreserving μ ν i).quasiMeasurePreserving.ae hB.cont

theorem iid_noise_paths (hBm : ∀ t, Measurable (B t)) :
    iIndepFun (fun i (ω : Space I W) t => noise B i t ω) (law μ ν) := by
  exact (iid_noise μ ν).comp (fun _ w t => B t w) (by fun_prop)

theorem signal_indep_noise_paths (hBm : ∀ t, Measurable (B t)) :
    IndepFun (Prod.fst : Space I W → I → Bool)
      (fun (ω : Space I W) i t => noise B i t ω) (law μ ν) := by
  exact (signal_indep_noiseField μ ν).comp measurable_id
    (show Measurable (fun w : I → W => fun i t => B t (w i)) from by fun_prop)

theorem measurable_noise (hBm : ∀ t, Measurable (B t)) (i : I) (t : ℝ≥0) :
    Measurable (noise B i t) := by
  exact (hBm t).comp ((measurable_pi_apply i).comp measurable_snd)

theorem measurable_observation (hBm : ∀ t, Measurable (B t)) (i : I) (t : ℝ≥0) :
    Measurable (observation B i t) := by
  unfold observation
  have hb : Measurable boolReal := measurable_of_finite _
  exact (measurable_const.mul (hb.comp ((measurable_pi_apply i).comp measurable_fst))).add
    (measurable_noise B hBm i t)

theorem measurable_observation_joint
    (hBm : Measurable (fun p : ℝ≥0 × W => B p.1 p.2)) (i : I) :
    Measurable (fun p : ℝ≥0 × Space I W => observation B i p.1 p.2) := by
  unfold observation noise
  have hb : Measurable boolReal := measurable_of_finite _
  fun_prop

omit [MeasurableSpace W] in
theorem continuous_observation_path (hBc : ∀ w, Continuous (fun t => B t w))
    (i : I) (ω : Space I W) : Continuous (fun t => observation B i t ω) := by
  exact ((NNReal.continuous_coe).mul continuous_const).add (hBc (ω.2 i))

theorem ae_continuous_noise_paths [Countable I]
    (hB : IsBrownianReal B (ν : Measure W)) :
    ∀ᵐ ω ∂law μ ν, ∀ i : I, Continuous (fun t => noise B i t ω) :=
  ae_all_iff.2 (fun i => (noise_isBrownian μ ν B hB i).cont)

theorem ae_continuous_observation_paths [Countable I]
    (hB : IsBrownianReal B (ν : Measure W)) :
    ∀ᵐ ω ∂law μ ν, ∀ i : I, Continuous (fun t => observation B i t ω) := by
  filter_upwards [ae_continuous_noise_paths μ ν B hB] with ω hω i
  exact (NNReal.continuous_coe.mul continuous_const).add (hω i)

omit [MeasurableSpace W] in
theorem signal_real_mem_unitInterval (i : I) (ω : Space I W) :
    boolReal (ω.1 i) ∈ Set.Icc (0 : ℝ) 1 := by
  cases ω.1 i <;> simp [boolReal]

theorem integrable_signal_real (i : I) :
    Integrable (fun ω : Space I W => boolReal (ω.1 i)) (law μ ν) := by
  have hm : Measurable (fun ω : Space I W => boolReal (ω.1 i)) :=
    (measurable_of_finite boolReal).comp ((measurable_pi_apply i).comp measurable_fst)
  refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (signal_real_mem_unitInterval i ω).1]
    exact (signal_real_mem_unitInterval i ω).2

theorem integrable_observation (hB : IsPreBrownianReal B (ν : Measure W))
    (i : I) (t : ℝ≥0) : Integrable (observation B i t) (law μ ν) :=
  ((integrable_signal_real μ ν i).const_mul (t : ℝ)).add
    ((noise_isPreBrownian μ ν B hB i).integrable_eval t)

end Problem336AdditiveD139.ReferenceObservation

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336AdditiveD139.PathRealization

local instance : MeasurableSpace Path := borel Path
local instance : BorelSpace Path := ⟨rfl⟩

def referencePaths {I : Type u_1} (ω : ReferenceObservation.Space I Path) : I → Path :=
  fun i => observationPath (boolReal (ω.1 i)) (ω.2 i)

theorem measurable_referencePaths {I : Type u_2} : Measurable (@referencePaths I) := by
  refine Measurable.of_eval (fun i => measurable_path_iff.mpr (fun t => ?_))
  exact ReferenceObservation.measurable_observation (fun (s : ℝ≥0) (w : Path) => w s)
    (fun s => (continuous_eval_const s).measurable) i t

@[simp] theorem referencePaths_apply {I : Type u_3}
    (ω : ReferenceObservation.Space I Path) (i : I) (t : ℝ≥0) :
    referencePaths ω i t = ReferenceObservation.observation (fun (s : ℝ≥0) (w : Path) => w s) i t ω := rfl

theorem factor_of_canonical_innovation_law
    {Γ : Type u_4} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (ν : ProbabilityMeasure Path)
    (hν : IsPreBrownianReal (fun (t : ℝ≥0) (w : Path) => w t) (ν : Measure Path))
    {b : (ℝ≥0 × (Γ → ℝ)) → Γ → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hunit : ∀ p i, 0 ≤ b p i ∧ b p i ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ t x y D, 0 ≤ D → (∀ i, |x i - y i| ≤ D) →
      ∀ i, |b (t, x) i - b (t, y) i| ≤ L * D)
    (hequiv : ∀ (g : Γ) t x i,
      b (t, leftTranslate g x) i = b (t, x) (g⁻¹ * i))
    (hinnovation : (ReferenceObservation.law μ ν).map
      (fun ω => innovation b hb C hbound (referencePaths ω)) =
        Measure.infinitePi (fun _ : Γ => (ν : Measure Path))) :
    HasEquivariantIIDFactor μ := by
  apply factor_of_brownian_reference_innovation (ReferenceObservation.law μ ν)
    (ν : Measure Path) μ hb C hbound hunit L hL hlip hequiv
    referencePaths measurable_referencePaths hinnovation
    Prod.fst (ReferenceObservation.signal_hasLaw μ ν).map_eq
    (fun ω i t => ω.2 i t)
  · intro ω i t
    rfl
  · exact ReferenceObservation.noise_isPreBrownian μ ν
      (fun (t : ℝ≥0) (w : Path) => w t) hν

end Problem336AdditiveD139.PathRealization

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem336AdditiveD139.GroupSampler


abbrev Path := PathRealization.Path

local instance : MeasurableSpace Path := borel Path
local instance : BorelSpace Path := ⟨rfl⟩

variable {Γ : Type u} [Group Γ] [Countable Γ] [MeasurableSpace Γ] [DecidableEq Γ]

theorem factor_of_innovation_law
    (hresponse : ∀ (F : Type u) [Fintype F] [Nonempty F]
      (ν : ProbabilityMeasure (F → Bool)), StronglyRayleighFinite ν →
      ∀ (i : F) (h h' : F → ℝ) (D : ℝ), 0 ≤ D →
        (∀ j, |h j - h' j| ≤ D) → |tiltMean ν h i - tiltMean ν h' i| ≤ D / 2)
    (μ : ProbabilityMeasure (Γ → Bool))
    (hSR : StronglyRayleighCountable μ) (hInv : InvariantBinaryLaw μ)
    (ν : ProbabilityMeasure Path)
    (hν : IsPreBrownianReal (fun t (w : Path) => w t) (ν : Measure Path))
    (hlaw : (ReferenceObservation.law μ ν).map
      (fun ω => GroupInnovation.transform μ (PathRealization.referencePaths ω)) =
        Measure.infinitePi (fun _ : Γ => (ν : Measure Path))) :
    HasEquivariantIIDFactor μ := by
  apply PathRealization.factor_of_canonical_innovation_law μ ν hν
    (GroupInnovation.measurable_drift μ) 1 (GroupInnovation.abs_drift_le_one μ)
    (GroupInnovation.drift_mem_unitInterval μ) ((1 : ℝ) / 2) (by positivity)
  · intro t x y D hD hxy i
    simpa only [GroupInnovation.drift, div_eq_mul_inv, one_mul, mul_comm] using
      groupDrift_response_of_finite_response hresponse μ hSR t x y D hD hxy i
  · intro g t x i
    exact congrFun (groupDrift_leftTranslate μ hInv g t x) i
  · exact hlaw

end Problem336AdditiveD139.GroupSampler

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped BigOperators Interval Topology

namespace Problem336AdditiveD139.CharacteristicTaylor

theorem norm_sub_zero_le_of_deriv_bound {E : Type u_1} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f f' : ℝ → E}
    (hd : ∀ t, HasDerivAt f (f' t) t) (hc : Continuous f')
    (C : ℝ) (n : ℕ) (hb : ∀ t, ‖f' t‖ ≤ C * |t| ^ n) (x : ℝ) :
    ‖f x - f 0‖ ≤ C * |x| ^ (n + 1) / (n + 1) := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 x)]
  calc
    ‖∫ t in 0..x, f' t‖ ≤ ∫ t in Ι 0 x, ‖f' t‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ t in Ι 0 x, C * |t| ^ n := by
      apply integral_mono
      · exact hc.norm.integrableOn_Icc.mono_set Set.uIoc_subset_uIcc
      · exact (continuous_const.mul (continuous_abs.pow n)).integrableOn_Icc.mono_set
          Set.uIoc_subset_uIcc
      · exact hb
    _ = C * |x| ^ (n + 1) / (n + 1) := by
      rw [integral_const_mul]
      have h := integral_pow_abs_sub_uIoc (a := (0 : ℝ)) (b := x) (n := n)
      simp only [sub_zero] at h
      rw [h]
      ring

theorem norm_exp_I_mul_sub_one_sub_linear (x : ℝ) :
    ‖Complex.exp (Complex.I * x) - 1 - Complex.I * x‖ ≤ |x| ^ 2 / 2 := by
  let f : ℝ → ℂ := fun t => Complex.exp (Complex.I * t) - 1 - Complex.I * t
  let f' : ℝ → ℂ := fun t => Complex.I * (Complex.exp (Complex.I * t) - 1)
  have hd : ∀ t, HasDerivAt f (f' t) t := by
    intro t
    have hlin := (hasDerivAt_id (t : ℂ)).const_mul Complex.I
    have h := ((hlin.cexp.sub_const 1).sub hlin).comp_ofReal
    convert h using 1 <;> dsimp [f, f']
    ring
  have hc : Continuous f' := by dsimp [f']; fun_prop
  have hb : ∀ t, ‖f' t‖ ≤ 1 * |t| ^ 1 := by
    intro t
    simpa [f', norm_mul, Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t))
  have h := norm_sub_zero_le_of_deriv_bound hd hc 1 1 hb x
  norm_num [f] at h ⊢
  exact h

theorem norm_exp_I_mul_sub_quadratic (x : ℝ) :
    ‖Complex.exp (Complex.I * x) - 1 - Complex.I * x + (x : ℂ) ^ 2 / 2‖ ≤
      |x| ^ 3 / 6 := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp (Complex.I * t) - 1 - Complex.I * t + (t : ℂ) ^ 2 / 2
  let f' : ℝ → ℂ := fun t =>
    Complex.I * (Complex.exp (Complex.I * t) - 1 - Complex.I * t)
  have hd : ∀ t, HasDerivAt f (f' t) t := by
    intro t
    have hlin := (hasDerivAt_id (t : ℂ)).const_mul Complex.I
    have h := (((hlin.cexp.sub_const 1).sub hlin).add
      (((hasDerivAt_id (t : ℂ)).pow 2).div_const 2)).comp_ofReal
    convert h using 1 <;> dsimp [f, f']
    ring_nf
    simp [Complex.I_sq]
  have hc : Continuous f' := by dsimp [f']; fun_prop
  have hb : ∀ t, ‖f' t‖ ≤ (1 / 2 : ℝ) * |t| ^ 2 := by
    intro t
    simpa [f', norm_mul, div_eq_mul_inv, mul_comm] using
      norm_exp_I_mul_sub_one_sub_linear t
  have h := norm_sub_zero_le_of_deriv_bound hd hc (1 / 2) 2 hb x
  norm_num [f] at h
  convert h using 1
  ring

end Problem336AdditiveD139.CharacteristicTaylor

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Problem336AdditiveD139
namespace CharacteristicTaylor

theorem abs_exp_neg_sub_one_add_le {s : ℝ} (hs : 0 ≤ s) :
    |Real.exp (-s) - 1 + s| ≤ s ^ 2 := by
  by_cases hs1 : s ≤ 1
  · simpa [Real.norm_eq_abs, abs_of_nonneg hs] using
      (Real.norm_exp_sub_one_sub_id_le (x := -s) (by simpa [Real.norm_eq_abs, abs_of_nonneg hs] using hs1))
  · have h1 : 1 ≤ s := le_of_lt (lt_of_not_ge hs1)
    have he0 := Real.exp_pos (-s)
    have he1 : Real.exp (-s) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hs)
    rw [abs_of_nonneg (by linarith)]
    nlinarith

section Conditional

variable {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} {X : Ω → ℝ}

lemma integrable_exp_I_mul (hX : Integrable X μ) :
    Integrable (fun ω => Complex.exp (Complex.I * (X ω : ℂ))) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · have hc : Continuous (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) := by fun_prop
    exact hc.comp_aestronglyMeasurable hX.aestronglyMeasurable
  · filter_upwards with ω
    simp

theorem condExp_quadratic_remainder_le (hm : m ≤ mΩ)
    (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => (X ω) ^ 2) μ)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) μ) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I * (X a : ℂ)) | m] ω - 1 -
          Complex.I * (μ[X | m] ω : ℂ) +
          (μ[fun a => (X a) ^ 2 | m] ω : ℂ) / 2‖ ≤
        μ[fun a => |X a| ^ 3 | m] ω / 6 := by
  let e : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω : ℂ))
  let c : Ω → ℂ := fun ω => (X ω : ℂ)
  let q : Ω → ℂ := fun ω => ((X ω) ^ 2 : ℝ)
  let R : Ω → ℂ := e - (fun _ => 1) - Complex.I • c + (1 / 2 : ℂ) • q
  have he : Integrable e μ := integrable_exp_I_mul hX
  have hc : Integrable c μ := hX.ofReal
  have hq : Integrable q μ := hX2.ofReal
  have hR : Integrable R μ := ((he.sub (integrable_const 1)).sub (hc.smul Complex.I)).add
      (hq.smul (1 / 2 : ℂ))
  have hbound : ∀ᵐ ω ∂μ, ‖R ω‖ ≤ (1 / 6 : ℝ) * |X ω| ^ 3 := by
    filter_upwards with ω
    simpa [R, e, c, q, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_pow, div_eq_mul_inv, mul_comm] using norm_exp_I_mul_sub_quadratic (X ω)
  have hmono := condExp_mono hR.norm (hX3.const_mul (1 / 6)) hbound (m := m)
  have hscale := condExp_smul (1 / 6 : ℝ) (fun ω => |X ω| ^ 3) m (μ := μ)
  have hcE := Complex.ofRealCLM.comp_condExp_comm hX (m := m)
  have hqE := Complex.ofRealCLM.comp_condExp_comm hX2 (m := m)
  have hR1 := condExp_sub he (integrable_const (1 : ℂ)) m
  have hR2 := condExp_sub (he.sub (integrable_const (1 : ℂ))) (hc.smul Complex.I) m
  have hR3 := condExp_add ((he.sub (integrable_const (1 : ℂ))).sub (hc.smul Complex.I))
      (hq.smul (1 / 2 : ℂ)) m
  have hi := condExp_smul Complex.I c m (μ := μ)
  have hh := condExp_smul (1 / 2 : ℂ) q m (μ := μ)
  filter_upwards [norm_condExp_le (μ := μ) (m := m) R, hmono, hscale,
    hcE, hqE, hR1, hR2, hR3, hi, hh] with ω hn hb hs hcω hqω h1 h2 h3 hiω hhω
  have hce : μ[c | m] ω = (μ[X | m] ω : ℂ) := by
    simpa [c, Function.comp_def] using hcω.symm
  have hqe : μ[q | m] ω = (μ[fun a => X a ^ 2 | m] ω : ℂ) := by
    simpa [q, Function.comp_def] using hqω.symm
  have hRe : μ[R | m] ω = μ[e | m] ω - 1 - Complex.I * (μ[X | m] ω : ℂ) +
      (μ[fun a => X a ^ 2 | m] ω : ℂ) / 2 := by
    change μ[e - (fun _ => 1) - Complex.I • c + (1 / 2 : ℂ) • q | m] ω = _
    rw [h3]
    simp only [Pi.add_apply]
    rw [h2]
    simp only [Pi.sub_apply]
    rw [h1, hiω, hhω]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, condExp_const hm,
      hce, hqe]
    ring
  rw [hRe] at hn
  have hb' : μ[fun a => ‖R a‖ | m] ω ≤ μ[fun a => |X a| ^ 3 | m] ω / 6 := by
    calc
      _ ≤ μ[fun a => (1 / 6 : ℝ) * |X a| ^ 3 | m] ω := hb
      _ = _ := by
        change μ[(1 / 6 : ℝ) • (fun a => |X a| ^ 3) | m] ω = _
        rw [hs]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
  exact hn.trans hb'

theorem conditional_characteristic_bound (hm : m ≤ mΩ)
    (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => (X ω) ^ 2) μ)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) μ)
    (hmean : μ[X | m] =ᵐ[μ] fun _ => 0) {v : ℝ} (hv : 0 ≤ v) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I * (X a : ℂ)) | m] ω -
          (Real.exp (-v / 2) : ℂ)‖ ≤
        μ[fun a => |X a| ^ 3 | m] ω / 6 +
          |μ[fun a => (X a) ^ 2 | m] ω - v| / 2 + v ^ 2 / 4 := by
  have hg : ‖(1 : ℂ) - (v : ℂ) / 2 - (Real.exp (-v / 2) : ℂ)‖ ≤ v ^ 2 / 4 := by
    have hg0 := abs_exp_neg_sub_one_add_le (s := v / 2) (by positivity)
    have heq : (1 : ℂ) - (v : ℂ) / 2 - (Real.exp (-v / 2) : ℂ) =
        ((-(Real.exp (-(v / 2)) - 1 + v / 2) : ℝ) : ℂ) := by
      push_cast
      rw [neg_div]
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    convert hg0 using 1; ring
  filter_upwards [condExp_quadratic_remainder_le hm hX hX2 hX3, hmean] with ω hr hmω
  rw [hmω] at hr
  simp only [Complex.ofReal_zero, mul_zero, sub_zero] at hr
  let a : ℂ := μ[fun a => Complex.exp (Complex.I * (X a : ℂ)) | m] ω
  let q : ℝ := μ[fun a => (X a) ^ 2 | m] ω
  change ‖a - (Real.exp (-v / 2) : ℂ)‖ ≤ _
  calc
    _ = ‖(a - 1 + (q : ℂ) / 2) + ((v - q : ℝ) : ℂ) / 2 +
        (1 - (v : ℂ) / 2 - (Real.exp (-v / 2) : ℂ))‖ := by
          congr 1
          push_cast
          ring
    _ ≤ ‖a - 1 + (q : ℂ) / 2‖ + ‖((v - q : ℝ) : ℂ) / 2‖ +
        ‖1 - (v : ℂ) / 2 - (Real.exp (-v / 2) : ℂ)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ μ[fun a => |X a| ^ 3 | m] ω / 6 + |q - v| / 2 + v ^ 2 / 4 := by
      have hnorm : ‖((v - q : ℝ) : ℂ) / 2‖ = |q - v| / 2 := by
        simp only [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      rw [hnorm]
      exact add_le_add (add_le_add hr le_rfl) hg

end Conditional
end CharacteristicTaylor
end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ProbabilityTheory

namespace Problem336AdditiveD139.InnovationErrorScale

def errorConstant (L σ c₃ : ℝ) : ℝ :=
  L * σ + L ^ 2 / 2 + (2 / 3 : ℝ) * (c₃ * σ ^ 3 + L ^ 3) + σ ^ 4 / 4

theorem errorConstant_nonneg {L σ c₃ : ℝ}
    (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hc : 0 ≤ c₃) :
    0 ≤ errorConstant L σ c₃ := by
  unfold errorConstant
  positivity

theorem higher_powers_le (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    h ^ 2 ≤ h * Real.sqrt h ∧ h ^ 3 ≤ h * Real.sqrt h := by
  have hs0 := Real.sqrt_nonneg h
  have hs1 : Real.sqrt h ≤ 1 := by simpa using Real.sqrt_le_sqrt h1
  have hsq := Real.sq_sqrt h0
  have hhs : h ≤ Real.sqrt h := by nlinarith
  have h2 : h ^ 2 ≤ h * Real.sqrt h := by nlinarith
  have h3 : h ^ 3 ≤ h ^ 2 := by nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr h1)]
  exact ⟨h2, h3.trans h2⟩

theorem moment_error_le_scale {L σ c₃ h : ℝ}
    (hL : 0 ≤ L) (_hσ : 0 ≤ σ) (_hc : 0 ≤ c₃) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    (2 * (L * h) * (σ * Real.sqrt h) + (L * h) ^ 2) / 2 +
        4 * (c₃ * σ ^ 3 * h * Real.sqrt h + (L * h) ^ 3) / 6 +
        (h * σ ^ 2) ^ 2 / 4 ≤ errorConstant L σ c₃ * h * Real.sqrt h := by
  obtain ⟨h2, h3⟩ := higher_powers_le h h0 h1
  have hA : 0 ≤ L ^ 2 / 2 + σ ^ 4 / 4 := by positivity
  have hB : 0 ≤ (2 / 3 : ℝ) * L ^ 3 := by positivity
  calc
    _ = (L * σ + (2 / 3 : ℝ) * c₃ * σ ^ 3) * (h * Real.sqrt h) +
        (L ^ 2 / 2 + σ ^ 4 / 4) * h ^ 2 + (2 / 3 : ℝ) * L ^ 3 * h ^ 3 := by ring
    _ ≤ (L * σ + (2 / 3 : ℝ) * c₃ * σ ^ 3) * (h * Real.sqrt h) +
        (L ^ 2 / 2 + σ ^ 4 / 4) * (h * Real.sqrt h) +
        (2 / 3 : ℝ) * L ^ 3 * (h * Real.sqrt h) := by
      linarith [mul_le_mul_of_nonneg_left h2 hA, mul_le_mul_of_nonneg_left h3 hB]
    _ = errorConstant L σ c₃ * h * Real.sqrt h := by unfold errorConstant; ring

theorem local_error_le_scale {L σ c₃ h e e₂ e₃ : ℝ}
    (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hc : 0 ≤ c₃) (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (he : e ≤ e₂ / 2 + e₃ / 6 + (h * σ ^ 2) ^ 2 / 4)
    (he₂ : e₂ ≤ 2 * (L * h) * (σ * Real.sqrt h) + (L * h) ^ 2)
    (he₃ : e₃ ≤ 4 * (c₃ * σ ^ 3 * h * Real.sqrt h + (L * h) ^ 3)) :
    e ≤ errorConstant L σ c₃ * h * Real.sqrt h := by
  have hs := moment_error_le_scale hL hσ hc h0 h1
  linarith

end Problem336AdditiveD139.InnovationErrorScale

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem336AdditiveD139.GaussianMomentBounds

def standardThirdAbsMoment : ℝ := ∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 1

lemma standardThirdAbsMoment_nonneg : 0 ≤ standardThirdAbsMoment := by
  exact integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3

lemma integral_sq_gaussianReal (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at h
  simpa only [integral_id_gaussianReal, sub_zero] using h

lemma integral_abs_gaussianReal_le (v : ℝ≥0) :
    (∫ x : ℝ, |x| ∂gaussianReal 0 v) ≤ Real.sqrt v := by
  have hLp : MemLp (fun x : ℝ => |x|) 2 (gaussianReal 0 v) := by
    simpa only [Real.norm_eq_abs, id_eq] using
      (memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by norm_num)).norm
  have hv := variance_nonneg (fun x : ℝ => |x|) (gaussianReal 0 v)
  rw [variance_eq_sub hLp] at hv
  have hs : (∫ x : ℝ, |x| ^ 2 ∂gaussianReal 0 v) = v := by
    simpa only [sq_abs] using integral_sq_gaussianReal v
  change 0 ≤ (∫ x : ℝ, |x| ^ 2 ∂gaussianReal 0 v) -
    (∫ x : ℝ, |x| ∂gaussianReal 0 v) ^ 2 at hv
  rw [hs] at hv
  exact (Real.le_sqrt (by positivity) (by positivity)).2 (by linarith)

lemma gaussianReal_map_sqrt (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp [Real.sq_sqrt v.coe_nonneg]

lemma integral_abs_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, |x| ^ n ∂gaussianReal 0 v) =
      Real.sqrt v ^ n * (∫ x : ℝ, |x| ^ n ∂gaussianReal 0 1) := by
  rw [← gaussianReal_map_sqrt v, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [integral_const_mul]

lemma integral_abs_cube_gaussianReal (v : ℝ≥0) :
    (∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 v) =
      standardThirdAbsMoment * (v : ℝ) * Real.sqrt v := by
  rw [integral_abs_pow_gaussianReal]
  change Real.sqrt v ^ 3 * standardThirdAbsMoment = _
  rw [pow_succ, Real.sq_sqrt v.coe_nonneg]
  ring

lemma integrable_abs_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) (gaussianReal 0 v) := by
  simpa only [Real.norm_eq_abs, id_eq] using
    (memLp_id_gaussianReal' (μ := 0) (v := v) n (by simp)).integrable_norm_pow'

section RandomVariable

variable {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Q : Ω → ℝ}
  {v : ℝ≥0}

lemma integral_eq_zero_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, Q ω ∂P) = 0 := by
  simpa using hQ.integral_eq

lemma integral_sq_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, Q ω ^ 2 ∂P) = v := by
  calc
    _ = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v :=
      hQ.integral_comp (by fun_prop)
    _ = v := integral_sq_gaussianReal v

lemma integral_abs_le_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, |Q ω| ∂P) ≤ Real.sqrt v := by
  calc
    _ = ∫ x : ℝ, |x| ∂gaussianReal 0 v :=
      hQ.integral_comp (by fun_prop)
    _ ≤ Real.sqrt v := integral_abs_gaussianReal_le v

lemma integral_abs_cube_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, |Q ω| ^ 3 ∂P) = standardThirdAbsMoment * (v : ℝ) * Real.sqrt v := by
  calc
    _ = ∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 v :=
      hQ.integral_comp (by fun_prop)
    _ = _ := integral_abs_cube_gaussianReal v

lemma integrable_abs_pow_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) (n : ℕ) :
    Integrable (fun ω => |Q ω| ^ n) P := by
  have hi := integrable_abs_pow_gaussianReal v n
  rw [← hQ.map_eq] at hi
  exact (integrable_map_measure (by fun_prop) hQ.aemeasurable).mp hi

lemma integrable_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) : Integrable Q P := by
  have hi := integrable_abs_pow_of_hasLaw hQ 1
  simpa only [pow_one, ← Real.norm_eq_abs, integrable_norm_iff hQ.aemeasurable.aestronglyMeasurable]
    using hi

lemma integrable_sq_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) :
    Integrable (fun ω => Q ω ^ 2) P := by
  simpa only [sq_abs] using integrable_abs_pow_of_hasLaw hQ 2

end RandomVariable

section Conditional

variable {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {mQ mH : MeasurableSpace Ω} {Q : Ω → ℝ} {v : ℝ≥0}

lemma conditional_gaussian_moments
    (hQ : HasLaw Q (gaussianReal 0 v) P)
    (hleQ : mQ ≤ mΩ) (hleH : mH ≤ mΩ)
    (hmQ : StronglyMeasurable[mQ] Q) (hind : Indep mQ mH P) :
    (P[Q | mH] =ᵐ[P] fun _ => (0 : ℝ)) ∧
    (P[fun ω => Q ω ^ 2 | mH] =ᵐ[P] fun _ => (v : ℝ)) ∧
    (∀ᵐ ω ∂P, P[fun ω => |Q ω| | mH] ω ≤ Real.sqrt v) ∧
    (P[fun ω => |Q ω| ^ 3 | mH] =ᵐ[P]
      fun _ => standardThirdAbsMoment * (v : ℝ) * Real.sqrt v) := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  have hmean := condExp_indep_eq hleQ hleH hmQ hind
  have hsq := condExp_indep_eq hleQ hleH (hmQ.pow 2) hind
  have hmabs : StronglyMeasurable[mQ] (fun ω => |Q ω|) := by
    simpa only [Real.norm_eq_abs] using hmQ.norm
  have habs := condExp_indep_eq hleQ hleH hmabs hind
  have hcube := condExp_indep_eq hleQ hleH (hmabs.pow 3) hind
  change P[fun ω => Q ω ^ 2 | mH] =ᵐ[P]
    (fun _ => ∫ ω, Q ω ^ 2 ∂P) at hsq
  change P[fun ω => |Q ω| ^ 3 | mH] =ᵐ[P]
    (fun _ => ∫ ω, |Q ω| ^ 3 ∂P) at hcube
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [integral_eq_zero_of_hasLaw hQ] using hmean
  · simpa only [integral_sq_of_hasLaw hQ] using hsq
  · filter_upwards [habs] with ω hω
    exact hω.le.trans (integral_abs_le_of_hasLaw hQ)
  · simpa only [integral_abs_cube_of_hasLaw hQ] using hcube

end Conditional

end Problem336AdditiveD139.GaussianMomentBounds

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory

namespace Problem336AdditiveD139
namespace PerturbedMoments

lemma abs_square_add_sub_square_le (q r b : ℝ) (hb : 0 ≤ b) (hr : |r| ≤ b) :
    |(q + r) ^ 2 - q ^ 2| ≤ 2 * b * |q| + b ^ 2 := by
  calc
    |(q + r) ^ 2 - q ^ 2| = |2 * q * r + r ^ 2| := by congr 1; ring
    _ ≤ |2 * q * r| + |r ^ 2| := abs_add_le _ _
    _ = 2 * |q| * |r| + |r| ^ 2 := by simp [abs_mul, abs_pow]
    _ ≤ 2 * b * |q| + b ^ 2 := by
      have h₁ := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * |q|)
      have h₂ := sq_le_sq₀ (abs_nonneg r) hb |>.2 hr
      nlinarith

lemma abs_add_cube_le (q r b : ℝ) (hb : 0 ≤ b) (hr : |r| ≤ b) :
    |q + r| ^ 3 ≤ 4 * (|q| ^ 3 + b ^ 3) := by
  have hsum : |q + r| ≤ |q| + b := (abs_add_le q r).trans (by gcongr)
  have hpow := pow_le_pow_left₀ (abs_nonneg (q + r)) hsum 3
  have haux := mul_nonneg (add_nonneg (abs_nonneg q) hb) (sq_nonneg (|q| - b))
  nlinarith

variable {Ω : Type u_1} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}

theorem integrable_square_add [IsFiniteMeasure μ]
    {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b) (hQ : Integrable Q μ)
    (hQ₂ : Integrable (fun ω => Q ω ^ 2) μ)
    (hRm : AEStronglyMeasurable R μ) (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b) :
    Integrable (fun ω => (Q ω + R ω) ^ 2) μ := by
  refine (hQ₂.add ((hQ.abs.const_mul (2 * b)).add (integrable_const (b ^ 2)))).mono'
    ((hQ.aestronglyMeasurable.add hRm).pow 2) ?_
  filter_upwards [hR] with ω hω
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Q ω + R ω))]
  have h := abs_square_add_sub_square_le (Q ω) (R ω) b hb hω
  have h' := le_abs_self ((Q ω + R ω) ^ 2 - Q ω ^ 2)
  dsimp
  linarith

theorem integrable_abs_cube_add [IsFiniteMeasure μ]
    {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b)
    (hQm : AEStronglyMeasurable Q μ)
    (hQ₃ : Integrable (fun ω => |Q ω| ^ 3) μ)
    (hRm : AEStronglyMeasurable R μ) (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b) :
    Integrable (fun ω => |Q ω + R ω| ^ 3) μ := by
  refine ((hQ₃.add (integrable_const (b ^ 3))).const_mul 4).mono'
    (by
      convert (hQm.add hRm).norm.pow 3 using 1; ext ω; simp [Real.norm_eq_abs]) ?_
  filter_upwards [hR] with ω hω
  simpa only [Real.norm_eq_abs, Pi.add_apply, abs_of_nonneg (by positivity : 0 ≤ |Q ω + R ω| ^ 3)]
    using abs_add_cube_le (Q ω) (R ω) b hb hω

theorem abs_condExp_le_affine [IsFiniteMeasure μ]
    (hm : m ≤ m₀) {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (a b : ℝ) (hbound : ∀ᵐ ω ∂μ, |f ω| ≤ a * g ω + b) :
    ∀ᵐ ω ∂μ, |μ[f | m] ω| ≤ a * μ[g | m] ω + b := by
  have habs := abs_condExp_ae_le_condExp_abs (μ := μ) (m := m) f
  have hmono := condExp_mono (m := m) hf.abs
    ((hg.const_mul a).add (integrable_const b)) hbound
  have hadd := condExp_add (hg.const_mul a) (integrable_const b) m
  have hmul := condExp_smul (μ := μ) a g m
  filter_upwards [habs, hmono, hadd, hmul] with ω hω₁ hω₂ hω₃ hω₄
  have hconst : μ[(fun _ : Ω => b) | m] ω = b := by rw [condExp_const hm]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hω₁ hω₂ hω₃ hω₄
  change μ[(fun ω => a * g ω + b) | m] ω =
    μ[(fun ω => a * g ω) | m] ω + μ[(fun _ : Ω => b) | m] ω at hω₃
  change μ[(fun ω => a * g ω) | m] ω = a * μ[g | m] ω at hω₄
  calc
    |μ[f | m] ω| ≤ μ[(fun ω => |f ω|) | m] ω := hω₁
    _ ≤ μ[(fun ω => a * g ω + b) | m] ω := hω₂
    _ = a * μ[g | m] ω + b := by rw [hω₃, hω₄, hconst]

theorem condExp_square_perturbation [IsFiniteMeasure μ]
    (hm : m ≤ m₀) {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b)
    (hQ : Integrable Q μ) (hQ₂ : Integrable (fun ω => Q ω ^ 2) μ)
    (hD₂ : Integrable (fun ω => (Q ω + R ω) ^ 2) μ)
    (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b) :
    ∀ᵐ ω ∂μ,
      |μ[(fun ω => (Q ω + R ω) ^ 2) | m] ω - μ[(fun ω => Q ω ^ 2) | m] ω| ≤
        2 * b * μ[(fun ω => |Q ω|) | m] ω + b ^ 2 := by
  have hbound := abs_condExp_le_affine hm (hD₂.sub hQ₂) hQ.abs (2 * b) (b ^ 2)
    (hR.mono fun ω hω => abs_square_add_sub_square_le (Q ω) (R ω) b hb hω)
  have hsub := condExp_sub hD₂ hQ₂ m
  filter_upwards [hbound, hsub] with ω hω hω'
  simpa only [Pi.sub_apply, hω'] using hω

theorem condExp_abs_cube_perturbation [IsFiniteMeasure μ]
    (hm : m ≤ m₀) {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b)
    (hQ₃ : Integrable (fun ω => |Q ω| ^ 3) μ)
    (hD₃ : Integrable (fun ω => |Q ω + R ω| ^ 3) μ)
    (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b) :
    ∀ᵐ ω ∂μ,
      μ[(fun ω => |Q ω + R ω| ^ 3) | m] ω ≤
        4 * (μ[(fun ω => |Q ω| ^ 3) | m] ω + b ^ 3) := by
  have hbound : ∀ᵐ ω ∂μ, |(|Q ω + R ω| ^ 3)| ≤ 4 * |Q ω| ^ 3 + 4 * b ^ 3 := by
    filter_upwards [hR] with ω hω
    rw [abs_of_nonneg (by positivity)]
    nlinarith [abs_add_cube_le (Q ω) (R ω) b hb hω]
  have h := abs_condExp_le_affine hm hD₃ hQ₃ 4 (4 * b ^ 3) hbound
  filter_upwards [h] with ω hω
  exact (le_abs_self _).trans (hω.trans_eq (by ring))

theorem condExp_square_perturbation_error [IsFiniteMeasure μ]
    (hm : m ≤ m₀) {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b)
    (hQ : Integrable Q μ) (hQ₂ : Integrable (fun ω => Q ω ^ 2) μ)
    (hRm : AEStronglyMeasurable R μ) (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b)
    (v ε : ℝ) (hv : ∀ᵐ ω ∂μ, |μ[(fun ω => Q ω ^ 2) | m] ω - v| ≤ ε) :
    ∀ᵐ ω ∂μ,
      |μ[(fun ω => (Q ω + R ω) ^ 2) | m] ω - v| ≤
        ε + 2 * b * μ[(fun ω => |Q ω|) | m] ω + b ^ 2 := by
  have h := condExp_square_perturbation hm b hb hQ hQ₂
    (integrable_square_add b hb hQ hQ₂ hRm hR) hR
  filter_upwards [h, hv] with ω hω hvω
  have htri := abs_sub_le
    (μ[(fun ω => (Q ω + R ω) ^ 2) | m] ω)
    (μ[(fun ω => Q ω ^ 2) | m] ω) v
  linarith

theorem integral_square_perturbation [IsProbabilityMeasure μ]
    {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b)
    (hQ : Integrable Q μ) (hQ₂ : Integrable (fun ω => Q ω ^ 2) μ)
    (hRm : AEStronglyMeasurable R μ) (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b) :
    |(∫ ω, (Q ω + R ω) ^ 2 ∂μ) - ∫ ω, Q ω ^ 2 ∂μ| ≤
      2 * b * (∫ ω, |Q ω| ∂μ) + b ^ 2 := by
  have h := condExp_square_perturbation (m := ⊥) bot_le b hb hQ hQ₂
    (integrable_square_add b hb hQ hQ₂ hRm hR) hR
  obtain ⟨ω, hω⟩ := h.exists
  simpa only [condExp_bot] using hω

theorem integral_abs_cube_perturbation [IsProbabilityMeasure μ]
    {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b)
    (hQm : AEStronglyMeasurable Q μ)
    (hQ₃ : Integrable (fun ω => |Q ω| ^ 3) μ)
    (hRm : AEStronglyMeasurable R μ) (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b) :
    (∫ ω, |Q ω + R ω| ^ 3 ∂μ) ≤ 4 * ((∫ ω, |Q ω| ^ 3 ∂μ) + b ^ 3) := by
  have h := condExp_abs_cube_perturbation (m := ⊥) bot_le b hb hQ₃
    (integrable_abs_cube_add b hb hQm hQ₃ hRm hR) hR
  obtain ⟨ω, hω⟩ := h.exists
  simpa only [condExp_bot] using hω

end PerturbedMoments
end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal MeasureTheory

namespace Problem336AdditiveD139.GaussianPerturbation

open GaussianMomentBounds PerturbedMoments

variable {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {mQ mH : MeasurableSpace Ω} {Q R : Ω → ℝ} {v : ℝ≥0}

theorem integrable_moments
    (hQ : HasLaw Q (gaussianReal 0 v) P)
    (hRm : AEStronglyMeasurable[mΩ] R P) (b : ℝ) (hb : 0 ≤ b)
    (hR : ∀ᵐ ω ∂P, |R ω| ≤ b) :
    Integrable (fun ω => Q ω + R ω) P ∧
    Integrable (fun ω => (Q ω + R ω) ^ 2) P ∧
    Integrable (fun ω => |Q ω + R ω| ^ 3) P := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  have hQi := integrable_of_hasLaw hQ
  have hRi : Integrable R P := (integrable_const b).mono' hRm (by
    simpa only [Real.norm_eq_abs] using hR)
  exact ⟨hQi.add hRi,
    integrable_square_add b hb hQi (integrable_sq_of_hasLaw hQ) hRm hR,
    integrable_abs_cube_add b hb hQ.aemeasurable.aestronglyMeasurable
      (integrable_abs_pow_of_hasLaw hQ 3) hRm hR⟩

theorem conditional_moment_bounds
    (hQ : HasLaw Q (gaussianReal 0 v) P)
    (hleQ : mQ ≤ mΩ) (hleH : mH ≤ mΩ)
    (hmQ : StronglyMeasurable[mQ] Q) (hind : Indep mQ mH P)
    (hRm : AEStronglyMeasurable[mΩ] R P) (b : ℝ) (hb : 0 ≤ b)
    (hR : ∀ᵐ ω ∂P, |R ω| ≤ b) :
    ∀ᵐ ω ∂P,
      |P[(fun ω => (Q ω + R ω) ^ 2) | mH] ω - (v : ℝ)| ≤
        2 * b * Real.sqrt v + b ^ 2 ∧
      P[(fun ω => |Q ω + R ω| ^ 3) | mH] ω ≤
        4 * (standardThirdAbsMoment * (v : ℝ) * Real.sqrt v + b ^ 3) := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  obtain ⟨_, hQ₂, hQ₁, hQ₃⟩ := conditional_gaussian_moments hQ hleQ hleH hmQ hind
  obtain ⟨_, hD₂, hD₃⟩ := integrable_moments hQ hRm b hb hR
  have hs := condExp_square_perturbation hleH b hb
    (integrable_of_hasLaw hQ) (integrable_sq_of_hasLaw hQ) hD₂ hR
  have hc := condExp_abs_cube_perturbation hleH b hb
    (integrable_abs_pow_of_hasLaw hQ 3) hD₃ hR
  filter_upwards [hQ₂, hQ₁, hQ₃, hs, hc] with ω h₂ h₁ h₃ hsω hcω
  constructor
  · rw [h₂] at hsω
    have hmul := mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ 2 * b)
    linarith
  · simpa only [h₃] using hcω

theorem integral_moment_bounds
    (hQ : HasLaw Q (gaussianReal 0 v) P)
    (hRm : AEStronglyMeasurable[mΩ] R P) (b : ℝ) (hb : 0 ≤ b)
    (hR : ∀ᵐ ω ∂P, |R ω| ≤ b) :
    |(∫ ω, (Q ω + R ω) ^ 2 ∂P) - (v : ℝ)| ≤
      2 * b * Real.sqrt v + b ^ 2 ∧
    (∫ ω, |Q ω + R ω| ^ 3 ∂P) ≤
      4 * (standardThirdAbsMoment * (v : ℝ) * Real.sqrt v + b ^ 3) := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  constructor
  · have h := integral_square_perturbation b hb
      (integrable_of_hasLaw hQ) (integrable_sq_of_hasLaw hQ) hRm hR
    rw [integral_sq_of_hasLaw hQ] at h
    have hmul := mul_le_mul_of_nonneg_left (integral_abs_le_of_hasLaw hQ)
      (by positivity : 0 ≤ 2 * b)
    linarith
  · have h := integral_abs_cube_perturbation b hb hQ.aemeasurable.aestronglyMeasurable
      (integrable_abs_pow_of_hasLaw hQ 3) hRm hR
    simpa only [integral_abs_cube_of_hasLaw hQ] using h

end Problem336AdditiveD139.GaussianPerturbation

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem336AdditiveD139.LocalInnovation

variable {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}

theorem conditional_characteristic_error_le_scale
    (hm : m ≤ mΩ) {D : Ω → ℝ} {L σ c₃ h : ℝ}
    (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hc : 0 ≤ c₃) (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hmean : μ[D | m] =ᵐ[μ] fun _ => 0)
    (hsecond : ∀ᵐ ω ∂μ,
      |μ[fun a => D a ^ 2 | m] ω - h * σ ^ 2|
        ≤ 2 * (L * h) * (σ * Real.sqrt h) + (L * h) ^ 2)
    (hthird : ∀ᵐ ω ∂μ,
      μ[fun a => |D a| ^ 3 | m] ω
        ≤ 4 * (c₃ * σ ^ 3 * h * Real.sqrt h + (L * h) ^ 3)) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I * (D a : ℂ)) | m] ω -
          (Real.exp (-(h * σ ^ 2) / 2) : ℂ)‖ ≤
        InnovationErrorScale.errorConstant L σ c₃ * h * Real.sqrt h := by
  have hTaylor := CharacteristicTaylor.conditional_characteristic_bound
    hm hD hD2 hD3 hmean (mul_nonneg h0 (sq_nonneg σ))
  filter_upwards [hTaylor, hsecond, hthird] with ω ht hs hcub
  apply InnovationErrorScale.local_error_le_scale hL hσ hc h0 h1 _ hs hcub
  linarith

theorem conditional_characteristic_error_le_variance_scale
    (hm : m ≤ mΩ) {D : Ω → ℝ} {L V c₃ h : ℝ}
    (hL : 0 ≤ L) (hV : 0 ≤ V) (hc : 0 ≤ c₃) (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hmean : μ[D | m] =ᵐ[μ] fun _ => 0)
    (hsecond : ∀ᵐ ω ∂μ,
      |μ[fun a => D a ^ 2 | m] ω - h * V|
        ≤ 2 * (L * h) * Real.sqrt (h * V) + (L * h) ^ 2)
    (hthird : ∀ᵐ ω ∂μ,
      μ[fun a => |D a| ^ 3 | m] ω
        ≤ 4 * (c₃ * (h * V) * Real.sqrt (h * V) + (L * h) ^ 3)) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I * (D a : ℂ)) | m] ω -
          (Real.exp (-(h * V) / 2) : ℂ)‖ ≤
        InnovationErrorScale.errorConstant L (Real.sqrt V) c₃ * h * Real.sqrt h := by
  have hsqrt : Real.sqrt (h * V) = Real.sqrt V * Real.sqrt h := by
    rw [Real.sqrt_mul h0]
    ring
  have hcube : c₃ * Real.sqrt V ^ 3 * h * Real.sqrt h =
      c₃ * (h * V) * Real.sqrt (h * V) := by
    rw [hsqrt, pow_succ, Real.sq_sqrt hV]
    ring
  have hs : ∀ᵐ ω ∂μ,
      |μ[fun a => D a ^ 2 | m] ω - h * Real.sqrt V ^ 2|
        ≤ 2 * (L * h) * (Real.sqrt V * Real.sqrt h) + (L * h) ^ 2 := by
    simpa only [Real.sq_sqrt hV, hsqrt] using hsecond
  have ht : ∀ᵐ ω ∂μ,
      μ[fun a => |D a| ^ 3 | m] ω
        ≤ 4 * (c₃ * Real.sqrt V ^ 3 * h * Real.sqrt h + (L * h) ^ 3) := by
    simpa only [hcube] using hthird
  simpa only [Real.sq_sqrt hV] using
    conditional_characteristic_error_le_scale hm hL (Real.sqrt_nonneg V) hc h0 h1
      hD hD2 hD3 hmean hs ht

theorem gaussian_perturbation_characteristic_error
    {mQ : MeasurableSpace Ω} {Q R : Ω → ℝ} {h V : ℝ≥0} {L : ℝ}
    (hleQ : mQ ≤ mΩ) (hm : m ≤ mΩ)
    (hQ : HasLaw Q (gaussianReal 0 (h * V)) μ)
    (hmQ : StronglyMeasurable[mQ] Q) (hind : Indep mQ m μ)
    (hRm : AEStronglyMeasurable[mΩ] R μ)
    (hL : 0 ≤ L) (h1 : (h : ℝ) ≤ 1)
    (hR : ∀ᵐ ω ∂μ, |R ω| ≤ L * (h : ℝ))
    (hmean : μ[(fun ω => Q ω + R ω) | m] =ᵐ[μ] fun _ => 0) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I * ((Q a + R a : ℝ) : ℂ)) | m] ω -
          (Real.exp (-((h : ℝ) * (V : ℝ)) / 2) : ℂ)‖ ≤
        InnovationErrorScale.errorConstant L (Real.sqrt V)
          GaussianMomentBounds.standardThirdAbsMoment * (h : ℝ) * Real.sqrt h := by
  have hb : 0 ≤ L * (h : ℝ) := mul_nonneg hL h.coe_nonneg
  obtain ⟨hD, hD2, hD3⟩ := GaussianPerturbation.integrable_moments hQ hRm _ hb hR
  have hbounds := GaussianPerturbation.conditional_moment_bounds
    hQ hleQ hm hmQ hind hRm _ hb hR
  apply conditional_characteristic_error_le_variance_scale hm hL V.coe_nonneg
    GaussianMomentBounds.standardThirdAbsMoment_nonneg h.coe_nonneg h1
    hD hD2 hD3 hmean
  · filter_upwards [hbounds] with ω hω
    simpa only [NNReal.coe_mul] using hω.1
  · filter_upwards [hbounds] with ω hω
    simpa only [NNReal.coe_mul] using hω.2

end Problem336AdditiveD139.LocalInnovation

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Problem336AdditiveD139.InnovationCorrection

def correction (x : ℝ) (b : ℝ → ℝ) (u v : ℝ) : ℝ :=
  (v - u) * x - ∫ s in u..v, b s

theorem integral_mem_unitInterval_scaled {b : ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v) (hb : ∀ s ∈ Icc u v, b s ∈ Icc (0 : ℝ) 1) :
    (∫ s in u..v, b s) ∈ Icc (0 : ℝ) (v - u) := by
  constructor
  · exact intervalIntegral.integral_nonneg huv (fun s hs => (hb s hs).1)
  · have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := u) (b := v) (C := (1 : ℝ)) (f := b) (by
        intro s hs
        rw [uIoc_of_le huv] at hs
        have h := hb s (Ioc_subset_Icc_self hs)
        simpa [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2)
    have hnonneg := intervalIntegral.integral_nonneg (μ := volume) huv (fun s hs => (hb s hs).1)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg (sub_nonneg.mpr huv)] using hnorm

theorem abs_correction_le {x : ℝ} {b : ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v) (hx : x ∈ Icc (0 : ℝ) 1)
    (hb : ∀ s ∈ Icc u v, b s ∈ Icc (0 : ℝ) 1) :
    |correction x b u v| ≤ v - u := by
  have hi := integral_mem_unitInterval_scaled huv hb
  have h0 : 0 ≤ (v - u) * x := mul_nonneg (sub_nonneg.mpr huv) hx.1
  have h1 : (v - u) * x ≤ v - u := by
    simpa using mul_le_mul_of_nonneg_left hx.2 (sub_nonneg.mpr huv)
  rw [correction, abs_le]
  constructor <;> linarith [hi.1, hi.2]

theorem correction_eq_integral {x : ℝ} {b : ℝ → ℝ} {u v : ℝ}
    (hb : IntervalIntegrable b volume u v) :
    correction x b u v = ∫ s in u..v, x - b s := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const hb]
  simp [correction]

theorem abs_sum_correction_le {I : Type u_1} (S : Finset I) (θ x : I → ℝ)
    (b : I → ℝ → ℝ) {u v : ℝ} (huv : u ≤ v)
    (hx : ∀ i ∈ S, x i ∈ Icc (0 : ℝ) 1)
    (hb : ∀ i ∈ S, ∀ s ∈ Icc u v, b i s ∈ Icc (0 : ℝ) 1) :
    |∑ i ∈ S, θ i * correction (x i) (b i) u v| ≤
      (v - u) * ∑ i ∈ S, |θ i| := by
  calc
    |∑ i ∈ S, θ i * correction (x i) (b i) u v| ≤
        ∑ i ∈ S, |θ i * correction (x i) (b i) u v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, |θ i| * (v - u) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_correction_le huv (hx i hi) (hb i hi)) (abs_nonneg _)
    _ = (v - u) * ∑ i ∈ S, |θ i| := by
      rw [← Finset.sum_mul, mul_comm]

def innovation (x : ℝ) (B b : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * x + B t - ∫ s in 0..t, b s

theorem innovation_sub_eq {x : ℝ} {B b : ℝ → ℝ} {u v : ℝ}
    (hbu : IntervalIntegrable b volume 0 u)
    (hbuv : IntervalIntegrable b volume u v) :
    innovation x B b v - innovation x B b u =
      (B v - B u) + correction x b u v := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals hbu hbuv
  simp only [innovation, correction]
  rw [← hadd]
  ring

theorem sum_innovation_sub_eq {I : Type u_2} (S : Finset I) (θ x : I → ℝ)
    (B b : I → ℝ → ℝ) {u v : ℝ}
    (hbu : ∀ i ∈ S, IntervalIntegrable (b i) volume 0 u)
    (hbuv : ∀ i ∈ S, IntervalIntegrable (b i) volume u v) :
    (∑ i ∈ S, θ i * (innovation (x i) (B i) (b i) v -
      innovation (x i) (B i) (b i) u)) =
    (∑ i ∈ S, θ i * (B i v - B i u)) +
      ∑ i ∈ S, θ i * correction (x i) (b i) u v := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [innovation_sub_eq (hbu i hi) (hbuv i hi), mul_add]

theorem intervalIntegrable_of_measurable_unitInterval {b : ℝ → ℝ}
    (hbm : Measurable b) (hb : ∀ s, b s ∈ Icc (0 : ℝ) 1) (u v : ℝ) :
    IntervalIntegrable b volume u v := by
  rw [intervalIntegrable_iff, uIoc]
  exact (integrable_const (1 : ℝ)).mono' hbm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hb s).1] using (hb s).2)

section RandomVariables

variable {Ω : Type u_3} [MeasurableSpace Ω]

theorem measurable_intervalIntegral {b : Ω → ℝ → ℝ}
    (hb : Measurable (Function.uncurry b)) (u v : ℝ) :
    Measurable (fun ω => ∫ s in u..v, b ω s) := by
  unfold intervalIntegral
  exact (hb.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Ioc u v))).measurable.sub
    (hb.stronglyMeasurable.integral_prod_right
      (ν := volume.restrict (Ioc v u))).measurable

theorem measurable_correction {x : Ω → ℝ} {b : Ω → ℝ → ℝ}
    (hx : Measurable x) (hb : Measurable (Function.uncurry b)) (u v : ℝ) :
    Measurable (fun ω => correction (x ω) (b ω) u v) :=
  (measurable_const.mul hx).sub (measurable_intervalIntegral hb u v)

theorem integrable_correction_pow (μ : Measure Ω) [IsFiniteMeasure μ]
    {x : Ω → ℝ} {b : Ω → ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v) (hxm : Measurable x) (hbm : Measurable (Function.uncurry b))
    (hx : ∀ ω, x ω ∈ Icc (0 : ℝ) 1)
    (hb : ∀ ω, ∀ s ∈ Icc u v, b ω s ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    Integrable (fun ω => correction (x ω) (b ω) u v ^ n) μ := by
  apply (integrable_const ((v - u) ^ n)).mono'
    ((measurable_correction hxm hbm u v).pow_const n).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_correction_le huv (hx ω) (hb ω)) n

theorem integrable_abs_correction_pow (μ : Measure Ω) [IsFiniteMeasure μ]
    {x : Ω → ℝ} {b : Ω → ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v) (hxm : Measurable x) (hbm : Measurable (Function.uncurry b))
    (hx : ∀ ω, x ω ∈ Icc (0 : ℝ) 1)
    (hb : ∀ ω, ∀ s ∈ Icc u v, b ω s ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    Integrable (fun ω => |correction (x ω) (b ω) u v| ^ n) μ := by
  simpa only [abs_pow] using (integrable_correction_pow μ huv hxm hbm hx hb n).abs

theorem measurable_sum_correction {I : Type u_4} (S : Finset I) (θ : I → ℝ)
    {x : I → Ω → ℝ} {b : I → Ω → ℝ → ℝ}
    (hx : ∀ i ∈ S, Measurable (x i))
    (hb : ∀ i ∈ S, Measurable (Function.uncurry (b i))) (u v : ℝ) :
    Measurable (fun ω => ∑ i ∈ S, θ i * correction (x i ω) (b i ω) u v) := by
  exact S.measurable_sum (fun i hi => measurable_const.mul
    (measurable_correction (hx i hi) (hb i hi) u v))

theorem integrable_sum_correction_pow (μ : Measure Ω) [IsFiniteMeasure μ]
    {I : Type u_5} (S : Finset I) (θ : I → ℝ)
    {x : I → Ω → ℝ} {b : I → Ω → ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v) (hxm : ∀ i ∈ S, Measurable (x i))
    (hbm : ∀ i ∈ S, Measurable (Function.uncurry (b i)))
    (hx : ∀ i ∈ S, ∀ ω, x i ω ∈ Icc (0 : ℝ) 1)
    (hb : ∀ i ∈ S, ∀ ω, ∀ s ∈ Icc u v, b i ω s ∈ Icc (0 : ℝ) 1)
    (n : ℕ) :
    Integrable (fun ω => (∑ i ∈ S, θ i * correction (x i ω) (b i ω) u v) ^ n) μ := by
  apply (integrable_const (((v - u) * ∑ i ∈ S, |θ i|) ^ n)).mono'
    ((measurable_sum_correction S θ hxm hbm u v).pow_const n).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_sum_correction_le S θ (fun i => x i ω) (fun i => b i ω) huv
      (fun i hi => hx i hi ω) (fun i hi => hb i hi ω)) n

end RandomVariables

end Problem336AdditiveD139.InnovationCorrection

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Problem336AdditiveD139.InnovationMean

variable {T : Type u_1} {Ω : Type u_2} [MeasurableSpace T] {m n : MeasurableSpace Ω}
  [mΩ : MeasurableSpace Ω]
  {ν : Measure T} {μ : Measure Ω} [IsFiniteMeasure ν] [IsFiniteMeasure μ]

theorem condExp_integral_of_posteriors
    (hm : m ≤ mΩ)
    (H : T → MeasurableSpace Ω) (hH : ∀ t, H t ≤ mΩ)
    (hmH : ∀ᵐ t ∂ν, m ≤ H t)
    {X : Ω → ℝ} (hX : Integrable X μ)
    {b : T → Ω → ℝ}
    (hb : Integrable (Function.uncurry b) (ν.prod μ))
    (hpost : ∀ᵐ t ∂ν, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => ∫ t, b t ω ∂ν | m] =ᵐ[μ]
      fun ω => ν.real Set.univ * μ[X | m] ω := by
  have hint : Integrable (fun ω => ∫ t, b t ω ∂ν) μ :=
    hb.integral_prod_right
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hint
    (fun s _ _ => (integrable_condExp.const_mul _).integrableOn) ?_
    (stronglyMeasurable_condExp.const_mul _).aestronglyMeasurable
  intro s hs _
  have hbs : Integrable (Function.uncurry b) (ν.prod (μ.restrict s)) := by
    simpa only [← Measure.prod_restrict, Measure.restrict_univ] using
      hb.restrict (s := Set.univ ×ˢ s)
  rw [integral_const_mul, setIntegral_condExp hm hX hs]
  rw [← integral_integral_swap hbs]
  have heq : (fun t => ∫ ω in s, b t ω ∂μ) =ᵐ[ν]
      fun _ => ∫ ω in s, X ω ∂μ := by
    filter_upwards [hmH, hpost] with t hmt hpt
    calc
      (∫ ω in s, b t ω ∂μ) = ∫ ω in s, μ[X | H t] ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hpt)
      _ = ∫ ω in s, X ω ∂μ := setIntegral_condExp (hH t) hX (hmt s hs)
  rw [integral_congr_ae heq, integral_const]
  rfl

theorem condExp_intervalIntegral_of_posteriors
    (H : Filtration ℝ mΩ) {u v : ℝ} (huv : u ≤ v)
    {X : Ω → ℝ} (hX : Integrable X μ)
    {b : ℝ → Ω → ℝ}
    (hb : Integrable (Function.uncurry b)
      ((volume.restrict (Set.Ioc u v)).prod μ))
    (hpost : ∀ t ∈ Set.Ioc u v, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => ∫ t in u..v, b t ω | H u] =ᵐ[μ]
      fun ω => (v - u) * μ[X | H u] ω := by
  have hle : ∀ᵐ t ∂volume.restrict (Set.Ioc u v), H u ≤ H t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact H.mono ht.1.le
  have hp : ∀ᵐ t ∂volume.restrict (Set.Ioc u v), b t =ᵐ[μ] μ[X | H t] := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hpost t ht
  have h := condExp_integral_of_posteriors (H.le u) H H.le hle hX hb hp
  simpa only [intervalIntegral.integral_of_le huv, measureReal_def,
    Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr huv)] using h

theorem integrable_bounded_drift
    {u v C : ℝ} {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b))
    (hbound : ∀ t ω, |b t ω| ≤ C) :
    Integrable (Function.uncurry b)
      ((volume.restrict (Set.Ioc u v)).prod μ) := by
  exact Integrable.of_bound hb.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs, Function.uncurry] using hbound p.1 p.2))

theorem condExp_innovation_increment_eq_zero
    (H : Filtration ℝ mΩ) {u v : ℝ} (huv : u ≤ v)
    {X Q : Ω → ℝ} (hX : Integrable X μ) (hQ : Integrable Q μ)
    (hQmean : μ[Q | H u] =ᵐ[μ] 0)
    {b : ℝ → Ω → ℝ}
    (hb : Integrable (Function.uncurry b)
      ((volume.restrict (Set.Ioc u v)).prod μ))
    (hpost : ∀ t ∈ Set.Ioc u v, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => (v - u) * X ω + Q ω - ∫ t in u..v, b t ω | H u] =ᵐ[μ] 0 := by
  have hi : Integrable (fun ω => ∫ t in u..v, b t ω) μ := by
    simpa only [intervalIntegral.integral_of_le huv, Function.uncurry] using hb.integral_prod_right
  have hci := condExp_intervalIntegral_of_posteriors H huv hX hb hpost
  have hsub := condExp_sub ((hX.const_mul (v - u)).add hQ) hi (H u)
  have hadd := condExp_add (hX.const_mul (v - u)) hQ (H u)
  have hmul := condExp_smul (μ := μ) (v - u) X (H u)
  filter_upwards [hsub, hadd, hmul, hQmean, hci] with ω hs ha hm hq hc
  change μ[fun ω => (v - u) * X ω + Q ω - ∫ t in u..v, b t ω | H u] ω = 0
  change μ[fun ω => (v - u) * X ω + Q ω - ∫ t in u..v, b t ω | H u] ω =
    μ[fun ω => (v - u) * X ω + Q ω | H u] ω -
      μ[fun ω => ∫ t in u..v, b t ω | H u] ω at hs
  change μ[fun ω => (v - u) * X ω + Q ω | H u] ω =
    μ[fun ω => (v - u) * X ω | H u] ω + μ[Q | H u] ω at ha
  change μ[fun ω => (v - u) * X ω | H u] ω = (v - u) * μ[X | H u] ω at hm
  change μ[Q | H u] ω = 0 at hq
  rw [hs, ha, hm, hq, hc]
  ring

theorem condExp_innovation_increment_eq_zero_of_indep
    (H : Filtration ℝ mΩ) {u v : ℝ} (huv : u ≤ v)
    {X Q : Ω → ℝ} (hX : Integrable X μ) (hQ : Integrable Q μ)
    (hn : n ≤ mΩ) (hQn : StronglyMeasurable[n] Q)
    (hindep : ProbabilityTheory.Indep n (H u) μ)
    (hQmean : ∫ ω, Q ω ∂μ = 0)
    {b : ℝ → Ω → ℝ}
    (hb : Integrable (Function.uncurry b)
      ((volume.restrict (Set.Ioc u v)).prod μ))
    (hpost : ∀ t ∈ Set.Ioc u v, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => (v - u) * X ω + Q ω - ∫ t in u..v, b t ω | H u] =ᵐ[μ] 0 := by
  apply condExp_innovation_increment_eq_zero H huv hX hQ _ hb hpost
  change μ[Q | H u] =ᵐ[μ] fun _ => (0 : ℝ)
  simpa only [hQmean] using condExp_indep_eq hn (H.le u) hQn hindep

theorem bounded_innovation_condExp_eq_zero
    (H : Filtration ℝ mΩ) {u v C : ℝ} (huv : u ≤ v)
    {X Q : Ω → ℝ} (hX : Integrable X μ) (hQ : Integrable Q μ)
    (hQmean : μ[Q | H u] =ᵐ[μ] 0)
    {b : ℝ → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    (hbound : ∀ t ω, |b t ω| ≤ C)
    (hpost : ∀ t ∈ Set.Ioc u v, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => (v - u) * X ω + Q ω - ∫ t in u..v, b t ω | H u] =ᵐ[μ] 0 :=
  condExp_innovation_increment_eq_zero H huv hX hQ hQmean
    (integrable_bounded_drift hb hbound) hpost

theorem condExp_intervalIntegral_nnreal_of_posteriors
    (H : Filtration ℝ≥0 mΩ) {u v : ℝ≥0} (huv : u ≤ v)
    {X : Ω → ℝ} (hX : Integrable X μ)
    {b : ℝ≥0 → Ω → ℝ}
    (hb : Integrable (fun p : ℝ × Ω => b p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (u : ℝ) (v : ℝ))).prod μ))
    (hpost : ∀ t : ℝ≥0, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => ∫ t in (u : ℝ)..(v : ℝ), b t.toNNReal ω | H u] =ᵐ[μ]
      fun ω => ((v : ℝ) - (u : ℝ)) * μ[X | H u] ω := by
  have hle : ∀ᵐ t ∂volume.restrict (Set.Ioc (u : ℝ) (v : ℝ)),
      H u ≤ H t.toNNReal := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply H.mono
    exact_mod_cast (ht.1.le.trans (Real.le_coe_toNNReal t))
  have hp : ∀ᵐ t ∂volume.restrict (Set.Ioc (u : ℝ) (v : ℝ)),
      b t.toNNReal =ᵐ[μ] μ[X | H t.toNNReal] :=
    Filter.Eventually.of_forall (fun t => hpost t.toNNReal)
  have h := condExp_integral_of_posteriors (H.le u)
    (fun t : ℝ => H t.toNNReal) (fun t => H.le t.toNNReal) hle hX
    (b := fun t ω => b t.toNNReal ω) (by
      change Integrable (fun p : ℝ × Ω => b p.1.toNNReal p.2) _
      exact hb) hp
  have huv' : (u : ℝ) ≤ (v : ℝ) := huv
  simpa only [intervalIntegral.integral_of_le huv', measureReal_def,
    Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr huv')] using h

theorem condExp_innovation_increment_nnreal_eq_zero
    (H : Filtration ℝ≥0 mΩ) {u v : ℝ≥0} (huv : u ≤ v)
    {X Q : Ω → ℝ} (hX : Integrable X μ) (hQ : Integrable Q μ)
    (hQmean : μ[Q | H u] =ᵐ[μ] 0)
    {b : ℝ≥0 → Ω → ℝ}
    (hb : Integrable (fun p : ℝ × Ω => b p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (u : ℝ) (v : ℝ))).prod μ))
    (hpost : ∀ t : ℝ≥0, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => ((v : ℝ) - (u : ℝ)) * X ω + Q ω -
      ∫ t in (u : ℝ)..(v : ℝ), b t.toNNReal ω | H u] =ᵐ[μ] 0 := by
  have hi : Integrable (fun ω => ∫ t in (u : ℝ)..(v : ℝ), b t.toNNReal ω) μ := by
    simpa only [intervalIntegral.integral_of_le (show (u : ℝ) ≤ (v : ℝ) from huv)]
      using hb.integral_prod_right
  have hci := condExp_intervalIntegral_nnreal_of_posteriors H huv hX hb hpost
  have hsub := condExp_sub ((hX.const_mul ((v : ℝ) - u)).add hQ) hi (H u)
  have hadd := condExp_add (hX.const_mul ((v : ℝ) - u)) hQ (H u)
  have hmul := condExp_smul (μ := μ) ((v : ℝ) - u) X (H u)
  filter_upwards [hsub, hadd, hmul, hQmean, hci] with ω hs ha hm hq hc
  change μ[(fun ω => ((v : ℝ) - u) * X ω) + Q -
    (fun ω => ∫ t in (u : ℝ)..(v : ℝ), b t.toNNReal ω) | H u] ω = 0
  dsimp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    at hs ha hm hq
  change μ[fun ω => ((v : ℝ) - u) * X ω | H u] ω =
    ((v : ℝ) - u) * μ[X | H u] ω at hm
  rw [hs, ha, hm, hq, hc]
  ring

theorem bounded_innovation_condExp_nnreal_eq_zero
    (H : Filtration ℝ≥0 mΩ) {u v : ℝ≥0} (huv : u ≤ v)
    {X Q : Ω → ℝ} (hX : Integrable X μ) (hQ : Integrable Q μ)
    (hQmean : μ[Q | H u] =ᵐ[μ] 0)
    {b : ℝ≥0 → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    {C : ℝ} (hbound : ∀ t ω, |b t ω| ≤ C)
    (hpost : ∀ t : ℝ≥0, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => ((v : ℝ) - (u : ℝ)) * X ω + Q ω -
      ∫ t in (u : ℝ)..(v : ℝ), b t.toNNReal ω | H u] =ᵐ[μ] 0 := by
  apply condExp_innovation_increment_nnreal_eq_zero H huv hX hQ hQmean _ hpost
  have hb' : Measurable (Function.uncurry (fun (t : ℝ) ω => b t.toNNReal ω)) :=
    hb.comp (show Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) by fun_prop)
  exact integrable_bounded_drift hb' (fun t ω => hbound t.toNNReal ω)

end Problem336AdditiveD139.InnovationMean

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal

namespace Problem336AdditiveD139.WeightedLocalInnovation

variable {I : Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

def signal (S : Finset I) (θ : I → ℝ) (X : I → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ S, θ i * X i ω

def drift (S : Finset I) (θ : I → ℝ) (b : I → Ω → ℝ → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ S, θ i * b i ω t

def correction (S : Finset I) (θ : I → ℝ) (X : I → Ω → ℝ)
    (b : I → Ω → ℝ → ℝ) (u v : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ S, θ i * InnovationCorrection.correction (X i ω) (b i ω) u v

theorem posterior_sum (S : Finset I) (θ : I → ℝ) {m : MeasurableSpace Ω}
    {X B : I → Ω → ℝ} (hX : ∀ i ∈ S, Integrable (X i) μ)
    (hB : ∀ i ∈ S, B i =ᵐ[μ] μ[X i | m]) :
    signal S θ B =ᵐ[μ] μ[signal S θ X | m] := by
  have hsum := condExp_finsetSum (μ := μ) (s := S)
    (f := fun i => θ i • X i) (fun i hi => (hX i hi).smul (θ i)) m
  have hscale : ∀ᵐ ω ∂μ, ∀ i ∈ S,
      μ[(θ i • X i) | m] ω = θ i * μ[X i | m] ω := by
    apply (S.eventually_all).mpr
    intro i hi
    filter_upwards [condExp_smul (μ := μ) (θ i) (X i) m] with ω hω
    exact hω
  have hf : (∑ i ∈ S, θ i • X i) = (fun ω => ∑ i ∈ S, θ i * X i ω) := by
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf] at hsum
  filter_upwards [hsum, hscale, (S.eventually_all).mpr hB] with ω hs hc hb
  simp only [Finset.sum_apply] at hs
  change (∑ i ∈ S, θ i * B i ω) = μ[(fun ω => ∑ i ∈ S, θ i * X i ω) | m] ω
  change μ[(fun ω => ∑ i ∈ S, θ i * X i ω) | m] ω =
    ∑ i ∈ S, μ[(θ i • X i) | m] ω at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc i hi, hb i hi]

theorem correction_eq (S : Finset I) (θ : I → ℝ) (X : I → Ω → ℝ)
    (b : I → Ω → ℝ → ℝ) (u v : ℝ)
    (hb : ∀ i ∈ S, ∀ ω, IntervalIntegrable (b i ω) volume u v) (ω : Ω) :
    correction S θ X b u v ω =
      (v - u) * signal S θ X ω - ∫ t in u..v, drift S θ b t ω := by
  unfold correction signal drift InnovationCorrection.correction
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hb i hi ω).const_mul (θ i))]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem measurable_drift (S : Finset I) (θ : I → ℝ)
    {b : I → Ω → ℝ → ℝ}
    (hb : ∀ i ∈ S, Measurable (Function.uncurry (b i))) :
    Measurable (Function.uncurry (drift S θ b)) := by
  exact S.measurable_sum (fun i hi =>
    measurable_const.mul ((hb i hi).comp measurable_swap))

theorem abs_drift_le (S : Finset I) (θ : I → ℝ)
    {b : I → Ω → ℝ → ℝ}
    (hb : ∀ i ∈ S, ∀ ω t, b i ω t ∈ Icc (0 : ℝ) 1) (t : ℝ) (ω : Ω) :
    |drift S θ b t ω| ≤ ∑ i ∈ S, |θ i| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul, abs_of_nonneg (hb i hi ω t).1]
  simpa using mul_le_mul_of_nonneg_left (hb i hi ω t).2 (abs_nonneg (θ i))

theorem intervalIntegrable_drift_coordinates (S : Finset I)
    {b : I → Ω → ℝ → ℝ}
    (hbm : ∀ i ∈ S, Measurable (Function.uncurry (b i)))
    (hb : ∀ i ∈ S, ∀ ω t, b i ω t ∈ Icc (0 : ℝ) 1)
    (u v : ℝ) :
    ∀ i ∈ S, ∀ ω, IntervalIntegrable (b i ω) volume u v := by
  intro i hi ω
  exact InnovationCorrection.intervalIntegrable_of_measurable_unitInterval
    ((hbm i hi).comp (measurable_const.prodMk measurable_id)) (hb i hi ω) u v

theorem correction_condExp_zero [IsFiniteMeasure μ]
    (S : Finset I) (θ : I → ℝ) (H : Filtration ℝ mΩ)
    {X : I → Ω → ℝ} {b : I → Ω → ℝ → ℝ} {Q : Ω → ℝ} {u v : ℝ}
    (huv : u ≤ v)
    (hX : ∀ i ∈ S, Integrable (X i) μ)
    (hbm : ∀ i ∈ S, Measurable (Function.uncurry (b i)))
    (hb : ∀ i ∈ S, ∀ ω t, b i ω t ∈ Icc (0 : ℝ) 1)
    (hQ : Integrable Q μ) (hQmean : μ[Q | H u] =ᵐ[μ] 0)
    (hpost : ∀ t ∈ Ioc u v, ∀ i ∈ S,
      (fun ω => b i ω t) =ᵐ[μ] μ[X i | H t]) :
    μ[(fun ω => Q ω + correction S θ X b u v ω) | H u] =ᵐ[μ] 0 := by
  have hXi : Integrable (signal S θ X) μ :=
    integrable_finsetSum S (fun i hi => (hX i hi).const_mul (θ i))
  have hmean := InnovationMean.bounded_innovation_condExp_eq_zero H huv hXi hQ hQmean
    (measurable_drift S θ hbm) (abs_drift_le S θ hb) (fun t ht =>
      posterior_sum S θ hX (hpost t ht))
  have heq : (fun ω => Q ω + correction S θ X b u v ω) =
      (fun ω => (v - u) * signal S θ X ω + Q ω - ∫ t in u..v, drift S θ b t ω) := by
    funext ω
    rw [correction_eq S θ X b u v (intervalIntegrable_drift_coordinates S hbm hb u v)]
    ring
  rw [heq]
  exact hmean

def amplitude (S : Finset I) (θ : I → ℝ) : ℝ := ∑ i ∈ S, |θ i|

def variance (S : Finset I) (θ : I → ℝ) : ℝ≥0 :=
  ⟨∑ i ∈ S, θ i ^ 2, Finset.sum_nonneg (fun i _ => sq_nonneg (θ i))⟩

def errorConstant (S : Finset I) (θ : I → ℝ) : ℝ :=
  InnovationErrorScale.errorConstant (amplitude S θ) (Real.sqrt (variance S θ))
    GaussianMomentBounds.standardThirdAbsMoment

theorem amplitude_nonneg (S : Finset I) (θ : I → ℝ) : 0 ≤ amplitude S θ :=
  Finset.sum_nonneg (fun i _ => abs_nonneg (θ i))

theorem errorConstant_nonneg (S : Finset I) (θ : I → ℝ) : 0 ≤ errorConstant S θ :=
  InnovationErrorScale.errorConstant_nonneg (amplitude_nonneg S θ) (Real.sqrt_nonneg _)
    GaussianMomentBounds.standardThirdAbsMoment_nonneg

theorem corrected_gaussian_characteristic_error [IsProbabilityMeasure μ]
    (S : Finset I) (θ : I → ℝ) (H : Filtration ℝ mΩ) (u : ℝ) (h : ℝ≥0)
    (h1 : (h : ℝ) ≤ 1) {mQ : MeasurableSpace Ω}
    {X : I → Ω → ℝ} {b : I → Ω → ℝ → ℝ} {Q : Ω → ℝ}
    (hxm : ∀ i ∈ S, Measurable[mΩ] (X i))
    (hx : ∀ i ∈ S, ∀ ω, X i ω ∈ Icc (0 : ℝ) 1)
    (hbm : ∀ i ∈ S, Measurable[mΩ.prod (borel ℝ)] (Function.uncurry (b i)))
    (hb : ∀ i ∈ S, ∀ ω t, b i ω t ∈ Icc (0 : ℝ) 1)
    (hleQ : mQ ≤ mΩ) (hmQ : StronglyMeasurable[mQ] Q)
    (hQ : HasLaw Q (gaussianReal 0 (h * variance S θ)) μ)
    (hind : Indep mQ (H u) μ)
    (hpost : ∀ t ∈ Ioc u (u + (h : ℝ)), ∀ i ∈ S,
      (fun ω => b i ω t) =ᵐ[μ] μ[X i | H t]) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I *
          ((Q a + correction S θ X b u (u + (h : ℝ)) a : ℝ) : ℂ)) | H u] ω -
          (Real.exp (-((h : ℝ) * (variance S θ : ℝ)) / 2) : ℂ)‖ ≤
        errorConstant S θ * (h : ℝ) * Real.sqrt h := by
  let : MeasurableSpace Ω := mΩ
  have huv : u ≤ u + (h : ℝ) := le_add_of_nonneg_right h.coe_nonneg
  have hXi : ∀ i ∈ S, Integrable (X i) μ := by
    intro i hi
    apply Integrable.of_bound (μ := μ) (hxm i hi).aestronglyMeasurable 1
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hx i hi ω).1] using (hx i hi ω).2
  have hQmean : μ[Q | H u] =ᵐ[μ] 0 :=
    (GaussianMomentBounds.conditional_gaussian_moments hQ hleQ (H.le u) hmQ hind).1
  have hmean := correction_condExp_zero S θ H huv hXi hbm hb
    (GaussianMomentBounds.integrable_of_hasLaw hQ) hQmean hpost
  have hRm : AEStronglyMeasurable[mΩ]
      (correction S θ X b u (u + (h : ℝ))) μ :=
    (InnovationCorrection.measurable_sum_correction S θ hxm hbm u (u + (h : ℝ))).aestronglyMeasurable
  have hR : ∀ᵐ ω ∂μ, |correction S θ X b u (u + (h : ℝ)) ω| ≤ amplitude S θ * (h : ℝ) := by
    filter_upwards with ω
    have hbound := InnovationCorrection.abs_sum_correction_le S θ
      (fun i => X i ω) (fun i => b i ω) huv
      (fun i hi => hx i hi ω) (fun i hi t _ => hb i hi ω t)
    simpa only [correction, amplitude, add_sub_cancel_left, mul_comm] using hbound
  exact LocalInnovation.gaussian_perturbation_characteristic_error hleQ (H.le u)
    hQ hmQ hind hRm (amplitude_nonneg S θ) h1 hR hmean

def noiseIncrement (S : Finset I) (θ : I → ℝ) (B : I → Ω → ℝ → ℝ)
    (u v : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ S, θ i * (B i ω v - B i ω u)

def innovationIncrement (S : Finset I) (θ : I → ℝ) (X : I → Ω → ℝ)
    (B b : I → Ω → ℝ → ℝ) (u v : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ S, θ i *
    (InnovationCorrection.innovation (X i ω) (B i ω) (b i ω) v -
      InnovationCorrection.innovation (X i ω) (B i ω) (b i ω) u)

theorem innovationIncrement_eq (S : Finset I) (θ : I → ℝ)
    (X : I → Ω → ℝ) (B b : I → Ω → ℝ → ℝ) (u v : ℝ)
    (hbm : ∀ i ∈ S, Measurable (Function.uncurry (b i)))
    (hb : ∀ i ∈ S, ∀ ω t, b i ω t ∈ Icc (0 : ℝ) 1) :
    innovationIncrement S θ X B b u v =
      fun ω => noiseIncrement S θ B u v ω + correction S θ X b u v ω := by
  funext ω
  exact InnovationCorrection.sum_innovation_sub_eq S θ (fun i => X i ω)
    (fun i => B i ω) (fun i => b i ω)
    (fun i hi => intervalIntegrable_drift_coordinates S hbm hb 0 u i hi ω)
    (fun i hi => intervalIntegrable_drift_coordinates S hbm hb u v i hi ω)

theorem innovation_characteristic_error [IsProbabilityMeasure μ]
    (S : Finset I) (θ : I → ℝ) (H : Filtration ℝ mΩ) (u : ℝ) (h : ℝ≥0)
    (h1 : (h : ℝ) ≤ 1) {mQ : MeasurableSpace Ω}
    {X : I → Ω → ℝ} {B b : I → Ω → ℝ → ℝ}
    (hxm : ∀ i ∈ S, Measurable[mΩ] (X i))
    (hx : ∀ i ∈ S, ∀ ω, X i ω ∈ Icc (0 : ℝ) 1)
    (hbm : ∀ i ∈ S, Measurable[mΩ.prod (borel ℝ)] (Function.uncurry (b i)))
    (hb : ∀ i ∈ S, ∀ ω t, b i ω t ∈ Icc (0 : ℝ) 1)
    (hleQ : mQ ≤ mΩ)
    (hmQ : StronglyMeasurable[mQ] (noiseIncrement S θ B u (u + (h : ℝ))))
    (hQ : HasLaw (noiseIncrement S θ B u (u + (h : ℝ)))
      (gaussianReal 0 (h * variance S θ)) μ)
    (hind : Indep mQ (H u) μ)
    (hpost : ∀ t ∈ Ioc u (u + (h : ℝ)), ∀ i ∈ S,
      (fun ω => b i ω t) =ᵐ[μ] μ[X i | H t]) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I *
          (innovationIncrement S θ X B b u (u + (h : ℝ)) a : ℂ)) | H u] ω -
          (Real.exp (-((h : ℝ) * (variance S θ : ℝ)) / 2) : ℂ)‖ ≤
        errorConstant S θ * (h : ℝ) * Real.sqrt h := by
  let : MeasurableSpace Ω := mΩ
  rw [innovationIncrement_eq S θ X B b u (u + (h : ℝ)) hbm hb]
  exact corrected_gaussian_characteristic_error S θ H u h h1
    hxm hx hbm hb hleQ hmQ hQ hind hpost

end Problem336AdditiveD139.WeightedLocalInnovation

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Problem336AdditiveD139.NoisePast

variable {S : Type u_1} {N : Type u_2} {E : Type u_3} {H : Type u_4} {O : Type u_5}
  [MeasurableSpace S] [MeasurableSpace N] [MeasurableSpace E]
  [MeasurableSpace H] [MeasurableSpace O]
  {μ : Measure S} {P : Measure N}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

theorem indepFun_snd_signal_history {Q : N → E} {hist : N → H}
    (hQ : Measurable Q) (hhist : Measurable hist)
    (hind : IndepFun Q hist P) :
    IndepFun (fun ω : S × N => Q ω.2)
      (fun ω : S × N => (ω.1, hist ω.2)) (μ.prod P) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A C hA hC
  have hQA : MeasurableSet ((fun ω : S × N => Q ω.2) ⁻¹' A) :=
    hA.preimage (hQ.comp measurable_snd)
  have hHC : MeasurableSet ((fun ω : S × N => (ω.1, hist ω.2)) ⁻¹' C) :=
    hC.preimage (measurable_fst.prodMk (hhist.comp measurable_snd))
  rw [Measure.prod_apply (hQA.inter hHC), Measure.prod_apply hQA,
    Measure.prod_apply hHC]
  have hsec (x : S) : MeasurableSet (Prod.mk x ⁻¹' C) :=
    hC.preimage (measurable_const.prodMk measurable_id)
  have heq (x : S) :
      P (Prod.mk x ⁻¹' (((fun ω : S × N => Q ω.2) ⁻¹' A) ∩
        ((fun ω : S × N => (ω.1, hist ω.2)) ⁻¹' C))) =
        P (Q ⁻¹' A) * P (hist ⁻¹' (Prod.mk x ⁻¹' C)) := by
    exact hind.measure_inter_preimage_eq_mul A (Prod.mk x ⁻¹' C) hA (hsec x)
  simp_rw [heq]
  simp only [Set.preimage_preimage]
  change (∫⁻ x, P (Q ⁻¹' A) * P (hist ⁻¹' (Prod.mk x ⁻¹' C)) ∂μ) =
    (∫⁻ _ : S, P (Q ⁻¹' A) ∂μ) *
      ∫⁻ x, P (hist ⁻¹' (Prod.mk x ⁻¹' C)) ∂μ
  rw [lintegral_const_mul' _ _ (measure_ne_top _ _)]
  simp

theorem indepFun_snd_observation {Q : N → E} {hist : N → H}
    (hQ : Measurable Q) (hhist : Measurable hist)
    (hind : IndepFun Q hist P) (observe : S × H → O)
    (hobserve : Measurable observe) :
    IndepFun (fun ω : S × N => Q ω.2)
      (fun ω : S × N => observe (ω.1, hist ω.2)) (μ.prod P) := by
  exact (indepFun_snd_signal_history (μ := μ) hQ hhist hind).comp
    measurable_id hobserve

theorem condExp_snd_observation {Q : N → E} {hist : N → H}
    (hQ : Measurable Q) (hhist : Measurable hist)
    (hind : IndepFun Q hist P) (observe : S × H → O)
    (hobserve : Measurable observe) (f : E → ℝ) (hf : Measurable f) :
    (μ.prod P)[(fun ω : S × N => f (Q ω.2)) |
      (inferInstance : MeasurableSpace O).comap
        (fun ω : S × N => observe (ω.1, hist ω.2))] =ᵐ[μ.prod P]
      fun _ => ∫ ω, f (Q ω) ∂P := by
  have hnoise : Measurable (fun ω : S × N => f (Q ω.2)) :=
    hf.comp (hQ.comp measurable_snd)
  have hobs : Measurable (fun ω : S × N => observe (ω.1, hist ω.2)) :=
    hobserve.comp (measurable_fst.prodMk (hhist.comp measurable_snd))
  have hi := (indepFun_snd_observation (μ := μ) hQ hhist hind observe hobserve).comp
    hf measurable_id
  have hc := condExp_indep_eq hnoise.comap_le hobs.comap_le
    (comap_measurable (fun ω : S × N => f (Q ω.2))).stronglyMeasurable hi
  have hint : (∫ ω : S × N, f (Q ω.2) ∂μ.prod P) = ∫ ω, f (Q ω) ∂P := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_snd (μ := μ) (ν := P) (fun ω => f (Q ω)))
  simpa only [hint] using hc

theorem condExp_snd_observation_eq_zero {Q : N → ℝ} {hist : N → H}
    (hQ : Measurable Q) (hhist : Measurable hist)
    (hind : IndepFun Q hist P) (observe : S × H → O)
    (hobserve : Measurable observe) (hmean : ∫ ω, Q ω ∂P = 0) :
    (μ.prod P)[(fun ω : S × N => Q ω.2) |
      (inferInstance : MeasurableSpace O).comap
        (fun ω : S × N => observe (ω.1, hist ω.2))] =ᵐ[μ.prod P]
      fun _ => 0 := by
  simpa only [id_eq, hmean] using
    condExp_snd_observation (μ := μ) hQ hhist hind observe hobserve id measurable_id

theorem brownian_increment_indep_observation
    {B : ℝ≥0 → N → ℝ} (hB : IsPreBrownianReal B P)
    (hmB : ∀ t, Measurable (B t)) {X : S → ℝ} (hX : Measurable X)
    (t u : ℝ≥0) :
    IndepFun (fun ω : S × N => B (t + u) ω.2 - B t ω.2)
      (fun ω : S × N => fun s : Set.Iic t => (s.1 : ℝ) * X ω.1 + B s.1 ω.2)
      (μ.prod P) := by
  have hind : IndepFun (fun ω => B (t + u) ω - B t ω)
      (fun ω => fun s : Set.Iic t => B s.1 ω) P :=
    (hB.indepFun_shift t).comp (measurable_pi_apply u) measurable_id
  exact indepFun_snd_observation (μ := μ) ((hmB _).sub (hmB _))
    (Measurable.of_eval (fun s => hmB s.1)) hind
    (fun p : S × (Set.Iic t → ℝ) => fun s => (s.1 : ℝ) * X p.1 + p.2 s)
    (Measurable.of_eval (fun s =>
      (measurable_const.mul (hX.comp measurable_fst)).add
        ((measurable_pi_apply s).comp measurable_snd)))

theorem brownian_increment_condExp_observation
    {B : ℝ≥0 → N → ℝ} (hB : IsPreBrownianReal B P)
    (hmB : ∀ t, Measurable (B t)) {X : S → ℝ} (hX : Measurable X)
    (t u : ℝ≥0) :
    (μ.prod P)[(fun ω : S × N => B (t + u) ω.2 - B t ω.2) |
      (inferInstance : MeasurableSpace (Set.Iic t → ℝ)).comap
        (fun ω : S × N => fun s : Set.Iic t => (s.1 : ℝ) * X ω.1 + B s.1 ω.2)]
      =ᵐ[μ.prod P] fun _ => 0 := by
  have hind : IndepFun (fun ω => B (t + u) ω - B t ω)
      (fun ω => fun s : Set.Iic t => B s.1 ω) P :=
    (hB.indepFun_shift t).comp (measurable_pi_apply u) measurable_id
  apply condExp_snd_observation_eq_zero (μ := μ) ((hmB _).sub (hmB _))
    (Measurable.of_eval (fun s => hmB s.1)) hind
    (fun p : S × (Set.Iic t → ℝ) => fun s => (s.1 : ℝ) * X p.1 + p.2 s)
    (Measurable.of_eval (fun s =>
      (measurable_const.mul (hX.comp measurable_fst)).add
        ((measurable_pi_apply s).comp measurable_snd)))
  change (∫ ω, B (t + u) ω - B t ω ∂P) = 0
  rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _),
    hB.integral_eval, hB.integral_eval, sub_self]

end Problem336AdditiveD139.NoisePast

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem336AdditiveD139.Noise

theorem indepFun_vectors_of_independent_pairs
    {I : Type u_1} {Ω : Type u_2} {A : Type u_3} {B : Type u_4} [Fintype I] [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : I → Ω → A} {Y : I → Ω → B}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hpair : iIndepFun (fun i ω => (X i ω, Y i ω)) P)
    (hxy : ∀ i, IndepFun (X i) (Y i) P) :
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P := by
  have hXi : iIndepFun X P := hpair.comp (fun _ => Prod.fst) (by fun_prop)
  have hYi : iIndepFun Y P := hpair.comp (fun _ => Prod.snd) (by fun_prop)
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).2
  have hsplit :
      (fun ω => (fun i => X i ω, fun i => Y i ω)) =
      (MeasurableEquiv.arrowProdEquivProdArrow A B I) ∘
        (fun ω i => (X i ω, Y i ω)) := rfl
  rw [hsplit, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [hpair.map_fun_eq_pi_map (fun i => (hX i).prodMk (hY i) |>.aemeasurable)]
  simp_rw [fun i => (hxy i).map_prod_eq_prod_map_map
    (hX i).aemeasurable (hY i).aemeasurable]
  have : ∀ i, IsProbabilityMeasure (P.map (X i)) :=
    fun i => Measure.isProbabilityMeasure_map (hX i).aemeasurable
  have : ∀ i, IsProbabilityMeasure (P.map (Y i)) :=
    fun i => Measure.isProbabilityMeasure_map (hY i).aemeasurable
  rw [(measurePreserving_arrowProdEquivProdArrow A B I
    (fun i => P.map (X i)) (fun i => P.map (Y i))).map_eq]
  rw [hXi.map_fun_eq_pi_map (fun i => (hX i).aemeasurable),
    hYi.map_fun_eq_pi_map (fun i => (hY i).aemeasurable)]

theorem indepFun_families_of_independent_pairs
    {I : Type u_5} {Ω : Type u_6} {A : Type u_7} {B : Type u_8} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : I → Ω → A} {Y : I → Ω → B}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hpair : iIndepFun (fun i ω => (X i ω, Y i ω)) P)
    (hxy : ∀ i, IndepFun (X i) (Y i) P) :
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P := by
  classical
  apply IndepFun.process_indepFun_process hX hY
  intro S T
  have hfin := indepFun_vectors_of_independent_pairs
    (I := ↥(S ∪ T)) (X := fun i => X i) (Y := fun i => Y i)
    (fun i => hX i) (fun i => hY i)
    (hpair.precomp Subtype.val_injective) (fun i => hxy i)
  exact hfin.comp
    (φ := fun x (i : S) => x ⟨i, Finset.mem_union_left T i.property⟩)
    (ψ := fun y (i : T) => y ⟨i, Finset.mem_union_right S i.property⟩)
    (by fun_prop) (by fun_prop)

theorem indepFun_families_infinitePi
    {I : Type u_9} {Ω : Type u_10} {A : Type u_11} {B : Type u_12} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    (P : I → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    {X : I → Ω → A} {Y : I → Ω → B}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hxy : ∀ i, IndepFun (X i) (Y i) (P i)) :
    IndepFun (fun ω i => X i (ω i)) (fun ω i => Y i (ω i))
      (Measure.infinitePi P) := by
  apply indepFun_families_of_independent_pairs
    (fun i => (hX i).comp (measurable_pi_apply i))
    (fun i => (hY i).comp (measurable_pi_apply i))
  · exact iIndepFun_infinitePi (fun i => (hX i).prodMk (hY i))
  · intro i
    apply (indepFun_iff_map_prod_eq_prod_map_map
      ((hX i).comp (measurable_pi_apply i)).aemeasurable
      ((hY i).comp (measurable_pi_apply i)).aemeasurable).2
    simp only [Function.comp_apply]
    have hm (f : Ω → A × B) (hf : Measurable f) :
        (Measure.infinitePi P).map (fun ω => f (ω i)) = (P i).map f := by
      rw [← Function.comp_def, ← Measure.map_map hf (measurable_pi_apply i),
        Measure.infinitePi_map_eval]
    rw [hm (fun ω => (X i ω, Y i ω)) ((hX i).prodMk (hY i))]
    rw [(hxy i).map_prod_eq_prod_map_map (hX i).aemeasurable (hY i).aemeasurable]
    congr 1
    · rw [← Measure.map_map (hX i) (measurable_pi_apply i), Measure.infinitePi_map_eval]
    · rw [← Measure.map_map (hY i) (measurable_pi_apply i), Measure.infinitePi_map_eval]

theorem brownian_iid_shift_indep_past
    {I : Type u_13} {Ω : Type u_14} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t)) (u : ℝ≥0) :
    IndepFun (fun (ω : I → Ω) i t => B (u + t) (ω i) - B u (ω i))
      (fun (ω : I → Ω) i (t : Set.Iic u) => B t (ω i))
      (Measure.infinitePi (fun _ : I => P)) := by
  apply indepFun_families_infinitePi (fun _ : I => P)
    (X := fun _ ω t => B (u + t) ω - B u ω)
    (Y := fun _ ω (t : Set.Iic u) => B t ω)
  · intro i
    exact Measurable.of_eval fun t => (hm (u + t)).sub (hm u)
  · intro i
    exact Measurable.of_eval fun t => hm t
  · intro i
    exact hB.indepFun_shift u

theorem brownian_iid_weighted_increment_indep_past
    {I : Type u_15} {Ω : Type u_16} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    IndepFun (fun (ω : I → Ω) => ∑ i ∈ S, θ i * (B (u + h) (ω i) - B u (ω i)))
      (fun (ω : I → Ω) i (t : Set.Iic u) => B t (ω i))
      (Measure.infinitePi (fun _ : I => P)) := by
  exact (brownian_iid_shift_indep_past hB hm u).comp
    (φ := fun z : I → ℝ≥0 → ℝ => ∑ i ∈ S, θ i * z i h)
    (ψ := id) (by fun_prop) measurable_id

theorem hasLaw_finsetSum_gaussian
    {I : Type u_17} {Ω : Type u_18} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : I → Ω → ℝ} {m : I → ℝ} {v : I → ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (gaussianReal (m i) (v i)) P)
    (hind : iIndepFun X P) (S : Finset I) :
    HasLaw (∑ i ∈ S, X i) (gaussianReal (∑ i ∈ S, m i) (∑ i ∈ S, v i)) P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change HasLaw (fun _ : Ω => (0 : ℝ)) (gaussianReal 0 0) P
      exact ⟨aemeasurable_const, by simp [gaussianReal_zero_var, Measure.map_const]⟩
  | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      refine ⟨(hX i).aemeasurable.add ih.aemeasurable, ?_⟩
      exact gaussianReal_add_gaussianReal_of_indepFun
        (hind.indepFun_finsetSum_of_notMem₀ (fun i => (hX i).aemeasurable) hi).symm
        (hX i).map_eq ih.map_eq

theorem hasLaw_infinitePi_eval
    {I : Type u_19} {Ω : Type u_20} [MeasurableSpace Ω]
    (P : I → Measure Ω) [∀ i, IsProbabilityMeasure (P i)] (i : I) :
    HasLaw (fun ω : I → Ω => ω i) (P i) (Measure.infinitePi P) :=
  ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval P i⟩

theorem brownian_iid_weighted_increment_hasLaw
    {I : Type u_21} {Ω : Type u_22} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    HasLaw (fun (ω : I → Ω) => ∑ i ∈ S, θ i * (B (u + h) (ω i) - B u (ω i)))
      (gaussianReal 0 (∑ i ∈ S, (NNReal.mk (θ i ^ 2) (sq_nonneg _)) * h))
      (Measure.infinitePi (fun _ : I => P)) := by
  have hlaw (i : I) :
      HasLaw (fun (ω : I → Ω) => θ i * (B (u + h) (ω i) - B u (ω i)))
        (gaussianReal 0 ((NNReal.mk (θ i ^ 2) (sq_nonneg _)) * h))
        (Measure.infinitePi (fun _ : I => P)) := by
    simpa only [Function.comp_def, mul_zero] using
      (gaussianReal_const_mul ((hB.shift u).hasLaw_eval h) (θ i)).comp
      (hasLaw_infinitePi_eval (fun _ : I => P) i)
  have hind : iIndepFun
      (fun i (ω : I → Ω) => θ i * (B (u + h) (ω i) - B u (ω i)))
      (Measure.infinitePi (fun _ : I => P)) :=
    iIndepFun_infinitePi (fun i => ((hm (u + h)).sub (hm u)).const_mul (θ i))
  convert hasLaw_finsetSum_gaussian hlaw hind S using 1
  · ext ω
    simp only [Finset.sum_apply]
  · simp

end Problem336AdditiveD139.Noise

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem336AdditiveD139.ObservationNoise

variable {I : Type u_1} {Ω : Type u_2} [MeasurableSpace Ω]
  (μ : ProbabilityMeasure (I → Bool)) (P : Measure Ω) [IsProbabilityMeasure P]

def referenceMeasure : Measure ((I → Bool) × (I → Ω)) :=
  (μ : Measure (I → Bool)).prod (Measure.infinitePi (fun _ : I => P))

instance : IsProbabilityMeasure (referenceMeasure μ P) := by
  unfold referenceMeasure
  infer_instance

def history (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0)
    (ω : (I → Bool) × (I → Ω)) (i : I) (s : Set.Iic u) : ℝ :=
  (s.1 : ℝ) * boolReal (ω.1 i) + B s.1 (ω.2 i)

def increment (B : ℝ≥0 → Ω → ℝ) (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ)
    (ω : (I → Bool) × (I → Ω)) : ℝ :=
  ∑ i ∈ S, θ i * (B (u + h) (ω.2 i) - B u (ω.2 i))

def incrementVariance (h : ℝ≥0) (S : Finset I) (θ : I → ℝ) : ℝ≥0 :=
  ∑ i ∈ S, (NNReal.mk (θ i ^ 2) (sq_nonneg _)) * h

theorem incrementVariance_coe (h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    (incrementVariance h S θ : ℝ) = (h : ℝ) * ∑ i ∈ S, θ i ^ 2 := by
  simp [incrementVariance, Finset.mul_sum, mul_comm]

variable {μ P}

theorem measurable_history {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (u : ℝ≥0) :
    Measurable (history B u : ((I → Bool) × (I → Ω)) → I → Set.Iic u → ℝ) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro s
  exact (measurable_const.mul
    ((measurable_of_countable boolReal).comp ((measurable_pi_apply i).comp measurable_fst))).add
      ((hm s.1).comp ((measurable_pi_apply i).comp measurable_snd))

theorem measurable_increment {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    Measurable (increment B u h S θ : ((I → Bool) × (I → Ω)) → ℝ) := by
  unfold increment
  fun_prop

@[reducible] def historySigma (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) :
    MeasurableSpace ((I → Bool) × (I → Ω)) :=
  (inferInstance : MeasurableSpace (I → Set.Iic u → ℝ)).comap (history B u)

omit [MeasurableSpace Ω] in
theorem historySigma_mono (B : ℝ≥0 → Ω → ℝ) :
    Monotone (historySigma (I := I) B) := by
  intro u v huv
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun y : I → Set.Iic v → ℝ => fun (i : I) (s : Set.Iic u) =>
      y i ⟨s.1, le_trans s.2 huv⟩)
  · fun_prop
  · rfl

def filtration {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace ((I → Bool) × (I → Ω))) where
  seq := historySigma B
  mono' := historySigma_mono B
  le' u := (measurable_history hm u).comap_le

omit [MeasurableSpace Ω] in

theorem measurable_current_observation (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (i : I) :
    Measurable[historySigma B u]
      (fun ω : (I → Bool) × (I → Ω) =>
        (u : ℝ) * boolReal (ω.1 i) + B u (ω.2 i)) :=
  (measurable_pi_apply (⟨u, by simp⟩ : Set.Iic u)).comp
    ((measurable_pi_apply i).comp (comap_measurable (history B u)))

theorem increment_indep_history {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    IndepFun (increment B u h S θ) (history B u) (referenceMeasure μ P) := by
  have hind := Noise.brownian_iid_weighted_increment_indep_past hB hm u h S θ
  refine NoisePast.indepFun_snd_observation (μ := (μ : Measure (I → Bool)))
    (by fun_prop) (by fun_prop) hind
    (fun p : (I → Bool) × (I → Set.Iic u → ℝ) =>
      fun i s => (s.1 : ℝ) * boolReal (p.1 i) + p.2 i s) ?_
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro s
  exact (measurable_const.mul
    ((measurable_of_countable boolReal).comp ((measurable_pi_apply i).comp measurable_fst))).add
      ((measurable_pi_apply s).comp ((measurable_pi_apply i).comp measurable_snd))

theorem increment_hasLaw {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    HasLaw (increment B u h S θ) (gaussianReal 0 (incrementVariance h S θ))
      (referenceMeasure μ P) := by
  exact (Noise.brownian_iid_weighted_increment_hasLaw hB hm u h S θ).comp
    (measurePreserving_snd (μ := (μ : Measure (I → Bool)))
      (ν := Measure.infinitePi (fun _ : I => P))).hasLaw

theorem increment_condExp_gaussian {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (referenceMeasure μ P)[(fun ω => f (increment B u h S θ ω)) | historySigma B u]
      =ᵐ[referenceMeasure μ P] fun _ =>
        ∫ x, f x ∂gaussianReal 0 (incrementVariance h S θ) := by
  have hQ := measurable_increment hm u h S θ
  have hY := measurable_history (I := I) hm u
  have hind := (increment_indep_history (μ := μ) hB hm u h S θ).comp hf measurable_id
  have hc := condExp_indep_eq (hf.comp hQ).comap_le hY.comap_le
    (comap_measurable (fun ω => f (increment B u h S θ ω))).stronglyMeasurable hind
  have hi := (increment_hasLaw (μ := μ) hB hm u h S θ).integral_comp
    hf.aestronglyMeasurable
  exact hc.trans (Filter.Eventually.of_forall (fun _ => hi))

theorem increment_condExp_eq_zero {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    (referenceMeasure μ P)[increment B u h S θ | historySigma B u]
      =ᵐ[referenceMeasure μ P] fun _ => 0 := by
  simpa only [id_eq, integral_id_gaussianReal] using
    increment_condExp_gaussian (μ := μ) hB hm u h S θ id measurable_id

end Problem336AdditiveD139.ObservationNoise

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem336AdditiveD139.ObservationNoise

variable {I : Type u_1} {Ω : Type u_2} [MeasurableSpace Ω]
  (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure Ω)

theorem referenceMeasure_eq_referenceLaw :
    referenceMeasure μ (ν : Measure Ω) = ReferenceObservation.law μ ν := rfl

omit [MeasurableSpace Ω] in
theorem history_eq_referenceObservation (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0)
    (ω : ReferenceObservation.Space I Ω) (i : I) (s : Set.Iic u) :
    history B u ω i s = ReferenceObservation.observation B i s.1 ω := rfl

def realFiltration {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t)) :
    Filtration ℝ (inferInstance : MeasurableSpace (ReferenceObservation.Space I Ω)) where
  seq t := historySigma B t.toNNReal
  mono' := fun _ _ huv => historySigma_mono B (Real.toNNReal_mono huv)
  le' t := (measurable_history hm t.toNNReal).comap_le

@[simp] theorem realFiltration_apply {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (u : ℝ) :
    realFiltration (I := I) hm u = historySigma B u.toNNReal := rfl

lemma toNNReal_add_interval {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    u.toNNReal + (v - u).toNNReal = v.toNNReal := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_add, Real.coe_toNNReal _ hu,
    Real.coe_toNNReal _ (sub_nonneg.mpr huv), Real.coe_toNNReal _ (hu.trans huv)]
  ring

theorem incrementVariance_real {u v : ℝ} (huv : u ≤ v)
    (S : Finset I) (θ : I → ℝ) :
    (incrementVariance (v - u).toNNReal S θ : ℝ) =
      (v - u) * ∑ i ∈ S, θ i ^ 2 := by
  rw [incrementVariance_coe, Real.coe_toNNReal _ (sub_nonneg.mpr huv)]

omit [MeasurableSpace Ω] in
theorem increment_real_eq (B : ℝ≥0 → Ω → ℝ) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (S : Finset I) (θ : I → ℝ) :
    increment B u.toNNReal (v - u).toNNReal S θ =
      (fun ω : ReferenceObservation.Space I Ω => ∑ i ∈ S, θ i *
        (ReferenceObservation.noise B i v.toNNReal ω -
          ReferenceObservation.noise B i u.toNNReal ω)) := by
  funext ω
  dsimp [increment, ReferenceObservation.noise]
  rw [toNNReal_add_interval hu huv]

theorem real_increment_hasLaw {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B (ν : Measure Ω)) (hm : ∀ t, Measurable (B t))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (S : Finset I) (θ : I → ℝ) :
    HasLaw (fun ω : ReferenceObservation.Space I Ω => ∑ i ∈ S, θ i *
      (ReferenceObservation.noise B i v.toNNReal ω -
        ReferenceObservation.noise B i u.toNNReal ω))
      (gaussianReal 0 (incrementVariance (v - u).toNNReal S θ))
      (ReferenceObservation.law μ ν) := by
  simpa only [increment_real_eq B hu huv S θ,
    referenceMeasure_eq_referenceLaw] using
    increment_hasLaw (μ := μ) hB hm u.toNNReal (v - u).toNNReal S θ

theorem real_increment_indep_history {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B (ν : Measure Ω)) (hm : ∀ t, Measurable (B t))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (S : Finset I) (θ : I → ℝ) :
    IndepFun (fun ω : ReferenceObservation.Space I Ω => ∑ i ∈ S, θ i *
      (ReferenceObservation.noise B i v.toNNReal ω -
        ReferenceObservation.noise B i u.toNNReal ω))
      (history B u.toNNReal) (ReferenceObservation.law μ ν) := by
  simpa only [increment_real_eq B hu huv S θ,
    referenceMeasure_eq_referenceLaw] using
    increment_indep_history (μ := μ) hB hm u.toNNReal (v - u).toNNReal S θ

theorem real_increment_condExp_eq_zero {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B (ν : Measure Ω)) (hm : ∀ t, Measurable (B t))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (S : Finset I) (θ : I → ℝ) :
    (ReferenceObservation.law μ ν)[(fun ω : ReferenceObservation.Space I Ω =>
      ∑ i ∈ S, θ i * (ReferenceObservation.noise B i v.toNNReal ω -
        ReferenceObservation.noise B i u.toNNReal ω)) | realFiltration (I := I) hm u]
      =ᵐ[ReferenceObservation.law μ ν] fun _ => 0 := by
  simpa only [increment_real_eq B hu huv S θ,
    referenceMeasure_eq_referenceLaw, realFiltration_apply] using
    increment_condExp_eq_zero (μ := μ) hB hm u.toNNReal (v - u).toNNReal S θ

end Problem336AdditiveD139.ObservationNoise

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem336AdditiveD139.InnovationCharacteristic

def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp [phase, add_mul, Complex.exp_add]

theorem phase_sub_split (x y z : ℝ) : phase (z - x) = phase (y - x) * phase (z - y) := by
  rw [← phase_add]
  congr 1
  ring

theorem continuous_phase : Continuous phase := by unfold phase; fun_prop

section Probability

variable {Ω : Type u_1} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

theorem weighted_condExp_error {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f g : Ω → ℂ} (hf : StronglyMeasurable[m] f) (hg : Integrable g μ)
    (hfb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ 1) {a : ℂ} {ε : ℝ}
    (herr : ∀ᵐ ω ∂μ, ‖μ[g | m] ω - a‖ ≤ ε) :
    ‖(∫ ω, f ω * g ω ∂μ) - a * ∫ ω, f ω ∂μ‖ ≤ ε := by
  have hfm : AEStronglyMeasurable[m₀] f μ := (hf.mono hm).aestronglyMeasurable
  have hfi : Integrable f μ := (integrable_const (1 : ℝ)).mono' hfm hfb
  have hCE : Integrable (μ[g | m]) μ := integrable_condExp
  have hprod : Integrable (fun ω => f ω * μ[g | m] ω) μ := hCE.bdd_mul hfm hfb
  have hfa : Integrable (fun ω => f ω * a) μ := hfi.mul_const a
  have hpull := condExp_stronglyMeasurable_bilin_of_bound (ContinuousLinearMap.mul ℝ ℂ)
    hm hf hg 1 hfb
  have heq : (∫ ω, f ω * g ω ∂μ) = ∫ ω, f ω * μ[g | m] ω ∂μ := by
    calc
      _ = ∫ ω, μ[fun ω => f ω * g ω | m] ω ∂μ := (integral_condExp hm).symm
      _ = _ := integral_congr_ae hpull
  have hnorm : ∀ᵐ ω ∂μ, ‖f ω * (μ[g | m] ω - a)‖ ≤ ε := by
    filter_upwards [hfb, herr] with ω hfω heω
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hfω (norm_nonneg _)).trans (by simpa using heω)
  have h := norm_integral_le_of_norm_le_const hnorm
  simp only [probReal_univ, mul_one] at h
  convert h using 1
  rw [heq]
  congr 1
  simp_rw [mul_sub]
  rw [integral_sub hprod hfa, integral_mul_const]
  ring

theorem discrete_characteristic_error (N : ℕ) (m : ℕ → MeasurableSpace Ω)
    (hm : Monotone m) (hle : ∀ n, m n ≤ m₀) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n, StronglyMeasurable[m n] (Z n))
    (A : Set Ω) (hA : MeasurableSet[m 0] A)
    (a : ℂ) (ha : ‖a‖ ≤ 1) (ε : ℝ) (_hε : 0 ≤ ε)
    (hstep : ∀ k < N, ∀ᵐ ω ∂μ,
      ‖μ[fun ω => phase (Z (k + 1) ω - Z k ω) | m k] ω - a‖ ≤ ε) :
    ‖(∫ ω in A, phase (Z N ω - Z 0 ω) ∂μ) -
      a ^ N * ((μ A).toReal : ℂ)‖ ≤ (N : ℝ) * ε := by
  have hAm : MeasurableSet A := hle 0 A hA
  have hphase (k : ℕ) : StronglyMeasurable[m k] (fun ω => phase (Z k ω - Z 0 ω)) :=
    continuous_phase.comp_stronglyMeasurable ((hZ k).sub ((hZ 0).mono (hm (Nat.zero_le _))))
  have hint (k : ℕ) : Integrable (fun ω => phase (Z k ω - Z 0 ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono'
      (((hphase k).mono (hle k)).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (fun ω => by simp)
  have hrec (k : ℕ) (hk : k < N) :
      ‖(∫ ω in A, phase (Z (k + 1) ω - Z 0 ω) ∂μ) -
        a * ∫ ω in A, phase (Z k ω - Z 0 ω) ∂μ‖ ≤ ε := by
    let f : Ω → ℂ := A.indicator (fun ω => phase (Z k ω - Z 0 ω))
    let g : Ω → ℂ := fun ω => phase (Z (k + 1) ω - Z k ω)
    have hf : StronglyMeasurable[m k] f := (hphase k).indicator (hm (Nat.zero_le k) A hA)
    have hg : Integrable g μ := by
      refine (integrable_const (1 : ℝ)).mono' ?_ ?_
      · exact (continuous_phase.comp_stronglyMeasurable
          (((hZ (k + 1)).mono (hle (k + 1))).sub ((hZ k).mono (hle k)))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun ω => by simp [g])
    have hfb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ 1 := by
      filter_upwards with ω
      by_cases hω : ω ∈ A <;> simp [f, hω]
    have h := weighted_condExp_error (hle k) hf hg hfb (hstep k hk)
    have heq : (fun ω => f ω * g ω) = A.indicator
        (fun ω => phase (Z (k + 1) ω - Z 0 ω)) := by
      ext ω
      by_cases hω : ω ∈ A
      · simp only [f, g, Set.indicator_of_mem hω]
        exact (phase_sub_split _ _ _).symm
      · simp [f, hω]
    simpa only [heq, f, integral_indicator hAm] using h
  have hind : ∀ k ≤ N,
      ‖(∫ ω in A, phase (Z k ω - Z 0 ω) ∂μ) -
        a ^ k * ((μ A).toReal : ℂ)‖ ≤ (k : ℝ) * ε := by
    intro k hk
    induction k with
    | zero => simp [Measure.real]
    | succ k ih =>
      have ih' := ih (Nat.le_of_succ_le hk)
      have hs := hrec k (Nat.lt_of_succ_le hk)
      calc
        _ = ‖((∫ ω in A, phase (Z (k + 1) ω - Z 0 ω) ∂μ) -
            a * ∫ ω in A, phase (Z k ω - Z 0 ω) ∂μ) +
            a * ((∫ ω in A, phase (Z k ω - Z 0 ω) ∂μ) -
              a ^ k * ((μ A).toReal : ℂ))‖ := by congr 1; rw [pow_succ]; ring
        _ ≤ ε + (k : ℝ) * ε := (norm_add_le _ _).trans
          (add_le_add hs (by rw [norm_mul]; exact
            (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using ih')))
        _ = ((k + 1 : ℕ) : ℝ) * ε := by push_cast; ring
  exact hind N le_rfl

theorem time_partition_characteristic_error
    (H : ℝ → MeasurableSpace Ω) (hH : Monotone H) (hle : ∀ u, H u ≤ m₀)
    (W : ℝ → Ω → ℝ) (hW : ∀ u, 0 ≤ u → StronglyMeasurable[H u] (W u))
    (C σ2 : ℝ) (hC : 0 ≤ C) (hσ : 0 ≤ σ2)
    (hlocal : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ 1 → ∀ᵐ ω ∂μ,
      ‖μ[fun ω => phase (W v ω - W u ω) | H u] ω -
        (Real.exp (-(v - u) * σ2 / 2) : ℂ)‖ ≤ C * (v - u) * Real.sqrt (v - u))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (A : Set Ω)
    (hA : MeasurableSet[H s] A) (N : ℕ) (hN : 0 < N)
    (hsmall : (t - s) / N ≤ 1) :
    ‖(∫ ω in A, phase (W t ω - W s ω) ∂μ) -
      (Real.exp (-(t - s) * σ2 / 2) : ℂ) * ((μ A).toReal : ℂ)‖ ≤
      C * (t - s) * Real.sqrt ((t - s) / N) := by
  let δ : ℝ := (t - s) / N
  let τ : ℕ → ℝ := fun k => s + δ * k
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hδ : 0 ≤ δ := div_nonneg (sub_nonneg.mpr hst) (Nat.cast_nonneg N)
  have hτ : Monotone τ := by
    intro i j hij
    dsimp [τ]
    gcongr
  have hτ0 : τ 0 = s := by simp [τ]
  have hτN : τ N = t := by dsimp [τ, δ]; field_simp; ring
  have hτpos (k : ℕ) : 0 ≤ τ k := hs.trans (by simpa [hτ0] using hτ (Nat.zero_le k))
  have hτstep (k : ℕ) : τ (k + 1) - τ k = δ := by dsimp [τ]; push_cast; ring
  let a : ℂ := Real.exp (-δ * σ2 / 2)
  have ha : ‖a‖ ≤ 1 := by
    dsimp [a]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hδ hσ]
  have haN : a ^ N = (Real.exp (-(t - s) * σ2 / 2) : ℂ) := by
    dsimp [a]
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    dsimp [δ]
    field_simp
  have hε : 0 ≤ C * δ * Real.sqrt δ :=
    mul_nonneg (mul_nonneg hC hδ) (Real.sqrt_nonneg _)
  have hstep : ∀ k < N, ∀ᵐ ω ∂μ,
      ‖μ[fun ω => phase (W (τ (k + 1)) ω - W (τ k) ω) | H (τ k)] ω - a‖ ≤
        C * δ * Real.sqrt δ := by
    intro k _hk
    have h := hlocal (τ k) (τ (k + 1)) (hτpos k) (hτ (Nat.le_succ k))
      (by simpa only [hτstep] using hsmall)
    simpa only [hτstep, a] using h
  have h := discrete_characteristic_error N (fun k => H (τ k)) (hH.comp hτ)
    (fun k => hle (τ k)) (fun k => W (τ k)) (fun k => hW (τ k) (hτpos k)) A
    (by rw [hτ0]; exact hA)
    a ha (C * δ * Real.sqrt δ) hε hstep
  rw [hτN, hτ0, haN] at h
  convert h using 1
  dsimp [δ]
  field_simp

theorem event_characteristic_eq
    (H : ℝ → MeasurableSpace Ω) (hH : Monotone H) (hle : ∀ u, H u ≤ m₀)
    (W : ℝ → Ω → ℝ) (hW : ∀ u, 0 ≤ u → StronglyMeasurable[H u] (W u))
    (C σ2 : ℝ) (hC : 0 ≤ C) (hσ : 0 ≤ σ2)
    (hlocal : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ 1 → ∀ᵐ ω ∂μ,
      ‖μ[fun ω => phase (W v ω - W u ω) | H u] ω -
        (Real.exp (-(v - u) * σ2 / 2) : ℂ)‖ ≤ C * (v - u) * Real.sqrt (v - u))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (A : Set Ω)
    (hA : MeasurableSet[H s] A) :
    (∫ ω in A, phase (W t ω - W s ω) ∂μ) =
      (Real.exp (-(t - s) * σ2 / 2) : ℂ) * ((μ A).toReal : ℂ) := by
  have hdiv : Tendsto (fun N : ℕ => (t - s) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlim : Tendsto (fun N : ℕ => C * (t - s) * Real.sqrt ((t - s) / N))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C * (t - s))).mul hdiv.sqrt
  have hsmall : ∀ᶠ N : ℕ in atTop, (t - s) / (N : ℝ) ≤ 1 :=
    (hdiv.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono
      (fun _ h => h.le)
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖(∫ ω in A, phase (W t ω - W s ω) ∂μ) -
        (Real.exp (-(t - s) * σ2 / 2) : ℂ) * ((μ A).toReal : ℂ)‖ ≤
        C * (t - s) * Real.sqrt ((t - s) / N) := by
    filter_upwards [hsmall, eventually_ge_atTop 1] with N hsmall hN
    exact time_partition_characteristic_error H hH hle W hW C σ2 hC hσ
      hlocal hs hst A hA N (by omega) hsmall
  have hz := ge_of_tendsto hlim hbound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

end Probability

end Problem336AdditiveD139.InnovationCharacteristic

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem336AdditiveD139.CharacteristicLaw

variable {Ω : Type u_1} {E : Type u_2} {m mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure E} [IsFiniteMeasure ν]
    {Z : Ω → E}

theorem map_restrict_eq_smul_of_characteristic
    (hZ : Measurable Z) (A : Set Ω)
    (hchar : ∀ t : E,
      (∫ ω in A, Complex.exp ((inner ℝ (Z ω) t : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) * charFun ν t) :
    Measure.map Z (μ.restrict A) = μ A • ν := by
  let : IsFiniteMeasure (μ A • ν) := ν.smul_finite (measure_ne_top μ A)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, integral_map hZ.aemeasurable (by fun_prop), hchar t]
  simp only [charFun_apply, integral_smul_measure, Complex.real_smul]

theorem map_eq_of_event_characteristic
    (hZ : Measurable Z) [IsProbabilityMeasure μ]
    (hchar : ∀ A : Set Ω, MeasurableSet[m] A → ∀ t : E,
      (∫ ω in A, Complex.exp ((inner ℝ (Z ω) t : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) * charFun ν t) :
    Measure.map Z μ = ν := by
  simpa using map_restrict_eq_smul_of_characteristic hZ Set.univ
    (hchar Set.univ MeasurableSet.univ)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E] [IsFiniteMeasure μ] [IsFiniteMeasure ν] in

theorem independent_of_restricted_law
    [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hm : m ≤ mΩ)
    (hlaw : Measure.map Z μ = ν)
    (hrestrict : ∀ A : Set Ω, MeasurableSet[m] A →
      Measure.map Z (μ.restrict A) = μ A • ν) :
    Indep m (MeasurableSpace.comap Z inferInstance) μ := by
  rw [indep_iff_forall_indepSet]
  intro A B hA hB
  obtain ⟨C, hC, rfl⟩ := hB
  apply (indepSet_iff_measure_inter_eq_mul (hm A hA) (hZ hC) μ).2
  have hr := congrArg (fun ρ : Measure E => ρ C) (hrestrict A hA)
  have hu := congrArg (fun ρ : Measure E => ρ C) hlaw
  rw [Measure.map_apply hZ hC, Measure.restrict_apply (hZ hC),
    Measure.smul_apply, smul_eq_mul] at hr
  rw [Measure.map_apply hZ hC] at hu
  simpa only [Set.inter_comm, hu] using hr

theorem law_and_independent_of_event_characteristic
    [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hm : m ≤ mΩ)
    (hchar : ∀ A : Set Ω, MeasurableSet[m] A → ∀ t : E,
      (∫ ω in A, Complex.exp ((inner ℝ (Z ω) t : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) * charFun ν t) :
    Measure.map Z μ = ν ∧ Indep m (MeasurableSpace.comap Z inferInstance) μ := by
  have hlaw := map_eq_of_event_characteristic hZ hchar
  refine ⟨hlaw, independent_of_restricted_law hZ hm hlaw ?_⟩
  intro A hA
  exact map_restrict_eq_smul_of_characteristic hZ A (hchar A hA)

theorem indepFun_of_event_characteristic
    [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hm : m ≤ mΩ)
    (hchar : ∀ A : Set Ω, MeasurableSet[m] A → ∀ t : E,
      (∫ ω in A, Complex.exp ((inner ℝ (Z ω) t : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) * charFun ν t)
    {Y : Type u_3} [MeasurableSpace Y] {X : Ω → Y} (hX : Measurable[m] X) :
    IndepFun X Z μ := by
  have h := (law_and_independent_of_event_characteristic hZ hm hchar).2
  exact indep_of_indep_of_le_left h hX.comap_le

end Problem336AdditiveD139.CharacteristicLaw

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Problem336AdditiveD139.CharacteristicLaw

variable {F : Type u_1} [Fintype F]

theorem charFun_pi_centered_gaussian (v : ℝ≥0) (t : EuclideanSpace ℝ F) :
    charFun ((Measure.pi (fun _ : F => gaussianReal 0 v)).map (WithLp.toLp 2)) t =
      Complex.exp (((-(v : ℝ) * ∑ i : F, (t i) ^ 2) / 2 : ℝ) : ℂ) := by
  rw [charFun_pi]
  simp_rw [charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

variable {Ω : Type u_2} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → F → ℝ}

theorem map_restrict_eq_gaussian_pi_of_characteristic
    (hZ : Measurable Z) (v : ℝ≥0) (A : Set Ω)
    (hchar : ∀ t : F → ℝ,
      (∫ ω in A, Complex.exp (((∑ i : F, Z ω i * t i : ℝ) : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) *
          Complex.exp (((-(v : ℝ) * ∑ i : F, (t i) ^ 2) / 2 : ℝ) : ℂ)) :
    Measure.map Z (μ.restrict A) = μ A • Measure.pi (fun _ : F => gaussianReal 0 v) := by
  let e : (F → ℝ) ≃ᵐ EuclideanSpace ℝ F := MeasurableEquiv.toLp 2 (F → ℝ)
  apply e.map_measurableEquiv_injective
  rw [Measure.map_map e.measurable hZ, Measure.map_smul]
  apply map_restrict_eq_smul_of_characteristic (e.measurable.comp hZ) A
  intro t
  rw [show Measure.map e (Measure.pi (fun _ : F => gaussianReal 0 v)) =
    (Measure.pi (fun _ : F => gaussianReal 0 v)).map (WithLp.toLp 2) from rfl,
    charFun_pi_centered_gaussian]
  simpa only [Function.comp_apply, e, MeasurableEquiv.coe_toLp,
    PiLp.inner_apply, Real.inner_apply, mul_comm] using hchar t

theorem gaussian_pi_law_and_independent_of_event_characteristic
    [IsProbabilityMeasure μ] (hZ : Measurable Z) (hm : m ≤ mΩ) (v : ℝ≥0)
    (hchar : ∀ A : Set Ω, MeasurableSet[m] A → ∀ t : F → ℝ,
      (∫ ω in A, Complex.exp (((∑ i : F, Z ω i * t i : ℝ) : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) *
          Complex.exp (((-(v : ℝ) * ∑ i : F, (t i) ^ 2) / 2 : ℝ) : ℂ)) :
    Measure.map Z μ = Measure.pi (fun _ : F => gaussianReal 0 v) ∧
      Indep m (MeasurableSpace.comap Z inferInstance) μ := by
  have hr (A : Set Ω) (hA : MeasurableSet[m] A) :=
    map_restrict_eq_gaussian_pi_of_characteristic hZ v A (hchar A hA)
  have hlaw : Measure.map Z μ = Measure.pi (fun _ : F => gaussianReal 0 v) := by
    simpa using hr Set.univ MeasurableSet.univ
  exact ⟨hlaw, independent_of_restricted_law hZ hm hlaw hr⟩

end Problem336AdditiveD139.CharacteristicLaw

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem336AdditiveD139.InnovationCharacteristic

variable {Ω : Type u_1} {F : Type u_2} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [Fintype F]

theorem gaussian_increment_law_of_local_characteristic
    (H : ℝ → MeasurableSpace Ω) (hH : Monotone H) (hle : ∀ u, H u ≤ mΩ)
    (W : ℝ → Ω → F → ℝ)
    (hW : ∀ u, 0 ≤ u → ∀ i, StronglyMeasurable[H u] (fun ω => W u ω i))
    (hlocal : ∀ θ : F → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ 1 → ∀ᵐ ω ∂μ,
        ‖μ[fun ω => phase (∑ i : F, (W v ω i - W u ω i) * θ i) | H u] ω -
          (Real.exp (-(v - u) * (∑ i : F, (θ i) ^ 2) / 2) : ℂ)‖ ≤
            C * (v - u) * Real.sqrt (v - u))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Measure.map (fun ω i => W t ω i - W s ω i) μ =
        Measure.pi (fun _ : F => gaussianReal 0 ⟨t - s, sub_nonneg.mpr hst⟩) ∧
      Indep (H s) (MeasurableSpace.comap (fun ω i => W t ω i - W s ω i)
        inferInstance) μ := by
  classical
  have ht : 0 ≤ t := hs.trans hst
  have hZ : Measurable (fun ω i => W t ω i - W s ω i) :=
    Measurable.of_eval (fun i =>
      (((hW t ht i).mono (hle t)).measurable.sub ((hW s hs i).mono (hle s)).measurable))
  apply CharacteristicLaw.gaussian_pi_law_and_independent_of_event_characteristic
    hZ (hle s) ⟨t - s, sub_nonneg.mpr hst⟩
  intro A hA θ
  obtain ⟨C, hC, herr⟩ := hlocal θ
  let V : ℝ → Ω → ℝ := fun u ω => ∑ i : F, W u ω i * θ i
  have hV (u : ℝ) (hu : 0 ≤ u) : StronglyMeasurable[H u] (V u) := by
    exact Finset.stronglyMeasurable_fun_sum _ (fun i _ => (hW u hu i).mul_const (θ i))
  have hdiff (u v : ℝ) (ω : Ω) :
      V v ω - V u ω = ∑ i : F, (W v ω i - W u ω i) * θ i := by
    simp only [V, sub_mul, Finset.sum_sub_distrib]
  have herr' : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ 1 → ∀ᵐ ω ∂μ,
      ‖μ[fun ω => phase (V v ω - V u ω) | H u] ω -
        (Real.exp (-(v - u) * (∑ i : F, (θ i) ^ 2) / 2) : ℂ)‖ ≤
          C * (v - u) * Real.sqrt (v - u) := by
    simpa only [hdiff] using herr
  have h := event_characteristic_eq H hH hle V hV C (∑ i : F, (θ i) ^ 2) hC
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) herr' hs hst A hA
  change (∫ ω in A, Complex.exp (((∑ i : F, (W t ω i - W s ω i) * θ i : ℝ) : ℂ) *
      Complex.I) ∂μ) = ((μ A).toReal : ℂ) *
        Complex.exp (((-(t - s) * ∑ i : F, (θ i) ^ 2) / 2 : ℝ) : ℂ)
  simpa only [hdiff, phase, Complex.ofReal_exp, mul_comm] using h

theorem gaussian_increment_law_of_local_characteristic_nnreal
    (H : ℝ≥0 → MeasurableSpace Ω) (hH : Monotone H) (hle : ∀ u, H u ≤ mΩ)
    (W : ℝ≥0 → Ω → F → ℝ)
    (hW : ∀ u i, StronglyMeasurable[H u] (fun ω => W u ω i))
    (hlocal : ∀ θ : F → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : ℝ≥0, u ≤ v → (v : ℝ) - u ≤ 1 → ∀ᵐ ω ∂μ,
        ‖μ[fun ω => phase (∑ i : F, (W v ω i - W u ω i) * θ i) | H u] ω -
          (Real.exp (-((v : ℝ) - u) * (∑ i : F, (θ i) ^ 2) / 2) : ℂ)‖ ≤
            C * ((v : ℝ) - u) * Real.sqrt ((v : ℝ) - u))
    {s t : ℝ≥0} (hst : s ≤ t) :
    Measure.map (fun ω i => W t ω i - W s ω i) μ =
        Measure.pi (fun _ : F => gaussianReal 0 (t - s)) ∧
      Indep (H s) (MeasurableSpace.comap (fun ω i => W t ω i - W s ω i)
        inferInstance) μ := by
  have hlocal' : ∀ θ : F → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ 1 → ∀ᵐ ω ∂μ,
        ‖μ[fun ω => phase (∑ i : F,
          (W v.toNNReal ω i - W u.toNNReal ω i) * θ i) | H u.toNNReal] ω -
          (Real.exp (-(v - u) * (∑ i : F, (θ i) ^ 2) / 2) : ℂ)‖ ≤
            C * (v - u) * Real.sqrt (v - u) := by
    intro θ
    obtain ⟨C, hC, hθ⟩ := hlocal θ
    refine ⟨C, hC, ?_⟩
    intro u v hu huv hvu
    have hv : 0 ≤ v := hu.trans huv
    have h := hθ u.toNNReal v.toNNReal (Real.toNNReal_monotone huv)
      (by simpa only [Real.coe_toNNReal _ hu, Real.coe_toNNReal _ hv] using hvu)
    simpa only [Real.coe_toNNReal _ hu, Real.coe_toNNReal _ hv] using h
  have h := gaussian_increment_law_of_local_characteristic
    (fun u => H u.toNNReal) (hH.comp Real.toNNReal_monotone)
    (fun u => hle u.toNNReal) (fun u => W u.toNNReal)
    (fun u _ => hW u.toNNReal) hlocal' (s := (s : ℝ)) (t := (t : ℝ))
    s.property (show (s : ℝ) ≤ t from hst)
  have hv : (⟨(t : ℝ) - s, sub_nonneg.mpr (show (s : ℝ) ≤ t from hst)⟩ : ℝ≥0) =
      t - s := by
    apply Subtype.ext
    exact (NNReal.coe_sub hst).symm
  have hscoe : ((s : ℝ).toNNReal) = s := Real.toNNReal_coe
  have htcoe : ((t : ℝ).toNNReal) = t := Real.toNNReal_coe
  rw [hscoe, htcoe] at h
  change (Measure.map (fun ω i => W t ω i - W s ω i) μ =
      Measure.pi (fun _ : F => gaussianReal 0
        ⟨(t : ℝ) - s, sub_nonneg.mpr (show (s : ℝ) ≤ t from hst)⟩)) ∧ _ at h
  rwa [hv] at h

end Problem336AdditiveD139.InnovationCharacteristic

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139

theorem iIndepFun_of_indep_predecessors
    {Ω : Type u_1} {ι : Type u_2} {E : Type u_3} [MeasurableSpace Ω] [LinearOrder ι] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : ι → Ω → E}
    (hindep : ∀ i, IndepFun (f i) (fun ω (j : Set.Iio i) => f j ω) P) :
    iIndepFun f P := by
  classical
  rw [iIndepFun_iff]
  intro s
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
      intro A hA
      have has : a ∉ s := fun ha => (lt_irrefl a) (hlt a ha)
      have hpast : MeasurableSet[
          MeasurableSpace.comap (fun ω (j : Set.Iio a) => f j ω) inferInstance]
          (⋂ j ∈ s, A j) := by
        apply MeasurableSet.biInter s.countable_toSet
        intro j hj
        obtain ⟨B, hB, hpre⟩ := hA j (Finset.mem_insert_of_mem hj)
        refine ⟨(fun z : Set.Iio a → E => z ⟨j, hlt j hj⟩) ⁻¹' B,
          hB.preimage (measurable_pi_apply _), ?_⟩
        exact hpre
      rw [Finset.set_biInter_insert, Finset.prod_insert has,
        (hindep a).meas_inter (hA a (Finset.mem_insert_self a s)) hpast,
        ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))]

theorem hasIndepIncrements_of_indep_history
    {Ω : Type u_4} {T : Type u_5} {E : Type u_6} [MeasurableSpace Ω] [Preorder T]
    [MeasurableSpace E] [Sub E] [MeasurableSub₂ E]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : T → Ω → E}
    (hindep : ∀ u v, u ≤ v → IndepFun
      (fun ω => X v ω - X u ω)
      (fun ω (s : Set.Iic u) => X s ω) P) :
    HasIndepIncrements X P := by
  intro n t ht
  apply iIndepFun_of_indep_predecessors
  intro i
  have htime : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hleft (j : Set.Iio i) : t j.1.castSucc ≤ t i.castSucc :=
    ht (by change j.1.val ≤ i.val; exact le_of_lt j.2)
  have hright (j : Set.Iio i) : t j.1.succ ≤ t i.castSucc :=
    ht (by change j.1.val + 1 ≤ i.val; exact j.2)
  let ψ : (Set.Iic (t i.castSucc) → E) → (Set.Iio i → E) :=
    fun z j => z ⟨t j.1.succ, hright j⟩ - z ⟨t j.1.castSucc, hleft j⟩
  have hψ : Measurable ψ := Measurable.of_eval fun j =>
    (measurable_pi_apply (⟨t j.1.succ, hright j⟩ : Set.Iic (t i.castSucc))).sub
      (measurable_pi_apply (⟨t j.1.castSucc, hleft j⟩ : Set.Iic (t i.castSucc)))
  exact (hindep _ _ htime).comp measurable_id hψ

theorem isPreBrownianReal_of_gaussian_increments_indep_history
    {Ω : Type u_7} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ}
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ u v, u ≤ v → HasLaw
      (fun ω => X v ω - X u ω) (gaussianReal 0 (v - u)) P)
    (hindep : ∀ u v, u ≤ v → IndepFun
      (fun ω => X v ω - X u ω)
      (fun ω (s : Set.Iic u) => X s ω) P) :
    IsPreBrownianReal X P := by
  apply HasIndepIncrements.isPreBrownianReal_of_hasLaw
    (incr := hasIndepIncrements_of_indep_history hindep)
  intro t
  have h := hlaw 0 t (show 0 ≤ t from zero_le)
  simp only [tsub_zero] at h
  apply h.congr
  filter_upwards [hzero] with ω hω
  simp [hω]

theorem iIndepFun_coordinates_of_gaussian_indep_increments
    {Ω : Type u_8} {F : Type u_9} [MeasurableSpace Ω] [Fintype F]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → (F → ℝ)}
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hgauss : ∀ t, HasGaussianLaw (X t) P)
    (hcoords : ∀ t, iIndepFun (fun i ω => X t ω i) P)
    (hincr : HasIndepIncrements X P) :
    iIndepFun (fun i ω t => X t ω i) P := by
  have hprocess : IsGaussianProcess X P :=
    hincr.isGaussianProcess hgauss hzero
  have hjoint : IsGaussianProcess
      (fun (p : (i : F) × ℝ≥0) ω => X p.2 ω p.1) P :=
    (hprocess.comp_right (fun p : (i : F) × ℝ≥0 => p.2)).comp_left
      (fun p => ContinuousLinearMap.proj p.1)
  have hmem (i : F) (t : ℝ≥0) : MemLp (fun ω => X t ω i) 2 P :=
    (hgauss t |>.eval i).memLp_two
  apply hjoint.iIndepFun_of_covariance_eq_zero
    (fun i t => (hgauss t |>.eval i).aemeasurable)
  intro i j hij s t
  wlog hst : s ≤ t generalizing i j s t
  · rw [covariance_comm]
    exact this j i hij.symm t s (le_of_not_ge hst)
  have hind : IndepFun (fun ω => X s ω i) (fun ω => X t ω j - X s ω j) P :=
    (hincr.indepFun_eval_sub (show 0 ≤ s from zero_le) hst hzero).comp
      (measurable_pi_apply i) (measurable_pi_apply j)
  have hsplit : (fun ω => X t ω j) =
      (fun ω => X s ω j) + (fun ω => X t ω j - X s ω j) := by
    ext ω
    simp
  rw [hsplit]
  change cov[fun ω => X s ω i,
    (fun ω => X s ω j) + ((fun ω => X t ω j) - (fun ω => X s ω j)); P] = 0
  rw [covariance_add_right (hmem i s) (hmem j s)
    ((hmem j t).sub (hmem j s)),
    ((hcoords s).indepFun hij).covariance_eq_zero (hmem i s) (hmem j s), zero_add]
  exact hind.covariance_eq_zero (hmem i s) ((hmem j t).sub (hmem j s))

theorem finite_independent_preBrownian_of_gaussian_increments
    {Ω : Type u_10} {F : Type u_11} [MeasurableSpace Ω] [Fintype F]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → (F → ℝ)}
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ u v, u ≤ v → HasLaw
      (fun ω i => X v ω i - X u ω i)
      (Measure.pi (fun _ : F => gaussianReal 0 (v - u))) P)
    (hindep : ∀ u v, u ≤ v → IndepFun
      (fun ω => X v ω - X u ω)
      (fun ω (s : Set.Iic u) => X s ω) P) :
    (∀ i, IsPreBrownianReal (fun t ω => X t ω i) P) ∧
      iIndepFun (fun i ω t => X t ω i) P := by
  have hincr : HasIndepIncrements X P :=
    hasIndepIncrements_of_indep_history hindep
  have heval (t : ℝ≥0) : HasLaw (X t)
      (Measure.pi (fun _ : F => gaussianReal 0 t)) P := by
    have h := hlaw 0 t (show 0 ≤ t from zero_le)
    simp only [tsub_zero] at h
    apply h.congr
    filter_upwards [hzero] with ω hω
    ext i
    simp [hω]
  have hcoord (t : ℝ≥0) (i : F) : HasLaw (fun ω => X t ω i)
      (gaussianReal 0 t) P :=
    (measurePreserving_eval (fun _ : F => gaussianReal 0 t) i).hasLaw.comp (heval t)
  have hcoords (t : ℝ≥0) : iIndepFun (fun i ω => X t ω i) P :=
    (iIndepFun_iff_hasLaw_pi_pi (hcoord t)).mpr (heval t)
  constructor
  · intro i
    exact HasIndepIncrements.isPreBrownianReal_of_hasLaw
      (fun t => hcoord t i) (hincr.map (ContinuousLinearMap.proj i : (F → ℝ) →L[ℝ] ℝ))
  · exact iIndepFun_coordinates_of_gaussian_indep_increments hzero
      (fun t => (hcoords t).hasGaussianLaw (fun i => (hcoord t i).hasGaussianLaw))
      hcoords hincr

theorem independent_preBrownian_of_finite_gaussian_increments
    {Ω : Type u_12} {I : Type u_13} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : I → ℝ≥0 → Ω → ℝ}
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (hlaw : ∀ (S : Finset I) u v, u ≤ v → HasLaw
      (fun ω (i : S) => X i v ω - X i u ω)
      (Measure.pi (fun _ : S => gaussianReal 0 (v - u))) P)
    (hindep : ∀ (S : Finset I) u v, u ≤ v → IndepFun
      (fun ω (i : S) => X i v ω - X i u ω)
      (fun ω (s : Set.Iic u) (i : S) => X i s ω) P) :
    (∀ i, IsPreBrownianReal (X i) P) ∧
      iIndepFun (fun i ω t => X i t ω) P := by
  classical
  have hfinite (S : Finset I) :
      (∀ i : S, IsPreBrownianReal (X i) P) ∧
        iIndepFun (fun (i : S) ω t => X i t ω) P := by
    apply finite_independent_preBrownian_of_gaussian_increments
      (X := fun t ω (i : S) => X i t ω) _ (hlaw S) (hindep S)
    filter_upwards [ae_all_iff.mpr (fun i : S => hzero i)] with ω hω
    exact funext hω
  constructor
  · intro i
    exact (hfinite {i}).1 ⟨i, Finset.mem_singleton_self i⟩
  · exact iIndepFun_iff_finset.mpr (fun S => (hfinite S).2)

theorem independent_preBrownian_of_adapted_gaussian_increments
    {Ω : Type u_14} {I : Type u_15} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (H : Filtration ℝ≥0 mΩ) {X : I → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, Adapted H (X i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (hlaw : ∀ (S : Finset I) u v, u ≤ v → HasLaw
      (fun ω (i : S) => X i v ω - X i u ω)
      (Measure.pi (fun _ : S => gaussianReal 0 (v - u))) P)
    (hindep : ∀ (S : Finset I) u v, u ≤ v → Indep
      (MeasurableSpace.comap (fun ω (i : S) => X i v ω - X i u ω) inferInstance)
      (H u) P) :
    (∀ i, IsPreBrownianReal (X i) P) ∧
      iIndepFun (fun i ω t => X i t ω) P := by
  apply independent_preBrownian_of_finite_gaussian_increments hzero hlaw
  intro S u v huv
  have hpast : Measurable[H u]
      (fun ω (s : Set.Iic u) (i : S) => X i s ω) := by
    let : MeasurableSpace Ω := H u
    apply Measurable.of_eval
    intro s
    apply Measurable.of_eval
    intro i
    exact (hX i).measurable_le s.2
  rw [IndepFun_iff_Indep, Indep_iff]
  intro A B hA hB
  exact (Indep_iff _ _ _).mp (hindep S u v huv) A B hA (hpast.comap_le _ hB)

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem336AdditiveD139

theorem independent_preBrownian_of_eventwise_characteristic
    {Ω : Type u_1} {I : Type u_2} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (H : Filtration ℝ≥0 mΩ) {X : I → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, Adapted H (X i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (hchar : ∀ (S : Finset I) (u v : ℝ≥0), u ≤ v →
      ∀ A : Set Ω, MeasurableSet[H u] A → ∀ θ : S → ℝ,
        (∫ ω in A, Complex.exp
          (((∑ i : S, θ i * (X i v ω - X i u ω) : ℝ) : ℂ) * Complex.I) ∂P) =
          ((P A).toReal : ℂ) * Complex.exp
            (- ((v - u : ℝ≥0) : ℂ) * ((∑ i : S, θ i ^ 2 : ℝ) : ℂ) / 2)) :
    (∀ i, IsPreBrownianReal (X i) P) ∧
      iIndepFun (fun i ω t => X i t ω) P := by
  classical
  have hmeas (S : Finset I) (u v : ℝ≥0) :
      Measurable (fun ω (i : S) => X i v ω - X i u ω) :=
    Measurable.of_eval fun i => (hX i).measurable.sub (hX i).measurable
  have hresult (S : Finset I) (u v : ℝ≥0) (huv : u ≤ v) :
      Measure.map (fun ω (i : S) => X i v ω - X i u ω) P =
          Measure.pi (fun _ : S => gaussianReal 0 (v - u)) ∧
        Indep (H u) (MeasurableSpace.comap
          (fun ω (i : S) => X i v ω - X i u ω) inferInstance) P := by
    apply CharacteristicLaw.gaussian_pi_law_and_independent_of_event_characteristic
      (hmeas S u v) (H.le u) (v - u)
    intro A hA θ
    simpa only [mul_comm, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_ofNat] using hchar S u v huv A hA θ
  apply independent_preBrownian_of_adapted_gaussian_increments H hX hzero
  · intro S u v huv
    exact ⟨(hmeas S u v).aemeasurable, (hresult S u v huv).1⟩
  · intro S u v huv
    exact (hresult S u v huv).2.symm

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace Problem336AdditiveD139.ContinuousPathLaw

section DenseEvaluations

variable {T : Type u_1} {D : Type u_2} {I : Type u_3} [TopologicalSpace T]

def familySamples (e : D → T) (f : I → C(T, ℝ)) : I × D → ℝ :=
  fun p => f p.1 (e p.2)

theorem continuous_familySamples (e : D → T) : Continuous (familySamples (I := I) e) := by
  apply continuous_pi
  intro p
  exact (continuous_eval_const (e p.2)).comp (continuous_apply p.1)

theorem familySamples_injective {e : D → T} (he : DenseRange e) :
    Function.Injective (familySamples (I := I) e) := by
  intro f g h
  funext i
  apply ContinuousMap.coe_injective
  apply he.equalizer (f i).continuous (g i).continuous
  funext d
  exact congrFun h (i, d)

variable [Countable D] [Countable I]
variable [PolishSpace C(T, ℝ)] [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]

theorem measurableEmbedding_familySamples {e : D → T} (he : DenseRange e) :
    MeasurableEmbedding (familySamples (I := I) e) :=
  (continuous_familySamples e).measurableEmbedding (familySamples_injective he)

theorem measurable_iff_dense_evaluations {Ω : Type u_4} [MeasurableSpace Ω]
    {e : D → T} (he : DenseRange e) {X : Ω → I → C(T, ℝ)} :
    Measurable X ↔ ∀ i d, Measurable (fun ω => X ω i (e d)) := by
  rw [← (measurableEmbedding_familySamples (I := I) he).measurable_comp_iff]
  simp only [measurable_pi_iff, Function.comp_def, familySamples]
  exact ⟨fun h i d => h (i, d), fun h p => h p.1 p.2⟩

theorem measure_eq_of_dense_finiteDimensional {e : D → T} (he : DenseRange e)
    {μ ν : Measure (I → C(T, ℝ))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ S : Finset (I × D),
      μ.map (fun f => S.restrict (familySamples e f)) =
        ν.map (fun f => S.restrict (familySamples e f))) : μ = ν := by
  have hs := (measurableEmbedding_familySamples (I := I) he).measurable
  apply (measurableEmbedding_familySamples (I := I) he).map_injective
  apply (isProjectiveLimit_map hs.aemeasurable).unique
  intro S
  rw [Measure.map_map (Finset.measurable_restrict S) hs]
  exact (h S).symm

theorem aemeasurable_iff_dense_evaluations {Ω : Type u_5} [MeasurableSpace Ω]
    {P : Measure Ω} {e : D → T} (he : DenseRange e) {X : Ω → I → C(T, ℝ)} :
    AEMeasurable X P ↔ ∀ i d, AEMeasurable (fun ω => X ω i (e d)) P := by
  rw [← (measurableEmbedding_familySamples (I := I) he).aemeasurable_comp_iff]
  simp only [aemeasurable_pi_iff, Function.comp_def, familySamples]
  exact ⟨fun h i d => h (i, d), fun h p => h p.1 p.2⟩

def bundlePaths {Ω : Type u_6} (Z : Ω → I → T → ℝ) : Ω → I → C(T, ℝ) :=
  fun ω i => ContinuousMap.mkD (Z ω i) 0

theorem aemeasurable_bundlePaths {Ω : Type u_7} [MeasurableSpace Ω]
    {P : Measure Ω} {e : D → T} (he : DenseRange e) {Z : Ω → I → T → ℝ}
    (hm : ∀ i d, AEMeasurable (fun ω => Z ω i (e d)) P)
    (hc : ∀ i, ∀ᵐ ω ∂P, Continuous (Z ω i)) :
    AEMeasurable (bundlePaths Z) P := by
  apply (aemeasurable_iff_dense_evaluations he).2
  intro i d
  apply (hm i d).congr
  filter_upwards [hc i] with ω hω
  simp only [bundlePaths, ContinuousMap.mkD_apply_of_continuous hω]

omit [Countable I] [PolishSpace C(T, ℝ)] [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)] in

theorem bundlePaths_eval_ae_eq {Ω : Type u_8} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → I → T → ℝ}
    (hc : ∀ i, ∀ᵐ ω ∂P, Continuous (Z ω i)) (i : I) (t : T) :
    (fun ω => bundlePaths Z ω i t) =ᵐ[P] (fun ω => Z ω i t) := by
  filter_upwards [hc i] with ω hω
  simp only [bundlePaths, ContinuousMap.mkD_apply_of_continuous hω]

theorem exists_measurable_path_version {Ω : Type u_9} [MeasurableSpace Ω]
    {P : Measure Ω} {e : D → T} (he : DenseRange e) {Z : Ω → I → T → ℝ}
    (hm : ∀ i d, AEMeasurable (fun ω => Z ω i (e d)) P)
    (hc : ∀ i, ∀ᵐ ω ∂P, Continuous (Z ω i)) :
    ∃ X : Ω → I → C(T, ℝ), Measurable X ∧
      ∀ i t, (fun ω => X ω i t) =ᵐ[P] (fun ω => Z ω i t) := by
  have h := aemeasurable_bundlePaths he hm hc
  refine ⟨h.mk _, h.measurable_mk, ?_⟩
  intro i t
  refine Filter.EventuallyEq.trans ?_ (bundlePaths_eval_ae_eq hc i t)
  filter_upwards [h.ae_eq_mk] with ω hω
  exact congrArg (fun f : I → C(T, ℝ) => f i t) hω.symm

theorem identDistrib_of_dense_finiteDimensional
    {Ω : Type u_10} {Ω' : Type u_11} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {e : D → T} (he : DenseRange e)
    {X : Ω → I → C(T, ℝ)} {Y : Ω' → I → C(T, ℝ)}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (h : ∀ S : Finset (I × D),
      IdentDistrib (fun ω => S.restrict (familySamples e (X ω)))
        (fun ω => S.restrict (familySamples e (Y ω))) P Q) :
    IdentDistrib X Y P Q := by
  refine ⟨hX, hY, measure_eq_of_dense_finiteDimensional he ?_⟩
  intro S
  have hs : Measurable (fun f : I → C(T, ℝ) => S.restrict (familySamples e f)) :=
    (Finset.measurable_restrict S).comp (continuous_familySamples e).measurable
  rw [AEMeasurable.map_map_of_aemeasurable hs.aemeasurable hX,
    AEMeasurable.map_map_of_aemeasurable hs.aemeasurable hY]
  exact (h S).map_eq

end DenseEvaluations

def rationalTime (q : ℚ) : ℝ≥0 := Real.toNNReal (q : ℝ)

theorem denseRange_rationalTime : DenseRange rationalTime := by
  have hs : Function.Surjective Real.toNNReal := fun x => ⟨x, by simp⟩
  exact hs.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal

section NonnegativeRealTime

variable {I : Type u_12} [Countable I]
variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

theorem measure_eq_of_rational_finiteDimensional
    {μ ν : Measure (I → C(ℝ≥0, ℝ))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ S : Finset (I × ℚ),
      μ.map (fun f => S.restrict (familySamples rationalTime f)) =
        ν.map (fun f => S.restrict (familySamples rationalTime f))) : μ = ν :=
  measure_eq_of_dense_finiteDimensional denseRange_rationalTime h

theorem measurable_iff_rational_evaluations {Ω : Type u_13} [MeasurableSpace Ω]
    {X : Ω → I → C(ℝ≥0, ℝ)} :
    Measurable X ↔ ∀ i q, Measurable (fun ω => X ω i (rationalTime q)) :=
  measurable_iff_dense_evaluations denseRange_rationalTime

end NonnegativeRealTime

end Problem336AdditiveD139.ContinuousPathLaw

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace Problem336AdditiveD139.ContinuousPathLaw

section FiniteEvaluations

variable {Ω : Type u_1} {Ω' : Type u_2} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} {Q : Measure Ω'}
variable {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ω' → ℝ}

theorem preBrownian_finite_eval_identDistrib
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    {J : Type u_3} [Fintype J] (t : J → ℝ≥0) :
    IdentDistrib (fun ω j => B (t j) ω) (fun ω j => C (t j) ω) P Q := by
  classical
  let S : Finset ℝ≥0 := Finset.univ.image t
  let r : (S → ℝ) → J → ℝ := fun f j => f ⟨t j, Finset.mem_image.mpr
    ⟨j, Finset.mem_univ j, rfl⟩⟩
  have hr : Measurable r := Measurable.of_eval fun j => measurable_pi_apply _
  exact ((hB.hasLaw S).identDistrib (hC.hasLaw S)).comp hr

theorem preBrownian_rational_identDistrib
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q) :
    IdentDistrib (fun ω q => B (rationalTime q) ω)
      (fun ω q => C (rationalTime q) ω) P Q := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let : IsProbabilityMeasure Q := (hC.hasLaw_eval 0).isProbabilityMeasure
  have hmB : AEMeasurable (fun ω q => B (rationalTime q) ω) P :=
    aemeasurable_pi_lambda _ fun q => hB.aemeasurable _
  have hmC : AEMeasurable (fun ω q => C (rationalTime q) ω) Q :=
    aemeasurable_pi_lambda _ fun q => hC.aemeasurable _
  refine ⟨hmB, hmC, ?_⟩
  apply (isProjectiveLimit_map hmB).unique
  intro S
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict S).aemeasurable hmC]
  exact (preBrownian_finite_eval_identDistrib hB hC (fun q : S => rationalTime q)).map_eq.symm

end FiniteEvaluations

section ContinuousPaths

variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

def rationalSamples (f : C(ℝ≥0, ℝ)) : ℚ → ℝ := fun q => f (rationalTime q)

theorem measurableEmbedding_rationalSamples : MeasurableEmbedding rationalSamples := by
  have hc : Continuous rationalSamples := continuous_pi fun q => continuous_eval_const _
  apply hc.measurableEmbedding
  intro f g h
  apply ContinuousMap.coe_injective
  exact denseRange_rationalTime.equalizer f.continuous g.continuous h

def brownianPath {Ω : Type u_4} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : C(ℝ≥0, ℝ) :=
  ContinuousMap.mkD (fun t => B t ω) 0

variable {Ω : Type u_5} {Ω' : Type u_6} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} {Q : Measure Ω'}
variable {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ω' → ℝ}

omit [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)] in
theorem brownianPath_samples_ae_eq (hB : IsBrownianReal B P) :
    (rationalSamples ∘ brownianPath B) =ᵐ[P]
      (fun ω q => B (rationalTime q) ω) := by
  filter_upwards [hB.cont] with ω hω
  funext q
  simp only [Function.comp_apply, rationalSamples, brownianPath,
    ContinuousMap.mkD_apply_of_continuous hω]

theorem aemeasurable_brownianPath (hB : IsBrownianReal B P) :
    AEMeasurable (brownianPath B) P := by
  apply measurableEmbedding_rationalSamples.aemeasurable_comp_iff.mp
  exact (aemeasurable_pi_lambda _ fun q => hB.aemeasurable (rationalTime q)).congr
    (brownianPath_samples_ae_eq hB).symm

theorem brownianPath_identDistrib (hB : IsBrownianReal B P) (hC : IsBrownianReal C Q) :
    IdentDistrib (brownianPath B) (brownianPath C) P Q := by
  refine ⟨aemeasurable_brownianPath hB, aemeasurable_brownianPath hC, ?_⟩
  apply measurableEmbedding_rationalSamples.map_injective
  rw [AEMeasurable.map_map_of_aemeasurable
      measurableEmbedding_rationalSamples.measurable.aemeasurable (aemeasurable_brownianPath hB),
    AEMeasurable.map_map_of_aemeasurable
      measurableEmbedding_rationalSamples.measurable.aemeasurable (aemeasurable_brownianPath hC)]
  exact (Measure.map_congr (brownianPath_samples_ae_eq hB)).trans
    ((preBrownian_rational_identDistrib hB.toIsPreBrownianReal hC.toIsPreBrownianReal).map_eq.trans
      (Measure.map_congr (brownianPath_samples_ae_eq hC)).symm)

theorem iIndepFun_paths_iff_rationalSamples {I : Type u_7}
    {X : I → Ω → C(ℝ≥0, ℝ)} :
    iIndepFun X P ↔ iIndepFun (fun i => rationalSamples ∘ X i) P := by
  constructor
  · intro h
    exact h.comp (fun _ => rationalSamples)
      (fun _ => measurableEmbedding_rationalSamples.measurable)
  · intro h
    have hi := h.comp (fun _ => measurableEmbedding_rationalSamples.invFun)
      (fun _ => measurableEmbedding_rationalSamples.measurable_invFun)
    convert hi using 1
    funext i ω
    exact (measurableEmbedding_rationalSamples.leftInverse_invFun (X i ω)).symm

theorem iIndepFun_brownianPath {I : Type u_8} {W : I → ℝ≥0 → Ω → ℝ}
    (hW : ∀ i, IsBrownianReal (W i) P)
    (hi : iIndepFun (fun i ω q => W i (rationalTime q) ω) P) :
    iIndepFun (fun i => brownianPath (W i)) P := by
  apply iIndepFun_paths_iff_rationalSamples.mpr
  exact iIndepFun.congr (fun i => (brownianPath_samples_ae_eq (hW i)).symm) hi

theorem map_brownianPath_family_eq_infinitePi {I : Type u_9} [Countable I]
    [IsProbabilityMeasure P] {W : I → ℝ≥0 → Ω → ℝ}
    (hW : ∀ i, IsBrownianReal (W i) P)
    (hi : iIndepFun (fun i ω q => W i (rationalTime q) ω) P)
    (hC : IsBrownianReal C Q) :
    P.map (fun ω i => brownianPath (W i) ω) =
      Measure.infinitePi (fun _ : I => Q.map (brownianPath C)) := by
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map₀'
    (fun i => aemeasurable_brownianPath (hW i))).mp (iIndepFun_brownianPath hW hi)]
  congr 1
  funext i
  exact (brownianPath_identDistrib (hW i) hC).map_eq

end ContinuousPaths

end Problem336AdditiveD139.ContinuousPathLaw

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem336AdditiveD139

variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

theorem exists_measurable_iid_brownian_path_version
    {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω] [Countable I]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : Measure C(ℝ≥0, ℝ))
    (hν : IsBrownianReal (fun t (w : C(ℝ≥0, ℝ)) => w t) ν)
    {X : I → ℝ≥0 → Ω → ℝ}
    (hpre : ∀ i, IsPreBrownianReal (X i) P)
    (hindep : iIndepFun (fun i ω t => X i t ω) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t => X i t ω)) :
    ∃ W : Ω → I → C(ℝ≥0, ℝ), Measurable W ∧
      Measure.map W P = Measure.infinitePi (fun _ : I => ν) ∧
      ∀ᵐ ω ∂P, ∀ i t, W ω i t = X i t ω := by
  let R : Ω → I → C(ℝ≥0, ℝ) :=
    fun ω i => ContinuousPathLaw.brownianPath (X i) ω
  have hBrown (i : I) : IsBrownianReal (X i) P := ⟨hpre i, hcont i⟩
  have hm : AEMeasurable R P :=
    aemeasurable_pi_lambda _ fun i => ContinuousPathLaw.aemeasurable_brownianPath (hBrown i)
  have hrational : iIndepFun
      (fun i ω q => X i (ContinuousPathLaw.rationalTime q) ω) P :=
    hindep.comp (fun _ f q => f (ContinuousPathLaw.rationalTime q))
      (fun _ => Measurable.of_eval fun q => measurable_pi_apply _)
  have hcanon : ContinuousPathLaw.brownianPath
      (fun t (w : C(ℝ≥0, ℝ)) => w t) = id := by
    funext w
    apply ContinuousMap.coe_injective
    funext t
    simp only [ContinuousPathLaw.brownianPath,
      ContinuousMap.mkD_apply_of_continuous w.continuous, id_eq]
  have hlaw : Measure.map R P = Measure.infinitePi (fun _ : I => ν) := by
    have h := ContinuousPathLaw.map_brownianPath_family_eq_infinitePi hBrown hrational hν
    simpa only [hcanon, Measure.map_id] using h
  refine ⟨hm.mk R, hm.measurable_mk, ?_, ?_⟩
  · exact (Measure.map_congr hm.ae_eq_mk.symm).trans hlaw
  · filter_upwards [hm.ae_eq_mk, ae_all_iff.mpr hcont] with ω he hc
    intro i t
    rw [← he]
    simp only [R, ContinuousPathLaw.brownianPath,
      ContinuousMap.mkD_apply_of_continuous (hc i)]

theorem exists_iid_path_version_of_eventwise_characteristic
    {Ω : Type u_3} {I : Type u_4} [mΩ : MeasurableSpace Ω] [Countable I]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : Measure C(ℝ≥0, ℝ))
    (hν : IsBrownianReal (fun t (w : C(ℝ≥0, ℝ)) => w t) ν)
    (H : Filtration ℝ≥0 mΩ) {X : I → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, Adapted H (X i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t => X i t ω))
    (hchar : ∀ (S : Finset I) (u v : ℝ≥0), u ≤ v →
      ∀ A : Set Ω, MeasurableSet[H u] A → ∀ θ : S → ℝ,
        (∫ ω in A, Complex.exp
          (((∑ i : S, θ i * (X i v ω - X i u ω) : ℝ) : ℂ) * Complex.I) ∂P) =
          ((P A).toReal : ℂ) * Complex.exp
            (- ((v - u : ℝ≥0) : ℂ) * ((∑ i : S, θ i ^ 2 : ℝ) : ℂ) / 2)) :
    ∃ W : Ω → I → C(ℝ≥0, ℝ), Measurable W ∧
      Measure.map W P = Measure.infinitePi (fun _ : I => ν) ∧
      ∀ᵐ ω ∂P, ∀ i t, W ω i t = X i t ω := by
  obtain ⟨hpre, hindep⟩ := independent_preBrownian_of_eventwise_characteristic H hX hzero hchar
  exact exists_measurable_iid_brownian_path_version ν hν hpre hindep hcont

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem336AdditiveD139

theorem independent_preBrownian_of_local_characteristic
    {Ω : Type u_1} {I : Type u_2} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (H : Filtration ℝ≥0 mΩ) {X : I → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, Adapted H (X i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (hlocal : ∀ (S : Finset I) (θ : S → ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : ℝ≥0, u ≤ v → (v : ℝ) - u ≤ 1 → ∀ᵐ ω ∂P,
        ‖P[fun ω => Complex.exp (Complex.I *
          ((∑ i : S, θ i * (X i v ω - X i u ω) : ℝ) : ℂ)) | H u] ω -
          (Real.exp (-((v : ℝ) - u) * (∑ i : S, θ i ^ 2) / 2) : ℂ)‖ ≤
            C * ((v : ℝ) - u) * Real.sqrt ((v : ℝ) - u)) :
    (∀ i, IsPreBrownianReal (X i) P) ∧
      iIndepFun (fun i ω t => X i t ω) P := by
  classical
  have hresult (S : Finset I) (u v : ℝ≥0) (huv : u ≤ v) :=
    InnovationCharacteristic.gaussian_increment_law_of_local_characteristic_nnreal
      (fun t => H t) (fun _ _ h => H.mono h) H.le (fun t ω (i : S) => X i t ω)
      (fun t i => (hX i t).stronglyMeasurable)
      (fun θ => by
        simpa only [InnovationCharacteristic.phase, mul_comm] using hlocal S θ) huv
  apply independent_preBrownian_of_adapted_gaussian_increments H hX hzero
  · intro S u v huv
    refine ⟨?_, (hresult S u v huv).1⟩
    exact (Measurable.of_eval fun (i : S) =>
      ((hX i).measurable (i := v)).sub ((hX i).measurable (i := u))).aemeasurable
  · intro S u v huv
    exact (hresult S u v huv).2.symm

variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

theorem exists_iid_path_version_of_local_characteristic
    {Ω : Type u_3} {I : Type u_4} [mΩ : MeasurableSpace Ω] [Countable I]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : Measure C(ℝ≥0, ℝ))
    (hν : IsBrownianReal (fun t (w : C(ℝ≥0, ℝ)) => w t) ν)
    (H : Filtration ℝ≥0 mΩ) {X : I → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, Adapted H (X i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t => X i t ω))
    (hlocal : ∀ (S : Finset I) (θ : S → ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : ℝ≥0, u ≤ v → (v : ℝ) - u ≤ 1 → ∀ᵐ ω ∂P,
        ‖P[fun ω => Complex.exp (Complex.I *
          ((∑ i : S, θ i * (X i v ω - X i u ω) : ℝ) : ℂ)) | H u] ω -
          (Real.exp (-((v : ℝ) - u) * (∑ i : S, θ i ^ 2) / 2) : ℂ)‖ ≤
            C * ((v : ℝ) - u) * Real.sqrt ((v : ℝ) - u)) :
    ∃ W : Ω → I → C(ℝ≥0, ℝ), Measurable W ∧
      Measure.map W P = Measure.infinitePi (fun _ : I => ν) ∧
      ∀ᵐ ω ∂P, ∀ i t, W ω i t = X i t ω := by
  obtain ⟨hpre, hindep⟩ :=
    independent_preBrownian_of_local_characteristic H hX hzero hlocal
  exact exists_measurable_iid_brownian_path_version ν hν hpre hindep hcont

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped Topology NNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace Problem336AdditiveD139.InnovationAdapted

variable {Ω : Type u_1} {I : Type u_2} {mΩ : MeasurableSpace Ω}

theorem measurable_history_coordinates
    (H : Filtration ℝ mΩ) (Y : ℝ → Ω → I → ℝ)
    (hY : ∀ i, Adapted H (fun t ω => Y t ω i))
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i)) (T : ℝ) :
    Measurable[Subtype.instMeasurableSpace.prod (H T)]
      (fun p : Set.Iic T × Ω => Y p.1 p.2) := by
  let : MeasurableSpace Ω := H T
  apply Measurable.of_eval
  intro i
  exact ((hY i).stronglyAdapted.isStronglyProgressive_of_continuous
    (fun ω => hcont ω i) T).measurable

theorem progressive_drift
    (H : Filtration ℝ mΩ) (Y : ℝ → Ω → I → ℝ)
    (hY : ∀ i, Adapted H (fun t ω => Y t ω i))
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (i : I) : IsProgressive H (fun t ω => b t (Y t ω) i) := by
  intro T
  exact (hb i).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_history_coordinates H Y hY hcont T))

theorem measurable_intervalIntegral_of_history
    (m : MeasurableSpace Ω) (f : ℝ → Ω → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hf : Measurable[Subtype.instMeasurableSpace.prod m]
      (fun p : Set.Iic T × Ω => f p.1 p.2)) :
    Measurable[m] (fun ω => ∫ s in (0 : ℝ)..T, f s ω) := by
  let : MeasurableSpace Ω := m
  have hsub : Measurable (fun p : Set.Ioc (0 : ℝ) T × Ω =>
      ((⟨p.1.1, p.1.2.2⟩ : Set.Iic T), p.2)) := by
    exact ((measurable_subtype_coe.comp measurable_fst).subtype_mk).prodMk measurable_snd
  have hjoint : Measurable (fun p : Set.Ioc (0 : ℝ) T × Ω => f p.1 p.2) :=
    hf.comp hsub
  let : IsFiniteMeasure (volume : Measure (Set.Ioc (0 : ℝ) T)) :=
    ⟨by rw [Measure.Subtype.volume_univ measurableSet_Ioc.nullMeasurableSet]; simp⟩
  have hint : Measurable (fun ω => ∫ s : Set.Ioc (0 : ℝ) T, f s ω) :=
    hjoint.stronglyMeasurable.integral_prod_left'.measurable
  convert hint using 1
  funext ω
  rw [intervalIntegral.integral_of_le hT]
  exact (integral_subtype measurableSet_Ioc (fun s => f s ω)).symm

theorem measurable_driftIntegral
    (H : Filtration ℝ mΩ) (Y : ℝ → Ω → I → ℝ)
    (hY : ∀ i, Adapted H (fun t ω => Y t ω i))
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (i : I) (T : ℝ) (hT : 0 ≤ T) :
    Measurable[H T] (fun ω => ∫ s in (0 : ℝ)..T, b s (Y s ω) i) :=
  measurable_intervalIntegral_of_history (H T) _ T hT
    (progressive_drift H Y hY hcont b hb i T)

theorem measurable_innovation
    (H : Filtration ℝ mΩ) (Y : ℝ → Ω → I → ℝ)
    (hY : ∀ i, Adapted H (fun t ω => Y t ω i))
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (i : I) (T : ℝ) (hT : 0 ≤ T) :
    Measurable[H T] (fun ω => Y T ω i - ∫ s in (0 : ℝ)..T, b s (Y s ω) i) :=
  (hY i T).sub (measurable_driftIntegral H Y hY hcont b hb i T hT)

theorem measurable_innovation_increment
    (H : Filtration ℝ mΩ) (Y : ℝ → Ω → I → ℝ)
    (hY : ∀ i, Adapted H (fun t ω => Y t ω i))
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (i : I) (u v T : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huT : u ≤ T) (hvT : v ≤ T) :
    Measurable[H T] (fun ω =>
      (Y v ω i - ∫ s in (0 : ℝ)..v, b s (Y s ω) i) -
      (Y u ω i - ∫ s in (0 : ℝ)..u, b s (Y s ω) i)) := by
  exact ((measurable_innovation H Y hY hcont b hb i v hv).mono
    (H.mono hvT) le_rfl).sub
    ((measurable_innovation H Y hY hcont b hb i u hu).mono (H.mono huT) le_rfl)

theorem intervalIntegrable_drift
    (Y : ℝ → I → ℝ) (hY : ∀ i, Continuous (fun t => Y t i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (C : ℝ) (hbound : ∀ t y i, |b t y i| ≤ C) (i : I) (u v : ℝ) :
    IntervalIntegrable (fun t => b t (Y t) i) volume u v := by
  have hm : Measurable (fun t => b t (Y t) i) :=
    (hb i).comp (measurable_id.prodMk (Measurable.of_eval (fun j => (hY j).measurable)))
  rw [intervalIntegrable_iff]
  exact IntegrableOn.of_bound (by simp [Set.uIoc]) hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hbound t (Y t) i))

theorem continuous_driftIntegral
    (Y : ℝ → I → ℝ) (hY : ∀ i, Continuous (fun t => Y t i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (C : ℝ) (hbound : ∀ t y i, |b t y i| ≤ C) (i : I) :
    Continuous (fun t => ∫ s in (0 : ℝ)..t, b s (Y s) i) :=
  intervalIntegral.continuous_primitive
    (fun u v => intervalIntegrable_drift Y hY b hb C hbound i u v) 0

theorem continuous_innovation
    (Y : ℝ → I → ℝ) (hY : ∀ i, Continuous (fun t => Y t i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (C : ℝ) (hbound : ∀ t y i, |b t y i| ≤ C) (i : I) :
    Continuous (fun t => Y t i - ∫ s in (0 : ℝ)..t, b s (Y s) i) :=
  (hY i).sub (continuous_driftIntegral Y hY b hb C hbound i)

def nonnegativeTimeExtension (H : Filtration ℝ≥0 mΩ) : Filtration ℝ mΩ where
  seq t := H t.toNNReal
  mono' := fun _ _ h => H.mono (Real.toNNReal_mono h)
  le' t := H.le t.toNNReal

theorem measurable_innovation_nnreal
    (H : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → I → ℝ)
    (hY : ∀ i, Adapted H (fun t ω => Y t ω i))
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (i : I) (T : ℝ≥0) :
    Measurable[H T] (fun ω => Y T ω i -
      ∫ s in (0 : ℝ)..(T : ℝ), b s (Y s.toNNReal ω) i) := by
  have h := measurable_innovation (nonnegativeTimeExtension H)
    (fun t => Y t.toNNReal) (fun i t => hY i t.toNNReal)
    (fun ω i => (hcont ω i).comp continuous_real_toNNReal) b hb i T T.property
  change Measurable[H (T : ℝ).toNNReal] (fun ω => Y (T : ℝ).toNNReal ω i -
    ∫ s in (0 : ℝ)..(T : ℝ), b s (Y s.toNNReal ω) i) at h
  rw [Real.toNNReal_coe] at h
  exact h

end Problem336AdditiveD139.InnovationAdapted

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem336AdditiveD139.InnovationAdapted

variable {I : Type u_1} {Ω : Type u_2}

theorem continuous_innovation_nnreal
    (Y : ℝ≥0 → I → ℝ) (hY : ∀ i, Continuous (fun t => Y t i))
    (b : ℝ≥0 → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ≥0 × (I → ℝ) => b p.1 p.2 i))
    (C : ℝ) (hbound : ∀ t y i, |b t y i| ≤ C) (i : I) :
    Continuous (fun t : ℝ≥0 => Y t i -
      ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal (Y s.toNNReal) i) := by
  have hb' : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1.toNNReal p.2 i) := by
    intro j
    exact (hb j).comp (show Measurable (fun p : ℝ × (I → ℝ) =>
      (p.1.toNNReal, p.2)) by fun_prop)
  have h := continuous_innovation (fun t : ℝ => Y t.toNNReal)
    (fun j => (hY j).comp continuous_real_toNNReal)
    (fun t : ℝ => b t.toNNReal) hb' C
    (fun t y j => hbound t.toNNReal y j) i
  have h' := h.comp NNReal.continuous_coe
  change Continuous (fun t : ℝ≥0 => Y (t : ℝ).toNNReal i -
    ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal (Y s.toNNReal) i) at h'
  simpa only [Real.toNNReal_coe] using h'

theorem ae_continuous_innovation_nnreal
    [Countable I] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (Y : ℝ≥0 → Ω → I → ℝ)
    (hY : ∀ i, ∀ᵐ ω ∂μ, Continuous (fun t => Y t ω i))
    (b : ℝ≥0 → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ≥0 × (I → ℝ) => b p.1 p.2 i))
    (C : ℝ) (hbound : ∀ t y i, |b t y i| ≤ C) :
    ∀ᵐ ω ∂μ, ∀ i, Continuous (fun t : ℝ≥0 => Y t ω i -
      ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal (Y s.toNNReal ω) i) := by
  filter_upwards [ae_all_iff.mpr hY] with ω hω i
  exact continuous_innovation_nnreal (fun t => Y t ω) hω b hb C hbound i

end Problem336AdditiveD139.InnovationAdapted

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators

namespace Problem336AdditiveD139.ReferenceInnovationLaw

variable {I : Type u_1} {Ω : Type u_2} [MeasurableSpace Ω]

def process (B : ℝ≥0 → Ω → ℝ)
    (b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ)
    (i : I) (t : ℝ≥0) (ω : ReferenceObservation.Space I Ω) : ℝ :=
  ReferenceObservation.observation B i t ω -
    ∫ s in (0 : ℝ)..(t : ℝ), b i ω s.toNNReal

def realDrift (b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ)
    (i : I) (ω : ReferenceObservation.Space I Ω) (t : ℝ) : ℝ :=
  b i ω t.toNNReal

lemma measurable_realDrift
    {b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ}
    (hbm : ∀ i, Measurable (Function.uncurry (b i))) (i : I) :
    Measurable (Function.uncurry (realDrift b i)) := by
  exact (hbm i).comp (measurable_fst.prodMk
    (continuous_real_toNNReal.measurable.comp measurable_snd))

omit [MeasurableSpace Ω] in
lemma process_eq_innovation
    (B : ℝ≥0 → Ω → ℝ)
    (b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ)
    (i : I) (t : ℝ≥0) (ω : ReferenceObservation.Space I Ω) :
    process B b i t ω = InnovationCorrection.innovation
      (boolReal (ω.1 i)) (fun s => ReferenceObservation.noise B i s.toNNReal ω)
      (realDrift b i ω) t := by
  simp [process, InnovationCorrection.innovation, ReferenceObservation.observation,
    realDrift]

theorem local_characteristic_error
    (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B (ν : Measure Ω))
    (hBm : ∀ t, Measurable (B t))
    (b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ)
    (hbm : ∀ i, Measurable (Function.uncurry (b i)))
    (hb : ∀ i ω t, b i ω t ∈ Set.Icc (0 : ℝ) 1)
    (hpost : ∀ t i, (fun ω => b i ω t) =ᵐ[ReferenceObservation.law μ ν]
      (ReferenceObservation.law μ ν)[(fun ω => boolReal (ω.1 i)) |
        ObservationNoise.historySigma B t])
    (S : Finset I) (θ : I → ℝ) (u v : ℝ≥0) (huv : u ≤ v)
    (hsmall : (v : ℝ) - (u : ℝ) ≤ 1) :
    ∀ᵐ ω ∂ ReferenceObservation.law μ ν,
      ‖(ReferenceObservation.law μ ν)[(fun a => Complex.exp
          (((∑ i ∈ S, θ i * (process B b i v a - process B b i u a) : ℝ) : ℂ) *
            Complex.I)) | ObservationNoise.historySigma B u] ω -
          (Real.exp (-(((v : ℝ) - (u : ℝ)) * ∑ i ∈ S, θ i ^ 2) / 2) : ℂ)‖ ≤
        WeightedLocalInnovation.errorConstant S θ * ((v : ℝ) - (u : ℝ)) *
          Real.sqrt ((v : ℝ) - (u : ℝ)) := by
  classical
  let P := ReferenceObservation.law μ ν
  let X : I → ReferenceObservation.Space I Ω → ℝ := fun i ω => boolReal (ω.1 i)
  let N : I → ReferenceObservation.Space I Ω → ℝ → ℝ :=
    fun i ω s => ReferenceObservation.noise B i s.toNNReal ω
  let h : ℝ≥0 := v - u
  have hh : (h : ℝ) = (v : ℝ) - (u : ℝ) := NNReal.coe_sub huv
  have huv' : (u : ℝ) + (h : ℝ) = (v : ℝ) := by rw [hh]; ring
  let Q := WeightedLocalInnovation.noiseIncrement S θ N u v
  have hQm : Measurable Q := by
    unfold Q WeightedLocalInnovation.noiseIncrement N
    exact S.measurable_sum (fun i _ => measurable_const.mul
      ((ReferenceObservation.measurable_noise B hBm i _).sub
        (ReferenceObservation.measurable_noise B hBm i _)))
  have hQlaw : HasLaw Q (gaussianReal 0 (h * WeightedLocalInnovation.variance S θ)) P := by
    have hq := ObservationNoise.real_increment_hasLaw μ ν hB hBm
      u.coe_nonneg (show (u : ℝ) ≤ (v : ℝ) from huv) S θ
    have hv : ObservationNoise.incrementVariance ((v : ℝ) - (u : ℝ)).toNNReal S θ =
        h * WeightedLocalInnovation.variance S θ := by
      apply NNReal.coe_injective
      rw [ObservationNoise.incrementVariance_real (show (u : ℝ) ≤ (v : ℝ) from huv)]
      change ((v : ℝ) - (u : ℝ)) * (∑ i ∈ S, θ i ^ 2) =
        (h : ℝ) * (∑ i ∈ S, θ i ^ 2)
      rw [hh]
    rw [hv] at hq
    exact hq
  have hQi : Indep (MeasurableSpace.comap Q inferInstance)
      (ObservationNoise.realFiltration (I := I) hBm (u : ℝ)) P := by
    rw [ObservationNoise.realFiltration_apply, Real.toNNReal_coe]
    change IndepFun Q (ObservationNoise.history B u) P
    have hi := ObservationNoise.real_increment_indep_history μ ν hB hBm
      u.coe_nonneg (show (u : ℝ) ≤ (v : ℝ) from huv) S θ
    change IndepFun Q (ObservationNoise.history B (u : ℝ).toNNReal) P at hi
    rw [Real.toNNReal_coe] at hi
    exact hi
  have hlocal := WeightedLocalInnovation.innovation_characteristic_error
    (μ := P) S θ (ObservationNoise.realFiltration (I := I) hBm) (u : ℝ) h
    (by simpa only [hh] using hsmall)
    (X := X) (B := N) (b := realDrift b)
    (fun i _ => (measurable_of_finite boolReal).comp
      ((measurable_pi_apply i).comp measurable_fst))
    (fun i _ ω => ReferenceObservation.signal_real_mem_unitInterval i ω)
    (fun i _ => measurable_realDrift hbm i)
    (fun i _ ω t => hb i ω t.toNNReal)
    hQm.comap_le (by simpa only [huv'] using (comap_measurable Q).stronglyMeasurable)
    (by simpa only [huv'] using hQlaw)
    hQi
    (fun t _ i _ => hpost t.toNNReal i)
  rw [huv'] at hlocal
  have hvar : (WeightedLocalInnovation.variance S θ : ℝ) = ∑ i ∈ S, θ i ^ 2 := rfl
  simpa only [WeightedLocalInnovation.innovationIncrement, X, N,
    ← process_eq_innovation, ObservationNoise.realFiltration_apply,
    Real.toNNReal_coe, hvar, hh, P, mul_comm Complex.I] using hlocal

theorem local_characteristic_subtype
    (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B (ν : Measure Ω))
    (hBm : ∀ t, Measurable (B t))
    (b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ)
    (hbm : ∀ i, Measurable (Function.uncurry (b i)))
    (hb : ∀ i ω t, b i ω t ∈ Set.Icc (0 : ℝ) 1)
    (hpost : ∀ t i, (fun ω => b i ω t) =ᵐ[ReferenceObservation.law μ ν]
      (ReferenceObservation.law μ ν)[(fun ω => boolReal (ω.1 i)) |
        ObservationNoise.historySigma B t])
    (S : Finset I) (θ : S → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ≥0, u ≤ v → (v : ℝ) - u ≤ 1 →
      ∀ᵐ ω ∂ ReferenceObservation.law μ ν,
        ‖(ReferenceObservation.law μ ν)[(fun a => Complex.exp (Complex.I *
            ((∑ i : S, θ i * (process B b i v a - process B b i u a) : ℝ) : ℂ))) |
              ObservationNoise.historySigma B u] ω -
            (Real.exp (-((v : ℝ) - u) * (∑ i : S, θ i ^ 2) / 2) : ℂ)‖ ≤
          C * ((v : ℝ) - u) * Real.sqrt ((v : ℝ) - u) := by
  classical
  let θ' : I → ℝ := fun i => if hi : i ∈ S then θ ⟨i, hi⟩ else 0
  have hs (f : I → ℝ) : (∑ i ∈ S, θ' i * f i) = ∑ i : S, θ i * f i := by
    rw [← Finset.sum_coe_sort]
    simp [θ']
  have hv : (∑ i ∈ S, θ' i ^ 2) = ∑ i : S, θ i ^ 2 := by
    rw [← Finset.sum_coe_sort]
    simp [θ']
  refine ⟨WeightedLocalInnovation.errorConstant S θ',
    WeightedLocalInnovation.errorConstant_nonneg S θ', ?_⟩
  intro u v huv hsmall
  have h := local_characteristic_error μ ν B hB hBm b hbm hb hpost S θ' u v huv hsmall
  simpa only [hs, hv, neg_mul, mul_comm Complex.I] using h

variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

theorem exists_iid_path_version [Countable I]
    (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B (ν : Measure Ω))
    (hBm : ∀ t, Measurable (B t))
    (ρ : Measure C(ℝ≥0, ℝ))
    (hρ : IsBrownianReal (fun t (w : C(ℝ≥0, ℝ)) => w t) ρ)
    (b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ)
    (hbm : ∀ i, Measurable (Function.uncurry (b i)))
    (hb : ∀ i ω t, b i ω t ∈ Set.Icc (0 : ℝ) 1)
    (hpost : ∀ t i, (fun ω => b i ω t) =ᵐ[ReferenceObservation.law μ ν]
      (ReferenceObservation.law μ ν)[(fun ω => boolReal (ω.1 i)) |
        ObservationNoise.historySigma B t])
    (hadapt : ∀ i, Adapted (ObservationNoise.filtration (I := I) hBm) (process B b i))
    (hcont : ∀ i, ∀ᵐ ω ∂ ReferenceObservation.law μ ν,
      Continuous (fun t => process B b i t ω)) :
    ∃ W : ReferenceObservation.Space I Ω → I → C(ℝ≥0, ℝ), Measurable W ∧
      Measure.map W (ReferenceObservation.law μ ν) = Measure.infinitePi (fun _ : I => ρ) ∧
      ∀ᵐ ω ∂ ReferenceObservation.law μ ν, ∀ i t, W ω i t = process B b i t ω := by
  refine exists_iid_path_version_of_local_characteristic ρ hρ
    (ObservationNoise.filtration (I := I) hBm) hadapt ?_ hcont ?_
  · intro i
    filter_upwards [(ReferenceObservation.noise_isPreBrownian μ ν B hB i).eval_zero_ae_eq_zero]
      with ω hω
    simpa only [process, ReferenceObservation.observation, NNReal.coe_zero,
      zero_mul, zero_add, intervalIntegral.integral_same, sub_zero] using hω
  · exact local_characteristic_subtype μ ν B hB hBm b hbm hb hpost

def fieldDrift (B : ℝ≥0 → Ω → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (i : I) (ω : ReferenceObservation.Space I Ω) (t : ℝ≥0) : ℝ :=
  b t (fun j => ReferenceObservation.observation B j t ω) i

def fieldProcess (B : ℝ≥0 → Ω → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (i : I) (t : ℝ≥0) (ω : ReferenceObservation.Space I Ω) : ℝ :=
  ReferenceObservation.observation B i t ω - ∫ s in (0 : ℝ)..(t : ℝ),
    b s (fun j => ReferenceObservation.observation B j s.toNNReal ω) i

omit [MeasurableSpace Ω] [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)] in
lemma process_fieldDrift_eq (B : ℝ≥0 → Ω → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (i : I) (t : ℝ≥0) (ω : ReferenceObservation.Space I Ω) :
    process B (fieldDrift B b) i t ω = fieldProcess B b i t ω := by
  unfold process fieldDrift fieldProcess
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le t.coe_nonneg] at hs
  dsimp only
  rw [Real.coe_toNNReal _ hs.1]

omit [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)] in
lemma measurable_fieldDrift
    {B : ℝ≥0 → Ω → ℝ} (hBj : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    {b : ℝ → (I → ℝ) → I → ℝ}
    (hbm : Measurable (Function.uncurry b)) (i : I) :
    Measurable (Function.uncurry (fieldDrift B b i)) := by
  have hg : Measurable (fun p : ReferenceObservation.Space I Ω × ℝ≥0 =>
      ((p.2 : ℝ), fun j => ReferenceObservation.observation B j p.2 p.1)) :=
    (NNReal.continuous_coe.measurable.comp measurable_snd).prodMk
      (Measurable.of_eval fun j =>
        (ReferenceObservation.measurable_observation_joint B hBj j).comp measurable_swap)
  exact ((measurable_pi_apply i).comp hbm).comp hg

theorem exists_iid_field_innovation [Countable I]
    (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B (ν : Measure Ω))
    (hBm : ∀ t, Measurable (B t))
    (hBj : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ w, Continuous (fun t => B t w))
    (ρ : Measure C(ℝ≥0, ℝ))
    (hρ : IsBrownianReal (fun t (w : C(ℝ≥0, ℝ)) => w t) ρ)
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hbm : Measurable (Function.uncurry b))
    (hb : ∀ t y i, b t y i ∈ Set.Icc (0 : ℝ) 1)
    (hpost : ∀ (t : ℝ≥0) i, (fun ω : ReferenceObservation.Space I Ω =>
      b t (fun j => ReferenceObservation.observation B j t ω) i)
        =ᵐ[ReferenceObservation.law μ ν]
      (ReferenceObservation.law μ ν)[(fun ω => boolReal (ω.1 i)) |
        ObservationNoise.historySigma B t]) :
    ∃ W : ReferenceObservation.Space I Ω → I → C(ℝ≥0, ℝ), Measurable W ∧
      Measure.map W (ReferenceObservation.law μ ν) = Measure.infinitePi (fun _ : I => ρ) ∧
      ∀ᵐ ω ∂ ReferenceObservation.law μ ν, ∀ i t, W ω i t = fieldProcess B b i t ω := by
  have hcoord (i : I) : Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i) :=
    (measurable_pi_apply i).comp hbm
  have hadapt : ∀ i, Adapted (ObservationNoise.filtration (I := I) hBm)
      (process B (fieldDrift B b) i) := by
    intro i t
    have ha := InnovationAdapted.measurable_innovation_nnreal
      (ObservationNoise.filtration (I := I) hBm)
      (fun t ω j => ReferenceObservation.observation B j t ω)
      (fun j t => ObservationNoise.measurable_current_observation B t j)
      (fun ω j => ReferenceObservation.continuous_observation_path B hBc j ω)
      b hcoord i t
    change Measurable[ObservationNoise.historySigma B t]
      (fun ω => process B (fieldDrift B b) i t ω)
    simp_rw [process_fieldDrift_eq]
    exact ha
  have hcont : ∀ i, ∀ᵐ ω ∂ ReferenceObservation.law μ ν,
      Continuous (fun t => process B (fieldDrift B b) i t ω) := by
    intro i
    apply ae_of_all
    intro ω
    have hcoords (j : I) : Measurable (fun p : ℝ≥0 × (I → ℝ) =>
        b (p.1 : ℝ) p.2 j) :=
      (hcoord j).comp (NNReal.continuous_coe.measurable.comp measurable_fst |>.prodMk measurable_snd)
    have hc := InnovationAdapted.continuous_innovation_nnreal
      (fun t j => ReferenceObservation.observation B j t ω)
      (fun j => ReferenceObservation.continuous_observation_path B hBc j ω)
      (fun t => b (t : ℝ)) hcoords 1
      (fun t y j => by rw [abs_of_nonneg (hb t y j).1]; exact (hb t y j).2) i
    exact hc
  obtain ⟨W, hWm, hWlaw, hWeq⟩ := exists_iid_path_version μ ν B hB hBm ρ hρ
    (fieldDrift B b) (measurable_fieldDrift hBj hbm)
    (fun i ω t => hb t _ i) hpost hadapt hcont
  exact ⟨W, hWm, hWlaw, hWeq.mono (fun ω hω i t =>
    (hω i t).trans (process_fieldDrift_eq B b i t ω))⟩

theorem map_field_innovation_eq [Countable I]
    (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B (ν : Measure Ω))
    (hBm : ∀ t, Measurable (B t))
    (hBj : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ w, Continuous (fun t => B t w))
    (ρ : Measure C(ℝ≥0, ℝ))
    (hρ : IsBrownianReal (fun t (w : C(ℝ≥0, ℝ)) => w t) ρ)
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hbm : Measurable (Function.uncurry b))
    (hb : ∀ t y i, b t y i ∈ Set.Icc (0 : ℝ) 1)
    (hpost : ∀ (t : ℝ≥0) i, (fun ω : ReferenceObservation.Space I Ω =>
      b t (fun j => ReferenceObservation.observation B j t ω) i)
        =ᵐ[ReferenceObservation.law μ ν]
      (ReferenceObservation.law μ ν)[(fun ω => boolReal (ω.1 i)) |
        ObservationNoise.historySigma B t])
    (Z : ReferenceObservation.Space I Ω → I → C(ℝ≥0, ℝ))
    (hZ : ∀ ω i t, Z ω i t = fieldProcess B b i t ω) :
    Measure.map Z (ReferenceObservation.law μ ν) = Measure.infinitePi (fun _ : I => ρ) := by
  obtain ⟨W, _, hWlaw, hWeq⟩ :=
    exists_iid_field_innovation μ ν B hB hBm hBj hBc ρ hρ b hbm hb hpost
  have heq : Z =ᵐ[ReferenceObservation.law μ ν] W := by
    filter_upwards [hWeq] with ω hω
    funext i
    apply ContinuousMap.coe_injective
    funext t
    exact (hZ ω i t).trans (hω i t).symm
  exact (Measure.map_congr heq).trans hWlaw

end Problem336AdditiveD139.ReferenceInnovationLaw

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Problem336AdditiveD139
namespace BrownianBridge

variable {Ω : Type u_1} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

lemma independent_processes_jointGaussian {I : Type u_2} {T : Type u_3} (X : I → T → Ω → ℝ)
    (hX : ∀ i, IsGaussianProcess (X i) P)
    (hInd : iIndepFun (fun i ω s => X i s ω) P) :
    IsGaussianProcess (fun p : I × T => X p.1 p.2) P := by
  classical
  constructor
  intro S
  let K := S.image Prod.fst
  let J := S.image Prod.snd
  have hInd' := (iIndepFun.precomp (g := fun i : K => i.val) Subtype.val_injective hInd).comp
    (fun _ (x : T → ℝ) (s : J) => x s) (by fun_prop)
  have hG := hInd'.hasGaussianLaw (fun i : K => (hX i).hasGaussianLaw J)
  let L : (K → J → ℝ) →L[ℝ] (S → ℝ) :=
    { toFun := fun x p => x ⟨p.val.1, Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩
          ⟨p.val.2, Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact hG.map L

def bridge (B : ℝ≥0 → Ω → ℝ) (t s : ℝ≥0) (ω : Ω) : ℝ :=
  B s ω - (s : ℝ) / (t : ℝ) * B t ω

lemma bridge_aemeasurable (hB : IsPreBrownianReal B P) (t s : ℝ≥0) :
    AEMeasurable (bridge B t s) P :=
  (hB.aemeasurable s).sub ((hB.aemeasurable t).const_mul _)

lemma bridge_endpoint_jointGaussian (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    IsGaussianProcess
      (Sum.elim (fun s : Set.Iic t => bridge B t s) (fun _ : Unit => B t)) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro u
  cases u with
  | inl s =>
    refine ⟨{s.val, t},
      { toFun := fun x => x ⟨s.val, by simp⟩ -
          (s.val : ℝ) / (t : ℝ) * x ⟨t, by simp⟩
        map_add' := ?_
        map_smul' := ?_ }, ?_⟩
    · intro x y
      simp
      ring
    · intro c x
      simp
      ring
    · intro ω
      rfl
  | inr u =>
    refine ⟨{t},
      { toFun := fun x => x ⟨t, by simp⟩
        map_add' := by simp
        map_smul' := by simp }, ?_⟩
    intro ω
    rfl

lemma bridge_endpoint_covariance (hB : IsPreBrownianReal B P)
    {t s : ℝ≥0} (ht : 0 < t) (hs : s ≤ t) :
    cov[bridge B t s, B t; P] = 0 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hL (u : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  change cov[fun ω => B s ω - (s : ℝ) / (t : ℝ) * B t ω, B t; P] = 0
  rw [covariance_fun_sub_left (hL s) ((hL t).const_mul _) (hL t),
    covariance_const_mul_left, hB.covariance_eval, hB.covariance_eval,
    min_eq_left hs, min_self]
  have htr : (t : ℝ) ≠ 0 := ne_of_gt (show (0 : ℝ) < t from ht)
  simp [div_mul_cancel₀ _ htr]

theorem bridge_indep_endpoint (hB : IsPreBrownianReal B P)
    {t : ℝ≥0} (ht : 0 < t) :
    IndepFun (fun ω (s : Set.Iic t) => bridge B t s ω) (B t) P := by
  have h := (bridge_endpoint_jointGaussian hB t).indepFun_of_covariance_eq_zero
    (fun s => bridge_aemeasurable hB t s)
    (fun _ => hB.aemeasurable t)
    (fun s _ => bridge_endpoint_covariance hB ht s.property)
  exact h.comp measurable_id (measurable_pi_apply ())

lemma family_bridge_endpoint_jointGaussian {I : Type u_4} (B : I → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hInd : iIndepFun (fun i ω s => B i s ω) P) (t : ℝ≥0) :
    IsGaussianProcess
      (Sum.elim (fun p : I × Set.Iic t => bridge (B p.1) t p.2)
        (fun i : I => B i t)) P := by
  classical
  apply (independent_processes_jointGaussian B
    (fun i => (hB i).isGaussianProcess) hInd).of_isGaussianProcess
  intro u
  cases u with
  | inl p =>
    refine ⟨{(p.1, p.2.val), (p.1, t)},
      { toFun := fun x => x ⟨(p.1, p.2.val), by simp⟩ -
          (p.2.val : ℝ) / (t : ℝ) * x ⟨(p.1, t), by simp⟩
        map_add' := ?_
        map_smul' := ?_ }, ?_⟩
    · intro x y
      simp
      ring
    · intro c x
      simp
      ring
    · intro ω
      rfl
  | inr i =>
    refine ⟨{(i, t)},
      { toFun := fun x => x ⟨(i, t), by simp⟩
        map_add' := by simp
        map_smul' := by simp }, ?_⟩
    intro ω
    rfl

theorem family_bridge_indep_endpoints {I : Type u_5} (B : I → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hInd : iIndepFun (fun i ω s => B i s ω) P) {t : ℝ≥0} (ht : 0 < t) :
    IndepFun (fun ω (p : I × Set.Iic t) => bridge (B p.1) t p.2 ω)
      (fun ω i => B i t ω) P := by
  apply (family_bridge_endpoint_jointGaussian B hB hInd t).indepFun_of_covariance_eq_zero
    (fun p => bridge_aemeasurable (hB p.1) t p.2)
    (fun i => (hB i).aemeasurable t)
  intro p j
  by_cases hij : p.1 = j
  · subst j
    exact bridge_endpoint_covariance (hB p.1) ht p.2.property
  · have h := (hInd.indepFun hij).comp
      (show Measurable (fun x : ℝ≥0 → ℝ => x p.2 - (p.2.val : ℝ) / (t : ℝ) * x t) by
        fun_prop)
      (measurable_pi_apply t)
    exact h.covariance_eq_zero
      (((hB p.1).isGaussianProcess.hasGaussianLaw_eval p.2).memLp_two.sub
        (((hB p.1).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.const_mul _))
      ((hB j).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

end BrownianBridge
end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139

theorem indepFun_pair_reassociate
    {Ω : Type u_1} {α : Type u_2} {β : Type u_3} {γ : Type u_4} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (mX : Measurable X) (mY : Measurable Y) (mZ : Measurable Z)
    (hXZ : IndepFun X Z P) (hY : IndepFun Y (fun ω => (X ω, Z ω)) P) :
    IndepFun X (fun ω => (Y ω, Z ω)) P := by
  have hYZ : IndepFun Y Z P := by
    simpa only [Function.comp_def, id_eq] using hY.comp measurable_id measurable_snd
  apply (indepFun_iff_map_prod_eq_prod_map_map mX.aemeasurable
    (mY.prodMk mZ).aemeasurable).2
  rw [hYZ.map_prod_eq_prod_map_map mY.aemeasurable mZ.aemeasurable]
  apply Measure.ext_prod₃
  intro s u v hs hu hv
  rw [Measure.map_apply (mX.prodMk (mY.prodMk mZ)) (hs.prod (hu.prod hv)),
    Measure.prod_prod, Measure.prod_prod,
    Measure.map_apply mX hs, Measure.map_apply mY hu, Measure.map_apply mZ hv]
  have hY' := (indepFun_iff_measure_inter_preimage_eq_mul.1 hY)
    u (s ×ˢ v) hu (hs.prod hv)
  have hXZ' := (indepFun_iff_measure_inter_preimage_eq_mul.1 hXZ) s v hs hv
  have hset : (fun ω => (X ω, Y ω, Z ω)) ⁻¹' (s ×ˢ u ×ˢ v) =
      Y ⁻¹' u ∩ (fun ω => (X ω, Z ω)) ⁻¹' (s ×ˢ v) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]
    tauto
  rw [hset, hY']
  change P (Y ⁻¹' u) * P (X ⁻¹' s ∩ Z ⁻¹' v) = _
  rw [hXZ']
  ring

theorem brownianBridgeFamily_indep_signal_endpoints
    {Ω : Type u_5} {I : Type u_6} {α : Type u_7} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s)) {X : Ω → α} (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (t : ℝ≥0) (ht : t ≠ 0) :
    IndepFun (fun ω (p : I × Set.Iic t) =>
      B p.1 p.2 ω - ((p.2 : ℝ≥0) : ℝ) / (t : ℝ) * B p.1 t ω)
      (fun ω => (X ω, fun i => B i t ω)) P := by
  have := hIndep.isProbabilityMeasure
  apply indepFun_pair_reassociate (by fun_prop) mX (by fun_prop)
    (show IndepFun (fun ω (p : I × Set.Iic t) =>
        B p.1 p.2 ω - ((p.2 : ℝ≥0) : ℝ) / (t : ℝ) * B p.1 t ω)
        (fun ω i => B i t ω) P from
      by simpa only [BrownianBridge.bridge] using
        BrownianBridge.family_bridge_indep_endpoints B hB hIndep (pos_of_ne_zero ht))
  simpa only [Function.comp_def, id_eq] using hX.comp measurable_id
    (show Measurable (fun b : I × ℝ≥0 → ℝ =>
      ((fun p : I × Set.Iic t => b (p.1, p.2) -
        ((p.2 : ℝ≥0) : ℝ) / (t : ℝ) * b (p.1, t)), fun i => b (i, t))) by
      fun_prop)

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory ProbabilityTheory

namespace Problem336AdditiveD139.IndependentConditioning

variable {Ω : Type u_1} {E : Type u_2} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def fieldRectangles (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ a b, MeasurableSet[m₁] a ∧ MeasurableSet[m₂] b ∧ s = a ∩ b}

lemma isPiSystem_fieldRectangles (m₁ m₂ : MeasurableSpace Ω) :
    IsPiSystem (fieldRectangles m₁ m₂) := by
  rintro s ⟨a, b, ha, hb, rfl⟩ t ⟨c, d, hc, hd, rfl⟩ _
  refine ⟨a ∩ c, b ∩ d, ha.inter hc, hb.inter hd, ?_⟩
  ext x
  simp only [mem_inter_iff]
  tauto

lemma generateFrom_fieldRectangles (m₁ m₂ : MeasurableSpace Ω) :
    MeasurableSpace.generateFrom (fieldRectangles m₁ m₂) = m₁ ⊔ m₂ := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨a, b, ha, hb, rfl⟩
    exact ((show m₁ ≤ m₁ ⊔ m₂ from le_sup_left) a ha).inter
      ((show m₂ ≤ m₁ ⊔ m₂ from le_sup_right) b hb)
  · refine sup_le ?_ ?_
    · intro a ha
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨a, univ, ha, .univ, (inter_univ a).symm⟩
    · intro b hb
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨univ, b, .univ, hb, (univ_inter b).symm⟩

variable {m₁ m₂ m : MeasurableSpace Ω} {μ : Measure Ω}

lemma setIntegral_inter_of_indep [IsFiniteMeasure μ]
    (h₁ : m₁ ≤ m) (h₂ : m₂ ≤ m) (hind : Indep m₁ m₂ μ)
    {f : Ω → E} (hfm : StronglyMeasurable[m₁] f) (hfi : Integrable f μ)
    {a b : Set Ω} (ha : MeasurableSet[m₁] a) (hb : MeasurableSet[m₂] b) :
    ∫ x in a ∩ b, f x ∂μ = μ.real b • ∫ x in a, f x ∂μ := by
  have hi : Integrable (a.indicator f) μ := hfi.indicator (h₁ a ha)
  have he := condExp_indep_eq h₁ h₂ (hfm.indicator ha) hind
  have he' := setIntegral_congr_ae (h₂ b hb) (he.mono fun x hx _ => hx)
  rw [setIntegral_condExp h₂ hi hb, setIntegral_const,
    setIntegral_indicator (h₁ a ha), integral_indicator (h₁ a ha)] at he'
  simpa only [inter_comm] using he'

omit [CompleteSpace E] in

lemma setIntegral_eq_of_fieldRectangles
    (h₁ : m₁ ≤ m) (h₂ : m₂ ≤ m) {f g : Ω → E}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hrect : ∀ a b, MeasurableSet[m₁] a → MeasurableSet[m₂] b →
      ∫ x in a ∩ b, f x ∂μ = ∫ x in a ∩ b, g x ∂μ) :
    ∀ s, MeasurableSet[m₁ ⊔ m₂] s →
      ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ := by
  have hsup : m₁ ⊔ m₂ ≤ m := sup_le h₁ h₂
  have htotal : ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
    simpa using hrect univ univ .univ .univ
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (generateFrom_fieldRectangles m₁ m₂).symm
    (isPiSystem_fieldRectangles m₁ m₂) ?_ ?_ ?_ ?_
  · simp
  · rintro s ⟨a, b, ha, hb, rfl⟩
    exact hrect a b ha hb
  · intro s hs ih
    rw [setIntegral_compl (hsup s hs) hf, setIntegral_compl (hsup s hs) hg,
      htotal, ih]
  · intro s hdisj hmeas ih
    rw [integral_iUnion (fun n => hsup _ (hmeas n)) hdisj hf.integrableOn,
      integral_iUnion (fun n => hsup _ (hmeas n)) hdisj hg.integrableOn]
    exact tsum_congr ih

theorem condExp_sup_of_indep [IsFiniteMeasure μ]
    {mX mY mZ : MeasurableSpace Ω}
    (hX : mX ≤ m) (hZ : mZ ≤ m) (hYX : mY ≤ mX)
    (hind : Indep mX mZ μ)
    {f : Ω → E} (hfm : StronglyMeasurable[mX] f) (hfi : Integrable f μ) :
    μ[f | mY ⊔ mZ] =ᵐ[μ] μ[f | mY] := by
  have hY : mY ≤ m := hYX.trans hX
  have hsup : mY ⊔ mZ ≤ m := sup_le hY hZ
  have hgm : StronglyMeasurable[mX] (μ[f | mY]) :=
    stronglyMeasurable_condExp.mono hYX
  have hgi : Integrable (μ[f | mY]) μ := integrable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hsup hfi
    (fun _ _ _ => hgi.integrableOn) (fun s hs _ => ?_) ?_).symm
  · apply setIntegral_eq_of_fieldRectangles hY hZ hgi hfi _ s hs
    intro a b ha hb
    rw [setIntegral_inter_of_indep hX hZ hind hgm hgi (hYX a ha) hb,
      setIntegral_inter_of_indep hX hZ hind hfm hfi (hYX a ha) hb,
      setIntegral_condExp hY hfi ha]
  · exact (stronglyMeasurable_condExp.mono
      (show mY ≤ mY ⊔ mZ from le_sup_left)).aestronglyMeasurable

theorem condExp_sup_comap_of_indepFun [IsFiniteMeasure μ]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {β : Type u_3} {γ : Type u_4} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω → E} {Y : Ω → β} {Z : Ω → γ}
    (hf : Measurable f) (hY : Measurable Y) (hZ : Measurable Z)
    (hfi : Integrable f μ) (hind : IndepFun (fun x => (f x, Y x)) Z μ) :
    μ[f | MeasurableSpace.comap Y inferInstance ⊔ MeasurableSpace.comap Z inferInstance]
      =ᵐ[μ] μ[f | MeasurableSpace.comap Y inferInstance] := by
  let mXY : MeasurableSpace Ω := MeasurableSpace.comap (fun x => (f x, Y x)) inferInstance
  have hfXY : @Measurable Ω E mXY _ f :=
    measurable_fst.comp (comap_measurable _)
  have hYXY : @Measurable Ω β mXY _ Y :=
    measurable_snd.comp (comap_measurable _)
  exact condExp_sup_of_indep (hf.prodMk hY).comap_le hZ.comap_le hYXY.comap_le
    hind hfXY.stronglyMeasurable hfi

theorem posterior_of_independent_auxiliary [IsFiniteMeasure μ]
    {mX mY mZ mHistory : MeasurableSpace Ω}
    (hX : mX ≤ m) (hZ : mZ ≤ m) (hYX : mY ≤ mX)
    (hind : Indep mX mZ μ) (hHistory : mHistory = mY ⊔ mZ)
    {f posterior : Ω → E} (hfm : StronglyMeasurable[mX] f) (hfi : Integrable f μ)
    (hposterior : posterior =ᵐ[μ] μ[f | mY]) :
    posterior =ᵐ[μ] μ[f | mHistory] := by
  rw [hHistory]
  exact hposterior.trans (condExp_sup_of_indep hX hZ hYX hind hfm hfi).symm

end Problem336AdditiveD139.IndependentConditioning

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Filter
open scoped Topology ProbabilityTheory

namespace Problem336AdditiveD139.PosteriorLimit

variable {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem tendsto_of_ae_eq_condExp [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : Ω → ℝ) (b : ℕ → Ω → ℝ)
    (hb : ∀ n, b n =ᵐ[μ] μ[X | ℱ n]) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => b n ω) atTop
      (𝓝 ((μ[X | ⨆ n, ℱ n]) ω)) := by
  have hall : ∀ᵐ ω ∂μ, ∀ n, b n ω = (μ[X | ℱ n]) ω :=
    ae_all_iff.mpr hb
  filter_upwards [hall, MeasureTheory.tendsto_ae_condExp (ℱ := ℱ) X] with ω hω hlim
  exact hlim.congr (fun n => (hω n).symm)

theorem limsup_ae_eq_condExp [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : Ω → ℝ) (b : ℕ → Ω → ℝ)
    (hb : ∀ n, b n =ᵐ[μ] μ[X | ℱ n]) :
    (fun ω => limsup (fun n => b n ω) atTop) =ᵐ[μ]
      μ[X | ⨆ n, ℱ n] := by
  filter_upwards [tendsto_of_ae_eq_condExp ℱ X b hb] with ω hω
  exact hω.limsup_eq

theorem tendsto_eLpNorm_of_ae_eq_condExp [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : Ω → ℝ) (b : ℕ → Ω → ℝ)
    (hb : ∀ n, b n =ᵐ[μ] μ[X | ℱ n]) :
    Tendsto (fun n => eLpNorm (b n - μ[X | ⨆ k, ℱ k]) 1 μ)
      atTop (𝓝 0) := by
  refine (MeasureTheory.tendsto_eLpNorm_condExp (μ := μ) (ℱ := ℱ) X).congr ?_
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [hb n] with ω hω
  simp only [Pi.sub_apply, hω]

section ObservationSpaces

variable {I : Type u_2} {T : Type u_3} {E : Type u_4} [MeasurableSpace E]

@[reducible] def observationSpace (Y : I → T → Ω → E) (S : Set I) : MeasurableSpace Ω :=
  ⨆ i ∈ S, ⨆ t, MeasurableSpace.comap (Y i t) inferInstance

theorem observationSpace_mono (Y : I → T → Ω → E) :
    Monotone (observationSpace Y) := by
  intro S S' hS
  exact iSup_le fun i => iSup_le fun hi =>
    le_iSup_of_le i (le_iSup_of_le (hS hi) le_rfl)

theorem observationSpace_le (Y : I → T → Ω → E)
    (hY : ∀ i t, Measurable (Y i t)) (S : Set I) :
    observationSpace Y S ≤ mΩ := by
  exact iSup_le fun i => iSup_le fun _ => iSup_le fun t => (hY i t).comap_le

theorem iSup_observationSpace_eq (Y : I → T → Ω → E) (S : ℕ → Set I)
    (hS : ∀ i, ∃ n, i ∈ S n) :
    (⨆ n, observationSpace Y (S n)) = observationSpace Y Set.univ := by
  apply le_antisymm
  · exact iSup_le fun n => observationSpace_mono Y (Set.subset_univ _)
  · refine iSup_le fun i => iSup_le fun _ => ?_
    obtain ⟨n, hn⟩ := hS i
    exact le_iSup_of_le n (le_iSup_of_le i (le_iSup_of_le hn le_rfl))

def observationFiltration (Y : I → T → Ω → E)
    (hY : ∀ i t, Measurable (Y i t)) (S : ℕ → Set I)
    (hmono : Monotone S) : Filtration ℕ mΩ where
  seq n := observationSpace Y (S n)
  mono' := fun _ _ hnm => observationSpace_mono Y (hmono hnm)
  le' n := observationSpace_le Y hY (S n)

theorem limsup_ae_eq_full_observation_condExp [IsFiniteMeasure μ]
    (Y : I → T → Ω → E) (hY : ∀ i t, Measurable (Y i t))
    (S : ℕ → Set I) (hmono : Monotone S) (hexhaust : ∀ i, ∃ n, i ∈ S n)
    (X : Ω → ℝ) (b : ℕ → Ω → ℝ)
    (hb : ∀ n, b n =ᵐ[μ] μ[X | observationSpace Y (S n)]) :
    (fun ω => limsup (fun n => b n ω) atTop) =ᵐ[μ]
      μ[X | observationSpace Y Set.univ] := by
  have h := limsup_ae_eq_condExp (observationFiltration Y hY S hmono) X b hb
  change (fun ω => limsup (fun n => b n ω) atTop) =ᵐ[μ]
    μ[X | ⨆ n, observationSpace Y (S n)] at h
  rwa [iSup_observationSpace_eq Y S hexhaust] at h

end ObservationSpaces

end Problem336AdditiveD139.PosteriorLimit

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped ProbabilityTheory NNReal

namespace Problem336AdditiveD139.PosteriorLimit

variable {Ω : Type u_1} {I : Type u_2} {T : Type u_3}

@[reducible] def endpointSpace (Y : I → T → Ω → ℝ) (S : Set I) (t : T) :
    MeasurableSpace Ω :=
  ⨆ i ∈ S, MeasurableSpace.comap (Y i t) inferInstance

def centeredHistory (Y : I → T → Ω → ℝ) (t : T) (a : T → ℝ) : I → T → Ω → ℝ :=
  fun i s ω => Y i s ω - a s * Y i t ω

theorem endpointSpace_eq_comap (Y : I → T → Ω → ℝ) (S : Set I) (t : T) :
    endpointSpace Y S t =
      MeasurableSpace.comap (fun ω (i : S) => Y i t ω) inferInstance := by
  simp only [MeasurableSpace.comap_process_pi, endpointSpace, iSup_subtype]

theorem observationSpace_eq_comap (Y : I → T → Ω → ℝ) (S : Set I) :
    observationSpace Y S =
      MeasurableSpace.comap (fun ω (i : S) (s : T) => Y i s ω) inferInstance := by
  simp only [MeasurableSpace.comap_process_pi, observationSpace, iSup_subtype]

theorem measurable_observation (Y : I → T → Ω → ℝ) (S : Set I)
    {i : I} (hi : i ∈ S) (s : T) :
    @Measurable Ω ℝ (observationSpace Y S) inferInstance (Y i s) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le i (le_iSup_of_le hi (le_iSup_of_le s le_rfl))

theorem endpointSpace_le_observationSpace (Y : I → T → Ω → ℝ)
    (S : Set I) (t : T) : endpointSpace Y S t ≤ observationSpace Y S := by
  exact iSup_le fun i => iSup_le fun hi =>
    (measurable_observation Y S hi t).comap_le

theorem observationSpace_eq_endpoint_sup_bridge (Y : I → T → Ω → ℝ)
    (S : Set I) (t : T) (a : T → ℝ) :
    observationSpace Y S = endpointSpace Y S t ⊔
      observationSpace (fun i s ω => Y i s ω - a s * Y i t ω) S := by
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun s => ?_
    apply Measurable.comap_le
    have he0 : MeasurableSpace.comap (Y i t) inferInstance ≤ endpointSpace Y S t := by
      exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
    have he : @Measurable Ω ℝ
        (endpointSpace Y S t ⊔
          observationSpace (fun i s ω => Y i s ω - a s * Y i t ω) S)
        inferInstance (Y i t) :=
      Measurable.of_comap_le (he0.trans le_sup_left)
    have hb : @Measurable Ω ℝ
        (endpointSpace Y S t ⊔
          observationSpace (fun i s ω => Y i s ω - a s * Y i t ω) S)
        inferInstance (fun ω => Y i s ω - a s * Y i t ω) :=
      (measurable_observation
        (fun i s ω => Y i s ω - a s * Y i t ω) S hi s).mono le_sup_right le_rfl
    convert hb.add (he.const_mul (a s)) using 1
    funext ω
    change Y i s ω = (Y i s ω - a s * Y i t ω) + a s * Y i t ω
    ring
  · refine sup_le (endpointSpace_le_observationSpace Y S t) ?_
    exact iSup_le fun i => iSup_le fun hi => iSup_le fun s =>
      ((measurable_observation Y S hi s).sub
        (measurable_const.mul (measurable_observation Y S hi t))).comap_le

theorem signal_observationSpace_eq_endpoint_sup_noise_bridge
    (X : I → Ω → ℝ) (B : I → ℝ≥0 → Ω → ℝ) (S : Set I)
    (t : ℝ≥0) (ht : t ≠ 0) :
    observationSpace
      (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * X i ω + B i s.1 ω) S =
      endpointSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * X i ω + B i s.1 ω)
        S ⟨t, by simp⟩ ⊔
      observationSpace
        (fun i (s : Set.Iic t) ω => B i s.1 ω - (s.1 : ℝ) / (t : ℝ) * B i t ω) S := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  rw [observationSpace_eq_endpoint_sup_bridge
    (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * X i ω + B i s.1 ω)
    S ⟨t, by simp⟩ (fun s : Set.Iic t => (s.1 : ℝ) / (t : ℝ))]
  congr 2
  funext i s ω
  field_simp [ht']
  ring

end Problem336AdditiveD139.PosteriorLimit

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Problem336AdditiveD139.BrownianObservationSufficiency

open PosteriorLimit

variable {Ω : Type u_1} {I : Type u_2} {α : Type u_3} [MeasurableSpace Ω] [MeasurableSpace α]
  {P : Measure Ω}

theorem condExp_history_eq_endpoint
    {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    {X : Ω → α} (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (a : α → I → ℝ) (ma : Measurable a)
    (f : α → ℝ) (mf : Measurable f) (hf : Integrable (fun ω => f (X ω)) P)
    (J : Set I) (t : ℝ≥0) (ht : t ≠ 0) :
    P[(fun ω => f (X ω)) |
      observationSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω) J]
      =ᵐ[P]
    P[(fun ω => f (X ω)) |
      endpointSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω)
        J ⟨t, by simp⟩] := by
  have := hIndep.isProbabilityMeasure
  have hIndepJ : iIndepFun (fun (i : J) ω s => B i s ω) P :=
    hIndep.precomp Subtype.val_injective
  have hXJ : IndepFun X (fun ω (p : J × ℝ≥0) => B p.1 p.2 ω) P := by
    simpa only [Function.comp_def, id_eq] using
      hX.comp measurable_id
        (show Measurable (fun z : I × ℝ≥0 → ℝ =>
          fun p : J × ℝ≥0 => z (p.1.1, p.2)) by fun_prop)
  have hbridge := brownianBridgeFamily_indep_signal_endpoints
    (fun i : J => hB i) hIndepJ (fun i : J => mB i) mX hXJ t ht
  have hpair : IndepFun
      (fun ω => (f (X ω), fun i : J => (t : ℝ) * a (X ω) i + B i t ω))
      (fun ω (i : J) (s : Set.Iic t) =>
        B i s ω - (s.1 : ℝ) / (t : ℝ) * B i t ω) P := by
    simpa only [Function.comp_def, id_eq] using hbridge.symm.comp
      (show Measurable (fun z : α × (J → ℝ) =>
        (f z.1, fun i : J => (t : ℝ) * a z.1 i + z.2 i)) by fun_prop)
      (show Measurable (fun z : (J × Set.Iic t) → ℝ =>
        fun (i : J) (s : Set.Iic t) => z (i, s)) by fun_prop)
  rw [signal_observationSpace_eq_endpoint_sup_noise_bridge
    (fun i ω => a (X ω) i) B J t ht,
    endpointSpace_eq_comap, observationSpace_eq_comap]
  exact IndependentConditioning.condExp_sup_comap_of_indepFun
    (mf.comp mX)
    (show Measurable (fun ω (i : J) => (t : ℝ) * a (X ω) i + B i t ω) by fun_prop)
    (show Measurable (fun ω (i : J) (s : Set.Iic t) =>
      B i s ω - (s.1 : ℝ) / (t : ℝ) * B i t ω) by fun_prop)
    hf hpair

theorem posterior_history_of_endpoint
    {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    {X : Ω → α} (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (a : α → I → ℝ) (ma : Measurable a)
    (f : α → ℝ) (mf : Measurable f) (hf : Integrable (fun ω => f (X ω)) P)
    (J : Set I) (t : ℝ≥0) (ht : t ≠ 0)
    (posterior : Ω → ℝ)
    (hp : posterior =ᵐ[P] P[(fun ω => f (X ω)) |
      endpointSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω)
        J ⟨t, by simp⟩]) :
    posterior =ᵐ[P] P[(fun ω => f (X ω)) |
      observationSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω) J] :=
  hp.trans (condExp_history_eq_endpoint hB hIndep mB mX hX a ma f mf hf J t ht).symm

omit [MeasurableSpace Ω] in

theorem observationSpace_zero_eq_endpointSpace
    (Y : I → Set.Iic (0 : ℝ≥0) → Ω → ℝ) (J : Set I) :
    observationSpace Y J = endpointSpace Y J ⟨0, by simp⟩ := by
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun s => ?_
    have hs : s = ⟨0, by simp⟩ := by
      apply Subtype.ext
      exact le_antisymm s.2 zero_le
    rw [hs]
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  · exact endpointSpace_le_observationSpace Y J ⟨0, by simp⟩

theorem condExp_history_eq_endpoint_all
    {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    {X : Ω → α} (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (a : α → I → ℝ) (ma : Measurable a)
    (f : α → ℝ) (mf : Measurable f) (hf : Integrable (fun ω => f (X ω)) P)
    (J : Set I) (t : ℝ≥0) :
    P[(fun ω => f (X ω)) |
      observationSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω) J]
      =ᵐ[P]
    P[(fun ω => f (X ω)) |
      endpointSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω)
        J ⟨t, by simp⟩] := by
  by_cases ht : t = 0
  · subst t
    rw [observationSpace_zero_eq_endpointSpace]
  · exact condExp_history_eq_endpoint hB hIndep mB mX hX a ma f mf hf J t ht

theorem limsup_endpoint_posteriors_eq_full_history
    {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    {X : Ω → α} (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (a : α → I → ℝ) (ma : Measurable a)
    (f : α → ℝ) (mf : Measurable f) (hf : Integrable (fun ω => f (X ω)) P)
    (J : ℕ → Set I) (hmono : Monotone J) (hexhaust : ∀ i, ∃ n, i ∈ J n)
    (t : ℝ≥0) (b : ℕ → Ω → ℝ)
    (hb : ∀ n, b n =ᵐ[P] P[(fun ω => f (X ω)) |
      endpointSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω)
        (J n) ⟨t, by simp⟩]) :
    (fun ω => Filter.limsup (fun n => b n ω) Filter.atTop) =ᵐ[P]
      P[(fun ω => f (X ω)) |
        observationSpace
          (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω) Set.univ] := by
  have := hIndep.isProbabilityMeasure
  apply limsup_ae_eq_full_observation_condExp
    (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω)
    (by intro i s; fun_prop) J hmono hexhaust (fun ω => f (X ω)) b
  intro n
  exact (hb n).trans
    (condExp_history_eq_endpoint_all hB hIndep mB mX hX a ma f mf hf (J n) t).symm

theorem condExp_endpoint_zero_eq_integral [IsProbabilityMeasure P]
    {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (mB : ∀ i, Measurable (B i 0))
    (g : Ω → ℝ) (mg : Measurable g)
    (J : Set I) [Countable J] :
    P[g | MeasurableSpace.comap (fun ω (i : J) => B i 0 ω) inferInstance]
      =ᵐ[P] fun _ => ∫ ω, g ω ∂P := by
  have hzero : (fun ω (i : J) => B i 0 ω) =ᵐ[P] (fun _ _ => (0 : ℝ)) := by
    have hall : ∀ᵐ ω ∂P, ∀ i : J, B i 0 ω = 0 :=
      ae_all_iff.mpr (fun i => (hB i).eval_zero_ae_eq_zero)
    filter_upwards [hall] with ω hω
    exact funext hω
  have hind : IndepFun g (fun ω (i : J) => B i 0 ω) P :=
    (indepFun_const_right g (fun _ : J => (0 : ℝ))).congr
      Filter.EventuallyEq.rfl hzero.symm
  exact condExp_indep_eq mg.comap_le
    (Measurable.of_eval fun i : J => mB i).comap_le
    (comap_measurable g).stronglyMeasurable hind

end Problem336AdditiveD139.BrownianObservationSufficiency

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory Filter

namespace Problem336AdditiveD139

theorem groupDrift_ae_eq_condExp_of_finite_posteriors
    {Γ : Type u_1} {Ω : Type u_2} {T : Type u_3} [Group Γ] [Countable Γ] [DecidableEq Γ]
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : ProbabilityMeasure (Γ → Bool)) (X : Γ → Ω → ℝ)
    (Y : Γ → T → Ω → ℝ) (hY : ∀ j s, Measurable (Y j s))
    (t : ℝ) (endpoint : T)
    (hfinite : ∀ (i : Γ) (S : Finset Γ),
      (fun ω => finiteObservationDrift μ i S t (fun j => Y j endpoint ω)) =ᵐ[P]
        P[X i | PosteriorLimit.observationSpace Y (S : Set Γ)])
    (i : Γ) :
    (fun ω => groupDrift μ t (fun j => Y j endpoint ω) i) =ᵐ[P]
      P[X i | PosteriorLimit.observationSpace Y Set.univ] := by
  apply PosteriorLimit.limsup_ae_eq_full_observation_condExp
    Y hY (fun n => (translatedGroupExhaustion Γ i n : Set Γ))
  · intro n m hnm
    exact translatedGroupExhaustion_monotone Γ i hnm
  · intro j
    obtain ⟨N, hN⟩ := mem_translatedGroupExhaustion_eventually Γ i j
    exact ⟨N, hN N le_rfl⟩
  · exact fun n => hfinite i (translatedGroupExhaustion Γ i n)

theorem groupDrift_ae_all_eq_condExp_of_finite_posteriors
    {Γ : Type u_4} {Ω : Type u_5} {T : Type u_6} [Group Γ] [Countable Γ] [DecidableEq Γ]
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : ProbabilityMeasure (Γ → Bool)) (X : Γ → Ω → ℝ)
    (Y : Γ → T → Ω → ℝ) (hY : ∀ j s, Measurable (Y j s))
    (t : ℝ) (endpoint : T)
    (hfinite : ∀ (i : Γ) (S : Finset Γ),
      (fun ω => finiteObservationDrift μ i S t (fun j => Y j endpoint ω)) =ᵐ[P]
        P[X i | PosteriorLimit.observationSpace Y (S : Set Γ)]) :
    ∀ᵐ ω ∂P, ∀ i, groupDrift μ t (fun j => Y j endpoint ω) i =
      P[X i | PosteriorLimit.observationSpace Y Set.univ] ω := by
  exact ae_all_iff.mpr (groupDrift_ae_eq_condExp_of_finite_posteriors
    P μ X Y hY t endpoint hfinite)

theorem groupDrift_ae_eq_condExp_of_observed_posteriors
    {Γ : Type u_7} {Ω : Type u_8} {T : Type u_9} [Group Γ] [Countable Γ] [DecidableEq Γ]
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : ProbabilityMeasure (Γ → Bool)) (X : Γ → Ω → ℝ)
    (Y : Γ → T → Ω → ℝ) (hY : ∀ j s, Measurable (Y j s))
    (t : ℝ) (endpoint : T)
    (hfinite : ∀ (S : Finset Γ) (i : S),
      (fun ω => tiltMean (finiteMarginal μ S)
        (fun j : S => Y j.1 endpoint ω - t / 2) i) =ᵐ[P]
        P[X i.1 | PosteriorLimit.observationSpace Y (S : Set Γ)])
    (i : Γ) :
    (fun ω => groupDrift μ t (fun j => Y j endpoint ω) i) =ᵐ[P]
      P[X i | PosteriorLimit.observationSpace Y Set.univ] := by
  apply PosteriorLimit.limsup_ae_eq_full_observation_condExp
    Y hY (fun n => (translatedGroupExhaustion Γ i n : Set Γ))
  · intro n m hnm
    exact translatedGroupExhaustion_monotone Γ i hnm
  · intro j
    obtain ⟨N, hN⟩ := mem_translatedGroupExhaustion_eventually Γ i j
    exact ⟨N, hN N le_rfl⟩
  · intro n
    simpa only [finiteObservationDrift_eq_tiltMean_of_mem μ i
      (translatedGroupExhaustion Γ i n) (self_mem_translatedGroupExhaustion Γ i n)] using
      hfinite (translatedGroupExhaustion Γ i n)
        ⟨i, self_mem_translatedGroupExhaustion Γ i n⟩

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Function
open scoped ENNReal ProbabilityTheory BigOperators

namespace Problem336AdditiveD139.DensityBayes

variable {Ω : Type u_1} {E : Type u_2} [MeasurableSpace Ω] [mE : MeasurableSpace E]

theorem condExp_indicator_of_observation_densities
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure E) [SigmaFinite ρ]
    (Y : Ω → E) (hY : Measurable Y) (A : Set Ω) (hA : MeasurableSet A)
    (num den : E → ℝ≥0∞) (hnum : Measurable num) (hden : Measurable den)
    (hden0 : ∀ᵐ y ∂ρ, den y ≠ 0) (hdenTop : ∀ᵐ y ∂ρ, den y ≠ ∞)
    (hnumLaw : Measure.map Y (μ.restrict A) = ρ.withDensity num)
    (hdenLaw : Measure.map Y μ = ρ.withDensity den) :
    μ[A.indicator (fun _ => (1 : ℝ)) | mE.comap Y] =ᵐ[μ]
      (fun ω => (num (Y ω) / den (Y ω)).toReal) := by
  let : IsFiniteMeasure (ρ.withDensity num) := hnumLaw ▸ inferInstance
  have hratio : (ρ.withDensity num).rnDeriv (ρ.withDensity den) =ᵐ[ρ]
      (fun y => num y / den y) := by
    filter_upwards [Measure.rnDeriv_withDensity_right (ρ.withDensity num) ρ
      hden.aemeasurable hden0 hdenTop, Measure.rnDeriv_withDensity ρ hnum]
      with y hy hn
    rw [hy, hn, div_eq_mul_inv, mul_comm]
  have hratioMap : (fun y => ((μ.restrict A).map Y).rnDeriv (μ.map Y) y) =ᵐ[μ.map Y]
      (fun y => num y / den y) := by
    rw [hnumLaw, hdenLaw]
    exact (withDensity_absolutelyContinuous ρ den).ae_eq hratio
  have hmap := toReal_rnDeriv_map ((Measure.restrict_le_self : μ.restrict A ≤ μ).absolutelyContinuous) hY
  have hsource : (fun ω => ((μ.restrict A).rnDeriv μ ω).toReal) =ᵐ[μ]
      A.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [Measure.rnDeriv_restrict_self μ hA] with ω hω
    rw [hω]
    by_cases hωA : ω ∈ A <;> simp [hωA]
  have hposterior := hmap.trans (condExp_congr_ae hsource)
  filter_upwards [hposterior, ae_of_ae_map hY.aemeasurable hratioMap] with ω hp hr
  rw [← hp, hr]

section FiniteSignal

variable {F : Type u_3} [Fintype F] [MeasurableSpace F] [MeasurableSingletonClass F]

theorem map_eq_withDensity_sum (μ : Measure Ω) (ρ : Measure E)
    (X : Ω → F) (hX : Measurable X) (Y : Ω → E) (hY : Measurable Y)
    (w : F → E → ℝ≥0∞) (hw : ∀ x, Measurable (w x))
    (hAtom : ∀ x, Measure.map Y (μ.restrict (X ⁻¹' {x})) = ρ.withDensity (w x)) :
    Measure.map Y μ = ρ.withDensity (fun y => ∑ x, w x y) := by
  classical
  have hcover : (⋃ x : F, X ⁻¹' {x}) = Set.univ := by
    ext ω
    simp
  have hdisj : Pairwise (Disjoint on (fun x : F => X ⁻¹' {x})) := by
    intro x z hxz
    exact (Set.disjoint_singleton.mpr hxz).preimage X
  have hdecomp := Measure.restrict_iUnion (μ := μ) hdisj
    (fun x => hX (measurableSet_singleton x))
  rw [hcover, Measure.restrict_univ] at hdecomp
  rw [hdecomp, Measure.map_sum hY.aemeasurable]
  simp_rw [hAtom]
  rw [← withDensity_tsum hw]
  congr 1
  funext y
  simp only [tsum_fintype, Finset.sum_apply]

theorem map_restrict_eq_withDensity_sum (μ : Measure Ω) (ρ : Measure E)
    (X : Ω → F) (hX : Measurable X) (Y : Ω → E) (hY : Measurable Y)
    (w : F → E → ℝ≥0∞) (hw : ∀ x, Measurable (w x))
    (hAtom : ∀ x, Measure.map Y (μ.restrict (X ⁻¹' {x})) = ρ.withDensity (w x))
    (C : Set F) [DecidablePred (· ∈ C)] :
    Measure.map Y (μ.restrict (X ⁻¹' C)) =
      ρ.withDensity (fun y => ∑ x, if x ∈ C then w x y else 0) := by
  classical
  apply map_eq_withDensity_sum (μ.restrict (X ⁻¹' C)) ρ X hX Y hY
    (fun x y => if x ∈ C then w x y else 0)
    (fun x => by split_ifs <;> fun_prop)
  intro x
  rw [Measure.restrict_restrict (hX (measurableSet_singleton x))]
  by_cases hx : x ∈ C
  · have heq : X ⁻¹' {x} ∩ X ⁻¹' C = X ⁻¹' {x} := by
      apply Set.inter_eq_left.mpr
      intro ω hω
      change X ω ∈ C
      rw [Set.mem_singleton_iff.mp hω]
      exact hx
    simp only [heq, hx, ite_true]
    exact hAtom x
  · have heq : X ⁻¹' {x} ∩ X ⁻¹' C = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro hω
      simpa [hω] using hx
    simp [heq, hx]

theorem finite_signal_condExp_indicator
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure E) [SigmaFinite ρ]
    (X : Ω → F) (hX : Measurable X) (Y : Ω → E) (hY : Measurable Y)
    (w : F → E → ℝ≥0∞) (hw : ∀ x, Measurable (w x))
    (hAtom : ∀ x, Measure.map Y (μ.restrict (X ⁻¹' {x})) = ρ.withDensity (w x))
    (hden0 : ∀ᵐ y ∂ρ, (∑ x, w x y) ≠ 0)
    (hdenTop : ∀ᵐ y ∂ρ, (∑ x, w x y) ≠ ∞)
    (C : Set F) [DecidablePred (· ∈ C)] :
    μ[(X ⁻¹' C).indicator (fun _ => (1 : ℝ)) | mE.comap Y] =ᵐ[μ]
      (fun ω => ((∑ x, if x ∈ C then w x (Y ω) else 0) /
        (∑ x, w x (Y ω))).toReal) := by
  have hnum : Measurable (fun y => ∑ x, if x ∈ C then w x y else 0) := by
    apply Finset.measurable_sum
    intro x _
    by_cases hx : x ∈ C
    · simpa only [hx, ite_true] using hw x
    · simp only [hx, ite_false]
      exact measurable_const
  have hden : Measurable (fun y => ∑ x, w x y) :=
    Finset.measurable_sum _ (fun x _ => hw x)
  exact condExp_indicator_of_observation_densities μ ρ Y hY (X ⁻¹' C)
    (hX (Set.toFinite C).measurableSet)
    (fun y => ∑ x, if x ∈ C then w x y else 0) (fun y => ∑ x, w x y)
    hnum hden hden0 hdenTop
    (map_restrict_eq_withDensity_sum μ ρ X hX Y hY w hw hAtom C)
    (map_eq_withDensity_sum μ ρ X hX Y hY w hw hAtom)

theorem finite_signal_condExp_indicator_real
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure E) [SigmaFinite ρ]
    (X : Ω → F) (hX : Measurable X) (Y : Ω → E) (hY : Measurable Y)
    (w : F → E → ℝ) (hw : ∀ x, Measurable (w x))
    (hw0 : ∀ x y, 0 ≤ w x y) (hpos : ∀ y, 0 < ∑ x, w x y)
    (hAtom : ∀ x, Measure.map Y (μ.restrict (X ⁻¹' {x})) =
      ρ.withDensity (fun y => ENNReal.ofReal (w x y)))
    (C : Set F) [DecidablePred (· ∈ C)] :
    μ[(X ⁻¹' C).indicator (fun _ => (1 : ℝ)) | mE.comap Y] =ᵐ[μ]
      (fun ω => (∑ x, if x ∈ C then w x (Y ω) else 0) /
        (∑ x, w x (Y ω))) := by
  have hsum (y : E) : (∑ x, ENNReal.ofReal (w x y)) =
      ENNReal.ofReal (∑ x, w x y) :=
    (ENNReal.ofReal_sum_of_nonneg (fun x _ => hw0 x y)).symm
  have hnum0 (y : E) : 0 ≤ ∑ x, if x ∈ C then w x y else 0 := by
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact hw0 x y
    · exact le_rfl
  have hnum (y : E) : (∑ x, if x ∈ C then ENNReal.ofReal (w x y) else 0) =
      ENNReal.ofReal (∑ x, if x ∈ C then w x y else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    · intro x _
      split_ifs
      · exact hw0 x y
      · exact le_rfl
  have hz : ∀ᵐ y ∂ρ, (∑ x, ENNReal.ofReal (w x y)) ≠ 0 :=
    Filter.Eventually.of_forall (fun y => by
      rw [hsum y]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (hpos y)))
  have ht : ∀ᵐ y ∂ρ, (∑ x, ENNReal.ofReal (w x y)) ≠ ∞ :=
    Filter.Eventually.of_forall (fun y => by
      rw [hsum y]
      exact ENNReal.ofReal_ne_top)
  have h := finite_signal_condExp_indicator μ ρ X hX Y hY
    (fun x y => ENNReal.ofReal (w x y)) (fun x => (hw x).ennreal_ofReal) hAtom
    hz ht C
  filter_upwards [h] with ω hω
  simpa only [hnum, hsum, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (hnum0 (Y ω)),
    ENNReal.toReal_ofReal (le_of_lt (hpos (Y ω)))] using hω

end FiniteSignal

end Problem336AdditiveD139.DensityBayes

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Problem336AdditiveD139
namespace GaussianObservation

theorem gaussianPDFReal_binary_shift (t : ℝ≥0) (ht : t ≠ 0) (b : Bool) (y : ℝ) :
    gaussianPDFReal ((t : ℝ) * boolReal b) t y =
      Real.exp ((y - (t : ℝ) / 2) * boolReal b) * gaussianPDFReal 0 t y := by
  cases b with
  | false => simp [boolReal]
  | true =>
    simp only [boolReal, ite_true, mul_one]
    have ht' : (t : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr ht
    have he : -(y - (t : ℝ)) ^ 2 / (2 * (t : ℝ)) =
        (y - (t : ℝ) / 2) + (-y ^ 2 / (2 * (t : ℝ))) := by
      field_simp [ht']
      ring
    simp only [gaussianPDFReal, sub_zero]
    rw [he, Real.exp_add]
    ring

theorem gaussianPDF_binary_shift (t : ℝ≥0) (ht : t ≠ 0) (b : Bool) (y : ℝ) :
    gaussianPDF ((t : ℝ) * boolReal b) t y =
      ENNReal.ofReal (Real.exp ((y - (t : ℝ) / 2) * boolReal b)) * gaussianPDF 0 t y := by
  rw [gaussianPDF, gaussianPDFReal_binary_shift t ht]
  exact ENNReal.ofReal_mul (Real.exp_nonneg _)

def likelihood {F : Type u_1} [Fintype F] (t : ℝ≥0) (x : F → Bool) (y : F → ℝ) : ℝ :=
  Real.exp (∑ i, (y i - (t : ℝ) / 2) * boolReal (x i))

lemma likelihood_pos {F : Type u_2} [Fintype F] (t : ℝ≥0) (x : F → Bool) (y : F → ℝ) :
    0 < likelihood t x y := Real.exp_pos _

lemma measurable_likelihood {F : Type u_3} [Fintype F] (t : ℝ≥0) (x : F → Bool) :
    Measurable (likelihood t x) := by
  unfold likelihood
  fun_prop

theorem gaussianPDFReal_product_binary_shift {F : Type u_4} [Fintype F]
    (t : ℝ≥0) (ht : t ≠ 0) (x : F → Bool) (y : F → ℝ) :
    (∏ i, gaussianPDFReal ((t : ℝ) * boolReal (x i)) t (y i)) =
      likelihood t x y * ∏ i, gaussianPDFReal 0 t (y i) := by
  classical
  simp_rw [gaussianPDFReal_binary_shift t ht]
  rw [Finset.prod_mul_distrib, likelihood, Real.exp_sum]

theorem gaussianReal_binary_shift (t : ℝ≥0) (ht : t ≠ 0) (b : Bool) :
    gaussianReal ((t : ℝ) * boolReal b) t =
      (gaussianReal 0 t).withDensity
        (fun y => ENNReal.ofReal (Real.exp ((y - (t : ℝ) / 2) * boolReal b))) := by
  rw [gaussianReal_of_var_ne_zero _ ht, gaussianReal_of_var_ne_zero _ ht,
    ← withDensity_mul volume (measurable_gaussianPDF 0 t) (by fun_prop)]
  congr 1
  funext y
  rw [gaussianPDF_binary_shift t ht]
  exact mul_comm _ _

theorem pi_withDensity_ofReal {F : Type u_5} [Fintype F]
    (μ : F → Measure ℝ) [∀ i, SigmaFinite (μ i)] (f : F → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (hnonneg : ∀ i y, 0 ≤ f i y) :
    Measure.pi (fun i => (μ i).withDensity (fun y => ENNReal.ofReal (f i y))) =
      (Measure.pi μ).withDensity (fun y => ENNReal.ofReal (∏ i, f i (y i))) := by
  classical
  have : ∀ i, IsFiniteMeasure ((μ i).withDensity (fun y => ENNReal.ofReal (f i y))) :=
    fun i => isFiniteMeasure_withDensity
      ((hasFiniteIntegral_iff_ofReal (ae_of_all _ (hnonneg i))).mp (hf i).2).ne
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hp : Integrable (fun y : F → ℝ => ∏ i, f i (y i))
      (Measure.pi (fun i => (μ i).restrict (s i))) :=
    Integrable.fintype_prod (fun i => (hf i).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hp
    (ae_of_all _ (fun y => Finset.prod_nonneg (fun i _ => hnonneg i (y i)))),
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnonneg i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hnonneg i))

lemma integrable_binary_likelihood (t : ℝ≥0) (ht : t ≠ 0) (b : Bool) :
    Integrable (fun y => Real.exp ((y - (t : ℝ) / 2) * boolReal b))
      (gaussianReal 0 t) := by
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun y => Real.exp_nonneg _))]
  have hm := congrArg (fun ν : Measure ℝ => ν Set.univ) (gaussianReal_binary_shift t ht b)
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hm
  rw [← hm]
  exact ENNReal.one_lt_top

theorem gaussianReal_pi_binary_shift {F : Type u_6} [Fintype F]
    (t : ℝ≥0) (ht : t ≠ 0) (x : F → Bool) :
    Measure.pi (fun i => gaussianReal ((t : ℝ) * boolReal (x i)) t) =
      (Measure.pi (fun _ : F => gaussianReal 0 t)).withDensity
        (fun y => ENNReal.ofReal (likelihood t x y)) := by
  classical
  simp_rw [gaussianReal_binary_shift t ht]
  rw [pi_withDensity_ofReal _ _ (fun i => integrable_binary_likelihood t ht (x i))
    (fun _ _ => Real.exp_nonneg _)]
  congr 1
  funext y
  congr 1
  exact (Real.exp_sum _ _).symm

end GaussianObservation
end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem336AdditiveD139.IndependentAtomObservation

variable {Ω : Type u_1} {F : Type u_2} {E : Type u_3} {Y : Type u_4} [MeasurableSpace Ω] [MeasurableSpace F]
    [MeasurableSpace E] [MeasurableSpace Y] [MeasurableSingletonClass F]
    {μ : Measure Ω} {X : Ω → F} {Z : Ω → E}

theorem map_noise_restrict_atom (hZ : Measurable Z)
    (hind : IndepFun X Z μ) (x : F) :
    Measure.map Z (μ.restrict (X ⁻¹' {x})) =
      μ (X ⁻¹' {x}) • Measure.map Z μ := by
  ext s hs
  rw [Measure.map_apply hZ hs, Measure.restrict_apply (hZ hs),
    Measure.smul_apply, smul_eq_mul, Measure.map_apply hZ hs]
  rw [Set.inter_comm]
  exact hind.measure_inter_preimage_eq_mul {x} s (measurableSet_singleton x) hs

theorem map_observation_restrict_atom (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z μ) (T : F → E → Y) (x : F) (hT : Measurable (T x)) :
    Measure.map (fun ω => T (X ω) (Z ω)) (μ.restrict (X ⁻¹' {x})) =
      μ (X ⁻¹' {x}) • Measure.map (T x) (Measure.map Z μ) := by
  have heq : (fun ω => T (X ω) (Z ω)) =ᵐ[μ.restrict (X ⁻¹' {x})]
      (fun ω => T x (Z ω)) := by
    filter_upwards [ae_restrict_mem (hX (measurableSet_singleton x))] with ω hω
    have hx : X ω = x := hω
    rw [hx]
  rw [Measure.map_congr heq]
  change Measure.map (T x ∘ Z) (μ.restrict (X ⁻¹' {x})) = _
  rw [← Measure.map_map hT hZ, map_noise_restrict_atom hZ hind x, Measure.map_smul]

theorem map_observation_restrict_atom_of_hasLaw (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z μ) {ρ : Measure E} (hρ : HasLaw Z ρ μ)
    (T : F → E → Y) (x : F) (hT : Measurable (T x)) :
    Measure.map (fun ω => T (X ω) (Z ω)) (μ.restrict (X ⁻¹' {x})) =
      μ (X ⁻¹' {x}) • Measure.map (T x) ρ := by
  rw [map_observation_restrict_atom hX hZ hind T x hT, hρ.map_eq]

theorem map_observation_restrict_atom_withDensity (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z μ) {ρ : Measure E} (hρ : HasLaw Z ρ μ)
    (T : F → E → Y) (x : F) (hT : Measurable (T x))
    (ν : Measure Y) (L : Y → ℝ≥0∞) (hL : Measurable L)
    (hlaw : Measure.map (T x) ρ = ν.withDensity L) :
    Measure.map (fun ω => T (X ω) (Z ω)) (μ.restrict (X ⁻¹' {x})) =
      ν.withDensity (fun y => μ (X ⁻¹' {x}) * L y) := by
  rw [map_observation_restrict_atom_of_hasLaw hX hZ hind hρ T x hT, hlaw]
  exact (withDensity_smul (μ (X ⁻¹' {x})) hL).symm

theorem map_observation_restrict_atom_withDensity_ofReal [IsFiniteMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hind : IndepFun X Z μ)
    {ρ : Measure E} (hρ : HasLaw Z ρ μ)
    (T : F → E → Y) (x : F) (hT : Measurable (T x))
    (ν : Measure Y) (L : Y → ℝ) (hL : Measurable L)
    (hlaw : Measure.map (T x) ρ = ν.withDensity (fun y => ENNReal.ofReal (L y))) :
    Measure.map (fun ω => T (X ω) (Z ω)) (μ.restrict (X ⁻¹' {x})) =
      ν.withDensity (fun y => ENNReal.ofReal ((μ (X ⁻¹' {x})).toReal * L y)) := by
  rw [map_observation_restrict_atom_withDensity hX hZ hind hρ T x hT ν
    (fun y => ENNReal.ofReal (L y)) hL.ennreal_ofReal hlaw]
  congr 1
  funext y
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end Problem336AdditiveD139.IndependentAtomObservation

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem336AdditiveD139

lemma finiteFieldWeight_congr_on {I : Type u_1} (S : Finset I) (h h' : I → ℝ)
    (heq : ∀ j ∈ S, h j = h' j) (x : I → Bool) :
    finiteFieldWeight S h x = finiteFieldWeight S h' x := by
  unfold finiteFieldWeight
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [heq j hj]

lemma finiteFieldMean_congr_on {I : Type u_2} (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (h h' : I → ℝ) (heq : ∀ j ∈ S, h j = h' j) (i : I) :
    finiteFieldMean μ S h i = finiteFieldMean μ S h' i := by
  unfold finiteFieldMean
  simp only [finiteFieldWeight_congr_on S h h' heq]

def endpointObservationField {I : Type u_3} [DecidableEq I]
    (S : Finset I) (t : ℝ) (y : S → ℝ) : I → ℝ :=
  fun j => if hj : j ∈ S then y ⟨j, hj⟩ - t / 2 else 0

def finiteEndpointMean {I : Type u_4} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I)
    (t : ℝ) (y : S → ℝ) : ℝ :=
  finiteFieldMean μ S (endpointObservationField S t y) i

lemma measurable_endpointObservationField {I : Type u_5} [DecidableEq I] (S : Finset I) :
    Measurable (fun p : ℝ × (S → ℝ) => endpointObservationField S p.1 p.2) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : j ∈ S
  · simp only [endpointObservationField, hj, dite_eq_left]
    exact ((measurable_pi_apply (⟨j, hj⟩ : S)).comp measurable_snd).sub
      (measurable_fst.div_const 2)
  · simp only [endpointObservationField, hj]
    exact measurable_const

lemma measurable_finiteEndpointMean {I : Type u_6} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I) :
    Measurable (fun p : ℝ × (S → ℝ) => finiteEndpointMean μ i S p.1 p.2) :=
  (measurable_finiteFieldMean μ S i).comp (measurable_endpointObservationField S)

lemma finiteEndpointMean_restrict {I : Type u_7} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I)
    (t : ℝ) (y : I → ℝ) :
    finiteEndpointMean μ i S t (fun j : S => y j.1) =
      finiteFieldMean μ S (fun j => y j - t / 2) i := by
  apply finiteFieldMean_congr_on
  intro j hj
  simp [endpointObservationField, hj]

theorem finiteBinary_condExp_of_field_densities
    {Ω : Type u_8} {E : Type u_9} {F : Type u_10} [MeasurableSpace Ω] [mE : MeasurableSpace E] [Fintype F]
    (P : Measure Ω) [IsFiniteMeasure P] (ρ : Measure E) [SigmaFinite ρ]
    (μ : ProbabilityMeasure (F → Bool)) (X : Ω → (F → Bool)) (hX : Measurable X)
    (Y : Ω → E) (hY : Measurable Y) (h : E → F → ℝ) (hh : Measurable h)
    (hAtom : ∀ x, Measure.map Y (P.restrict (X ⁻¹' {x})) =
      ρ.withDensity (fun y => ENNReal.ofReal
        (Real.exp (∑ j, h y j * boolReal (x j)) *
          ((μ : Measure (F → Bool)) {x}).toReal))) (i : F) :
    P[(fun ω => boolReal (X ω i)) | mE.comap Y] =ᵐ[P]
      (fun ω => tiltMean μ (h (Y ω)) i) := by
  classical
  let w : (F → Bool) → E → ℝ := fun x y =>
    Real.exp (∑ j, h y j * boolReal (x j)) * ((μ : Measure (F → Bool)) {x}).toReal
  have hw : ∀ x, Measurable (w x) := by
    intro x
    apply Measurable.mul_const
    apply Measurable.exp
    exact Finset.measurable_sum _ (fun j _ =>
      ((measurable_pi_apply j).comp hh).mul_const _)
  have hw0 : ∀ x y, 0 ≤ w x y := fun x y =>
    mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg
  have hpos : ∀ y, 0 < ∑ x, w x y := fun y => tiltPartition_pos μ (h y)
  have hb := DensityBayes.finite_signal_condExp_indicator_real P ρ X hX Y hY
    w hw hw0 hpos hAtom {x | x i = true}
  have hind : (X ⁻¹' {x | x i = true}).indicator (fun _ => (1 : ℝ)) =
      fun ω => boolReal (X ω i) := by
    funext ω
    simp [boolReal, Set.indicator_apply]
  rw [hind] at hb
  filter_upwards [hb] with ω hω
  rw [hω]
  unfold tiltMean tiltPartition
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x i = true <;> simp [w, boolReal, hx]

private lemma endpoint_pi_dirac_zero {G : Type u_11} [Fintype G] :
    Measure.pi (fun _ : G => Measure.dirac (0 : ℝ)) =
      Measure.dirac (fun _ : G => (0 : ℝ)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  by_cases h : ∀ j, (0 : ℝ) ∈ s j
  · simp [Measure.dirac_apply', MeasurableSet.univ_pi hs, hs, Set.mem_pi, h]
  · have hp : (∏ j, (Measure.dirac (0 : ℝ)) (s j)) = 0 := by
      obtain ⟨j, hj⟩ := not_forall.mp h
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [Measure.dirac_apply', hs, hj]
    rw [hp]
    simp [Measure.dirac_apply', MeasurableSet.univ_pi hs, Set.mem_pi, h]

lemma gaussianEndpoint_shift_map {G : Type u_12} [Fintype G]
    (t : ℝ≥0) (x : G → Bool) :
    Measure.map (fun z : G → ℝ => fun j => (t : ℝ) * boolReal (x j) + z j)
      (Measure.pi (fun _ : G => gaussianReal 0 t)) =
      (Measure.pi (fun _ : G => gaussianReal 0 t)).withDensity
        (fun y => ENNReal.ofReal (GaussianObservation.likelihood t x y)) := by
  by_cases ht : t = 0
  · subst t
    simp only [NNReal.coe_zero, zero_mul, zero_add, gaussianReal_zero_var]
    rw [endpoint_pi_dirac_zero]
    change Measure.map id (Measure.dirac (fun _ : G => (0 : ℝ))) = _
    rw [Measure.map_id, dirac_withDensity]
    simp [GaussianObservation.likelihood]
  · rw [Measure.pi_map_pi (f := fun j z => (t : ℝ) * boolReal (x j) + z)
      (fun j => (measurable_const.add measurable_id).aemeasurable)]
    simp_rw [gaussianReal_map_const_add, zero_add]
    exact GaussianObservation.gaussianReal_pi_binary_shift t ht x

theorem finiteBinary_condExp_independentGaussian
    {Ω : Type u_13} {F : Type u_14} {G : Type u_15} [MeasurableSpace Ω] [Fintype F] [Fintype G]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : ProbabilityMeasure (F → Bool))
    (X : Ω → (F → Bool)) (hX : Measurable X)
    (hXLaw : HasLaw X (μ : Measure (F → Bool)) P)
    (Z : Ω → (G → ℝ)) (hZ : Measurable Z)
    (t : ℝ≥0)
    (hZLaw : HasLaw Z (Measure.pi (fun _ : G => gaussianReal 0 t)) P)
    (hind : IndepFun X Z P) (σ : G → F)
    (h : (G → ℝ) → F → ℝ) (hh : Measurable h)
    (hsum : ∀ (x : F → Bool) (y : G → ℝ),
      (∑ j, h y j * boolReal (x j)) =
        ∑ j, (y j - (t : ℝ) / 2) * boolReal (x (σ j))) (i : F) :
    let Y : Ω → (G → ℝ) := fun ω j => (t : ℝ) * boolReal (X ω (σ j)) + Z ω j
    P[(fun ω => boolReal (X ω i)) | (inferInstance : MeasurableSpace (G → ℝ)).comap Y]
      =ᵐ[P] (fun ω => tiltMean μ (h (Y ω)) i) := by
  classical
  dsimp only
  let T : (F → Bool) → (G → ℝ) → (G → ℝ) :=
    fun x z j => (t : ℝ) * boolReal (x (σ j)) + z j
  have hT : ∀ x, Measurable (T x) := by
    intro x
    exact Measurable.of_eval (fun j => measurable_const.add (measurable_pi_apply j))
  have hY : Measurable (fun ω => T (X ω) (Z ω)) := by
    apply Measurable.of_eval
    intro j
    exact ((((measurable_of_countable boolReal).comp ((measurable_pi_apply (σ j)).comp hX)).const_mul
      (t : ℝ)).add ((measurable_pi_apply j).comp hZ))
  apply finiteBinary_condExp_of_field_densities P
    (Measure.pi (fun _ : G => gaussianReal 0 t)) μ X hX _ hY h hh ?_ i
  intro x
  have ha := IndependentAtomObservation.map_observation_restrict_atom_withDensity_ofReal
    hX hZ hind hZLaw T x (hT x)
    (Measure.pi (fun _ : G => gaussianReal 0 t))
    (GaussianObservation.likelihood t (fun j => x (σ j)))
    (GaussianObservation.measurable_likelihood t (fun j => x (σ j)))
    (gaussianEndpoint_shift_map t (fun j => x (σ j)))
  rw [ha]
  congr 1
  funext y
  have hmass : P (X ⁻¹' {x}) = (μ : Measure (F → Bool)) {x} := by
    rw [← Measure.map_apply hX (measurableSet_singleton x), hXLaw.map_eq]
  rw [hmass, hsum]
  unfold GaussianObservation.likelihood
  rw [mul_comm]

lemma endpointObservationField_sum {I : Type u_16} [DecidableEq I]
    (S J : Finset I) (hSJ : S ⊆ J) (t : ℝ) (y : S → ℝ) (x : J → Bool) :
    (∑ j : J, endpointObservationField S t y j.1 * boolReal (x j)) =
      ∑ j : S, (y j - t / 2) * boolReal (x ⟨j.1, hSJ j.2⟩) := by
  classical
  let f : I → ℝ := fun j => if hj : j ∈ S then
    (y ⟨j, hj⟩ - t / 2) * boolReal (x ⟨j, hSJ hj⟩) else 0
  calc
    _ = ∑ j : J, f j.1 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.1 ∈ S <;> simp [endpointObservationField, f, hj]
    _ = ∑ j ∈ J, f j := Finset.sum_coe_sort J f
    _ = ∑ j ∈ S, f j := (Finset.sum_subset hSJ (fun j _ hj => by simp [f, hj])).symm
    _ = ∑ j : S, f j.1 := (Finset.sum_coe_sort S f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp [f, j.2]

lemma finiteEndpointMean_eq_tiltMean {I : Type u_17} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (S J : Finset I) (hSJ : S ⊆ J)
    (i : J) (t : ℝ) (y : S → ℝ) :
    finiteEndpointMean μ i.1 S t y =
      tiltMean (finiteMarginal μ J) (fun j : J => endpointObservationField S t y j.1) i := by
  unfold finiteEndpointMean
  rw [finiteFieldMean_eq_tiltMean_finiteMarginal μ S J hSJ _ i]
  congr 1
  funext j
  by_cases hj : j.1 ∈ S <;> simp [endpointObservationField, hj]

theorem finiteEndpointMean_condExp
    {Ω : Type u_18} {I : Type u_19} [MeasurableSpace Ω] [DecidableEq I]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : ProbabilityMeasure (I → Bool))
    (X : Ω → (I → Bool)) (hX : Measurable X)
    (hXLaw : HasLaw X (μ : Measure (I → Bool)) P)
    (i : I) (S : Finset I) (Z : Ω → (S → ℝ)) (hZ : Measurable Z)
    (t : ℝ≥0)
    (hZLaw : HasLaw Z (Measure.pi (fun _ : S => gaussianReal 0 t)) P)
    (hind : IndepFun X Z P) :
    let Y : Ω → (S → ℝ) := fun ω j => (t : ℝ) * boolReal (X ω j.1) + Z ω j
    P[(fun ω => boolReal (X ω i)) | (inferInstance : MeasurableSpace (S → ℝ)).comap Y]
      =ᵐ[P] (fun ω => finiteEndpointMean μ i S (t : ℝ) (Y ω)) := by
  classical
  let J := insert i S
  let R : (I → Bool) → (J → Bool) := fun x j => x j.1
  have hR : Measurable R := Measurable.of_eval (fun j => measurable_pi_apply j.1)
  have hRJ : HasLaw R (finiteMarginal μ J : Measure (J → Bool))
      (μ : Measure (I → Bool)) := by
    refine ⟨hR.aemeasurable, ?_⟩
    rw [finiteMarginal, ProbabilityMeasure.toMeasure_map]
  have hRX : Measurable (R ∘ X) := hR.comp hX
  have hindR : IndepFun (R ∘ X) Z P := by
    simpa only [Function.id_comp] using hind.comp hR measurable_id
  have hSJ : S ⊆ J := Finset.subset_insert i S
  let σ : S → J := fun j => ⟨j.1, hSJ j.2⟩
  let h : (S → ℝ) → J → ℝ := fun y j => endpointObservationField S (t : ℝ) y j.1
  have hh : Measurable h := by
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply j.1).comp
      ((measurable_endpointObservationField S).comp (measurable_const.prodMk measurable_id))
  have hsum : ∀ (x : J → Bool) (y : S → ℝ),
      (∑ j, h y j * boolReal (x j)) =
        ∑ j, (y j - (t : ℝ) / 2) * boolReal (x (σ j)) :=
    fun x y => endpointObservationField_sum S J hSJ (t : ℝ) y x
  have hp := finiteBinary_condExp_independentGaussian P (finiteMarginal μ J)
    (R ∘ X) hRX (hRJ.comp hXLaw) Z hZ t hZLaw hindR σ h hh hsum
    ⟨i, Finset.mem_insert_self i S⟩
  change P[(fun ω => boolReal (X ω i)) |
      (inferInstance : MeasurableSpace (S → ℝ)).comap
        (fun ω j => (t : ℝ) * boolReal (X ω j.1) + Z ω j)] =ᵐ[P] _ at hp
  refine hp.trans (Filter.Eventually.of_forall (fun ω => ?_))
  exact (finiteEndpointMean_eq_tiltMean μ S J hSJ
    ⟨i, Finset.mem_insert_self i S⟩ (t : ℝ) _).symm

theorem finiteObservationDrift_condExp
    {Ω : Type u_20} {I : Type u_21} [MeasurableSpace Ω] [DecidableEq I]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : ProbabilityMeasure (I → Bool))
    (X : Ω → (I → Bool)) (hX : Measurable X)
    (hXLaw : HasLaw X (μ : Measure (I → Bool)) P)
    (i : I) (S : Finset I) (Z : Ω → (I → ℝ)) (hZ : Measurable Z)
    (t : ℝ≥0)
    (hZLaw : HasLaw (fun ω => fun j : S => Z ω j.1)
      (Measure.pi (fun _ : S => gaussianReal 0 t)) P)
    (hind : IndepFun X Z P) :
    let Y : Ω → (I → ℝ) := fun ω j => (t : ℝ) * boolReal (X ω j) + Z ω j
    P[(fun ω => boolReal (X ω i)) | (inferInstance : MeasurableSpace (S → ℝ)).comap
        (fun ω => fun j : S => Y ω j.1)] =ᵐ[P]
      (fun ω => finiteObservationDrift μ i S (t : ℝ) (Y ω)) := by
  let R : (I → ℝ) → (S → ℝ) := fun z j => z j.1
  have hR : Measurable R := Measurable.of_eval (fun j => measurable_pi_apply j.1)
  have hindR : IndepFun X (R ∘ Z) P := by
    simpa only [Function.id_comp] using hind.comp measurable_id hR
  have hp := finiteEndpointMean_condExp P μ X hX hXLaw i S (R ∘ Z)
    (hR.comp hZ) t hZLaw hindR
  refine hp.trans (Filter.Eventually.of_forall (fun ω => ?_))
  exact (finiteEndpointMean_restrict μ i S (t : ℝ)
    (fun j => (t : ℝ) * boolReal (X ω j) + Z ω j)).trans
    (finiteObservationDrift_eq_finiteFieldMean μ i S (t : ℝ)
      (fun j => (t : ℝ) * boolReal (X ω j) + Z ω j)).symm

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Problem336AdditiveD139.GroupBrownianPosterior

open PosteriorLimit BrownianObservationSufficiency

theorem measurable_binaryField {I : Type u_1} :
    Measurable (fun x : I → Bool => fun i => boolReal (x i)) :=
  Measurable.of_eval fun i =>
    (measurable_of_countable boolReal).comp (measurable_pi_apply i)

theorem integrable_binaryCoordinate {Ω : Type u_2} {I : Type u_3} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → I → Bool)
    (mX : Measurable X) (i : I) :
    Integrable (fun ω => boolReal (X ω i)) P := by
  apply (integrable_const (1 : ℝ)).mono'
    (((measurable_pi_apply i).comp (measurable_binaryField.comp mX)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  cases hx : X ω i <;> simp [boolReal, hx]

theorem finiteFieldMean_congr_on {I : Type u_4}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (i : I)
    (h h' : I → ℝ) (hh : ∀ j ∈ S, h j = h' j) :
    finiteFieldMean μ S h i = finiteFieldMean μ S h' i := by
  have hw (x : I → Bool) : finiteFieldWeight S h x = finiteFieldWeight S h' x := by
    unfold finiteFieldWeight
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hh j hj]
  simp only [finiteFieldMean, hw]

theorem finiteFieldMean_zero {I : Type u_5}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (i : I) :
    finiteFieldMean μ S (fun _ => 0) i =
      ∫ x, boolReal (x i) ∂(μ : Measure (I → Bool)) := by
  simp [finiteFieldMean, finiteFieldWeight]

theorem finiteFieldMean_zero_endpoint_posterior
    {I : Type u_6} {Ω : Type u_7} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : ProbabilityMeasure (I → Bool))
    {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (mB : ∀ i, Measurable (B i 0))
    (X : Ω → I → Bool) (mX : Measurable X)
    (hLaw : HasLaw X (μ : Measure (I → Bool)) P)
    (S : Finset I) (i : I) :
    (fun ω => finiteFieldMean μ S (fun j => B j 0 ω) i) =ᵐ[P]
      P[(fun ω => boolReal (X ω i)) |
        MeasurableSpace.comap (fun ω (j : (S : Set I)) => B j 0 ω) inferInstance] := by
  have := hLaw.isProbabilityMeasure
  have hzero : ∀ᵐ ω ∂P, ∀ j : S, B j 0 ω = 0 :=
    ae_all_iff.mpr (fun j => (hB j).eval_zero_ae_eq_zero)
  have hmean : (fun ω => finiteFieldMean μ S (fun j => B j 0 ω) i) =ᵐ[P]
      fun _ => ∫ x, boolReal (x i) ∂(μ : Measure (I → Bool)) := by
    filter_upwards [hzero] with ω hω
    rw [finiteFieldMean_congr_on μ S i (fun j => B j 0 ω) (fun _ => 0)
      (fun j hj => hω ⟨j, hj⟩), finiteFieldMean_zero]
  have mg : Measurable (fun x : I → Bool => boolReal (x i)) :=
    (measurable_pi_apply i).comp measurable_binaryField
  have hCE := condExp_endpoint_zero_eq_integral hB mB
    (fun ω => boolReal (X ω i)) (mg.comp mX) (S : Set I)
  have hInt : (∫ ω, boolReal (X ω i) ∂P) =
      ∫ x, boolReal (x i) ∂(μ : Measure (I → Bool)) :=
    hLaw.integral_comp mg.aestronglyMeasurable
  rw [hInt] at hCE
  exact hmean.trans hCE.symm

theorem groupDrift_ae_eq_condExp_of_endpoint_posteriors
    {Γ : Type u_8} {Ω : Type u_9} [Group Γ] [Countable Γ] [DecidableEq Γ] [MeasurableSpace Ω]
    (P : Measure Ω) (μ : ProbabilityMeasure (Γ → Bool))
    {B : Γ → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    (X : Ω → Γ → Bool) (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : Γ × ℝ≥0) => B p.1 p.2 ω) P)
    (t : ℝ≥0)
    (hEndpoint : ∀ (i : Γ) (S : Finset Γ),
      (fun ω => finiteFieldMean μ S
        (fun j => (t : ℝ) * boolReal (X ω j) + B j t ω - (t : ℝ) / 2) i) =ᵐ[P]
        P[(fun ω => boolReal (X ω i)) |
          endpointSpace
            (fun j (s : Set.Iic t) ω =>
              (s.1 : ℝ) * boolReal (X ω j) + B j s.1 ω)
            (S : Set Γ) ⟨t, by simp⟩])
    (i : Γ) :
    (fun ω => groupDrift μ (t : ℝ)
      (fun j => (t : ℝ) * boolReal (X ω j) + B j t ω) i) =ᵐ[P]
      P[(fun ω => boolReal (X ω i)) |
        observationSpace
          (fun j (s : Set.Iic t) ω =>
            (s.1 : ℝ) * boolReal (X ω j) + B j s.1 ω) Set.univ] := by
  have := hIndep.isProbabilityMeasure
  have mbit (j : Γ) : Measurable (fun ω => boolReal (X ω j)) :=
    (measurable_pi_apply j).comp (measurable_binaryField.comp mX)
  apply groupDrift_ae_eq_condExp_of_finite_posteriors P μ
    (fun j ω => boolReal (X ω j))
    (fun j (s : Set.Iic t) ω => (s.1 : ℝ) * boolReal (X ω j) + B j s.1 ω)
    (fun j s => (mbit j).const_mul _ |>.add (mB j s)) (t : ℝ) ⟨t, by simp⟩
    (fun j S => ?_) i
  have he := hEndpoint j S
  simp only [finiteObservationDrift_eq_finiteFieldMean]
  exact he.trans
    (condExp_history_eq_endpoint_all hB hIndep mB mX hX
      (fun x k => boolReal (x k)) measurable_binaryField
      (fun x => boolReal (x j))
      ((measurable_pi_apply j).comp measurable_binaryField)
      (integrable_binaryCoordinate P X mX j) (S : Set Γ) t).symm

theorem groupDrift_ae_eq_condExp_of_positive_endpoint_posteriors
    {Γ : Type u_10} {Ω : Type u_11} [Group Γ] [Countable Γ] [DecidableEq Γ] [MeasurableSpace Ω]
    (P : Measure Ω) (μ : ProbabilityMeasure (Γ → Bool))
    {B : Γ → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    (X : Ω → Γ → Bool) (mX : Measurable X)
    (hLaw : HasLaw X (μ : Measure (Γ → Bool)) P)
    (hX : IndepFun X (fun ω (p : Γ × ℝ≥0) => B p.1 p.2 ω) P)
    (t : ℝ≥0)
    (hEndpoint : 0 < t → ∀ (i : Γ) (S : Finset Γ),
      (fun ω => finiteFieldMean μ S
        (fun j => (t : ℝ) * boolReal (X ω j) + B j t ω - (t : ℝ) / 2) i) =ᵐ[P]
        P[(fun ω => boolReal (X ω i)) |
          endpointSpace
            (fun j (s : Set.Iic t) ω =>
              (s.1 : ℝ) * boolReal (X ω j) + B j s.1 ω)
            (S : Set Γ) ⟨t, by simp⟩])
    (i : Γ) :
    (fun ω => groupDrift μ (t : ℝ)
      (fun j => (t : ℝ) * boolReal (X ω j) + B j t ω) i) =ᵐ[P]
      P[(fun ω => boolReal (X ω i)) |
        observationSpace
          (fun j (s : Set.Iic t) ω =>
            (s.1 : ℝ) * boolReal (X ω j) + B j s.1 ω) Set.univ] := by
  apply groupDrift_ae_eq_condExp_of_endpoint_posteriors P μ hB hIndep mB X mX hX t
    (fun j S => ?_) i
  by_cases ht : t = 0
  · subst t
    simpa! only [NNReal.coe_zero, zero_mul, zero_div, zero_add, sub_zero,
      endpointSpace_eq_comap] using
      finiteFieldMean_zero_endpoint_posterior P μ hB (fun j => mB j 0) X mX hLaw S j
  · exact hEndpoint (pos_of_ne_zero ht) j S

theorem groupDrift_ae_eq_condExp
    {Γ : Type u_12} {Ω : Type u_13} [Group Γ] [Countable Γ] [DecidableEq Γ] [MeasurableSpace Ω]
    (P : Measure Ω) (μ : ProbabilityMeasure (Γ → Bool))
    {B : Γ → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    (X : Ω → Γ → Bool) (mX : Measurable X)
    (hLaw : HasLaw X (μ : Measure (Γ → Bool)) P)
    (hX : IndepFun X (fun ω (p : Γ × ℝ≥0) => B p.1 p.2 ω) P)
    (t : ℝ≥0) (i : Γ) :
    (fun ω => groupDrift μ (t : ℝ)
      (fun j => (t : ℝ) * boolReal (X ω j) + B j t ω) i) =ᵐ[P]
      P[(fun ω => boolReal (X ω i)) |
        observationSpace
          (fun j (s : Set.Iic t) ω =>
            (s.1 : ℝ) * boolReal (X ω j) + B j s.1 ω) Set.univ] := by
  have := hLaw.isProbabilityMeasure
  have mZ : Measurable (fun ω j => B j t ω) :=
    Measurable.of_eval (fun j => mB j t)
  have hXZ : IndepFun X (fun ω j => B j t ω) P := by
    simpa only [Function.comp_def, Function.id_def] using hX.comp measurable_id
      (show Measurable (fun f : (Γ × ℝ≥0) → ℝ => fun j => f (j, t)) by fun_prop)
  apply groupDrift_ae_eq_condExp_of_endpoint_posteriors P μ hB hIndep mB X mX hX t
    (fun j S => ?_) i
  have hSInd : iIndepFun (fun (j : S) ω => B j t ω) P :=
    (iIndepFun.precomp (g := fun j : S => (j : Γ))
      Subtype.val_injective hIndep).comp
        (fun _ f => f t) (fun _ => measurable_pi_apply t)
  have hSLaw : HasLaw (fun ω => fun j : S => B j t ω)
      (Measure.pi (fun _ : S => gaussianReal 0 t)) P :=
    iIndepFun.hasLaw_pi (fun j => (hB j).hasLaw_eval t) hSInd
  have hp := (finiteObservationDrift_condExp P μ X mX hLaw j S
    (fun ω k => B k t ω) mZ t hSLaw hXZ).symm
  simpa only [finiteObservationDrift_eq_finiteFieldMean, endpointSpace,
    MeasurableSpace.comap_process_pi, iSup_subtype, Finset.mem_coe] using hp

end Problem336AdditiveD139.GroupBrownianPosterior

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139.ReferenceObservation

variable {Γ : Type u_1} {W : Type u_2} [Group Γ] [Countable Γ] [DecidableEq Γ] [MeasurableSpace W]

theorem groupDrift_condExp_history
    (μ : ProbabilityMeasure (Γ → Bool)) (ν : ProbabilityMeasure W)
    (B : ℝ≥0 → W → ℝ) (hB : IsPreBrownianReal B (ν : Measure W))
    (hBm : ∀ t, Measurable (B t)) (t : ℝ≥0) (i : Γ) :
    (fun ω : Space Γ W => groupDrift μ (t : ℝ)
      (fun j => observation B j t ω) i) =ᵐ[law μ ν]
      (law μ ν)[(fun ω => boolReal (ω.1 i)) | ObservationNoise.historySigma B t] := by
  have hs : IndepFun (Prod.fst : Space Γ W → Γ → Bool)
      (fun ω (p : Γ × ℝ≥0) => noise B p.1 p.2 ω) (law μ ν) := by
    exact (signal_indep_noiseField μ ν).comp measurable_id
      (show Measurable (fun w : Γ → W => fun p : Γ × ℝ≥0 => B p.2 (w p.1)) by
        fun_prop)
  have hp := GroupBrownianPosterior.groupDrift_ae_eq_condExp (law μ ν) μ
    (noise_isPreBrownian μ ν B hB) (iid_noise_paths μ ν B hBm)
    (measurable_noise B hBm) Prod.fst measurable_fst (signal_hasLaw μ ν) hs t i
  have hspace : PosteriorLimit.observationSpace
      (fun j (s : Set.Iic t) (ω : Space Γ W) =>
        (s.1 : ℝ) * boolReal (ω.1 j) + noise B j s.1 ω) Set.univ =
      ObservationNoise.historySigma B t := by
    unfold PosteriorLimit.observationSpace ObservationNoise.historySigma ObservationNoise.history
    simp only [Set.mem_univ, iSup_true, MeasurableSpace.comap_process_pi, noise]
  rw [hspace] at hp
  exact hp

theorem groupDrift_condExp_filtration
    (μ : ProbabilityMeasure (Γ → Bool)) (ν : ProbabilityMeasure W)
    (B : ℝ≥0 → W → ℝ) (hB : IsPreBrownianReal B (ν : Measure W))
    (hBm : ∀ t, Measurable (B t)) (t : ℝ≥0) (i : Γ) :
    (fun ω : Space Γ W => groupDrift μ (t : ℝ)
      (fun j => observation B j t ω) i) =ᵐ[law μ ν]
      (law μ ν)[(fun ω => boolReal (ω.1 i)) | ObservationNoise.filtration hBm t] :=
  groupDrift_condExp_history μ ν B hB hBm t i

theorem groupDrift_condExp_realFiltration
    (μ : ProbabilityMeasure (Γ → Bool)) (ν : ProbabilityMeasure W)
    (B : ℝ≥0 → W → ℝ) (hB : IsPreBrownianReal B (ν : Measure W))
    (hBm : ∀ t, Measurable (B t)) (t : ℝ) (ht : 0 ≤ t) (i : Γ) :
    (fun ω : Space Γ W => groupDrift μ t
      (fun j => observation B j t.toNNReal ω) i) =ᵐ[law μ ν]
      (law μ ν)[(fun ω => boolReal (ω.1 i)) | ObservationNoise.realFiltration hBm t] := by
  simpa only [Real.coe_toNNReal _ ht, ObservationNoise.realFiltration_apply] using
    groupDrift_condExp_history μ ν B hB hBm t.toNNReal i

end Problem336AdditiveD139.ReferenceObservation

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory

namespace Problem336AdditiveD139.CantorProjective

variable {I : Type u_1} {E : Type u_2} [MeasurableSpace E]

def sites (A : Finset (I × ℕ)) : Finset I := by
  classical
  exact A.image Prod.fst

lemma mem_sites {A : Finset (I × ℕ)} (a : A) : a.1.1 ∈ sites A := by
  classical
  exact Finset.mem_image.mpr ⟨a.1, a.2, rfl⟩

lemma sites_mono {A B : Finset (I × ℕ)} (h : B ⊆ A) : sites B ⊆ sites A := by
  classical
  exact Finset.image_subset_image h

def extract (e : E ≃ᵐ (ℕ → Bool)) (A : Finset (I × ℕ))
    (x : sites A → E) : A → Bool :=
  fun a => e (x ⟨a.1.1, mem_sites a⟩) a.1.2

lemma measurable_extract (e : E ≃ᵐ (ℕ → Bool)) (A : Finset (I × ℕ)) :
    Measurable (extract e A) := by
  apply Measurable.of_eval
  intro a
  exact (measurable_pi_apply a.1.2).comp
    (e.measurable.comp (measurable_pi_apply (⟨a.1.1, mem_sites a⟩ : sites A)))

def bitFamily (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E)) (A : Finset (I × ℕ)) : Measure (A → Bool) :=
  (P (sites A)).map (extract e A)

instance bitFamily_isProbabilityMeasure (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E)) [∀ S, IsProbabilityMeasure (P S)]
    (A : Finset (I × ℕ)) : IsProbabilityMeasure (bitFamily e P A) :=
  by unfold bitFamily; exact Measure.isProbabilityMeasure_map (measurable_extract e A).aemeasurable

lemma bitFamily_projective (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E))
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P) :
    IsProjectiveMeasureFamily (α := fun _ : I × ℕ => Bool) (bitFamily e P) := by
  intro A B hBA
  unfold bitFamily
  rw [hP (sites A) (sites B) (sites_mono hBA)]
  rw [Measure.map_map (measurable_extract e B) (Finset.measurable_restrict₂ _),
    Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : I × ℕ => Bool) hBA)
      (measurable_extract e A)]
  congr 1

theorem exists_bit_limit (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E)) [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P) :
    ∃ μ : ProbabilityMeasure ((I × ℕ) → Bool),
      IsProjectiveLimit (α := fun _ : I × ℕ => Bool) (μ : Measure ((I × ℕ) → Bool)) (bitFamily e P) :=
  binary_projective_exists (bitFamily e P) (bitFamily_projective e P hP)

def extractFrom (e : E ≃ᵐ (ℕ → Bool)) (A : Finset (I × ℕ)) (S : Finset I)
    (hAS : sites A ⊆ S) (x : S → E) : A → Bool :=
  fun a => e (x ⟨a.1.1, hAS (mem_sites a)⟩) a.1.2

lemma measurable_extractFrom (e : E ≃ᵐ (ℕ → Bool)) (A : Finset (I × ℕ))
    (S : Finset I) (hAS : sites A ⊆ S) : Measurable (extractFrom e A S hAS) := by
  apply Measurable.of_eval
  intro a
  exact (measurable_pi_apply a.1.2).comp
    (e.measurable.comp (measurable_pi_apply (⟨a.1.1, hAS (mem_sites a)⟩ : S)))

lemma bitFamily_eq_map_of_sites_subset (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E))
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P)
    (A : Finset (I × ℕ)) (S : Finset I) (hAS : sites A ⊆ S) :
    bitFamily e P A = (P S).map (extractFrom e A S hAS) := by
  unfold bitFamily
  rw [hP S (sites A) hAS,
    Measure.map_map (measurable_extract e A) (Finset.measurable_restrict₂ _)]
  rfl

theorem map_finite_observations (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E))
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P)
    (μ : Measure ((I × ℕ) → Bool))
    (hμ : IsProjectiveLimit (α := fun _ : I × ℕ => Bool) μ (bitFamily e P))
    {F : Type u_3} [Fintype F] (f : F → I × ℕ) (S : Finset I)
    (hf : ∀ a, (f a).1 ∈ S) :
    μ.map (fun b a => b (f a)) =
      (P S).map (fun x a => e (x ⟨(f a).1, hf a⟩) (f a).2) := by
  classical
  let A : Finset (I × ℕ) := Finset.univ.image f
  have hA (a : F) : f a ∈ A := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hAS : sites A ⊆ S := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    exact hf a
  let r : (A → Bool) → F → Bool := fun b a => b ⟨f a, hA a⟩
  have hr : Measurable r := Measurable.of_eval (fun a => measurable_pi_apply _)
  calc
    μ.map (fun b a => b (f a)) = (μ.map A.restrict).map r := by
      rw [Measure.map_map hr (Finset.measurable_restrict _)]
      rfl
    _ = (bitFamily e P A).map r := by rw [hμ A]
    _ = ((P S).map (extractFrom e A S hAS)).map r := by
      rw [bitFamily_eq_map_of_sites_subset e P hP A S hAS]
    _ = (P S).map (fun x a => e (x ⟨(f a).1, hf a⟩) (f a).2) := by
      rw [Measure.map_map hr (measurable_extractFrom e A S hAS)]
      rfl

def encodeEquiv (e : E ≃ᵐ (ℕ → Bool)) (J : Type u_4) :
    (J → E) ≃ᵐ ((J × ℕ) → Bool) where
  toFun x p := e (x p.1) p.2
  invFun b j := e.symm (fun n => b (j, n))
  left_inv x := by ext j; exact e.symm_apply_apply (x j)
  right_inv b := by ext p; exact congrFun (e.apply_symm_apply (fun n => b (p.1, n))) p.2
  measurable_toFun := by
    exact Measurable.of_eval (fun p => (measurable_pi_apply p.2).comp
      (e.measurable.comp (measurable_pi_apply p.1)))
  measurable_invFun := by
    exact Measurable.of_eval (fun j => e.symm.measurable.comp
      (Measurable.of_eval (fun n => measurable_pi_apply (j, n))))

theorem encoded_marginal (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E)) [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P)
    (μ : Measure ((I × ℕ) → Bool))
    (hμ : IsProjectiveLimit (α := fun _ : I × ℕ => Bool) μ (bitFamily e P))
    (S : Finset I) :
    μ.map (fun b (p : S × ℕ) => b (p.1.1, p.2)) =
      (P S).map (encodeEquiv e S) := by
  let Q : Measure ((S × ℕ) → Bool) := (P S).map (encodeEquiv e S)
  have hQ : IsProjectiveLimit (α := fun _ : S × ℕ => Bool) Q
      (fun A => Q.map A.restrict) := fun _ => rfl
  apply IsProjectiveLimit.unique (P := fun A => Q.map A.restrict) ?_ hQ
  intro A
  dsimp only [Q]
  have hm : Measurable (fun (b : (I × ℕ) → Bool) (p : S × ℕ) =>
      b (p.1.1, p.2)) := by fun_prop
  rw [Measure.map_map (Finset.measurable_restrict A) hm,
    Measure.map_map (Finset.measurable_restrict A) (encodeEquiv e S).measurable]
  exact map_finite_observations e P hP μ hμ
    (fun a : A => (a.1.1.1, a.1.2)) S (fun a => a.1.1.2)

theorem decoded_isProjectiveLimit (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E)) [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P)
    (μ : Measure ((I × ℕ) → Bool))
    (hμ : IsProjectiveLimit (α := fun _ : I × ℕ => Bool) μ (bitFamily e P)) :
    IsProjectiveLimit (α := fun _ : I => E)
      (μ.map (encodeEquiv e I).symm) P := by
  intro S
  apply (encodeEquiv e S).measurableEmbedding.map_injective
  rw [Measure.map_map (Finset.measurable_restrict S) (encodeEquiv e I).symm.measurable,
    Measure.map_map (encodeEquiv e S).measurable
      ((Finset.measurable_restrict S).comp (encodeEquiv e I).symm.measurable)]
  have heq : (encodeEquiv e S) ∘ (S.restrict ∘ (encodeEquiv e I).symm) =
      (fun b (p : S × ℕ) => b (p.1.1, p.2)) := by
    funext b p
    exact congrFun (e.apply_symm_apply (fun n => b (p.1.1, n))) p.2
  rw [heq]
  exact encoded_marginal e P hP μ hμ S

theorem projective_exists_of_cantor_equiv (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E)) [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P) :
    ∃ μ : ProbabilityMeasure (I → E),
      IsProjectiveLimit (α := fun _ : I => E) (μ : Measure (I → E)) P := by
  obtain ⟨μ, hμ⟩ := exists_bit_limit e P hP
  refine ⟨μ.map (encodeEquiv e I).symm.measurable.aemeasurable, ?_⟩
  exact decoded_isProjectiveLimit e P hP (μ : Measure _) hμ

theorem real_projective_exists
    (P : (S : Finset I) → Measure (S → ℝ)) [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => ℝ) P) :
    ∃ μ : ProbabilityMeasure (I → ℝ),
      IsProjectiveLimit (α := fun _ : I => ℝ) (μ : Measure (I → ℝ)) P :=
  projective_exists_of_cantor_equiv
    (PolishSpace.measurableEquivNatBoolOfNotCountable (α := ℝ) not_countable) P hP

end Problem336AdditiveD139.CantorProjective

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139.BrownianConstruction

theorem exists_preBrownianMeasure :
    ∃ μ : ProbabilityMeasure (ℝ≥0 → ℝ),
      IsPreBrownianReal (fun t ω => ω t) (μ : Measure (ℝ≥0 → ℝ)) := by
  obtain ⟨μ, hμ⟩ := CantorProjective.real_projective_exists
    BrownianReal.projectiveFamily BrownianReal.isProjectiveMeasureFamily_projectiveFamily
  refine ⟨μ, ⟨fun I => ?_⟩⟩
  exact ⟨(Finset.measurable_restrict I).aemeasurable, hμ I⟩

def preBrownianMeasure : ProbabilityMeasure (ℝ≥0 → ℝ) :=
  Classical.choose exists_preBrownianMeasure

theorem isPreBrownianReal_preBrownianMeasure :
    IsPreBrownianReal (fun t ω => ω t)
      (preBrownianMeasure : Measure (ℝ≥0 → ℝ)) :=
  Classical.choose_spec exists_preBrownianMeasure

end Problem336AdditiveD139.BrownianConstruction

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace Problem336AdditiveD139.BrownianConstruction

theorem integral_pow_four_gaussianReal (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have he (t : ℝ) :
      HasDerivAt (fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2))
        ((v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2)) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul (v : ℝ)).div_const 2).exp using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  have h1 : deriv (fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => (v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    ext t
    exact (he t).deriv
  have h2 : deriv (fun t : ℝ => (v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => ((v : ℝ) + (v : ℝ)^2 * t^2) * Real.exp ((v : ℝ) * t^2 / 2) := by
    ext t
    convert! (((hasDerivAt_id t).const_mul (v : ℝ)).mul (he t)).deriv using 1
    simp only [id_eq]
    ring
  have h3 : deriv (fun t : ℝ => ((v : ℝ) + (v : ℝ)^2 * t^2) *
        Real.exp ((v : ℝ) * t^2 / 2)) =
      fun t => (3 * (v : ℝ)^2 * t + (v : ℝ)^3 * t^3) *
        Real.exp ((v : ℝ) * t^2 / 2) := by
    ext t
    convert! (((((hasDerivAt_id t).pow 2).const_mul ((v : ℝ)^2)).const_add
      (v : ℝ)).mul (he t)).deriv using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  have h4 : deriv (fun t : ℝ => (3 * (v : ℝ)^2 * t + (v : ℝ)^3 * t^3) *
        Real.exp ((v : ℝ) * t^2 / 2)) 0 = 3 * (v : ℝ)^2 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul (3 * (v : ℝ)^2)).add
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul ((v : ℝ)^3))).mul (he 0)
    convert! h.deriv using 1
    norm_num

  calc
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) =
        iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 := by
      rw [iteratedDeriv_mgf_zero (by simp)]
      rfl
    _ = 3 * (v : ℝ)^2 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add]
      rw [iteratedDeriv_succ', h1, iteratedDeriv_succ', h2,
        iteratedDeriv_succ', h3, iteratedDeriv_one]
      exact h4

theorem integral_abs_pow_four_of_hasLaw {Ω : Type u_1} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) :
    (∫ ω, |X ω| ^ 4 ∂P) = 3 * (v : ℝ) ^ 2 := by
  have heven : Even (4 : ℕ) := by decide
  simp_rw [heven.pow_abs]
  have h := hX.integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
  simpa only [Function.comp_def, integral_pow_four_gaussianReal] using h

theorem integrable_abs_pow_four_of_hasLaw {Ω : Type u_2} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) P) :
    Integrable (fun ω => |X ω| ^ 4) P := by
  have hLp : MemLp X (4 : ℕ) P := hX.hasGaussianLaw.memLp (by norm_num)
  simpa only [Real.norm_eq_abs] using hLp.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)

theorem lintegral_edist_pow_four_of_increment_law {Ω : Type u_3} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ} {v : ℝ≥0}
    (hXY : HasLaw (X - Y) (gaussianReal 0 v) P) :
    (∫⁻ ω, edist (X ω) (Y ω) ^ (4 : ℕ) ∂P) =
      ENNReal.ofReal (3 * (v : ℝ) ^ 2) := by
  simp_rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _) 4]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    exact integral_abs_pow_four_of_hasLaw hXY
  · exact integrable_abs_pow_four_of_hasLaw hXY
  · exact ae_of_all _ (fun _ => by positivity)

theorem preBrownian_integral_abs_sub_pow_four {Ω : Type u_4} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) :
    (∫ ω, |B s ω - B t ω| ^ 4 ∂P) = 3 * |(s : ℝ) - (t : ℝ)| ^ 2 := by
  convert! integral_abs_pow_four_of_hasLaw (hB.hasLaw_sub s t) using 1

theorem isKolmogorovProcess_of_gaussian_increments
    {T : Type u_5} {Ω : Type u_6} [PseudoMetricSpace T] [MeasurableSpace Ω]
    {P : Measure Ω} {X : T → Ω → ℝ}
    (hXm : ∀ t, Measurable (X t))
    (hX : ∀ s t, HasLaw (X s - X t) (gaussianReal 0 (nndist s t)) P) :
    IsKolmogorovProcess X P 4 2 3 := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology hXm (fun s t => ?_) (by norm_num)
    (by norm_num)
  have h := lintegral_edist_pow_four_of_increment_law (hX s t)
  convert! h.le using 1 <;>
    simp [edist_dist, ENNReal.ofReal_mul,
      ENNReal.ofReal_pow, dist_nonneg]

theorem isAEKolmogorovProcess_of_gaussian_increments
    {T : Type u_7} {Ω : Type u_8} [PseudoMetricSpace T] [MeasurableSpace Ω]
    {P : Measure Ω} {X : T → Ω → ℝ}
    (hXm : ∀ t, AEMeasurable (X t) P)
    (hX : ∀ s t, HasLaw (X s - X t) (gaussianReal 0 (nndist s t)) P) :
    IsAEKolmogorovProcess X P 4 2 3 := by
  let Y : T → Ω → ℝ := fun t => AEMeasurable.mk (X t) (hXm t)
  refine ⟨Y, isKolmogorovProcess_of_gaussian_increments
    (fun t => (hXm t).measurable_mk) (fun s t => ?_), fun t => (hXm t).ae_eq_mk⟩
  apply (hX s t).congr
  filter_upwards [(hXm s).ae_eq_mk, (hXm t).ae_eq_mk] with ω hs ht
  change Y s ω - Y t ω = X s ω - X t ω
  exact congrArg₂ (· - ·) hs.symm ht.symm

theorem preBrownian_isAEKolmogorovProcess {Ω : Type u_9} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsAEKolmogorovProcess B P 4 2 3 := by
  apply isAEKolmogorovProcess_of_gaussian_increments hB.aemeasurable
  intro s t
  convert! hB.hasLaw_sub s t using 1

end Problem336AdditiveD139.BrownianConstruction

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem336AdditiveD139.BrownianConstruction

def dyadicTime (p : ℕ × ℕ) : ℝ≥0 := p.2 / (2 : ℝ≥0) ^ p.1

def rationalDyadicTime (p : ℕ × ℕ) : ℚ≥0 := p.2 / (2 : ℚ≥0) ^ p.1

@[simp] theorem coe_rationalDyadicTime (p : ℕ × ℕ) :
    (rationalDyadicTime p : ℝ≥0) = dyadicTime p := by
  simp [rationalDyadicTime, dyadicTime]

@[simp] theorem dyadicTime_parent (n k : ℕ) :
    dyadicTime (n + 1, 2 * k) = dyadicTime (n, k) := by
  simp only [dyadicTime, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

@[simp] theorem rationalDyadicTime_parent (n k : ℕ) :
    rationalDyadicTime (n + 1, 2 * k) = rationalDyadicTime (n, k) := by
  simp only [rationalDyadicTime, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

theorem tendsto_dyadicTime_floor (t : ℝ≥0) :
    Tendsto (fun n : ℕ => dyadicTime (n, ⌊(t : ℝ) * (2 : ℝ)^n⌋₊))
      atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  simpa only [dyadicTime, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_ofNat, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop t.coe_nonneg).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

theorem denseRange_dyadicTime : DenseRange dyadicTime := by
  intro t
  apply mem_closure_of_tendsto (tendsto_dyadicTime_floor t)
  exact Eventually.of_forall (fun n => ⟨(n, ⌊(t : ℝ) * (2 : ℝ)^n⌋₊), rfl⟩)

theorem dist_dyadicTime_succ (n k : ℕ) :
    dist (dyadicTime (n, k + 1)) (dyadicTime (n, k)) = (1 / 2 : ℝ)^n := by
  rw [NNReal.dist_eq]
  simp only [dyadicTime, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_ofNat, Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
  have heq : ((k : ℝ) + 1) / 2^n - (k : ℝ) / 2^n = (1 / 2 : ℝ)^n := by
    rw [div_pow, one_pow]
    ring
  rw [heq, abs_of_nonneg (by positivity)]

theorem nndist_dyadicTime_succ (n k : ℕ) :
    nndist (dyadicTime (n, k + 1)) (dyadicTime (n, k)) = (1 / 2 : ℝ≥0)^n := by
  apply NNReal.coe_injective
  simpa only [coe_nndist, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat] using dist_dyadicTime_succ n k

theorem dyadic_increment_fourth_moment {Ω : Type u_1} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ s t, HasLaw (X s - X t) (gaussianReal 0 (nndist s t)) P)
    (n k : ℕ) :
    (∫ ω, |X (dyadicTime (n, k + 1)) ω - X (dyadicTime (n, k)) ω|^4 ∂P) =
      3 * (1 / 4 : ℝ)^n := by
  have h := integral_abs_pow_four_of_hasLaw
    (hX (dyadicTime (n, k + 1)) (dyadicTime (n, k)))
  rw [nndist_dyadicTime_succ] at h
  convert! h using 1
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num

theorem rationalDyadic_increment_fourth_moment {Ω : Type u_2} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℚ≥0 → Ω → ℝ}
    (hX : ∀ s t, HasLaw (X s - X t)
      (gaussianReal 0 (nndist (s : ℝ≥0) (t : ℝ≥0))) P)
    (n k : ℕ) :
    (∫ ω, |X (rationalDyadicTime (n, k + 1)) ω -
      X (rationalDyadicTime (n, k)) ω|^4 ∂P) = 3 * (1 / 4 : ℝ)^n := by
  have h := integral_abs_pow_four_of_hasLaw
    (hX (rationalDyadicTime (n, k + 1)) (rationalDyadicTime (n, k)))
  rw [coe_rationalDyadicTime, coe_rationalDyadicTime, nndist_dyadicTime_succ] at h
  convert! h using 1
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num

end Problem336AdditiveD139.BrownianConstruction

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace Problem336AdditiveD139.DyadicTail

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem measure_abs_gt_le_of_fourth_moment
    {f : Ω → ℝ} {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hf : Integrable (fun ω => |f ω| ^ 4) μ)
    (hm : (∫ ω, |f ω| ^ 4 ∂μ) ≤ M) :
    μ {ω | a < |f ω|} ≤ ENNReal.ofReal (M / a ^ 4) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (div_nonneg hM (pow_nonneg ha.le _))]
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => |f ω| ^ 4)
    (Filter.Eventually.of_forall fun ω => pow_nonneg (abs_nonneg _) _)
    hf (a ^ 4)
  calc
    (μ {ω | a < |f ω|}).toReal ≤ (μ {ω | a ^ 4 ≤ |f ω| ^ 4}).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      intro ω hω
      exact pow_le_pow_left₀ ha.le hω.le 4
    _ ≤ M / a ^ 4 := by
      apply (le_div_iff₀ (pow_pos ha 4)).2
      simpa [measureReal_def, mul_comm] using hmark.trans hm

theorem measure_exists_abs_gt_le_of_fourth_moment
    {κ : Type u_2} [Fintype κ] (f : κ → Ω → ℝ) {a M : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M)
    (hf : ∀ k, Integrable (fun ω => |f k ω| ^ 4) μ)
    (hm : ∀ k, (∫ ω, |f k ω| ^ 4 ∂μ) ≤ M) :
    μ {ω | ∃ k, a < |f k ω|} ≤
      ENNReal.ofReal ((Fintype.card κ : ℝ) * M / a ^ 4) := by
  classical
  calc
    μ {ω | ∃ k, a < |f k ω|} = μ (⋃ k, {ω | a < |f k ω|}) := by
      congr 1
      ext ω
      simp
    _ ≤ ∑ k, μ {ω | a < |f k ω|} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _k : κ, ENNReal.ofReal (M / a ^ 4) := by
      exact Finset.sum_le_sum fun k _ =>
        measure_abs_gt_le_of_fourth_moment ha hM (hf k) (hm k)
    _ = ENNReal.ofReal ((Fintype.card κ : ℝ) * M / a ^ 4) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => div_nonneg hM (pow_nonneg ha.le _))]
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem ae_eventually_forall_abs_le_of_summable_fourth_moments
    {κ : ℕ → Type u_4} [∀ n, Fintype (κ n)] (D : ∀ n, κ n → Ω → ℝ)
    {a M : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hM : ∀ n, 0 ≤ M n)
    (hD : ∀ n k, Integrable (fun ω => |D n k ω| ^ 4) μ)
    (hm : ∀ n k, (∫ ω, |D n k ω| ^ 4 ∂μ) ≤ M n)
    (hs : Summable (fun n => (Fintype.card (κ n) : ℝ) * M n / (a n) ^ 4)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ k, |D n k ω| ≤ a n := by
  have hbound := fun n => measure_exists_abs_gt_le_of_fourth_moment
    (D n) (ha n) (hM n) (hD n) (hm n)
  have hsum : (∑' n, μ {ω | ∃ k, a n < |D n k ω|}) ≠ ∞ :=
    ne_top_of_le_ne_top hs.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hbound)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simpa only [Set.mem_ofPred_eq, not_exists, not_lt] using hn

theorem dyadic_fourth_moment_cost (C : ℝ) (n : ℕ) :
    ((2 ^ n : ℕ) : ℝ) * (C * (1 / 4 : ℝ) ^ n) / ((9 / 10 : ℝ) ^ n) ^ 4 =
      C * (5000 / 6561 : ℝ) ^ n := by
  have hp : ((9 / 10 : ℝ) ^ n) ^ 4 = ((9 / 10 : ℝ) ^ 4) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 4]
  rw [hp, Nat.cast_pow, Nat.cast_ofNat]
  calc
    (2 : ℝ) ^ n * (C * (1 / 4 : ℝ) ^ n) / ((9 / 10 : ℝ) ^ 4) ^ n =
        C * ((2 * (1 / 4 : ℝ)) / ((9 / 10 : ℝ) ^ 4)) ^ n := by
      simp only [div_pow, mul_pow]
      ring
    _ = C * (5000 / 6561 : ℝ) ^ n := by norm_num

theorem ae_eventually_dyadic_abs_le
    (D : ∀ n : ℕ, Fin (2 ^ n) → Ω → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ n k, Integrable (fun ω => |D n k ω| ^ 4) μ)
    (hm : ∀ n k, (∫ ω, |D n k ω| ^ 4 ∂μ) ≤ C * (1 / 4 : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ k, |D n k ω| ≤ (9 / 10 : ℝ) ^ n := by
  apply ae_eventually_forall_abs_le_of_summable_fourth_moments D
    (fun n => pow_pos (by norm_num) n)
    (fun n => mul_nonneg hC (pow_nonneg (by norm_num) n)) hD hm
  have hs : Summable (fun n : ℕ => C * (5000 / 6561 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(5000 / 6561 : ℝ)‖ < 1)).mul_left C
  convert hs using 1
  funext n
  simp only [Fintype.card_fin]
  exact dyadic_fourth_moment_cost C n

theorem ae_all_eventually_dyadic_abs_le
    {J : Type u_3} [Countable J]
    (D : J → ∀ n : ℕ, Fin (2 ^ n) → Ω → ℝ) {C : J → ℝ} (hC : ∀ j, 0 ≤ C j)
    (hD : ∀ j n k, Integrable (fun ω => |D j n k ω| ^ 4) μ)
    (hm : ∀ j n k, (∫ ω, |D j n k ω| ^ 4 ∂μ) ≤ C j * (1 / 4 : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ j, ∀ᶠ n in atTop, ∀ k, |D j n k ω| ≤ (9 / 10 : ℝ) ^ n := by
  rw [ae_all_iff]
  intro j
  exact ae_eventually_dyadic_abs_le (D j) (hC j) (hD j) (hm j)

theorem exists_geometric_bound_of_eventually
    {κ : ℕ → Type u_5} [∀ n, Fintype (κ n)] (D : ∀ n, κ n → ℝ)
    {q : ℝ} (hq : 0 < q)
    (h : ∀ᶠ n in atTop, ∀ k, |D n k| ≤ q ^ n) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n k, |D n k| ≤ A * q ^ n := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  let s : ℕ → ℝ := fun n => ∑ k, |D n k| / q ^ n
  have hs (n : ℕ) : 0 ≤ s n := by
    exact Finset.sum_nonneg fun k _ => div_nonneg (abs_nonneg _) (pow_nonneg hq.le _)
  let A := 1 + ∑ n ∈ Finset.range N, s n
  have hA : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun n _ => hs n)
  refine ⟨A, hA, ?_⟩
  intro n k
  by_cases hn : n < N
  · have hk : |D n k| / q ^ n ≤ s n := by
      exact Finset.single_le_sum
        (fun j _ => div_nonneg (abs_nonneg _) (pow_nonneg hq.le _)) (Finset.mem_univ k)
    have hn' : s n ≤ ∑ m ∈ Finset.range N, s m :=
      Finset.single_le_sum (fun m _ => hs m) (Finset.mem_range.mpr hn)
    apply (div_le_iff₀ (pow_pos hq n)).mp
    exact hk.trans (hn'.trans (by dsimp [A]; linarith))
  · exact (hN n (Nat.le_of_not_gt hn) k).trans
      (le_mul_of_one_le_left (pow_nonneg hq.le n) hA)

theorem ae_exists_dyadic_geometric_bound
    (D : ∀ n : ℕ, Fin (2 ^ n) → Ω → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ n k, Integrable (fun ω => |D n k ω| ^ 4) μ)
    (hm : ∀ n k, (∫ ω, |D n k ω| ^ 4 ∂μ) ≤ C * (1 / 4 : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∃ A : ℝ, 1 ≤ A ∧ ∀ n k, |D n k ω| ≤ A * (9 / 10 : ℝ) ^ n := by
  filter_upwards [ae_eventually_dyadic_abs_le D hC hD hm] with ω hω
  exact exists_geometric_bound_of_eventually (fun n k => D n k ω) (by norm_num) hω

end Problem336AdditiveD139.DyadicTail

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Filter
open scoped Topology NNReal

namespace Problem336AdditiveD139.LocalDyadicContinuity

abbrev Interval (T : ℕ) := Set.Icc (0 : ℝ) (T : ℝ)

variable {T : ℕ}

def gridIndex (n : ℕ) (x : Interval T) : ℕ :=
  ⌊(2 : ℝ) ^ n * (x : ℝ)⌋₊

lemma gridIndex_le (n : ℕ) (x : Interval T) : gridIndex n x ≤ T * 2 ^ n := by
  apply Nat.floor_le_of_le
  push_cast
  nlinarith [x.property.2, pow_pos (show (0 : ℝ) < 2 by norm_num) n]

lemma gridIndex_succ_div_two (n : ℕ) (x : Interval T) :
    gridIndex (n + 1) x / 2 = gridIndex n x := by
  unfold gridIndex
  have heq : (2 : ℝ) ^ (n + 1) * (x : ℝ) = ((2 : ℝ) ^ n * (x : ℝ)) * 2 := by
    ring
  rw [heq]
  exact Nat.mul_cast_floor_div_cancel (by decide : 2 ≠ 0) _

lemma gridIndex_succ_cases (n : ℕ) (x : Interval T) :
    gridIndex (n + 1) x = 2 * gridIndex n x ∨
      gridIndex (n + 1) x = 2 * gridIndex n x + 1 := by
  have h := gridIndex_succ_div_two n x
  omega

def approximation (f : ℕ → ℕ → ℝ) (n : ℕ) (x : Interval T) : ℝ :=
  f n (gridIndex n x)

lemma approximation_increment_le (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hadj : ∀ n k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n)
    (n : ℕ) (x : Interval T) :
    |approximation f (n + 1) x - approximation f n x| ≤ a (n + 1) := by
  unfold approximation
  rcases gridIndex_succ_cases n x with heven | hodd
  · rw [heven, hcoh, sub_self, abs_zero]
    exact ha _
  · rw [hodd, ← hcoh n (gridIndex n x)]
    apply hadj
    have hle := gridIndex_le (n + 1) x
    rw [hodd] at hle
    omega

lemma gridIndex_close (n : ℕ) (x y : Interval T)
    (hxy : |(x : ℝ) - (y : ℝ)| < 1 / (2 : ℝ) ^ n) :
    gridIndex n x ≤ gridIndex n y + 1 := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hy := Nat.lt_floor_add_one ((2 : ℝ) ^ n * (y : ℝ))
  have hx0 : 0 ≤ (2 : ℝ) ^ n * (x : ℝ) := mul_nonneg hp.le x.property.1
  have hd : (2 : ℝ) ^ n * ((x : ℝ) - (y : ℝ)) < 1 := by
    have := (abs_lt.mp hxy).2
    nlinarith [mul_lt_mul_of_pos_left this hp, div_mul_cancel₀ (1 : ℝ) hp.ne']
  have hh : (2 : ℝ) ^ n * (x : ℝ) < (gridIndex n y : ℝ) + 2 := by
    change (2 : ℝ) ^ n * (y : ℝ) < (gridIndex n y : ℝ) + 1 at hy
    linarith
  have : gridIndex n x < gridIndex n y + 2 := by
    apply (Nat.floor_lt hx0).mpr
    push_cast
    exact hh
  omega

lemma approximation_close (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hadj : ∀ n k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n)
    (n : ℕ) (x y : Interval T)
    (hxy : |(x : ℝ) - (y : ℝ)| < 1 / (2 : ℝ) ^ n) :
    |approximation f n x - approximation f n y| ≤ a n := by
  have h1 := gridIndex_close n x y hxy
  have h2 := gridIndex_close n y x (by simpa [abs_sub_comm] using hxy)
  have hx := gridIndex_le n x
  have hy := gridIndex_le n y
  have hc : gridIndex n x = gridIndex n y ∨
      gridIndex n x = gridIndex n y + 1 ∨
      gridIndex n y = gridIndex n x + 1 := by omega
  unfold approximation
  rcases hc with heq | heq | heq
  · rw [heq, sub_self, abs_zero]
    exact ha n
  · rw [heq]
    exact hadj n _ (by omega)
  · rw [heq, abs_sub_comm]
    exact hadj n _ (by omega)

theorem exists_uniformContinuous_limit
    (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hadj : ∀ n k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n) :
    ∃ g : Interval T → ℝ, UniformContinuous g ∧
      TendstoUniformly (approximation f) g atTop ∧
      ∀ x, Tendsto (fun n => approximation f n x) atTop (𝓝 (g x)) := by
  have hsum' : Summable (fun n => a (n + 1)) :=
    hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hstep (x : Interval T) (n : ℕ) :
      dist (approximation f n x) (approximation f (n + 1) x) ≤ a (n + 1) := by
    rw [Real.dist_eq, abs_sub_comm]
    exact approximation_increment_le f a ha hcoh hadj n x
  have hex (x : Interval T) : ∃ z : ℝ,
      Tendsto (fun n => approximation f n x) atTop (𝓝 z) :=
    cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable (fun n => a (n + 1)) (hstep x) hsum')
  choose g hg using hex
  have hbound (n : ℕ) (x : Interval T) :
      dist (approximation f n x) (g x) ≤ ∑' m, a (n + m + 1) :=
    dist_le_tsum_of_dist_le_of_tendsto (fun n => a (n + 1))
      (hstep x) hsum' (hg x) n
  have htail : Tendsto (fun n => ∑' m, a (n + m + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add (fun n => a (n + 1))
  have hunif : TendstoUniformly (approximation f) g atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp htail).2 ε hε] with n hn
    intro x
    rw [dist_comm]
    exact (hbound n x).trans_lt hn
  refine ⟨g, ?_, hunif, hg⟩
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  have htotal : Tendsto (fun n => 2 * (∑' m, a (n + m + 1)) + a n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (htail.const_mul 2).add hsum.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := ((tendsto_order.mp htotal).2 ε hε).exists
  refine ⟨1 / (2 : ℝ) ^ N, by positivity, ?_⟩
  intro x y hxy
  change dist (x : ℝ) (y : ℝ) < 1 / (2 : ℝ) ^ N at hxy
  have hc : |approximation f N x - approximation f N y| ≤ a N :=
    approximation_close f a ha hadj N x y (by simpa only [Real.dist_eq] using hxy)
  have hx := hbound N x
  have hy := hbound N y
  have hx' : dist (g x) (approximation f N x) ≤ ∑' m, a (N + m + 1) := by
    simpa only [dist_comm] using hx
  have htri := dist_triangle4 (g x) (approximation f N x) (approximation f N y) (g y)
  rw [Real.dist_eq (approximation f N x) (approximation f N y)] at htri
  exact (htri.trans (by linarith)).trans_lt hN

lemma coherent_refinement (f : ℕ → ℕ → ℝ)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k) (n k l : ℕ) :
    f (n + l) (2 ^ l * k) = f n k := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [show n + (l + 1) = (n + l) + 1 by omega,
      show 2 ^ (l + 1) * k = 2 * (2 ^ l * k) by ring, hcoh, ih]

lemma gridIndex_at_node (n k l : ℕ) (x : Interval T)
    (hx : (x : ℝ) = (k : ℝ) / (2 : ℝ) ^ n) :
    gridIndex (n + l) x = 2 ^ l * k := by
  unfold gridIndex
  rw [hx]
  have heq : (2 : ℝ) ^ (n + l) * ((k : ℝ) / (2 : ℝ) ^ n) =
      ((2 ^ l * k : ℕ) : ℝ) := by
    push_cast
    rw [pow_add]
    field_simp
  rw [heq, Nat.floor_natCast]

theorem limit_agrees_grid (f : ℕ → ℕ → ℝ) (g : Interval T → ℝ)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hlim : ∀ x, Tendsto (fun n => approximation f n x) atTop (𝓝 (g x)))
    (n k : ℕ) (x : Interval T) (hx : (x : ℝ) = (k : ℝ) / (2 : ℝ) ^ n) :
    g x = f n k := by
  have hevent : (fun m => approximation f m x) =ᶠ[atTop] fun _ => f n k := by
    refine eventually_atTop.mpr ⟨n, fun m hm => ?_⟩
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hm
    dsimp only [approximation]
    rw [gridIndex_at_node n k l x hx, coherent_refinement f hcoh]
  exact tendsto_nhds_unique (hlim x) (tendsto_const_nhds.congr' hevent.symm)

def limit (f : ℕ → ℕ → ℝ) (x : Interval T) : ℝ :=
  limUnder atTop (fun n => approximation f n x)

theorem uniformContinuous_limit (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hadj : ∀ n k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n) :
    UniformContinuous (limit (T := T) f) ∧
      TendstoUniformly (approximation f) (limit (T := T) f) atTop ∧
      ∀ x, Tendsto (fun n => approximation f n x) atTop (𝓝 (limit (T := T) f x)) := by
  obtain ⟨g, hcont, hunif, hlim⟩ :=
    exists_uniformContinuous_limit (T := T) f a ha hsum hcoh hadj
  have heq : limit (T := T) f = g := funext fun x => (hlim x).limUnder_eq
  rw [heq]
  exact ⟨hcont, hunif, hlim⟩

theorem uniformContinuous_limit_of_eventually (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hadj : ∀ᶠ n in atTop, ∀ k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n) :
    UniformContinuous (limit (T := T) f) ∧
      TendstoUniformly (approximation f) (limit (T := T) f) atTop ∧
      ∀ x, Tendsto (fun n => approximation f n x) atTop (𝓝 (limit (T := T) f x)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hadj
  let b : ℕ → ℝ := fun n =>
    if n < N then ∑ k ∈ Finset.range (T * 2 ^ n), |f n (k + 1) - f n k| else a n
  have hb : ∀ n, 0 ≤ b n := by
    intro n
    dsimp [b]
    split_ifs
    · exact Finset.sum_nonneg fun k _ => abs_nonneg _
    · exact ha n
  have hab : a =ᶠ[cofinite] b := by
    rw [Nat.cofinite_eq_atTop]
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    simp [b, not_lt.mpr hn]
  have hbsum : Summable b := hsum.congr_cofinite hab
  apply uniformContinuous_limit (T := T) f b hb hbsum hcoh
  intro n k hk
  by_cases hn : n < N
  · dsimp [b]
    rw [ite_eq_left hn]
    exact Finset.single_le_sum (f := fun j => |f n (j + 1) - f n j|)
      (fun j _ => abs_nonneg _) (Finset.mem_range.mpr hk)
  · simpa [b, hn] using hN n (not_lt.mp hn) k hk

theorem measurable_limit_eval {Ω : Type u_1} [MeasurableSpace Ω]
    (f : Ω → ℕ → ℕ → ℝ) (hf : ∀ n k, Measurable (fun ω => f ω n k))
    (x : Interval T) : Measurable (fun ω => limit (T := T) (f ω) x) := by
  exact (MeasureTheory.StronglyMeasurable.limUnder
    (fun n => (hf n (gridIndex n x)).stronglyMeasurable)).measurable

theorem measurable_limit {Ω : Type u_2} [MeasurableSpace Ω]
    (f : Ω → ℕ → ℕ → ℝ) (hf : ∀ n k, Measurable (fun ω => f ω n k)) :
    Measurable (fun ω => limit (T := T) (f ω)) :=
  Measurable.of_eval (fun x => measurable_limit_eval f hf x)

def globalLimit (f : ℕ → ℕ → ℝ) (t : ℝ≥0) : ℝ :=
  limUnder atTop (fun n => f n ⌊(2 : ℝ) ^ n * (t : ℝ)⌋₊)

theorem continuous_globalLimit (f : ℕ → ℕ → ℝ)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hlocal : ∀ T : ℕ, ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧ Summable a ∧
      ∀ᶠ n in atTop, ∀ k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n) :
    Continuous (globalLimit f) := by
  have hcont (T : ℕ) : ContinuousOn (globalLimit f) (Set.Iic (T : ℝ≥0)) := by
    obtain ⟨a, ha, hsum, hadj⟩ := hlocal T
    have hc := (uniformContinuous_limit_of_eventually f a ha hsum hcoh hadj).1.continuous
    let e : Set.Iic (T : ℝ≥0) → Interval T := fun x =>
      ⟨(x.val : ℝ), x.val.property, by exact_mod_cast x.property⟩
    have he : Continuous e :=
      (NNReal.continuous_coe.comp continuous_subtype_val).subtype_mk _
    rw [continuousOn_iff_continuous_domRestrict]
    have hce : Continuous ((limit (T := T) f) ∘ e) := hc.comp he
    simpa only [Function.comp_def, Set.domRestrict_def, globalLimit, limit,
      approximation, gridIndex, e] using hce
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨T, hT⟩ := exists_nat_gt (t : ℝ)
  have hT' : t < (T : ℝ≥0) := by exact_mod_cast hT
  exact (hcont T).continuousAt
    (mem_of_superset (Iio_mem_nhds hT') Set.Iio_subset_Iic_self)

theorem globalLimit_agrees_grid (f : ℕ → ℕ → ℝ)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hlocal : ∀ T : ℕ, ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧ Summable a ∧
      ∀ᶠ n in atTop, ∀ k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n)
    (n k : ℕ) (t : ℝ≥0) (ht : (t : ℝ) = (k : ℝ) / (2 : ℝ) ^ n) :
    globalLimit f t = f n k := by
  obtain ⟨T, hT⟩ := exists_nat_gt (t : ℝ)
  obtain ⟨a, ha, hsum, hadj⟩ := hlocal T
  have hh := uniformContinuous_limit_of_eventually f a ha hsum hcoh hadj
  let x : Interval T := ⟨(t : ℝ), t.property, hT.le⟩
  exact limit_agrees_grid f (limit (T := T) f) hcoh hh.2.2 n k x ht

theorem measurable_globalLimit_eval {Ω : Type u_3} [MeasurableSpace Ω]
    (f : Ω → ℕ → ℕ → ℝ) (hf : ∀ n k, Measurable (fun ω => f ω n k))
    (t : ℝ≥0) : Measurable (fun ω => globalLimit (f ω) t) := by
  exact (MeasureTheory.StronglyMeasurable.limUnder
    (fun n => (hf n ⌊(2 : ℝ) ^ n * (t : ℝ)⌋₊).stronglyMeasurable)).measurable

theorem measurable_globalLimit {Ω : Type u_4} [MeasurableSpace Ω]
    (f : Ω → ℕ → ℕ → ℝ) (hf : ∀ n k, Measurable (fun ω => f ω n k)) :
    Measurable (fun ω => globalLimit (f ω)) :=
  Measurable.of_eval (fun t => measurable_globalLimit_eval f hf t)

theorem ae_globalLimit_properties {Ω : Type u_5} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (f : Ω → ℕ → ℕ → ℝ)
    (hcoh : ∀ᵐ ω ∂P, ∀ n k, f ω (n + 1) (2 * k) = f ω n k)
    (hlocal : ∀ T : ℕ, ∀ᵐ ω ∂P, ∃ a : ℕ → ℝ,
      (∀ n, 0 ≤ a n) ∧ Summable a ∧
      ∀ᶠ n in atTop, ∀ k, k < T * 2 ^ n → |f ω n (k + 1) - f ω n k| ≤ a n) :
    ∀ᵐ ω ∂P, Continuous (globalLimit (f ω)) ∧
      ∀ (n k : ℕ) (t : ℝ≥0), (t : ℝ) = (k : ℝ) / (2 : ℝ) ^ n →
        globalLimit (f ω) t = f ω n k := by
  filter_upwards [hcoh, MeasureTheory.ae_all_iff.mpr hlocal] with ω hc hl
  exact ⟨continuous_globalLimit (f ω) hc hl,
    fun n k t ht => globalLimit_agrees_grid (f ω) hc hl n k t ht⟩

theorem ae_globalLimit_properties_of_eventually {Ω : Type u_6} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (f : Ω → ℕ → ℕ → ℝ) (a : ℕ → ℕ → ℝ)
    (ha : ∀ T n, 0 ≤ a T n) (hsum : ∀ T, Summable (a T))
    (hcoh : ∀ᵐ ω ∂P, ∀ n k, f ω (n + 1) (2 * k) = f ω n k)
    (hadj : ∀ T : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∀ k, k < T * 2 ^ n → |f ω n (k + 1) - f ω n k| ≤ a T n) :
    ∀ᵐ ω ∂P, Continuous (globalLimit (f ω)) ∧
      ∀ (n k : ℕ) (t : ℝ≥0), (t : ℝ) = (k : ℝ) / (2 : ℝ) ^ n →
        globalLimit (f ω) t = f ω n k := by
  apply ae_globalLimit_properties P f hcoh
  intro T
  filter_upwards [hadj T] with ω hω
  exact ⟨a T, ha T, hsum T, hω⟩

end Problem336AdditiveD139.LocalDyadicContinuity

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology NNReal

namespace Problem336AdditiveD139.DensePathExtension

local instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

def restrictPath {D : Type u_1} (e : D → ℝ≥0) (f : C(ℝ≥0, ℝ)) : D → ℝ :=
  fun d => f (e d)

lemma measurable_restrictPath {D : Type u_2} (e : D → ℝ≥0) :
    Measurable (restrictPath e) := by
  exact Measurable.of_eval (fun d => (continuous_eval_const (e d)).measurable)

lemma injective_restrictPath {D : Type u_3} (e : D → ℝ≥0) (he : DenseRange e) :
    Injective (restrictPath e) := by
  intro f g h
  apply ContinuousMap.ext
  exact congr_fun (he.equalizer f.continuous g.continuous h)

lemma measurableEmbedding_restrictPath {D : Type u_4} [Countable D]
    (e : D → ℝ≥0) (he : DenseRange e) : MeasurableEmbedding (restrictPath e) :=
  (measurable_restrictPath e).measurableEmbedding (injective_restrictPath e he)

def Continuable {D : Type u_5} (e : D → ℝ≥0) (x : D → ℝ) : Prop :=
  ∃ f : C(ℝ≥0, ℝ), restrictPath e f = x

lemma measurableSet_continuable {D : Type u_6} [Countable D]
    (e : D → ℝ≥0) (he : DenseRange e) : MeasurableSet {x | Continuable e x} :=
  (measurableEmbedding_restrictPath e he).measurableSet_range

def extendPath {D : Type u_7} (e : D → ℝ≥0) : (D → ℝ) → C(ℝ≥0, ℝ) :=
  Function.extend (restrictPath e) id (fun _ => 0)

lemma measurable_extendPath {D : Type u_8} [Countable D]
    (e : D → ℝ≥0) (he : DenseRange e) : Measurable (extendPath e) :=
  (measurableEmbedding_restrictPath e he).measurable_extend measurable_id measurable_const

@[simp] lemma extendPath_restrictPath {D : Type u_9}
    (e : D → ℝ≥0) (he : DenseRange e) (f : C(ℝ≥0, ℝ)) :
    extendPath e (restrictPath e f) = f :=
  (injective_restrictPath e he).extend_apply id (fun _ => 0) f

lemma restrictPath_extendPath {D : Type u_10}
    (e : D → ℝ≥0) (he : DenseRange e) {x : D → ℝ} (hx : Continuable e x) :
    restrictPath e (extendPath e x) = x := by
  rcases hx with ⟨f, rfl⟩
  rw [extendPath_restrictPath e he]

lemma extendPath_eq_zero_of_not_continuable {D : Type u_11}
    (e : D → ℝ≥0) {x : D → ℝ} (hx : ¬ Continuable e x) : extendPath e x = 0 := by
  exact Function.extend_apply' _ _ _ hx

def LocalCauchyData {D : Type u_12} (e : D → ℝ≥0) (x : D → ℝ) : Prop :=
  ∀ t : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ i j : D, dist (e i) t < δ → dist (e j) t < δ → dist (x i) (x j) < ε

lemma continuable_of_localCauchyData {D : Type u_13}
    (e : D → ℝ≥0) (he : DenseRange e) {x : D → ℝ} (hx : LocalCauchyData e x) :
    Continuable e x := by
  let : TopologicalSpace D := TopologicalSpace.induced e inferInstance
  have hd : IsDenseInducing e := ⟨⟨rfl⟩, he⟩
  have hc (t : ℝ≥0) : Cauchy (Filter.map x (Filter.comap e (𝓝 t))) := by
    refine Metric.cauchy_iff.mpr ⟨(hd.comap_nhds_neBot t).map x, ?_⟩
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := hx t ε hε
    refine ⟨x '' (e ⁻¹' Metric.ball t δ),
      Filter.image_mem_map (Filter.preimage_mem_comap (Metric.ball_mem_nhds t hδ)), ?_⟩
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact hmod i j hi hj
  have hlim (t : ℝ≥0) : ∃ a : ℝ, Tendsto x (Filter.comap e (𝓝 t)) (𝓝 a) :=
    CompleteSpace.complete (hc t)
  refine ⟨⟨hd.extend x, hd.continuous_extend hlim⟩, ?_⟩
  exact funext (hd.extend_eq' hlim)

lemma localCauchyData_of_continuable {D : Type u_14}
    (e : D → ℝ≥0) {x : D → ℝ} (hx : Continuable e x) : LocalCauchyData e x := by
  rcases hx with ⟨f, rfl⟩
  intro t ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt (ε / 2)
    (half_pos hε)
  refine ⟨δ, hδ, fun i j hi hj => ?_⟩
  calc
    dist (f (e i)) (f (e j)) ≤ dist (f (e i)) (f t) + dist (f t) (f (e j)) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hmod hi) (by simpa [dist_comm] using hmod hj)
    _ = ε := by ring

lemma continuable_iff_localCauchyData {D : Type u_15}
    (e : D → ℝ≥0) (he : DenseRange e) (x : D → ℝ) :
    Continuable e x ↔ LocalCauchyData e x :=
  ⟨localCauchyData_of_continuable e, continuable_of_localCauchyData e he⟩

lemma measurableSet_localCauchyData {D : Type u_16} [Countable D]
    (e : D → ℝ≥0) (he : DenseRange e) : MeasurableSet {x | LocalCauchyData e x} := by
  simpa only [← continuable_iff_localCauchyData e he] using measurableSet_continuable e he

def UniformOnBoundedData {D : Type u_17} (e : D → ℝ≥0) (x : D → ℝ) : Prop :=
  ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ i j : D, e i ≤ N → e j ≤ N → dist (e i) (e j) < δ → dist (x i) (x j) < ε

lemma localCauchyData_of_uniformOnBoundedData {D : Type u_18}
    (e : D → ℝ≥0) {x : D → ℝ} (hx : UniformOnBoundedData e x) :
    LocalCauchyData e x := by
  intro t ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((t : ℝ) + 1)
  obtain ⟨δ, hδ, hmod⟩ := hx N ε hε
  refine ⟨min 1 (δ / 2), lt_min zero_lt_one (half_pos hδ), fun i j hi hj => ?_⟩
  have hi1 : dist (e i) t < 1 := lt_of_lt_of_le hi (min_le_left _ _)
  have hj1 : dist (e j) t < 1 := lt_of_lt_of_le hj (min_le_left _ _)
  have hiN : e i ≤ N := by
    rw [NNReal.dist_eq, abs_sub_lt_iff] at hi1
    exact_mod_cast (show (e i : ℝ) ≤ N by linarith [hi1.1])
  have hjN : e j ≤ N := by
    rw [NNReal.dist_eq, abs_sub_lt_iff] at hj1
    exact_mod_cast (show (e j : ℝ) ≤ N by linarith [hj1.1])
  apply hmod i j hiN hjN
  calc
    dist (e i) (e j) ≤ dist (e i) t + dist t (e j) := dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := add_lt_add
      (lt_of_lt_of_le hi (min_le_right _ _))
      (by simpa [dist_comm] using lt_of_lt_of_le hj (min_le_right 1 (δ / 2)))
    _ = δ := by ring

lemma continuable_of_uniformOnBoundedData {D : Type u_19}
    (e : D → ℝ≥0) (he : DenseRange e) {x : D → ℝ} (hx : UniformOnBoundedData e x) :
    Continuable e x :=
  continuable_of_localCauchyData e he (localCauchyData_of_uniformOnBoundedData e hx)

def liftLaw {D : Type u_20} [Countable D] (e : D → ℝ≥0) (he : DenseRange e)
    (μ : ProbabilityMeasure (D → ℝ)) : ProbabilityMeasure C(ℝ≥0, ℝ) :=
  ⟨(μ : Measure (D → ℝ)).map (extendPath e), ⟨by
    rw [Measure.map_apply (measurable_extendPath e he) MeasurableSet.univ]
    simp⟩⟩

lemma map_restrictPath_liftLaw {D : Type u_21} [Countable D]
    (e : D → ℝ≥0) (he : DenseRange e) (μ : ProbabilityMeasure (D → ℝ))
    (hμ : ∀ᵐ x ∂(μ : Measure (D → ℝ)), Continuable e x) :
    Measure.map (restrictPath e) (liftLaw e he μ : Measure C(ℝ≥0, ℝ)) =
      (μ : Measure (D → ℝ)) := by
  change Measure.map (restrictPath e)
    (Measure.map (extendPath e) (μ : Measure (D → ℝ))) = _
  rw [Measure.map_map (measurable_restrictPath e) (measurable_extendPath e he)]
  calc
    Measure.map (restrictPath e ∘ extendPath e) (μ : Measure (D → ℝ)) =
        Measure.map id (μ : Measure (D → ℝ)) :=
      Measure.map_congr (hμ.mono fun x hx => restrictPath_extendPath e he hx)
    _ = _ := Measure.map_id

theorem exists_measurable_path_realization {D : Type u_22} {Ω : Type u_23} [Countable D] [MeasurableSpace Ω]
    (e : D → ℝ≥0) (he : DenseRange e) (P : Measure Ω) (X : Ω → D → ℝ)
    (hX : Measurable X) (hc : ∀ᵐ ω ∂P, LocalCauchyData e (X ω)) :
    ∃ Y : Ω → C(ℝ≥0, ℝ), Measurable Y ∧
      ∀ᵐ ω ∂P, ∀ d : D, Y ω (e d) = X ω d := by
  refine ⟨extendPath e ∘ X, (measurable_extendPath e he).comp hX, ?_⟩
  filter_upwards [hc] with ω hω
  exact congr_fun (restrictPath_extendPath e he (continuable_of_localCauchyData e he hω))

end Problem336AdditiveD139.DensePathExtension

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem336AdditiveD139.BrownianConstruction

theorem preBrownian_ae_dyadic_bound {Ω : Type u_1} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (T : ℕ) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ k, k < T * 2 ^ n →
      |B (dyadicTime (n, k + 1)) ω - B (dyadicTime (n, k)) ω| ≤
        (9 / 10 : ℝ) ^ n := by
  let D : ∀ n, Fin (T * 2 ^ n) → Ω → ℝ := fun n k ω =>
    B (dyadicTime (n, k.val + 1)) ω - B (dyadicTime (n, k.val)) ω
  have hD (n) (k : Fin (T * 2 ^ n)) : Integrable (fun ω => |D n k ω| ^ 4) P :=
    integrable_abs_pow_four_of_hasLaw
      (hB.hasLaw_sub (dyadicTime (n, k.val + 1)) (dyadicTime (n, k.val)))
  have hm (n) (k : Fin (T * 2 ^ n)) :
      (∫ ω, |D n k ω| ^ 4 ∂P) ≤ 3 * (1 / 4 : ℝ) ^ n := by
    apply le_of_eq
    exact dyadic_increment_fourth_moment (fun s t => by
      convert hB.hasLaw_sub s t using 1; rfl) n k.val
  have hs : Summable (fun n : ℕ =>
      (Fintype.card (Fin (T * 2 ^ n)) : ℝ) * (3 * (1 / 4 : ℝ)^n) /
        ((9 / 10 : ℝ)^n)^4) := by
    have hgeom : Summable (fun n : ℕ =>
        (T : ℝ) * (3 * (5000 / 6561 : ℝ)^n)) :=
      ((summable_geometric_of_norm_lt_one
        (by norm_num : ‖(5000 / 6561 : ℝ)‖ < 1)).mul_left 3).mul_left (T : ℝ)
    convert hgeom using 1
    funext n
    simp only [Fintype.card_fin, Nat.cast_mul]
    calc
      _ = (T : ℝ) * (((2 ^ n : ℕ) : ℝ) * (3 * (1 / 4 : ℝ)^n) /
          ((9 / 10 : ℝ)^n)^4) := by ring
      _ = _ := congrArg (fun x : ℝ => (T : ℝ) * x)
        (DyadicTail.dyadic_fourth_moment_cost 3 n)
  have h := DyadicTail.ae_eventually_forall_abs_le_of_summable_fourth_moments
    D (fun n => pow_pos (by norm_num) n) (fun n => by positivity) hD hm hs
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  intro k hk
  exact hn ⟨k, hk⟩

theorem preBrownian_ae_continuable {Ω : Type u_2} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, DensePathExtension.Continuable dyadicTime
      (fun p => B (dyadicTime p) ω) := by
  have hr := LocalDyadicContinuity.ae_globalLimit_properties_of_eventually P
    (fun ω n k => B (dyadicTime (n, k)) ω)
    (fun _ n => (9 / 10 : ℝ)^n)
    (fun _ n => by positivity)
    (fun _ => summable_geometric_of_norm_lt_one (by norm_num))
    (ae_of_all _ (fun ω n k => by rw [dyadicTime_parent]))
    (preBrownian_ae_dyadic_bound hB)
  filter_upwards [hr] with ω hω
  refine ⟨⟨_, hω.1⟩, ?_⟩
  funext p
  exact hω.2 p.1 p.2 (dyadicTime p) rfl

end Problem336AdditiveD139.BrownianConstruction

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem336AdditiveD139.ContinuousModification

variable {Ω : Type u_1} {E : Type u_2} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_cauchySeq_of_summable_bad_increments [MetricSpace E]
    (f : ℕ → Ω → E) (r : ℕ → ℝ) (hr : Summable r)
    (hbad : (∑' n, μ {ω | r n < dist (f n ω) (f (n + 1) ω)}) ≠ ∞) :
    ∀ᵐ ω ∂μ, CauchySeq (fun n => f n ω) := by
  filter_upwards [ae_eventually_notMem hbad] with ω hω
  apply cauchySeq_of_summable_dist
  apply hr.of_norm_bounded_eventually_nat
  filter_upwards [hω] with n hn
  simpa only [Set.mem_ofPred_eq, not_lt, Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
    using hn

theorem exists_measurable_limit_of_summable_bad_increments
    [MetricSpace E] [CompleteSpace E] [Nonempty E]
    [MeasurableSpace E] [BorelSpace E]
    (f : ℕ → Ω → E) (hf : ∀ n, AEMeasurable (f n) μ)
    (r : ℕ → ℝ) (hr : Summable r)
    (hbad : (∑' n, μ {ω | r n < dist (f n ω) (f (n + 1) ω)}) ≠ ∞) :
    ∃ g : Ω → E, Measurable g ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
  let g : Ω → E := fun ω => limUnder atTop (fun n => f n ω)
  have hg : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [ae_cauchySeq_of_summable_bad_increments f r hr hbad] with ω hω
    exact hω.tendsto_limUnder
  have hgm : AEMeasurable g μ := aemeasurable_of_tendsto_metrizable_ae atTop hf hg
  refine ⟨hgm.mk g, hgm.measurable_mk, ?_⟩
  filter_upwards [hg, hgm.ae_eq_mk] with ω hω heq
  simpa only [← heq] using hω

theorem ae_eq_of_ae_tendsto_of_tendstoInMeasure [MetricSpace E]
    {f : ℕ → Ω → E} {g h : Ω → E}
    (hg : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hh : TendstoInMeasure μ f atTop h) : g =ᵐ[μ] h := by
  obtain ⟨ns, hns, hlim⟩ := hh.exists_seq_tendsto_ae
  filter_upwards [hg, hlim] with ω hω hω'
  exact tendsto_nhds_unique (hω.comp hns.tendsto_atTop) hω'

theorem exists_measurable_limit_with_modifications
    [MetricSpace E] [CompleteSpace E] [Nonempty E]
    [MeasurableSpace E] [BorelSpace E]
    {T : Type u_3} {V : Type u_4} [MetricSpace V]
    (f : ℕ → Ω → E) (hf : ∀ n, AEMeasurable (f n) μ)
    (r : ℕ → ℝ) (hr : Summable r)
    (hbad : (∑' n, μ {ω | r n < dist (f n ω) (f (n + 1) ω)}) ≠ ∞)
    (eval : T → E → V) (heval : ∀ t, Continuous (eval t))
    (X : T → Ω → V)
    (hX : ∀ t, TendstoInMeasure μ (fun n ω => eval t (f n ω)) atTop (X t)) :
    ∃ g : Ω → E, Measurable g ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) ∧
      ∀ t, (fun ω => eval t (g ω)) =ᵐ[μ] X t := by
  obtain ⟨g, hgm, hg⟩ := exists_measurable_limit_of_summable_bad_increments
    f hf r hr hbad
  refine ⟨g, hgm, hg, fun t => ?_⟩
  apply ae_eq_of_ae_tendsto_of_tendstoInMeasure _ (hX t)
  filter_upwards [hg] with ω hω
  exact ((heval t).tendsto (g ω)).comp hω

end Problem336AdditiveD139.ContinuousModification

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

namespace Problem336AdditiveD139.BrownianStochasticContinuity

variable {Ω : Type u_1} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem tendstoInMeasure_eval {ι : Type u_2} {l : Filter ι}
    (hB : IsPreBrownianReal B P) {u : ι → ℝ≥0} {t : ℝ≥0}
    (hu : Tendsto u l (𝓝 t)) : TendstoInMeasure P (fun i => B (u i)) l (B t) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hbound (i : ι) : P {ω | ε ≤ ‖B (u i) ω - B t ω‖} ≤
      ENNReal.ofReal (dist (u i : ℝ) (t : ℝ) / ε ^ 2) := by
    have hL := hB.hasLaw_sub (u i) t
    have hmean : (∫ ω, B (u i) ω - B t ω ∂P) = 0 := by
      change P[B (u i) - B t] = 0
      rw [hL.integral_eq, integral_id_gaussianReal]
    have hvar : Var[B (u i) - B t; P] = dist (u i : ℝ) (t : ℝ) := by
      rw [hL.variance_eq, variance_id_gaussianReal]
      rfl
    simpa only [hmean, sub_zero, hvar, Pi.sub_apply, Real.norm_eq_abs] using
      meas_ge_le_variance_div_sq hL.hasGaussianLaw.memLp_two hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun _ => bot_le) hbound
  have hu' : Tendsto (fun i => (u i : ℝ)) l (𝓝 (t : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hu
  have hd := (hu'.dist (tendsto_const_nhds (x := (t : ℝ)))).div_const (ε ^ 2)
  simpa only [Function.comp_def, dist_self, zero_div, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hd

theorem ae_eq_of_tendsto_times (hB : IsPreBrownianReal B P)
    (W : Ω → C(ℝ≥0, ℝ)) {u : ℕ → ℝ≥0} {t : ℝ≥0}
    (hu : Tendsto u atTop (𝓝 t))
    (hversion : ∀ n, (fun ω => W ω (u n)) =ᵐ[P] B (u n)) :
    (fun ω => W ω t) =ᵐ[P] B t := by
  apply ContinuousModification.ae_eq_of_ae_tendsto_of_tendstoInMeasure _
    (tendstoInMeasure_eval hB hu)
  filter_upwards [ae_all_iff.mpr hversion] with ω hω
  have hlim := ((W ω).continuous.tendsto t).comp hu
  simpa only [Function.comp_def, hω] using hlim

theorem ae_eq_of_dense (hB : IsPreBrownianReal B P)
    (W : Ω → C(ℝ≥0, ℝ)) {D : Type u_3} (e : D → ℝ≥0) (he : DenseRange e)
    (hversion : ∀ d, (fun ω => W ω (e d)) =ᵐ[P] B (e d)) (t : ℝ≥0) :
    (fun ω => W ω t) =ᵐ[P] B t := by
  classical
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (he t)
  choose v hv using hu
  have hvlim : Tendsto (fun n => e (v n)) atTop (𝓝 t) := by
    simpa only [hv] using hlim
  exact ae_eq_of_tendsto_times hB W hvlim (fun n => hversion (v n))

theorem isBrownianReal_of_dense (hB : IsPreBrownianReal B P)
    (W : Ω → C(ℝ≥0, ℝ)) {D : Type u_4} (e : D → ℝ≥0) (he : DenseRange e)
    (hversion : ∀ d, (fun ω => W ω (e d)) =ᵐ[P] B (e d)) :
    IsBrownianReal (fun t ω => W ω t) P := by
  exact ⟨hB.congr (fun t => (ae_eq_of_dense hB W e he hversion t).symm),
    ae_of_all _ (fun ω => (W ω).continuous)⟩

end Problem336AdditiveD139.BrownianStochasticContinuity

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336AdditiveD139.BrownianConstruction

local instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

def brownianRealization : (ℝ≥0 → ℝ) → C(ℝ≥0, ℝ) := fun ω =>
  DensePathExtension.extendPath dyadicTime (fun p => ω (dyadicTime p))

lemma measurable_brownianRealization : Measurable brownianRealization :=
  (DensePathExtension.measurable_extendPath dyadicTime denseRange_dyadicTime).comp
    (Measurable.of_eval (fun p => measurable_pi_apply (dyadicTime p)))

theorem isBrownianReal_brownianRealization :
    IsBrownianReal (fun t ω => brownianRealization ω t)
      (preBrownianMeasure : Measure (ℝ≥0 → ℝ)) := by
  apply BrownianStochasticContinuity.isBrownianReal_of_dense
    isPreBrownianReal_preBrownianMeasure brownianRealization
    dyadicTime denseRange_dyadicTime
  intro p
  filter_upwards [preBrownian_ae_continuable isPreBrownianReal_preBrownianMeasure] with ω hω
  exact congrFun (DensePathExtension.restrictPath_extendPath
    dyadicTime denseRange_dyadicTime hω) p

theorem exists_brownianPathMeasure :
    ∃ ν : ProbabilityMeasure C(ℝ≥0, ℝ),
      IsBrownianReal (fun t w => w t) (ν : Measure C(ℝ≥0, ℝ)) := by
  let ν := preBrownianMeasure.map measurable_brownianRealization.aemeasurable
  refine ⟨ν, ⟨⟨fun I => ?_⟩, ae_of_all _ (fun w => w.continuous)⟩⟩
  have hm : Measurable (fun w : C(ℝ≥0, ℝ) => I.restrict (fun t => w t)) :=
    Measurable.of_eval (fun t => (continuous_eval_const (t : ℝ≥0)).measurable)
  refine ⟨hm.aemeasurable, ?_⟩
  change Measure.map _ (preBrownianMeasure.map
    measurable_brownianRealization.aemeasurable : Measure C(ℝ≥0, ℝ)) = _
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_map hm measurable_brownianRealization]
  exact (isBrownianReal_brownianRealization.toIsPreBrownianReal.hasLaw I).map_eq

def brownianPathMeasure : ProbabilityMeasure C(ℝ≥0, ℝ) :=
  Classical.choose exists_brownianPathMeasure

theorem isBrownianReal_brownianPathMeasure :
    IsBrownianReal (fun t w => w t) (brownianPathMeasure : Measure C(ℝ≥0, ℝ)) :=
  Classical.choose_spec exists_brownianPathMeasure

theorem isPreBrownianReal_brownianPathMeasure :
    IsPreBrownianReal (fun t w => w t) (brownianPathMeasure : Measure C(ℝ≥0, ℝ)) :=
  isBrownianReal_brownianPathMeasure.toIsPreBrownianReal

end Problem336AdditiveD139.BrownianConstruction

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336AdditiveD139


local instance : MeasurableSpace PathRealization.Path := borel _
local instance : BorelSpace PathRealization.Path := ⟨rfl⟩

theorem group_innovation_map_eq
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool))
    (ν : ProbabilityMeasure PathRealization.Path)
    (hν : IsBrownianReal (fun t (w : PathRealization.Path) => w t)
      (ν : Measure PathRealization.Path)) :
    (ReferenceObservation.law μ ν).map
      (fun ω => GroupInnovation.transform μ (PathRealization.referencePaths ω)) =
        Measure.infinitePi (fun _ : Γ => (ν : Measure PathRealization.Path)) := by
  let B := fun (t : ℝ≥0) (w : PathRealization.Path) => w t
  have hBm : ∀ t, Measurable (B t) :=
    fun t => (continuous_eval_const t).measurable
  have hBj : Measurable (fun p : ℝ≥0 × PathRealization.Path => B p.1 p.2) :=
    (continuous_eval.comp (continuous_snd.prodMk continuous_fst)).measurable
  apply ReferenceInnovationLaw.map_field_innovation_eq μ ν B hν.toIsPreBrownianReal
    hBm hBj (fun w => w.continuous) (ν : Measure PathRealization.Path) hν
    (groupDrift μ) (measurable_groupDrift μ) (groupDrift_mem_Icc μ)
    (ReferenceObservation.groupDrift_condExp_history μ ν B hν.toIsPreBrownianReal hBm)
  intro ω i t
  rw [GroupInnovation.transform_apply_real_time]
  rfl

theorem group_factor_of_finite_response
    (hresponse : ∀ (F : Type u) [Fintype F] [Nonempty F]
      (ν : ProbabilityMeasure (F → Bool)), StronglyRayleighFinite ν →
      ∀ (i : F) (h h' : F → ℝ) (D : ℝ), 0 ≤ D →
        (∀ j, |h j - h' j| ≤ D) → |tiltMean ν h i - tiltMean ν h' i| ≤ D / 2)
    {Γ : Type u} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    (μ : ProbabilityMeasure (Γ → Bool))
    (hSR : StronglyRayleighCountable μ) (hInv : InvariantBinaryLaw μ) :
    HasEquivariantIIDFactor μ := by
  classical
  obtain ⟨ν, hν⟩ := BrownianConstruction.exists_brownianPathMeasure
  exact GroupSampler.factor_of_innovation_law hresponse μ hSR hInv ν
    hν.toIsPreBrownianReal (group_innovation_map_eq μ ν hν)

end Problem336AdditiveD139

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace Problem336AdditiveD139

theorem finite_strongly_rayleigh_response :
    ∀ (F : Type u_1) [Fintype F] [Nonempty F] (μ : ProbabilityMeasure (F → Bool)),
      StronglyRayleighFinite μ →
        (∀ (i j : F) (h : F → ℝ),
          HasDerivAt (fun r : ℝ => tiltMean μ (coordinatePerturb h j r) i)
            (tiltCovariance μ h i j) 0) ∧
        (∀ (i : F) (h : F → ℝ),
          (∑ j : F, |tiltCovariance μ h i j|) ≤
              2 * tiltMean μ h i * (1 - tiltMean μ h i) ∧
            2 * tiltMean μ h i * (1 - tiltMean μ h i) ≤ (1 : ℝ) / 2) ∧
        (∀ (i : F) (h h' : F → ℝ) (D : ℝ),
          0 ≤ D → (∀ j : F, |h j - h' j| ≤ D) →
            |tiltMean μ h i - tiltMean μ h' i| ≤ D / 2) := by
  intro F _ _ μ hμ
  exact finite_response_of_covariance_signs μ
    (fun i j h hij => hμ.tiltCovariance_nonpos h i j hij)
    (fun i h => hμ.tiltCovariance_row_nonneg h i)

theorem strongly_rayleigh_group_factor_oai :
    ∀ (Γ : Type u_2) [Group Γ] [Countable Γ] [MeasurableSpace Γ],
      ∀ μ : ProbabilityMeasure (Γ → Bool),
        StronglyRayleighCountable μ → InvariantBinaryLaw μ → HasEquivariantIIDFactor μ := by
  intro Γ _ _ _ μ hSR hInv
  exact group_factor_of_finite_response
    (fun F _ _ ν hν => (finite_strongly_rayleigh_response F ν hν).2.2)
    μ hSR hInv

theorem finite_positive_contraction_dpp_is_strongly_rayleigh :
    ∀ (F : Type u_3) [Fintype F] [Nonempty F] (K : F → F → ℂ),
      PositiveContractionFinite K →
        (∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K) ∧
          ∀ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K →
            StronglyRayleighFinite μ := by
  intro F _ _ K hK
  exact ⟨hK.exists_finiteDPP, fun μ hμ => hμ.stronglyRayleighFinite hK⟩

theorem countable_positive_contraction_dpp_exists_unique :
    ∀ (I : Type u_4) [Countable I] (K : I → I → ℂ),
      PositiveContractionKernel K →
        ∃! μ : ProbabilityMeasure (I → Bool), IsDeterminantalLaw μ K := by
  intro I _ K hK
  exact positiveContractionKernel_existsUnique_of_finite_exists
    (fun F _ _ K hK => hK.exists_finiteDPP) I K hK

theorem invariant_positive_contraction_dpp_factor :
    ∀ (Γ : Type u_5) [Group Γ] [Countable Γ] [MeasurableSpace Γ]
      (K : Γ → Γ → ℂ) (μ : ProbabilityMeasure (Γ → Bool)),
      PositiveContractionKernel K → IsDeterminantalLaw μ K →
        InvariantBinaryLaw μ → HasEquivariantIIDFactor μ := by
  intro Γ _ _ _ K μ hK hμ hinv
  apply strongly_rayleigh_group_factor_oai Γ μ ?_ hinv
  exact isDeterminantalLaw_stronglyRayleighCountable_of_finite K μ
    (fun F _ _ L hL ν hν => hν.stronglyRayleighFinite hL) hK hμ

theorem translation_invariant_kernel_dpp_factor :
    ∀ (Γ : Type u_6) [Group Γ] [Countable Γ] [MeasurableSpace Γ] (K : Γ → Γ → ℂ),
      PositiveContractionKernel K → TranslationInvariantKernel K →
        ∃ μ : ProbabilityMeasure (Γ → Bool),
          IsDeterminantalLaw μ K ∧ InvariantBinaryLaw μ ∧ HasEquivariantIIDFactor μ := by
  intro Γ _ _ _ K hK htranslation
  apply translationInvariantKernel_factor_of_exists K htranslation
    (countable_positive_contraction_dpp_exists_unique Γ K hK).exists
  intro μ hμ hinvariant
  exact invariant_positive_contraction_dpp_factor Γ K μ hK hμ hinvariant

end Problem336AdditiveD139

end

end OAI
end
end

theorem solution : type_of% @OAI.Problem336AdditiveD139.strongly_rayleigh_group_factor_oai := @OAI.Problem336AdditiveD139.strongly_rayleigh_group_factor_oai
