-- Prove2me | solution 1 for OAI.Erdos3.residue_source_stable_affine_comparison_at_degree_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:56:57.963087+00:00
-- url     : https://prove2.me/submissions/77014300-faa3-4d6a-9a4d-6bd0d30a2199

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B197
import Theorems.Thm_OAI_Erdos3_chosen_stable_residue_affine_total_at_degree_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductSectionSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem productCoordinateMix_empty (x y : ∀ i, X i) :
    productCoordinateMix ∅ x y = y := by
  funext i
  simp [productCoordinateMix]

variable [Fintype I] [∀ i, Fintype (X i)]

theorem productCoordinateMix_weight (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (x y : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix S x y) *
      (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix S y x) =
        (FiniteProbabilityWeights.pi μ).weight x * (FiniteProbabilityWeights.pi μ).weight y := by
  change (∏ i, (μ i).weight (productCoordinateMix S x y i)) *
      (∏ i, (μ i).weight (productCoordinateMix S y x i)) =
    (∏ i, (μ i).weight (x i)) * (∏ i, (μ i).weight (y i))
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem scalarResidue_card_mul_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r ≤ b - a + r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := Int.Ico_filter_modEq_card a b hr v
  have hcQ := congrArg (fun n : ℤ => (n : ℚ)) hc
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hcQ
  have hn : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) / r :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hrQ.le
  have hbound : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) ≤
      ((b - a : ℤ) : ℚ) / r + 1 := by
    rw [hcQ]
    apply max_le
    · have hx := Int.ceil_lt_add_one (((b : ℚ) - v) / r)
      have hy := Int.le_ceil (((a : ℚ) - v) / r)
      have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
        push_cast
        ring
      linarith
    · linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r + 1) * r = (b - a : ℤ) + (r : ℚ) := by
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_real_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) ≤
      ((b - a : ℤ) : ℝ) / r + 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_mul_le a b r v hab hr
  have hR : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r ≤
      ((b - a : ℤ) : ℝ) + r := by exact_mod_cast h
  have heq : ((b - a : ℤ) : ℝ) + r = (((b - a : ℤ) : ℝ) / r + 1) * r := by
    field_simp
  rw [heq] at hR
  exact (mul_le_mul_iff_left₀ hrR).mp hR

end Erdos3

end

section

namespace Erdos3

theorem scalarResidue_card_mul_ge (a b r v : ℤ) (hr : 0 < r) :
    b - a - r ≤ ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := congrArg (fun n : ℤ => (n : ℚ)) (Int.Ico_filter_modEq_card a b hr v)
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hc
  have hbound : ((b - a : ℤ) : ℚ) / r - 1 ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) := by
    rw [hc]
    apply le_trans _ (le_max_left _ _)
    have hx := Int.le_ceil (((b : ℚ) - v) / r)
    have hy := Int.ceil_lt_add_one (((a : ℚ) - v) / r)
    have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
      push_cast
      ring
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r - 1) * r = ((b - a - r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
      ((b - a : ℤ) : ℝ) / r| ≤ 1 := by
  have hu := scalarResidue_card_real_le a b r v hab hr
  have hl : ((b - a - r : ℤ) : ℝ) ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r := by
    exact_mod_cast scalarResidue_card_mul_ge a b r v hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heq : (((b - a : ℤ) : ℝ) / r - 1) * r = ((b - a - r : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [← heq] at hl
  have hlow := (mul_le_mul_iff_left₀ hrR).mp hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem scalarResidue_relative_count_error (a b r v : ℤ) (hab : a < b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r /
      ((b - a : ℤ) : ℝ) - 1| ≤ (r : ℝ) / ((b - a : ℤ) : ℝ) := by
  have hL : (0 : ℝ) < ((b - a : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr hab
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_absolute_error a b r v hab.le hr
  have heq : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r /
      ((b - a : ℤ) : ℝ) - 1 =
      (((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
        ((b - a : ℤ) : ℝ) / r) * ((r : ℝ) / ((b - a : ℤ) : ℝ)) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos (div_pos hrR hL)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h (div_nonneg hrR.le hL.le)

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_eq_card (a b r v : ℤ) (hr : 0 < r) :
    residueIndexLength a b r v =
      (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card := by
  rw [residueInterval_eq_map a b r v hr, Finset.card_map, Int.card_Ico]
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
namespace OAI

section

namespace Erdos3

theorem one_sub_sum_mul_prod_one_add_le_one {ι : Type*} (S : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ S, 0 ≤ e i) :
    (1 - ∑ i ∈ S, e i) * (∏ i ∈ S, (1 + e i)) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have heS : ∀ i ∈ S, 0 ≤ e i := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hea := he a (Finset.mem_insert_self _ _)
    have hs := Finset.sum_nonneg heS
    have hp : 0 ≤ ∏ i ∈ S, (1 + e i) := Finset.prod_nonneg (fun i hi => by linarith [heS i hi])
    have hstep : (1 - (e a + ∑ i ∈ S, e i)) * (1 + e a) ≤ 1 - ∑ i ∈ S, e i := by
      nlinarith [mul_nonneg hea hs, sq_nonneg (e a)]
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hstep hp).trans (ih heS)

theorem prod_one_add_le_one_add_twice_sum {ι : Type*} (S : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ S, 0 ≤ e i) (hsmall : (∑ i ∈ S, e i) ≤ 1 / 2) :
    (∏ i ∈ S, (1 + e i)) ≤ 1 + 2 * ∑ i ∈ S, e i := by
  have h := one_sub_sum_mul_prod_one_add_le_one S e he
  have hs := Finset.sum_nonneg he
  have hp : 0 ≤ ∏ i ∈ S, (1 + e i) := Finset.prod_nonneg (fun i hi => by linarith [he i hi])
  have hp2 : (∏ i ∈ S, (1 + e i)) ≤ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hp2 hs]

theorem positive_prod_sub_one_le_twice_sum {ι : Type*} (S : Finset ι) (f e : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (he : ∀ i ∈ S, 0 ≤ e i)
    (herror : ∀ i ∈ S, |f i - 1| ≤ e i) (hsmall : (∑ i ∈ S, e i) ≤ 1 / 2) :
    |(∏ i ∈ S, f i) - 1| ≤ 2 * ∑ i ∈ S, e i := by
  have hs := Finset.sum_nonneg he
  have he1 (i) (hi : i ∈ S) : e i ≤ 1 :=
    (Finset.single_le_sum he hi).trans (hsmall.trans (by norm_num))
  have hlo := one_sub_sum_le_positive_prod S f e hf (fun i hi => ⟨he i hi, he1 i hi⟩)
    (fun i hi => by have h := (abs_le.mp (herror i hi)).1; linarith)
  have hhi : (∏ i ∈ S, f i) ≤ 1 + 2 * ∑ i ∈ S, e i := by
    apply (Finset.prod_le_prod hf (fun index hindex => ?_)).trans
      (prod_one_add_le_one_add_twice_sum S e he hsmall)
    have hupper := (abs_le.mp (herror index hindex)).2
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoxResiduePartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem rectangularResidueCount_eq_card {I : Type*} [Fintype I] [DecidableEq I] (a b r v : I → ℤ) :
    rectangularResidueCount a b r v = Fintype.card
      (∀ i, ↥(Finset.filter (fun x => x ≡ v i [ZMOD r i]) (Finset.Ico (a i) (b i)))) := by
  classical
  rw [Fintype.card_pi]
  simp [rectangularResidueCount, integerResidueCount]

theorem rectangularResidueCount_relative_error {I : Type*} [Fintype I]
    (a b r v : I → ℤ) (hab : ∀ i, a i < b i) (hr : ∀ i, 0 < r i)
    (hsmall : (∑ i, (r i : ℝ) / ((b i - a i : ℤ) : ℝ)) ≤ 1 / 2) :
    |(∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) - integerRectangleVolume a b| ≤
      (2 * ∑ i, (r i : ℝ) / ((b i - a i : ℤ) : ℝ)) * integerRectangleVolume a b := by
  let L : I → ℝ := fun i => ((b i - a i : ℤ) : ℝ)
  let c : I → ℝ := fun i => integerResidueCount (a i) (b i) (r i) (v i)
  let f : I → ℝ := fun i => c i * r i / L i
  let e : I → ℝ := fun i => (r i : ℝ) / L i
  have hL (i) : 0 < L i := by
    dsimp only [L]
    exact_mod_cast sub_pos.mpr (hab i)
  have hrR (i) : (0 : ℝ) < r i := by exact_mod_cast hr i
  have hV : 0 < integerRectangleVolume a b := Finset.prod_pos (fun i _ => hL i)
  have hprod := positive_prod_sub_one_le_twice_sum Finset.univ f e
    (fun i _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hrR i).le) (hL i).le)
    (fun i _ => (div_pos (hrR i) (hL i)).le)
    (fun i _ => scalarResidue_relative_count_error (a i) (b i) (r i) (v i) (hab i) (hr i)) hsmall
  have heq : (∏ i, f i) * integerRectangleVolume a b =
      (∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) := by
    change (∏ i, f i) * (∏ i, L i) = _
    rw [← Finset.prod_mul_distrib]
    calc
      (∏ i, f i * L i) = ∏ i, c i * r i := by
        apply Finset.prod_congr rfl
        intro i _
        exact div_mul_cancel₀ (c i * r i) (hL i).ne'
      _ = (∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) := by
        simp only [Finset.prod_mul_distrib, rectangularResidueCount, Nat.cast_prod, c]
        ring
  calc
    _ = |((∏ i, f i) - 1) * integerRectangleVolume a b| := by
      rw [← heq]
      congr 1
      ring
    _ = |(∏ i, f i) - 1| * integerRectangleVolume a b := by rw [abs_mul, abs_of_pos hV]
    _ ≤ (2 * ∑ i, e i) * integerRectangleVolume a b := mul_le_mul_of_nonneg_right hprod hV.le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerResidueBox_lengths_pos {I : Type*} (a b r v : I → ℤ)
    (hr : ∀ i, 0 < r i) (hbox : Nonempty (IntegerResidueBox a b r v)) :
    ∀ i, 0 < residueIndexLength (a i) (b i) (r i) (v i) := by
  obtain ⟨x⟩ := hbox
  intro i
  rw [residueIndexLength_eq_card (a i) (b i) (r i) (v i) (hr i)]
  exact Finset.card_pos.mpr ⟨(x i).val, (x i).property⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_mul_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → ℝ) (c : ℝ) : p.mean (fun x => f x * c) = p.mean f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

end FiniteProbabilityWeights

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

theorem productMean_coordinateSwap (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (F : (∀ i, X i) → (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean
      (fun y => F (productCoordinateMix S x y) (productCoordinateMix S y x))) =
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean (F x)) := by
  let p := FiniteProbabilityWeights.pi μ
  have h : (∑ z : (∀ i, X i) × (∀ i, X i), p.weight z.1 * p.weight z.2 *
        F (productCoordinateMix S z.1 z.2) (productCoordinateMix S z.2 z.1)) =
      ∑ z : (∀ i, X i) × (∀ i, X i), p.weight z.1 * p.weight z.2 * F z.1 z.2 := by
    apply Fintype.sum_equiv (productCoordinateSwap (X := X) S)
    intro z
    change _ = p.weight (productCoordinateMix S z.1 z.2) *
      p.weight (productCoordinateMix S z.2 z.1) * _
    rw [productCoordinateMix_weight]
    rfl
  simpa only [FiniteProbabilityWeights.mean, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc] using h

theorem productMean_coordinateMix (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean
      (fun y => f (productCoordinateMix S x y))) = (FiniteProbabilityWeights.pi μ).mean f := by
  have h := productMean_coordinateSwap μ S (fun x _ => f x)
  simpa only [FiniteProbabilityWeights.mean_const] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_empty (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ ∅ f x = (FiniteProbabilityWeights.pi μ).mean f := by
  simp only [productConditionalMean, productCoordinateMix_empty]

theorem productConditionalMean_smul (S : Finset I) (c : ℝ) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => c * f y) x = c * productConditionalMean μ S f x :=
  (FiniteProbabilityWeights.pi μ).mean_const_mul _ _

theorem productConditionalMean_depends (S : Finset I) (f : (∀ i, X i) → ℝ) :
    ProductDependsOn S (productConditionalMean μ S f) := by
  intro x y hxy
  unfold productConditionalMean
  congr 1
  funext z
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [productCoordinateMix, hi, hxy i hi]
  · simp [productCoordinateMix, hi]

theorem productConditionalMean_of_depends (S : Finset I) {f : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn S f) (x : ∀ i, X i) : productConditionalMean μ S f x = f x := by
  have hpoint (y : ∀ i, X i) : f (productCoordinateMix S x y) = f x := by
    apply hf
    intro i hi
    simp [productCoordinateMix, hi]
  simp only [productConditionalMean, hpoint, FiniteProbabilityWeights.mean_const]

theorem productConditionalMean_selfadjoint (S : Finset I) (f g : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productConditionalMean μ S g x) =
      (FiniteProbabilityWeights.pi μ).mean (fun x => productConditionalMean μ S f x * g x) := by
  have h := productMean_coordinateSwap μ S
    (fun x y => f x * g (productCoordinateMix S x y))
  simp only [productCoordinateMix_swap] at h
  unfold productConditionalMean
  simp_rw [← FiniteProbabilityWeights.mean_const_mul, ← FiniteProbabilityWeights.mean_mul_const]
  exact h.symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem finiteWeightDensity_mul (p : FiniteProbabilityWeights Ω) (w : Ω → ℝ)
    (hsupport : ∀ x, p.weight x = 0 → w x = 0) (x : Ω) :
    p.weight x * finiteWeightDensity p w x = w x := by
  by_cases hx : p.weight x = 0
  · rw [hx, zero_mul, hsupport x hx]
  · unfold finiteWeightDensity
    field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem productFiberIndicator_depends {I : Type*} {X : I → Type*}
    (S : Finset I) (x : ∀ i, X i) : ProductDependsOn S (productFiberIndicator S x) := by
  intro y z hyz
  have he : (∀ i ∈ S, y i = x i) ↔ (∀ i ∈ S, z i = x i) :=
    ⟨fun h i hi => (hyz i hi).symm.trans (h i hi),
      fun h i hi => (hyz i hi).trans (h i hi)⟩
  simp only [productFiberIndicator, he]

theorem productFiberIndicator_self {I : Type*} {X : I → Type*}
    (S : Finset I) (x : ∀ i, X i) : productFiberIndicator S x x = 1 := by
  simp [productFiberIndicator]

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]

theorem weight_le_productFiberMass (w : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (S : Finset I) (x : ∀ i, X i) : w x ≤ productFiberMass w S x := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun y => w y * productFiberIndicator S x y)
    (fun y _ => mul_nonneg (hw y) (by unfold productFiberIndicator; split_ifs <;> norm_num))
    (Finset.mem_univ x)
  simpa only [productFiberMass, productFiberIndicator_self, mul_one] using h

theorem productFiberMass_pos (p : FiniteProbabilityWeights (∀ i, X i))
    (S : Finset I) (x : ∀ i, X i) (hx : 0 < p.weight x) : 0 < productFiberMass p.weight S x :=
  hx.trans_le (weight_le_productFiberMass p.weight p.nonneg S x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_fiber_identity (S : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi μ).weight S x * productConditionalMean μ S f x =
      productFiberMass (fun y => (FiniteProbabilityWeights.pi μ).weight y * f y) S x := by
  let p := FiniteProbabilityWeights.pi μ
  have he := productConditionalMean_selfadjoint μ S f (productFiberIndicator S x)
  simp_rw [productConditionalMean_of_depends μ S (productFiberIndicator_depends S x)] at he
  calc
    _ = p.mean (fun y => productConditionalMean μ S f y * productFiberIndicator S x y) := by
      unfold productFiberMass FiniteProbabilityWeights.mean
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      dsimp only
      by_cases hxy : ∀ i ∈ S, y i = x i
      · have hv := productConditionalMean_depends μ S f y x hxy
        rw [hv]
        dsimp [p]
        ring
      · simp only [productFiberIndicator, hxy, ite_false, mul_zero, zero_mul]
    _ = p.mean (fun y => f y * productFiberIndicator S x y) := he.symm
    _ = _ := by
      unfold productFiberMass FiniteProbabilityWeights.mean
      apply Finset.sum_congr rfl
      intro y _
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productFiberMass_fiberMean {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (f : Ω → ℝ)
    (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (fun y => p.fiberMean F y f) S x =
      p.mean (fun z => f z * productFiberIndicator S x (F z)) := by
  classical
  simp only [productFiberMass, FiniteProbabilityWeights.fiberMean, FiniteProbabilityWeights.mean,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [mul_ite, ite_mul, eq_comm, mul_assoc]

theorem observedProductDensity_fiber_identity {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (hμ : ∀ i x, 0 < (μ i).weight x) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (f : Ω → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi μ).weight S x *
        productConditionalMean μ S (observedProductDensity μ p F f) x =
      p.mean (fun z => f z * productFiberIndicator S x (F z)) := by
  have hpos : ∀ y, 0 < (FiniteProbabilityWeights.pi μ).weight y :=
    fun y => Finset.prod_pos (fun i _ => hμ i (y i))
  rw [productConditionalMean_fiber_identity]
  have heq : (fun y => (FiniteProbabilityWeights.pi μ).weight y * observedProductDensity μ p F f y) =
      (fun y => p.fiberMean F y f) := by
    funext y
    exact finiteWeightDensity_mul _ _ (fun z hz => False.elim ((hpos z).ne' hz)) y
  rw [heq]
  exact productFiberMass_fiberMean p F f S x

theorem observedProductDensity_conditional {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (hμ : ∀ i x, 0 < (μ i).weight x) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (f : Ω → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    productConditionalMean μ S (observedProductDensity μ p F f) x =
      p.mean (fun z => f z * productFiberIndicator S x (F z)) /
        productFiberMass (FiniteProbabilityWeights.pi μ).weight S x := by
  have hp : 0 < (FiniteProbabilityWeights.pi μ).weight x :=
    Finset.prod_pos (fun i _ => hμ i (x i))
  apply (eq_div_iff (productFiberMass_pos _ S x hp).ne').mpr
  simpa only [mul_comm] using observedProductDensity_fiber_identity μ hμ p F f S x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductCellMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem uniform_subtype_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] (f : Ω → ℝ) :
    (FiniteProbabilityWeights.uniform Ω).mean (fun z => if P z then f z else 0) =
      (Fintype.card {z // P z} : ℝ) / Fintype.card Ω * (𝔼 z : {z // P z}, f z.val) := by
  classical
  rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
  have hsum : (∑ z, if P z then f z else 0) = ∑ z : {z // P z}, f z.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) f
  rw [hsum, ← Fintype.card_mul_expect (fun z : {z // P z} => f z.val)]
  ring

theorem uniform_observedProductDensity_conditional {Ω ι : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i))
    (hμ : ∀ i x, 0 < (μ i).weight x) (F : Ω → ∀ i, X i) (f : Ω → ℝ)
    (S : Finset ι) (x : ∀ i, X i) :
    productConditionalMean μ S (observedProductDensity μ (FiniteProbabilityWeights.uniform Ω) F f) x =
      ((Fintype.card {z // ∀ i ∈ S, F z i = x i} : ℝ) / Fintype.card Ω /
        productFiberMass (FiniteProbabilityWeights.pi μ).weight S x) *
      (𝔼 z : {z // ∀ i ∈ S, F z i = x i}, f z.val) := by
  classical
  rw [observedProductDensity_conditional μ hμ]
  have hf : (fun z => f z * productFiberIndicator S x (F z)) =
      (fun z => if ∀ i ∈ S, F z i = x i then f z else 0) := by
    funext z
    unfold productFiberIndicator
    split_ifs <;> simp
  rw [hf, uniform_subtype_mean]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}

theorem productCoordinateMix_section (T A B : Finset I) (hAT : A ⊆ T)
    (z x y v : ∀ i, X i) :
    productCoordinateMix T (productCoordinateMix A z v) (productCoordinateMix B x y) =
      productCoordinateMix (A ∪ (B \ T)) (productCoordinateMix T z x)
        (productCoordinateMix Tᶜ y v) := by
  funext i
  by_cases hiT : i ∈ T
  · by_cases hiA : i ∈ A <;> simp [productCoordinateMix, hiT, hiA]
  · have hiA : i ∉ A := fun h => hiT (hAT h)
    by_cases hiB : i ∈ B <;> simp [productCoordinateMix, hiT, hiA, hiB]

end Erdos3

end

section

namespace Erdos3

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

variable [Fintype ι] [∀ i, Fintype (X i)]

theorem mem_bounded (b : ℕ) (c : ProductCylinder X) :
    c ∈ bounded (X := X) b ↔ c.1.card ≤ b := by
  classical
  simp only [bounded, Finset.mem_filter, Finset.mem_univ, true_and]

theorem bounded_nonempty (b : ℕ) (base : ∀ i, X i) :
    (bounded (X := X) b).Nonempty := by
  exact ⟨ofAssignment ∅ base, (mem_bounded b _).mpr (by simp [ofAssignment])⟩

theorem mass_ofAssignment (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    (ofAssignment S x).mass μ base f = productConditionalMean μ S f x := by
  apply productConditionalMean_depends
  intro i hi
  change i ∈ S at hi
  change (if h : i ∈ S then x i else base i) = x i
  exact dif_pos hi

theorem mass_empty (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) :
    (ofAssignment ∅ base).mass μ base f = (FiniteProbabilityWeights.pi μ).mean f := by
  rw [mass_ofAssignment, productConditionalMean_empty]

theorem mass_mono (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    {f g : (∀ i, X i) → ℝ} (hfg : ∀ x, f x ≤ g x) (c : ProductCylinder X) :
    c.mass μ base f ≤ c.mass μ base g :=
  (FiniteProbabilityWeights.pi μ).mean_mono (fun _ => hfg _)

end ProductCylinder

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_sectionAverage (T A B : Finset I) (hAT : A ⊆ T)
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ B (productSectionAverage μ T A z f) x =
      productConditionalMean μ (A ∪ (B \ T)) f (productCoordinateMix T z x) := by
  change (FiniteProbabilityWeights.pi μ).mean (fun y => (FiniteProbabilityWeights.pi μ).mean
    (fun v => f (productCoordinateMix T (productCoordinateMix A z v) (productCoordinateMix B x y)))) = _
  simp_rw [productCoordinateMix_section T A B hAT]
  exact productMean_coordinateMix μ Tᶜ
    (fun v => f (productCoordinateMix (A ∪ (B \ T)) (productCoordinateMix T z x) v))

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

theorem exists_maximizer (K : ℝ) (b : ℕ) : ∃ c : ProductCylinder X, Maximizes μ base f K b c := by
  classical
  obtain ⟨c, hc, hm⟩ := Finset.exists_max_image (bounded (X := X) b) (score μ base f K)
    (bounded_nonempty b base)
  exact ⟨c, (mem_bounded b c).mp hc, fun d hd => hm d ((mem_bounded b d).mpr hd)⟩

variable {μ base f}

theorem Maximizes.empty_le {K : ℝ} {b : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K b c) :
    (FiniteProbabilityWeights.pi μ).mean f ≤ c.mass μ base f / K ^ c.1.card := by
  have h := hmax.2 (ofAssignment ∅ base) (by simp [ofAssignment])
  change (ofAssignment ∅ base).mass μ base f / K ^ 0 ≤ c.mass μ base f / K ^ c.1.card at h
  rw [mass_empty, pow_zero, div_one] at h
  exact h

theorem Maximizes.mass_gt {K τ : ℝ} {b : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K b c) (hK : 1 ≤ K) (hτ : 0 ≤ τ)
    (hm : τ < (FiniteProbabilityWeights.pi μ).mean f) : τ < c.mass μ base f := by
  have hpos : 0 < K ^ c.1.card := pow_pos (zero_lt_one.trans_le hK) _
  have h := (lt_div_iff₀ hpos).mp (hm.trans_le hmax.empty_le)
  exact (le_mul_of_one_le_right hτ (one_le_pow₀ hK)).trans_lt h

theorem Maximizes.card_le {K τ : ℝ} {j r : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K (j + r) c) (hK : 1 ≤ K) (hτ : 0 ≤ τ)
    (hm : τ < (FiniteProbabilityWeights.pi μ).mean f)
    (hcap : ∀ d : ProductCylinder X, d.1.card ≤ j + r → d.mass μ base f ≤ 2)
    (hcut : 2 ≤ τ * K ^ (j + 1)) : c.1.card ≤ j := by
  by_contra hn
  have hle : j + 1 ≤ c.1.card := by omega
  have hpos : 0 < K ^ c.1.card := pow_pos (zero_lt_one.trans_le hK) _
  have h := (lt_div_iff₀ hpos).mp (hm.trans_le hmax.empty_le)
  have hmono := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hle) hτ
  have hcap' := hcap c hmax.1
  linarith

theorem Maximizes.refinement_bound {K : ℝ} {j r : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K (j + r) c) (hK : 0 < K) (hc : c.1.card ≤ j)
    (J : Finset ι) (hdis : Disjoint c.1 J) (hJ : J.card ≤ r) (y : ∀ i, X i) :
    productConditionalMean μ (c.1 ∪ J) f y ≤ K ^ J.card * c.mass μ base f := by
  have hcard : (c.1 ∪ J).card ≤ j + r := by
    rw [Finset.card_union_of_disjoint hdis]
    omega
  have hs := hmax.2 (ofAssignment (c.1 ∪ J) y) hcard
  change (ofAssignment (c.1 ∪ J) y).mass μ base f / K ^ (c.1 ∪ J).card ≤
    c.mass μ base f / K ^ c.1.card at hs
  rw [mass_ofAssignment] at hs
  have hcross := (div_le_div_iff₀ (pow_pos hK (c.1 ∪ J).card) (pow_pos hK c.1.card)).mp hs
  apply (mul_le_mul_iff_left₀ (pow_pos hK c.1.card)).mp
  calc
    _ ≤ c.mass μ base f * K ^ (c.1 ∪ J).card := hcross
    _ = (K ^ J.card * c.mass μ base f) * K ^ c.1.card := by
      rw [Finset.card_union_of_disjoint hdis, pow_add]
      ring

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

variable {μ base f}

theorem Maximizes.normalized_bounded {K : ℝ} {j r : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K (j + r) c) (hK : 1 ≤ K) (hc : c.1.card ≤ j)
    (hm : 0 < c.mass μ base f) :
    ProductBoundedMarginals μ (normalizedSection μ base f c) K r := by
  intro B hB x _
  change productConditionalMean μ B
    (fun y => (c.mass μ base f)⁻¹ * productSectionAverage μ c.1 c.1 (c.assignment base) f y) x ≤ _
  rw [productConditionalMean_smul, productConditionalMean_sectionAverage μ c.1 c.1 B (by rfl)]
  have hdis : Disjoint c.1 (B \ c.1) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hj).2 hi
  have hcard : (B \ c.1).card ≤ r := (Finset.card_le_card Finset.sdiff_subset).trans hB
  have hb := hmax.refinement_bound (zero_lt_one.trans_le hK) hc (B \ c.1) hdis hcard
    (productCoordinateMix c.1 (c.assignment base) x)
  calc
    _ ≤ (c.mass μ base f)⁻¹ * (K ^ (B \ c.1).card * c.mass μ base f) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hm.le)
    _ = K ^ (B \ c.1).card := by field_simp
    _ ≤ K ^ B.card := pow_le_pow_right₀ hK (Finset.card_le_card Finset.sdiff_subset)

theorem exists_regular {K τ : ℝ} {j r : ℕ} (hK : 1 ≤ K) (hτ : 0 ≤ τ)
    (hm : τ < (FiniteProbabilityWeights.pi μ).mean f)
    (hcap : ∀ d : ProductCylinder X, d.1.card ≤ j + r → d.mass μ base f ≤ 2)
    (hcut : 2 ≤ τ * K ^ (j + 1)) :
    ∃ c : ProductCylinder X, c.1.card ≤ j ∧ τ < c.mass μ base f ∧
      ProductBoundedMarginals μ (normalizedSection μ base f c) K r := by
  obtain ⟨c, hc⟩ := exists_maximizer μ base f K (j + r)
  have hcard := hc.card_le hK hτ hm hcap hcut
  have hmass := hc.mass_gt hK hτ hm
  exact ⟨c, hcard, hmass, hc.normalized_bounded hK hcard (hτ.trans_lt hmass)⟩

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem ProductMarginalsClose.mono {rho : (∀ i, X i) → ℝ} {eta : ℝ} {s t : ℕ}
    (h : ProductMarginalsClose μ rho eta s) (ht : t ≤ s) : ProductMarginalsClose μ rho eta t :=
  fun B hB x hx => h B (hB.trans ht) x hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductReferenceFiber
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem productFiberMass_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi μ).weight S x = ∏ i ∈ S, (μ i).weight (x i) := by
  classical
  have hind : ∀ y : ∀ i, X i, productFiberIndicator S x y =
      ∏ i, (if i ∈ S then if y i = x i then (1 : ℝ) else 0 else 1) := by
    intro y
    unfold productFiberIndicator
    split_ifs with h
    · symm
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i ∈ S
      · simp only [hi, h i hi, ite_true]
      · simp only [hi, ite_false]
    · push Not at h
      obtain ⟨i, hi, heq⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, heq, ite_true, ite_false]
  simp only [productFiberMass, hind, FiniteProbabilityWeights.pi, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (y : X i) => (μ i).weight y *
    (if i ∈ S then if y = x i then (1 : ℝ) else 0 else 1))]
  have hsum : ∀ i, (∑ y : X i, (μ i).weight y * (if i ∈ S then if y = x i then 1 else 0 else 1)) =
      if i ∈ S then (μ i).weight (x i) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simpa only [hi, ite_false, mul_one] using (μ i).total
  simp only [hsum]
  rw [Finset.prod_ite]
  simp

theorem productFiberMass_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (X i))).weight S x =
      ∏ i ∈ S, (Fintype.card (X i) : ℝ)⁻¹ := by
  rw [productFiberMass_pi]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedDensityTesting
namespace OAI

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_mono {f g : Ω → ℝ} (hfg : ∀ z, f z ≤ g z) (x : ∀ i, X i) :
    observedProductDensity μ p F f x ≤ observedProductDensity μ p F g x := by
  classical
  apply div_le_div_of_nonneg_right _ ((FiniteProbabilityWeights.pi μ).nonneg x)
  apply p.mean_mono
  intro z
  split_ifs
  · exact hfg z
  · exact le_rfl

theorem observedProductDensity_add (f g : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (fun z => f z + g z) x =
      observedProductDensity μ p F f x + observedProductDensity μ p F g x := by
  classical
  have he : p.fiberMean F x (fun z => f z + g z) = p.fiberMean F x f + p.fiberMean F x g := by
    unfold FiniteProbabilityWeights.fiberMean
    rw [← p.mean_add]
    congr 1
    funext z
    split_ifs <;> simp
  change p.fiberMean F x (fun z => f z + g z) / _ = p.fiberMean F x f / _ + p.fiberMean F x g / _
  rw [he, add_div]

theorem observedProductDensity_mean (hμ : ∀ i x, 0 < (μ i).weight x)
    (f : Ω → ℝ) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).mean (observedProductDensity μ p F f) = p.mean f := by
  have h := observedProductDensity_conditional μ hμ p F f ∅ base
  rw [productConditionalMean_empty, productFiberMass_empty, (FiniteProbabilityWeights.pi μ).total,
    div_one] at h
  simpa [productFiberIndicator] using h

theorem observedProductDensity_marginal_le (hμ : ∀ i x, 0 < (μ i).weight x)
    (f : Ω → ℝ) (hf : ∀ z, f z ≤ 1) {η : ℝ} {r : ℕ}
    (hbase : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η r)
    (S : Finset ι) (hS : S.card ≤ r) (x : ∀ i, X i) :
    productConditionalMean μ S (observedProductDensity μ p F f) x ≤ 1 + η := by
  have hm : productConditionalMean μ S (observedProductDensity μ p F f) x ≤
      productConditionalMean μ S (observedProductDensity μ p F (fun _ => 1)) x :=
    (FiniteProbabilityWeights.pi μ).mean_mono
      (fun y => observedProductDensity_mono μ p F hf (productCoordinateMix S x y))
  have hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0 :=
    (Finset.prod_pos (fun i _ => hμ i (x i))).ne'
  have hb := (abs_le.mp (hbase S hS x hx)).2
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition
namespace OAI

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} {X : ι → Type*}

theorem cut_add_erase (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (z : Ω) :
    c.cut F w z + c.erase F w z = w z := by
  unfold cut erase
  split_ifs <;> simp

theorem erase_nonneg (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : 0 ≤ c.erase F w z := by
  unfold erase
  split_ifs <;> simp [hw]

theorem erase_le (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : c.erase F w z ≤ w z := by
  unfold erase
  split_ifs <;> simp [hw]

variable [Fintype Ω] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

theorem density_cut (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (c.cut F w) x =
      if c.Contains x then observedProductDensity μ p F w x else 0 := by
  classical
  by_cases hx : c.Contains x
  · rw [if_pos hx]
    change p.fiberMean F x (c.cut F w) / _ = p.fiberMean F x w / _
    congr 1
    unfold FiniteProbabilityWeights.fiberMean
    congr 1
    funext z
    by_cases hz : F z = x
    · simp [cut, hz, hx]
    · simp [hz]
  · rw [if_neg hx]
    have he : p.fiberMean F x (c.cut F w) = 0 := by
      calc
        _ = p.mean (fun _ => 0) := by
          unfold FiniteProbabilityWeights.fiberMean
          congr 1
          funext z
          by_cases hz : F z = x
          · simp [cut, hz, hx]
          · simp [hz]
        _ = 0 := p.mean_const 0
    change p.fiberMean F x (c.cut F w) / _ = 0
    rw [he, zero_div]

theorem density_erase (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (c.erase F w) x =
      if c.Contains x then 0 else observedProductDensity μ p F w x := by
  classical
  have he : (fun z => c.cut F w z + c.erase F w z) = w := funext (c.cut_add_erase F w)
  have hs := observedProductDensity_add μ p F (c.cut F w) (c.erase F w) x
  rw [he, c.density_cut] at hs
  by_cases hx : c.Contains x
  · rw [if_pos hx] at hs ⊢
    linarith
  · rw [if_neg hx] at hs ⊢
    linarith

theorem mass_erase_self (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) :
    c.mass μ base (observedProductDensity μ p F (c.erase F w)) = 0 := by
  have hc (y : ∀ i, X i) : c.Contains (productCoordinateMix c.1 (c.assignment base) y) := by
    intro i
    simpa only [productCoordinateMix, i.property, ite_true] using c.assignment_mem base i.val i.property
  change (FiniteProbabilityWeights.pi μ).mean
    (fun y => observedProductDensity μ p F (c.erase F w) (productCoordinateMix c.1 (c.assignment base) y)) = 0
  have he : (fun y => observedProductDensity μ p F (c.erase F w)
      (productCoordinateMix c.1 (c.assignment base) y)) = (fun _ => 0) := by
    funext y
    rw [c.density_erase, if_pos (hc y)]
  rw [he, FiniteProbabilityWeights.mean_const]

omit [∀ i, DecidableEq (X i)] in
theorem mass_erase_le (c d : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) :
    d.mass μ base (observedProductDensity μ p F (c.erase F w)) ≤
      d.mass μ base (observedProductDensity μ p F w) :=
  mass_mono μ base (observedProductDensity_mono μ p F (c.erase_le F w hw)) d

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

theorem mem_positiveCandidates (b : ℕ) (w : Ω → ℝ) (c : ProductCylinder X) :
    c ∈ positiveCandidates μ base p F b w ↔
      c.1.card ≤ b ∧ 0 < c.mass μ base (observedProductDensity μ p F w) := by
  classical
  simp only [positiveCandidates, Finset.mem_filter, mem_bounded]

theorem positiveCandidates_card_le (b : ℕ) (w : Ω → ℝ) :
    (positiveCandidates μ base p F b w).card ≤ (bounded (X := X) b).card := by
  classical
  exact Finset.card_filter_le _ _

theorem positiveCandidates_erase_card_lt [∀ i, DecidableEq (X i)] (b : ℕ) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (c : ProductCylinder X) (hc : c.1.card ≤ b)
    (hm : 0 < c.mass μ base (observedProductDensity μ p F w)) :
    (positiveCandidates μ base p F b (c.erase F w)).card <
      (positiveCandidates μ base p F b w).card := by
  classical
  have hsub : positiveCandidates μ base p F b (c.erase F w) ⊆
      (positiveCandidates μ base p F b w).erase c := by
    intro d hd
    obtain ⟨hdsize, hdmass⟩ := (mem_positiveCandidates μ base p F b (c.erase F w) d).mp hd
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      subst d
      rw [c.mass_erase_self] at hdmass
      exact (lt_irrefl 0) hdmass
    · exact (mem_positiveCandidates μ base p F b w d).mpr
        ⟨hdsize, hdmass.trans_le (c.mass_erase_le d μ base p F w hw)⟩
  have hcpos := (mem_positiveCandidates μ base p F b w c).mpr ⟨hc, hm⟩
  exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem hcpos)

end Erdos3.ProductCylinder

end

section

namespace Erdos3

open ProductCylinder

theorem exists_finite_cylinder_removal {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (K τ η : ℝ) (j r : ℕ) (hK : 1 ≤ K) (hτ : 0 ≤ τ) (hη : η ≤ 1)
    (hcut : 2 ≤ τ * K ^ (j + 1))
    (hbase : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (j + r))
    (w : Ω → ℝ) (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1) :
    ∃ (v : Ω → ℝ) (cs : List (ProductCylinder X)),
      CylinderRemovalChain μ base p F K τ j r w v cs ∧
      cs.length ≤ (ProductCylinder.bounded (X := X) (j + r)).card ∧ p.mean v ≤ τ ∧
      (∀ z, 0 ≤ v z ∧ v z ≤ 1) := by
  have aux : ∀ n : ℕ, ∀ w : Ω → ℝ, (∀ z, 0 ≤ w z) → (∀ z, w z ≤ 1) →
      (positiveCandidates μ base p F (j + r) w).card ≤ n →
      ∃ (v : Ω → ℝ) (cs : List (ProductCylinder X)),
        CylinderRemovalChain μ base p F K τ j r w v cs ∧ cs.length ≤ n ∧ p.mean v ≤ τ ∧
        (∀ z, 0 ≤ v z ∧ v z ≤ 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw0 hw1 hn
      by_cases hs : p.mean w ≤ τ
      · exact ⟨w, [], .nil w, by simp, hs, fun z => ⟨hw0 z, hw1 z⟩⟩
      · have hm : τ < (FiniteProbabilityWeights.pi μ).mean (observedProductDensity μ p F w) := by
          rw [observedProductDensity_mean μ p F hμ w base]
          exact lt_of_not_ge hs
        have hcap : ∀ d : ProductCylinder X, d.1.card ≤ j + r →
            d.mass μ base (observedProductDensity μ p F w) ≤ 2 := by
          intro d hd
          have hb := observedProductDensity_marginal_le μ p F hμ w hw1 hbase d.1 hd (d.assignment base)
          change productConditionalMean μ d.1 (observedProductDensity μ p F w) (d.assignment base) ≤ 2
          linarith
        obtain ⟨c, hc, hmass, hregular⟩ := ProductCylinder.exists_regular hK hτ hm hcap hcut
        have hpos : 0 < c.mass μ base (observedProductDensity μ p F w) := hτ.trans_lt hmass
        have hsize : c.1.card ≤ j + r := by omega
        have hlt := positiveCandidates_erase_card_lt μ base p F (j + r) w hw0 c hsize hpos
        have hnext : (positiveCandidates μ base p F (j + r) (c.erase F w)).card < n := hlt.trans_le hn
        obtain ⟨v, cs, hchain, hcs, hv, hvbounds⟩ := ih _ hnext (c.erase F w)
          (c.erase_nonneg F w hw0) (fun z => (c.erase_le F w hw0 z).trans (hw1 z)) le_rfl
        refine ⟨v, c :: cs, .cons c hc hmass hregular hchain, ?_, hv, hvbounds⟩
        simp only [List.length_cons]
        omega
  exact aux _ w hw0 hw1 (positiveCandidates_card_le μ base p F (j + r) w)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedSourceAccuracy
namespace OAI

section

namespace Erdos3

theorem exp_neg_le_exp_neg_div_eight {A B : ℝ} (hAB : B + 4 ≤ A) :
    Real.exp (-A) ≤ Real.exp (-B) / 8 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 4 := by
    calc
      8 ≤ (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ Real.exp (-(B + 4)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-B) / Real.exp 4 := by simp only [neg_add, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h8

theorem exp_neg_le_half_exp_neg {A B : ℝ} (hAB : B + 1 ≤ A) :
    Real.exp (-A) ≤ (1 / 2) * Real.exp (-B) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp (-(B + 1)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-B) / Real.exp 1 := by simp only [neg_add, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (-B) / 2 := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h2
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineDegreeChoice
namespace OAI

section

namespace Erdos3

theorem affineRemovalDepth_cutoff (T : ℝ) :
    2 ≤ Real.exp (-T) * (2 : ℝ) ^ (affineRemovalDepth T + 1) := by
  have h := CyclicCrootSisask.half_pow_spectralIterations_mul_exp_le (p := T) (by norm_num : (0 : ℝ) < 1)
  have hp : 0 < (2 : ℝ) ^ affineRemovalDepth T := by positivity
  have hm := mul_le_mul_of_nonneg_right h hp.le
  have he : ((1 / 2 : ℝ) ^ CyclicCrootSisask.spectralIterations 1 T * Real.exp T) *
      (2 : ℝ) ^ affineRemovalDepth T = Real.exp T := by
    unfold affineRemovalDepth
    rw [div_pow, one_pow]
    field_simp
  rw [he] at hm
  have hh := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-T)).le
  have hc : Real.exp (-T) * Real.exp T = 1 := by rw [← Real.exp_add]; simp
  rw [hc] at hh
  rw [pow_succ]
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffinePrimitiveLogBudget
namespace OAI

section

namespace Erdos3

theorem affineComparisonScale_bounds {ε L T C : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) :
    0 ≤ affineComparisonScale ε L T C ∧
    L + T + 2 ≤ affineComparisonScale ε L T C ∧
    ((affineRemovalDepth T + affineComparisonTail ε L T : ℕ) : ℝ) ≤ affineComparisonScale ε L T C ∧
    C ≤ affineComparisonScale ε L T C := by
  have hn : (0 : ℝ) ≤ (affineRemovalDepth T + affineComparisonTail ε L T : ℕ) := Nat.cast_nonneg _
  unfold affineComparisonScale
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateReference_weight_pos {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (i : ι) (x : σ → ZMod (q i)) :
    0 < (primeCoordinateReference (σ := σ) q i).weight x := by
  dsimp only [primeCoordinateReference, FiniteProbabilityWeights.uniform]
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResiduePrimeDensityError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_prime_coordinate_integer_anchor {ι σ : Type*} [DecidableEq ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    ∃ u : σ → ℤ, ∀ i ∈ I, (fun j => (u j : ZMod (q i))) = x i := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨v, hv⟩ := ih
    have hc : (q i).Coprime (∏ k ∈ I, q k) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro k hk
      apply hcop
      intro heq
      exact hi (heq ▸ hk)
    have hu : ∀ j : σ, ∃ u : ℤ,
        u ≡ ((x i j).val : ℤ) [ZMOD (q i : ℤ)] ∧ u ≡ v j [ZMOD ((∏ k ∈ I, q k : ℕ) : ℤ)] := by
      intro j
      exact exists_integer_coprime_residues hc (x i j).val (v j)
    choose u hu using hu
    refine ⟨u, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with hki | hk
    · subst k
      funext j
      have h := (ZMod.intCast_eq_intCast_iff (u j) ((x i j).val : ℤ) (q i)).mpr (hu j).1
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h
    · funext j
      have hd : (q k : ℤ) ∣ ((∏ l ∈ I, q l : ℕ) : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem q hk
      have h := (ZMod.intCast_eq_intCast_iff (u j) (v j) (q k)).mpr ((hu j).2.of_dvd hd)
      exact h.trans (congrFun (hv k hk) j)

theorem primeCoordinateCell_eq_integer_anchor {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι)
    (x : ∀ i, σ → ZMod (q i)) (u : σ → ℤ)
    (hu : ∀ i ∈ I, (fun j => (u j : ZMod (q i))) = x i) :
    primeCoordinateCell lo N q I x =
      primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))) := by
  ext z
  simp only [mem_primeCoordinateCell]
  constructor
  · rintro ⟨hz, hx⟩
    exact ⟨hz, fun i hi => (hx i hi).trans (hu i hi).symm⟩
  · rintro ⟨hz, hx⟩
    exact ⟨hz, fun i hi => (hx i hi).trans (hu i hi)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateReference_fiber {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productFiberMass (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight I x =
      (((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ)⁻¹ := by
  change productFiberMass (FiniteProbabilityWeights.pi
    (fun i => FiniteProbabilityWeights.uniform (σ → ZMod (q i)))).weight I x = _
  rw [productFiberMass_uniform]
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow, Nat.cast_prod,
    Finset.prod_inv_distrib, Finset.prod_pow]

theorem primeCoordinateMassRatio_eq_count {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    primeCoordinateMassRatio lo N q I x =
      ((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ *
        (primeCoordinateCell lo N q I x).card / (translatedIntegerBox lo N).card := by
  rw [primeCoordinateMassRatio, primeCoordinateReference_fiber, div_inv_eq_mul]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateCell_card_residue {ι σ : Type*} [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι)
    (x : ∀ i, σ → ZMod (q i)) (u : σ → ℤ)
    (hu : ∀ i ∈ I, (fun j => (u j : ZMod (q i))) = x i) :
    (primeCoordinateCell lo N q I x).card =
      rectangularResidueCount lo (fun j => lo j + N j) (fun _ => ((∏ i ∈ I, q i : ℕ) : ℤ)) u := by
  rw [primeCoordinateCell_eq_integer_anchor lo N q I x u hu]
  have hc := Fintype.card_congr (primeCoordinateCellEquiv lo N q hcop I u)
  rw [Fintype.card_coe] at hc
  exact hc.trans (rectangularResidueCount_eq_card _ _ _ _).symm

theorem primeCoordinateMassRatio_close {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (hN : ∀ j, 0 < N j)
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι)
    (x : ∀ i, σ → ZMod (q i))
    (hsmall : (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) / N j) ≤ 1 / 2) :
    |primeCoordinateMassRatio lo N q I x - 1| ≤
      2 * ∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) / N j := by
  obtain ⟨u, hu⟩ := exists_prime_coordinate_integer_anchor q hcop I x
  have hM : 0 < ∏ i ∈ I, q i := Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))
  have herr := rectangularResidueCount_relative_error lo (fun j => lo j + N j)
    (fun _ => ((∏ i ∈ I, q i : ℕ) : ℤ)) u
    (fun j => by have hj := hN j; omega) (fun _ => Nat.cast_pos.mpr hM)
    (by simpa only [add_sub_cancel_left, Int.cast_natCast] using hsmall)
  have hcell := primeCoordinateCell_card_residue lo N q hcop I x u hu
  have hvolume : integerRectangleVolume lo (fun j => lo j + N j) =
      ((translatedIntegerBox lo N).card : ℝ) := by
    simp only [integerRectangleVolume, add_sub_cancel_left, Int.cast_natCast,
      translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod]
  rw [hvolume, ← hcell] at herr
  simp only [Finset.prod_const, Finset.card_univ, add_sub_cancel_left, Int.cast_natCast] at herr
  have hV : (0 : ℝ) < (translatedIntegerBox lo N).card := by
    simp only [translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod]
    exact Finset.prod_pos (fun j _ => Nat.cast_pos.mpr (hN j))
  rw [primeCoordinateMassRatio_eq_count]
  calc
    _ = |((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ * (primeCoordinateCell lo N q I x).card -
        (translatedIntegerBox lo N).card| / (translatedIntegerBox lo N).card := by
      rw [← abs_of_pos hV, ← abs_div]
      congr 1
      rw [abs_of_pos hV]
      field_simp
    _ ≤ _ := (div_le_iff₀ hV).mpr herr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateDensity_conditional {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f : (σ → ℤ) → ℝ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productConditionalMean (primeCoordinateReference (σ := σ) q) I
      (residuePrimeCoordinateDensity lo N M a hne q f) x =
      residuePrimeCoordinateMassRatio lo N M a q I x *
        (𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val)) := by
  let := hne
  exact uniform_observedProductDensity_conditional
    (Ω := IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a)
    (primeCoordinateReference (σ := σ) q)
    (primeCoordinateReference_weight_pos q)
    (fun z => primeCoordinateObservation q (fun j => (z j).val)) (fun z => f (fun j => (z j).val)) I x

theorem residuePrimeCoordinateMassRatio_eq_count {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMassRatio lo N M a q I x =
      ((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ *
        Fintype.card (ResiduePrimeCoordinateCell lo N M a q I x) /
        Fintype.card (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a) := by
  rw [residuePrimeCoordinateMassRatio, primeCoordinateReference_fiber, div_inv_eq_mul]
  ring

theorem residuePrimeCoordinateDensity_conditional_one {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productConditionalMean (primeCoordinateReference (σ := σ) q) I
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) x =
      residuePrimeCoordinateMassRatio lo N M a q I x := by
  classical
  rw [residuePrimeCoordinateDensity_conditional]
  by_cases hc : Nonempty (ResiduePrimeCoordinateCell lo N M a q I x)
  · let := hc
    rw [Fintype.expect_const, mul_one]
  · have hempty : IsEmpty (ResiduePrimeCoordinateCell lo N M a q I x) := not_nonempty_iff.mp hc
    let := hempty
    simp only [residuePrimeCoordinateMassRatio, Fintype.card_of_isEmpty, Nat.cast_zero,
      zero_div, zero_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMassRatio_affine {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMassRatio lo N M a q I
      (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (x i)) =
    primeCoordinateMassRatio (fun j => residueIndexLower (lo j) M (a j))
      (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) q I x := by
  have hc := Fintype.card_congr (residuePrimeCoordinateCellEquiv lo N M a q hM hcop I x)
  have hb := Fintype.card_congr (integerResidueBoxEquiv lo (fun j => lo j + N j)
    (fun _ => (M : ℤ)) a (fun _ => Nat.cast_pos.mpr hM))
  rw [Fintype.card_coe] at hc hb
  rw [residuePrimeCoordinateMassRatio_eq_count, primeCoordinateMassRatio_eq_count, ← hc, ← hb]

theorem residuePrimeCoordinateMassRatio_close {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hsmall : (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) ≤ 1 / 2) :
    |residuePrimeCoordinateMassRatio lo N M a q I x - 1| ≤
      2 * ∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
        residueIndexLength (lo j) (lo j + N j) M (a j) := by
  let inv : ∀ i, σ → ZMod (q i) :=
    fun i => (affineResidueCoordinateEquiv M (q i) a (hcop i)).symm (x i)
  have hx : (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (inv i)) = x := by
    funext i
    exact Equiv.apply_symm_apply _ _
  have hlength := integerResidueBox_lengths_pos lo (fun j => lo j + N j)
    (fun _ => (M : ℤ)) a (fun _ => Nat.cast_pos.mpr hM) hne
  rw [← hx, residuePrimeCoordinateMassRatio_affine lo N M a q hM hcop I inv]
  exact primeCoordinateMassRatio_close _ _ hlength q hpair I inv hsmall

theorem residuePrimeCoordinateDensity_productMarginalsClose {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (hpair : Pairwise (fun i j => (q i).Coprime (q j))) (r : ℕ) (η : ℝ)
    (hsmall : ∀ I : Finset ι, I.card ≤ r → (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) ≤ 1 / 2)
    (herror : ∀ I : Finset ι, I.card ≤ r → 2 * (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) ≤ η) :
    ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) η r := by
  intro I hI x _
  rw [residuePrimeCoordinateDensity_conditional_one]
  exact (residuePrimeCoordinateMassRatio_close lo N M a hne q hM hcop hpair I x
    (hsmall I hI)).trans (herror I hI)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateProduct_le_exp {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (I : Finset ι) (p : ℝ) (hq : ∀ i, (q i : ℝ) ≤ Real.exp p) :
    ((∏ i ∈ I, q i : ℕ) : ℝ) ≤ Real.exp (p * I.card) := by
  rw [Nat.cast_prod]
  calc
    (∏ i ∈ I, (q i : ℝ)) ≤ ∏ _i ∈ I, Real.exp p :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hq i)
    _ = Real.exp ((I.card : ℝ) * p) := by rw [Finset.prod_const, Real.exp_nat_mul]
    _ = Real.exp (p * I.card) := by rw [mul_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinate_error_le_exp {ι σ : Type*} [DecidableEq ι] [Fintype σ]
    (moduli : ι → ℕ) (L : σ → ℕ) (R : ℕ) (B C D : ℝ) (hB : 0 ≤ B)
    (hmoduli : ∀ i, (moduli i : ℝ) ≤ Real.exp B)
    (hdim : (Fintype.card σ : ℝ) ≤ Real.exp C)
    (hlength : ∀ k, Real.exp (B * R + D + C + 1) ≤ (L k : ℝ))
    (S : Finset ι) (hS : S.card ≤ R) :
    2 * (∑ k, ((∏ i ∈ S, moduli i : ℕ) : ℝ) / L k) ≤ Real.exp (-D) := by
  have hprod : ((∏ i ∈ S, moduli i : ℕ) : ℝ) ≤ Real.exp (B * R) :=
    (primeCoordinateProduct_le_exp moduli S B hmoduli).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hS) hB))
  have hterm (k : σ) : ((∏ i ∈ S, moduli i : ℕ) : ℝ) / L k ≤ Real.exp (-D - C - 1) := by
    have hL : (0 : ℝ) < L k := (Real.exp_pos _).trans_le (hlength k)
    apply (div_le_iff₀ hL).mpr
    calc
      _ ≤ Real.exp (B * R) := hprod
      _ = Real.exp (-D - C - 1) * Real.exp (B * R + D + C + 1) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlength k) (Real.exp_pos _).le
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset σ)) => hterm k)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ 2 * ((Fintype.card σ : ℝ) * Real.exp (-D - C - 1)) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ Real.exp 1 * (Real.exp C * Real.exp (-D - C - 1)) :=
      mul_le_mul htwo (mul_le_mul_of_nonneg_right hdim (Real.exp_pos _).le)
        (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-D) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem residuePrimeDensity_close_of_lengths {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (moduli : ι → ℕ) [∀ i, NeZero (moduli i)] (hM : 0 < M)
    (hcop : ∀ i, M.Coprime (moduli i)) (hpair : Pairwise (fun i l => (moduli i).Coprime (moduli l)))
    (R : ℕ) (B C D η : ℝ) (hB : 0 ≤ B) (hη : η ≤ 1) (herror : Real.exp (-D) ≤ η)
    (hmoduli : ∀ i, (moduli i : ℝ) ≤ Real.exp B) (hdim : (Fintype.card σ : ℝ) ≤ Real.exp C)
    (hlength : ∀ k, Real.exp (B * R + D + C + 1) ≤
      (residueIndexLength (lo k) (lo k + N k) M (a k) : ℝ)) :
    ProductMarginalsClose (primeCoordinateReference (σ := σ) moduli)
      (residuePrimeCoordinateDensity lo N M a hne moduli (fun _ => 1)) η R := by
  have herr (S : Finset ι) (hS : S.card ≤ R) :=
    (primeCoordinate_error_le_exp moduli (fun k => residueIndexLength (lo k) (lo k + N k) M (a k))
      R B C D hB hmoduli hdim hlength S hS).trans herror
  apply residuePrimeCoordinateDensity_productMarginalsClose lo N M a hne moduli hM hcop hpair R η
  · intro S hS
    have he := herr S hS
    linarith
  · exact herr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidueAccuracy
namespace OAI

section

namespace Erdos3

theorem affineComparisonAccuracy_bounds {P L T level : ℝ} (b : ℕ)
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hT : 0 ≤ T) (hlevel : Real.exp (-L) ≤ level) :
    0 < affineComparisonAccuracy b P L T ∧ affineComparisonAccuracy b P L T < 1 ∧
    affineComparisonAccuracy b P L T ≤ Real.exp (-T) / 8 ∧
    affineComparisonAccuracy b P L T ≤ level * Real.exp (-T) / 8 ∧
    affineComparisonAccuracy b P L T ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)) := by
  have hp : 0 ≤ (P + 3) ^ 3 := by positivity
  have hb : 0 ≤ 2 * (b : ℝ) * (P + 2) := by positivity
  have hpos : 0 < affineComparisonAccuracyLog b P L T := by
    unfold affineComparisonAccuracyLog
    linarith
  refine ⟨Real.exp_pos _, ?_, ?_, ?_, ?_⟩
  · exact Real.exp_lt_one_iff.mpr (by linarith)
  · exact exp_neg_le_exp_neg_div_eight (by unfold affineComparisonAccuracyLog; linarith)
  · calc
      _ ≤ Real.exp (-(L + T)) / 8 :=
        exp_neg_le_exp_neg_div_eight (by unfold affineComparisonAccuracyLog; linarith)
      _ ≤ level * Real.exp (-T) / 8 := by
        rw [neg_add, Real.exp_add]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlevel (Real.exp_pos _).le) (by norm_num)
  · exact exp_neg_le_half_exp_neg (by unfold affineComparisonAccuracyLog; linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.InitialMaskedAffineComparisonAtDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {Ω ι σ J : Type*} [Fintype J] [Fintype Ω] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {b : ℕ}
variable (hb : affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ b)

variable (p : FiniteProbabilityWeights Ω)

variable (F : Ω → ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (sourceBase : ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))

variable {w : Ω → ℝ}

variable (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (hsourceclose : ProductMarginalsClose (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) (observedProductDensity (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) p F (fun _ => 1)) (affineComparisonAccuracy (b) (affineComparisonScale ε L T C) L T)
      (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T))))

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

include hb p F sourceBase siteBase hw hstable hupper hM hpair hcop u hg hh hL hT hlower hsourceclose prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength

theorem chosen_stable_affine_from_source_marginals_at_degree :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (b)) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  let j := affineRemovalDepth T
  let r := affineComparisonTail ε L T
  let P := affineComparisonScale ε L T C
  let η := affineComparisonAccuracy b P L T
  let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
  have hscale := affineComparisonScale_bounds (ε := ε) hL hT hC
  have heta := affineComparisonAccuracy_bounds b hscale.1 hL hT hlower
  have hrank : j + r ≤ max ((j + r) * (affineComparisonMoment P + 1)) (2 * b + j) := by
    have hm : j + r ≤ (j + r) * (affineComparisonMoment P + 1) := by
      calc
        j + r = (j + r) * 1 := (Nat.mul_one _).symm
        _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    exact hm.trans (le_max_left _ _)
  obtain ⟨rem, cs, hchain, _, hmass, hrem⟩ :=
    exists_finite_cylinder_removal μ (primeCoordinateReference_weight_pos _)
      sourceBase p F 2 (Real.exp (-T)) η j r (by norm_num) (Real.exp_pos _).le heta.2.1.le
      (affineRemovalDepth_cutoff T) (ProductMarginalsClose.mono μ hsourceclose hrank)
      w (fun z => (hw z).1) (fun z => (hw z).2)
  have hc := chosen_stable_residue_affine_total_at_degree_s2 (b := b) (hb := hb) (Ω := Ω) (ι := ι) (σ := σ) (J := J)
    (h := h) (g := g) (lo := lo) (a := a) (N := N) (M := M) (q := q)
    (ε := ε) (L := L) (T := T) (C := C) (shell := shell) (modLog := modLog)
    (level := level) (K := K) (base := base) (w := w) (rem := rem) (cs := cs)
    p F sourceBase siteBase hchain hw hrem hmass hstable hupper hM hpair hcop u hg hh
  exact hc hL hT hlower hsourceclose prime power hprime hpower hJ hshell hlevel2
    hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength

end

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {b : ℕ}
variable (hb : affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ b)

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceNonempty : Nonempty (IntegerResidueBox sourceLo
  (fun k => sourceLo k + sourceN k) (fun _ => (sourceM : ℤ)) sourceA))
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k)
    (fun _ => (sourceM : ℤ)) sourceA,
  0 ≤ w (fun k => (z k).val) ∧ w (fun k => (z k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (hsourceCop : ∀ i ∉ K, sourceM.Coprime (q i))
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (modLog *
    (max ((affineRemovalDepth T + affineComparisonTail ε L T) *
      (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
      (2 * b + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (b)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) sourceM (sourceA k) : ℝ))

include hb hstable hupper hM hpair hcop u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceNonempty w hw hsourceM hsourceCop sourceDimLog hsourceDim hsourceLength

theorem residue_source_stable_affine_comparison_at_degree_s2_oai :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (b)) (residuePrimeCoordinateDensity sourceLo sourceN sourceM sourceA sourceNonempty
        (fun i : {i // i ∉ K} => q i.val) w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  let P := affineComparisonScale ε L T C
  let η := affineComparisonAccuracy b P L T
  let R := max ((affineRemovalDepth T + affineComparisonTail ε L T) * (affineComparisonMoment P + 1))
    (2 * b + affineRemovalDepth T)
  let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
  let p := @FiniteProbabilityWeights.uniform
    (IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k) (fun _ => (sourceM : ℤ)) sourceA) _ sourceNonempty
  let F := fun z : IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k)
      (fun _ => (sourceM : ℤ)) sourceA =>
    primeCoordinateObservation (fun i : {i // i ∉ K} => q i.val) (fun k => (z k).val)
  have hscale := affineComparisonScale_bounds (ε := ε) hL hT hC
  have heta := affineComparisonAccuracy_bounds b hscale.1 hL hT hlower
  have hpair' : Pairwise (fun i k : {i // i ∉ K} => (q i.val).Coprime (q k.val)) :=
    fun i k hik => hpair (fun heq => hik (Subtype.ext heq))
  have hsrc0 := residuePrimeDensity_close_of_lengths (ι := {i // i ∉ K}) (σ := Option J × σ)
    sourceLo sourceN sourceM sourceA sourceNonempty (fun i : {i // i ∉ K} => q i.val)
    hsourceM (fun i => hsourceCop i.val i.property) hpair'
    R modLog sourceDimLog (affineComparisonAccuracyLog b P L T) η
  have he : Real.exp (-affineComparisonAccuracyLog b P L T) ≤ η := by
    unfold η affineComparisonAccuracy
    exact le_rfl
  have hsrc1 := hsrc0 hmodLog heta.2.1.le he
  have hsrc := hsrc1 (fun i => hmoduli i.val i.property) hsourceDim hsourceLength
  change ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η R at hsrc
  have hc := chosen_stable_affine_from_source_marginals_at_degree (b := b) (hb := hb)
    (Ω := IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k) (fun _ => (sourceM : ℤ)) sourceA)
    (ι := ι) (σ := σ) (J := J) (h := h) (g := g) (lo := lo) (a := a) (N := N) (M := M) (q := q)
    (ε := ε) (L := L) (T := T) (C := C) (shell := shell) (modLog := modLog)
    (level := level) (K := K) (base := base) (w := fun z => w (fun k => (z k).val))
    p F (fun _ _ => 0) (fun _ _ => 0) hw hstable hupper hM hpair hcop u hg hh hL hT hlower
  exact hc hsrc prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC
    hcount hmandatory dimLog hdim hlength

end

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.residue_source_stable_affine_comparison_at_degree_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.residue_source_stable_affine_comparison_at_degree_s2_oai.{u_1, u_2, u_3}
