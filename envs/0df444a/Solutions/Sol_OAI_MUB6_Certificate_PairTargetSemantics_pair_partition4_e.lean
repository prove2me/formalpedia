-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T11:55:49.270506+00:00
-- url     : https://prove2.me/submissions/21f961b0-8ffb-4251-85dd-faede8135c90

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_ne_zero {z : ℂ} (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

theorem IsHadamard.row_gram {H : CMatrix} (hH : IsHadamard H) :
    H * Hᴴ = (6 : ℂ) • (1 : CMatrix) := by
  have hl : ((6 : ℂ)⁻¹ • Hᴴ) * H = (1 : CMatrix) := by
    rw [smul_mul_assoc, hH.2, smul_smul]
    norm_num
  have hr := mul_eq_one_comm.mp hl
  rw [mul_smul_comm] at hr
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hr
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Averages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6

theorem average_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → ℝ) : average (f ∘ e) = average f := by
  simp only [average, Fintype.card_congr e, Function.comp_apply, e.sum_comp]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem average_mul (c : ℝ) (f : ι → ℝ) :
    average (fun i => c * f i) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem sum_eq_card_mul_average (f : ι → ℝ) :
    (∑ i, f i) = (Fintype.card ι : ℝ) * average f := by
  classical
  by_cases hc : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp [average]
  · have hcr : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [average, ← mul_assoc, mul_inv_cancel₀ hcr, one_mul]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem injectiveMoment_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A = average (fun ρ : Fin p ↪ Coord =>
      average (fun κ : Fin q ↪ Coord =>
        ((exponentMonomial H A ρ κ).re +
          (exponentMonomial H.transpose A ρ κ).re) / 2)) :=
  average_prod _

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    {z : ℂ} (hz : z ≠ 0) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]

theorem product_grouped {n k : ℕ} (label : Fin n → Fin k)
    (x : Fin k → ℂ) (hx : ∀ b, x b ≠ 0) (a : Fin n → ℤ) :
    (∏ j, x (label j) ^ a j) = ∏ b, x b ^ (∑ j with label j = b, a j) := by
  rw [← Finset.prod_fiberwise Finset.univ label]
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_zpow_eq_zpow_sum _ a (hx b)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

theorem rawMonomial_grouped {p n k : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (ρ : Fin p ↪ Coord) (κ : Fin k ↪ Coord) :
    rawMonomial H A ρ (fun j => κ (label j)) =
      exponentMonomial H (groupedColumns A label) ρ κ := by
  unfold rawMonomial exponentMonomial groupedColumns
  apply Finset.prod_congr rfl
  intro i _
  exact product_grouped label (fun b => H (ρ i) (κ b))
    (fun b => unit_ne_zero (hH.1 _ _)) (fun j => A i j)

theorem rowFourier_product_expand {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) (ρ : Fin p ↪ Coord) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ κ : Fin n → Coord, rawMonomial H A ρ κ := by
  simp only [rowFourier, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _
  exact Finset.prod_comm

/-- The unnormalized equality-partition identity. The factor `(6)_k` in
the manuscript is exactly the cardinality of the inner injection type. -/
theorem rowFourier_partition_expand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        exponentMonomial H (groupedColumns A (F.label s)) ρ κ := by
  rw [rowFourier_product_expand]
  have hs := (F.assignmentsEquiv cover).sum_comp
    (fun κ : Fin n → Coord => rawMonomial H A ρ κ)
  change (∑ s : Σ s, Fin (F.blocks s) ↪ Coord,
    rawMonomial H A ρ (fun i => s.2 (F.label s.1 i))) = _ at hs
  rw [Fintype.sum_sigma] at hs
  rw [← hs]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro κ _
  exact rawMonomial_grouped hH A (F.label s) ρ κ

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

theorem pattern4_0 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    (_h30 : f 3 = f 0)
    (_h31 : f 3 = f 1)
    (h32 : f 3 = f 2)
    : ∀ i j, family4.label 0 i = family4.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_1 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    (h30 : f 3 ≠ f 0)
    (_h31 : f 3 ≠ f 1)
    (_h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 1 i = family4.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_2 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    (_h30 : f 3 = f 0)
    (h31 : f 3 = f 1)
    (h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 2 i = family4.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_3 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    (_h30 : f 3 ≠ f 0)
    (_h31 : f 3 ≠ f 1)
    (h32 : f 3 = f 2)
    : ∀ i j, family4.label 3 i = family4.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_4 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    (h30 : f 3 ≠ f 0)
    (_h31 : f 3 ≠ f 1)
    (h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 4 i = family4.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_5 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (_h21 : f 2 ≠ f 1)
    (_h30 : f 3 = f 0)
    (_h31 : f 3 ≠ f 1)
    (h32 : f 3 = f 2)
    : ∀ i j, family4.label 5 i = family4.label 5 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_6 {B : Type*} (f : Fin 4 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (_h21 : f 2 ≠ f 1)
    (_h30 : f 3 ≠ f 0)
    (h31 : f 3 = f 1)
    (h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 6 i = family4.label 6 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_7 {B : Type*} (f : Fin 4 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    (h30 : f 3 ≠ f 0)
    (h31 : f 3 ≠ f 1)
    (_h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 7 i = family4.label 7 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_8 {B : Type*} (f : Fin 4 → B)
    (_h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    (h30 : f 3 = f 0)
    (h31 : f 3 ≠ f 1)
    (_h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 8 i = family4.label 8 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_9 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    (_h30 : f 3 ≠ f 0)
    (_h31 : f 3 = f 1)
    (h32 : f 3 = f 2)
    : ∀ i j, family4.label 9 i = family4.label 9 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_10 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    (h30 : f 3 ≠ f 0)
    (h31 : f 3 ≠ f 1)
    (_h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 10 i = family4.label 10 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_11 {B : Type*} (f : Fin 4 → B)
    (_h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    (h30 : f 3 = f 0)
    (h31 : f 3 ≠ f 1)
    (h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 11 i = family4.label 11 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_12 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    (_h30 : f 3 ≠ f 0)
    (h31 : f 3 = f 1)
    (h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 12 i = family4.label 12 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_13 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    (_h30 : f 3 ≠ f 0)
    (_h31 : f 3 ≠ f 1)
    (h32 : f 3 = f 2)
    : ∀ i j, family4.label 13 i = family4.label 13 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm] <;> grind

theorem pattern4_14 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    (h30 : f 3 ≠ f 0)
    (h31 : f 3 ≠ f 1)
    (h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 14 i = family4.label 14 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm] <;> grind

theorem covers4 {B : Type*} (f : Fin 4 → B) :
    ∃ p, ∀ i j, (family4.label p i = family4.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      by_cases h30 : f 3 = f 0
      ·
        refine ⟨0, ?_⟩
        apply pattern4_0 f <;> simp_all [eq_comm]
      ·
        refine ⟨1, ?_⟩
        apply pattern4_1 f <;> simp_all [eq_comm]
    ·
      by_cases h30 : f 3 = f 0
      ·
        refine ⟨2, ?_⟩
        apply pattern4_2 f <;> simp_all [eq_comm]
      ·
        by_cases h32 : f 3 = f 2
        ·
          refine ⟨3, ?_⟩
          apply pattern4_3 f <;> simp_all [eq_comm]
        ·
          refine ⟨4, ?_⟩
          apply pattern4_4 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      by_cases h30 : f 3 = f 0
      ·
        refine ⟨5, ?_⟩
        apply pattern4_5 f <;> simp_all [eq_comm]
      ·
        by_cases h31 : f 3 = f 1
        ·
          refine ⟨6, ?_⟩
          apply pattern4_6 f <;> simp_all [eq_comm]
        ·
          refine ⟨7, ?_⟩
          apply pattern4_7 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        by_cases h30 : f 3 = f 0
        ·
          refine ⟨8, ?_⟩
          apply pattern4_8 f <;> simp_all [eq_comm]
        ·
          by_cases h31 : f 3 = f 1
          ·
            refine ⟨9, ?_⟩
            apply pattern4_9 f <;> simp_all [eq_comm]
          ·
            refine ⟨10, ?_⟩
            apply pattern4_10 f <;> simp_all [eq_comm]
      ·
        by_cases h30 : f 3 = f 0
        ·
          refine ⟨11, ?_⟩
          apply pattern4_11 f <;> simp_all [eq_comm]
        ·
          by_cases h31 : f 3 = f 1
          ·
            refine ⟨12, ?_⟩
            apply pattern4_12 f <;> simp_all [eq_comm]
          ·
            by_cases h32 : f 3 = f 2
            ·
              refine ⟨13, ?_⟩
              apply pattern4_13 f <;> simp_all [eq_comm]
            ·
              refine ⟨14, ?_⟩
              apply pattern4_14 f <;> simp_all [eq_comm]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_NormalizedPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem inverse_six_pow_real (n : ℕ) :
    (6 : ℂ)⁻¹ ^ n = (((6 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
  simp

theorem partition_integrand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    ((∏ j, rowFourier H ρ (fun i => A i j)).re +
      (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (6 : ℝ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        ((exponentMonomial H (groupedColumns A (F.label s)) ρ κ).re +
          (exponentMonomial H.transpose (groupedColumns A (F.label s)) ρ κ).re) / 2 := by
  rw [rowFourier_partition_expand hH A ρ F cover,
    rowFourier_partition_expand hH.transpose A ρ F cover, inverse_six_pow_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_add_distrib]
  ring

theorem average_injection_sum {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    average (fun ρ : Fin p ↪ Coord => ∑ κ : Fin q ↪ Coord,
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2) =
      (Fintype.card (Fin q ↪ Coord) : ℝ) * injectiveMoment H A := by
  have he (ρ : Fin p ↪ Coord) := sum_eq_card_mul_average
    (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2)
  simp_rw [he]
  rw [average_mul, ← injectiveMoment_iterated H A]

/-- The normalized equality-pattern expansion. For k blocks the coefficient
is `card (Fin k ↪ Fin 6) / 6^n`, exactly `(6)_k / 6^n` in the source. -/
theorem averagedRowProducts_partition {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    averagedRowProducts H A =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  unfold averagedRowProducts
  simp_rw [partition_integrand hH A _ F cover]
  rw [average_mul, average_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [average_injection_sum H (groupedColumns A (F.label s))]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

/-- A uniform injection of all six row indices is a uniform permutation.
This identifies the general partition theorem with the paper's pair average. -/
theorem averagedRowProducts_eq_pairAverage {n : ℕ} (H : CMatrix)
    (A : Matrix Coord (Fin n) ℤ) :
    averagedRowProducts H A =
      pairAverage H (fun K => (∏ j, g K (fun i => A i j)).re) := by
  let f : Equiv.Perm Coord → ℝ := fun π =>
    ((∏ j, g (fun i k => H (π i) k) (fun i => A i j)).re +
      (∏ j, g (fun i k => H k (π i)) (fun i => A i j)).re) / 2
  calc
    averagedRowProducts H A =
        average (f ∘ Equiv.embeddingEquivOfFinite Coord) := by rfl
    _ = average f := average_equiv (Equiv.embeddingEquivOfFinite Coord) f
    _ = _ := rfl

theorem pairAverage_products_partition {n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix Coord (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    pairAverage H (fun K => (∏ j, g K (fun i => A i j)).re) =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  rw [← averagedRowProducts_eq_pairAverage H A]
  exact averagedRowProducts_partition hH A F cover

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_PartitionRules
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open scoped BigOperators

theorem sum_fin_fifteen {α : Type*} [AddCommMonoid α] (f : Fin 15 → α) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + 0)))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14
  ac_rfl

theorem partitionWeight4_0 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 0) ↪ Coord) : ℝ) / 6 ^ 4 = (1/216 : ℝ) := by
  change (Fintype.card (Fin 1 ↪ Fin 6) : ℝ) / 6 ^ 4 = (1/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_1 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 1) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_2 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 2) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_3 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 3) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_4 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 4) ↪ Coord) : ℝ) / 6 ^ 4 = (5/54 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/54 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_5 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 5) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_6 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 6) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_7 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 7) ↪ Coord) : ℝ) / 6 ^ 4 = (5/54 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/54 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_8 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 8) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_9 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 9) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_10 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 10) ↪ Coord) : ℝ) / 6 ^ 4 = (5/54 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/54 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_11 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 11) ↪ Coord) : ℝ) / 6 ^ 4 = (5/54 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/54 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_12 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 12) ↪ Coord) : ℝ) / 6 ^ 4 = (5/54 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/54 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_13 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 13) ↪ Coord) : ℝ) / 6 ^ 4 = (5/54 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/54 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_14 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 14) ↪ Coord) : ℝ) / 6 ^ 4 = (5/18 : ℝ) := by
  change (Fintype.card (Fin 4 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/18 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem pair_partition4_e_oai {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix Coord (Fin 4) ℤ) :
    pairAverage H (fun K => (∏ j, g K (fun u => A u j)).re) =
      (1 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 0)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 1)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 2)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 3)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 4)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 5)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 6)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 7)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 8)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 9)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 10)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 11)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 12)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 13)) +
      (5 / 18 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 14)) := by
  have h := pairAverage_products_partition hH A EqualityPatterns.family4 EqualityPatterns.covers4
  rw [sum_fin_fifteen] at h
  simpa only [partitionWeight4_0, partitionWeight4_1, partitionWeight4_2, partitionWeight4_3, partitionWeight4_4, partitionWeight4_5, partitionWeight4_6, partitionWeight4_7, partitionWeight4_8, partitionWeight4_9, partitionWeight4_10, partitionWeight4_11, partitionWeight4_12, partitionWeight4_13, partitionWeight4_14] using h

end MUB6.Certificate.PairTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4_e_oai := @OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4_e_oai
