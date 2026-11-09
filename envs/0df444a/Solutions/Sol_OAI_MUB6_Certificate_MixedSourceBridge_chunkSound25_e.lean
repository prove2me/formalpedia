-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound25_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:04:42.515234+00:00
-- url     : https://prove2.me/submissions/86bebc49-3b9e-450a-80e6-e3129e9ef2ef

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound404_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound411_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound412_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound413_e

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

theorem character_add (x : Coord → ℂ) (hx : ∀ i, x i ≠ 0) (a b : Charge) :
    character x (a + b) = character x a * character x b := by
  simp only [character, Pi.add_apply, zpow_add₀ (hx _), Finset.prod_mul_distrib]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Characters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_inv_eq_conj {z : ℂ} (hz : Complex.normSq z = 1) : z⁻¹ = conj z := by
  simp [Complex.inv_def, hz]

theorem character_neg (x : Coord → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (a : Charge) : character x (-a) = conj (character x a) := by
  simp only [character, Pi.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro i _
  rw [← unit_inv_eq_conj (hx i), inv_zpow]

theorem g_neg {H : CMatrix} (hH : IsHadamard H) (a : Charge) :
    g H (-a) = conj (g H a) := by
  simp only [g, character_neg _ (fun i => hH.1 i _) a, map_mul, map_sum,
    map_inv₀, map_ofNat]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
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

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem character_single (x : Coord → ℂ) (i : Coord) (n : ℤ) :
    character x (Pi.single i n) = x i ^ n := by
  classical
  simp [character, Pi.single_apply]

theorem character_difference (x : Coord → ℂ) (hx : ∀ k, Complex.normSq (x k) = 1)
    (i j : Coord) : character x (difference i j) = x i * conj (x j) := by
  rw [difference, sub_eq_add_neg, character_add x (fun k => unit_ne_zero (hx k)),
    character_neg x hx, character_single, character_single]
  simp

theorem g_difference {H : CMatrix} (hH : IsHadamard H) (i j : Coord) :
    g H (difference i j) = if i = j then 1 else 0 := by
  simp only [g, character_difference _ (fun k => hH.1 k _)]
  rw [hH.row_orthogonal]
  split_ifs <;> norm_num

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_Transitions
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sqrt_six_square : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
  have h : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  exact_mod_cast h

theorem sqrt_six_normSq : Complex.normSq (Real.sqrt 6 : ℂ) = 6 := by
  rw [Complex.normSq_ofReal]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]

theorem transition_column_inner (b c d : Basis) (k l : Coord) :
    (∑ i, conj (transition b c i k) * transition b d i l) =
      6 * inner ℂ (c k) (d l) := by
  have hterm (i : Coord) : conj (transition b c i k) * transition b d i l =
      6 * (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by
    simp only [transition, map_mul, Complex.conj_ofReal, inner_conj_symm]
    calc
      _ = (Real.sqrt 6 : ℂ) ^ 2 *
        (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by ring
      _ = _ := by rw [sqrt_six_square]
  simp_rw [hterm]
  rw [← Finset.mul_sum, b.sum_inner_mul_inner]

theorem transition_isHadamard {m : ℕ} (B : Fin m → Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) : IsHadamard (transition (B r) (B s)) := by
  refine ⟨?_, ?_⟩
  · intro i k
    rw [transition, map_mul, sqrt_six_normSq, hB r s hrs i k]
    norm_num
  · ext i j
    change (∑ k, conj (transition (B r) (B s) k i) * transition (B r) (B s) k j) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [transition_column_inner, (B s).inner_eq_ite]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_ChargeDecomposition
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem weightMultiset_card (w : Coord → ℕ) :
    (weightMultiset w).card = ∑ i, w i := by
  have h (s : Finset Coord) : (∑ i ∈ s, Multiset.replicate (w i) i).card = ∑ i ∈ s, w i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, Multiset.card_add, ih]
  exact h Finset.univ

theorem weightMultiset_count (w : Coord → ℕ) (k : Coord) :
    (weightMultiset w).count k = w k := by
  have h (s : Finset Coord) :
      (∑ i ∈ s, Multiset.replicate (w i) i).count k = ∑ i ∈ s, if i = k then w i else 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, Multiset.count_add, Multiset.count_replicate, ih]
  simpa [weightMultiset] using h Finset.univ

theorem positivePositions_card (a : Charge) : (positivePositions a).card = order a :=
  weightMultiset_card _

theorem negativePositions_card {a : Charge} (ha : Balanced a) :
    (negativePositions a).card = order a := by
  have h : (∑ i, ((a i).toNat : ℤ)) - ∑ i, ((-a i).toNat : ℤ) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [Int.toNat_sub_toNat_neg] using (show ∑ i, a i = 0 from ha)
  rw [negativePositions, weightMultiset_card, order]
  exact_mod_cast (sub_eq_zero.mp h).symm

theorem charge_eq_counts (a : Charge) (k : Coord) :
    a k = ((positivePositions a).count k : ℤ) - (negativePositions a).count k := by
  rw [positivePositions, negativePositions, weightMultiset_count, weightMultiset_count]
  exact (Int.toNat_sub_toNat_neg _).symm

theorem positive_negative_ne {a : Charge} {i j : Coord}
    (hi : i ∈ positivePositions a) (hj : j ∈ negativePositions a) : i ≠ j := by
  intro h
  subst j
  rw [← Multiset.count_pos, positivePositions, weightMultiset_count] at hi
  rw [← Multiset.count_pos, negativePositions, weightMultiset_count] at hj
  have hp := Int.pos_iff_toNat_pos.mpr hi
  have hn := Int.pos_iff_toNat_pos.mpr hj
  omega

/-- A balanced charge of order one is one positive and one negative coordinate. -/
theorem order_one_decomposition {a : Charge} (ha : Balanced a) (ho : order a = 1) :
    ∃ i j, i ≠ j ∧ a = difference i j := by
  obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp ((positivePositions_card a).trans ho)
  obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp ((negativePositions_card ha).trans ho)
  refine ⟨i, j, positive_negative_ne (a := a) (by simp [hi]) (by simp [hj]), ?_⟩
  funext k
  rw [charge_eq_counts a k, hi, hj]
  simp [difference, Pi.single_apply, Multiset.count_singleton, eq_comm]

theorem g_order_one {H : CMatrix} (hH : IsHadamard H) {a : Charge}
    (ha : Balanced a) (ho : order a = 1) : g H a = 0 := by
  obtain ⟨i, j, hij, rfl⟩ := order_one_decomposition ha ho
  simp [g_difference hH, hij]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_CompleteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem relativeMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) : IsHadamard (relativeMatrix B r s) :=
  transition_isHadamard B hB r (r.succAbove s) (r.ne_succAbove s)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Equivalence
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem IsHadamard.permutations {H : CMatrix} (hH : IsHadamard H)
    (r c : Equiv.Perm Coord) : IsHadamard (fun i j => H (r i) (c j)) := by
  refine ⟨fun i j => hH.1 _ _, ?_⟩
  ext i j
  change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  rw [Equiv.sum_comp r (fun k => conj (H k (c i)) * H k (c j)), hH.column_orthogonal]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> norm_num

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

theorem average_congr {f g : ι → ℝ} (h : ∀ i, f i = g i) :
    average f = average g := by
  congr 1
  exact funext h

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sampling identities. The splitting theorem below is the counting
step behind contraction of an order-one row; it is independent of the values
of the matrix entries and uses no certificate data. -/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

variable {A B V : Type*} [Fintype A] [Fintype B] [AddCommMonoid V]

theorem sum_injective_extension {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) =
      ∑ e : Fin p ↪ B, ∑ b : {b // b ∉ Set.range e}, f e b := by
  classical
  have h := (Equiv.embeddingFinSucc p B).sum_comp
    (fun x : Σ e : Fin p ↪ B, {b // b ∉ Set.range e} => f x.1 x.2)
  simpa [dropFirst, Fintype.sum_sigma] using h

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SamplingAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

theorem unused_card {p n : ℕ} (e : Fin p ↪ Fin n)
    [Fintype {i // i ∉ Set.range e}] :
    Fintype.card {i // i ∉ Set.range e} = n - p := by
  rw [Fintype.card_subtype_compl]
  have hr : Fintype.card {i // i ∈ Set.range e} = p := by
    rw [Fintype.card_range, Fintype.card_fin]
  rw [hr, Fintype.card_fin]

theorem embedding_succ_card (p n : ℕ) :
    Fintype.card (Fin (p + 1) ↪ Fin n) =
      Fintype.card (Fin p ↪ Fin n) * (n - p) := by
  rw [Fintype.card_congr (Equiv.embeddingFinSucc p (Fin n)), Fintype.card_sigma]
  simp only [unused_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem sum_dropFirst {p n : ℕ} (f : (Fin p ↪ Fin n) → ℝ) :
    (∑ e : Fin (p + 1) ↪ Fin n, f (dropFirst e)) =
      (n - p : ℕ) * ∑ e, f e := by
  have hs := sum_injective_extension (fun e (_ : Fin n) => f e)
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin, Fintype.card_fin]

/-- Deleting a coordinate of a uniform injection leaves a uniform injection. -/
theorem average_dropFirst {p n : ℕ} (hp : p < n) (f : (Fin p ↪ Fin n) → ℝ) :
    average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e)) = average f := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  unfold average
  rw [embedding_succ_card, Nat.cast_mul, sum_dropFirst, mul_inv_rev]
  calc
    _ = (((n - p : ℕ) : ℝ)⁻¹ * (n - p : ℕ)) *
        ((Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ * ∑ e, f e) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_EmbeddedCharge
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem embedCharge_outside {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (i : Coord)
    (hi : i ∉ Set.range ρ) : embedCharge ρ a i = 0 :=
  Function.extend_apply' _ _ _ hi

theorem embedCharge_sum {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    ∑ i, embedCharge ρ a i = ∑ i, a i := by
  symm
  exact Fintype.sum_of_injective ρ ρ.injective a (embedCharge ρ a)
    (embedCharge_outside ρ a) (fun i => (embedCharge_apply ρ a i).symm)

theorem embedCharge_order {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    order (embedCharge ρ a) = ∑ i, (a i).toNat := by
  symm
  apply Fintype.sum_of_injective ρ ρ.injective (fun i => (a i).toNat)
    (fun i => (embedCharge ρ a i).toNat)
  · intro i hi
    rw [embedCharge_outside ρ a i hi]
    rfl
  · intro i
    rw [embedCharge_apply]

theorem embedCharge_neg {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    embedCharge ρ (-a) = -embedCharge ρ a := by
  funext i
  by_cases hi : i ∈ Set.range ρ
  · obtain ⟨j, rfl⟩ := hi
    simp
  · simp [Pi.neg_apply, embedCharge_outside ρ _ i hi]

theorem character_embedCharge {p : ℕ} (x : Coord → ℂ) (ρ : Fin p ↪ Coord)
    (a : Fin p → ℤ) : character x (embedCharge ρ a) = ∏ i, x (ρ i) ^ a i := by
  symm
  apply Fintype.prod_of_injective ρ ρ.injective (fun i => x (ρ i) ^ a i)
    (fun i => x i ^ embedCharge ρ a i)
  · intro i hi
    rw [embedCharge_outside ρ a i hi, zpow_zero]
  · intro i
    rw [embedCharge_apply]

theorem rowFourier_eq_g {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ a = g H (embedCharge ρ a) := by
  simp only [rowFourier, g, character_embedCharge]

theorem rowFourier_neg {p : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ (-a) = conj (rowFourier H ρ a) := by
  rw [rowFourier_eq_g, embedCharge_neg, g_neg hH, rowFourier_eq_g]

theorem rowFourier_order_one {p : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (ha : ∑ i, a i = 0)
    (ho : ∑ i, (a i).toNat = 1) : rowFourier H ρ a = 0 := by
  rw [rowFourier_eq_g]
  apply g_order_one hH
  · exact (embedCharge_sum ρ a).trans ha
  · exact (embedCharge_order ρ a).trans ho

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem mixedMoment_neg {p n l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) :
    mixedMoment B (-A) label = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  have h : mixedIntegrand B (-A) label r ρ τ = conj (mixedIntegrand B A label r ρ τ) := by
    unfold mixedIntegrand
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_neg (relativeMatrix_isHadamard B hB r _) ρ _
  rw [h, Complex.conj_re]

theorem mixedMoment_factor_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin n)) :
    mixedMoment B (fun i j => A i (σ j)) (label ∘ σ) = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  exact congrArg Complex.re (Equiv.prod_comp σ
    (fun j => rowFourier (relativeMatrix B r (τ (label j))) ρ (fun i => A i j)))

theorem rowFourier_row_permutation {p : ℕ} (H : CMatrix) (a : Fin p → ℤ)
    (σ : Equiv.Perm (Fin p)) (ρ : Fin p ↪ Coord) :
    rowFourier H ρ (a ∘ σ) =
      rowFourier H (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) a := by
  unfold rowFourier
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => H (ρ (σ.symm i)) k ^ a i)

theorem mixedMoment_row_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin p)) :
    mixedMoment B (fun i j => A (σ i) j) label = mixedMoment B A label := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B (fun i j => A (σ i) j) label r ρ τ =
        mixedIntegrand B A label r (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) τ := by
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_row_permutation _ (fun i => A i j) σ ρ
  simp_rw [h]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun τ : Fin l ↪ Coord =>
      (mixedIntegrand B A label r ρ τ).re))

theorem mixedMoment_order_one {p n l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (ha : ∑ i, A i j = 0) (ho : ∑ i, (A i j).toNat = 1) : mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact rowFourier_order_one (relativeMatrix_isHadamard B hB r _) ρ _ ha ho
  simp [mixedMoment, h]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowFourier_zero_first {p : ℕ} (H : CMatrix) (a : Fin (p + 1) → ℤ)
    (ha : a 0 = 0) (ρ : Fin (p + 1) ↪ Coord) :
    rowFourier H ρ a = rowFourier H (Sampling.dropFirst ρ) (fun i => a i.succ) := by
  simp only [rowFourier, Fin.prod_univ_succ, ha, zpow_zero, one_mul]
  rfl

theorem mixedMoment_zero_first_row {p n l : ℕ} (hp : p < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin (p + 1)) (Fin n) ℤ) (label : Fin n → Fin l)
    (hA : ∀ j, A 0 j = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i.succ j) label := by
  apply average_congr
  intro r
  have h (ρ : Fin (p + 1) ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ =
        mixedIntegrand B (fun i j => A i.succ j) label r (Sampling.dropFirst ρ) τ := by
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_zero_first _ (fun i => A i j) (hA j) ρ
  simp_rw [h]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun τ : Fin l ↪ Coord =>
      (mixedIntegrand B (fun i j => A i.succ j) label r ρ τ).re))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Orthogonality
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The finite orthogonality contraction underlying equation (same-matrix). -/
theorem weighted_contraction {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (i : Coord) :
    (∑ j, (∑ k, u k * H i k * conj (H j k)) *
      (∑ l, v l * conj (H i l) * H j l)) =
      6 * ∑ k, u k * v k := by
  have hexpand :
      (∑ j, (∑ k, u k * H i k * conj (H j k)) *
        (∑ l, v l * conj (H i l) * H j l)) =
      ∑ l, ∑ k, (u k * v l * H i k * conj (H i l)) *
        (∑ j, conj (H j k) * H j l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonal]
  have hunit (k : Coord) : H i k * conj (H i k) = 1 := by
    rw [Complex.mul_conj, hH.1]
    norm_num
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    u k * v k * H i k * conj (H i k) * 6 =
      6 * (u k * v k) * (H i k * conj (H i k)) := by ring
    _ = _ := by rw [hunit, mul_one]

theorem g_add_difference {H : CMatrix} (hH : IsHadamard H)
    (a : Charge) (i j : Coord) :
    g H (a + difference i j) = (6 : ℂ)⁻¹ *
      ∑ k, character (fun r => H r k) a * H i k * conj (H j k) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_add _ (fun r => unit_ne_zero (hH.1 r k)),
    character_difference _ (fun r => hH.1 r k)]
  ring

/-- Source Lemma (basic), equation (same-matrix), for arbitrary integral charges. -/
theorem same_matrix_identity {H : CMatrix} (hH : IsHadamard H)
    (a b : Charge) (i : Coord) :
    ∑ j, g H (a + difference i j) * g H (b + difference j i) = g H (a + b) := by
  simp_rw [g_add_difference hH]
  have hexpand :
      (∑ j, ((6 : ℂ)⁻¹ * ∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
        ((6 : ℂ)⁻¹ * ∑ l, character (fun r => H r l) b * H j l * conj (H i l))) =
      (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
        (∑ j, (∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
          (∑ l, character (fun r => H r l) b * conj (H i l) * H j l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∑ l, character (fun r => H r l) b * H j l * conj (H i l)) =
        ∑ l, character (fun r => H r l) b * conj (H i l) * H j l := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hexpand, weighted_contraction hH]
  unfold g
  have hs : (∑ k, character (fun r => H r k) a * character (fun r => H r k) b) =
      ∑ k, character (fun r => H r k) (a + b) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (character_add _ (fun r => unit_ne_zero (hH.1 r k)) a b).symm
  rw [hs]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedShifts
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sampledMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (ρ : Coord ↪ Coord) (s : Coord) : IsHadamard (sampledMatrix B r ρ s) := by
  let e : Equiv.Perm Coord := Equiv.ofBijective ρ
    ⟨ρ.injective, Finite.surjective_of_injective ρ.injective⟩
  exact (relativeMatrix_isHadamard B hB r s).permutations e (Equiv.refl Coord)

theorem mixedIntegrand_three {l : ℕ} (B : Fin 7 → Basis) (a b c : Charge)
    (s t u : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (tripleCharges a b c) ![s, t, u] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b *
        g (sampledMatrix B r ρ (τ u)) c := by
  simp [mixedIntegrand, tripleCharges, Fin.prod_univ_succ, rowFourier, g, character,
    sampledMatrix, mul_assoc]

theorem mixedIntegrand_two {l : ℕ} (B : Fin 7 → Basis) (a b : Charge)
    (s t : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (doubleCharges a b) ![s, t] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b := by
  simp [mixedIntegrand, doubleCharges, Fin.prod_univ_succ, rowFourier, g, character, sampledMatrix]

theorem mixedMoment_same {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  rw [same_matrix_identity (sampledMatrix_isHadamard B hB r ρ _) a b i]

theorem mixedMoment_same_reversed {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference j i) (b + difference i j) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  have h := same_matrix_identity (sampledMatrix_isHadamard B hB r ρ (τ s)) b a i
  simpa only [mul_comm, add_comm] using congrArg
    (fun z => (z * g (sampledMatrix B r ρ (τ u)) c).re) h

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Rules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sound rules for mixed certificate normalization

Generated witnesses may only permute rows or factors, negate all charges,
remove zero rows or factors, and injectively rename labels. The equalities
here justify those operations for the actual finite mixed moments.
-/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.MixedSemantics

theorem permute {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l)
    (ρ : Equiv.Perm (Fin p)) (σ : Equiv.Perm (Fin n)) :
    mixedMoment B A label = mixedMoment B (fun i j => A (ρ i) (σ j)) (label ∘ σ) := by
  rw [mixedMoment_factor_permutation B (fun i j => A (ρ i) j) label σ,
    mixedMoment_row_permutation]

theorem delete_zero_row {p n l : ℕ} (hp : p < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin (p + 1)) (Fin n) ℤ) (label : Fin n → Fin l)
    (ρ : Equiv.Perm (Fin (p + 1))) (hz : ∀ j, A (ρ 0) j = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A (ρ i.succ) j) label := by
  rw [← mixedMoment_row_permutation B A label ρ]
  exact mixedMoment_zero_first_row hp B _ label hz

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5754 raw5754Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5754 raw5754Labels = mixedMoment B raw5754step0 raw5754step0Labels := by
      have hz : ∀ j, raw5754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5754step0 = (fun i j => raw5754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5754step0 raw5754; decide +kernel
      have hl : raw5754step0Labels = raw5754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754 raw5754Labels permutation434 hz
    mixedMoment B raw5754step0 raw5754step0Labels = mixedMoment B raw5754step1 raw5754step1Labels := by
      have hz : ∀ j, raw5754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5754step1 = (fun i j => raw5754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5754step1 raw5754step0; decide +kernel
      have hl : raw5754step1Labels = raw5754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step0 raw5754step0Labels permutation80 hz
    mixedMoment B raw5754step1 raw5754step1Labels = mixedMoment B raw5754step2 raw5754step2Labels := by
      have hz : ∀ j, raw5754step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5754step2 = (fun i j => raw5754step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5754step2 raw5754step1; decide +kernel
      have hl : raw5754step2Labels = raw5754step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step1 raw5754step1Labels permutation14 hz
    mixedMoment B raw5754step2 raw5754step2Labels = mixedMoment B raw5754step3 raw5754step3Labels := by
      have ha : raw5754step3 = -raw5754step2 := by apply Matrix.ext; change ∀ i j, raw5754step3 i j = -(raw5754step2 i j); unfold raw5754step3 raw5754step2; decide +kernel
      have hl : raw5754step3Labels = raw5754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6788 raw6788Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw6788 raw6788Labels = mixedMoment B raw6788step0 raw6788step0Labels := by
      have hz : ∀ j, raw6788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6788step0 = (fun i j => raw6788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6788step0 raw6788; decide +kernel
      have hl : raw6788step0Labels = raw6788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6788 raw6788Labels permutation346 hz
    mixedMoment B raw6788step0 raw6788step0Labels = mixedMoment B raw6788step1 raw6788step1Labels := by
      have ha : raw6788step1 = (fun i j => raw6788step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6788step1 raw6788step0; decide +kernel
      have hl : raw6788step1Labels = raw6788step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6788step0 raw6788step0Labels permutation39 permutation2
    mixedMoment B raw6788step1 raw6788step1Labels = mixedMoment B raw6788step2 raw6788step2Labels := by
      have ha : raw6788step2 = -raw6788step1 := by apply Matrix.ext; change ∀ i j, raw6788step2 i j = -(raw6788step1 i j); unfold raw6788step2 raw6788step1; decide +kernel
      have hl : raw6788step2Labels = raw6788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3392 node3392Labels := by rfl

theorem canonical6790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6790 raw6790Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw6790 raw6790Labels = mixedMoment B raw6790step0 raw6790step0Labels := by
      have hz : ∀ j, raw6790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6790step0 = (fun i j => raw6790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6790step0 raw6790; decide +kernel
      have hl : raw6790step0Labels = raw6790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6790 raw6790Labels permutation346 hz
    mixedMoment B raw6790step0 raw6790step0Labels = mixedMoment B raw6790step1 raw6790step1Labels := by
      have hz : ∀ j, raw6790step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6790step1 = (fun i j => raw6790step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6790step1 raw6790step0; decide +kernel
      have hl : raw6790step1Labels = raw6790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6790step0 raw6790step0Labels permutation56 hz
    mixedMoment B raw6790step1 raw6790step1Labels = mixedMoment B raw6790step2 raw6790step2Labels := by
      have ha : raw6790step2 = (fun i j => raw6790step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6790step2 raw6790step1; decide +kernel
      have hl : raw6790step2Labels = raw6790step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6790step1 raw6790step1Labels permutation11 permutation4
    mixedMoment B raw6790step2 raw6790step2Labels = mixedMoment B raw6790step3 raw6790step3Labels := by
      have ha : raw6790step3 = -raw6790step2 := by apply Matrix.ext; change ∀ i j, raw6790step3 i j = -(raw6790step2 i j); unfold raw6790step3 raw6790step2; decide +kernel
      have hl : raw6790step3Labels = raw6790step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical6797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6797 raw6797Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw6797 raw6797Labels = mixedMoment B raw6797step0 raw6797step0Labels := by
      have hz : ∀ j, raw6797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6797step0 = (fun i j => raw6797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6797step0 raw6797; decide +kernel
      have hl : raw6797step0Labels = raw6797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6797 raw6797Labels permutation346 hz
    mixedMoment B raw6797step0 raw6797step0Labels = mixedMoment B raw6797step1 raw6797step1Labels := by
      have hz : ∀ j, raw6797step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6797step1 = (fun i j => raw6797step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6797step1 raw6797step0; decide +kernel
      have hl : raw6797step1Labels = raw6797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6797step0 raw6797step0Labels permutation56 hz
    mixedMoment B raw6797step1 raw6797step1Labels = mixedMoment B raw6797step2 raw6797step2Labels := by
      have ha : raw6797step2 = (fun i j => raw6797step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6797step2 raw6797step1; decide +kernel
      have hl : raw6797step2Labels = raw6797step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6797step1 raw6797step1Labels permutation11 permutation4
    mixedMoment B raw6797step2 raw6797step2Labels = mixedMoment B raw6797step3 raw6797step3Labels := by
      have ha : raw6797step3 = -raw6797step2 := by apply Matrix.ext; change ∀ i j, raw6797step3 i j = -(raw6797step2 i j); unfold raw6797step3 raw6797step2; decide +kernel
      have hl : raw6797step3Labels = raw6797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical6809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6809 raw6809Labels = mixedMoment B node3157 node3157Labels := by
  calc
    mixedMoment B raw6809 raw6809Labels = mixedMoment B raw6809step0 raw6809step0Labels := by
      have hz : ∀ j, raw6809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6809step0 = (fun i j => raw6809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6809step0 raw6809; decide +kernel
      have hl : raw6809step0Labels = raw6809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6809 raw6809Labels permutation346 hz
    mixedMoment B raw6809step0 raw6809step0Labels = mixedMoment B raw6809step1 raw6809step1Labels := by
      have ha : raw6809step1 = (fun i j => raw6809step0 (permutation81 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6809step1 raw6809step0; decide +kernel
      have hl : raw6809step1Labels = raw6809step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6809step0 raw6809step0Labels permutation81 permutation2
    mixedMoment B raw6809step1 raw6809step1Labels = mixedMoment B raw6809step2 raw6809step2Labels := by
      have ha : raw6809step2 = -raw6809step1 := by apply Matrix.ext; change ∀ i j, raw6809step2 i j = -(raw6809step1 i j); unfold raw6809step2 raw6809step1; decide +kernel
      have hl : raw6809step2Labels = raw6809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3157 node3157Labels := by rfl

theorem canonical6812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6812 raw6812Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw6812 raw6812Labels = mixedMoment B raw6812step0 raw6812step0Labels := by
      have hz : ∀ j, raw6812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6812step0 = (fun i j => raw6812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6812step0 raw6812; decide +kernel
      have hl : raw6812step0Labels = raw6812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6812 raw6812Labels permutation346 hz
    mixedMoment B raw6812step0 raw6812step0Labels = mixedMoment B raw6812step1 raw6812step1Labels := by
      have ha : raw6812step1 = (fun i j => raw6812step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6812step1 raw6812step0; decide +kernel
      have hl : raw6812step1Labels = raw6812step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6812step0 raw6812step0Labels permutation34 permutation4
    mixedMoment B raw6812step1 raw6812step1Labels = mixedMoment B raw6812step2 raw6812step2Labels := by
      have ha : raw6812step2 = -raw6812step1 := by apply Matrix.ext; change ∀ i j, raw6812step2 i j = -(raw6812step1 i j); unfold raw6812step2 raw6812step1; decide +kernel
      have hl : raw6812step2Labels = raw6812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3506 node3506Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7959 raw7959Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw7959 raw7959Labels = mixedMoment B raw7959step0 raw7959step0Labels := by
      have hz : ∀ j, raw7959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7959step0 = (fun i j => raw7959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7959step0 raw7959; decide +kernel
      have hl : raw7959step0Labels = raw7959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7959 raw7959Labels permutation346 hz
    mixedMoment B raw7959step0 raw7959step0Labels = mixedMoment B raw7959step1 raw7959step1Labels := by
      have hz : ∀ j, raw7959step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7959step1 = (fun i j => raw7959step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7959step1 raw7959step0; decide +kernel
      have hl : raw7959step1Labels = raw7959step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7959step0 raw7959step0Labels permutation56 hz
    mixedMoment B raw7959step1 raw7959step1Labels = mixedMoment B raw7959step2 raw7959step2Labels := by
      have ha : raw7959step2 = (fun i j => raw7959step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7959step2 raw7959step1; decide +kernel
      have hl : raw7959step2Labels = raw7959step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7959step1 raw7959step1Labels permutation9 permutation2
    mixedMoment B raw7959step2 raw7959step2Labels = mixedMoment B raw7959step3 raw7959step3Labels := by
      have ha : raw7959step3 = -raw7959step2 := by apply Matrix.ext; change ∀ i j, raw7959step3 i j = -(raw7959step2 i j); unfold raw7959step3 raw7959step2; decide +kernel
      have hl : raw7959step3Labels = raw7959step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical7965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7965 raw7965Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw7965 raw7965Labels = mixedMoment B raw7965step0 raw7965step0Labels := by
      have hz : ∀ j, raw7965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7965step0 = (fun i j => raw7965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7965step0 raw7965; decide +kernel
      have hl : raw7965step0Labels = raw7965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7965 raw7965Labels permutation346 hz
    mixedMoment B raw7965step0 raw7965step0Labels = mixedMoment B raw7965step1 raw7965step1Labels := by
      have ha : raw7965step1 = (fun i j => raw7965step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7965step1 raw7965step0; decide +kernel
      have hl : raw7965step1Labels = raw7965step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7965step0 raw7965step0Labels permutation44 permutation4
    mixedMoment B raw7965step1 raw7965step1Labels = mixedMoment B raw7965step2 raw7965step2Labels := by
      have ha : raw7965step2 = -raw7965step1 := by apply Matrix.ext; change ∀ i j, raw7965step2 i j = -(raw7965step1 i j); unfold raw7965step2 raw7965step1; decide +kernel
      have hl : raw7965step2Labels = raw7965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3580 node3580Labels := by rfl

theorem canonical7966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7966 raw7966Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw7966 raw7966Labels = mixedMoment B raw7966step0 raw7966step0Labels := by
      have hz : ∀ j, raw7966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7966step0 = (fun i j => raw7966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7966step0 raw7966; decide +kernel
      have hl : raw7966step0Labels = raw7966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7966 raw7966Labels permutation346 hz
    mixedMoment B raw7966step0 raw7966step0Labels = mixedMoment B raw7966step1 raw7966step1Labels := by
      have hz : ∀ j, raw7966step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7966step1 = (fun i j => raw7966step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7966step1 raw7966step0; decide +kernel
      have hl : raw7966step1Labels = raw7966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7966step0 raw7966step0Labels permutation56 hz
    mixedMoment B raw7966step1 raw7966step1Labels = mixedMoment B raw7966step2 raw7966step2Labels := by
      have ha : raw7966step2 = (fun i j => raw7966step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7966step2 raw7966step1; decide +kernel
      have hl : raw7966step2Labels = raw7966step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7966step1 raw7966step1Labels permutation10 permutation4
    mixedMoment B raw7966step2 raw7966step2Labels = mixedMoment B raw7966step3 raw7966step3Labels := by
      have ha : raw7966step3 = -raw7966step2 := by apply Matrix.ext; change ∀ i j, raw7966step3 i j = -(raw7966step2 i j); unfold raw7966step3 raw7966step2; decide +kernel
      have hl : raw7966step3Labels = raw7966step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8525 raw8525Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw8525 raw8525Labels = mixedMoment B raw8525step0 raw8525step0Labels := by
      have hz : ∀ j, raw8525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8525step0 = (fun i j => raw8525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8525step0 raw8525; decide +kernel
      have hl : raw8525step0Labels = raw8525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8525 raw8525Labels permutation346 hz
    mixedMoment B raw8525step0 raw8525step0Labels = mixedMoment B raw8525step1 raw8525step1Labels := by
      have hz : ∀ j, raw8525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8525step1 = (fun i j => raw8525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8525step1 raw8525step0; decide +kernel
      have hl : raw8525step1Labels = raw8525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8525step0 raw8525step0Labels permutation56 hz
    _ = mixedMoment B node3055 node3055Labels := by rfl

theorem canonical8526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8526 raw8526Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw8526 raw8526Labels = mixedMoment B raw8526step0 raw8526step0Labels := by
      have hz : ∀ j, raw8526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8526step0 = (fun i j => raw8526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8526step0 raw8526; decide +kernel
      have hl : raw8526step0Labels = raw8526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8526 raw8526Labels permutation346 hz
    mixedMoment B raw8526step0 raw8526step0Labels = mixedMoment B raw8526step1 raw8526step1Labels := by
      have ha : raw8526step1 = (fun i j => raw8526step0 (permutation98 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8526step1 raw8526step0; decide +kernel
      have hl : raw8526step1Labels = raw8526step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8526step0 raw8526step0Labels permutation98 permutation4
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical8528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8528 raw8528Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw8528 raw8528Labels = mixedMoment B raw8528step0 raw8528step0Labels := by
      have hz : ∀ j, raw8528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8528step0 = (fun i j => raw8528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8528step0 raw8528; decide +kernel
      have hl : raw8528step0Labels = raw8528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8528 raw8528Labels permutation346 hz
    mixedMoment B raw8528step0 raw8528step0Labels = mixedMoment B raw8528step1 raw8528step1Labels := by
      have hz : ∀ j, raw8528step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8528step1 = (fun i j => raw8528step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8528step1 raw8528step0; decide +kernel
      have hl : raw8528step1Labels = raw8528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8528step0 raw8528step0Labels permutation56 hz
    _ = mixedMoment B node3963 node3963Labels := by rfl

theorem canonical8529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8529 raw8529Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw8529 raw8529Labels = mixedMoment B raw8529step0 raw8529step0Labels := by
      have hz : ∀ j, raw8529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8529step0 = (fun i j => raw8529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8529step0 raw8529; decide +kernel
      have hl : raw8529step0Labels = raw8529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8529 raw8529Labels permutation346 hz
    mixedMoment B raw8529step0 raw8529step0Labels = mixedMoment B raw8529step1 raw8529step1Labels := by
      have hz : ∀ j, raw8529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8529step1 = (fun i j => raw8529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8529step1 raw8529step0; decide +kernel
      have hl : raw8529step1Labels = raw8529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8529step0 raw8529step0Labels permutation56 hz
    mixedMoment B raw8529step1 raw8529step1Labels = mixedMoment B raw8529step2 raw8529step2Labels := by
      have ha : raw8529step2 = (fun i j => raw8529step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8529step2 raw8529step1; decide +kernel
      have hl : raw8529step2Labels = raw8529step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8529step1 raw8529step1Labels permutation18 permutation4
    _ = mixedMoment B node3886 node3886Labels := by rfl

theorem canonical8531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8531 raw8531Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8531 raw8531Labels = mixedMoment B raw8531step0 raw8531step0Labels := by
      have hz : ∀ j, raw8531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8531step0 = (fun i j => raw8531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8531step0 raw8531; decide +kernel
      have hl : raw8531step0Labels = raw8531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8531 raw8531Labels permutation346 hz
    mixedMoment B raw8531step0 raw8531step0Labels = mixedMoment B raw8531step1 raw8531step1Labels := by
      have hz : ∀ j, raw8531step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8531step1 = (fun i j => raw8531step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8531step1 raw8531step0; decide +kernel
      have hl : raw8531step1Labels = raw8531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8531step0 raw8531step0Labels permutation56 hz
    mixedMoment B raw8531step1 raw8531step1Labels = mixedMoment B raw8531step2 raw8531step2Labels := by
      have ha : raw8531step2 = (fun i j => raw8531step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8531step2 raw8531step1; decide +kernel
      have hl : raw8531step2Labels = raw8531step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8531step1 raw8531step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical8535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8535 raw8535Labels = mixedMoment B node1375 node1375Labels := by
  calc
    mixedMoment B raw8535 raw8535Labels = mixedMoment B raw8535step0 raw8535step0Labels := by
      have hz : ∀ j, raw8535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8535step0 = (fun i j => raw8535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8535step0 raw8535; decide +kernel
      have hl : raw8535step0Labels = raw8535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8535 raw8535Labels permutation346 hz
    mixedMoment B raw8535step0 raw8535step0Labels = mixedMoment B raw8535step1 raw8535step1Labels := by
      have hz : ∀ j, raw8535step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8535step1 = (fun i j => raw8535step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8535step1 raw8535step0; decide +kernel
      have hl : raw8535step1Labels = raw8535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8535step0 raw8535step0Labels permutation56 hz
    mixedMoment B raw8535step1 raw8535step1Labels = mixedMoment B raw8535step2 raw8535step2Labels := by
      have ha : raw8535step2 = (fun i j => raw8535step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8535step2 raw8535step1; decide +kernel
      have hl : raw8535step2Labels = raw8535step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8535step1 raw8535step1Labels permutation9 permutation2
    _ = mixedMoment B node1375 node1375Labels := by rfl

theorem canonical8538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8538 raw8538Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw8538 raw8538Labels = mixedMoment B raw8538step0 raw8538step0Labels := by
      have hz : ∀ j, raw8538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8538step0 = (fun i j => raw8538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8538step0 raw8538; decide +kernel
      have hl : raw8538step0Labels = raw8538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8538 raw8538Labels permutation346 hz
    mixedMoment B raw8538step0 raw8538step0Labels = mixedMoment B raw8538step1 raw8538step1Labels := by
      have ha : raw8538step1 = (fun i j => raw8538step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8538step1 raw8538step0; decide +kernel
      have hl : raw8538step1Labels = raw8538step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8538step0 raw8538step0Labels permutation38 permutation2
    _ = mixedMoment B node2882 node2882Labels := by rfl

theorem canonical8539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8539 raw8539Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw8539 raw8539Labels = mixedMoment B raw8539step0 raw8539step0Labels := by
      have hz : ∀ j, raw8539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8539step0 = (fun i j => raw8539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8539step0 raw8539; decide +kernel
      have hl : raw8539step0Labels = raw8539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8539 raw8539Labels permutation346 hz
    mixedMoment B raw8539step0 raw8539step0Labels = mixedMoment B raw8539step1 raw8539step1Labels := by
      have ha : raw8539step1 = (fun i j => raw8539step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8539step1 raw8539step0; decide +kernel
      have hl : raw8539step1Labels = raw8539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8539step0 raw8539step0Labels permutation40 permutation2
    _ = mixedMoment B node3044 node3044Labels := by rfl

theorem canonical8541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8541 raw8541Labels = mixedMoment B node2975 node2975Labels := by
  calc
    mixedMoment B raw8541 raw8541Labels = mixedMoment B raw8541step0 raw8541step0Labels := by
      have ha : raw8541step0 = (fun i j => raw8541 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8541step0 raw8541; decide +kernel
      have hl : raw8541step0Labels = raw8541Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8541 raw8541Labels permutation158 permutation2
    _ = mixedMoment B node2975 node2975Labels := by rfl

theorem canonical8542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8542 raw8542Labels = mixedMoment B node2639 node2639Labels := by
  calc
    mixedMoment B raw8542 raw8542Labels = mixedMoment B raw8542step0 raw8542step0Labels := by
      have hz : ∀ j, raw8542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8542step0 = (fun i j => raw8542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8542step0 raw8542; decide +kernel
      have hl : raw8542step0Labels = raw8542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8542 raw8542Labels permutation346 hz
    mixedMoment B raw8542step0 raw8542step0Labels = mixedMoment B raw8542step1 raw8542step1Labels := by
      have ha : raw8542step1 = (fun i j => raw8542step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8542step1 raw8542step0; decide +kernel
      have hl : raw8542step1Labels = raw8542step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8542step0 raw8542step0Labels permutation101 permutation4
    _ = mixedMoment B node2639 node2639Labels := by rfl

theorem canonical8543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8543 raw8543Labels = mixedMoment B node2979 node2979Labels := by
  calc
    mixedMoment B raw8543 raw8543Labels = mixedMoment B raw8543step0 raw8543step0Labels := by
      have hz : ∀ j, raw8543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8543step0 = (fun i j => raw8543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8543step0 raw8543; decide +kernel
      have hl : raw8543step0Labels = raw8543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8543 raw8543Labels permutation346 hz
    mixedMoment B raw8543step0 raw8543step0Labels = mixedMoment B raw8543step1 raw8543step1Labels := by
      have ha : raw8543step1 = (fun i j => raw8543step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8543step1 raw8543step0; decide +kernel
      have hl : raw8543step1Labels = raw8543step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8543step0 raw8543step0Labels permutation33 permutation2
    _ = mixedMoment B node2979 node2979Labels := by rfl

theorem canonical8544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8544 raw8544Labels = mixedMoment B node2871 node2871Labels := by
  calc
    mixedMoment B raw8544 raw8544Labels = mixedMoment B raw8544step0 raw8544step0Labels := by
      have hz : ∀ j, raw8544 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8544step0 = (fun i j => raw8544 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8544step0 raw8544; decide +kernel
      have hl : raw8544step0Labels = raw8544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8544 raw8544Labels permutation346 hz
    mixedMoment B raw8544step0 raw8544step0Labels = mixedMoment B raw8544step1 raw8544step1Labels := by
      have ha : raw8544step1 = (fun i j => raw8544step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8544step1 raw8544step0; decide +kernel
      have hl : raw8544step1Labels = raw8544step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8544step0 raw8544step0Labels permutation151 permutation2
    mixedMoment B raw8544step1 raw8544step1Labels = mixedMoment B raw8544step2 raw8544step2Labels := by
      have ha : raw8544step2 = -raw8544step1 := by apply Matrix.ext; change ∀ i j, raw8544step2 i j = -(raw8544step1 i j); unfold raw8544step2 raw8544step1; decide +kernel
      have hl : raw8544step2Labels = raw8544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2871 node2871Labels := by rfl

theorem canonical8545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8545 raw8545Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw8545 raw8545Labels = mixedMoment B raw8545step0 raw8545step0Labels := by
      have hz : ∀ j, raw8545 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8545step0 = (fun i j => raw8545 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8545step0 raw8545; decide +kernel
      have hl : raw8545step0Labels = raw8545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8545 raw8545Labels permutation265 hz
    mixedMoment B raw8545step0 raw8545step0Labels = mixedMoment B raw8545step1 raw8545step1Labels := by
      have ha : raw8545step1 = (fun i j => raw8545step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8545step1 raw8545step0; decide +kernel
      have hl : raw8545step1Labels = raw8545step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8545step0 raw8545step0Labels permutation38 permutation2
    _ = mixedMoment B node2882 node2882Labels := by rfl

theorem canonical8546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8546 raw8546Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw8546 raw8546Labels = mixedMoment B raw8546step0 raw8546step0Labels := by
      have hz : ∀ j, raw8546 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8546step0 = (fun i j => raw8546 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8546step0 raw8546; decide +kernel
      have hl : raw8546step0Labels = raw8546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8546 raw8546Labels permutation346 hz
    mixedMoment B raw8546step0 raw8546step0Labels = mixedMoment B raw8546step1 raw8546step1Labels := by
      have hz : ∀ j, raw8546step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8546step1 = (fun i j => raw8546step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8546step1 raw8546step0; decide +kernel
      have hl : raw8546step1Labels = raw8546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8546step0 raw8546step0Labels permutation56 hz
    mixedMoment B raw8546step1 raw8546step1Labels = mixedMoment B raw8546step2 raw8546step2Labels := by
      have ha : raw8546step2 = (fun i j => raw8546step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8546step2 raw8546step1; decide +kernel
      have hl : raw8546step2Labels = raw8546step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8546step1 raw8546step1Labels permutation9 permutation2
    _ = mixedMoment B node2889 node2889Labels := by rfl

theorem canonical8547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8547 raw8547Labels = mixedMoment B node2886 node2886Labels := by
  calc
    mixedMoment B raw8547 raw8547Labels = mixedMoment B raw8547step0 raw8547step0Labels := by
      have hz : ∀ j, raw8547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8547step0 = (fun i j => raw8547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8547step0 raw8547; decide +kernel
      have hl : raw8547step0Labels = raw8547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8547 raw8547Labels permutation346 hz
    mixedMoment B raw8547step0 raw8547step0Labels = mixedMoment B raw8547step1 raw8547step1Labels := by
      have hz : ∀ j, raw8547step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8547step1 = (fun i j => raw8547step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8547step1 raw8547step0; decide +kernel
      have hl : raw8547step1Labels = raw8547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8547step0 raw8547step0Labels permutation56 hz
    _ = mixedMoment B node2886 node2886Labels := by rfl

theorem canonical8548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8548 raw8548Labels = mixedMoment B node2979 node2979Labels := by
  calc
    mixedMoment B raw8548 raw8548Labels = mixedMoment B raw8548step0 raw8548step0Labels := by
      have hz : ∀ j, raw8548 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8548step0 = (fun i j => raw8548 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8548step0 raw8548; decide +kernel
      have hl : raw8548step0Labels = raw8548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8548 raw8548Labels permutation265 hz
    mixedMoment B raw8548step0 raw8548step0Labels = mixedMoment B raw8548step1 raw8548step1Labels := by
      have ha : raw8548step1 = (fun i j => raw8548step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8548step1 raw8548step0; decide +kernel
      have hl : raw8548step1Labels = raw8548step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8548step0 raw8548step0Labels permutation33 permutation2
    _ = mixedMoment B node2979 node2979Labels := by rfl

theorem canonical8549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8549 raw8549Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw8549 raw8549Labels = mixedMoment B raw8549step0 raw8549step0Labels := by
      have hz : ∀ j, raw8549 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8549step0 = (fun i j => raw8549 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8549step0 raw8549; decide +kernel
      have hl : raw8549step0Labels = raw8549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8549 raw8549Labels permutation346 hz
    mixedMoment B raw8549step0 raw8549step0Labels = mixedMoment B raw8549step1 raw8549step1Labels := by
      have hz : ∀ j, raw8549step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8549step1 = (fun i j => raw8549step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8549step1 raw8549step0; decide +kernel
      have hl : raw8549step1Labels = raw8549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8549step0 raw8549step0Labels permutation56 hz
    mixedMoment B raw8549step1 raw8549step1Labels = mixedMoment B raw8549step2 raw8549step2Labels := by
      have ha : raw8549step2 = (fun i j => raw8549step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8549step2 raw8549step1; decide +kernel
      have hl : raw8549step2Labels = raw8549step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8549step1 raw8549step1Labels permutation9 permutation2
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical8550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8550 raw8550Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw8550 raw8550Labels = mixedMoment B raw8550step0 raw8550step0Labels := by
      have hz : ∀ j, raw8550 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8550step0 = (fun i j => raw8550 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8550step0 raw8550; decide +kernel
      have hl : raw8550step0Labels = raw8550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8550 raw8550Labels permutation265 hz
    mixedMoment B raw8550step0 raw8550step0Labels = mixedMoment B raw8550step1 raw8550step1Labels := by
      have ha : raw8550step1 = (fun i j => raw8550step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8550step1 raw8550step0; decide +kernel
      have hl : raw8550step1Labels = raw8550step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8550step0 raw8550step0Labels permutation40 permutation2
    _ = mixedMoment B node3044 node3044Labels := by rfl

theorem canonical8551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8551 raw8551Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw8551 raw8551Labels = mixedMoment B raw8551step0 raw8551step0Labels := by
      have hz : ∀ j, raw8551 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8551step0 = (fun i j => raw8551 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8551step0 raw8551; decide +kernel
      have hl : raw8551step0Labels = raw8551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8551 raw8551Labels permutation346 hz
    mixedMoment B raw8551step0 raw8551step0Labels = mixedMoment B raw8551step1 raw8551step1Labels := by
      have hz : ∀ j, raw8551step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8551step1 = (fun i j => raw8551step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8551step1 raw8551step0; decide +kernel
      have hl : raw8551step1Labels = raw8551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8551step0 raw8551step0Labels permutation56 hz
    mixedMoment B raw8551step1 raw8551step1Labels = mixedMoment B raw8551step2 raw8551step2Labels := by
      have ha : raw8551step2 = (fun i j => raw8551step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8551step2 raw8551step1; decide +kernel
      have hl : raw8551step2Labels = raw8551step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8551step1 raw8551step1Labels permutation18 permutation4
    _ = mixedMoment B node2643 node2643Labels := by rfl

theorem canonical8552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8552 raw8552Labels = mixedMoment B node3046 node3046Labels := by
  calc
    mixedMoment B raw8552 raw8552Labels = mixedMoment B raw8552step0 raw8552step0Labels := by
      have hz : ∀ j, raw8552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8552step0 = (fun i j => raw8552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8552step0 raw8552; decide +kernel
      have hl : raw8552step0Labels = raw8552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8552 raw8552Labels permutation346 hz
    mixedMoment B raw8552step0 raw8552step0Labels = mixedMoment B raw8552step1 raw8552step1Labels := by
      have hz : ∀ j, raw8552step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8552step1 = (fun i j => raw8552step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8552step1 raw8552step0; decide +kernel
      have hl : raw8552step1Labels = raw8552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8552step0 raw8552step0Labels permutation56 hz
    _ = mixedMoment B node3046 node3046Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8604 raw8604Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw8604 raw8604Labels = mixedMoment B raw8604step0 raw8604step0Labels := by
      have hz : ∀ j, raw8604 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8604step0 = (fun i j => raw8604 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8604step0 raw8604; decide +kernel
      have hl : raw8604step0Labels = raw8604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8604 raw8604Labels permutation265 hz
    mixedMoment B raw8604step0 raw8604step0Labels = mixedMoment B raw8604step1 raw8604step1Labels := by
      have ha : raw8604step1 = (fun i j => raw8604step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8604step1 raw8604step0; decide +kernel
      have hl : raw8604step1Labels = raw8604step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8604step0 raw8604step0Labels permutation39 permutation2
    mixedMoment B raw8604step1 raw8604step1Labels = mixedMoment B raw8604step2 raw8604step2Labels := by
      have ha : raw8604step2 = -raw8604step1 := by apply Matrix.ext; change ∀ i j, raw8604step2 i j = -(raw8604step1 i j); unfold raw8604step2 raw8604step1; decide +kernel
      have hl : raw8604step2Labels = raw8604step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3392 node3392Labels := by rfl

theorem canonical8605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8605 raw8605Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw8605 raw8605Labels = mixedMoment B raw8605step0 raw8605step0Labels := by
      have hz : ∀ j, raw8605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8605step0 = (fun i j => raw8605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8605step0 raw8605; decide +kernel
      have hl : raw8605step0Labels = raw8605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8605 raw8605Labels permutation346 hz
    mixedMoment B raw8605step0 raw8605step0Labels = mixedMoment B raw8605step1 raw8605step1Labels := by
      have hz : ∀ j, raw8605step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8605step1 = (fun i j => raw8605step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8605step1 raw8605step0; decide +kernel
      have hl : raw8605step1Labels = raw8605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8605step0 raw8605step0Labels permutation56 hz
    mixedMoment B raw8605step1 raw8605step1Labels = mixedMoment B raw8605step2 raw8605step2Labels := by
      have ha : raw8605step2 = (fun i j => raw8605step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8605step2 raw8605step1; decide +kernel
      have hl : raw8605step2Labels = raw8605step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8605step1 raw8605step1Labels permutation25 permutation2
    _ = mixedMoment B node2888 node2888Labels := by rfl

theorem canonical8606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8606 raw8606Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw8606 raw8606Labels = mixedMoment B raw8606step0 raw8606step0Labels := by
      have hz : ∀ j, raw8606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8606step0 = (fun i j => raw8606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8606step0 raw8606; decide +kernel
      have hl : raw8606step0Labels = raw8606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8606 raw8606Labels permutation346 hz
    mixedMoment B raw8606step0 raw8606step0Labels = mixedMoment B raw8606step1 raw8606step1Labels := by
      have hz : ∀ j, raw8606step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8606step1 = (fun i j => raw8606step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8606step1 raw8606step0; decide +kernel
      have hl : raw8606step1Labels = raw8606step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8606step0 raw8606step0Labels permutation56 hz
    mixedMoment B raw8606step1 raw8606step1Labels = mixedMoment B raw8606step2 raw8606step2Labels := by
      have ha : raw8606step2 = -raw8606step1 := by apply Matrix.ext; change ∀ i j, raw8606step2 i j = -(raw8606step1 i j); unfold raw8606step2 raw8606step1; decide +kernel
      have hl : raw8606step2Labels = raw8606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3397 node3397Labels := by rfl

theorem canonical8607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8607 raw8607Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw8607 raw8607Labels = mixedMoment B raw8607step0 raw8607step0Labels := by
      have hz : ∀ j, raw8607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8607step0 = (fun i j => raw8607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8607step0 raw8607; decide +kernel
      have hl : raw8607step0Labels = raw8607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8607 raw8607Labels permutation346 hz
    mixedMoment B raw8607step0 raw8607step0Labels = mixedMoment B raw8607step1 raw8607step1Labels := by
      have ha : raw8607step1 = (fun i j => raw8607step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8607step1 raw8607step0; decide +kernel
      have hl : raw8607step1Labels = raw8607step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8607step0 raw8607step0Labels permutation45 permutation4
    mixedMoment B raw8607step1 raw8607step1Labels = mixedMoment B raw8607step2 raw8607step2Labels := by
      have ha : raw8607step2 = -raw8607step1 := by apply Matrix.ext; change ∀ i j, raw8607step2 i j = -(raw8607step1 i j); unfold raw8607step2 raw8607step1; decide +kernel
      have hl : raw8607step2Labels = raw8607step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2108 node2108Labels := by rfl

theorem canonical8608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8608 raw8608Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw8608 raw8608Labels = mixedMoment B raw8608step0 raw8608step0Labels := by
      have hz : ∀ j, raw8608 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8608step0 = (fun i j => raw8608 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8608step0 raw8608; decide +kernel
      have hl : raw8608step0Labels = raw8608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8608 raw8608Labels permutation265 hz
    mixedMoment B raw8608step0 raw8608step0Labels = mixedMoment B raw8608step1 raw8608step1Labels := by
      have ha : raw8608step1 = (fun i j => raw8608step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8608step1 raw8608step0; decide +kernel
      have hl : raw8608step1Labels = raw8608step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8608step0 raw8608step0Labels permutation45 permutation4
    mixedMoment B raw8608step1 raw8608step1Labels = mixedMoment B raw8608step2 raw8608step2Labels := by
      have ha : raw8608step2 = -raw8608step1 := by apply Matrix.ext; change ∀ i j, raw8608step2 i j = -(raw8608step1 i j); unfold raw8608step2 raw8608step1; decide +kernel
      have hl : raw8608step2Labels = raw8608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2108 node2108Labels := by rfl

theorem canonical8609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8609 raw8609Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw8609 raw8609Labels = mixedMoment B raw8609step0 raw8609step0Labels := by
      have hz : ∀ j, raw8609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8609step0 = (fun i j => raw8609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8609step0 raw8609; decide +kernel
      have hl : raw8609step0Labels = raw8609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8609 raw8609Labels permutation346 hz
    mixedMoment B raw8609step0 raw8609step0Labels = mixedMoment B raw8609step1 raw8609step1Labels := by
      have hz : ∀ j, raw8609step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8609step1 = (fun i j => raw8609step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8609step1 raw8609step0; decide +kernel
      have hl : raw8609step1Labels = raw8609step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8609step0 raw8609step0Labels permutation56 hz
    mixedMoment B raw8609step1 raw8609step1Labels = mixedMoment B raw8609step2 raw8609step2Labels := by
      have ha : raw8609step2 = (fun i j => raw8609step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8609step2 raw8609step1; decide +kernel
      have hl : raw8609step2Labels = raw8609step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8609step1 raw8609step1Labels permutation11 permutation4
    mixedMoment B raw8609step2 raw8609step2Labels = mixedMoment B raw8609step3 raw8609step3Labels := by
      have ha : raw8609step3 = -raw8609step2 := by apply Matrix.ext; change ∀ i j, raw8609step3 i j = -(raw8609step2 i j); unfold raw8609step3 raw8609step2; decide +kernel
      have hl : raw8609step3Labels = raw8609step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2113 node2113Labels := by rfl

theorem canonical8610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8610 raw8610Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw8610 raw8610Labels = mixedMoment B raw8610step0 raw8610step0Labels := by
      have hz : ∀ j, raw8610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8610step0 = (fun i j => raw8610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8610step0 raw8610; decide +kernel
      have hl : raw8610step0Labels = raw8610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8610 raw8610Labels permutation346 hz
    mixedMoment B raw8610step0 raw8610step0Labels = mixedMoment B raw8610step1 raw8610step1Labels := by
      have hz : ∀ j, raw8610step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8610step1 = (fun i j => raw8610step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8610step1 raw8610step0; decide +kernel
      have hl : raw8610step1Labels = raw8610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8610step0 raw8610step0Labels permutation56 hz
    mixedMoment B raw8610step1 raw8610step1Labels = mixedMoment B raw8610step2 raw8610step2Labels := by
      have ha : raw8610step2 = (fun i j => raw8610step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8610step2 raw8610step1; decide +kernel
      have hl : raw8610step2Labels = raw8610step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8610step1 raw8610step1Labels permutation10 permutation4
    mixedMoment B raw8610step2 raw8610step2Labels = mixedMoment B raw8610step3 raw8610step3Labels := by
      have ha : raw8610step3 = -raw8610step2 := by apply Matrix.ext; change ∀ i j, raw8610step3 i j = -(raw8610step2 i j); unfold raw8610step3 raw8610step2; decide +kernel
      have hl : raw8610step3Labels = raw8610step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2115 node2115Labels := by rfl

theorem canonical8611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8611 raw8611Labels = mixedMoment B node3504 node3504Labels := by
  calc
    mixedMoment B raw8611 raw8611Labels = mixedMoment B raw8611step0 raw8611step0Labels := by
      have ha : raw8611step0 = (fun i j => raw8611 (permutation189 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8611step0 raw8611; decide +kernel
      have hl : raw8611step0Labels = raw8611Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8611 raw8611Labels permutation189 permutation4
    mixedMoment B raw8611step0 raw8611step0Labels = mixedMoment B raw8611step1 raw8611step1Labels := by
      have ha : raw8611step1 = -raw8611step0 := by apply Matrix.ext; change ∀ i j, raw8611step1 i j = -(raw8611step0 i j); unfold raw8611step1 raw8611step0; decide +kernel
      have hl : raw8611step1Labels = raw8611step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3504 node3504Labels := by rfl

theorem canonical8612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8612 raw8612Labels = mixedMoment B node2883 node2883Labels := by
  calc
    mixedMoment B raw8612 raw8612Labels = mixedMoment B raw8612step0 raw8612step0Labels := by
      have hz : ∀ j, raw8612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8612step0 = (fun i j => raw8612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8612step0 raw8612; decide +kernel
      have hl : raw8612step0Labels = raw8612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8612 raw8612Labels permutation346 hz
    mixedMoment B raw8612step0 raw8612step0Labels = mixedMoment B raw8612step1 raw8612step1Labels := by
      have ha : raw8612step1 = (fun i j => raw8612step0 (permutation124 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8612step1 raw8612step0; decide +kernel
      have hl : raw8612step1Labels = raw8612step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8612step0 raw8612step0Labels permutation124 permutation2
    _ = mixedMoment B node2883 node2883Labels := by rfl

theorem canonical8613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8613 raw8613Labels = mixedMoment B node3577 node3577Labels := by
  calc
    mixedMoment B raw8613 raw8613Labels = mixedMoment B raw8613step0 raw8613step0Labels := by
      have hz : ∀ j, raw8613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8613step0 = (fun i j => raw8613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8613step0 raw8613; decide +kernel
      have hl : raw8613step0Labels = raw8613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8613 raw8613Labels permutation346 hz
    mixedMoment B raw8613step0 raw8613step0Labels = mixedMoment B raw8613step1 raw8613step1Labels := by
      have ha : raw8613step1 = (fun i j => raw8613step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8613step1 raw8613step0; decide +kernel
      have hl : raw8613step1Labels = raw8613step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8613step0 raw8613step0Labels permutation48 permutation4
    mixedMoment B raw8613step1 raw8613step1Labels = mixedMoment B raw8613step2 raw8613step2Labels := by
      have ha : raw8613step2 = -raw8613step1 := by apply Matrix.ext; change ∀ i j, raw8613step2 i j = -(raw8613step1 i j); unfold raw8613step2 raw8613step1; decide +kernel
      have hl : raw8613step2Labels = raw8613step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3577 node3577Labels := by rfl

theorem canonical8614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8614 raw8614Labels = mixedMoment B node3157 node3157Labels := by
  calc
    mixedMoment B raw8614 raw8614Labels = mixedMoment B raw8614step0 raw8614step0Labels := by
      have hz : ∀ j, raw8614 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8614step0 = (fun i j => raw8614 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8614step0 raw8614; decide +kernel
      have hl : raw8614step0Labels = raw8614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8614 raw8614Labels permutation265 hz
    mixedMoment B raw8614step0 raw8614step0Labels = mixedMoment B raw8614step1 raw8614step1Labels := by
      have ha : raw8614step1 = (fun i j => raw8614step0 (permutation81 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8614step1 raw8614step0; decide +kernel
      have hl : raw8614step1Labels = raw8614step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8614step0 raw8614step0Labels permutation81 permutation2
    mixedMoment B raw8614step1 raw8614step1Labels = mixedMoment B raw8614step2 raw8614step2Labels := by
      have ha : raw8614step2 = -raw8614step1 := by apply Matrix.ext; change ∀ i j, raw8614step2 i j = -(raw8614step1 i j); unfold raw8614step2 raw8614step1; decide +kernel
      have hl : raw8614step2Labels = raw8614step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3157 node3157Labels := by rfl

theorem canonical8615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8615 raw8615Labels = mixedMoment B node2887 node2887Labels := by
  calc
    mixedMoment B raw8615 raw8615Labels = mixedMoment B raw8615step0 raw8615step0Labels := by
      have hz : ∀ j, raw8615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8615step0 = (fun i j => raw8615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8615step0 raw8615; decide +kernel
      have hl : raw8615step0Labels = raw8615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8615 raw8615Labels permutation346 hz
    mixedMoment B raw8615step0 raw8615step0Labels = mixedMoment B raw8615step1 raw8615step1Labels := by
      have hz : ∀ j, raw8615step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8615step1 = (fun i j => raw8615step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8615step1 raw8615step0; decide +kernel
      have hl : raw8615step1Labels = raw8615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8615step0 raw8615step0Labels permutation56 hz
    mixedMoment B raw8615step1 raw8615step1Labels = mixedMoment B raw8615step2 raw8615step2Labels := by
      have ha : raw8615step2 = (fun i j => raw8615step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8615step2 raw8615step1; decide +kernel
      have hl : raw8615step2Labels = raw8615step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8615step1 raw8615step1Labels permutation24 permutation2
    _ = mixedMoment B node2887 node2887Labels := by rfl

theorem canonical8616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8616 raw8616Labels = mixedMoment B node3161 node3161Labels := by
  calc
    mixedMoment B raw8616 raw8616Labels = mixedMoment B raw8616step0 raw8616step0Labels := by
      have hz : ∀ j, raw8616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8616step0 = (fun i j => raw8616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8616step0 raw8616; decide +kernel
      have hl : raw8616step0Labels = raw8616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8616 raw8616Labels permutation346 hz
    mixedMoment B raw8616step0 raw8616step0Labels = mixedMoment B raw8616step1 raw8616step1Labels := by
      have hz : ∀ j, raw8616step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8616step1 = (fun i j => raw8616step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8616step1 raw8616step0; decide +kernel
      have hl : raw8616step1Labels = raw8616step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8616step0 raw8616step0Labels permutation56 hz
    mixedMoment B raw8616step1 raw8616step1Labels = mixedMoment B raw8616step2 raw8616step2Labels := by
      have ha : raw8616step2 = (fun i j => raw8616step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8616step2 raw8616step1; decide +kernel
      have hl : raw8616step2Labels = raw8616step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8616step1 raw8616step1Labels permutation14 permutation2
    mixedMoment B raw8616step2 raw8616step2Labels = mixedMoment B raw8616step3 raw8616step3Labels := by
      have ha : raw8616step3 = -raw8616step2 := by apply Matrix.ext; change ∀ i j, raw8616step3 i j = -(raw8616step2 i j); unfold raw8616step3 raw8616step2; decide +kernel
      have hl : raw8616step3Labels = raw8616step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3161 node3161Labels := by rfl

theorem canonical8617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8617 raw8617Labels = mixedMoment B node2883 node2883Labels := by
  calc
    mixedMoment B raw8617 raw8617Labels = mixedMoment B raw8617step0 raw8617step0Labels := by
      have hz : ∀ j, raw8617 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8617step0 = (fun i j => raw8617 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8617step0 raw8617; decide +kernel
      have hl : raw8617step0Labels = raw8617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8617 raw8617Labels permutation265 hz
    mixedMoment B raw8617step0 raw8617step0Labels = mixedMoment B raw8617step1 raw8617step1Labels := by
      have ha : raw8617step1 = (fun i j => raw8617step0 (permutation124 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8617step1 raw8617step0; decide +kernel
      have hl : raw8617step1Labels = raw8617step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8617step0 raw8617step0Labels permutation124 permutation2
    _ = mixedMoment B node2883 node2883Labels := by rfl

theorem canonical8618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8618 raw8618Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw8618 raw8618Labels = mixedMoment B raw8618step0 raw8618step0Labels := by
      have hz : ∀ j, raw8618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8618step0 = (fun i j => raw8618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8618step0 raw8618; decide +kernel
      have hl : raw8618step0Labels = raw8618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8618 raw8618Labels permutation346 hz
    mixedMoment B raw8618step0 raw8618step0Labels = mixedMoment B raw8618step1 raw8618step1Labels := by
      have hz : ∀ j, raw8618step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8618step1 = (fun i j => raw8618step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8618step1 raw8618step0; decide +kernel
      have hl : raw8618step1Labels = raw8618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8618step0 raw8618step0Labels permutation56 hz
    mixedMoment B raw8618step1 raw8618step1Labels = mixedMoment B raw8618step2 raw8618step2Labels := by
      have ha : raw8618step2 = (fun i j => raw8618step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8618step2 raw8618step1; decide +kernel
      have hl : raw8618step2Labels = raw8618step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8618step1 raw8618step1Labels permutation24 permutation2
    _ = mixedMoment B node3056 node3056Labels := by rfl

theorem canonical8619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8619 raw8619Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw8619 raw8619Labels = mixedMoment B raw8619step0 raw8619step0Labels := by
      have hz : ∀ j, raw8619 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8619step0 = (fun i j => raw8619 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8619step0 raw8619; decide +kernel
      have hl : raw8619step0Labels = raw8619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8619 raw8619Labels permutation265 hz
    mixedMoment B raw8619step0 raw8619step0Labels = mixedMoment B raw8619step1 raw8619step1Labels := by
      have ha : raw8619step1 = (fun i j => raw8619step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8619step1 raw8619step0; decide +kernel
      have hl : raw8619step1Labels = raw8619step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8619step0 raw8619step0Labels permutation34 permutation4
    mixedMoment B raw8619step1 raw8619step1Labels = mixedMoment B raw8619step2 raw8619step2Labels := by
      have ha : raw8619step2 = -raw8619step1 := by apply Matrix.ext; change ∀ i j, raw8619step2 i j = -(raw8619step1 i j); unfold raw8619step2 raw8619step1; decide +kernel
      have hl : raw8619step2Labels = raw8619step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3506 node3506Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8770 raw8770Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw8770 raw8770Labels = mixedMoment B raw8770step0 raw8770step0Labels := by
      have hz : ∀ j, raw8770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8770step0 = (fun i j => raw8770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8770step0 raw8770; decide +kernel
      have hl : raw8770step0Labels = raw8770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8770 raw8770Labels permutation346 hz
    mixedMoment B raw8770step0 raw8770step0Labels = mixedMoment B raw8770step1 raw8770step1Labels := by
      have hz : ∀ j, raw8770step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8770step1 = (fun i j => raw8770step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8770step1 raw8770step0; decide +kernel
      have hl : raw8770step1Labels = raw8770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8770step0 raw8770step0Labels permutation56 hz
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical8771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8771 raw8771Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw8771 raw8771Labels = mixedMoment B raw8771step0 raw8771step0Labels := by
      have hz : ∀ j, raw8771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8771step0 = (fun i j => raw8771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8771step0 raw8771; decide +kernel
      have hl : raw8771step0Labels = raw8771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8771 raw8771Labels permutation346 hz
    mixedMoment B raw8771step0 raw8771step0Labels = mixedMoment B raw8771step1 raw8771step1Labels := by
      have ha : raw8771step1 = (fun i j => raw8771step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8771step1 raw8771step0; decide +kernel
      have hl : raw8771step1Labels = raw8771step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8771step0 raw8771step0Labels permutation151 permutation2
    mixedMoment B raw8771step1 raw8771step1Labels = mixedMoment B raw8771step2 raw8771step2Labels := by
      have ha : raw8771step2 = -raw8771step1 := by apply Matrix.ext; change ∀ i j, raw8771step2 i j = -(raw8771step1 i j); unfold raw8771step2 raw8771step1; decide +kernel
      have hl : raw8771step2Labels = raw8771step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical8772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8772 raw8772Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw8772 raw8772Labels = mixedMoment B raw8772step0 raw8772step0Labels := by
      have hz : ∀ j, raw8772 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8772step0 = (fun i j => raw8772 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8772step0 raw8772; decide +kernel
      have hl : raw8772step0Labels = raw8772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8772 raw8772Labels permutation265 hz
    mixedMoment B raw8772step0 raw8772step0Labels = mixedMoment B raw8772step1 raw8772step1Labels := by
      have ha : raw8772step1 = (fun i j => raw8772step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8772step1 raw8772step0; decide +kernel
      have hl : raw8772step1Labels = raw8772step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8772step0 raw8772step0Labels permutation151 permutation2
    mixedMoment B raw8772step1 raw8772step1Labels = mixedMoment B raw8772step2 raw8772step2Labels := by
      have ha : raw8772step2 = -raw8772step1 := by apply Matrix.ext; change ∀ i j, raw8772step2 i j = -(raw8772step1 i j); unfold raw8772step2 raw8772step1; decide +kernel
      have hl : raw8772step2Labels = raw8772step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical8773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8773 raw8773Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw8773 raw8773Labels = mixedMoment B raw8773step0 raw8773step0Labels := by
      have hz : ∀ j, raw8773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8773step0 = (fun i j => raw8773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8773step0 raw8773; decide +kernel
      have hl : raw8773step0Labels = raw8773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8773 raw8773Labels permutation346 hz
    mixedMoment B raw8773step0 raw8773step0Labels = mixedMoment B raw8773step1 raw8773step1Labels := by
      have hz : ∀ j, raw8773step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8773step1 = (fun i j => raw8773step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8773step1 raw8773step0; decide +kernel
      have hl : raw8773step1Labels = raw8773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8773step0 raw8773step0Labels permutation56 hz
    mixedMoment B raw8773step1 raw8773step1Labels = mixedMoment B raw8773step2 raw8773step2Labels := by
      have ha : raw8773step2 = (fun i j => raw8773step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8773step2 raw8773step1; decide +kernel
      have hl : raw8773step2Labels = raw8773step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8773step1 raw8773step1Labels permutation31 permutation2
    mixedMoment B raw8773step2 raw8773step2Labels = mixedMoment B raw8773step3 raw8773step3Labels := by
      have ha : raw8773step3 = -raw8773step2 := by apply Matrix.ext; change ∀ i j, raw8773step3 i j = -(raw8773step2 i j); unfold raw8773step3 raw8773step2; decide +kernel
      have hl : raw8773step3Labels = raw8773step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3817 node3817Labels := by rfl

theorem canonical8774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8774 raw8774Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw8774 raw8774Labels = mixedMoment B raw8774step0 raw8774step0Labels := by
      have hz : ∀ j, raw8774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8774step0 = (fun i j => raw8774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8774step0 raw8774; decide +kernel
      have hl : raw8774step0Labels = raw8774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8774 raw8774Labels permutation346 hz
    mixedMoment B raw8774step0 raw8774step0Labels = mixedMoment B raw8774step1 raw8774step1Labels := by
      have hz : ∀ j, raw8774step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8774step1 = (fun i j => raw8774step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8774step1 raw8774step0; decide +kernel
      have hl : raw8774step1Labels = raw8774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8774step0 raw8774step0Labels permutation56 hz
    mixedMoment B raw8774step1 raw8774step1Labels = mixedMoment B raw8774step2 raw8774step2Labels := by
      have ha : raw8774step2 = (fun i j => raw8774step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8774step2 raw8774step1; decide +kernel
      have hl : raw8774step2Labels = raw8774step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8774step1 raw8774step1Labels permutation31 permutation2
    mixedMoment B raw8774step2 raw8774step2Labels = mixedMoment B raw8774step3 raw8774step3Labels := by
      have ha : raw8774step3 = -raw8774step2 := by apply Matrix.ext; change ∀ i j, raw8774step3 i j = -(raw8774step2 i j); unfold raw8774step3 raw8774step2; decide +kernel
      have hl : raw8774step3Labels = raw8774step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical8775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8775 raw8775Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw8775 raw8775Labels = mixedMoment B raw8775step0 raw8775step0Labels := by
      have hz : ∀ j, raw8775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8775step0 = (fun i j => raw8775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8775step0 raw8775; decide +kernel
      have hl : raw8775step0Labels = raw8775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8775 raw8775Labels permutation346 hz
    mixedMoment B raw8775step0 raw8775step0Labels = mixedMoment B raw8775step1 raw8775step1Labels := by
      have hz : ∀ j, raw8775step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8775step1 = (fun i j => raw8775step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8775step1 raw8775step0; decide +kernel
      have hl : raw8775step1Labels = raw8775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8775step0 raw8775step0Labels permutation56 hz
    mixedMoment B raw8775step1 raw8775step1Labels = mixedMoment B raw8775step2 raw8775step2Labels := by
      have ha : raw8775step2 = (fun i j => raw8775step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8775step2 raw8775step1; decide +kernel
      have hl : raw8775step2Labels = raw8775step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8775step1 raw8775step1Labels permutation16 permutation4
    _ = mixedMoment B node3913 node3913Labels := by rfl

theorem canonical8776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8776 raw8776Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8776 raw8776Labels = mixedMoment B raw8776step0 raw8776step0Labels := by
      have hz : ∀ j, raw8776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8776step0 = (fun i j => raw8776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8776step0 raw8776; decide +kernel
      have hl : raw8776step0Labels = raw8776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8776 raw8776Labels permutation346 hz
    mixedMoment B raw8776step0 raw8776step0Labels = mixedMoment B raw8776step1 raw8776step1Labels := by
      have hz : ∀ j, raw8776step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8776step1 = (fun i j => raw8776step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8776step1 raw8776step0; decide +kernel
      have hl : raw8776step1Labels = raw8776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8776step0 raw8776step0Labels permutation56 hz
    mixedMoment B raw8776step1 raw8776step1Labels = mixedMoment B raw8776step2 raw8776step2Labels := by
      have ha : raw8776step2 = (fun i j => raw8776step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8776step2 raw8776step1; decide +kernel
      have hl : raw8776step2Labels = raw8776step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8776step1 raw8776step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical8777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8777 raw8777Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw8777 raw8777Labels = mixedMoment B raw8777step0 raw8777step0Labels := by
      have hz : ∀ j, raw8777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8777step0 = (fun i j => raw8777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8777step0 raw8777; decide +kernel
      have hl : raw8777step0Labels = raw8777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8777 raw8777Labels permutation346 hz
    mixedMoment B raw8777step0 raw8777step0Labels = mixedMoment B raw8777step1 raw8777step1Labels := by
      have ha : raw8777step1 = (fun i j => raw8777step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8777step1 raw8777step0; decide +kernel
      have hl : raw8777step1Labels = raw8777step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8777step0 raw8777step0Labels permutation38 permutation2
    _ = mixedMoment B node1367 node1367Labels := by rfl

theorem canonical8778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8778 raw8778Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw8778 raw8778Labels = mixedMoment B raw8778step0 raw8778step0Labels := by
      have hz : ∀ j, raw8778 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8778step0 = (fun i j => raw8778 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8778step0 raw8778; decide +kernel
      have hl : raw8778step0Labels = raw8778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8778 raw8778Labels permutation265 hz
    mixedMoment B raw8778step0 raw8778step0Labels = mixedMoment B raw8778step1 raw8778step1Labels := by
      have ha : raw8778step1 = (fun i j => raw8778step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8778step1 raw8778step0; decide +kernel
      have hl : raw8778step1Labels = raw8778step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8778step0 raw8778step0Labels permutation38 permutation2
    _ = mixedMoment B node1367 node1367Labels := by rfl

theorem canonical8779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8779 raw8779Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw8779 raw8779Labels = mixedMoment B raw8779step0 raw8779step0Labels := by
      have hz : ∀ j, raw8779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8779step0 = (fun i j => raw8779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8779step0 raw8779; decide +kernel
      have hl : raw8779step0Labels = raw8779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8779 raw8779Labels permutation346 hz
    mixedMoment B raw8779step0 raw8779step0Labels = mixedMoment B raw8779step1 raw8779step1Labels := by
      have hz : ∀ j, raw8779step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8779step1 = (fun i j => raw8779step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8779step1 raw8779step0; decide +kernel
      have hl : raw8779step1Labels = raw8779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8779step0 raw8779step0Labels permutation56 hz
    _ = mixedMoment B node1436 node1436Labels := by rfl

theorem canonical8780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8780 raw8780Labels = mixedMoment B node1375 node1375Labels := by
  calc
    mixedMoment B raw8780 raw8780Labels = mixedMoment B raw8780step0 raw8780step0Labels := by
      have hz : ∀ j, raw8780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8780step0 = (fun i j => raw8780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8780step0 raw8780; decide +kernel
      have hl : raw8780step0Labels = raw8780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8780 raw8780Labels permutation346 hz
    mixedMoment B raw8780step0 raw8780step0Labels = mixedMoment B raw8780step1 raw8780step1Labels := by
      have hz : ∀ j, raw8780step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8780step1 = (fun i j => raw8780step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8780step1 raw8780step0; decide +kernel
      have hl : raw8780step1Labels = raw8780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8780step0 raw8780step0Labels permutation56 hz
    _ = mixedMoment B node1375 node1375Labels := by rfl

theorem canonical8781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8781 raw8781Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw8781 raw8781Labels = mixedMoment B raw8781step0 raw8781step0Labels := by
      have hz : ∀ j, raw8781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8781step0 = (fun i j => raw8781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8781step0 raw8781; decide +kernel
      have hl : raw8781step0Labels = raw8781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8781 raw8781Labels permutation346 hz
    mixedMoment B raw8781step0 raw8781step0Labels = mixedMoment B raw8781step1 raw8781step1Labels := by
      have hz : ∀ j, raw8781step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8781step1 = (fun i j => raw8781step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8781step1 raw8781step0; decide +kernel
      have hl : raw8781step1Labels = raw8781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8781step0 raw8781step0Labels permutation56 hz
    _ = mixedMoment B node1372 node1372Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_NumericVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem integer_eval_numericVector (B : Fin 7 → Basis) (v : Integer.Sparse (Fin 3237)) :
    Integer.Sparse.eval v (numericVector B) =
      Integer.Sparse.eval (Integer.Sparse.reindex keyMap v) (mixedVector B) := by
  rw [Integer.Sparse.eval_reindex]
  rfl

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

theorem sound3907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3907 node3907Labels = Sparse.eval nodeValue3907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3907) = mixedMoment B node3907 node3907Labels := rfl
  simpa [nodeValue3907, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1367 node1367Labels = Sparse.eval nodeValue1367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1367) = mixedMoment B node1367 node1367Labels := rfl
  simpa [nodeValue1367, Sparse.eval] using hc.symm

theorem sound1372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1372 node1372Labels = Sparse.eval nodeValue1372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1372) = mixedMoment B node1372 node1372Labels := rfl
  simpa [nodeValue1372, Sparse.eval] using hc.symm

theorem sound1375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1375 node1375Labels = Sparse.eval nodeValue1375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1375) = mixedMoment B node1375 node1375Labels := rfl
  simpa [nodeValue1375, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1436 node1436Labels = Sparse.eval nodeValue1436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1436) = mixedMoment B node1436 node1436Labels := rfl
  simpa [nodeValue1436, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2108 node2108Labels = Sparse.eval nodeValue2108 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2108) = mixedMoment B node2108 node2108Labels := rfl
  simpa [nodeValue2108, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2113 node2113Labels = Sparse.eval nodeValue2113 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2113) = mixedMoment B node2113 node2113Labels := rfl
  simpa [nodeValue2113, Sparse.eval] using hc.symm

theorem sound2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2115 node2115Labels = Sparse.eval nodeValue2115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2115) = mixedMoment B node2115 node2115Labels := rfl
  simpa [nodeValue2115, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2639 node2639Labels = Sparse.eval nodeValue2639 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2639) = mixedMoment B node2639 node2639Labels := rfl
  simpa [nodeValue2639, Sparse.eval] using hc.symm

theorem sound2643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2643 node2643Labels = Sparse.eval nodeValue2643 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2643) = mixedMoment B node2643 node2643Labels := rfl
  simpa [nodeValue2643, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2871 node2871Labels = Sparse.eval nodeValue2871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2871) = mixedMoment B node2871 node2871Labels := rfl
  simpa [nodeValue2871, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2882 node2882Labels = Sparse.eval nodeValue2882 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2882) = mixedMoment B node2882 node2882Labels := rfl
  simpa [nodeValue2882, Sparse.eval] using hc.symm

theorem sound2883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2883 node2883Labels = Sparse.eval nodeValue2883 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2883) = mixedMoment B node2883 node2883Labels := rfl
  simpa [nodeValue2883, Sparse.eval] using hc.symm

theorem sound2886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2886 node2886Labels = Sparse.eval nodeValue2886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2886) = mixedMoment B node2886 node2886Labels := rfl
  simpa [nodeValue2886, Sparse.eval] using hc.symm

theorem sound2887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2887 node2887Labels = Sparse.eval nodeValue2887 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2887) = mixedMoment B node2887 node2887Labels := rfl
  simpa [nodeValue2887, Sparse.eval] using hc.symm

theorem sound2888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2888 node2888Labels = Sparse.eval nodeValue2888 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2888) = mixedMoment B node2888 node2888Labels := rfl
  simpa [nodeValue2888, Sparse.eval] using hc.symm

theorem sound2889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2889 node2889Labels = Sparse.eval nodeValue2889 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2889) = mixedMoment B node2889 node2889Labels := rfl
  simpa [nodeValue2889, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2975 node2975Labels = Sparse.eval nodeValue2975 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2975) = mixedMoment B node2975 node2975Labels := rfl
  simpa [nodeValue2975, Sparse.eval] using hc.symm

theorem sound2979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2979 node2979Labels = Sparse.eval nodeValue2979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2979) = mixedMoment B node2979 node2979Labels := rfl
  simpa [nodeValue2979, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3044 node3044Labels = Sparse.eval nodeValue3044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3044) = mixedMoment B node3044 node3044Labels := rfl
  simpa [nodeValue3044, Sparse.eval] using hc.symm

theorem sound3046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3046 node3046Labels = Sparse.eval nodeValue3046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3046) = mixedMoment B node3046 node3046Labels := rfl
  simpa [nodeValue3046, Sparse.eval] using hc.symm

theorem sound3055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3055 node3055Labels = Sparse.eval nodeValue3055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3055) = mixedMoment B node3055 node3055Labels := rfl
  simpa [nodeValue3055, Sparse.eval] using hc.symm

theorem sound3056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3056 node3056Labels = Sparse.eval nodeValue3056 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3056) = mixedMoment B node3056 node3056Labels := rfl
  simpa [nodeValue3056, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3157 node3157Labels = Sparse.eval nodeValue3157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3157) = mixedMoment B node3157 node3157Labels := rfl
  simpa [nodeValue3157, Sparse.eval] using hc.symm

theorem sound3161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3161 node3161Labels = Sparse.eval nodeValue3161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3161) = mixedMoment B node3161 node3161Labels := rfl
  simpa [nodeValue3161, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3392 node3392Labels = Sparse.eval nodeValue3392 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3392) = mixedMoment B node3392 node3392Labels := rfl
  simpa [nodeValue3392, Sparse.eval] using hc.symm

theorem sound3397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3397 node3397Labels = Sparse.eval nodeValue3397 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3397) = mixedMoment B node3397 node3397Labels := rfl
  simpa [nodeValue3397, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3504 node3504Labels = Sparse.eval nodeValue3504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3504) = mixedMoment B node3504 node3504Labels := rfl
  simpa [nodeValue3504, Sparse.eval] using hc.symm

theorem sound3506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3506 node3506Labels = Sparse.eval nodeValue3506 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3506) = mixedMoment B node3506 node3506Labels := rfl
  simpa [nodeValue3506, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3577 node3577Labels = Sparse.eval nodeValue3577 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3577) = mixedMoment B node3577 node3577Labels := rfl
  simpa [nodeValue3577, Sparse.eval] using hc.symm

theorem sound3580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3580 node3580Labels = Sparse.eval nodeValue3580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3580) = mixedMoment B node3580 node3580Labels := rfl
  simpa [nodeValue3580, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3584 node3584Labels = Sparse.eval nodeValue3584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3584) = mixedMoment B node3584 node3584Labels := rfl
  simpa [nodeValue3584, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3817 node3817Labels = 0 := by
  exact mixedMoment_order_one B hB node3817 node3817Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

theorem sound3817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3817 node3817Labels = Sparse.eval nodeValue3817 (mixedVector B) := by
  simpa only [nodeValue3817, Sparse.eval_nil] using zero3817 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

theorem sound3886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3886 node3886Labels = Sparse.eval nodeValue3886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3886) = mixedMoment B node3886 node3886Labels := rfl
  simpa [nodeValue3886, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3913 node3913Labels = Sparse.eval nodeValue3913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3913) = mixedMoment B node3913 node3913Labels := rfl
  simpa [nodeValue3913, Sparse.eval] using hc.symm

theorem sound3963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3963 node3963Labels = Sparse.eval nodeValue3963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3963) = mixedMoment B node3963 node3963Labels := rfl
  simpa [nodeValue3963, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources14
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm478 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA478 + difference 0 1) (sourceB478 + difference 1 0) sourceC478) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA478 + difference 0 1) (sourceB478 + difference 1 0) sourceC478) = raw8526 := by
      apply Matrix.ext; unfold tripleCharges sourceA478 sourceB478 sourceC478 difference raw8526; decide +kernel
    rw [ha]
    exact (canonical8526 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA478 + difference 1 1) (sourceB478 + difference 1 1) sourceC478) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA478 + difference 1 1) (sourceB478 + difference 1 1) sourceC478) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA478 sourceB478 sourceC478 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA478 + difference 2 1) (sourceB478 + difference 1 2) sourceC478) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2975) := by
    have ha : (tripleCharges (sourceA478 + difference 2 1) (sourceB478 + difference 1 2) sourceC478) = raw8541 := by
      apply Matrix.ext; unfold tripleCharges sourceA478 sourceB478 sourceC478 difference raw8541; decide +kernel
    rw [ha]
    exact (canonical8541 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA478 + difference 3 1) (sourceB478 + difference 1 3) sourceC478) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2639) := by
    have ha : (tripleCharges (sourceA478 + difference 3 1) (sourceB478 + difference 1 3) sourceC478) = raw8542 := by
      apply Matrix.ext; unfold tripleCharges sourceA478 sourceB478 sourceC478 difference raw8542; decide +kernel
    rw [ha]
    exact (canonical8542 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA478 + difference 4 1) (sourceB478 + difference 1 4) sourceC478) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA478 + difference 4 1) (sourceB478 + difference 1 4) sourceC478) = raw8543 := by
      apply Matrix.ext; unfold tripleCharges sourceA478 sourceB478 sourceC478 difference raw8543; decide +kernel
    rw [ha]
    exact (canonical8543 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA478 + difference 5 1) (sourceB478 + difference 1 5) sourceC478) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2871) := by
    have ha : (tripleCharges (sourceA478 + difference 5 1) (sourceB478 + difference 1 5) sourceC478) = raw8544 := by
      apply Matrix.ext; unfold tripleCharges sourceA478 sourceB478 sourceC478 difference raw8544; decide +kernel
    rw [ha]
    exact (canonical8544 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA478 + sourceB478) sourceC478) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA478 + sourceB478) sourceC478) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA478 sourceB478 sourceC478 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA478 sourceB478 sourceC478
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm478, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm479 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA479 + difference 0 3) (sourceB479 + difference 3 0) sourceC479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA479 + difference 0 3) (sourceB479 + difference 3 0) sourceC479) = raw8528 := by
      apply Matrix.ext; unfold tripleCharges sourceA479 sourceB479 sourceC479 difference raw8528; decide +kernel
    rw [ha]
    exact (canonical8528 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA479 + difference 1 3) (sourceB479 + difference 3 1) sourceC479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA479 + difference 1 3) (sourceB479 + difference 3 1) sourceC479) = raw8538 := by
      apply Matrix.ext; unfold tripleCharges sourceA479 sourceB479 sourceC479 difference raw8538; decide +kernel
    rw [ha]
    exact (canonical8538 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA479 + difference 2 3) (sourceB479 + difference 3 2) sourceC479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA479 + difference 2 3) (sourceB479 + difference 3 2) sourceC479) = raw8545 := by
      apply Matrix.ext; unfold tripleCharges sourceA479 sourceB479 sourceC479 difference raw8545; decide +kernel
    rw [ha]
    exact (canonical8545 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA479 + difference 3 3) (sourceB479 + difference 3 3) sourceC479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA479 + difference 3 3) (sourceB479 + difference 3 3) sourceC479) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA479 sourceB479 sourceC479 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA479 + difference 4 3) (sourceB479 + difference 3 4) sourceC479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA479 + difference 4 3) (sourceB479 + difference 3 4) sourceC479) = raw8546 := by
      apply Matrix.ext; unfold tripleCharges sourceA479 sourceB479 sourceC479 difference raw8546; decide +kernel
    rw [ha]
    exact (canonical8546 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA479 + difference 5 3) (sourceB479 + difference 3 5) sourceC479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2886) := by
    have ha : (tripleCharges (sourceA479 + difference 5 3) (sourceB479 + difference 3 5) sourceC479) = raw8547 := by
      apply Matrix.ext; unfold tripleCharges sourceA479 sourceB479 sourceC479 difference raw8547; decide +kernel
    rw [ha]
    exact (canonical8547 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA479 + sourceB479) sourceC479) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA479 + sourceB479) sourceC479) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA479 sourceB479 sourceC479 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA479 sourceB479 sourceC479
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm479, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources15
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm480 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA480 + difference 4 0) (sourceB480 + difference 0 4) sourceC480) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA480 + difference 4 0) (sourceB480 + difference 0 4) sourceC480) = raw8535 := by
      apply Matrix.ext; unfold tripleCharges sourceA480 sourceB480 sourceC480 difference raw8535; decide +kernel
    rw [ha]
    exact (canonical8535 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA480 + difference 4 1) (sourceB480 + difference 1 4) sourceC480) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA480 + difference 4 1) (sourceB480 + difference 1 4) sourceC480) = raw8543 := by
      apply Matrix.ext; unfold tripleCharges sourceA480 sourceB480 sourceC480 difference raw8543; decide +kernel
    rw [ha]
    exact (canonical8543 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA480 + difference 4 2) (sourceB480 + difference 2 4) sourceC480) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA480 + difference 4 2) (sourceB480 + difference 2 4) sourceC480) = raw8548 := by
      apply Matrix.ext; unfold tripleCharges sourceA480 sourceB480 sourceC480 difference raw8548; decide +kernel
    rw [ha]
    exact (canonical8548 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA480 + difference 4 3) (sourceB480 + difference 3 4) sourceC480) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA480 + difference 4 3) (sourceB480 + difference 3 4) sourceC480) = raw8546 := by
      apply Matrix.ext; unfold tripleCharges sourceA480 sourceB480 sourceC480 difference raw8546; decide +kernel
    rw [ha]
    exact (canonical8546 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA480 + difference 4 4) (sourceB480 + difference 4 4) sourceC480) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA480 + difference 4 4) (sourceB480 + difference 4 4) sourceC480) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA480 sourceB480 sourceC480 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA480 + difference 4 5) (sourceB480 + difference 5 4) sourceC480) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA480 + difference 4 5) (sourceB480 + difference 5 4) sourceC480) = raw8549 := by
      apply Matrix.ext; unfold tripleCharges sourceA480 sourceB480 sourceC480 difference raw8549; decide +kernel
    rw [ha]
    exact (canonical8549 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA480 + sourceB480) sourceC480) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA480 + sourceB480) sourceC480) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA480 sourceB480 sourceC480 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA480 sourceB480 sourceC480
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm480, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm481 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA481 + difference 0 4) (sourceB481 + difference 4 0) sourceC481) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA481 + difference 0 4) (sourceB481 + difference 4 0) sourceC481) = raw8529 := by
      apply Matrix.ext; unfold tripleCharges sourceA481 sourceB481 sourceC481 difference raw8529; decide +kernel
    rw [ha]
    exact (canonical8529 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA481 + difference 1 4) (sourceB481 + difference 4 1) sourceC481) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA481 + difference 1 4) (sourceB481 + difference 4 1) sourceC481) = raw8539 := by
      apply Matrix.ext; unfold tripleCharges sourceA481 sourceB481 sourceC481 difference raw8539; decide +kernel
    rw [ha]
    exact (canonical8539 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA481 + difference 2 4) (sourceB481 + difference 4 2) sourceC481) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA481 + difference 2 4) (sourceB481 + difference 4 2) sourceC481) = raw8550 := by
      apply Matrix.ext; unfold tripleCharges sourceA481 sourceB481 sourceC481 difference raw8550; decide +kernel
    rw [ha]
    exact (canonical8550 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA481 + difference 3 4) (sourceB481 + difference 4 3) sourceC481) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2643) := by
    have ha : (tripleCharges (sourceA481 + difference 3 4) (sourceB481 + difference 4 3) sourceC481) = raw8551 := by
      apply Matrix.ext; unfold tripleCharges sourceA481 sourceB481 sourceC481 difference raw8551; decide +kernel
    rw [ha]
    exact (canonical8551 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA481 + difference 4 4) (sourceB481 + difference 4 4) sourceC481) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA481 + difference 4 4) (sourceB481 + difference 4 4) sourceC481) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA481 sourceB481 sourceC481 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA481 + difference 5 4) (sourceB481 + difference 4 5) sourceC481) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3046) := by
    have ha : (tripleCharges (sourceA481 + difference 5 4) (sourceB481 + difference 4 5) sourceC481) = raw8552 := by
      apply Matrix.ext; unfold tripleCharges sourceA481 sourceB481 sourceC481 difference raw8552; decide +kernel
    rw [ha]
    exact (canonical8552 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA481 + sourceB481) sourceC481) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA481 + sourceB481) sourceC481) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA481 sourceB481 sourceC481 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA481 sourceB481 sourceC481
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm481, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm485 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA485 + difference 0 0) (sourceB485 + difference 0 0) sourceC485) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA485 + difference 0 0) (sourceB485 + difference 0 0) sourceC485) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA485 sourceB485 sourceC485 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA485 + difference 0 1) (sourceB485 + difference 1 0) sourceC485) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA485 + difference 0 1) (sourceB485 + difference 1 0) sourceC485) = raw6788 := by
      apply Matrix.ext; unfold tripleCharges sourceA485 sourceB485 sourceC485 difference raw6788; decide +kernel
    rw [ha]
    exact (canonical6788 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA485 + difference 0 2) (sourceB485 + difference 2 0) sourceC485) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA485 + difference 0 2) (sourceB485 + difference 2 0) sourceC485) = raw8604 := by
      apply Matrix.ext; unfold tripleCharges sourceA485 sourceB485 sourceC485 difference raw8604; decide +kernel
    rw [ha]
    exact (canonical8604 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA485 + difference 0 3) (sourceB485 + difference 3 0) sourceC485) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA485 + difference 0 3) (sourceB485 + difference 3 0) sourceC485) = raw7959 := by
      apply Matrix.ext; unfold tripleCharges sourceA485 sourceB485 sourceC485 difference raw7959; decide +kernel
    rw [ha]
    exact (canonical7959 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA485 + difference 0 4) (sourceB485 + difference 4 0) sourceC485) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA485 + difference 0 4) (sourceB485 + difference 4 0) sourceC485) = raw8605 := by
      apply Matrix.ext; unfold tripleCharges sourceA485 sourceB485 sourceC485 difference raw8605; decide +kernel
    rw [ha]
    exact (canonical8605 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA485 + difference 0 5) (sourceB485 + difference 5 0) sourceC485) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA485 + difference 0 5) (sourceB485 + difference 5 0) sourceC485) = raw8606 := by
      apply Matrix.ext; unfold tripleCharges sourceA485 sourceB485 sourceC485 difference raw8606; decide +kernel
    rw [ha]
    exact (canonical8606 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA485 + sourceB485) sourceC485) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA485 + sourceB485) sourceC485) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA485 sourceB485 sourceC485 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA485 sourceB485 sourceC485
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm485, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq486 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm486 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA486 + difference 0 0) (sourceB486 + difference 0 0) sourceC486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA486 + difference 0 0) (sourceB486 + difference 0 0) sourceC486) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA486 sourceB486 sourceC486 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA486 + difference 1 0) (sourceB486 + difference 0 1) sourceC486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA486 + difference 1 0) (sourceB486 + difference 0 1) sourceC486) = raw8607 := by
      apply Matrix.ext; unfold tripleCharges sourceA486 sourceB486 sourceC486 difference raw8607; decide +kernel
    rw [ha]
    exact (canonical8607 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA486 + difference 2 0) (sourceB486 + difference 0 2) sourceC486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA486 + difference 2 0) (sourceB486 + difference 0 2) sourceC486) = raw8608 := by
      apply Matrix.ext; unfold tripleCharges sourceA486 sourceB486 sourceC486 difference raw8608; decide +kernel
    rw [ha]
    exact (canonical8608 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA486 + difference 3 0) (sourceB486 + difference 0 3) sourceC486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA486 + difference 3 0) (sourceB486 + difference 0 3) sourceC486) = raw8609 := by
      apply Matrix.ext; unfold tripleCharges sourceA486 sourceB486 sourceC486 difference raw8609; decide +kernel
    rw [ha]
    exact (canonical8609 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA486 + difference 4 0) (sourceB486 + difference 0 4) sourceC486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA486 + difference 4 0) (sourceB486 + difference 0 4) sourceC486) = raw6790 := by
      apply Matrix.ext; unfold tripleCharges sourceA486 sourceB486 sourceC486 difference raw6790; decide +kernel
    rw [ha]
    exact (canonical6790 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA486 + difference 5 0) (sourceB486 + difference 0 5) sourceC486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA486 + difference 5 0) (sourceB486 + difference 0 5) sourceC486) = raw8610 := by
      apply Matrix.ext; unfold tripleCharges sourceA486 sourceB486 sourceC486 difference raw8610; decide +kernel
    rw [ha]
    exact (canonical8610 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA486 + sourceB486) sourceC486) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA486 + sourceB486) sourceC486) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA486 sourceB486 sourceC486 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA486 sourceB486 sourceC486
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm486, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq487 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm487 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA487 + difference 1 0) (sourceB487 + difference 0 1) sourceC487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA487 + difference 1 0) (sourceB487 + difference 0 1) sourceC487) = raw8607 := by
      apply Matrix.ext; unfold tripleCharges sourceA487 sourceB487 sourceC487 difference raw8607; decide +kernel
    rw [ha]
    exact (canonical8607 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA487 + difference 1 1) (sourceB487 + difference 1 1) sourceC487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA487 + difference 1 1) (sourceB487 + difference 1 1) sourceC487) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA487 sourceB487 sourceC487 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA487 + difference 1 2) (sourceB487 + difference 2 1) sourceC487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3504) := by
    have ha : (tripleCharges (sourceA487 + difference 1 2) (sourceB487 + difference 2 1) sourceC487) = raw8611 := by
      apply Matrix.ext; unfold tripleCharges sourceA487 sourceB487 sourceC487 difference raw8611; decide +kernel
    rw [ha]
    exact (canonical8611 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA487 + difference 1 3) (sourceB487 + difference 3 1) sourceC487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA487 + difference 1 3) (sourceB487 + difference 3 1) sourceC487) = raw7965 := by
      apply Matrix.ext; unfold tripleCharges sourceA487 sourceB487 sourceC487 difference raw7965; decide +kernel
    rw [ha]
    exact (canonical7965 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA487 + difference 1 4) (sourceB487 + difference 4 1) sourceC487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2883) := by
    have ha : (tripleCharges (sourceA487 + difference 1 4) (sourceB487 + difference 4 1) sourceC487) = raw8612 := by
      apply Matrix.ext; unfold tripleCharges sourceA487 sourceB487 sourceC487 difference raw8612; decide +kernel
    rw [ha]
    exact (canonical8612 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA487 + difference 1 5) (sourceB487 + difference 5 1) sourceC487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3577) := by
    have ha : (tripleCharges (sourceA487 + difference 1 5) (sourceB487 + difference 5 1) sourceC487) = raw8613 := by
      apply Matrix.ext; unfold tripleCharges sourceA487 sourceB487 sourceC487 difference raw8613; decide +kernel
    rw [ha]
    exact (canonical8613 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA487 + sourceB487) sourceC487) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA487 + sourceB487) sourceC487) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA487 sourceB487 sourceC487 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA487 sourceB487 sourceC487
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm487, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm488 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA488 + difference 3 0) (sourceB488 + difference 0 3) sourceC488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA488 + difference 3 0) (sourceB488 + difference 0 3) sourceC488) = raw8609 := by
      apply Matrix.ext; unfold tripleCharges sourceA488 sourceB488 sourceC488 difference raw8609; decide +kernel
    rw [ha]
    exact (canonical8609 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA488 + difference 3 1) (sourceB488 + difference 1 3) sourceC488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3157) := by
    have ha : (tripleCharges (sourceA488 + difference 3 1) (sourceB488 + difference 1 3) sourceC488) = raw6809 := by
      apply Matrix.ext; unfold tripleCharges sourceA488 sourceB488 sourceC488 difference raw6809; decide +kernel
    rw [ha]
    exact (canonical6809 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA488 + difference 3 2) (sourceB488 + difference 2 3) sourceC488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3157) := by
    have ha : (tripleCharges (sourceA488 + difference 3 2) (sourceB488 + difference 2 3) sourceC488) = raw8614 := by
      apply Matrix.ext; unfold tripleCharges sourceA488 sourceB488 sourceC488 difference raw8614; decide +kernel
    rw [ha]
    exact (canonical8614 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA488 + difference 3 3) (sourceB488 + difference 3 3) sourceC488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA488 + difference 3 3) (sourceB488 + difference 3 3) sourceC488) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA488 sourceB488 sourceC488 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA488 + difference 3 4) (sourceB488 + difference 4 3) sourceC488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2887) := by
    have ha : (tripleCharges (sourceA488 + difference 3 4) (sourceB488 + difference 4 3) sourceC488) = raw8615 := by
      apply Matrix.ext; unfold tripleCharges sourceA488 sourceB488 sourceC488 difference raw8615; decide +kernel
    rw [ha]
    exact (canonical8615 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA488 + difference 3 5) (sourceB488 + difference 5 3) sourceC488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3161) := by
    have ha : (tripleCharges (sourceA488 + difference 3 5) (sourceB488 + difference 5 3) sourceC488) = raw8616 := by
      apply Matrix.ext; unfold tripleCharges sourceA488 sourceB488 sourceC488 difference raw8616; decide +kernel
    rw [ha]
    exact (canonical8616 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA488 + sourceB488) sourceC488) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA488 + sourceB488) sourceC488) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA488 sourceB488 sourceC488 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA488 sourceB488 sourceC488
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm488, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm489 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA489 + difference 0 4) (sourceB489 + difference 4 0) sourceC489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA489 + difference 0 4) (sourceB489 + difference 4 0) sourceC489) = raw8605 := by
      apply Matrix.ext; unfold tripleCharges sourceA489 sourceB489 sourceC489 difference raw8605; decide +kernel
    rw [ha]
    exact (canonical8605 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA489 + difference 1 4) (sourceB489 + difference 4 1) sourceC489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2883) := by
    have ha : (tripleCharges (sourceA489 + difference 1 4) (sourceB489 + difference 4 1) sourceC489) = raw8612 := by
      apply Matrix.ext; unfold tripleCharges sourceA489 sourceB489 sourceC489 difference raw8612; decide +kernel
    rw [ha]
    exact (canonical8612 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA489 + difference 2 4) (sourceB489 + difference 4 2) sourceC489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2883) := by
    have ha : (tripleCharges (sourceA489 + difference 2 4) (sourceB489 + difference 4 2) sourceC489) = raw8617 := by
      apply Matrix.ext; unfold tripleCharges sourceA489 sourceB489 sourceC489 difference raw8617; decide +kernel
    rw [ha]
    exact (canonical8617 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA489 + difference 3 4) (sourceB489 + difference 4 3) sourceC489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2887) := by
    have ha : (tripleCharges (sourceA489 + difference 3 4) (sourceB489 + difference 4 3) sourceC489) = raw8615 := by
      apply Matrix.ext; unfold tripleCharges sourceA489 sourceB489 sourceC489 difference raw8615; decide +kernel
    rw [ha]
    exact (canonical8615 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA489 + difference 4 4) (sourceB489 + difference 4 4) sourceC489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA489 + difference 4 4) (sourceB489 + difference 4 4) sourceC489) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA489 sourceB489 sourceC489 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA489 + difference 5 4) (sourceB489 + difference 4 5) sourceC489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA489 + difference 5 4) (sourceB489 + difference 4 5) sourceC489) = raw8618 := by
      apply Matrix.ext; unfold tripleCharges sourceA489 sourceB489 sourceC489 difference raw8618; decide +kernel
    rw [ha]
    exact (canonical8618 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA489 + sourceB489) sourceC489) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA489 + sourceB489) sourceC489) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA489 sourceB489 sourceC489 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA489 sourceB489 sourceC489
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm489, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm490 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA490 + difference 5 0) (sourceB490 + difference 0 5) sourceC490) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA490 + difference 5 0) (sourceB490 + difference 0 5) sourceC490) = raw8610 := by
      apply Matrix.ext; unfold tripleCharges sourceA490 sourceB490 sourceC490 difference raw8610; decide +kernel
    rw [ha]
    exact (canonical8610 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA490 + difference 5 1) (sourceB490 + difference 1 5) sourceC490) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA490 + difference 5 1) (sourceB490 + difference 1 5) sourceC490) = raw6812 := by
      apply Matrix.ext; unfold tripleCharges sourceA490 sourceB490 sourceC490 difference raw6812; decide +kernel
    rw [ha]
    exact (canonical6812 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA490 + difference 5 2) (sourceB490 + difference 2 5) sourceC490) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA490 + difference 5 2) (sourceB490 + difference 2 5) sourceC490) = raw8619 := by
      apply Matrix.ext; unfold tripleCharges sourceA490 sourceB490 sourceC490 difference raw8619; decide +kernel
    rw [ha]
    exact (canonical8619 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA490 + difference 5 3) (sourceB490 + difference 3 5) sourceC490) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA490 + difference 5 3) (sourceB490 + difference 3 5) sourceC490) = raw7966 := by
      apply Matrix.ext; unfold tripleCharges sourceA490 sourceB490 sourceC490 difference raw7966; decide +kernel
    rw [ha]
    exact (canonical7966 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA490 + difference 5 4) (sourceB490 + difference 4 5) sourceC490) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA490 + difference 5 4) (sourceB490 + difference 4 5) sourceC490) = raw8618 := by
      apply Matrix.ext; unfold tripleCharges sourceA490 sourceB490 sourceC490 difference raw8618; decide +kernel
    rw [ha]
    exact (canonical8618 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA490 + difference 5 5) (sourceB490 + difference 5 5) sourceC490) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA490 + difference 5 5) (sourceB490 + difference 5 5) sourceC490) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA490 sourceB490 sourceC490 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA490 + sourceB490) sourceC490) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA490 + sourceB490) sourceC490) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA490 sourceB490 sourceC490 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA490 sourceB490 sourceC490
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm490, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm496 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA496 + difference 0 0) (sourceB496 + difference 0 0) sourceC496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA496 + difference 0 0) (sourceB496 + difference 0 0) sourceC496) = raw8770 := by
      apply Matrix.ext; unfold tripleCharges sourceA496 sourceB496 sourceC496 difference raw8770; decide +kernel
    rw [ha]
    exact (canonical8770 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA496 + difference 0 1) (sourceB496 + difference 1 0) sourceC496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA496 + difference 0 1) (sourceB496 + difference 1 0) sourceC496) = raw8771 := by
      apply Matrix.ext; unfold tripleCharges sourceA496 sourceB496 sourceC496 difference raw8771; decide +kernel
    rw [ha]
    exact (canonical8771 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA496 + difference 0 2) (sourceB496 + difference 2 0) sourceC496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA496 + difference 0 2) (sourceB496 + difference 2 0) sourceC496) = raw8772 := by
      apply Matrix.ext; unfold tripleCharges sourceA496 sourceB496 sourceC496 difference raw8772; decide +kernel
    rw [ha]
    exact (canonical8772 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA496 + difference 0 3) (sourceB496 + difference 3 0) sourceC496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA496 + difference 0 3) (sourceB496 + difference 3 0) sourceC496) = raw8773 := by
      apply Matrix.ext; unfold tripleCharges sourceA496 sourceB496 sourceC496 difference raw8773; decide +kernel
    rw [ha]
    exact (canonical8773 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA496 + difference 0 4) (sourceB496 + difference 4 0) sourceC496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA496 + difference 0 4) (sourceB496 + difference 4 0) sourceC496) = raw8774 := by
      apply Matrix.ext; unfold tripleCharges sourceA496 sourceB496 sourceC496 difference raw8774; decide +kernel
    rw [ha]
    exact (canonical8774 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA496 + difference 0 5) (sourceB496 + difference 5 0) sourceC496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA496 + difference 0 5) (sourceB496 + difference 5 0) sourceC496) = raw8775 := by
      apply Matrix.ext; unfold tripleCharges sourceA496 sourceB496 sourceC496 difference raw8775; decide +kernel
    rw [ha]
    exact (canonical8775 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA496 + sourceB496) sourceC496) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA496 + sourceB496) sourceC496) = raw8776 := by
      apply Matrix.ext; unfold doubleCharges sourceA496 sourceB496 sourceC496 raw8776; decide +kernel
    rw [ha]
    exact (canonical8776 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA496 sourceB496 sourceC496
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm496, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq497 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm497 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA497 + difference 0 0) (sourceB497 + difference 0 0) sourceC497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA497 + difference 0 0) (sourceB497 + difference 0 0) sourceC497) = raw8770 := by
      apply Matrix.ext; unfold tripleCharges sourceA497 sourceB497 sourceC497 difference raw8770; decide +kernel
    rw [ha]
    exact (canonical8770 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA497 + difference 1 0) (sourceB497 + difference 0 1) sourceC497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA497 + difference 1 0) (sourceB497 + difference 0 1) sourceC497) = raw8777 := by
      apply Matrix.ext; unfold tripleCharges sourceA497 sourceB497 sourceC497 difference raw8777; decide +kernel
    rw [ha]
    exact (canonical8777 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA497 + difference 2 0) (sourceB497 + difference 0 2) sourceC497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA497 + difference 2 0) (sourceB497 + difference 0 2) sourceC497) = raw8778 := by
      apply Matrix.ext; unfold tripleCharges sourceA497 sourceB497 sourceC497 difference raw8778; decide +kernel
    rw [ha]
    exact (canonical8778 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA497 + difference 3 0) (sourceB497 + difference 0 3) sourceC497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA497 + difference 3 0) (sourceB497 + difference 0 3) sourceC497) = raw8779 := by
      apply Matrix.ext; unfold tripleCharges sourceA497 sourceB497 sourceC497 difference raw8779; decide +kernel
    rw [ha]
    exact (canonical8779 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA497 + difference 4 0) (sourceB497 + difference 0 4) sourceC497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA497 + difference 4 0) (sourceB497 + difference 0 4) sourceC497) = raw8780 := by
      apply Matrix.ext; unfold tripleCharges sourceA497 sourceB497 sourceC497 difference raw8780; decide +kernel
    rw [ha]
    exact (canonical8780 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA497 + difference 5 0) (sourceB497 + difference 0 5) sourceC497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA497 + difference 5 0) (sourceB497 + difference 0 5) sourceC497) = raw8781 := by
      apply Matrix.ext; unfold tripleCharges sourceA497 sourceB497 sourceC497 difference raw8781; decide +kernel
    rw [ha]
    exact (canonical8781 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA497 + sourceB497) sourceC497) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA497 + sourceB497) sourceC497) = raw8776 := by
      apply Matrix.ext; unfold doubleCharges sourceA497 sourceB497 sourceC497 raw8776; decide +kernel
    rw [ha]
    exact (canonical8776 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA497 sourceB497 sourceC497
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm497, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck400 : Integer.Sparse.reindex keyMap MixedData.row400 = numericRow400 := by decide +kernel

theorem numericCheck400 (x : Master → ℝ) : Integer.Sparse.eval numericRow400 x =
    (1 : ℝ) * reducedSource400 x := by
  norm_num [numericRow400, reducedSource400, Integer.Sparse.eval, Sparse.eval, nodeValue2639, nodeValue2871, nodeValue2975, nodeValue2979, nodeValue3055, nodeValue3884, nodeValue4092]

theorem reindexCheck401 : Integer.Sparse.reindex keyMap MixedData.row401 = numericRow401 := by decide +kernel

theorem numericCheck401 (x : Master → ℝ) : Integer.Sparse.eval numericRow401 x =
    (1 : ℝ) * reducedSource401 x := by
  norm_num [numericRow401, reducedSource401, Integer.Sparse.eval, Sparse.eval, nodeValue2882, nodeValue2886, nodeValue2889, nodeValue3055, nodeValue3963, nodeValue4092]

theorem reindexCheck402 : Integer.Sparse.reindex keyMap MixedData.row402 = numericRow402 := by decide +kernel

theorem numericCheck402 (x : Master → ℝ) : Integer.Sparse.eval numericRow402 x =
    (1 : ℝ) * reducedSource402 x := by
  norm_num [numericRow402, reducedSource402, Integer.Sparse.eval, Sparse.eval, nodeValue1375, nodeValue2889, nodeValue2979, nodeValue3054, nodeValue3055, nodeValue4092]

theorem reindexCheck403 : Integer.Sparse.reindex keyMap MixedData.row403 = numericRow403 := by decide +kernel

theorem numericCheck403 (x : Master → ℝ) : Integer.Sparse.eval numericRow403 x =
    (1 : ℝ) * reducedSource403 x := by
  norm_num [numericRow403, reducedSource403, Integer.Sparse.eval, Sparse.eval, nodeValue2643, nodeValue3044, nodeValue3046, nodeValue3055, nodeValue3886, nodeValue4092]

theorem reindexCheck405 : Integer.Sparse.reindex keyMap MixedData.row405 = numericRow405 := by decide +kernel

theorem numericCheck405 (x : Master → ℝ) : Integer.Sparse.eval numericRow405 x =
    (1 : ℝ) * reducedSource405 x := by
  norm_num [numericRow405, reducedSource405, Integer.Sparse.eval, Sparse.eval, nodeValue2888, nodeValue3392, nodeValue3397, nodeValue3548, nodeValue3584, nodeValue4084]

theorem reindexCheck406 : Integer.Sparse.reindex keyMap MixedData.row406 = numericRow406 := by decide +kernel

theorem numericCheck406 (x : Master → ℝ) : Integer.Sparse.eval numericRow406 x =
    (1 : ℝ) * reducedSource406 x := by
  norm_num [numericRow406, reducedSource406, Integer.Sparse.eval, Sparse.eval, nodeValue2108, nodeValue2113, nodeValue2115, nodeValue2266, nodeValue3584, nodeValue4084]

theorem reindexCheck407 : Integer.Sparse.reindex keyMap MixedData.row407 = numericRow407 := by decide +kernel

theorem numericCheck407 (x : Master → ℝ) : Integer.Sparse.eval numericRow407 x =
    (1 : ℝ) * reducedSource407 x := by
  norm_num [numericRow407, reducedSource407, Integer.Sparse.eval, Sparse.eval, nodeValue2108, nodeValue2883, nodeValue3504, nodeValue3577, nodeValue3580, nodeValue3584, nodeValue4084]

theorem reindexCheck408 : Integer.Sparse.reindex keyMap MixedData.row408 = numericRow408 := by decide +kernel

theorem numericCheck408 (x : Master → ℝ) : Integer.Sparse.eval numericRow408 x =
    (1 : ℝ) * reducedSource408 x := by
  norm_num [numericRow408, reducedSource408, Integer.Sparse.eval, Sparse.eval, nodeValue2113, nodeValue2887, nodeValue3157, nodeValue3161, nodeValue3584, nodeValue4084]

theorem reindexCheck409 : Integer.Sparse.reindex keyMap MixedData.row409 = numericRow409 := by decide +kernel

theorem numericCheck409 (x : Master → ℝ) : Integer.Sparse.eval numericRow409 x =
    (1 : ℝ) * reducedSource409 x := by
  norm_num [numericRow409, reducedSource409, Integer.Sparse.eval, Sparse.eval, nodeValue2883, nodeValue2887, nodeValue2888, nodeValue3056, nodeValue3584, nodeValue4084]

theorem reindexCheck410 : Integer.Sparse.reindex keyMap MixedData.row410 = numericRow410 := by decide +kernel

theorem numericCheck410 (x : Master → ℝ) : Integer.Sparse.eval numericRow410 x =
    (1 : ℝ) * reducedSource410 x := by
  norm_num [numericRow410, reducedSource410, Integer.Sparse.eval, Sparse.eval, nodeValue2115, nodeValue3056, nodeValue3506, nodeValue3582, nodeValue3584, nodeValue4084]

theorem reindexCheck414 : Integer.Sparse.reindex keyMap MixedData.row414 = numericRow414 := by decide +kernel

theorem numericCheck414 (x : Master → ℝ) : Integer.Sparse.eval numericRow414 x =
    (1 : ℝ) * reducedSource414 x := by
  norm_num [numericRow414, reducedSource414, Integer.Sparse.eval, Sparse.eval, nodeValue3054, nodeValue3813, nodeValue3817, nodeValue3907, nodeValue3913, nodeValue4092]

theorem reindexCheck415 : Integer.Sparse.reindex keyMap MixedData.row415 = numericRow415 := by decide +kernel

theorem numericCheck415 (x : Master → ℝ) : Integer.Sparse.eval numericRow415 x =
    (1 : ℝ) * reducedSource415 x := by
  norm_num [numericRow415, reducedSource415, Integer.Sparse.eval, Sparse.eval, nodeValue1367, nodeValue1372, nodeValue1375, nodeValue1436, nodeValue3054, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero400 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource400 (mixedVector B) = 0 := by
  have h2639 : mixedVector B (Sum.inr 2639) = Sparse.eval nodeValue2639 (mixedVector B) := by
    change mixedMoment B node2639 node2639Labels = _
    exact sound2639 B hB hF
  have h2871 : mixedVector B (Sum.inr 2871) = Sparse.eval nodeValue2871 (mixedVector B) := by
    change mixedMoment B node2871 node2871Labels = _
    exact sound2871 B hB hF
  have h2975 : mixedVector B (Sum.inr 2975) = Sparse.eval nodeValue2975 (mixedVector B) := by
    change mixedMoment B node2975 node2975Labels = _
    exact sound2975 B hB hF
  have h2979 : mixedVector B (Sum.inr 2979) = Sparse.eval nodeValue2979 (mixedVector B) := by
    change mixedMoment B node2979 node2979Labels = _
    exact sound2979 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm478, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2639, h2871, h2975, h2979, h3055, h3884, h4092, reducedSource400] using sourceEq478 B hB

theorem rowSound400 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row400 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck400, numericCheck400, reducedZero400 B hB hF, mul_zero]

theorem reducedZero401 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource401 (mixedVector B) = 0 := by
  have h2882 : mixedVector B (Sum.inr 2882) = Sparse.eval nodeValue2882 (mixedVector B) := by
    change mixedMoment B node2882 node2882Labels = _
    exact sound2882 B hB hF
  have h2886 : mixedVector B (Sum.inr 2886) = Sparse.eval nodeValue2886 (mixedVector B) := by
    change mixedMoment B node2886 node2886Labels = _
    exact sound2886 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3963 : mixedVector B (Sum.inr 3963) = Sparse.eval nodeValue3963 (mixedVector B) := by
    change mixedMoment B node3963 node3963Labels = _
    exact sound3963 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm479, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2882, h2886, h2889, h3055, h3963, h4092, reducedSource401] using sourceEq479 B hB

theorem rowSound401 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row401 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck401, numericCheck401, reducedZero401 B hB hF, mul_zero]

theorem reducedZero402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource402 (mixedVector B) = 0 := by
  have h1375 : mixedVector B (Sum.inr 1375) = Sparse.eval nodeValue1375 (mixedVector B) := by
    change mixedMoment B node1375 node1375Labels = _
    exact sound1375 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h2979 : mixedVector B (Sum.inr 2979) = Sparse.eval nodeValue2979 (mixedVector B) := by
    change mixedMoment B node2979 node2979Labels = _
    exact sound2979 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm480, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1375, h2889, h2979, h3054, h3055, h4092, reducedSource402] using sourceEq480 B hB

theorem rowSound402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row402 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck402, numericCheck402, reducedZero402 B hB hF, mul_zero]

theorem reducedZero403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource403 (mixedVector B) = 0 := by
  have h2643 : mixedVector B (Sum.inr 2643) = Sparse.eval nodeValue2643 (mixedVector B) := by
    change mixedMoment B node2643 node2643Labels = _
    exact sound2643 B hB hF
  have h3044 : mixedVector B (Sum.inr 3044) = Sparse.eval nodeValue3044 (mixedVector B) := by
    change mixedMoment B node3044 node3044Labels = _
    exact sound3044 B hB hF
  have h3046 : mixedVector B (Sum.inr 3046) = Sparse.eval nodeValue3046 (mixedVector B) := by
    change mixedMoment B node3046 node3046Labels = _
    exact sound3046 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm481, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2643, h3044, h3046, h3055, h3886, h4092, reducedSource403] using sourceEq481 B hB

theorem rowSound403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row403 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck403, numericCheck403, reducedZero403 B hB hF, mul_zero]

theorem reducedZero405 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource405 (mixedVector B) = 0 := by
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h3392 : mixedVector B (Sum.inr 3392) = Sparse.eval nodeValue3392 (mixedVector B) := by
    change mixedMoment B node3392 node3392Labels = _
    exact sound3392 B hB hF
  have h3397 : mixedVector B (Sum.inr 3397) = Sparse.eval nodeValue3397 (mixedVector B) := by
    change mixedMoment B node3397 node3397Labels = _
    exact sound3397 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm485, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2888, h3392, h3397, h3548, h3584, h4084, reducedSource405] using sourceEq485 B hB

theorem rowSound405 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row405 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck405, numericCheck405, reducedZero405 B hB hF, mul_zero]

theorem reducedZero406 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource406 (mixedVector B) = 0 := by
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm486, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2108, h2113, h2115, h2266, h3584, h4084, reducedSource406] using sourceEq486 B hB

theorem rowSound406 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row406 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck406, numericCheck406, reducedZero406 B hB hF, mul_zero]

theorem reducedZero407 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource407 (mixedVector B) = 0 := by
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2883 : mixedVector B (Sum.inr 2883) = Sparse.eval nodeValue2883 (mixedVector B) := by
    change mixedMoment B node2883 node2883Labels = _
    exact sound2883 B hB hF
  have h3504 : mixedVector B (Sum.inr 3504) = Sparse.eval nodeValue3504 (mixedVector B) := by
    change mixedMoment B node3504 node3504Labels = _
    exact sound3504 B hB hF
  have h3577 : mixedVector B (Sum.inr 3577) = Sparse.eval nodeValue3577 (mixedVector B) := by
    change mixedMoment B node3577 node3577Labels = _
    exact sound3577 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm487, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2108, h2883, h3504, h3577, h3580, h3584, h4084, reducedSource407] using sourceEq487 B hB

theorem rowSound407 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row407 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck407, numericCheck407, reducedZero407 B hB hF, mul_zero]

theorem reducedZero408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource408 (mixedVector B) = 0 := by
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2887 : mixedVector B (Sum.inr 2887) = Sparse.eval nodeValue2887 (mixedVector B) := by
    change mixedMoment B node2887 node2887Labels = _
    exact sound2887 B hB hF
  have h3157 : mixedVector B (Sum.inr 3157) = Sparse.eval nodeValue3157 (mixedVector B) := by
    change mixedMoment B node3157 node3157Labels = _
    exact sound3157 B hB hF
  have h3161 : mixedVector B (Sum.inr 3161) = Sparse.eval nodeValue3161 (mixedVector B) := by
    change mixedMoment B node3161 node3161Labels = _
    exact sound3161 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm488, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2113, h2887, h3157, h3161, h3584, h4084, reducedSource408] using sourceEq488 B hB

theorem rowSound408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row408 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck408, numericCheck408, reducedZero408 B hB hF, mul_zero]

theorem reducedZero409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource409 (mixedVector B) = 0 := by
  have h2883 : mixedVector B (Sum.inr 2883) = Sparse.eval nodeValue2883 (mixedVector B) := by
    change mixedMoment B node2883 node2883Labels = _
    exact sound2883 B hB hF
  have h2887 : mixedVector B (Sum.inr 2887) = Sparse.eval nodeValue2887 (mixedVector B) := by
    change mixedMoment B node2887 node2887Labels = _
    exact sound2887 B hB hF
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h3056 : mixedVector B (Sum.inr 3056) = Sparse.eval nodeValue3056 (mixedVector B) := by
    change mixedMoment B node3056 node3056Labels = _
    exact sound3056 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm489, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2883, h2887, h2888, h3056, h3584, h4084, reducedSource409] using sourceEq489 B hB

theorem rowSound409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row409 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck409, numericCheck409, reducedZero409 B hB hF, mul_zero]

theorem reducedZero410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource410 (mixedVector B) = 0 := by
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h3056 : mixedVector B (Sum.inr 3056) = Sparse.eval nodeValue3056 (mixedVector B) := by
    change mixedMoment B node3056 node3056Labels = _
    exact sound3056 B hB hF
  have h3506 : mixedVector B (Sum.inr 3506) = Sparse.eval nodeValue3506 (mixedVector B) := by
    change mixedMoment B node3506 node3506Labels = _
    exact sound3506 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm490, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2115, h3056, h3506, h3582, h3584, h4084, reducedSource410] using sourceEq490 B hB

theorem rowSound410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row410 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck410, numericCheck410, reducedZero410 B hB hF, mul_zero]

theorem reducedZero414 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource414 (mixedVector B) = 0 := by
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm496, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3054, h3813, h3817, h3907, h3913, h4092, reducedSource414] using sourceEq496 B hB

theorem rowSound414 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row414 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck414, numericCheck414, reducedZero414 B hB hF, mul_zero]

theorem reducedZero415 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource415 (mixedVector B) = 0 := by
  have h1367 : mixedVector B (Sum.inr 1367) = Sparse.eval nodeValue1367 (mixedVector B) := by
    change mixedMoment B node1367 node1367Labels = _
    exact sound1367 B hB hF
  have h1372 : mixedVector B (Sum.inr 1372) = Sparse.eval nodeValue1372 (mixedVector B) := by
    change mixedMoment B node1372 node1372Labels = _
    exact sound1372 B hB hF
  have h1375 : mixedVector B (Sum.inr 1375) = Sparse.eval nodeValue1375 (mixedVector B) := by
    change mixedMoment B node1375 node1375Labels = _
    exact sound1375 B hB hF
  have h1436 : mixedVector B (Sum.inr 1436) = Sparse.eval nodeValue1436 (mixedVector B) := by
    change mixedMoment B node1436 node1436Labels = _
    exact sound1436 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm497, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1367, h1372, h1375, h1436, h3054, h4092, reducedSource415] using sourceEq497 B hB

theorem rowSound415 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row415 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck415, numericCheck415, reducedZero415 B hB hF, mul_zero]

theorem sourceRowsAt400 : MixedData.sourceRows (400 : Fin 2425) =
    MixedData.row400 := by decide +kernel

theorem sourceRowsAt401 : MixedData.sourceRows (401 : Fin 2425) =
    MixedData.row401 := by decide +kernel

theorem sourceRowsAt402 : MixedData.sourceRows (402 : Fin 2425) =
    MixedData.row402 := by decide +kernel

theorem sourceRowsAt403 : MixedData.sourceRows (403 : Fin 2425) =
    MixedData.row403 := by decide +kernel

theorem sourceRowsAt404 : MixedData.sourceRows (404 : Fin 2425) =
    MixedData.row404 := by decide +kernel

theorem sourceRowsAt405 : MixedData.sourceRows (405 : Fin 2425) =
    MixedData.row405 := by decide +kernel

theorem sourceRowsAt406 : MixedData.sourceRows (406 : Fin 2425) =
    MixedData.row406 := by decide +kernel

theorem sourceRowsAt407 : MixedData.sourceRows (407 : Fin 2425) =
    MixedData.row407 := by decide +kernel

theorem sourceRowsAt408 : MixedData.sourceRows (408 : Fin 2425) =
    MixedData.row408 := by decide +kernel

theorem sourceRowsAt409 : MixedData.sourceRows (409 : Fin 2425) =
    MixedData.row409 := by decide +kernel

theorem sourceRowsAt410 : MixedData.sourceRows (410 : Fin 2425) =
    MixedData.row410 := by decide +kernel

theorem sourceRowsAt411 : MixedData.sourceRows (411 : Fin 2425) =
    MixedData.row411 := by decide +kernel

theorem sourceRowsAt412 : MixedData.sourceRows (412 : Fin 2425) =
    MixedData.row412 := by decide +kernel

theorem sourceRowsAt413 : MixedData.sourceRows (413 : Fin 2425) =
    MixedData.row413 := by decide +kernel

theorem sourceRowsAt414 : MixedData.sourceRows (414 : Fin 2425) =
    MixedData.row414 := by decide +kernel

theorem sourceRowsAt415 : MixedData.sourceRows (415 : Fin 2425) =
    MixedData.row415 := by decide +kernel

theorem chunkSound25_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 25) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 400 ∨ k.val = 401 ∨ k.val = 402 ∨ k.val = 403 ∨ k.val = 404 ∨ k.val = 405 ∨ k.val = 406 ∨ k.val = 407 ∨ k.val = 408 ∨ k.val = 409 ∨ k.val = 410 ∨ k.val = 411 ∨ k.val = 412 ∨ k.val = 413 ∨ k.val = 414 ∨ k.val = 415 := by omega
  rcases heq with h400 | h401 | h402 | h403 | h404 | h405 | h406 | h407 | h408 | h409 | h410 | h411 | h412 | h413 | h414 | h415
  · have he : k = (400 : Fin 2425) := Fin.ext h400
    subst k
    rw [sourceRowsAt400]
    exact rowSound400 B hB hF
  · have he : k = (401 : Fin 2425) := Fin.ext h401
    subst k
    rw [sourceRowsAt401]
    exact rowSound401 B hB hF
  · have he : k = (402 : Fin 2425) := Fin.ext h402
    subst k
    rw [sourceRowsAt402]
    exact rowSound402 B hB hF
  · have he : k = (403 : Fin 2425) := Fin.ext h403
    subst k
    rw [sourceRowsAt403]
    exact rowSound403 B hB hF
  · have he : k = (404 : Fin 2425) := Fin.ext h404
    subst k
    rw [sourceRowsAt404]
    exact rowSound404_e B hB hF
  · have he : k = (405 : Fin 2425) := Fin.ext h405
    subst k
    rw [sourceRowsAt405]
    exact rowSound405 B hB hF
  · have he : k = (406 : Fin 2425) := Fin.ext h406
    subst k
    rw [sourceRowsAt406]
    exact rowSound406 B hB hF
  · have he : k = (407 : Fin 2425) := Fin.ext h407
    subst k
    rw [sourceRowsAt407]
    exact rowSound407 B hB hF
  · have he : k = (408 : Fin 2425) := Fin.ext h408
    subst k
    rw [sourceRowsAt408]
    exact rowSound408 B hB hF
  · have he : k = (409 : Fin 2425) := Fin.ext h409
    subst k
    rw [sourceRowsAt409]
    exact rowSound409 B hB hF
  · have he : k = (410 : Fin 2425) := Fin.ext h410
    subst k
    rw [sourceRowsAt410]
    exact rowSound410 B hB hF
  · have he : k = (411 : Fin 2425) := Fin.ext h411
    subst k
    rw [sourceRowsAt411]
    exact rowSound411_e B hB hF
  · have he : k = (412 : Fin 2425) := Fin.ext h412
    subst k
    rw [sourceRowsAt412]
    exact rowSound412_e B hB hF
  · have he : k = (413 : Fin 2425) := Fin.ext h413
    subst k
    rw [sourceRowsAt413]
    exact rowSound413_e B hB hF
  · have he : k = (414 : Fin 2425) := Fin.ext h414
    subst k
    rw [sourceRowsAt414]
    exact rowSound414 B hB hF
  · have he : k = (415 : Fin 2425) := Fin.ext h415
    subst k
    rw [sourceRowsAt415]
    exact rowSound415 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound25_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound25_e_oai
