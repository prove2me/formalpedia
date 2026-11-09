-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:41:48.734202+00:00
-- url     : https://prove2.me/submissions/e3e670e5-925d-4290-a400-d1b6f96817a3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1521_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedAlpha
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem rowFourier_alpha_zero {H : CMatrix} (hH : FourierZero H)
    (ρ : Coord ↪ Coord) (σ : Equiv.Perm Coord) :
    rowFourier H ρ (permuteCharge σ alpha) = 0 := by
  rw [permuteCharge, rowFourier_row_permutation]
  let e : Coord ↪ Coord := Equiv.embeddingCongr σ (Equiv.refl Coord) ρ
  let π : Equiv.Perm Coord := Equiv.ofBijective e
    ⟨e.injective, Finite.surjective_of_injective e.injective⟩
  exact hH π

theorem mixedMoment_alpha {n l : ℕ} (B : Fin 7 → Basis) (hB : AllTransitionsFourierZero B)
    (A : Matrix Coord (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (σ : Equiv.Perm Coord) (hA : (fun i => A i j) = permuteCharge σ alpha) :
    mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hA]
    exact rowFourier_alpha_zero (hB r _) ρ σ
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19953 raw19953Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw19953 raw19953Labels = mixedMoment B raw19953step0 raw19953step0Labels := by
      have hz : ∀ j, raw19953 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19953step0 = (fun i j => raw19953 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19953step0 raw19953; decide +kernel
      have hl : raw19953step0Labels = raw19953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953 raw19953Labels permutation520 hz
    mixedMoment B raw19953step0 raw19953step0Labels = mixedMoment B raw19953step1 raw19953step1Labels := by
      have hz : ∀ j, raw19953step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19953step1 = (fun i j => raw19953step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19953step1 raw19953step0; decide +kernel
      have hl : raw19953step1Labels = raw19953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953step0 raw19953step0Labels permutation104 hz
    mixedMoment B raw19953step1 raw19953step1Labels = mixedMoment B raw19953step2 raw19953step2Labels := by
      have hz : ∀ j, raw19953step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19953step2 = (fun i j => raw19953step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19953step2 raw19953step1; decide +kernel
      have hl : raw19953step2Labels = raw19953step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953step1 raw19953step1Labels permutation20 hz
    mixedMoment B raw19953step2 raw19953step2Labels = mixedMoment B raw19953step3 raw19953step3Labels := by
      have hz : ∀ j, raw19953step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19953step3 = (fun i j => raw19953step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19953step3 raw19953step2; decide +kernel
      have hl : raw19953step3Labels = raw19953step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953step2 raw19953step2Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21883 raw21883Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw21883 raw21883Labels = mixedMoment B raw21883step0 raw21883step0Labels := by
      have hz : ∀ j, raw21883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21883step0 = (fun i j => raw21883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21883step0 raw21883; decide +kernel
      have hl : raw21883step0Labels = raw21883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21883 raw21883Labels permutation434 hz
    mixedMoment B raw21883step0 raw21883step0Labels = mixedMoment B raw21883step1 raw21883step1Labels := by
      have hz : ∀ j, raw21883step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21883step1 = (fun i j => raw21883step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21883step1 raw21883step0; decide +kernel
      have hl : raw21883step1Labels = raw21883step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21883step0 raw21883step0Labels permutation80 hz
    _ = mixedMoment B node1080 node1080Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22058 raw22058Labels = mixedMoment B node1699 node1699Labels := by
  calc
    _ = mixedMoment B node1699 node1699Labels := by rfl

theorem canonical22061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22061 raw22061Labels = mixedMoment B node786 node786Labels := by
  calc
    _ = mixedMoment B node786 node786Labels := by rfl

theorem canonical22064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22064 raw22064Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw22064 raw22064Labels = mixedMoment B raw22064step0 raw22064step0Labels := by
      have hz : ∀ j, raw22064 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22064step0 = (fun i j => raw22064 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22064step0 raw22064; decide +kernel
      have hl : raw22064step0Labels = raw22064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22064 raw22064Labels permutation590 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical22065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22065 raw22065Labels = mixedMoment B node1698 node1698Labels := by
  calc
    _ = mixedMoment B node1698 node1698Labels := by rfl

theorem canonical22066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22066 raw22066Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw22066 raw22066Labels = mixedMoment B raw22066step0 raw22066step0Labels := by
      have ha : raw22066step0 = (fun i j => raw22066 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22066step0 raw22066; decide +kernel
      have hl : raw22066step0Labels = raw22066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22066 raw22066Labels permutation184 permutation2
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical22068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22068 raw22068Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw22068 raw22068Labels = mixedMoment B raw22068step0 raw22068step0Labels := by
      have ha : raw22068step0 = (fun i j => raw22068 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22068step0 raw22068; decide +kernel
      have hl : raw22068step0Labels = raw22068Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22068 raw22068Labels permutation154 permutation2
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical22071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22071 raw22071Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw22071 raw22071Labels = mixedMoment B raw22071step0 raw22071step0Labels := by
      have hz : ∀ j, raw22071 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22071step0 = (fun i j => raw22071 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22071step0 raw22071; decide +kernel
      have hl : raw22071step0Labels = raw22071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22071 raw22071Labels permutation520 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23799 raw23799Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23799 raw23799Labels = mixedMoment B raw23799step0 raw23799step0Labels := by
      have hz : ∀ j, raw23799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23799step0 = (fun i j => raw23799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23799step0 raw23799; decide +kernel
      have hl : raw23799step0Labels = raw23799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23799 raw23799Labels permutation346 hz
    mixedMoment B raw23799step0 raw23799step0Labels = mixedMoment B raw23799step1 raw23799step1Labels := by
      have hz : ∀ j, raw23799step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23799step1 = (fun i j => raw23799step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23799step1 raw23799step0; decide +kernel
      have hl : raw23799step1Labels = raw23799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23799step0 raw23799step0Labels permutation56 hz
    mixedMoment B raw23799step1 raw23799step1Labels = mixedMoment B raw23799step2 raw23799step2Labels := by
      have ha : raw23799step2 = -raw23799step1 := by apply Matrix.ext; change ∀ i j, raw23799step2 i j = -(raw23799step1 i j); unfold raw23799step2 raw23799step1; decide +kernel
      have hl : raw23799step2Labels = raw23799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23890 raw23890Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw23890 raw23890Labels = mixedMoment B raw23890step0 raw23890step0Labels := by
      have ha : raw23890step0 = (fun i j => raw23890 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23890step0 raw23890; decide +kernel
      have hl : raw23890step0Labels = raw23890Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23890 raw23890Labels permutation224 permutation4
    mixedMoment B raw23890step0 raw23890step0Labels = mixedMoment B raw23890step1 raw23890step1Labels := by
      have ha : raw23890step1 = -raw23890step0 := by apply Matrix.ext; change ∀ i j, raw23890step1 i j = -(raw23890step0 i j); unfold raw23890step1 raw23890step0; decide +kernel
      have hl : raw23890step1Labels = raw23890step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node803 node803Labels := by rfl

theorem canonical23891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23891 raw23891Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw23891 raw23891Labels = mixedMoment B raw23891step0 raw23891step0Labels := by
      have ha : raw23891step0 = (fun i j => raw23891 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23891step0 raw23891; decide +kernel
      have hl : raw23891step0Labels = raw23891Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23891 raw23891Labels permutation200 permutation4
    mixedMoment B raw23891step0 raw23891step0Labels = mixedMoment B raw23891step1 raw23891step1Labels := by
      have ha : raw23891step1 = -raw23891step0 := by apply Matrix.ext; change ∀ i j, raw23891step1 i j = -(raw23891step0 i j); unfold raw23891step1 raw23891step0; decide +kernel
      have hl : raw23891step1Labels = raw23891step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node803 node803Labels := by rfl

theorem canonical23917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23917 raw23917Labels = mixedMoment B node822 node822Labels := by
  calc
    mixedMoment B raw23917 raw23917Labels = mixedMoment B raw23917step0 raw23917step0Labels := by
      have ha : raw23917step0 = (fun i j => raw23917 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23917step0 raw23917; decide +kernel
      have hl : raw23917step0Labels = raw23917Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23917 raw23917Labels permutation246 permutation4
    mixedMoment B raw23917step0 raw23917step0Labels = mixedMoment B raw23917step1 raw23917step1Labels := by
      have ha : raw23917step1 = -raw23917step0 := by apply Matrix.ext; change ∀ i j, raw23917step1 i j = -(raw23917step0 i j); unfold raw23917step1 raw23917step0; decide +kernel
      have hl : raw23917step1Labels = raw23917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node822 node822Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical199
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25543 raw25543Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw25543 raw25543Labels = mixedMoment B raw25543step0 raw25543step0Labels := by
      have hz : ∀ j, raw25543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25543step0 = (fun i j => raw25543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25543step0 raw25543; decide +kernel
      have hl : raw25543step0Labels = raw25543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25543 raw25543Labels permutation346 hz
    mixedMoment B raw25543step0 raw25543step0Labels = mixedMoment B raw25543step1 raw25543step1Labels := by
      have ha : raw25543step1 = (fun i j => raw25543step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25543step1 raw25543step0; decide +kernel
      have hl : raw25543step1Labels = raw25543step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25543step0 raw25543step0Labels permutation32 permutation4
    mixedMoment B raw25543step1 raw25543step1Labels = mixedMoment B raw25543step2 raw25543step2Labels := by
      have ha : raw25543step2 = -raw25543step1 := by apply Matrix.ext; change ∀ i j, raw25543step2 i j = -(raw25543step1 i j); unfold raw25543step2 raw25543step1; decide +kernel
      have hl : raw25543step2Labels = raw25543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node850 node850Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical203
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25994 raw25994Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw25994 raw25994Labels = mixedMoment B raw25994step0 raw25994step0Labels := by
      have hz : ∀ j, raw25994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25994step0 = (fun i j => raw25994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25994step0 raw25994; decide +kernel
      have hl : raw25994step0Labels = raw25994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25994 raw25994Labels permutation346 hz
    mixedMoment B raw25994step0 raw25994step0Labels = mixedMoment B raw25994step1 raw25994step1Labels := by
      have hz : ∀ j, raw25994step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25994step1 = (fun i j => raw25994step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25994step1 raw25994step0; decide +kernel
      have hl : raw25994step1Labels = raw25994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25994step0 raw25994step0Labels permutation56 hz
    _ = mixedMoment B node1080 node1080Labels := by rfl

theorem canonical25995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25995 raw25995Labels = mixedMoment B node598 node598Labels := by
  calc
    mixedMoment B raw25995 raw25995Labels = mixedMoment B raw25995step0 raw25995step0Labels := by
      have hz : ∀ j, raw25995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25995step0 = (fun i j => raw25995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25995step0 raw25995; decide +kernel
      have hl : raw25995step0Labels = raw25995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25995 raw25995Labels permutation346 hz
    _ = mixedMoment B node598 node598Labels := by rfl

theorem canonical25999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25999 raw25999Labels = mixedMoment B node918 node918Labels := by
  calc
    mixedMoment B raw25999 raw25999Labels = mixedMoment B raw25999step0 raw25999step0Labels := by
      have ha : raw25999step0 = (fun i j => raw25999 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25999step0 raw25999; decide +kernel
      have hl : raw25999step0Labels = raw25999Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25999 raw25999Labels permutation176 permutation2
    _ = mixedMoment B node918 node918Labels := by rfl

theorem canonical26000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26000 raw26000Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw26000 raw26000Labels = mixedMoment B raw26000step0 raw26000step0Labels := by
      have hz : ∀ j, raw26000 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26000step0 = (fun i j => raw26000 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26000step0 raw26000; decide +kernel
      have hl : raw26000step0Labels = raw26000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26000 raw26000Labels permutation520 hz
    mixedMoment B raw26000step0 raw26000step0Labels = mixedMoment B raw26000step1 raw26000step1Labels := by
      have hz : ∀ j, raw26000step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw26000step1 = (fun i j => raw26000step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw26000step1 raw26000step0; decide +kernel
      have hl : raw26000step1Labels = raw26000step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26000step0 raw26000step0Labels permutation80 hz
    _ = mixedMoment B node1080 node1080Labels := by rfl

theorem canonical26001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26001 raw26001Labels = mixedMoment B node1078 node1078Labels := by
  calc
    mixedMoment B raw26001 raw26001Labels = mixedMoment B raw26001step0 raw26001step0Labels := by
      have hz : ∀ j, raw26001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26001step0 = (fun i j => raw26001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26001step0 raw26001; decide +kernel
      have hl : raw26001step0Labels = raw26001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26001 raw26001Labels permutation346 hz
    _ = mixedMoment B node1078 node1078Labels := by rfl

theorem canonical26074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26074 raw26074Labels = mixedMoment B node1006 node1006Labels := by
  calc
    mixedMoment B raw26074 raw26074Labels = mixedMoment B raw26074step0 raw26074step0Labels := by
      have hz : ∀ j, raw26074 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26074step0 = (fun i j => raw26074 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26074step0 raw26074; decide +kernel
      have hl : raw26074step0Labels = raw26074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26074 raw26074Labels permutation265 hz
    mixedMoment B raw26074step0 raw26074step0Labels = mixedMoment B raw26074step1 raw26074step1Labels := by
      have ha : raw26074step1 = (fun i j => raw26074step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26074step1 raw26074step0; decide +kernel
      have hl : raw26074step1Labels = raw26074step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26074step0 raw26074step0Labels permutation34 permutation2
    _ = mixedMoment B node1006 node1006Labels := by rfl

theorem canonical26075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26075 raw26075Labels = mixedMoment B node2001 node2001Labels := by
  calc
    mixedMoment B raw26075 raw26075Labels = mixedMoment B raw26075step0 raw26075step0Labels := by
      have ha : raw26075step0 = (fun i j => raw26075 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26075step0 raw26075; decide +kernel
      have hl : raw26075step0Labels = raw26075Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26075 raw26075Labels permutation154 permutation2
    _ = mixedMoment B node2001 node2001Labels := by rfl

theorem canonical26076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26076 raw26076Labels = mixedMoment B node1948 node1948Labels := by
  calc
    mixedMoment B raw26076 raw26076Labels = mixedMoment B raw26076step0 raw26076step0Labels := by
      have hz : ∀ j, raw26076 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26076step0 = (fun i j => raw26076 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26076step0 raw26076; decide +kernel
      have hl : raw26076step0Labels = raw26076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26076 raw26076Labels permutation265 hz
    mixedMoment B raw26076step0 raw26076step0Labels = mixedMoment B raw26076step1 raw26076step1Labels := by
      have ha : raw26076step1 = (fun i j => raw26076step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26076step1 raw26076step0; decide +kernel
      have hl : raw26076step1Labels = raw26076step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26076step0 raw26076step0Labels permutation34 permutation2
    _ = mixedMoment B node1948 node1948Labels := by rfl

theorem canonical26077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26077 raw26077Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw26077 raw26077Labels = mixedMoment B raw26077step0 raw26077step0Labels := by
      have hz : ∀ j, raw26077 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26077step0 = (fun i j => raw26077 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26077step0 raw26077; decide +kernel
      have hl : raw26077step0Labels = raw26077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26077 raw26077Labels permutation265 hz
    _ = mixedMoment B node2221 node2221Labels := by rfl

theorem canonical26078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26078 raw26078Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw26078 raw26078Labels = mixedMoment B raw26078step0 raw26078step0Labels := by
      have hz : ∀ j, raw26078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26078step0 = (fun i j => raw26078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26078step0 raw26078; decide +kernel
      have hl : raw26078step0Labels = raw26078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26078 raw26078Labels permutation265 hz
    mixedMoment B raw26078step0 raw26078step0Labels = mixedMoment B raw26078step1 raw26078step1Labels := by
      have ha : raw26078step1 = (fun i j => raw26078step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26078step1 raw26078step0; decide +kernel
      have hl : raw26078step1Labels = raw26078step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26078step0 raw26078step0Labels permutation34 permutation2
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical26079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26079 raw26079Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw26079 raw26079Labels = mixedMoment B raw26079step0 raw26079step0Labels := by
      have hz : ∀ j, raw26079 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26079step0 = (fun i j => raw26079 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26079step0 raw26079; decide +kernel
      have hl : raw26079step0Labels = raw26079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26079 raw26079Labels permutation265 hz
    mixedMoment B raw26079step0 raw26079step0Labels = mixedMoment B raw26079step1 raw26079step1Labels := by
      have ha : raw26079step1 = (fun i j => raw26079step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26079step1 raw26079step0; decide +kernel
      have hl : raw26079step1Labels = raw26079step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26079step0 raw26079step0Labels permutation37 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical26080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26080 raw26080Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw26080 raw26080Labels = mixedMoment B raw26080step0 raw26080step0Labels := by
      have hz : ∀ j, raw26080 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26080step0 = (fun i j => raw26080 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26080step0 raw26080; decide +kernel
      have hl : raw26080step0Labels = raw26080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26080 raw26080Labels permutation590 hz
    mixedMoment B raw26080step0 raw26080step0Labels = mixedMoment B raw26080step1 raw26080step1Labels := by
      have hz : ∀ j, raw26080step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26080step1 = (fun i j => raw26080step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26080step1 raw26080step0; decide +kernel
      have hl : raw26080step1Labels = raw26080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26080step0 raw26080step0Labels permutation56 hz
    mixedMoment B raw26080step1 raw26080step1Labels = mixedMoment B raw26080step2 raw26080step2Labels := by
      have ha : raw26080step2 = (fun i j => raw26080step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26080step2 raw26080step1; decide +kernel
      have hl : raw26080step2Labels = raw26080step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26080step1 raw26080step1Labels permutation9 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical26085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26085 raw26085Labels = mixedMoment B node1001 node1001Labels := by
  calc
    mixedMoment B raw26085 raw26085Labels = mixedMoment B raw26085step0 raw26085step0Labels := by
      have hz : ∀ j, raw26085 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26085step0 = (fun i j => raw26085 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26085step0 raw26085; decide +kernel
      have hl : raw26085step0Labels = raw26085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26085 raw26085Labels permutation265 hz
    mixedMoment B raw26085step0 raw26085step0Labels = mixedMoment B raw26085step1 raw26085step1Labels := by
      have ha : raw26085step1 = (fun i j => raw26085step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26085step1 raw26085step0; decide +kernel
      have hl : raw26085step1Labels = raw26085step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26085step0 raw26085step0Labels permutation34 permutation2
    _ = mixedMoment B node1001 node1001Labels := by rfl

theorem canonical26086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26086 raw26086Labels = mixedMoment B node1998 node1998Labels := by
  calc
    mixedMoment B raw26086 raw26086Labels = mixedMoment B raw26086step0 raw26086step0Labels := by
      have ha : raw26086step0 = (fun i j => raw26086 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26086step0 raw26086; decide +kernel
      have hl : raw26086step0Labels = raw26086Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26086 raw26086Labels permutation154 permutation2
    _ = mixedMoment B node1998 node1998Labels := by rfl

theorem canonical26087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26087 raw26087Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw26087 raw26087Labels = mixedMoment B raw26087step0 raw26087step0Labels := by
      have hz : ∀ j, raw26087 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26087step0 = (fun i j => raw26087 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26087step0 raw26087; decide +kernel
      have hl : raw26087step0Labels = raw26087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26087 raw26087Labels permutation265 hz
    mixedMoment B raw26087step0 raw26087step0Labels = mixedMoment B raw26087step1 raw26087step1Labels := by
      have ha : raw26087step1 = (fun i j => raw26087step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26087step1 raw26087step0; decide +kernel
      have hl : raw26087step1Labels = raw26087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26087step0 raw26087step0Labels permutation34 permutation2
    _ = mixedMoment B node1946 node1946Labels := by rfl

theorem canonical26088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26088 raw26088Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw26088 raw26088Labels = mixedMoment B raw26088step0 raw26088step0Labels := by
      have hz : ∀ j, raw26088 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26088step0 = (fun i j => raw26088 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26088step0 raw26088; decide +kernel
      have hl : raw26088step0Labels = raw26088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26088 raw26088Labels permutation265 hz
    _ = mixedMoment B node2220 node2220Labels := by rfl

theorem canonical26089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26089 raw26089Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw26089 raw26089Labels = mixedMoment B raw26089step0 raw26089step0Labels := by
      have hz : ∀ j, raw26089 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26089step0 = (fun i j => raw26089 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26089step0 raw26089; decide +kernel
      have hl : raw26089step0Labels = raw26089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26089 raw26089Labels permutation520 hz
    mixedMoment B raw26089step0 raw26089step0Labels = mixedMoment B raw26089step1 raw26089step1Labels := by
      have hz : ∀ j, raw26089step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26089step1 = (fun i j => raw26089step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26089step1 raw26089step0; decide +kernel
      have hl : raw26089step1Labels = raw26089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26089step0 raw26089step0Labels permutation56 hz
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical26090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26090 raw26090Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw26090 raw26090Labels = mixedMoment B raw26090step0 raw26090step0Labels := by
      have hz : ∀ j, raw26090 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26090step0 = (fun i j => raw26090 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26090step0 raw26090; decide +kernel
      have hl : raw26090step0Labels = raw26090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26090 raw26090Labels permutation265 hz
    mixedMoment B raw26090step0 raw26090step0Labels = mixedMoment B raw26090step1 raw26090step1Labels := by
      have ha : raw26090step1 = (fun i j => raw26090step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26090step1 raw26090step0; decide +kernel
      have hl : raw26090step1Labels = raw26090step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26090step0 raw26090step0Labels permutation35 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical26091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26091 raw26091Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw26091 raw26091Labels = mixedMoment B raw26091step0 raw26091step0Labels := by
      have hz : ∀ j, raw26091 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26091step0 = (fun i j => raw26091 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26091step0 raw26091; decide +kernel
      have hl : raw26091step0Labels = raw26091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26091 raw26091Labels permutation520 hz
    mixedMoment B raw26091step0 raw26091step0Labels = mixedMoment B raw26091step1 raw26091step1Labels := by
      have hz : ∀ j, raw26091step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26091step1 = (fun i j => raw26091step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26091step1 raw26091step0; decide +kernel
      have hl : raw26091step1Labels = raw26091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26091step0 raw26091step0Labels permutation56 hz
    mixedMoment B raw26091step1 raw26091step1Labels = mixedMoment B raw26091step2 raw26091step2Labels := by
      have ha : raw26091step2 = (fun i j => raw26091step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26091step2 raw26091step1; decide +kernel
      have hl : raw26091step2Labels = raw26091step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26091step1 raw26091step1Labels permutation9 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical26092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26092 raw26092Labels = mixedMoment B node1008 node1008Labels := by
  calc
    mixedMoment B raw26092 raw26092Labels = mixedMoment B raw26092step0 raw26092step0Labels := by
      have hz : ∀ j, raw26092 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26092step0 = (fun i j => raw26092 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26092step0 raw26092; decide +kernel
      have hl : raw26092step0Labels = raw26092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26092 raw26092Labels permutation265 hz
    _ = mixedMoment B node1008 node1008Labels := by rfl

theorem canonical26093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26093 raw26093Labels = mixedMoment B node2002 node2002Labels := by
  calc
    _ = mixedMoment B node2002 node2002Labels := by rfl

theorem canonical26094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26094 raw26094Labels = mixedMoment B node1949 node1949Labels := by
  calc
    mixedMoment B raw26094 raw26094Labels = mixedMoment B raw26094step0 raw26094step0Labels := by
      have hz : ∀ j, raw26094 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26094step0 = (fun i j => raw26094 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26094step0 raw26094; decide +kernel
      have hl : raw26094step0Labels = raw26094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26094 raw26094Labels permutation265 hz
    _ = mixedMoment B node1949 node1949Labels := by rfl

theorem canonical26095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26095 raw26095Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw26095 raw26095Labels = mixedMoment B raw26095step0 raw26095step0Labels := by
      have hz : ∀ j, raw26095 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26095step0 = (fun i j => raw26095 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26095step0 raw26095; decide +kernel
      have hl : raw26095step0Labels = raw26095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26095 raw26095Labels permutation265 hz
    _ = mixedMoment B node2217 node2217Labels := by rfl

theorem canonical26096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26096 raw26096Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw26096 raw26096Labels = mixedMoment B raw26096step0 raw26096step0Labels := by
      have hz : ∀ j, raw26096 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26096step0 = (fun i j => raw26096 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26096step0 raw26096; decide +kernel
      have hl : raw26096step0Labels = raw26096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26096 raw26096Labels permutation265 hz
    mixedMoment B raw26096step0 raw26096step0Labels = mixedMoment B raw26096step1 raw26096step1Labels := by
      have ha : raw26096step1 = (fun i j => raw26096step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26096step1 raw26096step0; decide +kernel
      have hl : raw26096step1Labels = raw26096step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26096step0 raw26096step0Labels permutation34 permutation2
    _ = mixedMoment B node2217 node2217Labels := by rfl

theorem canonical26097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26097 raw26097Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw26097 raw26097Labels = mixedMoment B raw26097step0 raw26097step0Labels := by
      have hz : ∀ j, raw26097 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26097step0 = (fun i j => raw26097 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26097step0 raw26097; decide +kernel
      have hl : raw26097step0Labels = raw26097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26097 raw26097Labels permutation265 hz
    mixedMoment B raw26097step0 raw26097step0Labels = mixedMoment B raw26097step1 raw26097step1Labels := by
      have ha : raw26097step1 = (fun i j => raw26097step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26097step1 raw26097step0; decide +kernel
      have hl : raw26097step1Labels = raw26097step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26097step0 raw26097step0Labels permutation36 permutation2
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical26098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26098 raw26098Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw26098 raw26098Labels = mixedMoment B raw26098step0 raw26098step0Labels := by
      have hz : ∀ j, raw26098 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26098step0 = (fun i j => raw26098 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26098step0 raw26098; decide +kernel
      have hl : raw26098step0Labels = raw26098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26098 raw26098Labels permutation590 hz
    mixedMoment B raw26098step0 raw26098step0Labels = mixedMoment B raw26098step1 raw26098step1Labels := by
      have hz : ∀ j, raw26098step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26098step1 = (fun i j => raw26098step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26098step1 raw26098step0; decide +kernel
      have hl : raw26098step1Labels = raw26098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26098step0 raw26098step0Labels permutation56 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical26099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26099 raw26099Labels = mixedMoment B node996 node996Labels := by
  calc
    mixedMoment B raw26099 raw26099Labels = mixedMoment B raw26099step0 raw26099step0Labels := by
      have ha : raw26099step0 = (fun i j => raw26099 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26099step0 raw26099; decide +kernel
      have hl : raw26099step0Labels = raw26099Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26099 raw26099Labels permutation180 permutation2
    _ = mixedMoment B node996 node996Labels := by rfl

theorem canonical26100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26100 raw26100Labels = mixedMoment B node1071 node1071Labels := by
  calc
    mixedMoment B raw26100 raw26100Labels = mixedMoment B raw26100step0 raw26100step0Labels := by
      have hz : ∀ j, raw26100 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26100step0 = (fun i j => raw26100 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26100step0 raw26100; decide +kernel
      have hl : raw26100step0Labels = raw26100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26100 raw26100Labels permutation265 hz
    mixedMoment B raw26100step0 raw26100step0Labels = mixedMoment B raw26100step1 raw26100step1Labels := by
      have ha : raw26100step1 = (fun i j => raw26100step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26100step1 raw26100step0; decide +kernel
      have hl : raw26100step1Labels = raw26100step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26100step0 raw26100step0Labels permutation36 permutation2
    _ = mixedMoment B node1071 node1071Labels := by rfl

theorem canonical26101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26101 raw26101Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw26101 raw26101Labels = mixedMoment B raw26101step0 raw26101step0Labels := by
      have hz : ∀ j, raw26101 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26101step0 = (fun i j => raw26101 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26101step0 raw26101; decide +kernel
      have hl : raw26101step0Labels = raw26101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26101 raw26101Labels permutation265 hz
    mixedMoment B raw26101step0 raw26101step0Labels = mixedMoment B raw26101step1 raw26101step1Labels := by
      have ha : raw26101step1 = (fun i j => raw26101step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26101step1 raw26101step0; decide +kernel
      have hl : raw26101step1Labels = raw26101step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26101step0 raw26101step0Labels permutation37 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical26102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26102 raw26102Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw26102 raw26102Labels = mixedMoment B raw26102step0 raw26102step0Labels := by
      have hz : ∀ j, raw26102 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26102step0 = (fun i j => raw26102 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26102step0 raw26102; decide +kernel
      have hl : raw26102step0Labels = raw26102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26102 raw26102Labels permutation265 hz
    mixedMoment B raw26102step0 raw26102step0Labels = mixedMoment B raw26102step1 raw26102step1Labels := by
      have ha : raw26102step1 = (fun i j => raw26102step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26102step1 raw26102step0; decide +kernel
      have hl : raw26102step1Labels = raw26102step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26102step0 raw26102step0Labels permutation36 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical26103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26103 raw26103Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw26103 raw26103Labels = mixedMoment B raw26103step0 raw26103step0Labels := by
      have hz : ∀ j, raw26103 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26103step0 = (fun i j => raw26103 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26103step0 raw26103; decide +kernel
      have hl : raw26103step0Labels = raw26103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26103 raw26103Labels permutation265 hz
    mixedMoment B raw26103step0 raw26103step0Labels = mixedMoment B raw26103step1 raw26103step1Labels := by
      have ha : raw26103step1 = (fun i j => raw26103step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26103step1 raw26103step0; decide +kernel
      have hl : raw26103step1Labels = raw26103step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26103step0 raw26103step0Labels permutation34 permutation2
    _ = mixedMoment B node1005 node1005Labels := by rfl

theorem canonical26104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26104 raw26104Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw26104 raw26104Labels = mixedMoment B raw26104step0 raw26104step0Labels := by
      have ha : raw26104step0 = (fun i j => raw26104 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26104step0 raw26104; decide +kernel
      have hl : raw26104step0Labels = raw26104Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26104 raw26104Labels permutation154 permutation2
    _ = mixedMoment B node2000 node2000Labels := by rfl

theorem canonical26105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26105 raw26105Labels = mixedMoment B node1947 node1947Labels := by
  calc
    mixedMoment B raw26105 raw26105Labels = mixedMoment B raw26105step0 raw26105step0Labels := by
      have hz : ∀ j, raw26105 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26105step0 = (fun i j => raw26105 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26105step0 raw26105; decide +kernel
      have hl : raw26105step0Labels = raw26105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26105 raw26105Labels permutation265 hz
    mixedMoment B raw26105step0 raw26105step0Labels = mixedMoment B raw26105step1 raw26105step1Labels := by
      have ha : raw26105step1 = (fun i j => raw26105step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26105step1 raw26105step0; decide +kernel
      have hl : raw26105step1Labels = raw26105step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26105step0 raw26105step0Labels permutation34 permutation2
    _ = mixedMoment B node1947 node1947Labels := by rfl

theorem canonical26106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26106 raw26106Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw26106 raw26106Labels = mixedMoment B raw26106step0 raw26106step0Labels := by
      have hz : ∀ j, raw26106 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26106step0 = (fun i j => raw26106 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26106step0 raw26106; decide +kernel
      have hl : raw26106step0Labels = raw26106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26106 raw26106Labels permutation265 hz
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical26107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26107 raw26107Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw26107 raw26107Labels = mixedMoment B raw26107step0 raw26107step0Labels := by
      have hz : ∀ j, raw26107 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26107step0 = (fun i j => raw26107 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26107step0 raw26107; decide +kernel
      have hl : raw26107step0Labels = raw26107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26107 raw26107Labels permutation265 hz
    mixedMoment B raw26107step0 raw26107step0Labels = mixedMoment B raw26107step1 raw26107step1Labels := by
      have ha : raw26107step1 = (fun i j => raw26107step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26107step1 raw26107step0; decide +kernel
      have hl : raw26107step1Labels = raw26107step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26107step0 raw26107step0Labels permutation34 permutation2
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical26108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26108 raw26108Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw26108 raw26108Labels = mixedMoment B raw26108step0 raw26108step0Labels := by
      have hz : ∀ j, raw26108 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26108step0 = (fun i j => raw26108 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26108step0 raw26108; decide +kernel
      have hl : raw26108step0Labels = raw26108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26108 raw26108Labels permutation265 hz
    mixedMoment B raw26108step0 raw26108step0Labels = mixedMoment B raw26108step1 raw26108step1Labels := by
      have ha : raw26108step1 = (fun i j => raw26108step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26108step1 raw26108step0; decide +kernel
      have hl : raw26108step1Labels = raw26108step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26108step0 raw26108step0Labels permutation35 permutation2
    _ = mixedMoment B node2227 node2227Labels := by rfl

theorem canonical26109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26109 raw26109Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw26109 raw26109Labels = mixedMoment B raw26109step0 raw26109step0Labels := by
      have hz : ∀ j, raw26109 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26109step0 = (fun i j => raw26109 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26109step0 raw26109; decide +kernel
      have hl : raw26109step0Labels = raw26109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26109 raw26109Labels permutation265 hz
    mixedMoment B raw26109step0 raw26109step0Labels = mixedMoment B raw26109step1 raw26109step1Labels := by
      have ha : raw26109step1 = (fun i j => raw26109step0 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26109step1 raw26109step0; decide +kernel
      have hl : raw26109step1Labels = raw26109step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26109step0 raw26109step0Labels permutation35 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical204
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26114 raw26114Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw26114 raw26114Labels = mixedMoment B raw26114step0 raw26114step0Labels := by
      have ha : raw26114step0 = (fun i j => raw26114 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26114step0 raw26114; decide +kernel
      have hl : raw26114step0Labels = raw26114Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26114 raw26114Labels permutation179 permutation2
    _ = mixedMoment B node998 node998Labels := by rfl

theorem canonical26115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26115 raw26115Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw26115 raw26115Labels = mixedMoment B raw26115step0 raw26115step0Labels := by
      have hz : ∀ j, raw26115 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26115step0 = (fun i j => raw26115 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26115step0 raw26115; decide +kernel
      have hl : raw26115step0Labels = raw26115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26115 raw26115Labels permutation265 hz
    mixedMoment B raw26115step0 raw26115step0Labels = mixedMoment B raw26115step1 raw26115step1Labels := by
      have ha : raw26115step1 = (fun i j => raw26115step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26115step1 raw26115step0; decide +kernel
      have hl : raw26115step1Labels = raw26115step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26115step0 raw26115step0Labels permutation35 permutation2
    _ = mixedMoment B node1073 node1073Labels := by rfl

theorem canonical26116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26116 raw26116Labels = mixedMoment B node1004 node1004Labels := by
  calc
    mixedMoment B raw26116 raw26116Labels = mixedMoment B raw26116step0 raw26116step0Labels := by
      have hz : ∀ j, raw26116 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26116step0 = (fun i j => raw26116 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26116step0 raw26116; decide +kernel
      have hl : raw26116step0Labels = raw26116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26116 raw26116Labels permutation265 hz
    mixedMoment B raw26116step0 raw26116step0Labels = mixedMoment B raw26116step1 raw26116step1Labels := by
      have ha : raw26116step1 = (fun i j => raw26116step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26116step1 raw26116step0; decide +kernel
      have hl : raw26116step1Labels = raw26116step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26116step0 raw26116step0Labels permutation35 permutation2
    _ = mixedMoment B node1004 node1004Labels := by rfl

theorem canonical26117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26117 raw26117Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw26117 raw26117Labels = mixedMoment B raw26117step0 raw26117step0Labels := by
      have hz : ∀ j, raw26117 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26117step0 = (fun i j => raw26117 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26117step0 raw26117; decide +kernel
      have hl : raw26117step0Labels = raw26117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26117 raw26117Labels permutation265 hz
    mixedMoment B raw26117step0 raw26117step0Labels = mixedMoment B raw26117step1 raw26117step1Labels := by
      have ha : raw26117step1 = (fun i j => raw26117step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26117step1 raw26117step0; decide +kernel
      have hl : raw26117step1Labels = raw26117step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26117step0 raw26117step0Labels permutation36 permutation2
    _ = mixedMoment B node1005 node1005Labels := by rfl

theorem canonical26124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26124 raw26124Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw26124 raw26124Labels = mixedMoment B raw26124step0 raw26124step0Labels := by
      have hz : ∀ j, raw26124 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26124step0 = (fun i j => raw26124 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26124step0 raw26124; decide +kernel
      have hl : raw26124step0Labels = raw26124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26124 raw26124Labels permutation265 hz
    mixedMoment B raw26124step0 raw26124step0Labels = mixedMoment B raw26124step1 raw26124step1Labels := by
      have ha : raw26124step1 = (fun i j => raw26124step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26124step1 raw26124step0; decide +kernel
      have hl : raw26124step1Labels = raw26124step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26124step0 raw26124step0Labels permutation34 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical26125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26125 raw26125Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw26125 raw26125Labels = mixedMoment B raw26125step0 raw26125step0Labels := by
      have ha : raw26125step0 = (fun i j => raw26125 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26125step0 raw26125; decide +kernel
      have hl : raw26125step0Labels = raw26125Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26125 raw26125Labels permutation154 permutation2
    _ = mixedMoment B node1997 node1997Labels := by rfl

theorem canonical26126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26126 raw26126Labels = mixedMoment B node1945 node1945Labels := by
  calc
    mixedMoment B raw26126 raw26126Labels = mixedMoment B raw26126step0 raw26126step0Labels := by
      have hz : ∀ j, raw26126 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26126step0 = (fun i j => raw26126 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26126step0 raw26126; decide +kernel
      have hl : raw26126step0Labels = raw26126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26126 raw26126Labels permutation265 hz
    mixedMoment B raw26126step0 raw26126step0Labels = mixedMoment B raw26126step1 raw26126step1Labels := by
      have ha : raw26126step1 = (fun i j => raw26126step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26126step1 raw26126step0; decide +kernel
      have hl : raw26126step1Labels = raw26126step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26126step0 raw26126step0Labels permutation34 permutation2
    _ = mixedMoment B node1945 node1945Labels := by rfl

theorem canonical26127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26127 raw26127Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw26127 raw26127Labels = mixedMoment B raw26127step0 raw26127step0Labels := by
      have hz : ∀ j, raw26127 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26127step0 = (fun i j => raw26127 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26127step0 raw26127; decide +kernel
      have hl : raw26127step0Labels = raw26127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26127 raw26127Labels permutation265 hz
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical26128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26128 raw26128Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw26128 raw26128Labels = mixedMoment B raw26128step0 raw26128step0Labels := by
      have hz : ∀ j, raw26128 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26128step0 = (fun i j => raw26128 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26128step0 raw26128; decide +kernel
      have hl : raw26128step0Labels = raw26128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26128 raw26128Labels permutation520 hz
    mixedMoment B raw26128step0 raw26128step0Labels = mixedMoment B raw26128step1 raw26128step1Labels := by
      have hz : ∀ j, raw26128step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26128step1 = (fun i j => raw26128step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26128step1 raw26128step0; decide +kernel
      have hl : raw26128step1Labels = raw26128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26128step0 raw26128step0Labels permutation56 hz
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical26129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26129 raw26129Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw26129 raw26129Labels = mixedMoment B raw26129step0 raw26129step0Labels := by
      have hz : ∀ j, raw26129 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26129step0 = (fun i j => raw26129 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26129step0 raw26129; decide +kernel
      have hl : raw26129step0Labels = raw26129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26129 raw26129Labels permutation265 hz
    mixedMoment B raw26129step0 raw26129step0Labels = mixedMoment B raw26129step1 raw26129step1Labels := by
      have ha : raw26129step1 = (fun i j => raw26129step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26129step1 raw26129step0; decide +kernel
      have hl : raw26129step1Labels = raw26129step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26129step0 raw26129step0Labels permutation34 permutation2
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical26130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26130 raw26130Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw26130 raw26130Labels = mixedMoment B raw26130step0 raw26130step0Labels := by
      have hz : ∀ j, raw26130 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26130step0 = (fun i j => raw26130 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26130step0 raw26130; decide +kernel
      have hl : raw26130step0Labels = raw26130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26130 raw26130Labels permutation520 hz
    mixedMoment B raw26130step0 raw26130step0Labels = mixedMoment B raw26130step1 raw26130step1Labels := by
      have hz : ∀ j, raw26130step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26130step1 = (fun i j => raw26130step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26130step1 raw26130step0; decide +kernel
      have hl : raw26130step1Labels = raw26130step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26130step0 raw26130step0Labels permutation56 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical26131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26131 raw26131Labels = mixedMoment B node876 node876Labels := by
  calc
    mixedMoment B raw26131 raw26131Labels = mixedMoment B raw26131step0 raw26131step0Labels := by
      have ha : raw26131step0 = (fun i j => raw26131 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26131step0 raw26131; decide +kernel
      have hl : raw26131step0Labels = raw26131Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26131 raw26131Labels permutation178 permutation2
    _ = mixedMoment B node876 node876Labels := by rfl

theorem canonical26132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26132 raw26132Labels = mixedMoment B node883 node883Labels := by
  calc
    mixedMoment B raw26132 raw26132Labels = mixedMoment B raw26132step0 raw26132step0Labels := by
      have hz : ∀ j, raw26132 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26132step0 = (fun i j => raw26132 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26132step0 raw26132; decide +kernel
      have hl : raw26132step0Labels = raw26132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26132 raw26132Labels permutation265 hz
    mixedMoment B raw26132step0 raw26132step0Labels = mixedMoment B raw26132step1 raw26132step1Labels := by
      have ha : raw26132step1 = (fun i j => raw26132step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26132step1 raw26132step0; decide +kernel
      have hl : raw26132step1Labels = raw26132step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26132step0 raw26132step0Labels permutation34 permutation2
    _ = mixedMoment B node883 node883Labels := by rfl

theorem canonical26133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26133 raw26133Labels = mixedMoment B node891 node891Labels := by
  calc
    mixedMoment B raw26133 raw26133Labels = mixedMoment B raw26133step0 raw26133step0Labels := by
      have hz : ∀ j, raw26133 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26133step0 = (fun i j => raw26133 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26133step0 raw26133; decide +kernel
      have hl : raw26133step0Labels = raw26133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26133 raw26133Labels permutation265 hz
    _ = mixedMoment B node891 node891Labels := by rfl

theorem canonical26134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26134 raw26134Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw26134 raw26134Labels = mixedMoment B raw26134step0 raw26134step0Labels := by
      have hz : ∀ j, raw26134 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26134step0 = (fun i j => raw26134 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26134step0 raw26134; decide +kernel
      have hl : raw26134step0Labels = raw26134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26134 raw26134Labels permutation265 hz
    mixedMoment B raw26134step0 raw26134step0Labels = mixedMoment B raw26134step1 raw26134step1Labels := by
      have ha : raw26134step1 = (fun i j => raw26134step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26134step1 raw26134step0; decide +kernel
      have hl : raw26134step1Labels = raw26134step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26134step0 raw26134step0Labels permutation34 permutation2
    _ = mixedMoment B node881 node881Labels := by rfl

theorem canonical26179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26179 raw26179Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw26179 raw26179Labels = mixedMoment B raw26179step0 raw26179step0Labels := by
      have hz : ∀ j, raw26179 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26179step0 = (fun i j => raw26179 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26179step0 raw26179; decide +kernel
      have hl : raw26179step0Labels = raw26179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26179 raw26179Labels permutation265 hz
    mixedMoment B raw26179step0 raw26179step0Labels = mixedMoment B raw26179step1 raw26179step1Labels := by
      have ha : raw26179step1 = (fun i j => raw26179step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26179step1 raw26179step0; decide +kernel
      have hl : raw26179step1Labels = raw26179step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26179step0 raw26179step0Labels permutation34 permutation2
    _ = mixedMoment B node999 node999Labels := by rfl

theorem canonical26180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26180 raw26180Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw26180 raw26180Labels = mixedMoment B raw26180step0 raw26180step0Labels := by
      have ha : raw26180step0 = (fun i j => raw26180 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26180step0 raw26180; decide +kernel
      have hl : raw26180step0Labels = raw26180Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26180 raw26180Labels permutation154 permutation2
    _ = mixedMoment B node1996 node1996Labels := by rfl

theorem canonical26181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26181 raw26181Labels = mixedMoment B node1944 node1944Labels := by
  calc
    mixedMoment B raw26181 raw26181Labels = mixedMoment B raw26181step0 raw26181step0Labels := by
      have hz : ∀ j, raw26181 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26181step0 = (fun i j => raw26181 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26181step0 raw26181; decide +kernel
      have hl : raw26181step0Labels = raw26181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26181 raw26181Labels permutation265 hz
    mixedMoment B raw26181step0 raw26181step0Labels = mixedMoment B raw26181step1 raw26181step1Labels := by
      have ha : raw26181step1 = (fun i j => raw26181step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26181step1 raw26181step0; decide +kernel
      have hl : raw26181step1Labels = raw26181step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26181step0 raw26181step0Labels permutation34 permutation2
    _ = mixedMoment B node1944 node1944Labels := by rfl

theorem canonical26182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26182 raw26182Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw26182 raw26182Labels = mixedMoment B raw26182step0 raw26182step0Labels := by
      have hz : ∀ j, raw26182 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26182step0 = (fun i j => raw26182 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26182step0 raw26182; decide +kernel
      have hl : raw26182step0Labels = raw26182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26182 raw26182Labels permutation265 hz
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical26183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26183 raw26183Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw26183 raw26183Labels = mixedMoment B raw26183step0 raw26183step0Labels := by
      have hz : ∀ j, raw26183 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26183step0 = (fun i j => raw26183 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26183step0 raw26183; decide +kernel
      have hl : raw26183step0Labels = raw26183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26183 raw26183Labels permutation520 hz
    mixedMoment B raw26183step0 raw26183step0Labels = mixedMoment B raw26183step1 raw26183step1Labels := by
      have hz : ∀ j, raw26183step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26183step1 = (fun i j => raw26183step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26183step1 raw26183step0; decide +kernel
      have hl : raw26183step1Labels = raw26183step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26183step0 raw26183step0Labels permutation56 hz
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical26184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26184 raw26184Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw26184 raw26184Labels = mixedMoment B raw26184step0 raw26184step0Labels := by
      have hz : ∀ j, raw26184 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26184step0 = (fun i j => raw26184 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26184step0 raw26184; decide +kernel
      have hl : raw26184step0Labels = raw26184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26184 raw26184Labels permutation265 hz
    mixedMoment B raw26184step0 raw26184step0Labels = mixedMoment B raw26184step1 raw26184step1Labels := by
      have ha : raw26184step1 = (fun i j => raw26184step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26184step1 raw26184step0; decide +kernel
      have hl : raw26184step1Labels = raw26184step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26184step0 raw26184step0Labels permutation34 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical26185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26185 raw26185Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw26185 raw26185Labels = mixedMoment B raw26185step0 raw26185step0Labels := by
      have hz : ∀ j, raw26185 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26185step0 = (fun i j => raw26185 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26185step0 raw26185; decide +kernel
      have hl : raw26185step0Labels = raw26185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26185 raw26185Labels permutation520 hz
    mixedMoment B raw26185step0 raw26185step0Labels = mixedMoment B raw26185step1 raw26185step1Labels := by
      have hz : ∀ j, raw26185step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26185step1 = (fun i j => raw26185step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26185step1 raw26185step0; decide +kernel
      have hl : raw26185step1Labels = raw26185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26185step0 raw26185step0Labels permutation56 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical26193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26193 raw26193Labels = mixedMoment B node1638 node1638Labels := by
  calc
    _ = mixedMoment B node1638 node1638Labels := by rfl

theorem canonical26194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26194 raw26194Labels = mixedMoment B node1638 node1638Labels := by
  calc
    mixedMoment B raw26194 raw26194Labels = mixedMoment B raw26194step0 raw26194step0Labels := by
      have ha : raw26194step0 = (fun i j => raw26194 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26194step0 raw26194; decide +kernel
      have hl : raw26194step0Labels = raw26194Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26194 raw26194Labels permutation176 permutation2
    _ = mixedMoment B node1638 node1638Labels := by rfl

theorem canonical26195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26195 raw26195Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw26195 raw26195Labels = mixedMoment B raw26195step0 raw26195step0Labels := by
      have ha : raw26195step0 = (fun i j => raw26195 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26195step0 raw26195; decide +kernel
      have hl : raw26195step0Labels = raw26195Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26195 raw26195Labels permutation154 permutation2
    _ = mixedMoment B node1699 node1699Labels := by rfl

theorem canonical26196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26196 raw26196Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26196 raw26196Labels = mixedMoment B raw26196step0 raw26196step0Labels := by
      have ha : raw26196step0 = (fun i j => raw26196 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26196step0 raw26196; decide +kernel
      have hl : raw26196step0Labels = raw26196Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26196 raw26196Labels permutation156 permutation2
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical26200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26200 raw26200Labels = mixedMoment B node805 node805Labels := by
  calc
    mixedMoment B raw26200 raw26200Labels = mixedMoment B raw26200step0 raw26200step0Labels := by
      have ha : raw26200step0 = (fun i j => raw26200 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26200step0 raw26200; decide +kernel
      have hl : raw26200step0Labels = raw26200Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26200 raw26200Labels permutation194 permutation2
    _ = mixedMoment B node805 node805Labels := by rfl

theorem canonical26201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26201 raw26201Labels = mixedMoment B node805 node805Labels := by
  calc
    mixedMoment B raw26201 raw26201Labels = mixedMoment B raw26201step0 raw26201step0Labels := by
      have ha : raw26201step0 = (fun i j => raw26201 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26201step0 raw26201; decide +kernel
      have hl : raw26201step0Labels = raw26201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26201 raw26201Labels permutation170 permutation2
    _ = mixedMoment B node805 node805Labels := by rfl

theorem canonical26202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26202 raw26202Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw26202 raw26202Labels = mixedMoment B raw26202step0 raw26202step0Labels := by
      have ha : raw26202step0 = (fun i j => raw26202 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26202step0 raw26202; decide +kernel
      have hl : raw26202step0Labels = raw26202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26202 raw26202Labels permutation157 permutation2
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical26203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26203 raw26203Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw26203 raw26203Labels = mixedMoment B raw26203step0 raw26203step0Labels := by
      have ha : raw26203step0 = (fun i j => raw26203 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26203step0 raw26203; decide +kernel
      have hl : raw26203step0Labels = raw26203Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26203 raw26203Labels permutation156 permutation2
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical26204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26204 raw26204Labels = mixedMoment B node550 node550Labels := by
  calc
    mixedMoment B raw26204 raw26204Labels = mixedMoment B raw26204step0 raw26204step0Labels := by
      have ha : raw26204step0 = (fun i j => raw26204 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26204step0 raw26204; decide +kernel
      have hl : raw26204step0Labels = raw26204Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26204 raw26204Labels permutation152 permutation4
    mixedMoment B raw26204step0 raw26204step0Labels = mixedMoment B raw26204step1 raw26204step1Labels := by
      have ha : raw26204step1 = -raw26204step0 := by apply Matrix.ext; change ∀ i j, raw26204step1 i j = -(raw26204step0 i j); unfold raw26204step1 raw26204step0; decide +kernel
      have hl : raw26204step1Labels = raw26204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node550 node550Labels := by rfl

theorem canonical26205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26205 raw26205Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw26205 raw26205Labels = mixedMoment B raw26205step0 raw26205step0Labels := by
      have hz : ∀ j, raw26205 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26205step0 = (fun i j => raw26205 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26205step0 raw26205; decide +kernel
      have hl : raw26205step0Labels = raw26205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26205 raw26205Labels permutation265 hz
    mixedMoment B raw26205step0 raw26205step0Labels = mixedMoment B raw26205step1 raw26205step1Labels := by
      have ha : raw26205step1 = (fun i j => raw26205step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26205step1 raw26205step0; decide +kernel
      have hl : raw26205step1Labels = raw26205step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26205step0 raw26205step0Labels permutation32 permutation4
    mixedMoment B raw26205step1 raw26205step1Labels = mixedMoment B raw26205step2 raw26205step2Labels := by
      have ha : raw26205step2 = -raw26205step1 := by apply Matrix.ext; change ∀ i j, raw26205step2 i j = -(raw26205step1 i j); unfold raw26205step2 raw26205step1; decide +kernel
      have hl : raw26205step2Labels = raw26205step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node850 node850Labels := by rfl

theorem canonical26206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26206 raw26206Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw26206 raw26206Labels = mixedMoment B raw26206step0 raw26206step0Labels := by
      have ha : raw26206step0 = (fun i j => raw26206 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26206step0 raw26206; decide +kernel
      have hl : raw26206step0Labels = raw26206Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26206 raw26206Labels permutation154 permutation2
    _ = mixedMoment B node1636 node1636Labels := by rfl

theorem canonical26207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26207 raw26207Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw26207 raw26207Labels = mixedMoment B raw26207step0 raw26207step0Labels := by
      have ha : raw26207step0 = (fun i j => raw26207 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26207step0 raw26207; decide +kernel
      have hl : raw26207step0Labels = raw26207Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26207 raw26207Labels permutation178 permutation2
    _ = mixedMoment B node1636 node1636Labels := by rfl

theorem canonical26208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26208 raw26208Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw26208 raw26208Labels = mixedMoment B raw26208step0 raw26208step0Labels := by
      have hz : ∀ j, raw26208 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26208step0 = (fun i j => raw26208 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26208step0 raw26208; decide +kernel
      have hl : raw26208step0Labels = raw26208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26208 raw26208Labels permutation520 hz
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical26209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26209 raw26209Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26209 raw26209Labels = mixedMoment B raw26209step0 raw26209step0Labels := by
      have ha : raw26209step0 = (fun i j => raw26209 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26209step0 raw26209; decide +kernel
      have hl : raw26209step0Labels = raw26209Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26209 raw26209Labels permutation154 permutation2
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical26210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26210 raw26210Labels = mixedMoment B node537 node537Labels := by
  calc
    mixedMoment B raw26210 raw26210Labels = mixedMoment B raw26210step0 raw26210step0Labels := by
      have ha : raw26210step0 = (fun i j => raw26210 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26210step0 raw26210; decide +kernel
      have hl : raw26210step0Labels = raw26210Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26210 raw26210Labels permutation188 permutation2
    _ = mixedMoment B node537 node537Labels := by rfl

theorem canonical26211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26211 raw26211Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw26211 raw26211Labels = mixedMoment B raw26211step0 raw26211step0Labels := by
      have ha : raw26211step0 = (fun i j => raw26211 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26211step0 raw26211; decide +kernel
      have hl : raw26211step0Labels = raw26211Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26211 raw26211Labels permutation188 permutation2
    _ = mixedMoment B node732 node732Labels := by rfl

theorem canonical26212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26212 raw26212Labels = mixedMoment B node810 node810Labels := by
  calc
    mixedMoment B raw26212 raw26212Labels = mixedMoment B raw26212step0 raw26212step0Labels := by
      have hz : ∀ j, raw26212 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26212step0 = (fun i j => raw26212 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26212step0 raw26212; decide +kernel
      have hl : raw26212step0Labels = raw26212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26212 raw26212Labels permutation520 hz
    mixedMoment B raw26212step0 raw26212step0Labels = mixedMoment B raw26212step1 raw26212step1Labels := by
      have ha : raw26212step1 = (fun i j => raw26212step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26212step1 raw26212step0; decide +kernel
      have hl : raw26212step1Labels = raw26212step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26212step0 raw26212step0Labels permutation38 permutation2
    _ = mixedMoment B node810 node810Labels := by rfl

theorem canonical26213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26213 raw26213Labels = mixedMoment B node805 node805Labels := by
  calc
    mixedMoment B raw26213 raw26213Labels = mixedMoment B raw26213step0 raw26213step0Labels := by
      have ha : raw26213step0 = (fun i j => raw26213 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26213step0 raw26213; decide +kernel
      have hl : raw26213step0Labels = raw26213Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26213 raw26213Labels permutation188 permutation2
    _ = mixedMoment B node805 node805Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node732 node732Labels = Sparse.eval nodeValue732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 732) = mixedMoment B node732 node732Labels := rfl
  simpa [nodeValue732, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node805 node805Labels = 0 := by
  exact mixedMoment_order_one B hB node805 node805Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node810 node810Labels = 0 := by
  exact mixedMoment_order_one B hB node810 node810Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node783 node783Labels = Sparse.eval nodeValue783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 783) = mixedMoment B node783 node783Labels := rfl
  simpa [nodeValue783, Sparse.eval] using hc.symm

theorem sound786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node786 node786Labels = Sparse.eval nodeValue786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 786) = mixedMoment B node786 node786Labels := rfl
  simpa [nodeValue786, Sparse.eval] using hc.symm

theorem sound803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node803 node803Labels = Sparse.eval nodeValue803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 803) = mixedMoment B node803 node803Labels := rfl
  simpa [nodeValue803, Sparse.eval] using hc.symm

theorem sound805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node805 node805Labels = Sparse.eval nodeValue805 (mixedVector B) := by
  simpa only [nodeValue805, Sparse.eval_nil] using zero805 B _hB _hF

theorem sound810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node810 node810Labels = Sparse.eval nodeValue810 (mixedVector B) := by
  simpa only [nodeValue810, Sparse.eval_nil] using zero810 B _hB _hF

theorem sound822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node822 node822Labels = Sparse.eval nodeValue822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 822) = mixedMoment B node822 node822Labels := rfl
  simpa [nodeValue822, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node850 node850Labels = 0 := by
  exact mixedMoment_order_one B hB node850 node850Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero883 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node883 node883Labels = 0 := by
  exact mixedMoment_order_one B hB node883 node883Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node850 node850Labels = Sparse.eval nodeValue850 (mixedVector B) := by
  simpa only [nodeValue850, Sparse.eval_nil] using zero850 B _hB _hF

theorem sound876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node876 node876Labels = Sparse.eval nodeValue876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 876) = mixedMoment B node876 node876Labels := rfl
  simpa [nodeValue876, Sparse.eval] using hc.symm

theorem sound881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node881 node881Labels = Sparse.eval nodeValue881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 881) = mixedMoment B node881 node881Labels := rfl
  simpa [nodeValue881, Sparse.eval] using hc.symm

theorem sound883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node883 node883Labels = Sparse.eval nodeValue883 (mixedVector B) := by
  simpa only [nodeValue883, Sparse.eval_nil] using zero883 B _hB _hF

theorem sound891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node891 node891Labels = Sparse.eval nodeValue891 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 891) = mixedMoment B node891 node891Labels := rfl
  simpa [nodeValue891, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node918 node918Labels = 0 := by
  exact mixedMoment_alpha B hF node918 node918Labels 1 permutation161
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node918 node918Labels = Sparse.eval nodeValue918 (mixedVector B) := by
  simpa only [nodeValue918, Sparse.eval_nil] using zero918 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node996 node996Labels = 0 := by
  exact mixedMoment_alpha B hF node996 node996Labels 1 permutation216
    (by decide +kernel)

theorem zero1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1004 node1004Labels = 0 := by
  exact mixedMoment_order_one B hB node1004 node1004Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node996 node996Labels = Sparse.eval nodeValue996 (mixedVector B) := by
  simpa only [nodeValue996, Sparse.eval_nil] using zero996 B _hB _hF

theorem sound998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node998 node998Labels = Sparse.eval nodeValue998 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 998) = mixedMoment B node998 node998Labels := rfl
  simpa [nodeValue998, Sparse.eval] using hc.symm

theorem sound999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node999 node999Labels = Sparse.eval nodeValue999 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 999) = mixedMoment B node999 node999Labels := rfl
  simpa [nodeValue999, Sparse.eval] using hc.symm

theorem sound1000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1000 node1000Labels = Sparse.eval nodeValue1000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1000) = mixedMoment B node1000 node1000Labels := rfl
  simpa [nodeValue1000, Sparse.eval] using hc.symm

theorem sound1001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1001 node1001Labels = Sparse.eval nodeValue1001 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1001) = mixedMoment B node1001 node1001Labels := rfl
  simpa [nodeValue1001, Sparse.eval] using hc.symm

theorem sound1004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1004 node1004Labels = Sparse.eval nodeValue1004 (mixedVector B) := by
  simpa only [nodeValue1004, Sparse.eval_nil] using zero1004 B _hB _hF

theorem sound1005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1005 node1005Labels = Sparse.eval nodeValue1005 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1005) = mixedMoment B node1005 node1005Labels := rfl
  simpa [nodeValue1005, Sparse.eval] using hc.symm

theorem sound1006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1006 node1006Labels = Sparse.eval nodeValue1006 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1006) = mixedMoment B node1006 node1006Labels := rfl
  simpa [nodeValue1006, Sparse.eval] using hc.symm

theorem sound1008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1008 node1008Labels = Sparse.eval nodeValue1008 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1008) = mixedMoment B node1008 node1008Labels := rfl
  simpa [nodeValue1008, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1071 node1071Labels = Sparse.eval nodeValue1071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1071) = mixedMoment B node1071 node1071Labels := rfl
  simpa [nodeValue1071, Sparse.eval] using hc.symm

theorem sound1073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1073 node1073Labels = Sparse.eval nodeValue1073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1073) = mixedMoment B node1073 node1073Labels := rfl
  simpa [nodeValue1073, Sparse.eval] using hc.symm

theorem sound1078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1078 node1078Labels = Sparse.eval nodeValue1078 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1078) = mixedMoment B node1078 node1078Labels := rfl
  simpa [nodeValue1078, Sparse.eval] using hc.symm

theorem sound1080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1080 node1080Labels = Sparse.eval nodeValue1080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1080) = mixedMoment B node1080 node1080Labels := rfl
  simpa [nodeValue1080, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1636 node1636Labels = Sparse.eval nodeValue1636 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1636) = mixedMoment B node1636 node1636Labels := rfl
  simpa [nodeValue1636, Sparse.eval] using hc.symm

theorem sound1638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1638 node1638Labels = Sparse.eval nodeValue1638 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1638) = mixedMoment B node1638 node1638Labels := rfl
  simpa [nodeValue1638, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1698 node1698Labels = 0 := by
  exact mixedMoment_alpha B hF node1698 node1698Labels 1 permutation434
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1698 node1698Labels = Sparse.eval nodeValue1698 (mixedVector B) := by
  simpa only [nodeValue1698, Sparse.eval_nil] using zero1698 B _hB _hF

theorem sound1699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1699 node1699Labels = Sparse.eval nodeValue1699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1699) = mixedMoment B node1699 node1699Labels := rfl
  simpa [nodeValue1699, Sparse.eval] using hc.symm

theorem sound1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1706 node1706Labels = Sparse.eval nodeValue1706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1706) = mixedMoment B node1706 node1706Labels := rfl
  simpa [nodeValue1706, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1944 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1944 node1944Labels = 0 := by
  exact mixedMoment_order_one B hB node1944 node1944Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1945 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1945 node1945Labels = 0 := by
  exact mixedMoment_order_one B hB node1945 node1945Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1947 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1947 node1947Labels = 0 := by
  exact mixedMoment_order_one B hB node1947 node1947Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1944 node1944Labels = Sparse.eval nodeValue1944 (mixedVector B) := by
  simpa only [nodeValue1944, Sparse.eval_nil] using zero1944 B _hB _hF

theorem sound1945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1945 node1945Labels = Sparse.eval nodeValue1945 (mixedVector B) := by
  simpa only [nodeValue1945, Sparse.eval_nil] using zero1945 B _hB _hF

theorem sound1946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1946 node1946Labels = Sparse.eval nodeValue1946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1946) = mixedMoment B node1946 node1946Labels := rfl
  simpa [nodeValue1946, Sparse.eval] using hc.symm

theorem sound1947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1947 node1947Labels = Sparse.eval nodeValue1947 (mixedVector B) := by
  simpa only [nodeValue1947, Sparse.eval_nil] using zero1947 B _hB _hF

theorem sound1948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1948 node1948Labels = Sparse.eval nodeValue1948 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1948) = mixedMoment B node1948 node1948Labels := rfl
  simpa [nodeValue1948, Sparse.eval] using hc.symm

theorem sound1949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1949 node1949Labels = Sparse.eval nodeValue1949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1949) = mixedMoment B node1949 node1949Labels := rfl
  simpa [nodeValue1949, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1996 node1996Labels = Sparse.eval nodeValue1996 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1996) = mixedMoment B node1996 node1996Labels := rfl
  simpa [nodeValue1996, Sparse.eval] using hc.symm

theorem sound1997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1997 node1997Labels = Sparse.eval nodeValue1997 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1997) = mixedMoment B node1997 node1997Labels := rfl
  simpa [nodeValue1997, Sparse.eval] using hc.symm

theorem sound1998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1998 node1998Labels = Sparse.eval nodeValue1998 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1998) = mixedMoment B node1998 node1998Labels := rfl
  simpa [nodeValue1998, Sparse.eval] using hc.symm

theorem sound2000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2000 node2000Labels = Sparse.eval nodeValue2000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2000) = mixedMoment B node2000 node2000Labels := rfl
  simpa [nodeValue2000, Sparse.eval] using hc.symm

theorem sound2001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2001 node2001Labels = Sparse.eval nodeValue2001 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2001) = mixedMoment B node2001 node2001Labels := rfl
  simpa [nodeValue2001, Sparse.eval] using hc.symm

theorem sound2002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2002 node2002Labels = Sparse.eval nodeValue2002 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2002) = mixedMoment B node2002 node2002Labels := rfl
  simpa [nodeValue2002, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2227 node2227Labels = 0 := by
  exact mixedMoment_order_one B hB node2227 node2227Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = 0 := by
  exact mixedMoment_order_one B hB node2228 node2228Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2229 node2229Labels = 0 := by
  exact mixedMoment_order_one B hB node2229 node2229Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2207 node2207Labels = Sparse.eval nodeValue2207 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2207) = mixedMoment B node2207 node2207Labels := rfl
  simpa [nodeValue2207, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

theorem sound2217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2217 node2217Labels = Sparse.eval nodeValue2217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2217) = mixedMoment B node2217 node2217Labels := rfl
  simpa [nodeValue2217, Sparse.eval] using hc.symm

theorem sound2220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2220 node2220Labels = Sparse.eval nodeValue2220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2220) = mixedMoment B node2220 node2220Labels := rfl
  simpa [nodeValue2220, Sparse.eval] using hc.symm

theorem sound2221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2221 node2221Labels = Sparse.eval nodeValue2221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2221) = mixedMoment B node2221 node2221Labels := rfl
  simpa [nodeValue2221, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

theorem sound2227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2227 node2227Labels = Sparse.eval nodeValue2227 (mixedVector B) := by
  simpa only [nodeValue2227, Sparse.eval_nil] using zero2227 B _hB _hF

theorem sound2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = Sparse.eval nodeValue2228 (mixedVector B) := by
  simpa only [nodeValue2228, Sparse.eval_nil] using zero2228 B _hB _hF

theorem sound2229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2229 node2229Labels = Sparse.eval nodeValue2229 (mixedVector B) := by
  simpa only [nodeValue2229, Sparse.eval_nil] using zero2229 B _hB _hF

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node537 node537Labels = Sparse.eval nodeValue537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 537) = mixedMoment B node537 node537Labels := rfl
  simpa [nodeValue537, Sparse.eval] using hc.symm

theorem sound550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node550 node550Labels = Sparse.eval nodeValue550 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 550) = mixedMoment B node550 node550Labels := rfl
  simpa [nodeValue550, Sparse.eval] using hc.symm

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

theorem sound4068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4068 node4068Labels = Sparse.eval nodeValue4068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4068) = mixedMoment B node4068 node4068Labels := rfl
  simpa [nodeValue4068, Sparse.eval] using hc.symm

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node598 node598Labels = Sparse.eval nodeValue598 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 598) = mixedMoment B node598 node598Labels := rfl
  simpa [nodeValue598, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources55
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1788 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1788 + difference 1 0) (sourceB1788 + difference 0 1) sourceC1788) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 598) := by
    have ha : (tripleCharges (sourceA1788 + difference 1 0) (sourceB1788 + difference 0 1) sourceC1788) = raw25995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1788 sourceB1788 sourceC1788 difference raw25995; decide +kernel
    rw [ha]
    exact (canonical25995 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1788 + difference 1 1) (sourceB1788 + difference 1 1) sourceC1788) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1788 + difference 1 1) (sourceB1788 + difference 1 1) sourceC1788) = raw25994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1788 sourceB1788 sourceC1788 difference raw25994; decide +kernel
    rw [ha]
    exact (canonical25994 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1788 + difference 1 2) (sourceB1788 + difference 2 1) sourceC1788) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 918) := by
    have ha : (tripleCharges (sourceA1788 + difference 1 2) (sourceB1788 + difference 2 1) sourceC1788) = raw25999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1788 sourceB1788 sourceC1788 difference raw25999; decide +kernel
    rw [ha]
    exact (canonical25999 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1788 + difference 1 3) (sourceB1788 + difference 3 1) sourceC1788) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1788 + difference 1 3) (sourceB1788 + difference 3 1) sourceC1788) = raw21883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1788 sourceB1788 sourceC1788 difference raw21883; decide +kernel
    rw [ha]
    exact (canonical21883 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1788 + difference 1 4) (sourceB1788 + difference 4 1) sourceC1788) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1788 + difference 1 4) (sourceB1788 + difference 4 1) sourceC1788) = raw26000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1788 sourceB1788 sourceC1788 difference raw26000; decide +kernel
    rw [ha]
    exact (canonical26000 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1788 + difference 1 5) (sourceB1788 + difference 5 1) sourceC1788) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1078) := by
    have ha : (tripleCharges (sourceA1788 + difference 1 5) (sourceB1788 + difference 5 1) sourceC1788) = raw26001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1788 sourceB1788 sourceC1788 difference raw26001; decide +kernel
    rw [ha]
    exact (canonical26001 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1788 + sourceB1788) sourceC1788) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1788 + sourceB1788) sourceC1788) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA1788 sourceB1788 sourceC1788 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1788 sourceB1788 sourceC1788
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1788, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources56
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1793 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1793 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1793 + difference 0 0) (sourceB1793 + difference 0 0) sourceC1793) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1006) := by
    have ha : (tripleCharges (sourceA1793 + difference 0 0) (sourceB1793 + difference 0 0) sourceC1793) = raw26074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1793 sourceB1793 sourceC1793 difference raw26074; decide +kernel
    rw [ha]
    exact (canonical26074 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1793 + difference 0 1) (sourceB1793 + difference 1 0) sourceC1793) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2001) := by
    have ha : (tripleCharges (sourceA1793 + difference 0 1) (sourceB1793 + difference 1 0) sourceC1793) = raw26075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1793 sourceB1793 sourceC1793 difference raw26075; decide +kernel
    rw [ha]
    exact (canonical26075 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1793 + difference 0 2) (sourceB1793 + difference 2 0) sourceC1793) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1948) := by
    have ha : (tripleCharges (sourceA1793 + difference 0 2) (sourceB1793 + difference 2 0) sourceC1793) = raw26076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1793 sourceB1793 sourceC1793 difference raw26076; decide +kernel
    rw [ha]
    exact (canonical26076 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1793 + difference 0 3) (sourceB1793 + difference 3 0) sourceC1793) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2221) := by
    have ha : (tripleCharges (sourceA1793 + difference 0 3) (sourceB1793 + difference 3 0) sourceC1793) = raw26077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1793 sourceB1793 sourceC1793 difference raw26077; decide +kernel
    rw [ha]
    exact (canonical26077 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1793 + difference 0 4) (sourceB1793 + difference 4 0) sourceC1793) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA1793 + difference 0 4) (sourceB1793 + difference 4 0) sourceC1793) = raw26078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1793 sourceB1793 sourceC1793 difference raw26078; decide +kernel
    rw [ha]
    exact (canonical26078 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1793 + difference 0 5) (sourceB1793 + difference 5 0) sourceC1793) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1793 + difference 0 5) (sourceB1793 + difference 5 0) sourceC1793) = raw26079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1793 sourceB1793 sourceC1793 difference raw26079; decide +kernel
    rw [ha]
    exact (canonical26079 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1793 + sourceB1793) sourceC1793) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1793 + sourceB1793) sourceC1793) = raw26080 := by
      apply Matrix.ext; unfold doubleCharges sourceA1793 sourceB1793 sourceC1793 raw26080; decide +kernel
    rw [ha]
    exact (canonical26080 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1793 sourceB1793 sourceC1793
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1793, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1795 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1795 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1795 + difference 0 0) (sourceB1795 + difference 0 0) sourceC1795) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1001) := by
    have ha : (tripleCharges (sourceA1795 + difference 0 0) (sourceB1795 + difference 0 0) sourceC1795) = raw26085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1795 sourceB1795 sourceC1795 difference raw26085; decide +kernel
    rw [ha]
    exact (canonical26085 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1795 + difference 0 1) (sourceB1795 + difference 1 0) sourceC1795) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1998) := by
    have ha : (tripleCharges (sourceA1795 + difference 0 1) (sourceB1795 + difference 1 0) sourceC1795) = raw26086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1795 sourceB1795 sourceC1795 difference raw26086; decide +kernel
    rw [ha]
    exact (canonical26086 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1795 + difference 0 2) (sourceB1795 + difference 2 0) sourceC1795) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1946) := by
    have ha : (tripleCharges (sourceA1795 + difference 0 2) (sourceB1795 + difference 2 0) sourceC1795) = raw26087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1795 sourceB1795 sourceC1795 difference raw26087; decide +kernel
    rw [ha]
    exact (canonical26087 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1795 + difference 0 3) (sourceB1795 + difference 3 0) sourceC1795) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1795 + difference 0 3) (sourceB1795 + difference 3 0) sourceC1795) = raw26088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1795 sourceB1795 sourceC1795 difference raw26088; decide +kernel
    rw [ha]
    exact (canonical26088 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1795 + difference 0 4) (sourceB1795 + difference 4 0) sourceC1795) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1795 + difference 0 4) (sourceB1795 + difference 4 0) sourceC1795) = raw26089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1795 sourceB1795 sourceC1795 difference raw26089; decide +kernel
    rw [ha]
    exact (canonical26089 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1795 + difference 0 5) (sourceB1795 + difference 5 0) sourceC1795) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1795 + difference 0 5) (sourceB1795 + difference 5 0) sourceC1795) = raw26090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1795 sourceB1795 sourceC1795 difference raw26090; decide +kernel
    rw [ha]
    exact (canonical26090 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1795 + sourceB1795) sourceC1795) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1795 + sourceB1795) sourceC1795) = raw26091 := by
      apply Matrix.ext; unfold doubleCharges sourceA1795 sourceB1795 sourceC1795 raw26091; decide +kernel
    rw [ha]
    exact (canonical26091 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1795 sourceB1795 sourceC1795
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1795, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1796 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1796 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1796 + difference 0 0) (sourceB1796 + difference 0 0) sourceC1796) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1008) := by
    have ha : (tripleCharges (sourceA1796 + difference 0 0) (sourceB1796 + difference 0 0) sourceC1796) = raw26092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1796 sourceB1796 sourceC1796 difference raw26092; decide +kernel
    rw [ha]
    exact (canonical26092 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1796 + difference 0 1) (sourceB1796 + difference 1 0) sourceC1796) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2002) := by
    have ha : (tripleCharges (sourceA1796 + difference 0 1) (sourceB1796 + difference 1 0) sourceC1796) = raw26093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1796 sourceB1796 sourceC1796 difference raw26093; decide +kernel
    rw [ha]
    exact (canonical26093 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1796 + difference 0 2) (sourceB1796 + difference 2 0) sourceC1796) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1949) := by
    have ha : (tripleCharges (sourceA1796 + difference 0 2) (sourceB1796 + difference 2 0) sourceC1796) = raw26094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1796 sourceB1796 sourceC1796 difference raw26094; decide +kernel
    rw [ha]
    exact (canonical26094 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1796 + difference 0 3) (sourceB1796 + difference 3 0) sourceC1796) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA1796 + difference 0 3) (sourceB1796 + difference 3 0) sourceC1796) = raw26095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1796 sourceB1796 sourceC1796 difference raw26095; decide +kernel
    rw [ha]
    exact (canonical26095 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1796 + difference 0 4) (sourceB1796 + difference 4 0) sourceC1796) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA1796 + difference 0 4) (sourceB1796 + difference 4 0) sourceC1796) = raw26096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1796 sourceB1796 sourceC1796 difference raw26096; decide +kernel
    rw [ha]
    exact (canonical26096 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1796 + difference 0 5) (sourceB1796 + difference 5 0) sourceC1796) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1796 + difference 0 5) (sourceB1796 + difference 5 0) sourceC1796) = raw26097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1796 sourceB1796 sourceC1796 difference raw26097; decide +kernel
    rw [ha]
    exact (canonical26097 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1796 + sourceB1796) sourceC1796) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1796 + sourceB1796) sourceC1796) = raw26098 := by
      apply Matrix.ext; unfold doubleCharges sourceA1796 sourceB1796 sourceC1796 raw26098; decide +kernel
    rw [ha]
    exact (canonical26098 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1796 sourceB1796 sourceC1796
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1796, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1797 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1797 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1797 + difference 0 5) (sourceB1797 + difference 5 0) sourceC1797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1797 + difference 0 5) (sourceB1797 + difference 5 0) sourceC1797) = raw26097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1797 sourceB1797 sourceC1797 difference raw26097; decide +kernel
    rw [ha]
    exact (canonical26097 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1797 + difference 1 5) (sourceB1797 + difference 5 1) sourceC1797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 996) := by
    have ha : (tripleCharges (sourceA1797 + difference 1 5) (sourceB1797 + difference 5 1) sourceC1797) = raw26099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1797 sourceB1797 sourceC1797 difference raw26099; decide +kernel
    rw [ha]
    exact (canonical26099 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1797 + difference 2 5) (sourceB1797 + difference 5 2) sourceC1797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1071) := by
    have ha : (tripleCharges (sourceA1797 + difference 2 5) (sourceB1797 + difference 5 2) sourceC1797) = raw26100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1797 sourceB1797 sourceC1797 difference raw26100; decide +kernel
    rw [ha]
    exact (canonical26100 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1797 + difference 3 5) (sourceB1797 + difference 5 3) sourceC1797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1797 + difference 3 5) (sourceB1797 + difference 5 3) sourceC1797) = raw26101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1797 sourceB1797 sourceC1797 difference raw26101; decide +kernel
    rw [ha]
    exact (canonical26101 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1797 + difference 4 5) (sourceB1797 + difference 5 4) sourceC1797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1797 + difference 4 5) (sourceB1797 + difference 5 4) sourceC1797) = raw26102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1797 sourceB1797 sourceC1797 difference raw26102; decide +kernel
    rw [ha]
    exact (canonical26102 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1797 + difference 5 5) (sourceB1797 + difference 5 5) sourceC1797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1008) := by
    have ha : (tripleCharges (sourceA1797 + difference 5 5) (sourceB1797 + difference 5 5) sourceC1797) = raw26092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1797 sourceB1797 sourceC1797 difference raw26092; decide +kernel
    rw [ha]
    exact (canonical26092 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1797 + sourceB1797) sourceC1797) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1797 + sourceB1797) sourceC1797) = raw26098 := by
      apply Matrix.ext; unfold doubleCharges sourceA1797 sourceB1797 sourceC1797 raw26098; decide +kernel
    rw [ha]
    exact (canonical26098 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1797 sourceB1797 sourceC1797
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1797, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1798 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1798 + difference 0 0) (sourceB1798 + difference 0 0) sourceC1798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1798 + difference 0 0) (sourceB1798 + difference 0 0) sourceC1798) = raw26103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1798 sourceB1798 sourceC1798 difference raw26103; decide +kernel
    rw [ha]
    exact (canonical26103 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1798 + difference 0 1) (sourceB1798 + difference 1 0) sourceC1798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2000) := by
    have ha : (tripleCharges (sourceA1798 + difference 0 1) (sourceB1798 + difference 1 0) sourceC1798) = raw26104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1798 sourceB1798 sourceC1798 difference raw26104; decide +kernel
    rw [ha]
    exact (canonical26104 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1798 + difference 0 2) (sourceB1798 + difference 2 0) sourceC1798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1947) := by
    have ha : (tripleCharges (sourceA1798 + difference 0 2) (sourceB1798 + difference 2 0) sourceC1798) = raw26105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1798 sourceB1798 sourceC1798 difference raw26105; decide +kernel
    rw [ha]
    exact (canonical26105 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1798 + difference 0 3) (sourceB1798 + difference 3 0) sourceC1798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1798 + difference 0 3) (sourceB1798 + difference 3 0) sourceC1798) = raw26106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1798 sourceB1798 sourceC1798 difference raw26106; decide +kernel
    rw [ha]
    exact (canonical26106 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1798 + difference 0 4) (sourceB1798 + difference 4 0) sourceC1798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1798 + difference 0 4) (sourceB1798 + difference 4 0) sourceC1798) = raw26107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1798 sourceB1798 sourceC1798 difference raw26107; decide +kernel
    rw [ha]
    exact (canonical26107 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1798 + difference 0 5) (sourceB1798 + difference 5 0) sourceC1798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA1798 + difference 0 5) (sourceB1798 + difference 5 0) sourceC1798) = raw26108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1798 sourceB1798 sourceC1798 difference raw26108; decide +kernel
    rw [ha]
    exact (canonical26108 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1798 + sourceB1798) sourceC1798) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1798 + sourceB1798) sourceC1798) = raw26109 := by
      apply Matrix.ext; unfold doubleCharges sourceA1798 sourceB1798 sourceC1798 raw26109; decide +kernel
    rw [ha]
    exact (canonical26109 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1798 sourceB1798 sourceC1798
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1798, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1800 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1800 + difference 0 5) (sourceB1800 + difference 5 0) sourceC1800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA1800 + difference 0 5) (sourceB1800 + difference 5 0) sourceC1800) = raw26108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1800 sourceB1800 sourceC1800 difference raw26108; decide +kernel
    rw [ha]
    exact (canonical26108 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1800 + difference 1 5) (sourceB1800 + difference 5 1) sourceC1800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1800 + difference 1 5) (sourceB1800 + difference 5 1) sourceC1800) = raw26114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1800 sourceB1800 sourceC1800 difference raw26114; decide +kernel
    rw [ha]
    exact (canonical26114 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1800 + difference 2 5) (sourceB1800 + difference 5 2) sourceC1800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1800 + difference 2 5) (sourceB1800 + difference 5 2) sourceC1800) = raw26115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1800 sourceB1800 sourceC1800 difference raw26115; decide +kernel
    rw [ha]
    exact (canonical26115 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1800 + difference 3 5) (sourceB1800 + difference 5 3) sourceC1800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1004) := by
    have ha : (tripleCharges (sourceA1800 + difference 3 5) (sourceB1800 + difference 5 3) sourceC1800) = raw26116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1800 sourceB1800 sourceC1800 difference raw26116; decide +kernel
    rw [ha]
    exact (canonical26116 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1800 + difference 4 5) (sourceB1800 + difference 5 4) sourceC1800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1800 + difference 4 5) (sourceB1800 + difference 5 4) sourceC1800) = raw26117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1800 sourceB1800 sourceC1800 difference raw26117; decide +kernel
    rw [ha]
    exact (canonical26117 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1800 + difference 5 5) (sourceB1800 + difference 5 5) sourceC1800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1800 + difference 5 5) (sourceB1800 + difference 5 5) sourceC1800) = raw26103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1800 sourceB1800 sourceC1800 difference raw26103; decide +kernel
    rw [ha]
    exact (canonical26103 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1800 + sourceB1800) sourceC1800) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1800 + sourceB1800) sourceC1800) = raw26109 := by
      apply Matrix.ext; unfold doubleCharges sourceA1800 sourceB1800 sourceC1800 raw26109; decide +kernel
    rw [ha]
    exact (canonical26109 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1800 sourceB1800 sourceC1800
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1800, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1803 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1803 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1803 + difference 0 0) (sourceB1803 + difference 0 0) sourceC1803) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1803 + difference 0 0) (sourceB1803 + difference 0 0) sourceC1803) = raw26124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1803 sourceB1803 sourceC1803 difference raw26124; decide +kernel
    rw [ha]
    exact (canonical26124 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1803 + difference 0 1) (sourceB1803 + difference 1 0) sourceC1803) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1997) := by
    have ha : (tripleCharges (sourceA1803 + difference 0 1) (sourceB1803 + difference 1 0) sourceC1803) = raw26125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1803 sourceB1803 sourceC1803 difference raw26125; decide +kernel
    rw [ha]
    exact (canonical26125 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1803 + difference 0 2) (sourceB1803 + difference 2 0) sourceC1803) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1945) := by
    have ha : (tripleCharges (sourceA1803 + difference 0 2) (sourceB1803 + difference 2 0) sourceC1803) = raw26126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1803 sourceB1803 sourceC1803 difference raw26126; decide +kernel
    rw [ha]
    exact (canonical26126 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1803 + difference 0 3) (sourceB1803 + difference 3 0) sourceC1803) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1803 + difference 0 3) (sourceB1803 + difference 3 0) sourceC1803) = raw26127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1803 sourceB1803 sourceC1803 difference raw26127; decide +kernel
    rw [ha]
    exact (canonical26127 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1803 + difference 0 4) (sourceB1803 + difference 4 0) sourceC1803) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1803 + difference 0 4) (sourceB1803 + difference 4 0) sourceC1803) = raw26128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1803 sourceB1803 sourceC1803 difference raw26128; decide +kernel
    rw [ha]
    exact (canonical26128 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1803 + difference 0 5) (sourceB1803 + difference 5 0) sourceC1803) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1803 + difference 0 5) (sourceB1803 + difference 5 0) sourceC1803) = raw26129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1803 sourceB1803 sourceC1803 difference raw26129; decide +kernel
    rw [ha]
    exact (canonical26129 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1803 + sourceB1803) sourceC1803) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1803 + sourceB1803) sourceC1803) = raw26130 := by
      apply Matrix.ext; unfold doubleCharges sourceA1803 sourceB1803 sourceC1803 raw26130; decide +kernel
    rw [ha]
    exact (canonical26130 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1803 sourceB1803 sourceC1803
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1803, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1804 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1804 + difference 0 2) (sourceB1804 + difference 2 0) sourceC1804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1945) := by
    have ha : (tripleCharges (sourceA1804 + difference 0 2) (sourceB1804 + difference 2 0) sourceC1804) = raw26126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1804 sourceB1804 sourceC1804 difference raw26126; decide +kernel
    rw [ha]
    exact (canonical26126 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1804 + difference 1 2) (sourceB1804 + difference 2 1) sourceC1804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 876) := by
    have ha : (tripleCharges (sourceA1804 + difference 1 2) (sourceB1804 + difference 2 1) sourceC1804) = raw26131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1804 sourceB1804 sourceC1804 difference raw26131; decide +kernel
    rw [ha]
    exact (canonical26131 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1804 + difference 2 2) (sourceB1804 + difference 2 2) sourceC1804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1804 + difference 2 2) (sourceB1804 + difference 2 2) sourceC1804) = raw26124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1804 sourceB1804 sourceC1804 difference raw26124; decide +kernel
    rw [ha]
    exact (canonical26124 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1804 + difference 3 2) (sourceB1804 + difference 2 3) sourceC1804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 883) := by
    have ha : (tripleCharges (sourceA1804 + difference 3 2) (sourceB1804 + difference 2 3) sourceC1804) = raw26132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1804 sourceB1804 sourceC1804 difference raw26132; decide +kernel
    rw [ha]
    exact (canonical26132 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1804 + difference 4 2) (sourceB1804 + difference 2 4) sourceC1804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 891) := by
    have ha : (tripleCharges (sourceA1804 + difference 4 2) (sourceB1804 + difference 2 4) sourceC1804) = raw26133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1804 sourceB1804 sourceC1804 difference raw26133; decide +kernel
    rw [ha]
    exact (canonical26133 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1804 + difference 5 2) (sourceB1804 + difference 2 5) sourceC1804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 881) := by
    have ha : (tripleCharges (sourceA1804 + difference 5 2) (sourceB1804 + difference 2 5) sourceC1804) = raw26134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1804 sourceB1804 sourceC1804 difference raw26134; decide +kernel
    rw [ha]
    exact (canonical26134 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1804 + sourceB1804) sourceC1804) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1804 + sourceB1804) sourceC1804) = raw26130 := by
      apply Matrix.ext; unfold doubleCharges sourceA1804 sourceB1804 sourceC1804 raw26130; decide +kernel
    rw [ha]
    exact (canonical26130 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1804 sourceB1804 sourceC1804
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1804, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1807 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1807 + difference 0 0) (sourceB1807 + difference 0 0) sourceC1807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1807 + difference 0 0) (sourceB1807 + difference 0 0) sourceC1807) = raw26179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1807 sourceB1807 sourceC1807 difference raw26179; decide +kernel
    rw [ha]
    exact (canonical26179 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1807 + difference 0 1) (sourceB1807 + difference 1 0) sourceC1807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1996) := by
    have ha : (tripleCharges (sourceA1807 + difference 0 1) (sourceB1807 + difference 1 0) sourceC1807) = raw26180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1807 sourceB1807 sourceC1807 difference raw26180; decide +kernel
    rw [ha]
    exact (canonical26180 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1807 + difference 0 2) (sourceB1807 + difference 2 0) sourceC1807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1944) := by
    have ha : (tripleCharges (sourceA1807 + difference 0 2) (sourceB1807 + difference 2 0) sourceC1807) = raw26181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1807 sourceB1807 sourceC1807 difference raw26181; decide +kernel
    rw [ha]
    exact (canonical26181 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1807 + difference 0 3) (sourceB1807 + difference 3 0) sourceC1807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1807 + difference 0 3) (sourceB1807 + difference 3 0) sourceC1807) = raw26182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1807 sourceB1807 sourceC1807 difference raw26182; decide +kernel
    rw [ha]
    exact (canonical26182 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1807 + difference 0 4) (sourceB1807 + difference 4 0) sourceC1807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1807 + difference 0 4) (sourceB1807 + difference 4 0) sourceC1807) = raw26183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1807 sourceB1807 sourceC1807 difference raw26183; decide +kernel
    rw [ha]
    exact (canonical26183 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1807 + difference 0 5) (sourceB1807 + difference 5 0) sourceC1807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1807 + difference 0 5) (sourceB1807 + difference 5 0) sourceC1807) = raw26184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1807 sourceB1807 sourceC1807 difference raw26184; decide +kernel
    rw [ha]
    exact (canonical26184 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1807 + sourceB1807) sourceC1807) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1807 + sourceB1807) sourceC1807) = raw26185 := by
      apply Matrix.ext; unfold doubleCharges sourceA1807 sourceB1807 sourceC1807 raw26185; decide +kernel
    rw [ha]
    exact (canonical26185 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1807 sourceB1807 sourceC1807
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1807, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1809 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1809 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1809 + difference 0 0) (sourceB1809 + difference 0 0) sourceC1809) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 786) := by
    have ha : (tripleCharges (sourceA1809 + difference 0 0) (sourceB1809 + difference 0 0) sourceC1809) = raw22061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1809 sourceB1809 sourceC1809 difference raw22061; decide +kernel
    rw [ha]
    exact (canonical22061 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1809 + difference 0 1) (sourceB1809 + difference 1 0) sourceC1809) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1638) := by
    have ha : (tripleCharges (sourceA1809 + difference 0 1) (sourceB1809 + difference 1 0) sourceC1809) = raw26193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1809 sourceB1809 sourceC1809 difference raw26193; decide +kernel
    rw [ha]
    exact (canonical26193 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1809 + difference 0 2) (sourceB1809 + difference 2 0) sourceC1809) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1638) := by
    have ha : (tripleCharges (sourceA1809 + difference 0 2) (sourceB1809 + difference 2 0) sourceC1809) = raw26194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1809 sourceB1809 sourceC1809 difference raw26194; decide +kernel
    rw [ha]
    exact (canonical26194 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1809 + difference 0 3) (sourceB1809 + difference 3 0) sourceC1809) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1809 + difference 0 3) (sourceB1809 + difference 3 0) sourceC1809) = raw22058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1809 sourceB1809 sourceC1809 difference raw22058; decide +kernel
    rw [ha]
    exact (canonical22058 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1809 + difference 0 4) (sourceB1809 + difference 4 0) sourceC1809) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1809 + difference 0 4) (sourceB1809 + difference 4 0) sourceC1809) = raw26195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1809 sourceB1809 sourceC1809 difference raw26195; decide +kernel
    rw [ha]
    exact (canonical26195 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1809 + difference 0 5) (sourceB1809 + difference 5 0) sourceC1809) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1809 + difference 0 5) (sourceB1809 + difference 5 0) sourceC1809) = raw26196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1809 sourceB1809 sourceC1809 difference raw26196; decide +kernel
    rw [ha]
    exact (canonical26196 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1809 + sourceB1809) sourceC1809) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1809 + sourceB1809) sourceC1809) = raw22064 := by
      apply Matrix.ext; unfold doubleCharges sourceA1809 sourceB1809 sourceC1809 raw22064; decide +kernel
    rw [ha]
    exact (canonical22064 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1809 sourceB1809 sourceC1809
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1809, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1811 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1811 + difference 0 5) (sourceB1811 + difference 5 0) sourceC1811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1811 + difference 0 5) (sourceB1811 + difference 5 0) sourceC1811) = raw26196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1811 sourceB1811 sourceC1811 difference raw26196; decide +kernel
    rw [ha]
    exact (canonical26196 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1811 + difference 1 5) (sourceB1811 + difference 5 1) sourceC1811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 805) := by
    have ha : (tripleCharges (sourceA1811 + difference 1 5) (sourceB1811 + difference 5 1) sourceC1811) = raw26200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1811 sourceB1811 sourceC1811 difference raw26200; decide +kernel
    rw [ha]
    exact (canonical26200 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1811 + difference 2 5) (sourceB1811 + difference 5 2) sourceC1811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 805) := by
    have ha : (tripleCharges (sourceA1811 + difference 2 5) (sourceB1811 + difference 5 2) sourceC1811) = raw26201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1811 sourceB1811 sourceC1811 difference raw26201; decide +kernel
    rw [ha]
    exact (canonical26201 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1811 + difference 3 5) (sourceB1811 + difference 5 3) sourceC1811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1811 + difference 3 5) (sourceB1811 + difference 5 3) sourceC1811) = raw26202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1811 sourceB1811 sourceC1811 difference raw26202; decide +kernel
    rw [ha]
    exact (canonical26202 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1811 + difference 4 5) (sourceB1811 + difference 5 4) sourceC1811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1811 + difference 4 5) (sourceB1811 + difference 5 4) sourceC1811) = raw26203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1811 sourceB1811 sourceC1811 difference raw26203; decide +kernel
    rw [ha]
    exact (canonical26203 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1811 + difference 5 5) (sourceB1811 + difference 5 5) sourceC1811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 786) := by
    have ha : (tripleCharges (sourceA1811 + difference 5 5) (sourceB1811 + difference 5 5) sourceC1811) = raw22061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1811 sourceB1811 sourceC1811 difference raw22061; decide +kernel
    rw [ha]
    exact (canonical22061 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1811 + sourceB1811) sourceC1811) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1811 + sourceB1811) sourceC1811) = raw22064 := by
      apply Matrix.ext; unfold doubleCharges sourceA1811 sourceB1811 sourceC1811 raw22064; decide +kernel
    rw [ha]
    exact (canonical22064 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1811 sourceB1811 sourceC1811
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1811, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1812 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1812 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1812 + difference 5 0) (sourceB1812 + difference 0 5) sourceC1812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 550) := by
    have ha : (tripleCharges (sourceA1812 + difference 5 0) (sourceB1812 + difference 0 5) sourceC1812) = raw26204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1812 sourceB1812 sourceC1812 difference raw26204; decide +kernel
    rw [ha]
    exact (canonical26204 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1812 + difference 5 1) (sourceB1812 + difference 1 5) sourceC1812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1812 + difference 5 1) (sourceB1812 + difference 1 5) sourceC1812) = raw26205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1812 sourceB1812 sourceC1812 difference raw26205; decide +kernel
    rw [ha]
    exact (canonical26205 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1812 + difference 5 2) (sourceB1812 + difference 2 5) sourceC1812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1812 + difference 5 2) (sourceB1812 + difference 2 5) sourceC1812) = raw25543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1812 sourceB1812 sourceC1812 difference raw25543; decide +kernel
    rw [ha]
    exact (canonical25543 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1812 + difference 5 3) (sourceB1812 + difference 3 5) sourceC1812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1812 + difference 5 3) (sourceB1812 + difference 3 5) sourceC1812) = raw23891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1812 sourceB1812 sourceC1812 difference raw23891; decide +kernel
    rw [ha]
    exact (canonical23891 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1812 + difference 5 4) (sourceB1812 + difference 4 5) sourceC1812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1812 + difference 5 4) (sourceB1812 + difference 4 5) sourceC1812) = raw23890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1812 sourceB1812 sourceC1812 difference raw23890; decide +kernel
    rw [ha]
    exact (canonical23890 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1812 + difference 5 5) (sourceB1812 + difference 5 5) sourceC1812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 822) := by
    have ha : (tripleCharges (sourceA1812 + difference 5 5) (sourceB1812 + difference 5 5) sourceC1812) = raw23917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1812 sourceB1812 sourceC1812 difference raw23917; decide +kernel
    rw [ha]
    exact (canonical23917 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1812 + sourceB1812) sourceC1812) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1812 + sourceB1812) sourceC1812) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1812 sourceB1812 sourceC1812 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1812 sourceB1812 sourceC1812
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1812, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1813 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1813 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1813 + difference 0 0) (sourceB1813 + difference 0 0) sourceC1813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1813 + difference 0 0) (sourceB1813 + difference 0 0) sourceC1813) = raw22068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1813 sourceB1813 sourceC1813 difference raw22068; decide +kernel
    rw [ha]
    exact (canonical22068 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1813 + difference 0 1) (sourceB1813 + difference 1 0) sourceC1813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA1813 + difference 0 1) (sourceB1813 + difference 1 0) sourceC1813) = raw26206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1813 sourceB1813 sourceC1813 difference raw26206; decide +kernel
    rw [ha]
    exact (canonical26206 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1813 + difference 0 2) (sourceB1813 + difference 2 0) sourceC1813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA1813 + difference 0 2) (sourceB1813 + difference 2 0) sourceC1813) = raw26207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1813 sourceB1813 sourceC1813 difference raw26207; decide +kernel
    rw [ha]
    exact (canonical26207 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1813 + difference 0 3) (sourceB1813 + difference 3 0) sourceC1813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1813 + difference 0 3) (sourceB1813 + difference 3 0) sourceC1813) = raw22065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1813 sourceB1813 sourceC1813 difference raw22065; decide +kernel
    rw [ha]
    exact (canonical22065 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1813 + difference 0 4) (sourceB1813 + difference 4 0) sourceC1813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1813 + difference 0 4) (sourceB1813 + difference 4 0) sourceC1813) = raw26208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1813 sourceB1813 sourceC1813 difference raw26208; decide +kernel
    rw [ha]
    exact (canonical26208 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1813 + difference 0 5) (sourceB1813 + difference 5 0) sourceC1813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1813 + difference 0 5) (sourceB1813 + difference 5 0) sourceC1813) = raw26209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1813 sourceB1813 sourceC1813 difference raw26209; decide +kernel
    rw [ha]
    exact (canonical26209 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1813 + sourceB1813) sourceC1813) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1813 + sourceB1813) sourceC1813) = raw22071 := by
      apply Matrix.ext; unfold doubleCharges sourceA1813 sourceB1813 sourceC1813 raw22071; decide +kernel
    rw [ha]
    exact (canonical22071 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1813 sourceB1813 sourceC1813
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1813, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1814 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1814 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1814 + difference 1 0) (sourceB1814 + difference 0 1) sourceC1814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 537) := by
    have ha : (tripleCharges (sourceA1814 + difference 1 0) (sourceB1814 + difference 0 1) sourceC1814) = raw26210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1814 sourceB1814 sourceC1814 difference raw26210; decide +kernel
    rw [ha]
    exact (canonical26210 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1814 + difference 1 1) (sourceB1814 + difference 1 1) sourceC1814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1814 + difference 1 1) (sourceB1814 + difference 1 1) sourceC1814) = raw22068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1814 sourceB1814 sourceC1814 difference raw22068; decide +kernel
    rw [ha]
    exact (canonical22068 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1814 + difference 1 2) (sourceB1814 + difference 2 1) sourceC1814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 732) := by
    have ha : (tripleCharges (sourceA1814 + difference 1 2) (sourceB1814 + difference 2 1) sourceC1814) = raw26211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1814 sourceB1814 sourceC1814 difference raw26211; decide +kernel
    rw [ha]
    exact (canonical26211 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1814 + difference 1 3) (sourceB1814 + difference 3 1) sourceC1814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1814 + difference 1 3) (sourceB1814 + difference 3 1) sourceC1814) = raw22066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1814 sourceB1814 sourceC1814 difference raw22066; decide +kernel
    rw [ha]
    exact (canonical22066 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1814 + difference 1 4) (sourceB1814 + difference 4 1) sourceC1814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1814 + difference 1 4) (sourceB1814 + difference 4 1) sourceC1814) = raw26212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1814 sourceB1814 sourceC1814 difference raw26212; decide +kernel
    rw [ha]
    exact (canonical26212 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1814 + difference 1 5) (sourceB1814 + difference 5 1) sourceC1814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 805) := by
    have ha : (tripleCharges (sourceA1814 + difference 1 5) (sourceB1814 + difference 5 1) sourceC1814) = raw26213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1814 sourceB1814 sourceC1814 difference raw26213; decide +kernel
    rw [ha]
    exact (canonical26213 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1814 + sourceB1814) sourceC1814) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1814 + sourceB1814) sourceC1814) = raw22071 := by
      apply Matrix.ext; unfold doubleCharges sourceA1814 sourceB1814 sourceC1814 raw22071; decide +kernel
    rw [ha]
    exact (canonical22071 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1814 sourceB1814 sourceC1814
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1814, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1520 : Integer.Sparse.reindex keyMap MixedData.row1520 = numericRow1520 := by decide +kernel

theorem numericCheck1520 (x : Master → ℝ) : Integer.Sparse.eval numericRow1520 x =
    (1 : ℝ) * reducedSource1520 x := by
  norm_num [numericRow1520, reducedSource1520, Integer.Sparse.eval, Sparse.eval, nodeValue598, nodeValue918, nodeValue1078, nodeValue1080, nodeValue4085]

theorem reindexCheck1522 : Integer.Sparse.reindex keyMap MixedData.row1522 = numericRow1522 := by decide +kernel

theorem numericCheck1522 (x : Master → ℝ) : Integer.Sparse.eval numericRow1522 x =
    (1 : ℝ) * reducedSource1522 x := by
  norm_num [numericRow1522, reducedSource1522, Integer.Sparse.eval, Sparse.eval, nodeValue1006, nodeValue1948, nodeValue2001, nodeValue2207, nodeValue2221, nodeValue2224, nodeValue4081]

theorem reindexCheck1523 : Integer.Sparse.reindex keyMap MixedData.row1523 = numericRow1523 := by decide +kernel

theorem numericCheck1523 (x : Master → ℝ) : Integer.Sparse.eval numericRow1523 x =
    (1 : ℝ) * reducedSource1523 x := by
  norm_num [numericRow1523, reducedSource1523, Integer.Sparse.eval, Sparse.eval, nodeValue1001, nodeValue1946, nodeValue1998, nodeValue2220, nodeValue2224, nodeValue2230, nodeValue4081]

theorem reindexCheck1524 : Integer.Sparse.reindex keyMap MixedData.row1524 = numericRow1524 := by decide +kernel

theorem numericCheck1524 (x : Master → ℝ) : Integer.Sparse.eval numericRow1524 x =
    (1 : ℝ) * reducedSource1524 x := by
  norm_num [numericRow1524, reducedSource1524, Integer.Sparse.eval, Sparse.eval, nodeValue1008, nodeValue1949, nodeValue2002, nodeValue2217, nodeValue2225, nodeValue4082]

theorem reindexCheck1525 : Integer.Sparse.reindex keyMap MixedData.row1525 = numericRow1525 := by decide +kernel

theorem numericCheck1525 (x : Master → ℝ) : Integer.Sparse.eval numericRow1525 x =
    (1 : ℝ) * reducedSource1525 x := by
  norm_num [numericRow1525, reducedSource1525, Integer.Sparse.eval, Sparse.eval, nodeValue996, nodeValue1000, nodeValue1008, nodeValue1071, nodeValue2225, nodeValue4082]

theorem reindexCheck1526 : Integer.Sparse.reindex keyMap MixedData.row1526 = numericRow1526 := by decide +kernel

theorem numericCheck1526 (x : Master → ℝ) : Integer.Sparse.eval numericRow1526 x =
    (1 : ℝ) * reducedSource1526 x := by
  norm_num [numericRow1526, reducedSource1526, Integer.Sparse.eval, Sparse.eval, nodeValue1005, nodeValue1947, nodeValue2000, nodeValue2206, nodeValue2216, nodeValue2227, nodeValue4080]

theorem reindexCheck1527 : Integer.Sparse.reindex keyMap MixedData.row1527 = numericRow1527 := by decide +kernel

theorem numericCheck1527 (x : Master → ℝ) : Integer.Sparse.eval numericRow1527 x =
    (1 : ℝ) * reducedSource1527 x := by
  norm_num [numericRow1527, reducedSource1527, Integer.Sparse.eval, Sparse.eval, nodeValue998, nodeValue1004, nodeValue1005, nodeValue1073, nodeValue2227, nodeValue4080]

theorem reindexCheck1528 : Integer.Sparse.reindex keyMap MixedData.row1528 = numericRow1528 := by decide +kernel

theorem numericCheck1528 (x : Master → ℝ) : Integer.Sparse.eval numericRow1528 x =
    (1 : ℝ) * reducedSource1528 x := by
  norm_num [numericRow1528, reducedSource1528, Integer.Sparse.eval, Sparse.eval, nodeValue1000, nodeValue1945, nodeValue1997, nodeValue2215, nodeValue2225, nodeValue2229, nodeValue4082]

theorem reindexCheck1529 : Integer.Sparse.reindex keyMap MixedData.row1529 = numericRow1529 := by decide +kernel

theorem numericCheck1529 (x : Master → ℝ) : Integer.Sparse.eval numericRow1529 x =
    (1 : ℝ) * reducedSource1529 x := by
  norm_num [numericRow1529, reducedSource1529, Integer.Sparse.eval, Sparse.eval, nodeValue876, nodeValue881, nodeValue883, nodeValue891, nodeValue1000, nodeValue1945, nodeValue4082]

theorem reindexCheck1530 : Integer.Sparse.reindex keyMap MixedData.row1530 = numericRow1530 := by decide +kernel

theorem numericCheck1530 (x : Master → ℝ) : Integer.Sparse.eval numericRow1530 x =
    (1 : ℝ) * reducedSource1530 x := by
  norm_num [numericRow1530, reducedSource1530, Integer.Sparse.eval, Sparse.eval, nodeValue999, nodeValue1944, nodeValue1996, nodeValue2203, nodeValue2224, nodeValue2228, nodeValue4081]

theorem reindexCheck1531 : Integer.Sparse.reindex keyMap MixedData.row1531 = numericRow1531 := by decide +kernel

theorem numericCheck1531 (x : Master → ℝ) : Integer.Sparse.eval numericRow1531 x =
    (1 : ℝ) * reducedSource1531 x := by
  norm_num [numericRow1531, reducedSource1531, Integer.Sparse.eval, Sparse.eval, nodeValue786, nodeValue1638, nodeValue1699, nodeValue1706, nodeValue4068]

theorem reindexCheck1532 : Integer.Sparse.reindex keyMap MixedData.row1532 = numericRow1532 := by decide +kernel

theorem numericCheck1532 (x : Master → ℝ) : Integer.Sparse.eval numericRow1532 x =
    (1 : ℝ) * reducedSource1532 x := by
  norm_num [numericRow1532, reducedSource1532, Integer.Sparse.eval, Sparse.eval, nodeValue783, nodeValue786, nodeValue805, nodeValue1706, nodeValue4068]

theorem reindexCheck1533 : Integer.Sparse.reindex keyMap MixedData.row1533 = numericRow1533 := by decide +kernel

theorem numericCheck1533 (x : Master → ℝ) : Integer.Sparse.eval numericRow1533 x =
    (1 : ℝ) * reducedSource1533 x := by
  norm_num [numericRow1533, reducedSource1533, Integer.Sparse.eval, Sparse.eval, nodeValue550, nodeValue803, nodeValue822, nodeValue850, nodeValue4069]

theorem reindexCheck1534 : Integer.Sparse.reindex keyMap MixedData.row1534 = numericRow1534 := by decide +kernel

theorem numericCheck1534 (x : Master → ℝ) : Integer.Sparse.eval numericRow1534 x =
    (1 : ℝ) * reducedSource1534 x := by
  norm_num [numericRow1534, reducedSource1534, Integer.Sparse.eval, Sparse.eval, nodeValue783, nodeValue1636, nodeValue1698, nodeValue1706, nodeValue1708, nodeValue4068]

theorem reindexCheck1535 : Integer.Sparse.reindex keyMap MixedData.row1535 = numericRow1535 := by decide +kernel

theorem numericCheck1535 (x : Master → ℝ) : Integer.Sparse.eval numericRow1535 x =
    (1 : ℝ) * reducedSource1535 x := by
  norm_num [numericRow1535, reducedSource1535, Integer.Sparse.eval, Sparse.eval, nodeValue537, nodeValue732, nodeValue783, nodeValue805, nodeValue810, nodeValue4068]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1520 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1520 (mixedVector B) = 0 := by
  have h598 : mixedVector B (Sum.inr 598) = Sparse.eval nodeValue598 (mixedVector B) := by
    change mixedMoment B node598 node598Labels = _
    exact sound598 B hB hF
  have h918 : mixedVector B (Sum.inr 918) = Sparse.eval nodeValue918 (mixedVector B) := by
    change mixedMoment B node918 node918Labels = _
    exact sound918 B hB hF
  have h1078 : mixedVector B (Sum.inr 1078) = Sparse.eval nodeValue1078 (mixedVector B) := by
    change mixedMoment B node1078 node1078Labels = _
    exact sound1078 B hB hF
  have h1080 : mixedVector B (Sum.inr 1080) = Sparse.eval nodeValue1080 (mixedVector B) := by
    change mixedMoment B node1080 node1080Labels = _
    exact sound1080 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1788, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h598, h918, h1078, h1080, h4085, reducedSource1520] using sourceEq1788 B hB

theorem rowSound1520 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1520 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1520, numericCheck1520, reducedZero1520 B hB hF, mul_zero]

theorem reducedZero1522 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1522 (mixedVector B) = 0 := by
  have h1006 : mixedVector B (Sum.inr 1006) = Sparse.eval nodeValue1006 (mixedVector B) := by
    change mixedMoment B node1006 node1006Labels = _
    exact sound1006 B hB hF
  have h1948 : mixedVector B (Sum.inr 1948) = Sparse.eval nodeValue1948 (mixedVector B) := by
    change mixedMoment B node1948 node1948Labels = _
    exact sound1948 B hB hF
  have h2001 : mixedVector B (Sum.inr 2001) = Sparse.eval nodeValue2001 (mixedVector B) := by
    change mixedMoment B node2001 node2001Labels = _
    exact sound2001 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2221 : mixedVector B (Sum.inr 2221) = Sparse.eval nodeValue2221 (mixedVector B) := by
    change mixedMoment B node2221 node2221Labels = _
    exact sound2221 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1793, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1006, h1948, h2001, h2207, h2221, h2224, h4081, reducedSource1522] using sourceEq1793 B hB

theorem rowSound1522 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1522 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1522, numericCheck1522, reducedZero1522 B hB hF, mul_zero]

theorem reducedZero1523 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1523 (mixedVector B) = 0 := by
  have h1001 : mixedVector B (Sum.inr 1001) = Sparse.eval nodeValue1001 (mixedVector B) := by
    change mixedMoment B node1001 node1001Labels = _
    exact sound1001 B hB hF
  have h1946 : mixedVector B (Sum.inr 1946) = Sparse.eval nodeValue1946 (mixedVector B) := by
    change mixedMoment B node1946 node1946Labels = _
    exact sound1946 B hB hF
  have h1998 : mixedVector B (Sum.inr 1998) = Sparse.eval nodeValue1998 (mixedVector B) := by
    change mixedMoment B node1998 node1998Labels = _
    exact sound1998 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1795, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1001, h1946, h1998, h2220, h2224, h2230, h4081, reducedSource1523] using sourceEq1795 B hB

theorem rowSound1523 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1523 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1523, numericCheck1523, reducedZero1523 B hB hF, mul_zero]

theorem reducedZero1524 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1524 (mixedVector B) = 0 := by
  have h1008 : mixedVector B (Sum.inr 1008) = Sparse.eval nodeValue1008 (mixedVector B) := by
    change mixedMoment B node1008 node1008Labels = _
    exact sound1008 B hB hF
  have h1949 : mixedVector B (Sum.inr 1949) = Sparse.eval nodeValue1949 (mixedVector B) := by
    change mixedMoment B node1949 node1949Labels = _
    exact sound1949 B hB hF
  have h2002 : mixedVector B (Sum.inr 2002) = Sparse.eval nodeValue2002 (mixedVector B) := by
    change mixedMoment B node2002 node2002Labels = _
    exact sound2002 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1796, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1008, h1949, h2002, h2217, h2225, h4082, reducedSource1524] using sourceEq1796 B hB

theorem rowSound1524 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1524 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1524, numericCheck1524, reducedZero1524 B hB hF, mul_zero]

theorem reducedZero1525 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1525 (mixedVector B) = 0 := by
  have h996 : mixedVector B (Sum.inr 996) = Sparse.eval nodeValue996 (mixedVector B) := by
    change mixedMoment B node996 node996Labels = _
    exact sound996 B hB hF
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1008 : mixedVector B (Sum.inr 1008) = Sparse.eval nodeValue1008 (mixedVector B) := by
    change mixedMoment B node1008 node1008Labels = _
    exact sound1008 B hB hF
  have h1071 : mixedVector B (Sum.inr 1071) = Sparse.eval nodeValue1071 (mixedVector B) := by
    change mixedMoment B node1071 node1071Labels = _
    exact sound1071 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1797, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h996, h1000, h1008, h1071, h2225, h4082, reducedSource1525] using sourceEq1797 B hB

theorem rowSound1525 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1525 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1525, numericCheck1525, reducedZero1525 B hB hF, mul_zero]

theorem reducedZero1526 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1526 (mixedVector B) = 0 := by
  have h1005 : mixedVector B (Sum.inr 1005) = Sparse.eval nodeValue1005 (mixedVector B) := by
    change mixedMoment B node1005 node1005Labels = _
    exact sound1005 B hB hF
  have h1947 : mixedVector B (Sum.inr 1947) = Sparse.eval nodeValue1947 (mixedVector B) := by
    change mixedMoment B node1947 node1947Labels = _
    exact sound1947 B hB hF
  have h2000 : mixedVector B (Sum.inr 2000) = Sparse.eval nodeValue2000 (mixedVector B) := by
    change mixedMoment B node2000 node2000Labels = _
    exact sound2000 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1798, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1005, h1947, h2000, h2206, h2216, h2227, h4080, reducedSource1526] using sourceEq1798 B hB

theorem rowSound1526 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1526 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1526, numericCheck1526, reducedZero1526 B hB hF, mul_zero]

theorem reducedZero1527 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1527 (mixedVector B) = 0 := by
  have h998 : mixedVector B (Sum.inr 998) = Sparse.eval nodeValue998 (mixedVector B) := by
    change mixedMoment B node998 node998Labels = _
    exact sound998 B hB hF
  have h1004 : mixedVector B (Sum.inr 1004) = Sparse.eval nodeValue1004 (mixedVector B) := by
    change mixedMoment B node1004 node1004Labels = _
    exact sound1004 B hB hF
  have h1005 : mixedVector B (Sum.inr 1005) = Sparse.eval nodeValue1005 (mixedVector B) := by
    change mixedMoment B node1005 node1005Labels = _
    exact sound1005 B hB hF
  have h1073 : mixedVector B (Sum.inr 1073) = Sparse.eval nodeValue1073 (mixedVector B) := by
    change mixedMoment B node1073 node1073Labels = _
    exact sound1073 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1800, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h998, h1004, h1005, h1073, h2227, h4080, reducedSource1527] using sourceEq1800 B hB

theorem rowSound1527 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1527 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1527, numericCheck1527, reducedZero1527 B hB hF, mul_zero]

theorem reducedZero1528 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1528 (mixedVector B) = 0 := by
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1945 : mixedVector B (Sum.inr 1945) = Sparse.eval nodeValue1945 (mixedVector B) := by
    change mixedMoment B node1945 node1945Labels = _
    exact sound1945 B hB hF
  have h1997 : mixedVector B (Sum.inr 1997) = Sparse.eval nodeValue1997 (mixedVector B) := by
    change mixedMoment B node1997 node1997Labels = _
    exact sound1997 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1803, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1000, h1945, h1997, h2215, h2225, h2229, h4082, reducedSource1528] using sourceEq1803 B hB

theorem rowSound1528 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1528 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1528, numericCheck1528, reducedZero1528 B hB hF, mul_zero]

theorem reducedZero1529 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1529 (mixedVector B) = 0 := by
  have h876 : mixedVector B (Sum.inr 876) = Sparse.eval nodeValue876 (mixedVector B) := by
    change mixedMoment B node876 node876Labels = _
    exact sound876 B hB hF
  have h881 : mixedVector B (Sum.inr 881) = Sparse.eval nodeValue881 (mixedVector B) := by
    change mixedMoment B node881 node881Labels = _
    exact sound881 B hB hF
  have h883 : mixedVector B (Sum.inr 883) = Sparse.eval nodeValue883 (mixedVector B) := by
    change mixedMoment B node883 node883Labels = _
    exact sound883 B hB hF
  have h891 : mixedVector B (Sum.inr 891) = Sparse.eval nodeValue891 (mixedVector B) := by
    change mixedMoment B node891 node891Labels = _
    exact sound891 B hB hF
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1945 : mixedVector B (Sum.inr 1945) = Sparse.eval nodeValue1945 (mixedVector B) := by
    change mixedMoment B node1945 node1945Labels = _
    exact sound1945 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1804, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h876, h881, h883, h891, h1000, h1945, h4082, reducedSource1529] using sourceEq1804 B hB

theorem rowSound1529 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1529 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1529, numericCheck1529, reducedZero1529 B hB hF, mul_zero]

theorem reducedZero1530 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1530 (mixedVector B) = 0 := by
  have h999 : mixedVector B (Sum.inr 999) = Sparse.eval nodeValue999 (mixedVector B) := by
    change mixedMoment B node999 node999Labels = _
    exact sound999 B hB hF
  have h1944 : mixedVector B (Sum.inr 1944) = Sparse.eval nodeValue1944 (mixedVector B) := by
    change mixedMoment B node1944 node1944Labels = _
    exact sound1944 B hB hF
  have h1996 : mixedVector B (Sum.inr 1996) = Sparse.eval nodeValue1996 (mixedVector B) := by
    change mixedMoment B node1996 node1996Labels = _
    exact sound1996 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1807, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h999, h1944, h1996, h2203, h2224, h2228, h4081, reducedSource1530] using sourceEq1807 B hB

theorem rowSound1530 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1530 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1530, numericCheck1530, reducedZero1530 B hB hF, mul_zero]

theorem reducedZero1531 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1531 (mixedVector B) = 0 := by
  have h786 : mixedVector B (Sum.inr 786) = Sparse.eval nodeValue786 (mixedVector B) := by
    change mixedMoment B node786 node786Labels = _
    exact sound786 B hB hF
  have h1638 : mixedVector B (Sum.inr 1638) = Sparse.eval nodeValue1638 (mixedVector B) := by
    change mixedMoment B node1638 node1638Labels = _
    exact sound1638 B hB hF
  have h1699 : mixedVector B (Sum.inr 1699) = Sparse.eval nodeValue1699 (mixedVector B) := by
    change mixedMoment B node1699 node1699Labels = _
    exact sound1699 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1809, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h786, h1638, h1699, h1706, h4068, reducedSource1531] using sourceEq1809 B hB

theorem rowSound1531 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1531 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1531, numericCheck1531, reducedZero1531 B hB hF, mul_zero]

theorem reducedZero1532 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1532 (mixedVector B) = 0 := by
  have h783 : mixedVector B (Sum.inr 783) = Sparse.eval nodeValue783 (mixedVector B) := by
    change mixedMoment B node783 node783Labels = _
    exact sound783 B hB hF
  have h786 : mixedVector B (Sum.inr 786) = Sparse.eval nodeValue786 (mixedVector B) := by
    change mixedMoment B node786 node786Labels = _
    exact sound786 B hB hF
  have h805 : mixedVector B (Sum.inr 805) = Sparse.eval nodeValue805 (mixedVector B) := by
    change mixedMoment B node805 node805Labels = _
    exact sound805 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1811, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h783, h786, h805, h1706, h4068, reducedSource1532] using sourceEq1811 B hB

theorem rowSound1532 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1532 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1532, numericCheck1532, reducedZero1532 B hB hF, mul_zero]

theorem reducedZero1533 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1533 (mixedVector B) = 0 := by
  have h550 : mixedVector B (Sum.inr 550) = Sparse.eval nodeValue550 (mixedVector B) := by
    change mixedMoment B node550 node550Labels = _
    exact sound550 B hB hF
  have h803 : mixedVector B (Sum.inr 803) = Sparse.eval nodeValue803 (mixedVector B) := by
    change mixedMoment B node803 node803Labels = _
    exact sound803 B hB hF
  have h822 : mixedVector B (Sum.inr 822) = Sparse.eval nodeValue822 (mixedVector B) := by
    change mixedMoment B node822 node822Labels = _
    exact sound822 B hB hF
  have h850 : mixedVector B (Sum.inr 850) = Sparse.eval nodeValue850 (mixedVector B) := by
    change mixedMoment B node850 node850Labels = _
    exact sound850 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1812, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h550, h803, h822, h850, h4069, reducedSource1533] using sourceEq1812 B hB

theorem rowSound1533 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1533 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1533, numericCheck1533, reducedZero1533 B hB hF, mul_zero]

theorem reducedZero1534 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1534 (mixedVector B) = 0 := by
  have h783 : mixedVector B (Sum.inr 783) = Sparse.eval nodeValue783 (mixedVector B) := by
    change mixedMoment B node783 node783Labels = _
    exact sound783 B hB hF
  have h1636 : mixedVector B (Sum.inr 1636) = Sparse.eval nodeValue1636 (mixedVector B) := by
    change mixedMoment B node1636 node1636Labels = _
    exact sound1636 B hB hF
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1813, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h783, h1636, h1698, h1706, h1708, h4068, reducedSource1534] using sourceEq1813 B hB

theorem rowSound1534 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1534 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1534, numericCheck1534, reducedZero1534 B hB hF, mul_zero]

theorem reducedZero1535 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1535 (mixedVector B) = 0 := by
  have h537 : mixedVector B (Sum.inr 537) = Sparse.eval nodeValue537 (mixedVector B) := by
    change mixedMoment B node537 node537Labels = _
    exact sound537 B hB hF
  have h732 : mixedVector B (Sum.inr 732) = Sparse.eval nodeValue732 (mixedVector B) := by
    change mixedMoment B node732 node732Labels = _
    exact sound732 B hB hF
  have h783 : mixedVector B (Sum.inr 783) = Sparse.eval nodeValue783 (mixedVector B) := by
    change mixedMoment B node783 node783Labels = _
    exact sound783 B hB hF
  have h805 : mixedVector B (Sum.inr 805) = Sparse.eval nodeValue805 (mixedVector B) := by
    change mixedMoment B node805 node805Labels = _
    exact sound805 B hB hF
  have h810 : mixedVector B (Sum.inr 810) = Sparse.eval nodeValue810 (mixedVector B) := by
    change mixedMoment B node810 node810Labels = _
    exact sound810 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1814, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h537, h732, h783, h805, h810, h4068, reducedSource1535] using sourceEq1814 B hB

theorem rowSound1535 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1535 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1535, numericCheck1535, reducedZero1535 B hB hF, mul_zero]

theorem sourceRowsAt1520 : MixedData.sourceRows (1520 : Fin 2425) =
    MixedData.row1520 := by decide +kernel

theorem sourceRowsAt1521 : MixedData.sourceRows (1521 : Fin 2425) =
    MixedData.row1521 := by decide +kernel

theorem sourceRowsAt1522 : MixedData.sourceRows (1522 : Fin 2425) =
    MixedData.row1522 := by decide +kernel

theorem sourceRowsAt1523 : MixedData.sourceRows (1523 : Fin 2425) =
    MixedData.row1523 := by decide +kernel

theorem sourceRowsAt1524 : MixedData.sourceRows (1524 : Fin 2425) =
    MixedData.row1524 := by decide +kernel

theorem sourceRowsAt1525 : MixedData.sourceRows (1525 : Fin 2425) =
    MixedData.row1525 := by decide +kernel

theorem sourceRowsAt1526 : MixedData.sourceRows (1526 : Fin 2425) =
    MixedData.row1526 := by decide +kernel

theorem sourceRowsAt1527 : MixedData.sourceRows (1527 : Fin 2425) =
    MixedData.row1527 := by decide +kernel

theorem sourceRowsAt1528 : MixedData.sourceRows (1528 : Fin 2425) =
    MixedData.row1528 := by decide +kernel

theorem sourceRowsAt1529 : MixedData.sourceRows (1529 : Fin 2425) =
    MixedData.row1529 := by decide +kernel

theorem sourceRowsAt1530 : MixedData.sourceRows (1530 : Fin 2425) =
    MixedData.row1530 := by decide +kernel

theorem sourceRowsAt1531 : MixedData.sourceRows (1531 : Fin 2425) =
    MixedData.row1531 := by decide +kernel

theorem sourceRowsAt1532 : MixedData.sourceRows (1532 : Fin 2425) =
    MixedData.row1532 := by decide +kernel

theorem sourceRowsAt1533 : MixedData.sourceRows (1533 : Fin 2425) =
    MixedData.row1533 := by decide +kernel

theorem sourceRowsAt1534 : MixedData.sourceRows (1534 : Fin 2425) =
    MixedData.row1534 := by decide +kernel

theorem sourceRowsAt1535 : MixedData.sourceRows (1535 : Fin 2425) =
    MixedData.row1535 := by decide +kernel

theorem chunkSound95_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 95) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1520 ∨ k.val = 1521 ∨ k.val = 1522 ∨ k.val = 1523 ∨ k.val = 1524 ∨ k.val = 1525 ∨ k.val = 1526 ∨ k.val = 1527 ∨ k.val = 1528 ∨ k.val = 1529 ∨ k.val = 1530 ∨ k.val = 1531 ∨ k.val = 1532 ∨ k.val = 1533 ∨ k.val = 1534 ∨ k.val = 1535 := by omega
  rcases heq with h1520 | h1521 | h1522 | h1523 | h1524 | h1525 | h1526 | h1527 | h1528 | h1529 | h1530 | h1531 | h1532 | h1533 | h1534 | h1535
  · have he : k = (1520 : Fin 2425) := Fin.ext h1520
    subst k
    rw [sourceRowsAt1520]
    exact rowSound1520 B hB hF
  · have he : k = (1521 : Fin 2425) := Fin.ext h1521
    subst k
    rw [sourceRowsAt1521]
    exact rowSound1521_e B hB hF
  · have he : k = (1522 : Fin 2425) := Fin.ext h1522
    subst k
    rw [sourceRowsAt1522]
    exact rowSound1522 B hB hF
  · have he : k = (1523 : Fin 2425) := Fin.ext h1523
    subst k
    rw [sourceRowsAt1523]
    exact rowSound1523 B hB hF
  · have he : k = (1524 : Fin 2425) := Fin.ext h1524
    subst k
    rw [sourceRowsAt1524]
    exact rowSound1524 B hB hF
  · have he : k = (1525 : Fin 2425) := Fin.ext h1525
    subst k
    rw [sourceRowsAt1525]
    exact rowSound1525 B hB hF
  · have he : k = (1526 : Fin 2425) := Fin.ext h1526
    subst k
    rw [sourceRowsAt1526]
    exact rowSound1526 B hB hF
  · have he : k = (1527 : Fin 2425) := Fin.ext h1527
    subst k
    rw [sourceRowsAt1527]
    exact rowSound1527 B hB hF
  · have he : k = (1528 : Fin 2425) := Fin.ext h1528
    subst k
    rw [sourceRowsAt1528]
    exact rowSound1528 B hB hF
  · have he : k = (1529 : Fin 2425) := Fin.ext h1529
    subst k
    rw [sourceRowsAt1529]
    exact rowSound1529 B hB hF
  · have he : k = (1530 : Fin 2425) := Fin.ext h1530
    subst k
    rw [sourceRowsAt1530]
    exact rowSound1530 B hB hF
  · have he : k = (1531 : Fin 2425) := Fin.ext h1531
    subst k
    rw [sourceRowsAt1531]
    exact rowSound1531 B hB hF
  · have he : k = (1532 : Fin 2425) := Fin.ext h1532
    subst k
    rw [sourceRowsAt1532]
    exact rowSound1532 B hB hF
  · have he : k = (1533 : Fin 2425) := Fin.ext h1533
    subst k
    rw [sourceRowsAt1533]
    exact rowSound1533 B hB hF
  · have he : k = (1534 : Fin 2425) := Fin.ext h1534
    subst k
    rw [sourceRowsAt1534]
    exact rowSound1534 B hB hF
  · have he : k = (1535 : Fin 2425) := Fin.ext h1535
    subst k
    rw [sourceRowsAt1535]
    exact rowSound1535 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95_e_oai
