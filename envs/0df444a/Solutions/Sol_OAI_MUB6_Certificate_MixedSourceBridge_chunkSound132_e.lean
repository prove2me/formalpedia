-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:49:20.870935+00:00
-- url     : https://prove2.me/submissions/42a3df1c-4e1d-4e78-96f5-b3508e30ae92

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E126
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical291
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37330 raw37330Labels = mixedMoment B node1541 node1541Labels := by
  calc
    mixedMoment B raw37330 raw37330Labels = mixedMoment B raw37330step0 raw37330step0Labels := by
      have hz : ∀ j, raw37330 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37330step0 = (fun i j => raw37330 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37330step0 raw37330; decide +kernel
      have hl : raw37330step0Labels = raw37330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37330 raw37330Labels permutation520 hz
    mixedMoment B raw37330step0 raw37330step0Labels = mixedMoment B raw37330step1 raw37330step1Labels := by
      have hz : ∀ j, raw37330step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37330step1 = (fun i j => raw37330step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37330step1 raw37330step0; decide +kernel
      have hl : raw37330step1Labels = raw37330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37330step0 raw37330step0Labels permutation104 hz
    mixedMoment B raw37330step1 raw37330step1Labels = mixedMoment B raw37330step2 raw37330step2Labels := by
      have hz : ∀ j, raw37330step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw37330step2 = (fun i j => raw37330step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw37330step2 raw37330step1; decide +kernel
      have hl : raw37330step2Labels = raw37330step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37330step1 raw37330step1Labels permutation20 hz
    mixedMoment B raw37330step2 raw37330step2Labels = mixedMoment B raw37330step3 raw37330step3Labels := by
      have hz : ∀ j, raw37330step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw37330step3 = (fun i j => raw37330step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw37330step3 raw37330step2; decide +kernel
      have hl : raw37330step3Labels = raw37330step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37330step2 raw37330step2Labels permutation4 hz
    mixedMoment B raw37330step3 raw37330step3Labels = mixedMoment B raw37330step4 raw37330step4Labels := by
      have ha : raw37330step4 = (fun i j => raw37330step3 (permutation1 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37330step4 raw37330step3; decide +kernel
      have hl : raw37330step4Labels = raw37330step3Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37330step3 raw37330step3Labels permutation1 permutation2
    _ = mixedMoment B node1541 node1541Labels := by rfl

theorem canonical37331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37331 raw37331Labels = mixedMoment B node1534 node1534Labels := by
  calc
    mixedMoment B raw37331 raw37331Labels = mixedMoment B raw37331step0 raw37331step0Labels := by
      have hz : ∀ j, raw37331 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37331step0 = (fun i j => raw37331 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37331step0 raw37331; decide +kernel
      have hl : raw37331step0Labels = raw37331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37331 raw37331Labels permutation520 hz
    mixedMoment B raw37331step0 raw37331step0Labels = mixedMoment B raw37331step1 raw37331step1Labels := by
      have hz : ∀ j, raw37331step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37331step1 = (fun i j => raw37331step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37331step1 raw37331step0; decide +kernel
      have hl : raw37331step1Labels = raw37331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37331step0 raw37331step0Labels permutation104 hz
    mixedMoment B raw37331step1 raw37331step1Labels = mixedMoment B raw37331step2 raw37331step2Labels := by
      have hz : ∀ j, raw37331step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw37331step2 = (fun i j => raw37331step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw37331step2 raw37331step1; decide +kernel
      have hl : raw37331step2Labels = raw37331step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37331step1 raw37331step1Labels permutation20 hz
    mixedMoment B raw37331step2 raw37331step2Labels = mixedMoment B raw37331step3 raw37331step3Labels := by
      have ha : raw37331step3 = (fun i j => raw37331step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37331step3 raw37331step2; decide +kernel
      have hl : raw37331step3Labels = raw37331step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37331step2 raw37331step2Labels permutation7 permutation2
    _ = mixedMoment B node1534 node1534Labels := by rfl

theorem canonical37332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37332 raw37332Labels = mixedMoment B node1534 node1534Labels := by
  calc
    mixedMoment B raw37332 raw37332Labels = mixedMoment B raw37332step0 raw37332step0Labels := by
      have hz : ∀ j, raw37332 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37332step0 = (fun i j => raw37332 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37332step0 raw37332; decide +kernel
      have hl : raw37332step0Labels = raw37332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37332 raw37332Labels permutation520 hz
    mixedMoment B raw37332step0 raw37332step0Labels = mixedMoment B raw37332step1 raw37332step1Labels := by
      have hz : ∀ j, raw37332step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37332step1 = (fun i j => raw37332step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37332step1 raw37332step0; decide +kernel
      have hl : raw37332step1Labels = raw37332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37332step0 raw37332step0Labels permutation104 hz
    mixedMoment B raw37332step1 raw37332step1Labels = mixedMoment B raw37332step2 raw37332step2Labels := by
      have hz : ∀ j, raw37332step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37332step2 = (fun i j => raw37332step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37332step2 raw37332step1; decide +kernel
      have hl : raw37332step2Labels = raw37332step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37332step1 raw37332step1Labels permutation14 hz
    mixedMoment B raw37332step2 raw37332step2Labels = mixedMoment B raw37332step3 raw37332step3Labels := by
      have ha : raw37332step3 = (fun i j => raw37332step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37332step3 raw37332step2; decide +kernel
      have hl : raw37332step3Labels = raw37332step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37332step2 raw37332step2Labels permutation7 permutation2
    _ = mixedMoment B node1534 node1534Labels := by rfl

theorem canonical37333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37333 raw37333Labels = mixedMoment B node1534 node1534Labels := by
  calc
    mixedMoment B raw37333 raw37333Labels = mixedMoment B raw37333step0 raw37333step0Labels := by
      have hz : ∀ j, raw37333 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37333step0 = (fun i j => raw37333 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37333step0 raw37333; decide +kernel
      have hl : raw37333step0Labels = raw37333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37333 raw37333Labels permutation520 hz
    mixedMoment B raw37333step0 raw37333step0Labels = mixedMoment B raw37333step1 raw37333step1Labels := by
      have hz : ∀ j, raw37333step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37333step1 = (fun i j => raw37333step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37333step1 raw37333step0; decide +kernel
      have hl : raw37333step1Labels = raw37333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37333step0 raw37333step0Labels permutation80 hz
    mixedMoment B raw37333step1 raw37333step1Labels = mixedMoment B raw37333step2 raw37333step2Labels := by
      have hz : ∀ j, raw37333step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37333step2 = (fun i j => raw37333step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37333step2 raw37333step1; decide +kernel
      have hl : raw37333step2Labels = raw37333step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37333step1 raw37333step1Labels permutation14 hz
    mixedMoment B raw37333step2 raw37333step2Labels = mixedMoment B raw37333step3 raw37333step3Labels := by
      have ha : raw37333step3 = (fun i j => raw37333step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37333step3 raw37333step2; decide +kernel
      have hl : raw37333step3Labels = raw37333step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37333step2 raw37333step2Labels permutation7 permutation2
    _ = mixedMoment B node1534 node1534Labels := by rfl

theorem canonical37334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37334 raw37334Labels = mixedMoment B node1534 node1534Labels := by
  calc
    mixedMoment B raw37334 raw37334Labels = mixedMoment B raw37334step0 raw37334step0Labels := by
      have hz : ∀ j, raw37334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37334step0 = (fun i j => raw37334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37334step0 raw37334; decide +kernel
      have hl : raw37334step0Labels = raw37334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37334 raw37334Labels permutation434 hz
    mixedMoment B raw37334step0 raw37334step0Labels = mixedMoment B raw37334step1 raw37334step1Labels := by
      have hz : ∀ j, raw37334step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37334step1 = (fun i j => raw37334step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37334step1 raw37334step0; decide +kernel
      have hl : raw37334step1Labels = raw37334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37334step0 raw37334step0Labels permutation80 hz
    mixedMoment B raw37334step1 raw37334step1Labels = mixedMoment B raw37334step2 raw37334step2Labels := by
      have hz : ∀ j, raw37334step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37334step2 = (fun i j => raw37334step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37334step2 raw37334step1; decide +kernel
      have hl : raw37334step2Labels = raw37334step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37334step1 raw37334step1Labels permutation14 hz
    mixedMoment B raw37334step2 raw37334step2Labels = mixedMoment B raw37334step3 raw37334step3Labels := by
      have ha : raw37334step3 = (fun i j => raw37334step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37334step3 raw37334step2; decide +kernel
      have hl : raw37334step3Labels = raw37334step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37334step2 raw37334step2Labels permutation7 permutation2
    _ = mixedMoment B node1534 node1534Labels := by rfl

theorem canonical37335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37335 raw37335Labels = mixedMoment B node1541 node1541Labels := by
  calc
    mixedMoment B raw37335 raw37335Labels = mixedMoment B raw37335step0 raw37335step0Labels := by
      have hz : ∀ j, raw37335 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37335step0 = (fun i j => raw37335 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37335step0 raw37335; decide +kernel
      have hl : raw37335step0Labels = raw37335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37335 raw37335Labels permutation520 hz
    mixedMoment B raw37335step0 raw37335step0Labels = mixedMoment B raw37335step1 raw37335step1Labels := by
      have hz : ∀ j, raw37335step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37335step1 = (fun i j => raw37335step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37335step1 raw37335step0; decide +kernel
      have hl : raw37335step1Labels = raw37335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37335step0 raw37335step0Labels permutation104 hz
    mixedMoment B raw37335step1 raw37335step1Labels = mixedMoment B raw37335step2 raw37335step2Labels := by
      have hz : ∀ j, raw37335step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw37335step2 = (fun i j => raw37335step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw37335step2 raw37335step1; decide +kernel
      have hl : raw37335step2Labels = raw37335step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37335step1 raw37335step1Labels permutation20 hz
    mixedMoment B raw37335step2 raw37335step2Labels = mixedMoment B raw37335step3 raw37335step3Labels := by
      have hz : ∀ j, raw37335step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw37335step3 = (fun i j => raw37335step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw37335step3 raw37335step2; decide +kernel
      have hl : raw37335step3Labels = raw37335step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37335step2 raw37335step2Labels permutation4 hz
    mixedMoment B raw37335step3 raw37335step3Labels = mixedMoment B raw37335step4 raw37335step4Labels := by
      have ha : raw37335step4 = (fun i j => raw37335step3 (permutation1 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37335step4 raw37335step3; decide +kernel
      have hl : raw37335step4Labels = raw37335step3Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37335step3 raw37335step3Labels permutation1 permutation4
    _ = mixedMoment B node1541 node1541Labels := by rfl

theorem canonical37336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37336 raw37336Labels = mixedMoment B node4062 node4062Labels := by
  calc
    mixedMoment B raw37336 raw37336Labels = mixedMoment B raw37336step0 raw37336step0Labels := by
      have hz : ∀ j, raw37336 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37336step0 = (fun i j => raw37336 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37336step0 raw37336; decide +kernel
      have hl : raw37336step0Labels = raw37336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37336 raw37336Labels permutation520 hz
    mixedMoment B raw37336step0 raw37336step0Labels = mixedMoment B raw37336step1 raw37336step1Labels := by
      have hz : ∀ j, raw37336step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37336step1 = (fun i j => raw37336step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37336step1 raw37336step0; decide +kernel
      have hl : raw37336step1Labels = raw37336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37336step0 raw37336step0Labels permutation104 hz
    mixedMoment B raw37336step1 raw37336step1Labels = mixedMoment B raw37336step2 raw37336step2Labels := by
      have hz : ∀ j, raw37336step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw37336step2 = (fun i j => raw37336step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw37336step2 raw37336step1; decide +kernel
      have hl : raw37336step2Labels = raw37336step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37336step1 raw37336step1Labels permutation20 hz
    mixedMoment B raw37336step2 raw37336step2Labels = mixedMoment B raw37336step3 raw37336step3Labels := by
      have hz : ∀ j, raw37336step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw37336step3 = (fun i j => raw37336step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw37336step3 raw37336step2; decide +kernel
      have hl : raw37336step3Labels = raw37336step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37336step2 raw37336step2Labels permutation4 hz
    mixedMoment B raw37336step3 raw37336step3Labels = mixedMoment B raw37336step4 raw37336step4Labels := by
      have ha : raw37336step4 = (fun i j => raw37336step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37336step4 raw37336step3; decide +kernel
      have hl : raw37336step4Labels = raw37336step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37336step3 raw37336step3Labels permutation1 permutation0
    _ = mixedMoment B node4062 node4062Labels := by rfl

theorem canonical37337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37337 raw37337Labels = mixedMoment B node686 node686Labels := by
  calc
    mixedMoment B raw37337 raw37337Labels = mixedMoment B raw37337step0 raw37337step0Labels := by
      have hz : ∀ j, raw37337 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37337step0 = (fun i j => raw37337 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37337step0 raw37337; decide +kernel
      have hl : raw37337step0Labels = raw37337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37337 raw37337Labels permutation520 hz
    mixedMoment B raw37337step0 raw37337step0Labels = mixedMoment B raw37337step1 raw37337step1Labels := by
      have hz : ∀ j, raw37337step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37337step1 = (fun i j => raw37337step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37337step1 raw37337step0; decide +kernel
      have hl : raw37337step1Labels = raw37337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37337step0 raw37337step0Labels permutation104 hz
    mixedMoment B raw37337step1 raw37337step1Labels = mixedMoment B raw37337step2 raw37337step2Labels := by
      have hz : ∀ j, raw37337step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw37337step2 = (fun i j => raw37337step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw37337step2 raw37337step1; decide +kernel
      have hl : raw37337step2Labels = raw37337step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37337step1 raw37337step1Labels permutation20 hz
    mixedMoment B raw37337step2 raw37337step2Labels = mixedMoment B raw37337step3 raw37337step3Labels := by
      have ha : raw37337step3 = (fun i j => raw37337step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37337step3 raw37337step2; decide +kernel
      have hl : raw37337step3Labels = raw37337step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37337step2 raw37337step2Labels permutation2 permutation4
    mixedMoment B raw37337step3 raw37337step3Labels = mixedMoment B raw37337step4 raw37337step4Labels := by
      have ha : raw37337step4 = -raw37337step3 := by apply Matrix.ext; change ∀ i j, raw37337step4 i j = -(raw37337step3 i j); unfold raw37337step4 raw37337step3; decide +kernel
      have hl : raw37337step4Labels = raw37337step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node686 node686Labels := by rfl

theorem canonical37338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37338 raw37338Labels = mixedMoment B node686 node686Labels := by
  calc
    mixedMoment B raw37338 raw37338Labels = mixedMoment B raw37338step0 raw37338step0Labels := by
      have hz : ∀ j, raw37338 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37338step0 = (fun i j => raw37338 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37338step0 raw37338; decide +kernel
      have hl : raw37338step0Labels = raw37338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37338 raw37338Labels permutation520 hz
    mixedMoment B raw37338step0 raw37338step0Labels = mixedMoment B raw37338step1 raw37338step1Labels := by
      have hz : ∀ j, raw37338step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37338step1 = (fun i j => raw37338step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37338step1 raw37338step0; decide +kernel
      have hl : raw37338step1Labels = raw37338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37338step0 raw37338step0Labels permutation104 hz
    mixedMoment B raw37338step1 raw37338step1Labels = mixedMoment B raw37338step2 raw37338step2Labels := by
      have hz : ∀ j, raw37338step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37338step2 = (fun i j => raw37338step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37338step2 raw37338step1; decide +kernel
      have hl : raw37338step2Labels = raw37338step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37338step1 raw37338step1Labels permutation14 hz
    mixedMoment B raw37338step2 raw37338step2Labels = mixedMoment B raw37338step3 raw37338step3Labels := by
      have ha : raw37338step3 = (fun i j => raw37338step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37338step3 raw37338step2; decide +kernel
      have hl : raw37338step3Labels = raw37338step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37338step2 raw37338step2Labels permutation2 permutation4
    mixedMoment B raw37338step3 raw37338step3Labels = mixedMoment B raw37338step4 raw37338step4Labels := by
      have ha : raw37338step4 = -raw37338step3 := by apply Matrix.ext; change ∀ i j, raw37338step4 i j = -(raw37338step3 i j); unfold raw37338step4 raw37338step3; decide +kernel
      have hl : raw37338step4Labels = raw37338step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node686 node686Labels := by rfl

theorem canonical37339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37339 raw37339Labels = mixedMoment B node686 node686Labels := by
  calc
    mixedMoment B raw37339 raw37339Labels = mixedMoment B raw37339step0 raw37339step0Labels := by
      have hz : ∀ j, raw37339 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37339step0 = (fun i j => raw37339 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37339step0 raw37339; decide +kernel
      have hl : raw37339step0Labels = raw37339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37339 raw37339Labels permutation520 hz
    mixedMoment B raw37339step0 raw37339step0Labels = mixedMoment B raw37339step1 raw37339step1Labels := by
      have hz : ∀ j, raw37339step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37339step1 = (fun i j => raw37339step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37339step1 raw37339step0; decide +kernel
      have hl : raw37339step1Labels = raw37339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37339step0 raw37339step0Labels permutation80 hz
    mixedMoment B raw37339step1 raw37339step1Labels = mixedMoment B raw37339step2 raw37339step2Labels := by
      have hz : ∀ j, raw37339step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37339step2 = (fun i j => raw37339step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37339step2 raw37339step1; decide +kernel
      have hl : raw37339step2Labels = raw37339step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37339step1 raw37339step1Labels permutation14 hz
    mixedMoment B raw37339step2 raw37339step2Labels = mixedMoment B raw37339step3 raw37339step3Labels := by
      have ha : raw37339step3 = (fun i j => raw37339step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37339step3 raw37339step2; decide +kernel
      have hl : raw37339step3Labels = raw37339step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37339step2 raw37339step2Labels permutation2 permutation4
    mixedMoment B raw37339step3 raw37339step3Labels = mixedMoment B raw37339step4 raw37339step4Labels := by
      have ha : raw37339step4 = -raw37339step3 := by apply Matrix.ext; change ∀ i j, raw37339step4 i j = -(raw37339step3 i j); unfold raw37339step4 raw37339step3; decide +kernel
      have hl : raw37339step4Labels = raw37339step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node686 node686Labels := by rfl

theorem canonical37340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37340 raw37340Labels = mixedMoment B node686 node686Labels := by
  calc
    mixedMoment B raw37340 raw37340Labels = mixedMoment B raw37340step0 raw37340step0Labels := by
      have hz : ∀ j, raw37340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37340step0 = (fun i j => raw37340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37340step0 raw37340; decide +kernel
      have hl : raw37340step0Labels = raw37340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37340 raw37340Labels permutation434 hz
    mixedMoment B raw37340step0 raw37340step0Labels = mixedMoment B raw37340step1 raw37340step1Labels := by
      have hz : ∀ j, raw37340step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37340step1 = (fun i j => raw37340step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37340step1 raw37340step0; decide +kernel
      have hl : raw37340step1Labels = raw37340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37340step0 raw37340step0Labels permutation80 hz
    mixedMoment B raw37340step1 raw37340step1Labels = mixedMoment B raw37340step2 raw37340step2Labels := by
      have hz : ∀ j, raw37340step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37340step2 = (fun i j => raw37340step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37340step2 raw37340step1; decide +kernel
      have hl : raw37340step2Labels = raw37340step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37340step1 raw37340step1Labels permutation14 hz
    mixedMoment B raw37340step2 raw37340step2Labels = mixedMoment B raw37340step3 raw37340step3Labels := by
      have ha : raw37340step3 = (fun i j => raw37340step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37340step3 raw37340step2; decide +kernel
      have hl : raw37340step3Labels = raw37340step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37340step2 raw37340step2Labels permutation2 permutation4
    mixedMoment B raw37340step3 raw37340step3Labels = mixedMoment B raw37340step4 raw37340step4Labels := by
      have ha : raw37340step4 = -raw37340step3 := by apply Matrix.ext; change ∀ i j, raw37340step4 i j = -(raw37340step3 i j); unfold raw37340step4 raw37340step3; decide +kernel
      have hl : raw37340step4Labels = raw37340step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node686 node686Labels := by rfl

theorem canonical37341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37341 raw37341Labels = mixedMoment B node697 node697Labels := by
  calc
    mixedMoment B raw37341 raw37341Labels = mixedMoment B raw37341step0 raw37341step0Labels := by
      have hz : ∀ j, raw37341 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37341step0 = (fun i j => raw37341 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37341step0 raw37341; decide +kernel
      have hl : raw37341step0Labels = raw37341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37341 raw37341Labels permutation520 hz
    mixedMoment B raw37341step0 raw37341step0Labels = mixedMoment B raw37341step1 raw37341step1Labels := by
      have hz : ∀ j, raw37341step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37341step1 = (fun i j => raw37341step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37341step1 raw37341step0; decide +kernel
      have hl : raw37341step1Labels = raw37341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37341step0 raw37341step0Labels permutation104 hz
    mixedMoment B raw37341step1 raw37341step1Labels = mixedMoment B raw37341step2 raw37341step2Labels := by
      have hz : ∀ j, raw37341step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw37341step2 = (fun i j => raw37341step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw37341step2 raw37341step1; decide +kernel
      have hl : raw37341step2Labels = raw37341step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37341step1 raw37341step1Labels permutation20 hz
    mixedMoment B raw37341step2 raw37341step2Labels = mixedMoment B raw37341step3 raw37341step3Labels := by
      have hz : ∀ j, raw37341step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw37341step3 = (fun i j => raw37341step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw37341step3 raw37341step2; decide +kernel
      have hl : raw37341step3Labels = raw37341step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37341step2 raw37341step2Labels permutation4 hz
    mixedMoment B raw37341step3 raw37341step3Labels = mixedMoment B raw37341step4 raw37341step4Labels := by
      have ha : raw37341step4 = (fun i j => raw37341step3 (permutation1 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37341step4 raw37341step3; decide +kernel
      have hl : raw37341step4Labels = raw37341step3Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37341step3 raw37341step3Labels permutation1 permutation4
    _ = mixedMoment B node697 node697Labels := by rfl

theorem canonical37342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37342 raw37342Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw37342 raw37342Labels = mixedMoment B raw37342step0 raw37342step0Labels := by
      have hz : ∀ j, raw37342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37342step0 = (fun i j => raw37342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37342step0 raw37342; decide +kernel
      have hl : raw37342step0Labels = raw37342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37342 raw37342Labels permutation434 hz
    mixedMoment B raw37342step0 raw37342step0Labels = mixedMoment B raw37342step1 raw37342step1Labels := by
      have hz : ∀ j, raw37342step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37342step1 = (fun i j => raw37342step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37342step1 raw37342step0; decide +kernel
      have hl : raw37342step1Labels = raw37342step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37342step0 raw37342step0Labels permutation80 hz
    mixedMoment B raw37342step1 raw37342step1Labels = mixedMoment B raw37342step2 raw37342step2Labels := by
      have hz : ∀ j, raw37342step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37342step2 = (fun i j => raw37342step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37342step2 raw37342step1; decide +kernel
      have hl : raw37342step2Labels = raw37342step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37342step1 raw37342step1Labels permutation14 hz
    mixedMoment B raw37342step2 raw37342step2Labels = mixedMoment B raw37342step3 raw37342step3Labels := by
      have ha : raw37342step3 = -raw37342step2 := by apply Matrix.ext; change ∀ i j, raw37342step3 i j = -(raw37342step2 i j); unfold raw37342step3 raw37342step2; decide +kernel
      have hl : raw37342step3Labels = raw37342step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1521 node1521Labels := by rfl

theorem canonical37343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37343 raw37343Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw37343 raw37343Labels = mixedMoment B raw37343step0 raw37343step0Labels := by
      have hz : ∀ j, raw37343 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37343step0 = (fun i j => raw37343 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37343step0 raw37343; decide +kernel
      have hl : raw37343step0Labels = raw37343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37343 raw37343Labels permutation434 hz
    mixedMoment B raw37343step0 raw37343step0Labels = mixedMoment B raw37343step1 raw37343step1Labels := by
      have hz : ∀ j, raw37343step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37343step1 = (fun i j => raw37343step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37343step1 raw37343step0; decide +kernel
      have hl : raw37343step1Labels = raw37343step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37343step0 raw37343step0Labels permutation80 hz
    mixedMoment B raw37343step1 raw37343step1Labels = mixedMoment B raw37343step2 raw37343step2Labels := by
      have ha : raw37343step2 = (fun i j => raw37343step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37343step2 raw37343step1; decide +kernel
      have hl : raw37343step2Labels = raw37343step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37343step1 raw37343step1Labels permutation8 permutation4
    mixedMoment B raw37343step2 raw37343step2Labels = mixedMoment B raw37343step3 raw37343step3Labels := by
      have ha : raw37343step3 = -raw37343step2 := by apply Matrix.ext; change ∀ i j, raw37343step3 i j = -(raw37343step2 i j); unfold raw37343step3 raw37343step2; decide +kernel
      have hl : raw37343step3Labels = raw37343step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1532 node1532Labels := by rfl

theorem canonical37344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37344 raw37344Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw37344 raw37344Labels = mixedMoment B raw37344step0 raw37344step0Labels := by
      have hz : ∀ j, raw37344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37344step0 = (fun i j => raw37344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37344step0 raw37344; decide +kernel
      have hl : raw37344step0Labels = raw37344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37344 raw37344Labels permutation434 hz
    mixedMoment B raw37344step0 raw37344step0Labels = mixedMoment B raw37344step1 raw37344step1Labels := by
      have hz : ∀ j, raw37344step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37344step1 = (fun i j => raw37344step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37344step1 raw37344step0; decide +kernel
      have hl : raw37344step1Labels = raw37344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37344step0 raw37344step0Labels permutation56 hz
    mixedMoment B raw37344step1 raw37344step1Labels = mixedMoment B raw37344step2 raw37344step2Labels := by
      have ha : raw37344step2 = (fun i j => raw37344step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37344step2 raw37344step1; decide +kernel
      have hl : raw37344step2Labels = raw37344step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37344step1 raw37344step1Labels permutation8 permutation4
    mixedMoment B raw37344step2 raw37344step2Labels = mixedMoment B raw37344step3 raw37344step3Labels := by
      have ha : raw37344step3 = -raw37344step2 := by apply Matrix.ext; change ∀ i j, raw37344step3 i j = -(raw37344step2 i j); unfold raw37344step3 raw37344step2; decide +kernel
      have hl : raw37344step3Labels = raw37344step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1532 node1532Labels := by rfl

theorem canonical37345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37345 raw37345Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw37345 raw37345Labels = mixedMoment B raw37345step0 raw37345step0Labels := by
      have hz : ∀ j, raw37345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37345step0 = (fun i j => raw37345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37345step0 raw37345; decide +kernel
      have hl : raw37345step0Labels = raw37345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37345 raw37345Labels permutation346 hz
    mixedMoment B raw37345step0 raw37345step0Labels = mixedMoment B raw37345step1 raw37345step1Labels := by
      have hz : ∀ j, raw37345step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37345step1 = (fun i j => raw37345step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37345step1 raw37345step0; decide +kernel
      have hl : raw37345step1Labels = raw37345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37345step0 raw37345step0Labels permutation56 hz
    mixedMoment B raw37345step1 raw37345step1Labels = mixedMoment B raw37345step2 raw37345step2Labels := by
      have ha : raw37345step2 = (fun i j => raw37345step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37345step2 raw37345step1; decide +kernel
      have hl : raw37345step2Labels = raw37345step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37345step1 raw37345step1Labels permutation8 permutation4
    mixedMoment B raw37345step2 raw37345step2Labels = mixedMoment B raw37345step3 raw37345step3Labels := by
      have ha : raw37345step3 = -raw37345step2 := by apply Matrix.ext; change ∀ i j, raw37345step3 i j = -(raw37345step2 i j); unfold raw37345step3 raw37345step2; decide +kernel
      have hl : raw37345step3Labels = raw37345step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1532 node1532Labels := by rfl

theorem canonical37346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37346 raw37346Labels = mixedMoment B node1540 node1540Labels := by
  calc
    mixedMoment B raw37346 raw37346Labels = mixedMoment B raw37346step0 raw37346step0Labels := by
      have hz : ∀ j, raw37346 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37346step0 = (fun i j => raw37346 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37346step0 raw37346; decide +kernel
      have hl : raw37346step0Labels = raw37346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37346 raw37346Labels permutation434 hz
    mixedMoment B raw37346step0 raw37346step0Labels = mixedMoment B raw37346step1 raw37346step1Labels := by
      have hz : ∀ j, raw37346step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37346step1 = (fun i j => raw37346step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37346step1 raw37346step0; decide +kernel
      have hl : raw37346step1Labels = raw37346step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37346step0 raw37346step0Labels permutation80 hz
    mixedMoment B raw37346step1 raw37346step1Labels = mixedMoment B raw37346step2 raw37346step2Labels := by
      have hz : ∀ j, raw37346step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37346step2 = (fun i j => raw37346step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37346step2 raw37346step1; decide +kernel
      have hl : raw37346step2Labels = raw37346step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37346step1 raw37346step1Labels permutation14 hz
    mixedMoment B raw37346step2 raw37346step2Labels = mixedMoment B raw37346step3 raw37346step3Labels := by
      have ha : raw37346step3 = (fun i j => raw37346step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37346step3 raw37346step2; decide +kernel
      have hl : raw37346step3Labels = raw37346step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37346step2 raw37346step2Labels permutation3 permutation4
    mixedMoment B raw37346step3 raw37346step3Labels = mixedMoment B raw37346step4 raw37346step4Labels := by
      have ha : raw37346step4 = -raw37346step3 := by apply Matrix.ext; change ∀ i j, raw37346step4 i j = -(raw37346step3 i j); unfold raw37346step4 raw37346step3; decide +kernel
      have hl : raw37346step4Labels = raw37346step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1540 node1540Labels := by rfl

theorem canonical37347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37347 raw37347Labels = mixedMoment B node1537 node1537Labels := by
  calc
    mixedMoment B raw37347 raw37347Labels = mixedMoment B raw37347step0 raw37347step0Labels := by
      have hz : ∀ j, raw37347 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37347step0 = (fun i j => raw37347 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37347step0 raw37347; decide +kernel
      have hl : raw37347step0Labels = raw37347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37347 raw37347Labels permutation434 hz
    mixedMoment B raw37347step0 raw37347step0Labels = mixedMoment B raw37347step1 raw37347step1Labels := by
      have hz : ∀ j, raw37347step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37347step1 = (fun i j => raw37347step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37347step1 raw37347step0; decide +kernel
      have hl : raw37347step1Labels = raw37347step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37347step0 raw37347step0Labels permutation80 hz
    mixedMoment B raw37347step1 raw37347step1Labels = mixedMoment B raw37347step2 raw37347step2Labels := by
      have hz : ∀ j, raw37347step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37347step2 = (fun i j => raw37347step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37347step2 raw37347step1; decide +kernel
      have hl : raw37347step2Labels = raw37347step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37347step1 raw37347step1Labels permutation14 hz
    mixedMoment B raw37347step2 raw37347step2Labels = mixedMoment B raw37347step3 raw37347step3Labels := by
      have ha : raw37347step3 = (fun i j => raw37347step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37347step3 raw37347step2; decide +kernel
      have hl : raw37347step3Labels = raw37347step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37347step2 raw37347step2Labels permutation2 permutation4
    mixedMoment B raw37347step3 raw37347step3Labels = mixedMoment B raw37347step4 raw37347step4Labels := by
      have ha : raw37347step4 = -raw37347step3 := by apply Matrix.ext; change ∀ i j, raw37347step4 i j = -(raw37347step3 i j); unfold raw37347step4 raw37347step3; decide +kernel
      have hl : raw37347step4Labels = raw37347step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1537 node1537Labels := by rfl

theorem canonical37348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37348 raw37348Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw37348 raw37348Labels = mixedMoment B raw37348step0 raw37348step0Labels := by
      have hz : ∀ j, raw37348 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37348step0 = (fun i j => raw37348 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37348step0 raw37348; decide +kernel
      have hl : raw37348step0Labels = raw37348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37348 raw37348Labels permutation434 hz
    mixedMoment B raw37348step0 raw37348step0Labels = mixedMoment B raw37348step1 raw37348step1Labels := by
      have hz : ∀ j, raw37348step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37348step1 = (fun i j => raw37348step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37348step1 raw37348step0; decide +kernel
      have hl : raw37348step1Labels = raw37348step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37348step0 raw37348step0Labels permutation80 hz
    mixedMoment B raw37348step1 raw37348step1Labels = mixedMoment B raw37348step2 raw37348step2Labels := by
      have hz : ∀ j, raw37348step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37348step2 = (fun i j => raw37348step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37348step2 raw37348step1; decide +kernel
      have hl : raw37348step2Labels = raw37348step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37348step1 raw37348step1Labels permutation14 hz
    mixedMoment B raw37348step2 raw37348step2Labels = mixedMoment B raw37348step3 raw37348step3Labels := by
      have ha : raw37348step3 = -raw37348step2 := by apply Matrix.ext; change ∀ i j, raw37348step3 i j = -(raw37348step2 i j); unfold raw37348step3 raw37348step2; decide +kernel
      have hl : raw37348step3Labels = raw37348step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4060 node4060Labels := by rfl

theorem canonical37349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37349 raw37349Labels = mixedMoment B node1537 node1537Labels := by
  calc
    mixedMoment B raw37349 raw37349Labels = mixedMoment B raw37349step0 raw37349step0Labels := by
      have hz : ∀ j, raw37349 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37349step0 = (fun i j => raw37349 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37349step0 raw37349; decide +kernel
      have hl : raw37349step0Labels = raw37349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37349 raw37349Labels permutation434 hz
    mixedMoment B raw37349step0 raw37349step0Labels = mixedMoment B raw37349step1 raw37349step1Labels := by
      have hz : ∀ j, raw37349step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37349step1 = (fun i j => raw37349step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37349step1 raw37349step0; decide +kernel
      have hl : raw37349step1Labels = raw37349step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37349step0 raw37349step0Labels permutation80 hz
    mixedMoment B raw37349step1 raw37349step1Labels = mixedMoment B raw37349step2 raw37349step2Labels := by
      have hz : ∀ j, raw37349step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37349step2 = (fun i j => raw37349step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37349step2 raw37349step1; decide +kernel
      have hl : raw37349step2Labels = raw37349step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37349step1 raw37349step1Labels permutation14 hz
    mixedMoment B raw37349step2 raw37349step2Labels = mixedMoment B raw37349step3 raw37349step3Labels := by
      have ha : raw37349step3 = -raw37349step2 := by apply Matrix.ext; change ∀ i j, raw37349step3 i j = -(raw37349step2 i j); unfold raw37349step3 raw37349step2; decide +kernel
      have hl : raw37349step3Labels = raw37349step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1537 node1537Labels := by rfl

theorem canonical37350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37350 raw37350Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw37350 raw37350Labels = mixedMoment B raw37350step0 raw37350step0Labels := by
      have hz : ∀ j, raw37350 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37350step0 = (fun i j => raw37350 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37350step0 raw37350; decide +kernel
      have hl : raw37350step0Labels = raw37350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37350 raw37350Labels permutation434 hz
    mixedMoment B raw37350step0 raw37350step0Labels = mixedMoment B raw37350step1 raw37350step1Labels := by
      have hz : ∀ j, raw37350step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37350step1 = (fun i j => raw37350step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37350step1 raw37350step0; decide +kernel
      have hl : raw37350step1Labels = raw37350step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37350step0 raw37350step0Labels permutation80 hz
    mixedMoment B raw37350step1 raw37350step1Labels = mixedMoment B raw37350step2 raw37350step2Labels := by
      have ha : raw37350step2 = (fun i j => raw37350step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37350step2 raw37350step1; decide +kernel
      have hl : raw37350step2Labels = raw37350step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37350step1 raw37350step1Labels permutation10 permutation4
    mixedMoment B raw37350step2 raw37350step2Labels = mixedMoment B raw37350step3 raw37350step3Labels := by
      have ha : raw37350step3 = -raw37350step2 := by apply Matrix.ext; change ∀ i j, raw37350step3 i j = -(raw37350step2 i j); unfold raw37350step3 raw37350step2; decide +kernel
      have hl : raw37350step3Labels = raw37350step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1516 node1516Labels := by rfl

theorem canonical37351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37351 raw37351Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw37351 raw37351Labels = mixedMoment B raw37351step0 raw37351step0Labels := by
      have hz : ∀ j, raw37351 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37351step0 = (fun i j => raw37351 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37351step0 raw37351; decide +kernel
      have hl : raw37351step0Labels = raw37351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37351 raw37351Labels permutation434 hz
    mixedMoment B raw37351step0 raw37351step0Labels = mixedMoment B raw37351step1 raw37351step1Labels := by
      have hz : ∀ j, raw37351step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37351step1 = (fun i j => raw37351step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37351step1 raw37351step0; decide +kernel
      have hl : raw37351step1Labels = raw37351step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37351step0 raw37351step0Labels permutation56 hz
    mixedMoment B raw37351step1 raw37351step1Labels = mixedMoment B raw37351step2 raw37351step2Labels := by
      have ha : raw37351step2 = (fun i j => raw37351step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37351step2 raw37351step1; decide +kernel
      have hl : raw37351step2Labels = raw37351step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37351step1 raw37351step1Labels permutation10 permutation4
    mixedMoment B raw37351step2 raw37351step2Labels = mixedMoment B raw37351step3 raw37351step3Labels := by
      have ha : raw37351step3 = -raw37351step2 := by apply Matrix.ext; change ∀ i j, raw37351step3 i j = -(raw37351step2 i j); unfold raw37351step3 raw37351step2; decide +kernel
      have hl : raw37351step3Labels = raw37351step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1516 node1516Labels := by rfl

theorem canonical37352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37352 raw37352Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw37352 raw37352Labels = mixedMoment B raw37352step0 raw37352step0Labels := by
      have hz : ∀ j, raw37352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37352step0 = (fun i j => raw37352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37352step0 raw37352; decide +kernel
      have hl : raw37352step0Labels = raw37352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37352 raw37352Labels permutation346 hz
    mixedMoment B raw37352step0 raw37352step0Labels = mixedMoment B raw37352step1 raw37352step1Labels := by
      have hz : ∀ j, raw37352step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37352step1 = (fun i j => raw37352step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37352step1 raw37352step0; decide +kernel
      have hl : raw37352step1Labels = raw37352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37352step0 raw37352step0Labels permutation56 hz
    mixedMoment B raw37352step1 raw37352step1Labels = mixedMoment B raw37352step2 raw37352step2Labels := by
      have ha : raw37352step2 = (fun i j => raw37352step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37352step2 raw37352step1; decide +kernel
      have hl : raw37352step2Labels = raw37352step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37352step1 raw37352step1Labels permutation10 permutation4
    mixedMoment B raw37352step2 raw37352step2Labels = mixedMoment B raw37352step3 raw37352step3Labels := by
      have ha : raw37352step3 = -raw37352step2 := by apply Matrix.ext; change ∀ i j, raw37352step3 i j = -(raw37352step2 i j); unfold raw37352step3 raw37352step2; decide +kernel
      have hl : raw37352step3Labels = raw37352step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1516 node1516Labels := by rfl

theorem canonical37353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37353 raw37353Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw37353 raw37353Labels = mixedMoment B raw37353step0 raw37353step0Labels := by
      have hz : ∀ j, raw37353 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37353step0 = (fun i j => raw37353 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37353step0 raw37353; decide +kernel
      have hl : raw37353step0Labels = raw37353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37353 raw37353Labels permutation434 hz
    mixedMoment B raw37353step0 raw37353step0Labels = mixedMoment B raw37353step1 raw37353step1Labels := by
      have hz : ∀ j, raw37353step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37353step1 = (fun i j => raw37353step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37353step1 raw37353step0; decide +kernel
      have hl : raw37353step1Labels = raw37353step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37353step0 raw37353step0Labels permutation80 hz
    mixedMoment B raw37353step1 raw37353step1Labels = mixedMoment B raw37353step2 raw37353step2Labels := by
      have hz : ∀ j, raw37353step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37353step2 = (fun i j => raw37353step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37353step2 raw37353step1; decide +kernel
      have hl : raw37353step2Labels = raw37353step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37353step1 raw37353step1Labels permutation14 hz
    mixedMoment B raw37353step2 raw37353step2Labels = mixedMoment B raw37353step3 raw37353step3Labels := by
      have ha : raw37353step3 = (fun i j => raw37353step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37353step3 raw37353step2; decide +kernel
      have hl : raw37353step3Labels = raw37353step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37353step2 raw37353step2Labels permutation2 permutation4
    mixedMoment B raw37353step3 raw37353step3Labels = mixedMoment B raw37353step4 raw37353step4Labels := by
      have ha : raw37353step4 = -raw37353step3 := by apply Matrix.ext; change ∀ i j, raw37353step4 i j = -(raw37353step3 i j); unfold raw37353step4 raw37353step3; decide +kernel
      have hl : raw37353step4Labels = raw37353step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1521 node1521Labels := by rfl

theorem canonical37354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37354 raw37354Labels = mixedMoment B node683 node683Labels := by
  calc
    mixedMoment B raw37354 raw37354Labels = mixedMoment B raw37354step0 raw37354step0Labels := by
      have hz : ∀ j, raw37354 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37354step0 = (fun i j => raw37354 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37354step0 raw37354; decide +kernel
      have hl : raw37354step0Labels = raw37354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37354 raw37354Labels permutation434 hz
    mixedMoment B raw37354step0 raw37354step0Labels = mixedMoment B raw37354step1 raw37354step1Labels := by
      have hz : ∀ j, raw37354step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37354step1 = (fun i j => raw37354step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37354step1 raw37354step0; decide +kernel
      have hl : raw37354step1Labels = raw37354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37354step0 raw37354step0Labels permutation80 hz
    mixedMoment B raw37354step1 raw37354step1Labels = mixedMoment B raw37354step2 raw37354step2Labels := by
      have ha : raw37354step2 = (fun i j => raw37354step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37354step2 raw37354step1; decide +kernel
      have hl : raw37354step2Labels = raw37354step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37354step1 raw37354step1Labels permutation8 permutation4
    mixedMoment B raw37354step2 raw37354step2Labels = mixedMoment B raw37354step3 raw37354step3Labels := by
      have ha : raw37354step3 = -raw37354step2 := by apply Matrix.ext; change ∀ i j, raw37354step3 i j = -(raw37354step2 i j); unfold raw37354step3 raw37354step2; decide +kernel
      have hl : raw37354step3Labels = raw37354step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node683 node683Labels := by rfl

theorem canonical37355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37355 raw37355Labels = mixedMoment B node683 node683Labels := by
  calc
    mixedMoment B raw37355 raw37355Labels = mixedMoment B raw37355step0 raw37355step0Labels := by
      have hz : ∀ j, raw37355 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37355step0 = (fun i j => raw37355 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37355step0 raw37355; decide +kernel
      have hl : raw37355step0Labels = raw37355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37355 raw37355Labels permutation434 hz
    mixedMoment B raw37355step0 raw37355step0Labels = mixedMoment B raw37355step1 raw37355step1Labels := by
      have hz : ∀ j, raw37355step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37355step1 = (fun i j => raw37355step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37355step1 raw37355step0; decide +kernel
      have hl : raw37355step1Labels = raw37355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37355step0 raw37355step0Labels permutation56 hz
    mixedMoment B raw37355step1 raw37355step1Labels = mixedMoment B raw37355step2 raw37355step2Labels := by
      have ha : raw37355step2 = (fun i j => raw37355step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37355step2 raw37355step1; decide +kernel
      have hl : raw37355step2Labels = raw37355step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37355step1 raw37355step1Labels permutation8 permutation4
    mixedMoment B raw37355step2 raw37355step2Labels = mixedMoment B raw37355step3 raw37355step3Labels := by
      have ha : raw37355step3 = -raw37355step2 := by apply Matrix.ext; change ∀ i j, raw37355step3 i j = -(raw37355step2 i j); unfold raw37355step3 raw37355step2; decide +kernel
      have hl : raw37355step3Labels = raw37355step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node683 node683Labels := by rfl

theorem canonical37356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37356 raw37356Labels = mixedMoment B node683 node683Labels := by
  calc
    mixedMoment B raw37356 raw37356Labels = mixedMoment B raw37356step0 raw37356step0Labels := by
      have hz : ∀ j, raw37356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37356step0 = (fun i j => raw37356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37356step0 raw37356; decide +kernel
      have hl : raw37356step0Labels = raw37356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37356 raw37356Labels permutation346 hz
    mixedMoment B raw37356step0 raw37356step0Labels = mixedMoment B raw37356step1 raw37356step1Labels := by
      have hz : ∀ j, raw37356step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37356step1 = (fun i j => raw37356step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37356step1 raw37356step0; decide +kernel
      have hl : raw37356step1Labels = raw37356step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37356step0 raw37356step0Labels permutation56 hz
    mixedMoment B raw37356step1 raw37356step1Labels = mixedMoment B raw37356step2 raw37356step2Labels := by
      have ha : raw37356step2 = (fun i j => raw37356step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37356step2 raw37356step1; decide +kernel
      have hl : raw37356step2Labels = raw37356step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37356step1 raw37356step1Labels permutation8 permutation4
    mixedMoment B raw37356step2 raw37356step2Labels = mixedMoment B raw37356step3 raw37356step3Labels := by
      have ha : raw37356step3 = -raw37356step2 := by apply Matrix.ext; change ∀ i j, raw37356step3 i j = -(raw37356step2 i j); unfold raw37356step3 raw37356step2; decide +kernel
      have hl : raw37356step3Labels = raw37356step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node683 node683Labels := by rfl

theorem canonical37357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37357 raw37357Labels = mixedMoment B node695 node695Labels := by
  calc
    mixedMoment B raw37357 raw37357Labels = mixedMoment B raw37357step0 raw37357step0Labels := by
      have hz : ∀ j, raw37357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37357step0 = (fun i j => raw37357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37357step0 raw37357; decide +kernel
      have hl : raw37357step0Labels = raw37357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37357 raw37357Labels permutation434 hz
    mixedMoment B raw37357step0 raw37357step0Labels = mixedMoment B raw37357step1 raw37357step1Labels := by
      have hz : ∀ j, raw37357step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37357step1 = (fun i j => raw37357step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37357step1 raw37357step0; decide +kernel
      have hl : raw37357step1Labels = raw37357step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37357step0 raw37357step0Labels permutation80 hz
    mixedMoment B raw37357step1 raw37357step1Labels = mixedMoment B raw37357step2 raw37357step2Labels := by
      have hz : ∀ j, raw37357step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37357step2 = (fun i j => raw37357step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37357step2 raw37357step1; decide +kernel
      have hl : raw37357step2Labels = raw37357step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37357step1 raw37357step1Labels permutation14 hz
    mixedMoment B raw37357step2 raw37357step2Labels = mixedMoment B raw37357step3 raw37357step3Labels := by
      have ha : raw37357step3 = (fun i j => raw37357step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37357step3 raw37357step2; decide +kernel
      have hl : raw37357step3Labels = raw37357step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37357step2 raw37357step2Labels permutation2 permutation4
    mixedMoment B raw37357step3 raw37357step3Labels = mixedMoment B raw37357step4 raw37357step4Labels := by
      have ha : raw37357step4 = -raw37357step3 := by apply Matrix.ext; change ∀ i j, raw37357step4 i j = -(raw37357step3 i j); unfold raw37357step4 raw37357step3; decide +kernel
      have hl : raw37357step4Labels = raw37357step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node695 node695Labels := by rfl

theorem canonical37358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37358 raw37358Labels = mixedMoment B node691 node691Labels := by
  calc
    mixedMoment B raw37358 raw37358Labels = mixedMoment B raw37358step0 raw37358step0Labels := by
      have hz : ∀ j, raw37358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37358step0 = (fun i j => raw37358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37358step0 raw37358; decide +kernel
      have hl : raw37358step0Labels = raw37358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37358 raw37358Labels permutation434 hz
    mixedMoment B raw37358step0 raw37358step0Labels = mixedMoment B raw37358step1 raw37358step1Labels := by
      have hz : ∀ j, raw37358step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37358step1 = (fun i j => raw37358step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37358step1 raw37358step0; decide +kernel
      have hl : raw37358step1Labels = raw37358step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37358step0 raw37358step0Labels permutation80 hz
    mixedMoment B raw37358step1 raw37358step1Labels = mixedMoment B raw37358step2 raw37358step2Labels := by
      have hz : ∀ j, raw37358step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37358step2 = (fun i j => raw37358step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37358step2 raw37358step1; decide +kernel
      have hl : raw37358step2Labels = raw37358step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37358step1 raw37358step1Labels permutation14 hz
    mixedMoment B raw37358step2 raw37358step2Labels = mixedMoment B raw37358step3 raw37358step3Labels := by
      have ha : raw37358step3 = (fun i j => raw37358step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37358step3 raw37358step2; decide +kernel
      have hl : raw37358step3Labels = raw37358step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37358step2 raw37358step2Labels permutation2 permutation4
    mixedMoment B raw37358step3 raw37358step3Labels = mixedMoment B raw37358step4 raw37358step4Labels := by
      have ha : raw37358step4 = -raw37358step3 := by apply Matrix.ext; change ∀ i j, raw37358step4 i j = -(raw37358step3 i j); unfold raw37358step4 raw37358step3; decide +kernel
      have hl : raw37358step4Labels = raw37358step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node691 node691Labels := by rfl

theorem canonical37370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37370 raw37370Labels = mixedMoment B node1527 node1527Labels := by
  calc
    mixedMoment B raw37370 raw37370Labels = mixedMoment B raw37370step0 raw37370step0Labels := by
      have hz : ∀ j, raw37370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37370step0 = (fun i j => raw37370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37370step0 raw37370; decide +kernel
      have hl : raw37370step0Labels = raw37370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37370 raw37370Labels permutation434 hz
    mixedMoment B raw37370step0 raw37370step0Labels = mixedMoment B raw37370step1 raw37370step1Labels := by
      have hz : ∀ j, raw37370step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37370step1 = (fun i j => raw37370step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37370step1 raw37370step0; decide +kernel
      have hl : raw37370step1Labels = raw37370step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37370step0 raw37370step0Labels permutation80 hz
    mixedMoment B raw37370step1 raw37370step1Labels = mixedMoment B raw37370step2 raw37370step2Labels := by
      have hz : ∀ j, raw37370step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37370step2 = (fun i j => raw37370step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37370step2 raw37370step1; decide +kernel
      have hl : raw37370step2Labels = raw37370step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37370step1 raw37370step1Labels permutation14 hz
    mixedMoment B raw37370step2 raw37370step2Labels = mixedMoment B raw37370step3 raw37370step3Labels := by
      have ha : raw37370step3 = -raw37370step2 := by apply Matrix.ext; change ∀ i j, raw37370step3 i j = -(raw37370step2 i j); unfold raw37370step3 raw37370step2; decide +kernel
      have hl : raw37370step3Labels = raw37370step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1527 node1527Labels := by rfl

theorem canonical37371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37371 raw37371Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw37371 raw37371Labels = mixedMoment B raw37371step0 raw37371step0Labels := by
      have hz : ∀ j, raw37371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37371step0 = (fun i j => raw37371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37371step0 raw37371; decide +kernel
      have hl : raw37371step0Labels = raw37371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37371 raw37371Labels permutation434 hz
    mixedMoment B raw37371step0 raw37371step0Labels = mixedMoment B raw37371step1 raw37371step1Labels := by
      have hz : ∀ j, raw37371step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37371step1 = (fun i j => raw37371step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37371step1 raw37371step0; decide +kernel
      have hl : raw37371step1Labels = raw37371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37371step0 raw37371step0Labels permutation80 hz
    mixedMoment B raw37371step1 raw37371step1Labels = mixedMoment B raw37371step2 raw37371step2Labels := by
      have ha : raw37371step2 = (fun i j => raw37371step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37371step2 raw37371step1; decide +kernel
      have hl : raw37371step2Labels = raw37371step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37371step1 raw37371step1Labels permutation12 permutation4
    mixedMoment B raw37371step2 raw37371step2Labels = mixedMoment B raw37371step3 raw37371step3Labels := by
      have ha : raw37371step3 = -raw37371step2 := by apply Matrix.ext; change ∀ i j, raw37371step3 i j = -(raw37371step2 i j); unfold raw37371step3 raw37371step2; decide +kernel
      have hl : raw37371step3Labels = raw37371step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1529 node1529Labels := by rfl

theorem canonical37372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37372 raw37372Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw37372 raw37372Labels = mixedMoment B raw37372step0 raw37372step0Labels := by
      have hz : ∀ j, raw37372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37372step0 = (fun i j => raw37372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37372step0 raw37372; decide +kernel
      have hl : raw37372step0Labels = raw37372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37372 raw37372Labels permutation434 hz
    mixedMoment B raw37372step0 raw37372step0Labels = mixedMoment B raw37372step1 raw37372step1Labels := by
      have hz : ∀ j, raw37372step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37372step1 = (fun i j => raw37372step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37372step1 raw37372step0; decide +kernel
      have hl : raw37372step1Labels = raw37372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37372step0 raw37372step0Labels permutation56 hz
    mixedMoment B raw37372step1 raw37372step1Labels = mixedMoment B raw37372step2 raw37372step2Labels := by
      have ha : raw37372step2 = (fun i j => raw37372step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37372step2 raw37372step1; decide +kernel
      have hl : raw37372step2Labels = raw37372step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37372step1 raw37372step1Labels permutation12 permutation4
    mixedMoment B raw37372step2 raw37372step2Labels = mixedMoment B raw37372step3 raw37372step3Labels := by
      have ha : raw37372step3 = -raw37372step2 := by apply Matrix.ext; change ∀ i j, raw37372step3 i j = -(raw37372step2 i j); unfold raw37372step3 raw37372step2; decide +kernel
      have hl : raw37372step3Labels = raw37372step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1529 node1529Labels := by rfl

theorem canonical37373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37373 raw37373Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw37373 raw37373Labels = mixedMoment B raw37373step0 raw37373step0Labels := by
      have hz : ∀ j, raw37373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37373step0 = (fun i j => raw37373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37373step0 raw37373; decide +kernel
      have hl : raw37373step0Labels = raw37373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37373 raw37373Labels permutation346 hz
    mixedMoment B raw37373step0 raw37373step0Labels = mixedMoment B raw37373step1 raw37373step1Labels := by
      have hz : ∀ j, raw37373step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37373step1 = (fun i j => raw37373step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37373step1 raw37373step0; decide +kernel
      have hl : raw37373step1Labels = raw37373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37373step0 raw37373step0Labels permutation56 hz
    mixedMoment B raw37373step1 raw37373step1Labels = mixedMoment B raw37373step2 raw37373step2Labels := by
      have ha : raw37373step2 = (fun i j => raw37373step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37373step2 raw37373step1; decide +kernel
      have hl : raw37373step2Labels = raw37373step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37373step1 raw37373step1Labels permutation12 permutation4
    mixedMoment B raw37373step2 raw37373step2Labels = mixedMoment B raw37373step3 raw37373step3Labels := by
      have ha : raw37373step3 = -raw37373step2 := by apply Matrix.ext; change ∀ i j, raw37373step3 i j = -(raw37373step2 i j); unfold raw37373step3 raw37373step2; decide +kernel
      have hl : raw37373step3Labels = raw37373step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1529 node1529Labels := by rfl

theorem canonical37374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37374 raw37374Labels = mixedMoment B node1531 node1531Labels := by
  calc
    mixedMoment B raw37374 raw37374Labels = mixedMoment B raw37374step0 raw37374step0Labels := by
      have hz : ∀ j, raw37374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37374step0 = (fun i j => raw37374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37374step0 raw37374; decide +kernel
      have hl : raw37374step0Labels = raw37374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37374 raw37374Labels permutation434 hz
    mixedMoment B raw37374step0 raw37374step0Labels = mixedMoment B raw37374step1 raw37374step1Labels := by
      have hz : ∀ j, raw37374step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37374step1 = (fun i j => raw37374step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37374step1 raw37374step0; decide +kernel
      have hl : raw37374step1Labels = raw37374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37374step0 raw37374step0Labels permutation80 hz
    mixedMoment B raw37374step1 raw37374step1Labels = mixedMoment B raw37374step2 raw37374step2Labels := by
      have hz : ∀ j, raw37374step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37374step2 = (fun i j => raw37374step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37374step2 raw37374step1; decide +kernel
      have hl : raw37374step2Labels = raw37374step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37374step1 raw37374step1Labels permutation14 hz
    mixedMoment B raw37374step2 raw37374step2Labels = mixedMoment B raw37374step3 raw37374step3Labels := by
      have ha : raw37374step3 = (fun i j => raw37374step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37374step3 raw37374step2; decide +kernel
      have hl : raw37374step3Labels = raw37374step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37374step2 raw37374step2Labels permutation3 permutation4
    mixedMoment B raw37374step3 raw37374step3Labels = mixedMoment B raw37374step4 raw37374step4Labels := by
      have ha : raw37374step4 = -raw37374step3 := by apply Matrix.ext; change ∀ i j, raw37374step4 i j = -(raw37374step3 i j); unfold raw37374step4 raw37374step3; decide +kernel
      have hl : raw37374step4Labels = raw37374step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1531 node1531Labels := by rfl

theorem canonical37375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37375 raw37375Labels = mixedMoment B node1539 node1539Labels := by
  calc
    mixedMoment B raw37375 raw37375Labels = mixedMoment B raw37375step0 raw37375step0Labels := by
      have hz : ∀ j, raw37375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37375step0 = (fun i j => raw37375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37375step0 raw37375; decide +kernel
      have hl : raw37375step0Labels = raw37375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37375 raw37375Labels permutation434 hz
    mixedMoment B raw37375step0 raw37375step0Labels = mixedMoment B raw37375step1 raw37375step1Labels := by
      have hz : ∀ j, raw37375step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37375step1 = (fun i j => raw37375step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37375step1 raw37375step0; decide +kernel
      have hl : raw37375step1Labels = raw37375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37375step0 raw37375step0Labels permutation80 hz
    mixedMoment B raw37375step1 raw37375step1Labels = mixedMoment B raw37375step2 raw37375step2Labels := by
      have hz : ∀ j, raw37375step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37375step2 = (fun i j => raw37375step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37375step2 raw37375step1; decide +kernel
      have hl : raw37375step2Labels = raw37375step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37375step1 raw37375step1Labels permutation14 hz
    mixedMoment B raw37375step2 raw37375step2Labels = mixedMoment B raw37375step3 raw37375step3Labels := by
      have ha : raw37375step3 = (fun i j => raw37375step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37375step3 raw37375step2; decide +kernel
      have hl : raw37375step3Labels = raw37375step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37375step2 raw37375step2Labels permutation3 permutation4
    mixedMoment B raw37375step3 raw37375step3Labels = mixedMoment B raw37375step4 raw37375step4Labels := by
      have ha : raw37375step4 = -raw37375step3 := by apply Matrix.ext; change ∀ i j, raw37375step4 i j = -(raw37375step3 i j); unfold raw37375step4 raw37375step3; decide +kernel
      have hl : raw37375step4Labels = raw37375step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1539 node1539Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical292
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37376 raw37376Labels = mixedMoment B node4061 node4061Labels := by
  calc
    mixedMoment B raw37376 raw37376Labels = mixedMoment B raw37376step0 raw37376step0Labels := by
      have hz : ∀ j, raw37376 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37376step0 = (fun i j => raw37376 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37376step0 raw37376; decide +kernel
      have hl : raw37376step0Labels = raw37376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37376 raw37376Labels permutation434 hz
    mixedMoment B raw37376step0 raw37376step0Labels = mixedMoment B raw37376step1 raw37376step1Labels := by
      have hz : ∀ j, raw37376step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37376step1 = (fun i j => raw37376step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37376step1 raw37376step0; decide +kernel
      have hl : raw37376step1Labels = raw37376step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37376step0 raw37376step0Labels permutation80 hz
    mixedMoment B raw37376step1 raw37376step1Labels = mixedMoment B raw37376step2 raw37376step2Labels := by
      have hz : ∀ j, raw37376step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37376step2 = (fun i j => raw37376step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37376step2 raw37376step1; decide +kernel
      have hl : raw37376step2Labels = raw37376step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37376step1 raw37376step1Labels permutation14 hz
    mixedMoment B raw37376step2 raw37376step2Labels = mixedMoment B raw37376step3 raw37376step3Labels := by
      have ha : raw37376step3 = -raw37376step2 := by apply Matrix.ext; change ∀ i j, raw37376step3 i j = -(raw37376step2 i j); unfold raw37376step3 raw37376step2; decide +kernel
      have hl : raw37376step3Labels = raw37376step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4061 node4061Labels := by rfl

theorem canonical37377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37377 raw37377Labels = mixedMoment B node1539 node1539Labels := by
  calc
    mixedMoment B raw37377 raw37377Labels = mixedMoment B raw37377step0 raw37377step0Labels := by
      have hz : ∀ j, raw37377 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37377step0 = (fun i j => raw37377 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37377step0 raw37377; decide +kernel
      have hl : raw37377step0Labels = raw37377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37377 raw37377Labels permutation434 hz
    mixedMoment B raw37377step0 raw37377step0Labels = mixedMoment B raw37377step1 raw37377step1Labels := by
      have hz : ∀ j, raw37377step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37377step1 = (fun i j => raw37377step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37377step1 raw37377step0; decide +kernel
      have hl : raw37377step1Labels = raw37377step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37377step0 raw37377step0Labels permutation80 hz
    mixedMoment B raw37377step1 raw37377step1Labels = mixedMoment B raw37377step2 raw37377step2Labels := by
      have hz : ∀ j, raw37377step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37377step2 = (fun i j => raw37377step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37377step2 raw37377step1; decide +kernel
      have hl : raw37377step2Labels = raw37377step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37377step1 raw37377step1Labels permutation14 hz
    mixedMoment B raw37377step2 raw37377step2Labels = mixedMoment B raw37377step3 raw37377step3Labels := by
      have ha : raw37377step3 = (fun i j => raw37377step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37377step3 raw37377step2; decide +kernel
      have hl : raw37377step3Labels = raw37377step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37377step2 raw37377step2Labels permutation3 permutation2
    mixedMoment B raw37377step3 raw37377step3Labels = mixedMoment B raw37377step4 raw37377step4Labels := by
      have ha : raw37377step4 = -raw37377step3 := by apply Matrix.ext; change ∀ i j, raw37377step4 i j = -(raw37377step3 i j); unfold raw37377step4 raw37377step3; decide +kernel
      have hl : raw37377step4Labels = raw37377step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1539 node1539Labels := by rfl

theorem canonical37378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37378 raw37378Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw37378 raw37378Labels = mixedMoment B raw37378step0 raw37378step0Labels := by
      have hz : ∀ j, raw37378 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37378step0 = (fun i j => raw37378 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37378step0 raw37378; decide +kernel
      have hl : raw37378step0Labels = raw37378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37378 raw37378Labels permutation434 hz
    mixedMoment B raw37378step0 raw37378step0Labels = mixedMoment B raw37378step1 raw37378step1Labels := by
      have hz : ∀ j, raw37378step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37378step1 = (fun i j => raw37378step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37378step1 raw37378step0; decide +kernel
      have hl : raw37378step1Labels = raw37378step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37378step0 raw37378step0Labels permutation80 hz
    mixedMoment B raw37378step1 raw37378step1Labels = mixedMoment B raw37378step2 raw37378step2Labels := by
      have ha : raw37378step2 = (fun i j => raw37378step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37378step2 raw37378step1; decide +kernel
      have hl : raw37378step2Labels = raw37378step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37378step1 raw37378step1Labels permutation10 permutation4
    mixedMoment B raw37378step2 raw37378step2Labels = mixedMoment B raw37378step3 raw37378step3Labels := by
      have ha : raw37378step3 = -raw37378step2 := by apply Matrix.ext; change ∀ i j, raw37378step3 i j = -(raw37378step2 i j); unfold raw37378step3 raw37378step2; decide +kernel
      have hl : raw37378step3Labels = raw37378step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1523 node1523Labels := by rfl

theorem canonical37379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37379 raw37379Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw37379 raw37379Labels = mixedMoment B raw37379step0 raw37379step0Labels := by
      have hz : ∀ j, raw37379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37379step0 = (fun i j => raw37379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37379step0 raw37379; decide +kernel
      have hl : raw37379step0Labels = raw37379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37379 raw37379Labels permutation434 hz
    mixedMoment B raw37379step0 raw37379step0Labels = mixedMoment B raw37379step1 raw37379step1Labels := by
      have hz : ∀ j, raw37379step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37379step1 = (fun i j => raw37379step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37379step1 raw37379step0; decide +kernel
      have hl : raw37379step1Labels = raw37379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37379step0 raw37379step0Labels permutation56 hz
    mixedMoment B raw37379step1 raw37379step1Labels = mixedMoment B raw37379step2 raw37379step2Labels := by
      have ha : raw37379step2 = (fun i j => raw37379step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37379step2 raw37379step1; decide +kernel
      have hl : raw37379step2Labels = raw37379step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37379step1 raw37379step1Labels permutation10 permutation4
    mixedMoment B raw37379step2 raw37379step2Labels = mixedMoment B raw37379step3 raw37379step3Labels := by
      have ha : raw37379step3 = -raw37379step2 := by apply Matrix.ext; change ∀ i j, raw37379step3 i j = -(raw37379step2 i j); unfold raw37379step3 raw37379step2; decide +kernel
      have hl : raw37379step3Labels = raw37379step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1523 node1523Labels := by rfl

theorem canonical37380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37380 raw37380Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw37380 raw37380Labels = mixedMoment B raw37380step0 raw37380step0Labels := by
      have hz : ∀ j, raw37380 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37380step0 = (fun i j => raw37380 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37380step0 raw37380; decide +kernel
      have hl : raw37380step0Labels = raw37380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37380 raw37380Labels permutation346 hz
    mixedMoment B raw37380step0 raw37380step0Labels = mixedMoment B raw37380step1 raw37380step1Labels := by
      have hz : ∀ j, raw37380step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37380step1 = (fun i j => raw37380step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37380step1 raw37380step0; decide +kernel
      have hl : raw37380step1Labels = raw37380step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37380step0 raw37380step0Labels permutation56 hz
    mixedMoment B raw37380step1 raw37380step1Labels = mixedMoment B raw37380step2 raw37380step2Labels := by
      have ha : raw37380step2 = (fun i j => raw37380step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37380step2 raw37380step1; decide +kernel
      have hl : raw37380step2Labels = raw37380step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37380step1 raw37380step1Labels permutation10 permutation4
    mixedMoment B raw37380step2 raw37380step2Labels = mixedMoment B raw37380step3 raw37380step3Labels := by
      have ha : raw37380step3 = -raw37380step2 := by apply Matrix.ext; change ∀ i j, raw37380step3 i j = -(raw37380step2 i j); unfold raw37380step3 raw37380step2; decide +kernel
      have hl : raw37380step3Labels = raw37380step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1523 node1523Labels := by rfl

theorem canonical37381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37381 raw37381Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw37381 raw37381Labels = mixedMoment B raw37381step0 raw37381step0Labels := by
      have hz : ∀ j, raw37381 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37381step0 = (fun i j => raw37381 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37381step0 raw37381; decide +kernel
      have hl : raw37381step0Labels = raw37381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37381 raw37381Labels permutation434 hz
    mixedMoment B raw37381step0 raw37381step0Labels = mixedMoment B raw37381step1 raw37381step1Labels := by
      have hz : ∀ j, raw37381step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37381step1 = (fun i j => raw37381step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37381step1 raw37381step0; decide +kernel
      have hl : raw37381step1Labels = raw37381step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37381step0 raw37381step0Labels permutation80 hz
    mixedMoment B raw37381step1 raw37381step1Labels = mixedMoment B raw37381step2 raw37381step2Labels := by
      have hz : ∀ j, raw37381step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37381step2 = (fun i j => raw37381step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37381step2 raw37381step1; decide +kernel
      have hl : raw37381step2Labels = raw37381step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37381step1 raw37381step1Labels permutation14 hz
    mixedMoment B raw37381step2 raw37381step2Labels = mixedMoment B raw37381step3 raw37381step3Labels := by
      have ha : raw37381step3 = (fun i j => raw37381step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37381step3 raw37381step2; decide +kernel
      have hl : raw37381step3Labels = raw37381step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37381step2 raw37381step2Labels permutation2 permutation4
    mixedMoment B raw37381step3 raw37381step3Labels = mixedMoment B raw37381step4 raw37381step4Labels := by
      have ha : raw37381step4 = -raw37381step3 := by apply Matrix.ext; change ∀ i j, raw37381step4 i j = -(raw37381step3 i j); unfold raw37381step4 raw37381step3; decide +kernel
      have hl : raw37381step4Labels = raw37381step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1538 node1538Labels := by rfl

theorem canonical37382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37382 raw37382Labels = mixedMoment B node1527 node1527Labels := by
  calc
    mixedMoment B raw37382 raw37382Labels = mixedMoment B raw37382step0 raw37382step0Labels := by
      have hz : ∀ j, raw37382 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37382step0 = (fun i j => raw37382 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37382step0 raw37382; decide +kernel
      have hl : raw37382step0Labels = raw37382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37382 raw37382Labels permutation434 hz
    mixedMoment B raw37382step0 raw37382step0Labels = mixedMoment B raw37382step1 raw37382step1Labels := by
      have hz : ∀ j, raw37382step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37382step1 = (fun i j => raw37382step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37382step1 raw37382step0; decide +kernel
      have hl : raw37382step1Labels = raw37382step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37382step0 raw37382step0Labels permutation80 hz
    mixedMoment B raw37382step1 raw37382step1Labels = mixedMoment B raw37382step2 raw37382step2Labels := by
      have hz : ∀ j, raw37382step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37382step2 = (fun i j => raw37382step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37382step2 raw37382step1; decide +kernel
      have hl : raw37382step2Labels = raw37382step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37382step1 raw37382step1Labels permutation14 hz
    mixedMoment B raw37382step2 raw37382step2Labels = mixedMoment B raw37382step3 raw37382step3Labels := by
      have ha : raw37382step3 = (fun i j => raw37382step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37382step3 raw37382step2; decide +kernel
      have hl : raw37382step3Labels = raw37382step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37382step2 raw37382step2Labels permutation2 permutation4
    mixedMoment B raw37382step3 raw37382step3Labels = mixedMoment B raw37382step4 raw37382step4Labels := by
      have ha : raw37382step4 = -raw37382step3 := by apply Matrix.ext; change ∀ i j, raw37382step4 i j = -(raw37382step3 i j); unfold raw37382step4 raw37382step3; decide +kernel
      have hl : raw37382step4Labels = raw37382step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1527 node1527Labels := by rfl

theorem canonical37383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37383 raw37383Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw37383 raw37383Labels = mixedMoment B raw37383step0 raw37383step0Labels := by
      have hz : ∀ j, raw37383 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37383step0 = (fun i j => raw37383 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37383step0 raw37383; decide +kernel
      have hl : raw37383step0Labels = raw37383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37383 raw37383Labels permutation434 hz
    mixedMoment B raw37383step0 raw37383step0Labels = mixedMoment B raw37383step1 raw37383step1Labels := by
      have hz : ∀ j, raw37383step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37383step1 = (fun i j => raw37383step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37383step1 raw37383step0; decide +kernel
      have hl : raw37383step1Labels = raw37383step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37383step0 raw37383step0Labels permutation80 hz
    mixedMoment B raw37383step1 raw37383step1Labels = mixedMoment B raw37383step2 raw37383step2Labels := by
      have hz : ∀ j, raw37383step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37383step2 = (fun i j => raw37383step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37383step2 raw37383step1; decide +kernel
      have hl : raw37383step2Labels = raw37383step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37383step1 raw37383step1Labels permutation14 hz
    mixedMoment B raw37383step2 raw37383step2Labels = mixedMoment B raw37383step3 raw37383step3Labels := by
      have ha : raw37383step3 = -raw37383step2 := by apply Matrix.ext; change ∀ i j, raw37383step3 i j = -(raw37383step2 i j); unfold raw37383step3 raw37383step2; decide +kernel
      have hl : raw37383step3Labels = raw37383step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1538 node1538Labels := by rfl

theorem canonical37384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37384 raw37384Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw37384 raw37384Labels = mixedMoment B raw37384step0 raw37384step0Labels := by
      have hz : ∀ j, raw37384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37384step0 = (fun i j => raw37384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37384step0 raw37384; decide +kernel
      have hl : raw37384step0Labels = raw37384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37384 raw37384Labels permutation434 hz
    mixedMoment B raw37384step0 raw37384step0Labels = mixedMoment B raw37384step1 raw37384step1Labels := by
      have hz : ∀ j, raw37384step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37384step1 = (fun i j => raw37384step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37384step1 raw37384step0; decide +kernel
      have hl : raw37384step1Labels = raw37384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37384step0 raw37384step0Labels permutation80 hz
    mixedMoment B raw37384step1 raw37384step1Labels = mixedMoment B raw37384step2 raw37384step2Labels := by
      have ha : raw37384step2 = (fun i j => raw37384step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37384step2 raw37384step1; decide +kernel
      have hl : raw37384step2Labels = raw37384step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37384step1 raw37384step1Labels permutation8 permutation4
    mixedMoment B raw37384step2 raw37384step2Labels = mixedMoment B raw37384step3 raw37384step3Labels := by
      have ha : raw37384step3 = -raw37384step2 := by apply Matrix.ext; change ∀ i j, raw37384step3 i j = -(raw37384step2 i j); unfold raw37384step3 raw37384step2; decide +kernel
      have hl : raw37384step3Labels = raw37384step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1533 node1533Labels := by rfl

theorem canonical37385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37385 raw37385Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw37385 raw37385Labels = mixedMoment B raw37385step0 raw37385step0Labels := by
      have hz : ∀ j, raw37385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37385step0 = (fun i j => raw37385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37385step0 raw37385; decide +kernel
      have hl : raw37385step0Labels = raw37385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37385 raw37385Labels permutation434 hz
    mixedMoment B raw37385step0 raw37385step0Labels = mixedMoment B raw37385step1 raw37385step1Labels := by
      have hz : ∀ j, raw37385step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37385step1 = (fun i j => raw37385step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37385step1 raw37385step0; decide +kernel
      have hl : raw37385step1Labels = raw37385step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37385step0 raw37385step0Labels permutation56 hz
    mixedMoment B raw37385step1 raw37385step1Labels = mixedMoment B raw37385step2 raw37385step2Labels := by
      have ha : raw37385step2 = (fun i j => raw37385step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37385step2 raw37385step1; decide +kernel
      have hl : raw37385step2Labels = raw37385step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37385step1 raw37385step1Labels permutation8 permutation4
    mixedMoment B raw37385step2 raw37385step2Labels = mixedMoment B raw37385step3 raw37385step3Labels := by
      have ha : raw37385step3 = -raw37385step2 := by apply Matrix.ext; change ∀ i j, raw37385step3 i j = -(raw37385step2 i j); unfold raw37385step3 raw37385step2; decide +kernel
      have hl : raw37385step3Labels = raw37385step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1533 node1533Labels := by rfl

theorem canonical37386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37386 raw37386Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw37386 raw37386Labels = mixedMoment B raw37386step0 raw37386step0Labels := by
      have hz : ∀ j, raw37386 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37386step0 = (fun i j => raw37386 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37386step0 raw37386; decide +kernel
      have hl : raw37386step0Labels = raw37386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37386 raw37386Labels permutation346 hz
    mixedMoment B raw37386step0 raw37386step0Labels = mixedMoment B raw37386step1 raw37386step1Labels := by
      have hz : ∀ j, raw37386step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37386step1 = (fun i j => raw37386step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37386step1 raw37386step0; decide +kernel
      have hl : raw37386step1Labels = raw37386step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37386step0 raw37386step0Labels permutation56 hz
    mixedMoment B raw37386step1 raw37386step1Labels = mixedMoment B raw37386step2 raw37386step2Labels := by
      have ha : raw37386step2 = (fun i j => raw37386step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37386step2 raw37386step1; decide +kernel
      have hl : raw37386step2Labels = raw37386step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37386step1 raw37386step1Labels permutation8 permutation4
    mixedMoment B raw37386step2 raw37386step2Labels = mixedMoment B raw37386step3 raw37386step3Labels := by
      have ha : raw37386step3 = -raw37386step2 := by apply Matrix.ext; change ∀ i j, raw37386step3 i j = -(raw37386step2 i j); unfold raw37386step3 raw37386step2; decide +kernel
      have hl : raw37386step3Labels = raw37386step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1533 node1533Labels := by rfl

theorem canonical37391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37391 raw37391Labels = mixedMoment B node696 node696Labels := by
  calc
    mixedMoment B raw37391 raw37391Labels = mixedMoment B raw37391step0 raw37391step0Labels := by
      have hz : ∀ j, raw37391 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37391step0 = (fun i j => raw37391 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37391step0 raw37391; decide +kernel
      have hl : raw37391step0Labels = raw37391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37391 raw37391Labels permutation434 hz
    mixedMoment B raw37391step0 raw37391step0Labels = mixedMoment B raw37391step1 raw37391step1Labels := by
      have hz : ∀ j, raw37391step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37391step1 = (fun i j => raw37391step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37391step1 raw37391step0; decide +kernel
      have hl : raw37391step1Labels = raw37391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37391step0 raw37391step0Labels permutation80 hz
    mixedMoment B raw37391step1 raw37391step1Labels = mixedMoment B raw37391step2 raw37391step2Labels := by
      have hz : ∀ j, raw37391step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37391step2 = (fun i j => raw37391step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37391step2 raw37391step1; decide +kernel
      have hl : raw37391step2Labels = raw37391step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37391step1 raw37391step1Labels permutation14 hz
    mixedMoment B raw37391step2 raw37391step2Labels = mixedMoment B raw37391step3 raw37391step3Labels := by
      have ha : raw37391step3 = (fun i j => raw37391step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37391step3 raw37391step2; decide +kernel
      have hl : raw37391step3Labels = raw37391step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37391step2 raw37391step2Labels permutation2 permutation4
    mixedMoment B raw37391step3 raw37391step3Labels = mixedMoment B raw37391step4 raw37391step4Labels := by
      have ha : raw37391step4 = -raw37391step3 := by apply Matrix.ext; change ∀ i j, raw37391step4 i j = -(raw37391step3 i j); unfold raw37391step4 raw37391step3; decide +kernel
      have hl : raw37391step4Labels = raw37391step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node696 node696Labels := by rfl

theorem canonical37392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37392 raw37392Labels = mixedMoment B node1496 node1496Labels := by
  calc
    mixedMoment B raw37392 raw37392Labels = mixedMoment B raw37392step0 raw37392step0Labels := by
      have hz : ∀ j, raw37392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37392step0 = (fun i j => raw37392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37392step0 raw37392; decide +kernel
      have hl : raw37392step0Labels = raw37392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37392 raw37392Labels permutation434 hz
    mixedMoment B raw37392step0 raw37392step0Labels = mixedMoment B raw37392step1 raw37392step1Labels := by
      have hz : ∀ j, raw37392step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37392step1 = (fun i j => raw37392step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37392step1 raw37392step0; decide +kernel
      have hl : raw37392step1Labels = raw37392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37392step0 raw37392step0Labels permutation80 hz
    mixedMoment B raw37392step1 raw37392step1Labels = mixedMoment B raw37392step2 raw37392step2Labels := by
      have ha : raw37392step2 = (fun i j => raw37392step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37392step2 raw37392step1; decide +kernel
      have hl : raw37392step2Labels = raw37392step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37392step1 raw37392step1Labels permutation8 permutation4
    mixedMoment B raw37392step2 raw37392step2Labels = mixedMoment B raw37392step3 raw37392step3Labels := by
      have ha : raw37392step3 = -raw37392step2 := by apply Matrix.ext; change ∀ i j, raw37392step3 i j = -(raw37392step2 i j); unfold raw37392step3 raw37392step2; decide +kernel
      have hl : raw37392step3Labels = raw37392step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1496 node1496Labels := by rfl

theorem canonical37393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37393 raw37393Labels = mixedMoment B node1496 node1496Labels := by
  calc
    mixedMoment B raw37393 raw37393Labels = mixedMoment B raw37393step0 raw37393step0Labels := by
      have hz : ∀ j, raw37393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37393step0 = (fun i j => raw37393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37393step0 raw37393; decide +kernel
      have hl : raw37393step0Labels = raw37393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37393 raw37393Labels permutation434 hz
    mixedMoment B raw37393step0 raw37393step0Labels = mixedMoment B raw37393step1 raw37393step1Labels := by
      have hz : ∀ j, raw37393step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37393step1 = (fun i j => raw37393step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37393step1 raw37393step0; decide +kernel
      have hl : raw37393step1Labels = raw37393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37393step0 raw37393step0Labels permutation56 hz
    mixedMoment B raw37393step1 raw37393step1Labels = mixedMoment B raw37393step2 raw37393step2Labels := by
      have ha : raw37393step2 = (fun i j => raw37393step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37393step2 raw37393step1; decide +kernel
      have hl : raw37393step2Labels = raw37393step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37393step1 raw37393step1Labels permutation8 permutation4
    mixedMoment B raw37393step2 raw37393step2Labels = mixedMoment B raw37393step3 raw37393step3Labels := by
      have ha : raw37393step3 = -raw37393step2 := by apply Matrix.ext; change ∀ i j, raw37393step3 i j = -(raw37393step2 i j); unfold raw37393step3 raw37393step2; decide +kernel
      have hl : raw37393step3Labels = raw37393step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1496 node1496Labels := by rfl

theorem canonical37394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37394 raw37394Labels = mixedMoment B node1496 node1496Labels := by
  calc
    mixedMoment B raw37394 raw37394Labels = mixedMoment B raw37394step0 raw37394step0Labels := by
      have hz : ∀ j, raw37394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37394step0 = (fun i j => raw37394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37394step0 raw37394; decide +kernel
      have hl : raw37394step0Labels = raw37394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37394 raw37394Labels permutation346 hz
    mixedMoment B raw37394step0 raw37394step0Labels = mixedMoment B raw37394step1 raw37394step1Labels := by
      have hz : ∀ j, raw37394step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37394step1 = (fun i j => raw37394step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37394step1 raw37394step0; decide +kernel
      have hl : raw37394step1Labels = raw37394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37394step0 raw37394step0Labels permutation56 hz
    mixedMoment B raw37394step1 raw37394step1Labels = mixedMoment B raw37394step2 raw37394step2Labels := by
      have ha : raw37394step2 = (fun i j => raw37394step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37394step2 raw37394step1; decide +kernel
      have hl : raw37394step2Labels = raw37394step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37394step1 raw37394step1Labels permutation8 permutation4
    mixedMoment B raw37394step2 raw37394step2Labels = mixedMoment B raw37394step3 raw37394step3Labels := by
      have ha : raw37394step3 = -raw37394step2 := by apply Matrix.ext; change ∀ i j, raw37394step3 i j = -(raw37394step2 i j); unfold raw37394step3 raw37394step2; decide +kernel
      have hl : raw37394step3Labels = raw37394step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1496 node1496Labels := by rfl

theorem canonical37398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37398 raw37398Labels = mixedMoment B node693 node693Labels := by
  calc
    mixedMoment B raw37398 raw37398Labels = mixedMoment B raw37398step0 raw37398step0Labels := by
      have hz : ∀ j, raw37398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37398step0 = (fun i j => raw37398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37398step0 raw37398; decide +kernel
      have hl : raw37398step0Labels = raw37398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37398 raw37398Labels permutation434 hz
    mixedMoment B raw37398step0 raw37398step0Labels = mixedMoment B raw37398step1 raw37398step1Labels := by
      have hz : ∀ j, raw37398step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37398step1 = (fun i j => raw37398step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37398step1 raw37398step0; decide +kernel
      have hl : raw37398step1Labels = raw37398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37398step0 raw37398step0Labels permutation80 hz
    mixedMoment B raw37398step1 raw37398step1Labels = mixedMoment B raw37398step2 raw37398step2Labels := by
      have hz : ∀ j, raw37398step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37398step2 = (fun i j => raw37398step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37398step2 raw37398step1; decide +kernel
      have hl : raw37398step2Labels = raw37398step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37398step1 raw37398step1Labels permutation14 hz
    mixedMoment B raw37398step2 raw37398step2Labels = mixedMoment B raw37398step3 raw37398step3Labels := by
      have ha : raw37398step3 = (fun i j => raw37398step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37398step3 raw37398step2; decide +kernel
      have hl : raw37398step3Labels = raw37398step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37398step2 raw37398step2Labels permutation2 permutation4
    mixedMoment B raw37398step3 raw37398step3Labels = mixedMoment B raw37398step4 raw37398step4Labels := by
      have ha : raw37398step4 = -raw37398step3 := by apply Matrix.ext; change ∀ i j, raw37398step4 i j = -(raw37398step3 i j); unfold raw37398step4 raw37398step3; decide +kernel
      have hl : raw37398step4Labels = raw37398step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node693 node693Labels := by rfl

theorem canonical37399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37399 raw37399Labels = mixedMoment B node1495 node1495Labels := by
  calc
    mixedMoment B raw37399 raw37399Labels = mixedMoment B raw37399step0 raw37399step0Labels := by
      have hz : ∀ j, raw37399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37399step0 = (fun i j => raw37399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37399step0 raw37399; decide +kernel
      have hl : raw37399step0Labels = raw37399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37399 raw37399Labels permutation434 hz
    mixedMoment B raw37399step0 raw37399step0Labels = mixedMoment B raw37399step1 raw37399step1Labels := by
      have hz : ∀ j, raw37399step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37399step1 = (fun i j => raw37399step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37399step1 raw37399step0; decide +kernel
      have hl : raw37399step1Labels = raw37399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37399step0 raw37399step0Labels permutation80 hz
    mixedMoment B raw37399step1 raw37399step1Labels = mixedMoment B raw37399step2 raw37399step2Labels := by
      have ha : raw37399step2 = (fun i j => raw37399step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37399step2 raw37399step1; decide +kernel
      have hl : raw37399step2Labels = raw37399step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37399step1 raw37399step1Labels permutation8 permutation4
    mixedMoment B raw37399step2 raw37399step2Labels = mixedMoment B raw37399step3 raw37399step3Labels := by
      have ha : raw37399step3 = -raw37399step2 := by apply Matrix.ext; change ∀ i j, raw37399step3 i j = -(raw37399step2 i j); unfold raw37399step3 raw37399step2; decide +kernel
      have hl : raw37399step3Labels = raw37399step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1495 node1495Labels := by rfl

theorem canonical37400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37400 raw37400Labels = mixedMoment B node1495 node1495Labels := by
  calc
    mixedMoment B raw37400 raw37400Labels = mixedMoment B raw37400step0 raw37400step0Labels := by
      have hz : ∀ j, raw37400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37400step0 = (fun i j => raw37400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37400step0 raw37400; decide +kernel
      have hl : raw37400step0Labels = raw37400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37400 raw37400Labels permutation434 hz
    mixedMoment B raw37400step0 raw37400step0Labels = mixedMoment B raw37400step1 raw37400step1Labels := by
      have hz : ∀ j, raw37400step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37400step1 = (fun i j => raw37400step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37400step1 raw37400step0; decide +kernel
      have hl : raw37400step1Labels = raw37400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37400step0 raw37400step0Labels permutation56 hz
    mixedMoment B raw37400step1 raw37400step1Labels = mixedMoment B raw37400step2 raw37400step2Labels := by
      have ha : raw37400step2 = (fun i j => raw37400step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37400step2 raw37400step1; decide +kernel
      have hl : raw37400step2Labels = raw37400step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37400step1 raw37400step1Labels permutation8 permutation4
    mixedMoment B raw37400step2 raw37400step2Labels = mixedMoment B raw37400step3 raw37400step3Labels := by
      have ha : raw37400step3 = -raw37400step2 := by apply Matrix.ext; change ∀ i j, raw37400step3 i j = -(raw37400step2 i j); unfold raw37400step3 raw37400step2; decide +kernel
      have hl : raw37400step3Labels = raw37400step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1495 node1495Labels := by rfl

theorem canonical37401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37401 raw37401Labels = mixedMoment B node1495 node1495Labels := by
  calc
    mixedMoment B raw37401 raw37401Labels = mixedMoment B raw37401step0 raw37401step0Labels := by
      have hz : ∀ j, raw37401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37401step0 = (fun i j => raw37401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37401step0 raw37401; decide +kernel
      have hl : raw37401step0Labels = raw37401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37401 raw37401Labels permutation346 hz
    mixedMoment B raw37401step0 raw37401step0Labels = mixedMoment B raw37401step1 raw37401step1Labels := by
      have hz : ∀ j, raw37401step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37401step1 = (fun i j => raw37401step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37401step1 raw37401step0; decide +kernel
      have hl : raw37401step1Labels = raw37401step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37401step0 raw37401step0Labels permutation56 hz
    mixedMoment B raw37401step1 raw37401step1Labels = mixedMoment B raw37401step2 raw37401step2Labels := by
      have ha : raw37401step2 = (fun i j => raw37401step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37401step2 raw37401step1; decide +kernel
      have hl : raw37401step2Labels = raw37401step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37401step1 raw37401step1Labels permutation8 permutation4
    mixedMoment B raw37401step2 raw37401step2Labels = mixedMoment B raw37401step3 raw37401step3Labels := by
      have ha : raw37401step3 = -raw37401step2 := by apply Matrix.ext; change ∀ i j, raw37401step3 i j = -(raw37401step2 i j); unfold raw37401step3 raw37401step2; decide +kernel
      have hl : raw37401step3Labels = raw37401step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1495 node1495Labels := by rfl

theorem canonical37406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37406 raw37406Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw37406 raw37406Labels = mixedMoment B raw37406step0 raw37406step0Labels := by
      have hz : ∀ j, raw37406 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37406step0 = (fun i j => raw37406 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37406step0 raw37406; decide +kernel
      have hl : raw37406step0Labels = raw37406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37406 raw37406Labels permutation346 hz
    mixedMoment B raw37406step0 raw37406step0Labels = mixedMoment B raw37406step1 raw37406step1Labels := by
      have hz : ∀ j, raw37406step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37406step1 = (fun i j => raw37406step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37406step1 raw37406step0; decide +kernel
      have hl : raw37406step1Labels = raw37406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37406step0 raw37406step0Labels permutation56 hz
    mixedMoment B raw37406step1 raw37406step1Labels = mixedMoment B raw37406step2 raw37406step2Labels := by
      have ha : raw37406step2 = (fun i j => raw37406step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37406step2 raw37406step1; decide +kernel
      have hl : raw37406step2Labels = raw37406step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37406step1 raw37406step1Labels permutation10 permutation2
    mixedMoment B raw37406step2 raw37406step2Labels = mixedMoment B raw37406step3 raw37406step3Labels := by
      have ha : raw37406step3 = -raw37406step2 := by apply Matrix.ext; change ∀ i j, raw37406step3 i j = -(raw37406step2 i j); unfold raw37406step3 raw37406step2; decide +kernel
      have hl : raw37406step3Labels = raw37406step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1518 node1518Labels := by rfl

theorem canonical37407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37407 raw37407Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw37407 raw37407Labels = mixedMoment B raw37407step0 raw37407step0Labels := by
      have hz : ∀ j, raw37407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37407step0 = (fun i j => raw37407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37407step0 raw37407; decide +kernel
      have hl : raw37407step0Labels = raw37407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37407 raw37407Labels permutation346 hz
    mixedMoment B raw37407step0 raw37407step0Labels = mixedMoment B raw37407step1 raw37407step1Labels := by
      have ha : raw37407step1 = (fun i j => raw37407step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37407step1 raw37407step0; decide +kernel
      have hl : raw37407step1Labels = raw37407step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37407step0 raw37407step0Labels permutation38 permutation4
    mixedMoment B raw37407step1 raw37407step1Labels = mixedMoment B raw37407step2 raw37407step2Labels := by
      have ha : raw37407step2 = -raw37407step1 := by apply Matrix.ext; change ∀ i j, raw37407step2 i j = -(raw37407step1 i j); unfold raw37407step2 raw37407step1; decide +kernel
      have hl : raw37407step2Labels = raw37407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1514 node1514Labels := by rfl

theorem canonical37408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37408 raw37408Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw37408 raw37408Labels = mixedMoment B raw37408step0 raw37408step0Labels := by
      have hz : ∀ j, raw37408 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37408step0 = (fun i j => raw37408 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37408step0 raw37408; decide +kernel
      have hl : raw37408step0Labels = raw37408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37408 raw37408Labels permutation265 hz
    mixedMoment B raw37408step0 raw37408step0Labels = mixedMoment B raw37408step1 raw37408step1Labels := by
      have ha : raw37408step1 = (fun i j => raw37408step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37408step1 raw37408step0; decide +kernel
      have hl : raw37408step1Labels = raw37408step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37408step0 raw37408step0Labels permutation38 permutation4
    mixedMoment B raw37408step1 raw37408step1Labels = mixedMoment B raw37408step2 raw37408step2Labels := by
      have ha : raw37408step2 = -raw37408step1 := by apply Matrix.ext; change ∀ i j, raw37408step2 i j = -(raw37408step1 i j); unfold raw37408step2 raw37408step1; decide +kernel
      have hl : raw37408step2Labels = raw37408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1514 node1514Labels := by rfl

theorem canonical37409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37409 raw37409Labels = mixedMoment B node1535 node1535Labels := by
  calc
    mixedMoment B raw37409 raw37409Labels = mixedMoment B raw37409step0 raw37409step0Labels := by
      have hz : ∀ j, raw37409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37409step0 = (fun i j => raw37409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37409step0 raw37409; decide +kernel
      have hl : raw37409step0Labels = raw37409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37409 raw37409Labels permutation346 hz
    mixedMoment B raw37409step0 raw37409step0Labels = mixedMoment B raw37409step1 raw37409step1Labels := by
      have hz : ∀ j, raw37409step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37409step1 = (fun i j => raw37409step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37409step1 raw37409step0; decide +kernel
      have hl : raw37409step1Labels = raw37409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37409step0 raw37409step0Labels permutation56 hz
    mixedMoment B raw37409step1 raw37409step1Labels = mixedMoment B raw37409step2 raw37409step2Labels := by
      have ha : raw37409step2 = (fun i j => raw37409step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37409step2 raw37409step1; decide +kernel
      have hl : raw37409step2Labels = raw37409step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37409step1 raw37409step1Labels permutation8 permutation4
    mixedMoment B raw37409step2 raw37409step2Labels = mixedMoment B raw37409step3 raw37409step3Labels := by
      have ha : raw37409step3 = -raw37409step2 := by apply Matrix.ext; change ∀ i j, raw37409step3 i j = -(raw37409step2 i j); unfold raw37409step3 raw37409step2; decide +kernel
      have hl : raw37409step3Labels = raw37409step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1535 node1535Labels := by rfl

theorem canonical37410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37410 raw37410Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw37410 raw37410Labels = mixedMoment B raw37410step0 raw37410step0Labels := by
      have hz : ∀ j, raw37410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37410step0 = (fun i j => raw37410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37410step0 raw37410; decide +kernel
      have hl : raw37410step0Labels = raw37410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37410 raw37410Labels permutation346 hz
    mixedMoment B raw37410step0 raw37410step0Labels = mixedMoment B raw37410step1 raw37410step1Labels := by
      have hz : ∀ j, raw37410step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37410step1 = (fun i j => raw37410step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37410step1 raw37410step0; decide +kernel
      have hl : raw37410step1Labels = raw37410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37410step0 raw37410step0Labels permutation56 hz
    mixedMoment B raw37410step1 raw37410step1Labels = mixedMoment B raw37410step2 raw37410step2Labels := by
      have ha : raw37410step2 = (fun i j => raw37410step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37410step2 raw37410step1; decide +kernel
      have hl : raw37410step2Labels = raw37410step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37410step1 raw37410step1Labels permutation9 permutation4
    mixedMoment B raw37410step2 raw37410step2Labels = mixedMoment B raw37410step3 raw37410step3Labels := by
      have ha : raw37410step3 = -raw37410step2 := by apply Matrix.ext; change ∀ i j, raw37410step3 i j = -(raw37410step2 i j); unfold raw37410step3 raw37410step2; decide +kernel
      have hl : raw37410step3Labels = raw37410step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1520 node1520Labels := by rfl

theorem canonical37411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37411 raw37411Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw37411 raw37411Labels = mixedMoment B raw37411step0 raw37411step0Labels := by
      have hz : ∀ j, raw37411 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37411step0 = (fun i j => raw37411 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37411step0 raw37411; decide +kernel
      have hl : raw37411step0Labels = raw37411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37411 raw37411Labels permutation346 hz
    mixedMoment B raw37411step0 raw37411step0Labels = mixedMoment B raw37411step1 raw37411step1Labels := by
      have hz : ∀ j, raw37411step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37411step1 = (fun i j => raw37411step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37411step1 raw37411step0; decide +kernel
      have hl : raw37411step1Labels = raw37411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37411step0 raw37411step0Labels permutation56 hz
    mixedMoment B raw37411step1 raw37411step1Labels = mixedMoment B raw37411step2 raw37411step2Labels := by
      have ha : raw37411step2 = (fun i j => raw37411step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37411step2 raw37411step1; decide +kernel
      have hl : raw37411step2Labels = raw37411step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37411step1 raw37411step1Labels permutation8 permutation4
    mixedMoment B raw37411step2 raw37411step2Labels = mixedMoment B raw37411step3 raw37411step3Labels := by
      have ha : raw37411step3 = -raw37411step2 := by apply Matrix.ext; change ∀ i j, raw37411step3 i j = -(raw37411step2 i j); unfold raw37411step3 raw37411step2; decide +kernel
      have hl : raw37411step3Labels = raw37411step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1518 node1518Labels := by rfl

theorem canonical37412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37412 raw37412Labels = mixedMoment B node4058 node4058Labels := by
  calc
    mixedMoment B raw37412 raw37412Labels = mixedMoment B raw37412step0 raw37412step0Labels := by
      have hz : ∀ j, raw37412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37412step0 = (fun i j => raw37412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37412step0 raw37412; decide +kernel
      have hl : raw37412step0Labels = raw37412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37412 raw37412Labels permutation346 hz
    mixedMoment B raw37412step0 raw37412step0Labels = mixedMoment B raw37412step1 raw37412step1Labels := by
      have hz : ∀ j, raw37412step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37412step1 = (fun i j => raw37412step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37412step1 raw37412step0; decide +kernel
      have hl : raw37412step1Labels = raw37412step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37412step0 raw37412step0Labels permutation56 hz
    mixedMoment B raw37412step1 raw37412step1Labels = mixedMoment B raw37412step2 raw37412step2Labels := by
      have ha : raw37412step2 = -raw37412step1 := by apply Matrix.ext; change ∀ i j, raw37412step2 i j = -(raw37412step1 i j); unfold raw37412step2 raw37412step1; decide +kernel
      have hl : raw37412step2Labels = raw37412step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4058 node4058Labels := by rfl

theorem canonical37413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37413 raw37413Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw37413 raw37413Labels = mixedMoment B raw37413step0 raw37413step0Labels := by
      have hz : ∀ j, raw37413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37413step0 = (fun i j => raw37413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37413step0 raw37413; decide +kernel
      have hl : raw37413step0Labels = raw37413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37413 raw37413Labels permutation346 hz
    mixedMoment B raw37413step0 raw37413step0Labels = mixedMoment B raw37413step1 raw37413step1Labels := by
      have hz : ∀ j, raw37413step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37413step1 = (fun i j => raw37413step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37413step1 raw37413step0; decide +kernel
      have hl : raw37413step1Labels = raw37413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37413step0 raw37413step0Labels permutation56 hz
    mixedMoment B raw37413step1 raw37413step1Labels = mixedMoment B raw37413step2 raw37413step2Labels := by
      have ha : raw37413step2 = -raw37413step1 := by apply Matrix.ext; change ∀ i j, raw37413step2 i j = -(raw37413step1 i j); unfold raw37413step2 raw37413step1; decide +kernel
      have hl : raw37413step2Labels = raw37413step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1509 node1509Labels := by rfl

theorem canonical37414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37414 raw37414Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw37414 raw37414Labels = mixedMoment B raw37414step0 raw37414step0Labels := by
      have hz : ∀ j, raw37414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37414step0 = (fun i j => raw37414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37414step0 raw37414; decide +kernel
      have hl : raw37414step0Labels = raw37414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37414 raw37414Labels permutation346 hz
    mixedMoment B raw37414step0 raw37414step0Labels = mixedMoment B raw37414step1 raw37414step1Labels := by
      have ha : raw37414step1 = (fun i j => raw37414step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37414step1 raw37414step0; decide +kernel
      have hl : raw37414step1Labels = raw37414step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37414step0 raw37414step0Labels permutation50 permutation4
    mixedMoment B raw37414step1 raw37414step1Labels = mixedMoment B raw37414step2 raw37414step2Labels := by
      have ha : raw37414step2 = -raw37414step1 := by apply Matrix.ext; change ∀ i j, raw37414step2 i j = -(raw37414step1 i j); unfold raw37414step2 raw37414step1; decide +kernel
      have hl : raw37414step2Labels = raw37414step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1528 node1528Labels := by rfl

theorem canonical37415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37415 raw37415Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw37415 raw37415Labels = mixedMoment B raw37415step0 raw37415step0Labels := by
      have hz : ∀ j, raw37415 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37415step0 = (fun i j => raw37415 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37415step0 raw37415; decide +kernel
      have hl : raw37415step0Labels = raw37415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37415 raw37415Labels permutation265 hz
    mixedMoment B raw37415step0 raw37415step0Labels = mixedMoment B raw37415step1 raw37415step1Labels := by
      have ha : raw37415step1 = (fun i j => raw37415step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37415step1 raw37415step0; decide +kernel
      have hl : raw37415step1Labels = raw37415step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37415step0 raw37415step0Labels permutation50 permutation4
    mixedMoment B raw37415step1 raw37415step1Labels = mixedMoment B raw37415step2 raw37415step2Labels := by
      have ha : raw37415step2 = -raw37415step1 := by apply Matrix.ext; change ∀ i j, raw37415step2 i j = -(raw37415step1 i j); unfold raw37415step2 raw37415step1; decide +kernel
      have hl : raw37415step2Labels = raw37415step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1528 node1528Labels := by rfl

theorem canonical37416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37416 raw37416Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw37416 raw37416Labels = mixedMoment B raw37416step0 raw37416step0Labels := by
      have hz : ∀ j, raw37416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37416step0 = (fun i j => raw37416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37416step0 raw37416; decide +kernel
      have hl : raw37416step0Labels = raw37416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37416 raw37416Labels permutation346 hz
    mixedMoment B raw37416step0 raw37416step0Labels = mixedMoment B raw37416step1 raw37416step1Labels := by
      have hz : ∀ j, raw37416step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37416step1 = (fun i j => raw37416step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37416step1 raw37416step0; decide +kernel
      have hl : raw37416step1Labels = raw37416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37416step0 raw37416step0Labels permutation56 hz
    mixedMoment B raw37416step1 raw37416step1Labels = mixedMoment B raw37416step2 raw37416step2Labels := by
      have ha : raw37416step2 = (fun i j => raw37416step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37416step2 raw37416step1; decide +kernel
      have hl : raw37416step2Labels = raw37416step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37416step1 raw37416step1Labels permutation13 permutation4
    mixedMoment B raw37416step2 raw37416step2Labels = mixedMoment B raw37416step3 raw37416step3Labels := by
      have ha : raw37416step3 = -raw37416step2 := by apply Matrix.ext; change ∀ i j, raw37416step3 i j = -(raw37416step2 i j); unfold raw37416step3 raw37416step2; decide +kernel
      have hl : raw37416step3Labels = raw37416step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1530 node1530Labels := by rfl

theorem canonical37417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37417 raw37417Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw37417 raw37417Labels = mixedMoment B raw37417step0 raw37417step0Labels := by
      have hz : ∀ j, raw37417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37417step0 = (fun i j => raw37417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37417step0 raw37417; decide +kernel
      have hl : raw37417step0Labels = raw37417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37417 raw37417Labels permutation346 hz
    mixedMoment B raw37417step0 raw37417step0Labels = mixedMoment B raw37417step1 raw37417step1Labels := by
      have hz : ∀ j, raw37417step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37417step1 = (fun i j => raw37417step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37417step1 raw37417step0; decide +kernel
      have hl : raw37417step1Labels = raw37417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37417step0 raw37417step0Labels permutation56 hz
    mixedMoment B raw37417step1 raw37417step1Labels = mixedMoment B raw37417step2 raw37417step2Labels := by
      have ha : raw37417step2 = (fun i j => raw37417step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37417step2 raw37417step1; decide +kernel
      have hl : raw37417step2Labels = raw37417step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37417step1 raw37417step1Labels permutation12 permutation4
    mixedMoment B raw37417step2 raw37417step2Labels = mixedMoment B raw37417step3 raw37417step3Labels := by
      have ha : raw37417step3 = -raw37417step2 := by apply Matrix.ext; change ∀ i j, raw37417step3 i j = -(raw37417step2 i j); unfold raw37417step3 raw37417step2; decide +kernel
      have hl : raw37417step3Labels = raw37417step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1530 node1530Labels := by rfl

theorem canonical37418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37418 raw37418Labels = mixedMoment B node1535 node1535Labels := by
  calc
    mixedMoment B raw37418 raw37418Labels = mixedMoment B raw37418step0 raw37418step0Labels := by
      have hz : ∀ j, raw37418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37418step0 = (fun i j => raw37418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37418step0 raw37418; decide +kernel
      have hl : raw37418step0Labels = raw37418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37418 raw37418Labels permutation346 hz
    mixedMoment B raw37418step0 raw37418step0Labels = mixedMoment B raw37418step1 raw37418step1Labels := by
      have hz : ∀ j, raw37418step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37418step1 = (fun i j => raw37418step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37418step1 raw37418step0; decide +kernel
      have hl : raw37418step1Labels = raw37418step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37418step0 raw37418step0Labels permutation56 hz
    mixedMoment B raw37418step1 raw37418step1Labels = mixedMoment B raw37418step2 raw37418step2Labels := by
      have ha : raw37418step2 = -raw37418step1 := by apply Matrix.ext; change ∀ i j, raw37418step2 i j = -(raw37418step1 i j); unfold raw37418step2 raw37418step1; decide +kernel
      have hl : raw37418step2Labels = raw37418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1535 node1535Labels := by rfl

theorem canonical37419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37419 raw37419Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw37419 raw37419Labels = mixedMoment B raw37419step0 raw37419step0Labels := by
      have hz : ∀ j, raw37419 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37419step0 = (fun i j => raw37419 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37419step0 raw37419; decide +kernel
      have hl : raw37419step0Labels = raw37419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37419 raw37419Labels permutation346 hz
    mixedMoment B raw37419step0 raw37419step0Labels = mixedMoment B raw37419step1 raw37419step1Labels := by
      have ha : raw37419step1 = (fun i j => raw37419step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37419step1 raw37419step0; decide +kernel
      have hl : raw37419step1Labels = raw37419step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37419step0 raw37419step0Labels permutation40 permutation4
    mixedMoment B raw37419step1 raw37419step1Labels = mixedMoment B raw37419step2 raw37419step2Labels := by
      have ha : raw37419step2 = -raw37419step1 := by apply Matrix.ext; change ∀ i j, raw37419step2 i j = -(raw37419step1 i j); unfold raw37419step2 raw37419step1; decide +kernel
      have hl : raw37419step2Labels = raw37419step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1505 node1505Labels := by rfl

theorem canonical37420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37420 raw37420Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw37420 raw37420Labels = mixedMoment B raw37420step0 raw37420step0Labels := by
      have hz : ∀ j, raw37420 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37420step0 = (fun i j => raw37420 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37420step0 raw37420; decide +kernel
      have hl : raw37420step0Labels = raw37420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37420 raw37420Labels permutation265 hz
    mixedMoment B raw37420step0 raw37420step0Labels = mixedMoment B raw37420step1 raw37420step1Labels := by
      have ha : raw37420step1 = (fun i j => raw37420step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37420step1 raw37420step0; decide +kernel
      have hl : raw37420step1Labels = raw37420step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37420step0 raw37420step0Labels permutation40 permutation4
    mixedMoment B raw37420step1 raw37420step1Labels = mixedMoment B raw37420step2 raw37420step2Labels := by
      have ha : raw37420step2 = -raw37420step1 := by apply Matrix.ext; change ∀ i j, raw37420step2 i j = -(raw37420step1 i j); unfold raw37420step2 raw37420step1; decide +kernel
      have hl : raw37420step2Labels = raw37420step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1505 node1505Labels := by rfl

theorem canonical37421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37421 raw37421Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw37421 raw37421Labels = mixedMoment B raw37421step0 raw37421step0Labels := by
      have hz : ∀ j, raw37421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37421step0 = (fun i j => raw37421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37421step0 raw37421; decide +kernel
      have hl : raw37421step0Labels = raw37421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37421 raw37421Labels permutation346 hz
    mixedMoment B raw37421step0 raw37421step0Labels = mixedMoment B raw37421step1 raw37421step1Labels := by
      have hz : ∀ j, raw37421step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37421step1 = (fun i j => raw37421step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37421step1 raw37421step0; decide +kernel
      have hl : raw37421step1Labels = raw37421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37421step0 raw37421step0Labels permutation56 hz
    mixedMoment B raw37421step1 raw37421step1Labels = mixedMoment B raw37421step2 raw37421step2Labels := by
      have ha : raw37421step2 = (fun i j => raw37421step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37421step2 raw37421step1; decide +kernel
      have hl : raw37421step2Labels = raw37421step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37421step1 raw37421step1Labels permutation10 permutation4
    mixedMoment B raw37421step2 raw37421step2Labels = mixedMoment B raw37421step3 raw37421step3Labels := by
      have ha : raw37421step3 = -raw37421step2 := by apply Matrix.ext; change ∀ i j, raw37421step3 i j = -(raw37421step2 i j); unfold raw37421step3 raw37421step2; decide +kernel
      have hl : raw37421step3Labels = raw37421step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1518 node1518Labels := by rfl

theorem canonical37422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37422 raw37422Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw37422 raw37422Labels = mixedMoment B raw37422step0 raw37422step0Labels := by
      have hz : ∀ j, raw37422 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37422step0 = (fun i j => raw37422 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37422step0 raw37422; decide +kernel
      have hl : raw37422step0Labels = raw37422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37422 raw37422Labels permutation346 hz
    mixedMoment B raw37422step0 raw37422step0Labels = mixedMoment B raw37422step1 raw37422step1Labels := by
      have hz : ∀ j, raw37422step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37422step1 = (fun i j => raw37422step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37422step1 raw37422step0; decide +kernel
      have hl : raw37422step1Labels = raw37422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37422step0 raw37422step0Labels permutation56 hz
    mixedMoment B raw37422step1 raw37422step1Labels = mixedMoment B raw37422step2 raw37422step2Labels := by
      have ha : raw37422step2 = (fun i j => raw37422step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37422step2 raw37422step1; decide +kernel
      have hl : raw37422step2Labels = raw37422step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37422step1 raw37422step1Labels permutation8 permutation4
    mixedMoment B raw37422step2 raw37422step2Labels = mixedMoment B raw37422step3 raw37422step3Labels := by
      have ha : raw37422step3 = -raw37422step2 := by apply Matrix.ext; change ∀ i j, raw37422step3 i j = -(raw37422step2 i j); unfold raw37422step3 raw37422step2; decide +kernel
      have hl : raw37422step3Labels = raw37422step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1509 node1509Labels := by rfl

theorem canonical37441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37441 raw37441Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw37441 raw37441Labels = mixedMoment B raw37441step0 raw37441step0Labels := by
      have hz : ∀ j, raw37441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37441step0 = (fun i j => raw37441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37441step0 raw37441; decide +kernel
      have hl : raw37441step0Labels = raw37441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37441 raw37441Labels permutation346 hz
    mixedMoment B raw37441step0 raw37441step0Labels = mixedMoment B raw37441step1 raw37441step1Labels := by
      have hz : ∀ j, raw37441step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37441step1 = (fun i j => raw37441step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37441step1 raw37441step0; decide +kernel
      have hl : raw37441step1Labels = raw37441step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37441step0 raw37441step0Labels permutation56 hz
    mixedMoment B raw37441step1 raw37441step1Labels = mixedMoment B raw37441step2 raw37441step2Labels := by
      have ha : raw37441step2 = (fun i j => raw37441step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37441step2 raw37441step1; decide +kernel
      have hl : raw37441step2Labels = raw37441step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37441step1 raw37441step1Labels permutation12 permutation2
    mixedMoment B raw37441step2 raw37441step2Labels = mixedMoment B raw37441step3 raw37441step3Labels := by
      have ha : raw37441step3 = -raw37441step2 := by apply Matrix.ext; change ∀ i j, raw37441step3 i j = -(raw37441step2 i j); unfold raw37441step3 raw37441step2; decide +kernel
      have hl : raw37441step3Labels = raw37441step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1525 node1525Labels := by rfl

theorem canonical37442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37442 raw37442Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw37442 raw37442Labels = mixedMoment B raw37442step0 raw37442step0Labels := by
      have hz : ∀ j, raw37442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37442step0 = (fun i j => raw37442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37442step0 raw37442; decide +kernel
      have hl : raw37442step0Labels = raw37442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37442 raw37442Labels permutation346 hz
    mixedMoment B raw37442step0 raw37442step0Labels = mixedMoment B raw37442step1 raw37442step1Labels := by
      have ha : raw37442step1 = (fun i j => raw37442step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37442step1 raw37442step0; decide +kernel
      have hl : raw37442step1Labels = raw37442step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37442step0 raw37442step0Labels permutation40 permutation4
    mixedMoment B raw37442step1 raw37442step1Labels = mixedMoment B raw37442step2 raw37442step2Labels := by
      have ha : raw37442step2 = -raw37442step1 := by apply Matrix.ext; change ∀ i j, raw37442step2 i j = -(raw37442step1 i j); unfold raw37442step2 raw37442step1; decide +kernel
      have hl : raw37442step2Labels = raw37442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1511 node1511Labels := by rfl

theorem canonical37443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37443 raw37443Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw37443 raw37443Labels = mixedMoment B raw37443step0 raw37443step0Labels := by
      have hz : ∀ j, raw37443 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37443step0 = (fun i j => raw37443 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37443step0 raw37443; decide +kernel
      have hl : raw37443step0Labels = raw37443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37443 raw37443Labels permutation265 hz
    mixedMoment B raw37443step0 raw37443step0Labels = mixedMoment B raw37443step1 raw37443step1Labels := by
      have ha : raw37443step1 = (fun i j => raw37443step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37443step1 raw37443step0; decide +kernel
      have hl : raw37443step1Labels = raw37443step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37443step0 raw37443step0Labels permutation40 permutation4
    mixedMoment B raw37443step1 raw37443step1Labels = mixedMoment B raw37443step2 raw37443step2Labels := by
      have ha : raw37443step2 = -raw37443step1 := by apply Matrix.ext; change ∀ i j, raw37443step2 i j = -(raw37443step1 i j); unfold raw37443step2 raw37443step1; decide +kernel
      have hl : raw37443step2Labels = raw37443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1511 node1511Labels := by rfl

theorem canonical37444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37444 raw37444Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw37444 raw37444Labels = mixedMoment B raw37444step0 raw37444step0Labels := by
      have hz : ∀ j, raw37444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37444step0 = (fun i j => raw37444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37444step0 raw37444; decide +kernel
      have hl : raw37444step0Labels = raw37444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37444 raw37444Labels permutation346 hz
    mixedMoment B raw37444step0 raw37444step0Labels = mixedMoment B raw37444step1 raw37444step1Labels := by
      have hz : ∀ j, raw37444step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37444step1 = (fun i j => raw37444step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37444step1 raw37444step0; decide +kernel
      have hl : raw37444step1Labels = raw37444step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37444step0 raw37444step0Labels permutation56 hz
    mixedMoment B raw37444step1 raw37444step1Labels = mixedMoment B raw37444step2 raw37444step2Labels := by
      have ha : raw37444step2 = (fun i j => raw37444step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37444step2 raw37444step1; decide +kernel
      have hl : raw37444step2Labels = raw37444step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37444step1 raw37444step1Labels permutation10 permutation4
    mixedMoment B raw37444step2 raw37444step2Labels = mixedMoment B raw37444step3 raw37444step3Labels := by
      have ha : raw37444step3 = -raw37444step2 := by apply Matrix.ext; change ∀ i j, raw37444step3 i j = -(raw37444step2 i j); unfold raw37444step3 raw37444step2; decide +kernel
      have hl : raw37444step3Labels = raw37444step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1525 node1525Labels := by rfl

theorem canonical37445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37445 raw37445Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw37445 raw37445Labels = mixedMoment B raw37445step0 raw37445step0Labels := by
      have hz : ∀ j, raw37445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37445step0 = (fun i j => raw37445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37445step0 raw37445; decide +kernel
      have hl : raw37445step0Labels = raw37445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37445 raw37445Labels permutation346 hz
    mixedMoment B raw37445step0 raw37445step0Labels = mixedMoment B raw37445step1 raw37445step1Labels := by
      have hz : ∀ j, raw37445step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37445step1 = (fun i j => raw37445step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37445step1 raw37445step0; decide +kernel
      have hl : raw37445step1Labels = raw37445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37445step0 raw37445step0Labels permutation56 hz
    mixedMoment B raw37445step1 raw37445step1Labels = mixedMoment B raw37445step2 raw37445step2Labels := by
      have ha : raw37445step2 = (fun i j => raw37445step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37445step2 raw37445step1; decide +kernel
      have hl : raw37445step2Labels = raw37445step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37445step1 raw37445step1Labels permutation8 permutation4
    mixedMoment B raw37445step2 raw37445step2Labels = mixedMoment B raw37445step3 raw37445step3Labels := by
      have ha : raw37445step3 = -raw37445step2 := by apply Matrix.ext; change ∀ i j, raw37445step3 i j = -(raw37445step2 i j); unfold raw37445step3 raw37445step2; decide +kernel
      have hl : raw37445step3Labels = raw37445step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1519 node1519Labels := by rfl

theorem canonical37446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37446 raw37446Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw37446 raw37446Labels = mixedMoment B raw37446step0 raw37446step0Labels := by
      have hz : ∀ j, raw37446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37446step0 = (fun i j => raw37446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37446step0 raw37446; decide +kernel
      have hl : raw37446step0Labels = raw37446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37446 raw37446Labels permutation346 hz
    mixedMoment B raw37446step0 raw37446step0Labels = mixedMoment B raw37446step1 raw37446step1Labels := by
      have hz : ∀ j, raw37446step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37446step1 = (fun i j => raw37446step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37446step1 raw37446step0; decide +kernel
      have hl : raw37446step1Labels = raw37446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37446step0 raw37446step0Labels permutation56 hz
    mixedMoment B raw37446step1 raw37446step1Labels = mixedMoment B raw37446step2 raw37446step2Labels := by
      have ha : raw37446step2 = (fun i j => raw37446step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37446step2 raw37446step1; decide +kernel
      have hl : raw37446step2Labels = raw37446step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37446step1 raw37446step1Labels permutation8 permutation4
    mixedMoment B raw37446step2 raw37446step2Labels = mixedMoment B raw37446step3 raw37446step3Labels := by
      have ha : raw37446step3 = -raw37446step2 := by apply Matrix.ext; change ∀ i j, raw37446step3 i j = -(raw37446step2 i j); unfold raw37446step3 raw37446step2; decide +kernel
      have hl : raw37446step3Labels = raw37446step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1513 node1513Labels := by rfl

theorem canonical37447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37447 raw37447Labels = mixedMoment B node4059 node4059Labels := by
  calc
    mixedMoment B raw37447 raw37447Labels = mixedMoment B raw37447step0 raw37447step0Labels := by
      have hz : ∀ j, raw37447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37447step0 = (fun i j => raw37447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37447step0 raw37447; decide +kernel
      have hl : raw37447step0Labels = raw37447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37447 raw37447Labels permutation346 hz
    mixedMoment B raw37447step0 raw37447step0Labels = mixedMoment B raw37447step1 raw37447step1Labels := by
      have hz : ∀ j, raw37447step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37447step1 = (fun i j => raw37447step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37447step1 raw37447step0; decide +kernel
      have hl : raw37447step1Labels = raw37447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37447step0 raw37447step0Labels permutation56 hz
    mixedMoment B raw37447step1 raw37447step1Labels = mixedMoment B raw37447step2 raw37447step2Labels := by
      have ha : raw37447step2 = -raw37447step1 := by apply Matrix.ext; change ∀ i j, raw37447step2 i j = -(raw37447step1 i j); unfold raw37447step2 raw37447step1; decide +kernel
      have hl : raw37447step2Labels = raw37447step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4059 node4059Labels := by rfl

theorem canonical37448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37448 raw37448Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw37448 raw37448Labels = mixedMoment B raw37448step0 raw37448step0Labels := by
      have hz : ∀ j, raw37448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37448step0 = (fun i j => raw37448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37448step0 raw37448; decide +kernel
      have hl : raw37448step0Labels = raw37448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37448 raw37448Labels permutation346 hz
    mixedMoment B raw37448step0 raw37448step0Labels = mixedMoment B raw37448step1 raw37448step1Labels := by
      have hz : ∀ j, raw37448step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37448step1 = (fun i j => raw37448step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37448step1 raw37448step0; decide +kernel
      have hl : raw37448step1Labels = raw37448step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37448step0 raw37448step0Labels permutation56 hz
    mixedMoment B raw37448step1 raw37448step1Labels = mixedMoment B raw37448step2 raw37448step2Labels := by
      have ha : raw37448step2 = (fun i j => raw37448step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37448step2 raw37448step1; decide +kernel
      have hl : raw37448step2Labels = raw37448step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37448step1 raw37448step1Labels permutation9 permutation2
    mixedMoment B raw37448step2 raw37448step2Labels = mixedMoment B raw37448step3 raw37448step3Labels := by
      have ha : raw37448step3 = -raw37448step2 := by apply Matrix.ext; change ∀ i j, raw37448step3 i j = -(raw37448step2 i j); unfold raw37448step3 raw37448step2; decide +kernel
      have hl : raw37448step3Labels = raw37448step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1519 node1519Labels := by rfl

theorem canonical37449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37449 raw37449Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw37449 raw37449Labels = mixedMoment B raw37449step0 raw37449step0Labels := by
      have hz : ∀ j, raw37449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37449step0 = (fun i j => raw37449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37449step0 raw37449; decide +kernel
      have hl : raw37449step0Labels = raw37449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37449 raw37449Labels permutation346 hz
    mixedMoment B raw37449step0 raw37449step0Labels = mixedMoment B raw37449step1 raw37449step1Labels := by
      have ha : raw37449step1 = (fun i j => raw37449step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37449step1 raw37449step0; decide +kernel
      have hl : raw37449step1Labels = raw37449step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37449step0 raw37449step0Labels permutation44 permutation4
    mixedMoment B raw37449step1 raw37449step1Labels = mixedMoment B raw37449step2 raw37449step2Labels := by
      have ha : raw37449step2 = -raw37449step1 := by apply Matrix.ext; change ∀ i j, raw37449step2 i j = -(raw37449step1 i j); unfold raw37449step2 raw37449step1; decide +kernel
      have hl : raw37449step2Labels = raw37449step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1522 node1522Labels := by rfl

theorem canonical37450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37450 raw37450Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw37450 raw37450Labels = mixedMoment B raw37450step0 raw37450step0Labels := by
      have hz : ∀ j, raw37450 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37450step0 = (fun i j => raw37450 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37450step0 raw37450; decide +kernel
      have hl : raw37450step0Labels = raw37450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37450 raw37450Labels permutation265 hz
    mixedMoment B raw37450step0 raw37450step0Labels = mixedMoment B raw37450step1 raw37450step1Labels := by
      have ha : raw37450step1 = (fun i j => raw37450step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37450step1 raw37450step0; decide +kernel
      have hl : raw37450step1Labels = raw37450step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37450step0 raw37450step0Labels permutation44 permutation4
    mixedMoment B raw37450step1 raw37450step1Labels = mixedMoment B raw37450step2 raw37450step2Labels := by
      have ha : raw37450step2 = -raw37450step1 := by apply Matrix.ext; change ∀ i j, raw37450step2 i j = -(raw37450step1 i j); unfold raw37450step2 raw37450step1; decide +kernel
      have hl : raw37450step2Labels = raw37450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1522 node1522Labels := by rfl

theorem canonical37451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37451 raw37451Labels = mixedMoment B node1526 node1526Labels := by
  calc
    mixedMoment B raw37451 raw37451Labels = mixedMoment B raw37451step0 raw37451step0Labels := by
      have hz : ∀ j, raw37451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37451step0 = (fun i j => raw37451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37451step0 raw37451; decide +kernel
      have hl : raw37451step0Labels = raw37451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37451 raw37451Labels permutation346 hz
    mixedMoment B raw37451step0 raw37451step0Labels = mixedMoment B raw37451step1 raw37451step1Labels := by
      have hz : ∀ j, raw37451step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37451step1 = (fun i j => raw37451step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37451step1 raw37451step0; decide +kernel
      have hl : raw37451step1Labels = raw37451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37451step0 raw37451step0Labels permutation56 hz
    mixedMoment B raw37451step1 raw37451step1Labels = mixedMoment B raw37451step2 raw37451step2Labels := by
      have ha : raw37451step2 = (fun i j => raw37451step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37451step2 raw37451step1; decide +kernel
      have hl : raw37451step2Labels = raw37451step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37451step1 raw37451step1Labels permutation11 permutation4
    mixedMoment B raw37451step2 raw37451step2Labels = mixedMoment B raw37451step3 raw37451step3Labels := by
      have ha : raw37451step3 = -raw37451step2 := by apply Matrix.ext; change ∀ i j, raw37451step3 i j = -(raw37451step2 i j); unfold raw37451step3 raw37451step2; decide +kernel
      have hl : raw37451step3Labels = raw37451step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1526 node1526Labels := by rfl

theorem canonical37452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37452 raw37452Labels = mixedMoment B node1536 node1536Labels := by
  calc
    mixedMoment B raw37452 raw37452Labels = mixedMoment B raw37452step0 raw37452step0Labels := by
      have hz : ∀ j, raw37452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37452step0 = (fun i j => raw37452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37452step0 raw37452; decide +kernel
      have hl : raw37452step0Labels = raw37452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37452 raw37452Labels permutation346 hz
    mixedMoment B raw37452step0 raw37452step0Labels = mixedMoment B raw37452step1 raw37452step1Labels := by
      have hz : ∀ j, raw37452step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37452step1 = (fun i j => raw37452step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37452step1 raw37452step0; decide +kernel
      have hl : raw37452step1Labels = raw37452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37452step0 raw37452step0Labels permutation56 hz
    mixedMoment B raw37452step1 raw37452step1Labels = mixedMoment B raw37452step2 raw37452step2Labels := by
      have ha : raw37452step2 = (fun i j => raw37452step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37452step2 raw37452step1; decide +kernel
      have hl : raw37452step2Labels = raw37452step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37452step1 raw37452step1Labels permutation8 permutation4
    mixedMoment B raw37452step2 raw37452step2Labels = mixedMoment B raw37452step3 raw37452step3Labels := by
      have ha : raw37452step3 = -raw37452step2 := by apply Matrix.ext; change ∀ i j, raw37452step3 i j = -(raw37452step2 i j); unfold raw37452step3 raw37452step2; decide +kernel
      have hl : raw37452step3Labels = raw37452step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1536 node1536Labels := by rfl

theorem canonical37453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37453 raw37453Labels = mixedMoment B node1536 node1536Labels := by
  calc
    mixedMoment B raw37453 raw37453Labels = mixedMoment B raw37453step0 raw37453step0Labels := by
      have hz : ∀ j, raw37453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37453step0 = (fun i j => raw37453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37453step0 raw37453; decide +kernel
      have hl : raw37453step0Labels = raw37453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37453 raw37453Labels permutation346 hz
    mixedMoment B raw37453step0 raw37453step0Labels = mixedMoment B raw37453step1 raw37453step1Labels := by
      have hz : ∀ j, raw37453step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37453step1 = (fun i j => raw37453step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37453step1 raw37453step0; decide +kernel
      have hl : raw37453step1Labels = raw37453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37453step0 raw37453step0Labels permutation56 hz
    mixedMoment B raw37453step1 raw37453step1Labels = mixedMoment B raw37453step2 raw37453step2Labels := by
      have ha : raw37453step2 = -raw37453step1 := by apply Matrix.ext; change ∀ i j, raw37453step2 i j = -(raw37453step1 i j); unfold raw37453step2 raw37453step1; decide +kernel
      have hl : raw37453step2Labels = raw37453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1536 node1536Labels := by rfl

theorem canonical37454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37454 raw37454Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw37454 raw37454Labels = mixedMoment B raw37454step0 raw37454step0Labels := by
      have hz : ∀ j, raw37454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37454step0 = (fun i j => raw37454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37454step0 raw37454; decide +kernel
      have hl : raw37454step0Labels = raw37454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37454 raw37454Labels permutation346 hz
    mixedMoment B raw37454step0 raw37454step0Labels = mixedMoment B raw37454step1 raw37454step1Labels := by
      have ha : raw37454step1 = (fun i j => raw37454step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37454step1 raw37454step0; decide +kernel
      have hl : raw37454step1Labels = raw37454step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37454step0 raw37454step0Labels permutation38 permutation4
    mixedMoment B raw37454step1 raw37454step1Labels = mixedMoment B raw37454step2 raw37454step2Labels := by
      have ha : raw37454step2 = -raw37454step1 := by apply Matrix.ext; change ∀ i j, raw37454step2 i j = -(raw37454step1 i j); unfold raw37454step2 raw37454step1; decide +kernel
      have hl : raw37454step2Labels = raw37454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1515 node1515Labels := by rfl

theorem canonical37455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37455 raw37455Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw37455 raw37455Labels = mixedMoment B raw37455step0 raw37455step0Labels := by
      have hz : ∀ j, raw37455 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37455step0 = (fun i j => raw37455 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37455step0 raw37455; decide +kernel
      have hl : raw37455step0Labels = raw37455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37455 raw37455Labels permutation265 hz
    mixedMoment B raw37455step0 raw37455step0Labels = mixedMoment B raw37455step1 raw37455step1Labels := by
      have ha : raw37455step1 = (fun i j => raw37455step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37455step1 raw37455step0; decide +kernel
      have hl : raw37455step1Labels = raw37455step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37455step0 raw37455step0Labels permutation38 permutation4
    mixedMoment B raw37455step1 raw37455step1Labels = mixedMoment B raw37455step2 raw37455step2Labels := by
      have ha : raw37455step2 = -raw37455step1 := by apply Matrix.ext; change ∀ i j, raw37455step2 i j = -(raw37455step1 i j); unfold raw37455step2 raw37455step1; decide +kernel
      have hl : raw37455step2Labels = raw37455step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1515 node1515Labels := by rfl

theorem canonical37456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37456 raw37456Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw37456 raw37456Labels = mixedMoment B raw37456step0 raw37456step0Labels := by
      have hz : ∀ j, raw37456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37456step0 = (fun i j => raw37456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37456step0 raw37456; decide +kernel
      have hl : raw37456step0Labels = raw37456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37456 raw37456Labels permutation346 hz
    mixedMoment B raw37456step0 raw37456step0Labels = mixedMoment B raw37456step1 raw37456step1Labels := by
      have hz : ∀ j, raw37456step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37456step1 = (fun i j => raw37456step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37456step1 raw37456step0; decide +kernel
      have hl : raw37456step1Labels = raw37456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37456step0 raw37456step0Labels permutation56 hz
    mixedMoment B raw37456step1 raw37456step1Labels = mixedMoment B raw37456step2 raw37456step2Labels := by
      have ha : raw37456step2 = (fun i j => raw37456step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37456step2 raw37456step1; decide +kernel
      have hl : raw37456step2Labels = raw37456step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37456step1 raw37456step1Labels permutation9 permutation4
    mixedMoment B raw37456step2 raw37456step2Labels = mixedMoment B raw37456step3 raw37456step3Labels := by
      have ha : raw37456step3 = -raw37456step2 := by apply Matrix.ext; change ∀ i j, raw37456step3 i j = -(raw37456step2 i j); unfold raw37456step3 raw37456step2; decide +kernel
      have hl : raw37456step3Labels = raw37456step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1519 node1519Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node691 node691Labels = 0 := by
  exact mixedMoment_order_one B hB node691 node691Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node693 node693Labels = 0 := by
  exact mixedMoment_order_one B hB node693 node693Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero696 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node696 node696Labels = 0 := by
  exact mixedMoment_order_one B hB node696 node696Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero697 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node697 node697Labels = 0 := by
  exact mixedMoment_order_one B hB node697 node697Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node683 node683Labels = Sparse.eval nodeValue683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 683) = mixedMoment B node683 node683Labels := rfl
  simpa [nodeValue683, Sparse.eval] using hc.symm

theorem sound686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node686 node686Labels = Sparse.eval nodeValue686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 686) = mixedMoment B node686 node686Labels := rfl
  simpa [nodeValue686, Sparse.eval] using hc.symm

theorem sound691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node691 node691Labels = Sparse.eval nodeValue691 (mixedVector B) := by
  simpa only [nodeValue691, Sparse.eval_nil] using zero691 B _hB _hF

theorem sound693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node693 node693Labels = Sparse.eval nodeValue693 (mixedVector B) := by
  simpa only [nodeValue693, Sparse.eval_nil] using zero693 B _hB _hF

theorem sound695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node695 node695Labels = Sparse.eval nodeValue695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 695) = mixedMoment B node695 node695Labels := rfl
  simpa [nodeValue695, Sparse.eval] using hc.symm

theorem sound696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node696 node696Labels = Sparse.eval nodeValue696 (mixedVector B) := by
  simpa only [nodeValue696, Sparse.eval_nil] using zero696 B _hB _hF

theorem sound697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node697 node697Labels = Sparse.eval nodeValue697 (mixedVector B) := by
  simpa only [nodeValue697, Sparse.eval_nil] using zero697 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1495 node1495Labels = Sparse.eval nodeValue1495 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1495) = mixedMoment B node1495 node1495Labels := rfl
  simpa [nodeValue1495, Sparse.eval] using hc.symm

theorem sound1496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1496 node1496Labels = Sparse.eval nodeValue1496 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1496) = mixedMoment B node1496 node1496Labels := rfl
  simpa [nodeValue1496, Sparse.eval] using hc.symm

theorem sound1505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1505 node1505Labels = Sparse.eval nodeValue1505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1505) = mixedMoment B node1505 node1505Labels := rfl
  simpa [nodeValue1505, Sparse.eval] using hc.symm

theorem sound1509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1509 node1509Labels = Sparse.eval nodeValue1509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1509) = mixedMoment B node1509 node1509Labels := rfl
  simpa [nodeValue1509, Sparse.eval] using hc.symm

theorem sound1511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1511 node1511Labels = Sparse.eval nodeValue1511 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1511) = mixedMoment B node1511 node1511Labels := rfl
  simpa [nodeValue1511, Sparse.eval] using hc.symm

theorem sound1513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1513 node1513Labels = Sparse.eval nodeValue1513 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1513) = mixedMoment B node1513 node1513Labels := rfl
  simpa [nodeValue1513, Sparse.eval] using hc.symm

theorem sound1514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1514 node1514Labels = Sparse.eval nodeValue1514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1514) = mixedMoment B node1514 node1514Labels := rfl
  simpa [nodeValue1514, Sparse.eval] using hc.symm

theorem sound1515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1515 node1515Labels = Sparse.eval nodeValue1515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1515) = mixedMoment B node1515 node1515Labels := rfl
  simpa [nodeValue1515, Sparse.eval] using hc.symm

theorem sound1516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1516 node1516Labels = Sparse.eval nodeValue1516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1516) = mixedMoment B node1516 node1516Labels := rfl
  simpa [nodeValue1516, Sparse.eval] using hc.symm

theorem sound1518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1518 node1518Labels = Sparse.eval nodeValue1518 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1518) = mixedMoment B node1518 node1518Labels := rfl
  simpa [nodeValue1518, Sparse.eval] using hc.symm

theorem sound1519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1519 node1519Labels = Sparse.eval nodeValue1519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1519) = mixedMoment B node1519 node1519Labels := rfl
  simpa [nodeValue1519, Sparse.eval] using hc.symm

theorem sound1520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1520 node1520Labels = Sparse.eval nodeValue1520 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1520) = mixedMoment B node1520 node1520Labels := rfl
  simpa [nodeValue1520, Sparse.eval] using hc.symm

theorem sound1521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1521 node1521Labels = Sparse.eval nodeValue1521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1521) = mixedMoment B node1521 node1521Labels := rfl
  simpa [nodeValue1521, Sparse.eval] using hc.symm

theorem sound1522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1522 node1522Labels = Sparse.eval nodeValue1522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1522) = mixedMoment B node1522 node1522Labels := rfl
  simpa [nodeValue1522, Sparse.eval] using hc.symm

theorem sound1523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1523 node1523Labels = Sparse.eval nodeValue1523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1523) = mixedMoment B node1523 node1523Labels := rfl
  simpa [nodeValue1523, Sparse.eval] using hc.symm

theorem sound1525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1525 node1525Labels = Sparse.eval nodeValue1525 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1525) = mixedMoment B node1525 node1525Labels := rfl
  simpa [nodeValue1525, Sparse.eval] using hc.symm

theorem sound1526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1526 node1526Labels = Sparse.eval nodeValue1526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1526) = mixedMoment B node1526 node1526Labels := rfl
  simpa [nodeValue1526, Sparse.eval] using hc.symm

theorem sound1527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1527 node1527Labels = Sparse.eval nodeValue1527 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1527) = mixedMoment B node1527 node1527Labels := rfl
  simpa [nodeValue1527, Sparse.eval] using hc.symm

theorem sound1528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1528 node1528Labels = Sparse.eval nodeValue1528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1528) = mixedMoment B node1528 node1528Labels := rfl
  simpa [nodeValue1528, Sparse.eval] using hc.symm

theorem sound1529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1529 node1529Labels = Sparse.eval nodeValue1529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1529) = mixedMoment B node1529 node1529Labels := rfl
  simpa [nodeValue1529, Sparse.eval] using hc.symm

theorem sound1530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1530 node1530Labels = Sparse.eval nodeValue1530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1530) = mixedMoment B node1530 node1530Labels := rfl
  simpa [nodeValue1530, Sparse.eval] using hc.symm

theorem sound1531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1531 node1531Labels = Sparse.eval nodeValue1531 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1531) = mixedMoment B node1531 node1531Labels := rfl
  simpa [nodeValue1531, Sparse.eval] using hc.symm

theorem sound1532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1532 node1532Labels = Sparse.eval nodeValue1532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1532) = mixedMoment B node1532 node1532Labels := rfl
  simpa [nodeValue1532, Sparse.eval] using hc.symm

theorem sound1533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1533 node1533Labels = Sparse.eval nodeValue1533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1533) = mixedMoment B node1533 node1533Labels := rfl
  simpa [nodeValue1533, Sparse.eval] using hc.symm

theorem sound1534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1534 node1534Labels = Sparse.eval nodeValue1534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1534) = mixedMoment B node1534 node1534Labels := rfl
  simpa [nodeValue1534, Sparse.eval] using hc.symm

theorem sound1535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1535 node1535Labels = Sparse.eval nodeValue1535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1535) = mixedMoment B node1535 node1535Labels := rfl
  simpa [nodeValue1535, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1536 node1536Labels = Sparse.eval nodeValue1536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1536) = mixedMoment B node1536 node1536Labels := rfl
  simpa [nodeValue1536, Sparse.eval] using hc.symm

theorem sound1537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1537 node1537Labels = Sparse.eval nodeValue1537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1537) = mixedMoment B node1537 node1537Labels := rfl
  simpa [nodeValue1537, Sparse.eval] using hc.symm

theorem sound1538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1538 node1538Labels = Sparse.eval nodeValue1538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1538) = mixedMoment B node1538 node1538Labels := rfl
  simpa [nodeValue1538, Sparse.eval] using hc.symm

theorem sound1539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1539 node1539Labels = Sparse.eval nodeValue1539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1539) = mixedMoment B node1539 node1539Labels := rfl
  simpa [nodeValue1539, Sparse.eval] using hc.symm

theorem sound1540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1540 node1540Labels = Sparse.eval nodeValue1540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1540) = mixedMoment B node1540 node1540Labels := rfl
  simpa [nodeValue1540, Sparse.eval] using hc.symm

theorem sound1541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1541 node1541Labels = Sparse.eval nodeValue1541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1541) = mixedMoment B node1541 node1541Labels := rfl
  simpa [nodeValue1541, Sparse.eval] using hc.symm

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

theorem sound4058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4058 node4058Labels = Sparse.eval nodeValue4058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4058) = mixedMoment B node4058 node4058Labels := rfl
  simpa [nodeValue4058, Sparse.eval] using hc.symm

theorem sound4059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4059 node4059Labels = Sparse.eval nodeValue4059 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4059) = mixedMoment B node4059 node4059Labels := rfl
  simpa [nodeValue4059, Sparse.eval] using hc.symm

theorem sound4060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4060 node4060Labels = Sparse.eval nodeValue4060 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4060) = mixedMoment B node4060 node4060Labels := rfl
  simpa [nodeValue4060, Sparse.eval] using hc.symm

theorem sound4061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4061 node4061Labels = Sparse.eval nodeValue4061 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4061) = mixedMoment B node4061 node4061Labels := rfl
  simpa [nodeValue4061, Sparse.eval] using hc.symm

theorem sound4062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4062 node4062Labels = Sparse.eval nodeValue4062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4062) = mixedMoment B node4062 node4062Labels := rfl
  simpa [nodeValue4062, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2655 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2655 + difference 0 4) (sourceB2655 + difference 4 0) sourceC2655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1541) := by
    have ha : (tripleCharges (sourceA2655 + difference 0 4) (sourceB2655 + difference 4 0) sourceC2655) = raw37330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2655 sourceB2655 sourceC2655 difference raw37330; decide +kernel
    rw [ha]
    exact (canonical37330 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2655 + difference 1 4) (sourceB2655 + difference 4 1) sourceC2655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1534) := by
    have ha : (tripleCharges (sourceA2655 + difference 1 4) (sourceB2655 + difference 4 1) sourceC2655) = raw37331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2655 sourceB2655 sourceC2655 difference raw37331; decide +kernel
    rw [ha]
    exact (canonical37331 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2655 + difference 2 4) (sourceB2655 + difference 4 2) sourceC2655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1534) := by
    have ha : (tripleCharges (sourceA2655 + difference 2 4) (sourceB2655 + difference 4 2) sourceC2655) = raw37332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2655 sourceB2655 sourceC2655 difference raw37332; decide +kernel
    rw [ha]
    exact (canonical37332 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2655 + difference 3 4) (sourceB2655 + difference 4 3) sourceC2655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1534) := by
    have ha : (tripleCharges (sourceA2655 + difference 3 4) (sourceB2655 + difference 4 3) sourceC2655) = raw37333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2655 sourceB2655 sourceC2655 difference raw37333; decide +kernel
    rw [ha]
    exact (canonical37333 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2655 + difference 4 4) (sourceB2655 + difference 4 4) sourceC2655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1534) := by
    have ha : (tripleCharges (sourceA2655 + difference 4 4) (sourceB2655 + difference 4 4) sourceC2655) = raw37334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2655 sourceB2655 sourceC2655 difference raw37334; decide +kernel
    rw [ha]
    exact (canonical37334 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2655 + difference 5 4) (sourceB2655 + difference 4 5) sourceC2655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1541) := by
    have ha : (tripleCharges (sourceA2655 + difference 5 4) (sourceB2655 + difference 4 5) sourceC2655) = raw37335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2655 sourceB2655 sourceC2655 difference raw37335; decide +kernel
    rw [ha]
    exact (canonical37335 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2655 + sourceB2655) sourceC2655) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4062) := by
    have ha : (doubleCharges (sourceA2655 + sourceB2655) sourceC2655) = raw37336 := by
      apply Matrix.ext; unfold doubleCharges sourceA2655 sourceB2655 sourceC2655 raw37336; decide +kernel
    rw [ha]
    exact (canonical37336 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2655 sourceB2655 sourceC2655
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2655, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources83
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2656 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2656 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2656 + difference 0 0) (sourceB2656 + difference 0 0) sourceC2656) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1541) := by
    have ha : (tripleCharges (sourceA2656 + difference 0 0) (sourceB2656 + difference 0 0) sourceC2656) = raw37335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2656 sourceB2656 sourceC2656 difference raw37335; decide +kernel
    rw [ha]
    exact (canonical37335 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2656 + difference 1 0) (sourceB2656 + difference 0 1) sourceC2656) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 686) := by
    have ha : (tripleCharges (sourceA2656 + difference 1 0) (sourceB2656 + difference 0 1) sourceC2656) = raw37337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2656 sourceB2656 sourceC2656 difference raw37337; decide +kernel
    rw [ha]
    exact (canonical37337 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2656 + difference 2 0) (sourceB2656 + difference 0 2) sourceC2656) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 686) := by
    have ha : (tripleCharges (sourceA2656 + difference 2 0) (sourceB2656 + difference 0 2) sourceC2656) = raw37338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2656 sourceB2656 sourceC2656 difference raw37338; decide +kernel
    rw [ha]
    exact (canonical37338 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2656 + difference 3 0) (sourceB2656 + difference 0 3) sourceC2656) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 686) := by
    have ha : (tripleCharges (sourceA2656 + difference 3 0) (sourceB2656 + difference 0 3) sourceC2656) = raw37339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2656 sourceB2656 sourceC2656 difference raw37339; decide +kernel
    rw [ha]
    exact (canonical37339 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2656 + difference 4 0) (sourceB2656 + difference 0 4) sourceC2656) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 686) := by
    have ha : (tripleCharges (sourceA2656 + difference 4 0) (sourceB2656 + difference 0 4) sourceC2656) = raw37340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2656 sourceB2656 sourceC2656 difference raw37340; decide +kernel
    rw [ha]
    exact (canonical37340 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2656 + difference 5 0) (sourceB2656 + difference 0 5) sourceC2656) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 697) := by
    have ha : (tripleCharges (sourceA2656 + difference 5 0) (sourceB2656 + difference 0 5) sourceC2656) = raw37341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2656 sourceB2656 sourceC2656 difference raw37341; decide +kernel
    rw [ha]
    exact (canonical37341 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2656 + sourceB2656) sourceC2656) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4062) := by
    have ha : (doubleCharges (sourceA2656 + sourceB2656) sourceC2656) = raw37336 := by
      apply Matrix.ext; unfold doubleCharges sourceA2656 sourceB2656 sourceC2656 raw37336; decide +kernel
    rw [ha]
    exact (canonical37336 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2656 sourceB2656 sourceC2656
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2656, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2657 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2657 + difference 0 4) (sourceB2657 + difference 4 0) sourceC2657) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA2657 + difference 0 4) (sourceB2657 + difference 4 0) sourceC2657) = raw37342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2657 sourceB2657 sourceC2657 difference raw37342; decide +kernel
    rw [ha]
    exact (canonical37342 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2657 + difference 1 4) (sourceB2657 + difference 4 1) sourceC2657) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA2657 + difference 1 4) (sourceB2657 + difference 4 1) sourceC2657) = raw37343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2657 sourceB2657 sourceC2657 difference raw37343; decide +kernel
    rw [ha]
    exact (canonical37343 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2657 + difference 2 4) (sourceB2657 + difference 4 2) sourceC2657) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA2657 + difference 2 4) (sourceB2657 + difference 4 2) sourceC2657) = raw37344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2657 sourceB2657 sourceC2657 difference raw37344; decide +kernel
    rw [ha]
    exact (canonical37344 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2657 + difference 3 4) (sourceB2657 + difference 4 3) sourceC2657) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA2657 + difference 3 4) (sourceB2657 + difference 4 3) sourceC2657) = raw37345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2657 sourceB2657 sourceC2657 difference raw37345; decide +kernel
    rw [ha]
    exact (canonical37345 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2657 + difference 4 4) (sourceB2657 + difference 4 4) sourceC2657) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1540) := by
    have ha : (tripleCharges (sourceA2657 + difference 4 4) (sourceB2657 + difference 4 4) sourceC2657) = raw37346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2657 sourceB2657 sourceC2657 difference raw37346; decide +kernel
    rw [ha]
    exact (canonical37346 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2657 + difference 5 4) (sourceB2657 + difference 4 5) sourceC2657) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA2657 + difference 5 4) (sourceB2657 + difference 4 5) sourceC2657) = raw37347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2657 sourceB2657 sourceC2657 difference raw37347; decide +kernel
    rw [ha]
    exact (canonical37347 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2657 + sourceB2657) sourceC2657) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (doubleCharges (sourceA2657 + sourceB2657) sourceC2657) = raw37348 := by
      apply Matrix.ext; unfold doubleCharges sourceA2657 sourceB2657 sourceC2657 raw37348; decide +kernel
    rw [ha]
    exact (canonical37348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2657 sourceB2657 sourceC2657
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2657, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2658 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2658 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2658 + difference 0 3) (sourceB2658 + difference 3 0) sourceC2658) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA2658 + difference 0 3) (sourceB2658 + difference 3 0) sourceC2658) = raw37349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2658 sourceB2658 sourceC2658 difference raw37349; decide +kernel
    rw [ha]
    exact (canonical37349 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2658 + difference 1 3) (sourceB2658 + difference 3 1) sourceC2658) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA2658 + difference 1 3) (sourceB2658 + difference 3 1) sourceC2658) = raw37350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2658 sourceB2658 sourceC2658 difference raw37350; decide +kernel
    rw [ha]
    exact (canonical37350 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2658 + difference 2 3) (sourceB2658 + difference 3 2) sourceC2658) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA2658 + difference 2 3) (sourceB2658 + difference 3 2) sourceC2658) = raw37351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2658 sourceB2658 sourceC2658 difference raw37351; decide +kernel
    rw [ha]
    exact (canonical37351 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2658 + difference 3 3) (sourceB2658 + difference 3 3) sourceC2658) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA2658 + difference 3 3) (sourceB2658 + difference 3 3) sourceC2658) = raw37352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2658 sourceB2658 sourceC2658 difference raw37352; decide +kernel
    rw [ha]
    exact (canonical37352 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2658 + difference 4 3) (sourceB2658 + difference 3 4) sourceC2658) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA2658 + difference 4 3) (sourceB2658 + difference 3 4) sourceC2658) = raw37347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2658 sourceB2658 sourceC2658 difference raw37347; decide +kernel
    rw [ha]
    exact (canonical37347 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2658 + difference 5 3) (sourceB2658 + difference 3 5) sourceC2658) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA2658 + difference 5 3) (sourceB2658 + difference 3 5) sourceC2658) = raw37353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2658 sourceB2658 sourceC2658 difference raw37353; decide +kernel
    rw [ha]
    exact (canonical37353 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2658 + sourceB2658) sourceC2658) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (doubleCharges (sourceA2658 + sourceB2658) sourceC2658) = raw37348 := by
      apply Matrix.ext; unfold doubleCharges sourceA2658 sourceB2658 sourceC2658 raw37348; decide +kernel
    rw [ha]
    exact (canonical37348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2658 sourceB2658 sourceC2658
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2658, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2659 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2659 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2659 + difference 0 0) (sourceB2659 + difference 0 0) sourceC2659) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA2659 + difference 0 0) (sourceB2659 + difference 0 0) sourceC2659) = raw37347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2659 sourceB2659 sourceC2659 difference raw37347; decide +kernel
    rw [ha]
    exact (canonical37347 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2659 + difference 1 0) (sourceB2659 + difference 0 1) sourceC2659) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 683) := by
    have ha : (tripleCharges (sourceA2659 + difference 1 0) (sourceB2659 + difference 0 1) sourceC2659) = raw37354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2659 sourceB2659 sourceC2659 difference raw37354; decide +kernel
    rw [ha]
    exact (canonical37354 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2659 + difference 2 0) (sourceB2659 + difference 0 2) sourceC2659) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 683) := by
    have ha : (tripleCharges (sourceA2659 + difference 2 0) (sourceB2659 + difference 0 2) sourceC2659) = raw37355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2659 sourceB2659 sourceC2659 difference raw37355; decide +kernel
    rw [ha]
    exact (canonical37355 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2659 + difference 3 0) (sourceB2659 + difference 0 3) sourceC2659) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 683) := by
    have ha : (tripleCharges (sourceA2659 + difference 3 0) (sourceB2659 + difference 0 3) sourceC2659) = raw37356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2659 sourceB2659 sourceC2659 difference raw37356; decide +kernel
    rw [ha]
    exact (canonical37356 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2659 + difference 4 0) (sourceB2659 + difference 0 4) sourceC2659) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 695) := by
    have ha : (tripleCharges (sourceA2659 + difference 4 0) (sourceB2659 + difference 0 4) sourceC2659) = raw37357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2659 sourceB2659 sourceC2659 difference raw37357; decide +kernel
    rw [ha]
    exact (canonical37357 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2659 + difference 5 0) (sourceB2659 + difference 0 5) sourceC2659) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 691) := by
    have ha : (tripleCharges (sourceA2659 + difference 5 0) (sourceB2659 + difference 0 5) sourceC2659) = raw37358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2659 sourceB2659 sourceC2659 difference raw37358; decide +kernel
    rw [ha]
    exact (canonical37358 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2659 + sourceB2659) sourceC2659) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (doubleCharges (sourceA2659 + sourceB2659) sourceC2659) = raw37348 := by
      apply Matrix.ext; unfold doubleCharges sourceA2659 sourceB2659 sourceC2659 raw37348; decide +kernel
    rw [ha]
    exact (canonical37348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2659 sourceB2659 sourceC2659
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2659, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2663 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2663 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2663 + difference 0 4) (sourceB2663 + difference 4 0) sourceC2663) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1527) := by
    have ha : (tripleCharges (sourceA2663 + difference 0 4) (sourceB2663 + difference 4 0) sourceC2663) = raw37370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2663 sourceB2663 sourceC2663 difference raw37370; decide +kernel
    rw [ha]
    exact (canonical37370 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2663 + difference 1 4) (sourceB2663 + difference 4 1) sourceC2663) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1529) := by
    have ha : (tripleCharges (sourceA2663 + difference 1 4) (sourceB2663 + difference 4 1) sourceC2663) = raw37371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2663 sourceB2663 sourceC2663 difference raw37371; decide +kernel
    rw [ha]
    exact (canonical37371 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2663 + difference 2 4) (sourceB2663 + difference 4 2) sourceC2663) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1529) := by
    have ha : (tripleCharges (sourceA2663 + difference 2 4) (sourceB2663 + difference 4 2) sourceC2663) = raw37372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2663 sourceB2663 sourceC2663 difference raw37372; decide +kernel
    rw [ha]
    exact (canonical37372 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2663 + difference 3 4) (sourceB2663 + difference 4 3) sourceC2663) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1529) := by
    have ha : (tripleCharges (sourceA2663 + difference 3 4) (sourceB2663 + difference 4 3) sourceC2663) = raw37373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2663 sourceB2663 sourceC2663 difference raw37373; decide +kernel
    rw [ha]
    exact (canonical37373 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2663 + difference 4 4) (sourceB2663 + difference 4 4) sourceC2663) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1531) := by
    have ha : (tripleCharges (sourceA2663 + difference 4 4) (sourceB2663 + difference 4 4) sourceC2663) = raw37374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2663 sourceB2663 sourceC2663 difference raw37374; decide +kernel
    rw [ha]
    exact (canonical37374 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2663 + difference 5 4) (sourceB2663 + difference 4 5) sourceC2663) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA2663 + difference 5 4) (sourceB2663 + difference 4 5) sourceC2663) = raw37375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2663 sourceB2663 sourceC2663 difference raw37375; decide +kernel
    rw [ha]
    exact (canonical37375 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2663 + sourceB2663) sourceC2663) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2663 + sourceB2663) sourceC2663) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2663 sourceB2663 sourceC2663 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2663 sourceB2663 sourceC2663
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2663, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2664 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2664 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2664 + difference 0 3) (sourceB2664 + difference 3 0) sourceC2664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA2664 + difference 0 3) (sourceB2664 + difference 3 0) sourceC2664) = raw37377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2664 sourceB2664 sourceC2664 difference raw37377; decide +kernel
    rw [ha]
    exact (canonical37377 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2664 + difference 1 3) (sourceB2664 + difference 3 1) sourceC2664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1523) := by
    have ha : (tripleCharges (sourceA2664 + difference 1 3) (sourceB2664 + difference 3 1) sourceC2664) = raw37378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2664 sourceB2664 sourceC2664 difference raw37378; decide +kernel
    rw [ha]
    exact (canonical37378 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2664 + difference 2 3) (sourceB2664 + difference 3 2) sourceC2664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1523) := by
    have ha : (tripleCharges (sourceA2664 + difference 2 3) (sourceB2664 + difference 3 2) sourceC2664) = raw37379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2664 sourceB2664 sourceC2664 difference raw37379; decide +kernel
    rw [ha]
    exact (canonical37379 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2664 + difference 3 3) (sourceB2664 + difference 3 3) sourceC2664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1523) := by
    have ha : (tripleCharges (sourceA2664 + difference 3 3) (sourceB2664 + difference 3 3) sourceC2664) = raw37380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2664 sourceB2664 sourceC2664 difference raw37380; decide +kernel
    rw [ha]
    exact (canonical37380 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2664 + difference 4 3) (sourceB2664 + difference 3 4) sourceC2664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA2664 + difference 4 3) (sourceB2664 + difference 3 4) sourceC2664) = raw37381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2664 sourceB2664 sourceC2664 difference raw37381; decide +kernel
    rw [ha]
    exact (canonical37381 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2664 + difference 5 3) (sourceB2664 + difference 3 5) sourceC2664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1527) := by
    have ha : (tripleCharges (sourceA2664 + difference 5 3) (sourceB2664 + difference 3 5) sourceC2664) = raw37382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2664 sourceB2664 sourceC2664 difference raw37382; decide +kernel
    rw [ha]
    exact (canonical37382 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2664 + sourceB2664) sourceC2664) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2664 + sourceB2664) sourceC2664) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2664 sourceB2664 sourceC2664 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2664 sourceB2664 sourceC2664
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2664, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2665 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2665 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2665 + difference 0 3) (sourceB2665 + difference 3 0) sourceC2665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA2665 + difference 0 3) (sourceB2665 + difference 3 0) sourceC2665) = raw37383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2665 sourceB2665 sourceC2665 difference raw37383; decide +kernel
    rw [ha]
    exact (canonical37383 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2665 + difference 1 3) (sourceB2665 + difference 3 1) sourceC2665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA2665 + difference 1 3) (sourceB2665 + difference 3 1) sourceC2665) = raw37384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2665 sourceB2665 sourceC2665 difference raw37384; decide +kernel
    rw [ha]
    exact (canonical37384 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2665 + difference 2 3) (sourceB2665 + difference 3 2) sourceC2665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA2665 + difference 2 3) (sourceB2665 + difference 3 2) sourceC2665) = raw37385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2665 sourceB2665 sourceC2665 difference raw37385; decide +kernel
    rw [ha]
    exact (canonical37385 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2665 + difference 3 3) (sourceB2665 + difference 3 3) sourceC2665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA2665 + difference 3 3) (sourceB2665 + difference 3 3) sourceC2665) = raw37386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2665 sourceB2665 sourceC2665 difference raw37386; decide +kernel
    rw [ha]
    exact (canonical37386 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2665 + difference 4 3) (sourceB2665 + difference 3 4) sourceC2665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA2665 + difference 4 3) (sourceB2665 + difference 3 4) sourceC2665) = raw37375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2665 sourceB2665 sourceC2665 difference raw37375; decide +kernel
    rw [ha]
    exact (canonical37375 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2665 + difference 5 3) (sourceB2665 + difference 3 5) sourceC2665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA2665 + difference 5 3) (sourceB2665 + difference 3 5) sourceC2665) = raw37381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2665 sourceB2665 sourceC2665 difference raw37381; decide +kernel
    rw [ha]
    exact (canonical37381 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2665 + sourceB2665) sourceC2665) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2665 + sourceB2665) sourceC2665) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2665 sourceB2665 sourceC2665 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2665 sourceB2665 sourceC2665
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2665, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2667 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2667 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2667 + difference 5 0) (sourceB2667 + difference 0 5) sourceC2667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 696) := by
    have ha : (tripleCharges (sourceA2667 + difference 5 0) (sourceB2667 + difference 0 5) sourceC2667) = raw37391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2667 sourceB2667 sourceC2667 difference raw37391; decide +kernel
    rw [ha]
    exact (canonical37391 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2667 + difference 5 1) (sourceB2667 + difference 1 5) sourceC2667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1496) := by
    have ha : (tripleCharges (sourceA2667 + difference 5 1) (sourceB2667 + difference 1 5) sourceC2667) = raw37392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2667 sourceB2667 sourceC2667 difference raw37392; decide +kernel
    rw [ha]
    exact (canonical37392 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2667 + difference 5 2) (sourceB2667 + difference 2 5) sourceC2667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1496) := by
    have ha : (tripleCharges (sourceA2667 + difference 5 2) (sourceB2667 + difference 2 5) sourceC2667) = raw37393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2667 sourceB2667 sourceC2667 difference raw37393; decide +kernel
    rw [ha]
    exact (canonical37393 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2667 + difference 5 3) (sourceB2667 + difference 3 5) sourceC2667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1496) := by
    have ha : (tripleCharges (sourceA2667 + difference 5 3) (sourceB2667 + difference 3 5) sourceC2667) = raw37394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2667 sourceB2667 sourceC2667 difference raw37394; decide +kernel
    rw [ha]
    exact (canonical37394 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2667 + difference 5 4) (sourceB2667 + difference 4 5) sourceC2667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA2667 + difference 5 4) (sourceB2667 + difference 4 5) sourceC2667) = raw37381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2667 sourceB2667 sourceC2667 difference raw37381; decide +kernel
    rw [ha]
    exact (canonical37381 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2667 + difference 5 5) (sourceB2667 + difference 5 5) sourceC2667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA2667 + difference 5 5) (sourceB2667 + difference 5 5) sourceC2667) = raw37375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2667 sourceB2667 sourceC2667 difference raw37375; decide +kernel
    rw [ha]
    exact (canonical37375 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2667 + sourceB2667) sourceC2667) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2667 + sourceB2667) sourceC2667) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2667 sourceB2667 sourceC2667 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2667 sourceB2667 sourceC2667
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2667, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2669 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2669 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2669 + difference 5 0) (sourceB2669 + difference 0 5) sourceC2669) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 693) := by
    have ha : (tripleCharges (sourceA2669 + difference 5 0) (sourceB2669 + difference 0 5) sourceC2669) = raw37398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2669 sourceB2669 sourceC2669 difference raw37398; decide +kernel
    rw [ha]
    exact (canonical37398 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2669 + difference 5 1) (sourceB2669 + difference 1 5) sourceC2669) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1495) := by
    have ha : (tripleCharges (sourceA2669 + difference 5 1) (sourceB2669 + difference 1 5) sourceC2669) = raw37399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2669 sourceB2669 sourceC2669 difference raw37399; decide +kernel
    rw [ha]
    exact (canonical37399 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2669 + difference 5 2) (sourceB2669 + difference 2 5) sourceC2669) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1495) := by
    have ha : (tripleCharges (sourceA2669 + difference 5 2) (sourceB2669 + difference 2 5) sourceC2669) = raw37400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2669 sourceB2669 sourceC2669 difference raw37400; decide +kernel
    rw [ha]
    exact (canonical37400 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2669 + difference 5 3) (sourceB2669 + difference 3 5) sourceC2669) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1495) := by
    have ha : (tripleCharges (sourceA2669 + difference 5 3) (sourceB2669 + difference 3 5) sourceC2669) = raw37401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2669 sourceB2669 sourceC2669 difference raw37401; decide +kernel
    rw [ha]
    exact (canonical37401 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2669 + difference 5 4) (sourceB2669 + difference 4 5) sourceC2669) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1527) := by
    have ha : (tripleCharges (sourceA2669 + difference 5 4) (sourceB2669 + difference 4 5) sourceC2669) = raw37382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2669 sourceB2669 sourceC2669 difference raw37382; decide +kernel
    rw [ha]
    exact (canonical37382 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2669 + difference 5 5) (sourceB2669 + difference 5 5) sourceC2669) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA2669 + difference 5 5) (sourceB2669 + difference 5 5) sourceC2669) = raw37381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2669 sourceB2669 sourceC2669 difference raw37381; decide +kernel
    rw [ha]
    exact (canonical37381 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2669 + sourceB2669) sourceC2669) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2669 + sourceB2669) sourceC2669) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2669 sourceB2669 sourceC2669 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2669 sourceB2669 sourceC2669
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2669, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2671 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2671 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2671 + difference 0 4) (sourceB2671 + difference 4 0) sourceC2671) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA2671 + difference 0 4) (sourceB2671 + difference 4 0) sourceC2671) = raw37406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2671 sourceB2671 sourceC2671 difference raw37406; decide +kernel
    rw [ha]
    exact (canonical37406 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2671 + difference 1 4) (sourceB2671 + difference 4 1) sourceC2671) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA2671 + difference 1 4) (sourceB2671 + difference 4 1) sourceC2671) = raw37407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2671 sourceB2671 sourceC2671 difference raw37407; decide +kernel
    rw [ha]
    exact (canonical37407 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2671 + difference 2 4) (sourceB2671 + difference 4 2) sourceC2671) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA2671 + difference 2 4) (sourceB2671 + difference 4 2) sourceC2671) = raw37408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2671 sourceB2671 sourceC2671 difference raw37408; decide +kernel
    rw [ha]
    exact (canonical37408 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2671 + difference 3 4) (sourceB2671 + difference 4 3) sourceC2671) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1535) := by
    have ha : (tripleCharges (sourceA2671 + difference 3 4) (sourceB2671 + difference 4 3) sourceC2671) = raw37409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2671 sourceB2671 sourceC2671 difference raw37409; decide +kernel
    rw [ha]
    exact (canonical37409 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2671 + difference 4 4) (sourceB2671 + difference 4 4) sourceC2671) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA2671 + difference 4 4) (sourceB2671 + difference 4 4) sourceC2671) = raw37410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2671 sourceB2671 sourceC2671 difference raw37410; decide +kernel
    rw [ha]
    exact (canonical37410 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2671 + difference 5 4) (sourceB2671 + difference 4 5) sourceC2671) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA2671 + difference 5 4) (sourceB2671 + difference 4 5) sourceC2671) = raw37411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2671 sourceB2671 sourceC2671 difference raw37411; decide +kernel
    rw [ha]
    exact (canonical37411 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2671 + sourceB2671) sourceC2671) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (doubleCharges (sourceA2671 + sourceB2671) sourceC2671) = raw37412 := by
      apply Matrix.ext; unfold doubleCharges sourceA2671 sourceB2671 sourceC2671 raw37412; decide +kernel
    rw [ha]
    exact (canonical37412 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2671 sourceB2671 sourceC2671
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2671, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2672 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2672 + difference 0 4) (sourceB2672 + difference 4 0) sourceC2672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA2672 + difference 0 4) (sourceB2672 + difference 4 0) sourceC2672) = raw37413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2672 sourceB2672 sourceC2672 difference raw37413; decide +kernel
    rw [ha]
    exact (canonical37413 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2672 + difference 1 4) (sourceB2672 + difference 4 1) sourceC2672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1528) := by
    have ha : (tripleCharges (sourceA2672 + difference 1 4) (sourceB2672 + difference 4 1) sourceC2672) = raw37414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2672 sourceB2672 sourceC2672 difference raw37414; decide +kernel
    rw [ha]
    exact (canonical37414 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2672 + difference 2 4) (sourceB2672 + difference 4 2) sourceC2672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1528) := by
    have ha : (tripleCharges (sourceA2672 + difference 2 4) (sourceB2672 + difference 4 2) sourceC2672) = raw37415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2672 sourceB2672 sourceC2672 difference raw37415; decide +kernel
    rw [ha]
    exact (canonical37415 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2672 + difference 3 4) (sourceB2672 + difference 4 3) sourceC2672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA2672 + difference 3 4) (sourceB2672 + difference 4 3) sourceC2672) = raw37416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2672 sourceB2672 sourceC2672 difference raw37416; decide +kernel
    rw [ha]
    exact (canonical37416 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2672 + difference 4 4) (sourceB2672 + difference 4 4) sourceC2672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA2672 + difference 4 4) (sourceB2672 + difference 4 4) sourceC2672) = raw37417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2672 sourceB2672 sourceC2672 difference raw37417; decide +kernel
    rw [ha]
    exact (canonical37417 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2672 + difference 5 4) (sourceB2672 + difference 4 5) sourceC2672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1535) := by
    have ha : (tripleCharges (sourceA2672 + difference 5 4) (sourceB2672 + difference 4 5) sourceC2672) = raw37409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2672 sourceB2672 sourceC2672 difference raw37409; decide +kernel
    rw [ha]
    exact (canonical37409 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2672 + sourceB2672) sourceC2672) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (doubleCharges (sourceA2672 + sourceB2672) sourceC2672) = raw37412 := by
      apply Matrix.ext; unfold doubleCharges sourceA2672 sourceB2672 sourceC2672 raw37412; decide +kernel
    rw [ha]
    exact (canonical37412 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2672 sourceB2672 sourceC2672
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2672, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2673 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2673 + difference 0 2) (sourceB2673 + difference 2 0) sourceC2673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1535) := by
    have ha : (tripleCharges (sourceA2673 + difference 0 2) (sourceB2673 + difference 2 0) sourceC2673) = raw37418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2673 sourceB2673 sourceC2673 difference raw37418; decide +kernel
    rw [ha]
    exact (canonical37418 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2673 + difference 1 2) (sourceB2673 + difference 2 1) sourceC2673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1505) := by
    have ha : (tripleCharges (sourceA2673 + difference 1 2) (sourceB2673 + difference 2 1) sourceC2673) = raw37419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2673 sourceB2673 sourceC2673 difference raw37419; decide +kernel
    rw [ha]
    exact (canonical37419 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2673 + difference 2 2) (sourceB2673 + difference 2 2) sourceC2673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1505) := by
    have ha : (tripleCharges (sourceA2673 + difference 2 2) (sourceB2673 + difference 2 2) sourceC2673) = raw37420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2673 sourceB2673 sourceC2673 difference raw37420; decide +kernel
    rw [ha]
    exact (canonical37420 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2673 + difference 3 2) (sourceB2673 + difference 2 3) sourceC2673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA2673 + difference 3 2) (sourceB2673 + difference 2 3) sourceC2673) = raw37421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2673 sourceB2673 sourceC2673 difference raw37421; decide +kernel
    rw [ha]
    exact (canonical37421 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2673 + difference 4 2) (sourceB2673 + difference 2 4) sourceC2673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA2673 + difference 4 2) (sourceB2673 + difference 2 4) sourceC2673) = raw37411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2673 sourceB2673 sourceC2673 difference raw37411; decide +kernel
    rw [ha]
    exact (canonical37411 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2673 + difference 5 2) (sourceB2673 + difference 2 5) sourceC2673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA2673 + difference 5 2) (sourceB2673 + difference 2 5) sourceC2673) = raw37422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2673 sourceB2673 sourceC2673 difference raw37422; decide +kernel
    rw [ha]
    exact (canonical37422 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2673 + sourceB2673) sourceC2673) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (doubleCharges (sourceA2673 + sourceB2673) sourceC2673) = raw37412 := by
      apply Matrix.ext; unfold doubleCharges sourceA2673 sourceB2673 sourceC2673 raw37412; decide +kernel
    rw [ha]
    exact (canonical37412 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2673 sourceB2673 sourceC2673
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2673, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2679 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2679 + difference 0 5) (sourceB2679 + difference 5 0) sourceC2679) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1525) := by
    have ha : (tripleCharges (sourceA2679 + difference 0 5) (sourceB2679 + difference 5 0) sourceC2679) = raw37441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2679 sourceB2679 sourceC2679 difference raw37441; decide +kernel
    rw [ha]
    exact (canonical37441 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2679 + difference 1 5) (sourceB2679 + difference 5 1) sourceC2679) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA2679 + difference 1 5) (sourceB2679 + difference 5 1) sourceC2679) = raw37442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2679 sourceB2679 sourceC2679 difference raw37442; decide +kernel
    rw [ha]
    exact (canonical37442 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2679 + difference 2 5) (sourceB2679 + difference 5 2) sourceC2679) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA2679 + difference 2 5) (sourceB2679 + difference 5 2) sourceC2679) = raw37443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2679 sourceB2679 sourceC2679 difference raw37443; decide +kernel
    rw [ha]
    exact (canonical37443 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2679 + difference 3 5) (sourceB2679 + difference 5 3) sourceC2679) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1525) := by
    have ha : (tripleCharges (sourceA2679 + difference 3 5) (sourceB2679 + difference 5 3) sourceC2679) = raw37444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2679 sourceB2679 sourceC2679 difference raw37444; decide +kernel
    rw [ha]
    exact (canonical37444 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2679 + difference 4 5) (sourceB2679 + difference 5 4) sourceC2679) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA2679 + difference 4 5) (sourceB2679 + difference 5 4) sourceC2679) = raw37445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2679 sourceB2679 sourceC2679 difference raw37445; decide +kernel
    rw [ha]
    exact (canonical37445 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2679 + difference 5 5) (sourceB2679 + difference 5 5) sourceC2679) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA2679 + difference 5 5) (sourceB2679 + difference 5 5) sourceC2679) = raw37446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2679 sourceB2679 sourceC2679 difference raw37446; decide +kernel
    rw [ha]
    exact (canonical37446 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2679 + sourceB2679) sourceC2679) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (doubleCharges (sourceA2679 + sourceB2679) sourceC2679) = raw37447 := by
      apply Matrix.ext; unfold doubleCharges sourceA2679 sourceB2679 sourceC2679 raw37447; decide +kernel
    rw [ha]
    exact (canonical37447 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2679 sourceB2679 sourceC2679
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2679, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2680 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2680 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2680 + difference 0 3) (sourceB2680 + difference 3 0) sourceC2680) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA2680 + difference 0 3) (sourceB2680 + difference 3 0) sourceC2680) = raw37448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2680 sourceB2680 sourceC2680 difference raw37448; decide +kernel
    rw [ha]
    exact (canonical37448 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2680 + difference 1 3) (sourceB2680 + difference 3 1) sourceC2680) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA2680 + difference 1 3) (sourceB2680 + difference 3 1) sourceC2680) = raw37449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2680 sourceB2680 sourceC2680 difference raw37449; decide +kernel
    rw [ha]
    exact (canonical37449 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2680 + difference 2 3) (sourceB2680 + difference 3 2) sourceC2680) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA2680 + difference 2 3) (sourceB2680 + difference 3 2) sourceC2680) = raw37450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2680 sourceB2680 sourceC2680 difference raw37450; decide +kernel
    rw [ha]
    exact (canonical37450 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2680 + difference 3 3) (sourceB2680 + difference 3 3) sourceC2680) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1526) := by
    have ha : (tripleCharges (sourceA2680 + difference 3 3) (sourceB2680 + difference 3 3) sourceC2680) = raw37451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2680 sourceB2680 sourceC2680 difference raw37451; decide +kernel
    rw [ha]
    exact (canonical37451 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2680 + difference 4 3) (sourceB2680 + difference 3 4) sourceC2680) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1536) := by
    have ha : (tripleCharges (sourceA2680 + difference 4 3) (sourceB2680 + difference 3 4) sourceC2680) = raw37452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2680 sourceB2680 sourceC2680 difference raw37452; decide +kernel
    rw [ha]
    exact (canonical37452 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2680 + difference 5 3) (sourceB2680 + difference 3 5) sourceC2680) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1525) := by
    have ha : (tripleCharges (sourceA2680 + difference 5 3) (sourceB2680 + difference 3 5) sourceC2680) = raw37444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2680 sourceB2680 sourceC2680 difference raw37444; decide +kernel
    rw [ha]
    exact (canonical37444 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2680 + sourceB2680) sourceC2680) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (doubleCharges (sourceA2680 + sourceB2680) sourceC2680) = raw37447 := by
      apply Matrix.ext; unfold doubleCharges sourceA2680 sourceB2680 sourceC2680 raw37447; decide +kernel
    rw [ha]
    exact (canonical37447 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2680 sourceB2680 sourceC2680
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2680, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2681 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2681 + difference 0 2) (sourceB2681 + difference 2 0) sourceC2681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1536) := by
    have ha : (tripleCharges (sourceA2681 + difference 0 2) (sourceB2681 + difference 2 0) sourceC2681) = raw37453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2681 sourceB2681 sourceC2681 difference raw37453; decide +kernel
    rw [ha]
    exact (canonical37453 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2681 + difference 1 2) (sourceB2681 + difference 2 1) sourceC2681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA2681 + difference 1 2) (sourceB2681 + difference 2 1) sourceC2681) = raw37454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2681 sourceB2681 sourceC2681 difference raw37454; decide +kernel
    rw [ha]
    exact (canonical37454 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2681 + difference 2 2) (sourceB2681 + difference 2 2) sourceC2681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA2681 + difference 2 2) (sourceB2681 + difference 2 2) sourceC2681) = raw37455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2681 sourceB2681 sourceC2681 difference raw37455; decide +kernel
    rw [ha]
    exact (canonical37455 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2681 + difference 3 2) (sourceB2681 + difference 2 3) sourceC2681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1536) := by
    have ha : (tripleCharges (sourceA2681 + difference 3 2) (sourceB2681 + difference 2 3) sourceC2681) = raw37452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2681 sourceB2681 sourceC2681 difference raw37452; decide +kernel
    rw [ha]
    exact (canonical37452 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2681 + difference 4 2) (sourceB2681 + difference 2 4) sourceC2681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA2681 + difference 4 2) (sourceB2681 + difference 2 4) sourceC2681) = raw37456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2681 sourceB2681 sourceC2681 difference raw37456; decide +kernel
    rw [ha]
    exact (canonical37456 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2681 + difference 5 2) (sourceB2681 + difference 2 5) sourceC2681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA2681 + difference 5 2) (sourceB2681 + difference 2 5) sourceC2681) = raw37445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2681 sourceB2681 sourceC2681 difference raw37445; decide +kernel
    rw [ha]
    exact (canonical37445 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2681 + sourceB2681) sourceC2681) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (doubleCharges (sourceA2681 + sourceB2681) sourceC2681) = raw37447 := by
      apply Matrix.ext; unfold doubleCharges sourceA2681 sourceB2681 sourceC2681 raw37447; decide +kernel
    rw [ha]
    exact (canonical37447 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2681 sourceB2681 sourceC2681
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2681, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2112 : Integer.Sparse.reindex keyMap MixedData.row2112 = numericRow2112 := by decide +kernel

theorem numericCheck2112 (x : Master → ℝ) : Integer.Sparse.eval numericRow2112 x =
    (1 : ℝ) * reducedSource2112 x := by
  norm_num [numericRow2112, reducedSource2112, Integer.Sparse.eval, Sparse.eval, nodeValue1534, nodeValue1541, nodeValue4062]

theorem reindexCheck2113 : Integer.Sparse.reindex keyMap MixedData.row2113 = numericRow2113 := by decide +kernel

theorem numericCheck2113 (x : Master → ℝ) : Integer.Sparse.eval numericRow2113 x =
    (1 : ℝ) * reducedSource2113 x := by
  norm_num [numericRow2113, reducedSource2113, Integer.Sparse.eval, Sparse.eval, nodeValue686, nodeValue697, nodeValue1541, nodeValue4062]

theorem reindexCheck2114 : Integer.Sparse.reindex keyMap MixedData.row2114 = numericRow2114 := by decide +kernel

theorem numericCheck2114 (x : Master → ℝ) : Integer.Sparse.eval numericRow2114 x =
    (1 : ℝ) * reducedSource2114 x := by
  norm_num [numericRow2114, reducedSource2114, Integer.Sparse.eval, Sparse.eval, nodeValue1521, nodeValue1532, nodeValue1537, nodeValue1540, nodeValue4060]

theorem reindexCheck2115 : Integer.Sparse.reindex keyMap MixedData.row2115 = numericRow2115 := by decide +kernel

theorem numericCheck2115 (x : Master → ℝ) : Integer.Sparse.eval numericRow2115 x =
    (1 : ℝ) * reducedSource2115 x := by
  norm_num [numericRow2115, reducedSource2115, Integer.Sparse.eval, Sparse.eval, nodeValue1516, nodeValue1521, nodeValue1537, nodeValue4060]

theorem reindexCheck2116 : Integer.Sparse.reindex keyMap MixedData.row2116 = numericRow2116 := by decide +kernel

theorem numericCheck2116 (x : Master → ℝ) : Integer.Sparse.eval numericRow2116 x =
    (1 : ℝ) * reducedSource2116 x := by
  norm_num [numericRow2116, reducedSource2116, Integer.Sparse.eval, Sparse.eval, nodeValue683, nodeValue691, nodeValue695, nodeValue1537, nodeValue4060]

theorem reindexCheck2117 : Integer.Sparse.reindex keyMap MixedData.row2117 = numericRow2117 := by decide +kernel

theorem numericCheck2117 (x : Master → ℝ) : Integer.Sparse.eval numericRow2117 x =
    (1 : ℝ) * reducedSource2117 x := by
  norm_num [numericRow2117, reducedSource2117, Integer.Sparse.eval, Sparse.eval, nodeValue1527, nodeValue1529, nodeValue1531, nodeValue1539, nodeValue4061]

theorem reindexCheck2118 : Integer.Sparse.reindex keyMap MixedData.row2118 = numericRow2118 := by decide +kernel

theorem numericCheck2118 (x : Master → ℝ) : Integer.Sparse.eval numericRow2118 x =
    (1 : ℝ) * reducedSource2118 x := by
  norm_num [numericRow2118, reducedSource2118, Integer.Sparse.eval, Sparse.eval, nodeValue1523, nodeValue1527, nodeValue1538, nodeValue1539, nodeValue4061]

theorem reindexCheck2119 : Integer.Sparse.reindex keyMap MixedData.row2119 = numericRow2119 := by decide +kernel

theorem numericCheck2119 (x : Master → ℝ) : Integer.Sparse.eval numericRow2119 x =
    (1 : ℝ) * reducedSource2119 x := by
  norm_num [numericRow2119, reducedSource2119, Integer.Sparse.eval, Sparse.eval, nodeValue1533, nodeValue1538, nodeValue1539, nodeValue4061]

theorem reindexCheck2120 : Integer.Sparse.reindex keyMap MixedData.row2120 = numericRow2120 := by decide +kernel

theorem numericCheck2120 (x : Master → ℝ) : Integer.Sparse.eval numericRow2120 x =
    (1 : ℝ) * reducedSource2120 x := by
  norm_num [numericRow2120, reducedSource2120, Integer.Sparse.eval, Sparse.eval, nodeValue696, nodeValue1496, nodeValue1538, nodeValue1539, nodeValue4061]

theorem reindexCheck2121 : Integer.Sparse.reindex keyMap MixedData.row2121 = numericRow2121 := by decide +kernel

theorem numericCheck2121 (x : Master → ℝ) : Integer.Sparse.eval numericRow2121 x =
    (1 : ℝ) * reducedSource2121 x := by
  norm_num [numericRow2121, reducedSource2121, Integer.Sparse.eval, Sparse.eval, nodeValue693, nodeValue1495, nodeValue1527, nodeValue1538, nodeValue4061]

theorem reindexCheck2122 : Integer.Sparse.reindex keyMap MixedData.row2122 = numericRow2122 := by decide +kernel

theorem numericCheck2122 (x : Master → ℝ) : Integer.Sparse.eval numericRow2122 x =
    (1 : ℝ) * reducedSource2122 x := by
  norm_num [numericRow2122, reducedSource2122, Integer.Sparse.eval, Sparse.eval, nodeValue1514, nodeValue1518, nodeValue1520, nodeValue1535, nodeValue4058]

theorem reindexCheck2123 : Integer.Sparse.reindex keyMap MixedData.row2123 = numericRow2123 := by decide +kernel

theorem numericCheck2123 (x : Master → ℝ) : Integer.Sparse.eval numericRow2123 x =
    (1 : ℝ) * reducedSource2123 x := by
  norm_num [numericRow2123, reducedSource2123, Integer.Sparse.eval, Sparse.eval, nodeValue1509, nodeValue1528, nodeValue1530, nodeValue1535, nodeValue4058]

theorem reindexCheck2124 : Integer.Sparse.reindex keyMap MixedData.row2124 = numericRow2124 := by decide +kernel

theorem numericCheck2124 (x : Master → ℝ) : Integer.Sparse.eval numericRow2124 x =
    (1 : ℝ) * reducedSource2124 x := by
  norm_num [numericRow2124, reducedSource2124, Integer.Sparse.eval, Sparse.eval, nodeValue1505, nodeValue1509, nodeValue1518, nodeValue1535, nodeValue4058]

theorem reindexCheck2125 : Integer.Sparse.reindex keyMap MixedData.row2125 = numericRow2125 := by decide +kernel

theorem numericCheck2125 (x : Master → ℝ) : Integer.Sparse.eval numericRow2125 x =
    (1 : ℝ) * reducedSource2125 x := by
  norm_num [numericRow2125, reducedSource2125, Integer.Sparse.eval, Sparse.eval, nodeValue1511, nodeValue1513, nodeValue1519, nodeValue1525, nodeValue4059]

theorem reindexCheck2126 : Integer.Sparse.reindex keyMap MixedData.row2126 = numericRow2126 := by decide +kernel

theorem numericCheck2126 (x : Master → ℝ) : Integer.Sparse.eval numericRow2126 x =
    (1 : ℝ) * reducedSource2126 x := by
  norm_num [numericRow2126, reducedSource2126, Integer.Sparse.eval, Sparse.eval, nodeValue1519, nodeValue1522, nodeValue1525, nodeValue1526, nodeValue1536, nodeValue4059]

theorem reindexCheck2127 : Integer.Sparse.reindex keyMap MixedData.row2127 = numericRow2127 := by decide +kernel

theorem numericCheck2127 (x : Master → ℝ) : Integer.Sparse.eval numericRow2127 x =
    (1 : ℝ) * reducedSource2127 x := by
  norm_num [numericRow2127, reducedSource2127, Integer.Sparse.eval, Sparse.eval, nodeValue1515, nodeValue1519, nodeValue1536, nodeValue4059]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2112 (mixedVector B) = 0 := by
  have h1534 : mixedVector B (Sum.inr 1534) = Sparse.eval nodeValue1534 (mixedVector B) := by
    change mixedMoment B node1534 node1534Labels = _
    exact sound1534 B hB hF
  have h1541 : mixedVector B (Sum.inr 1541) = Sparse.eval nodeValue1541 (mixedVector B) := by
    change mixedMoment B node1541 node1541Labels = _
    exact sound1541 B hB hF
  have h4062 : mixedVector B (Sum.inr 4062) = Sparse.eval nodeValue4062 (mixedVector B) := by
    change mixedMoment B node4062 node4062Labels = _
    exact sound4062 B hB hF
  simpa only [sourceForm2655, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1534, h1541, h4062, reducedSource2112] using sourceEq2655 B hB

theorem rowSound2112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2112 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2112, numericCheck2112, reducedZero2112 B hB hF, mul_zero]

theorem reducedZero2113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2113 (mixedVector B) = 0 := by
  have h686 : mixedVector B (Sum.inr 686) = Sparse.eval nodeValue686 (mixedVector B) := by
    change mixedMoment B node686 node686Labels = _
    exact sound686 B hB hF
  have h697 : mixedVector B (Sum.inr 697) = Sparse.eval nodeValue697 (mixedVector B) := by
    change mixedMoment B node697 node697Labels = _
    exact sound697 B hB hF
  have h1541 : mixedVector B (Sum.inr 1541) = Sparse.eval nodeValue1541 (mixedVector B) := by
    change mixedMoment B node1541 node1541Labels = _
    exact sound1541 B hB hF
  have h4062 : mixedVector B (Sum.inr 4062) = Sparse.eval nodeValue4062 (mixedVector B) := by
    change mixedMoment B node4062 node4062Labels = _
    exact sound4062 B hB hF
  simpa only [sourceForm2656, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h686, h697, h1541, h4062, reducedSource2113] using sourceEq2656 B hB

theorem rowSound2113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2113 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2113, numericCheck2113, reducedZero2113 B hB hF, mul_zero]

theorem reducedZero2114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2114 (mixedVector B) = 0 := by
  have h1521 : mixedVector B (Sum.inr 1521) = Sparse.eval nodeValue1521 (mixedVector B) := by
    change mixedMoment B node1521 node1521Labels = _
    exact sound1521 B hB hF
  have h1532 : mixedVector B (Sum.inr 1532) = Sparse.eval nodeValue1532 (mixedVector B) := by
    change mixedMoment B node1532 node1532Labels = _
    exact sound1532 B hB hF
  have h1537 : mixedVector B (Sum.inr 1537) = Sparse.eval nodeValue1537 (mixedVector B) := by
    change mixedMoment B node1537 node1537Labels = _
    exact sound1537 B hB hF
  have h1540 : mixedVector B (Sum.inr 1540) = Sparse.eval nodeValue1540 (mixedVector B) := by
    change mixedMoment B node1540 node1540Labels = _
    exact sound1540 B hB hF
  have h4060 : mixedVector B (Sum.inr 4060) = Sparse.eval nodeValue4060 (mixedVector B) := by
    change mixedMoment B node4060 node4060Labels = _
    exact sound4060 B hB hF
  simpa only [sourceForm2657, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1521, h1532, h1537, h1540, h4060, reducedSource2114] using sourceEq2657 B hB

theorem rowSound2114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2114 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2114, numericCheck2114, reducedZero2114 B hB hF, mul_zero]

theorem reducedZero2115 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2115 (mixedVector B) = 0 := by
  have h1516 : mixedVector B (Sum.inr 1516) = Sparse.eval nodeValue1516 (mixedVector B) := by
    change mixedMoment B node1516 node1516Labels = _
    exact sound1516 B hB hF
  have h1521 : mixedVector B (Sum.inr 1521) = Sparse.eval nodeValue1521 (mixedVector B) := by
    change mixedMoment B node1521 node1521Labels = _
    exact sound1521 B hB hF
  have h1537 : mixedVector B (Sum.inr 1537) = Sparse.eval nodeValue1537 (mixedVector B) := by
    change mixedMoment B node1537 node1537Labels = _
    exact sound1537 B hB hF
  have h4060 : mixedVector B (Sum.inr 4060) = Sparse.eval nodeValue4060 (mixedVector B) := by
    change mixedMoment B node4060 node4060Labels = _
    exact sound4060 B hB hF
  simpa only [sourceForm2658, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1516, h1521, h1537, h4060, reducedSource2115] using sourceEq2658 B hB

theorem rowSound2115 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2115 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2115, numericCheck2115, reducedZero2115 B hB hF, mul_zero]

theorem reducedZero2116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2116 (mixedVector B) = 0 := by
  have h683 : mixedVector B (Sum.inr 683) = Sparse.eval nodeValue683 (mixedVector B) := by
    change mixedMoment B node683 node683Labels = _
    exact sound683 B hB hF
  have h691 : mixedVector B (Sum.inr 691) = Sparse.eval nodeValue691 (mixedVector B) := by
    change mixedMoment B node691 node691Labels = _
    exact sound691 B hB hF
  have h695 : mixedVector B (Sum.inr 695) = Sparse.eval nodeValue695 (mixedVector B) := by
    change mixedMoment B node695 node695Labels = _
    exact sound695 B hB hF
  have h1537 : mixedVector B (Sum.inr 1537) = Sparse.eval nodeValue1537 (mixedVector B) := by
    change mixedMoment B node1537 node1537Labels = _
    exact sound1537 B hB hF
  have h4060 : mixedVector B (Sum.inr 4060) = Sparse.eval nodeValue4060 (mixedVector B) := by
    change mixedMoment B node4060 node4060Labels = _
    exact sound4060 B hB hF
  simpa only [sourceForm2659, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h683, h691, h695, h1537, h4060, reducedSource2116] using sourceEq2659 B hB

theorem rowSound2116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2116 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2116, numericCheck2116, reducedZero2116 B hB hF, mul_zero]

theorem reducedZero2117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2117 (mixedVector B) = 0 := by
  have h1527 : mixedVector B (Sum.inr 1527) = Sparse.eval nodeValue1527 (mixedVector B) := by
    change mixedMoment B node1527 node1527Labels = _
    exact sound1527 B hB hF
  have h1529 : mixedVector B (Sum.inr 1529) = Sparse.eval nodeValue1529 (mixedVector B) := by
    change mixedMoment B node1529 node1529Labels = _
    exact sound1529 B hB hF
  have h1531 : mixedVector B (Sum.inr 1531) = Sparse.eval nodeValue1531 (mixedVector B) := by
    change mixedMoment B node1531 node1531Labels = _
    exact sound1531 B hB hF
  have h1539 : mixedVector B (Sum.inr 1539) = Sparse.eval nodeValue1539 (mixedVector B) := by
    change mixedMoment B node1539 node1539Labels = _
    exact sound1539 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  simpa only [sourceForm2663, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1527, h1529, h1531, h1539, h4061, reducedSource2117] using sourceEq2663 B hB

theorem rowSound2117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2117 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2117, numericCheck2117, reducedZero2117 B hB hF, mul_zero]

theorem reducedZero2118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2118 (mixedVector B) = 0 := by
  have h1523 : mixedVector B (Sum.inr 1523) = Sparse.eval nodeValue1523 (mixedVector B) := by
    change mixedMoment B node1523 node1523Labels = _
    exact sound1523 B hB hF
  have h1527 : mixedVector B (Sum.inr 1527) = Sparse.eval nodeValue1527 (mixedVector B) := by
    change mixedMoment B node1527 node1527Labels = _
    exact sound1527 B hB hF
  have h1538 : mixedVector B (Sum.inr 1538) = Sparse.eval nodeValue1538 (mixedVector B) := by
    change mixedMoment B node1538 node1538Labels = _
    exact sound1538 B hB hF
  have h1539 : mixedVector B (Sum.inr 1539) = Sparse.eval nodeValue1539 (mixedVector B) := by
    change mixedMoment B node1539 node1539Labels = _
    exact sound1539 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  simpa only [sourceForm2664, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1523, h1527, h1538, h1539, h4061, reducedSource2118] using sourceEq2664 B hB

theorem rowSound2118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2118 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2118, numericCheck2118, reducedZero2118 B hB hF, mul_zero]

theorem reducedZero2119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2119 (mixedVector B) = 0 := by
  have h1533 : mixedVector B (Sum.inr 1533) = Sparse.eval nodeValue1533 (mixedVector B) := by
    change mixedMoment B node1533 node1533Labels = _
    exact sound1533 B hB hF
  have h1538 : mixedVector B (Sum.inr 1538) = Sparse.eval nodeValue1538 (mixedVector B) := by
    change mixedMoment B node1538 node1538Labels = _
    exact sound1538 B hB hF
  have h1539 : mixedVector B (Sum.inr 1539) = Sparse.eval nodeValue1539 (mixedVector B) := by
    change mixedMoment B node1539 node1539Labels = _
    exact sound1539 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  simpa only [sourceForm2665, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1533, h1538, h1539, h4061, reducedSource2119] using sourceEq2665 B hB

theorem rowSound2119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2119 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2119, numericCheck2119, reducedZero2119 B hB hF, mul_zero]

theorem reducedZero2120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2120 (mixedVector B) = 0 := by
  have h696 : mixedVector B (Sum.inr 696) = Sparse.eval nodeValue696 (mixedVector B) := by
    change mixedMoment B node696 node696Labels = _
    exact sound696 B hB hF
  have h1496 : mixedVector B (Sum.inr 1496) = Sparse.eval nodeValue1496 (mixedVector B) := by
    change mixedMoment B node1496 node1496Labels = _
    exact sound1496 B hB hF
  have h1538 : mixedVector B (Sum.inr 1538) = Sparse.eval nodeValue1538 (mixedVector B) := by
    change mixedMoment B node1538 node1538Labels = _
    exact sound1538 B hB hF
  have h1539 : mixedVector B (Sum.inr 1539) = Sparse.eval nodeValue1539 (mixedVector B) := by
    change mixedMoment B node1539 node1539Labels = _
    exact sound1539 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  simpa only [sourceForm2667, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h696, h1496, h1538, h1539, h4061, reducedSource2120] using sourceEq2667 B hB

theorem rowSound2120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2120 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2120, numericCheck2120, reducedZero2120 B hB hF, mul_zero]

theorem reducedZero2121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2121 (mixedVector B) = 0 := by
  have h693 : mixedVector B (Sum.inr 693) = Sparse.eval nodeValue693 (mixedVector B) := by
    change mixedMoment B node693 node693Labels = _
    exact sound693 B hB hF
  have h1495 : mixedVector B (Sum.inr 1495) = Sparse.eval nodeValue1495 (mixedVector B) := by
    change mixedMoment B node1495 node1495Labels = _
    exact sound1495 B hB hF
  have h1527 : mixedVector B (Sum.inr 1527) = Sparse.eval nodeValue1527 (mixedVector B) := by
    change mixedMoment B node1527 node1527Labels = _
    exact sound1527 B hB hF
  have h1538 : mixedVector B (Sum.inr 1538) = Sparse.eval nodeValue1538 (mixedVector B) := by
    change mixedMoment B node1538 node1538Labels = _
    exact sound1538 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  simpa only [sourceForm2669, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h693, h1495, h1527, h1538, h4061, reducedSource2121] using sourceEq2669 B hB

theorem rowSound2121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2121 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2121, numericCheck2121, reducedZero2121 B hB hF, mul_zero]

theorem reducedZero2122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2122 (mixedVector B) = 0 := by
  have h1514 : mixedVector B (Sum.inr 1514) = Sparse.eval nodeValue1514 (mixedVector B) := by
    change mixedMoment B node1514 node1514Labels = _
    exact sound1514 B hB hF
  have h1518 : mixedVector B (Sum.inr 1518) = Sparse.eval nodeValue1518 (mixedVector B) := by
    change mixedMoment B node1518 node1518Labels = _
    exact sound1518 B hB hF
  have h1520 : mixedVector B (Sum.inr 1520) = Sparse.eval nodeValue1520 (mixedVector B) := by
    change mixedMoment B node1520 node1520Labels = _
    exact sound1520 B hB hF
  have h1535 : mixedVector B (Sum.inr 1535) = Sparse.eval nodeValue1535 (mixedVector B) := by
    change mixedMoment B node1535 node1535Labels = _
    exact sound1535 B hB hF
  have h4058 : mixedVector B (Sum.inr 4058) = Sparse.eval nodeValue4058 (mixedVector B) := by
    change mixedMoment B node4058 node4058Labels = _
    exact sound4058 B hB hF
  simpa only [sourceForm2671, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1514, h1518, h1520, h1535, h4058, reducedSource2122] using sourceEq2671 B hB

theorem rowSound2122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2122 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2122, numericCheck2122, reducedZero2122 B hB hF, mul_zero]

theorem reducedZero2123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2123 (mixedVector B) = 0 := by
  have h1509 : mixedVector B (Sum.inr 1509) = Sparse.eval nodeValue1509 (mixedVector B) := by
    change mixedMoment B node1509 node1509Labels = _
    exact sound1509 B hB hF
  have h1528 : mixedVector B (Sum.inr 1528) = Sparse.eval nodeValue1528 (mixedVector B) := by
    change mixedMoment B node1528 node1528Labels = _
    exact sound1528 B hB hF
  have h1530 : mixedVector B (Sum.inr 1530) = Sparse.eval nodeValue1530 (mixedVector B) := by
    change mixedMoment B node1530 node1530Labels = _
    exact sound1530 B hB hF
  have h1535 : mixedVector B (Sum.inr 1535) = Sparse.eval nodeValue1535 (mixedVector B) := by
    change mixedMoment B node1535 node1535Labels = _
    exact sound1535 B hB hF
  have h4058 : mixedVector B (Sum.inr 4058) = Sparse.eval nodeValue4058 (mixedVector B) := by
    change mixedMoment B node4058 node4058Labels = _
    exact sound4058 B hB hF
  simpa only [sourceForm2672, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1509, h1528, h1530, h1535, h4058, reducedSource2123] using sourceEq2672 B hB

theorem rowSound2123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2123 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2123, numericCheck2123, reducedZero2123 B hB hF, mul_zero]

theorem reducedZero2124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2124 (mixedVector B) = 0 := by
  have h1505 : mixedVector B (Sum.inr 1505) = Sparse.eval nodeValue1505 (mixedVector B) := by
    change mixedMoment B node1505 node1505Labels = _
    exact sound1505 B hB hF
  have h1509 : mixedVector B (Sum.inr 1509) = Sparse.eval nodeValue1509 (mixedVector B) := by
    change mixedMoment B node1509 node1509Labels = _
    exact sound1509 B hB hF
  have h1518 : mixedVector B (Sum.inr 1518) = Sparse.eval nodeValue1518 (mixedVector B) := by
    change mixedMoment B node1518 node1518Labels = _
    exact sound1518 B hB hF
  have h1535 : mixedVector B (Sum.inr 1535) = Sparse.eval nodeValue1535 (mixedVector B) := by
    change mixedMoment B node1535 node1535Labels = _
    exact sound1535 B hB hF
  have h4058 : mixedVector B (Sum.inr 4058) = Sparse.eval nodeValue4058 (mixedVector B) := by
    change mixedMoment B node4058 node4058Labels = _
    exact sound4058 B hB hF
  simpa only [sourceForm2673, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1505, h1509, h1518, h1535, h4058, reducedSource2124] using sourceEq2673 B hB

theorem rowSound2124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2124 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2124, numericCheck2124, reducedZero2124 B hB hF, mul_zero]

theorem reducedZero2125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2125 (mixedVector B) = 0 := by
  have h1511 : mixedVector B (Sum.inr 1511) = Sparse.eval nodeValue1511 (mixedVector B) := by
    change mixedMoment B node1511 node1511Labels = _
    exact sound1511 B hB hF
  have h1513 : mixedVector B (Sum.inr 1513) = Sparse.eval nodeValue1513 (mixedVector B) := by
    change mixedMoment B node1513 node1513Labels = _
    exact sound1513 B hB hF
  have h1519 : mixedVector B (Sum.inr 1519) = Sparse.eval nodeValue1519 (mixedVector B) := by
    change mixedMoment B node1519 node1519Labels = _
    exact sound1519 B hB hF
  have h1525 : mixedVector B (Sum.inr 1525) = Sparse.eval nodeValue1525 (mixedVector B) := by
    change mixedMoment B node1525 node1525Labels = _
    exact sound1525 B hB hF
  have h4059 : mixedVector B (Sum.inr 4059) = Sparse.eval nodeValue4059 (mixedVector B) := by
    change mixedMoment B node4059 node4059Labels = _
    exact sound4059 B hB hF
  simpa only [sourceForm2679, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1511, h1513, h1519, h1525, h4059, reducedSource2125] using sourceEq2679 B hB

theorem rowSound2125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2125 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2125, numericCheck2125, reducedZero2125 B hB hF, mul_zero]

theorem reducedZero2126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2126 (mixedVector B) = 0 := by
  have h1519 : mixedVector B (Sum.inr 1519) = Sparse.eval nodeValue1519 (mixedVector B) := by
    change mixedMoment B node1519 node1519Labels = _
    exact sound1519 B hB hF
  have h1522 : mixedVector B (Sum.inr 1522) = Sparse.eval nodeValue1522 (mixedVector B) := by
    change mixedMoment B node1522 node1522Labels = _
    exact sound1522 B hB hF
  have h1525 : mixedVector B (Sum.inr 1525) = Sparse.eval nodeValue1525 (mixedVector B) := by
    change mixedMoment B node1525 node1525Labels = _
    exact sound1525 B hB hF
  have h1526 : mixedVector B (Sum.inr 1526) = Sparse.eval nodeValue1526 (mixedVector B) := by
    change mixedMoment B node1526 node1526Labels = _
    exact sound1526 B hB hF
  have h1536 : mixedVector B (Sum.inr 1536) = Sparse.eval nodeValue1536 (mixedVector B) := by
    change mixedMoment B node1536 node1536Labels = _
    exact sound1536 B hB hF
  have h4059 : mixedVector B (Sum.inr 4059) = Sparse.eval nodeValue4059 (mixedVector B) := by
    change mixedMoment B node4059 node4059Labels = _
    exact sound4059 B hB hF
  simpa only [sourceForm2680, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1519, h1522, h1525, h1526, h1536, h4059, reducedSource2126] using sourceEq2680 B hB

theorem rowSound2126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2126 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2126, numericCheck2126, reducedZero2126 B hB hF, mul_zero]

theorem reducedZero2127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2127 (mixedVector B) = 0 := by
  have h1515 : mixedVector B (Sum.inr 1515) = Sparse.eval nodeValue1515 (mixedVector B) := by
    change mixedMoment B node1515 node1515Labels = _
    exact sound1515 B hB hF
  have h1519 : mixedVector B (Sum.inr 1519) = Sparse.eval nodeValue1519 (mixedVector B) := by
    change mixedMoment B node1519 node1519Labels = _
    exact sound1519 B hB hF
  have h1536 : mixedVector B (Sum.inr 1536) = Sparse.eval nodeValue1536 (mixedVector B) := by
    change mixedMoment B node1536 node1536Labels = _
    exact sound1536 B hB hF
  have h4059 : mixedVector B (Sum.inr 4059) = Sparse.eval nodeValue4059 (mixedVector B) := by
    change mixedMoment B node4059 node4059Labels = _
    exact sound4059 B hB hF
  simpa only [sourceForm2681, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1515, h1519, h1536, h4059, reducedSource2127] using sourceEq2681 B hB

theorem rowSound2127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2127 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2127, numericCheck2127, reducedZero2127 B hB hF, mul_zero]

theorem sourceRowsAt2112 : MixedData.sourceRows (2112 : Fin 2425) =
    MixedData.row2112 := by decide +kernel

theorem sourceRowsAt2113 : MixedData.sourceRows (2113 : Fin 2425) =
    MixedData.row2113 := by decide +kernel

theorem sourceRowsAt2114 : MixedData.sourceRows (2114 : Fin 2425) =
    MixedData.row2114 := by decide +kernel

theorem sourceRowsAt2115 : MixedData.sourceRows (2115 : Fin 2425) =
    MixedData.row2115 := by decide +kernel

theorem sourceRowsAt2116 : MixedData.sourceRows (2116 : Fin 2425) =
    MixedData.row2116 := by decide +kernel

theorem sourceRowsAt2117 : MixedData.sourceRows (2117 : Fin 2425) =
    MixedData.row2117 := by decide +kernel

theorem sourceRowsAt2118 : MixedData.sourceRows (2118 : Fin 2425) =
    MixedData.row2118 := by decide +kernel

theorem sourceRowsAt2119 : MixedData.sourceRows (2119 : Fin 2425) =
    MixedData.row2119 := by decide +kernel

theorem sourceRowsAt2120 : MixedData.sourceRows (2120 : Fin 2425) =
    MixedData.row2120 := by decide +kernel

theorem sourceRowsAt2121 : MixedData.sourceRows (2121 : Fin 2425) =
    MixedData.row2121 := by decide +kernel

theorem sourceRowsAt2122 : MixedData.sourceRows (2122 : Fin 2425) =
    MixedData.row2122 := by decide +kernel

theorem sourceRowsAt2123 : MixedData.sourceRows (2123 : Fin 2425) =
    MixedData.row2123 := by decide +kernel

theorem sourceRowsAt2124 : MixedData.sourceRows (2124 : Fin 2425) =
    MixedData.row2124 := by decide +kernel

theorem sourceRowsAt2125 : MixedData.sourceRows (2125 : Fin 2425) =
    MixedData.row2125 := by decide +kernel

theorem sourceRowsAt2126 : MixedData.sourceRows (2126 : Fin 2425) =
    MixedData.row2126 := by decide +kernel

theorem sourceRowsAt2127 : MixedData.sourceRows (2127 : Fin 2425) =
    MixedData.row2127 := by decide +kernel

theorem chunkSound132_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 132) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2112 ∨ k.val = 2113 ∨ k.val = 2114 ∨ k.val = 2115 ∨ k.val = 2116 ∨ k.val = 2117 ∨ k.val = 2118 ∨ k.val = 2119 ∨ k.val = 2120 ∨ k.val = 2121 ∨ k.val = 2122 ∨ k.val = 2123 ∨ k.val = 2124 ∨ k.val = 2125 ∨ k.val = 2126 ∨ k.val = 2127 := by omega
  rcases heq with h2112 | h2113 | h2114 | h2115 | h2116 | h2117 | h2118 | h2119 | h2120 | h2121 | h2122 | h2123 | h2124 | h2125 | h2126 | h2127
  · have he : k = (2112 : Fin 2425) := Fin.ext h2112
    subst k
    rw [sourceRowsAt2112]
    exact rowSound2112 B hB hF
  · have he : k = (2113 : Fin 2425) := Fin.ext h2113
    subst k
    rw [sourceRowsAt2113]
    exact rowSound2113 B hB hF
  · have he : k = (2114 : Fin 2425) := Fin.ext h2114
    subst k
    rw [sourceRowsAt2114]
    exact rowSound2114 B hB hF
  · have he : k = (2115 : Fin 2425) := Fin.ext h2115
    subst k
    rw [sourceRowsAt2115]
    exact rowSound2115 B hB hF
  · have he : k = (2116 : Fin 2425) := Fin.ext h2116
    subst k
    rw [sourceRowsAt2116]
    exact rowSound2116 B hB hF
  · have he : k = (2117 : Fin 2425) := Fin.ext h2117
    subst k
    rw [sourceRowsAt2117]
    exact rowSound2117 B hB hF
  · have he : k = (2118 : Fin 2425) := Fin.ext h2118
    subst k
    rw [sourceRowsAt2118]
    exact rowSound2118 B hB hF
  · have he : k = (2119 : Fin 2425) := Fin.ext h2119
    subst k
    rw [sourceRowsAt2119]
    exact rowSound2119 B hB hF
  · have he : k = (2120 : Fin 2425) := Fin.ext h2120
    subst k
    rw [sourceRowsAt2120]
    exact rowSound2120 B hB hF
  · have he : k = (2121 : Fin 2425) := Fin.ext h2121
    subst k
    rw [sourceRowsAt2121]
    exact rowSound2121 B hB hF
  · have he : k = (2122 : Fin 2425) := Fin.ext h2122
    subst k
    rw [sourceRowsAt2122]
    exact rowSound2122 B hB hF
  · have he : k = (2123 : Fin 2425) := Fin.ext h2123
    subst k
    rw [sourceRowsAt2123]
    exact rowSound2123 B hB hF
  · have he : k = (2124 : Fin 2425) := Fin.ext h2124
    subst k
    rw [sourceRowsAt2124]
    exact rowSound2124 B hB hF
  · have he : k = (2125 : Fin 2425) := Fin.ext h2125
    subst k
    rw [sourceRowsAt2125]
    exact rowSound2125 B hB hF
  · have he : k = (2126 : Fin 2425) := Fin.ext h2126
    subst k
    rw [sourceRowsAt2126]
    exact rowSound2126 B hB hF
  · have he : k = (2127 : Fin 2425) := Fin.ext h2127
    subst k
    rw [sourceRowsAt2127]
    exact rowSound2127 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132_e_oai
