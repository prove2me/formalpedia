-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound133_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:49:49.134923+00:00
-- url     : https://prove2.me/submissions/d31561a9-e5b2-47c1-b58c-9ef484ff549d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E121
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical292
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37476 raw37476Labels = mixedMoment B node1524 node1524Labels := by
  calc
    mixedMoment B raw37476 raw37476Labels = mixedMoment B raw37476step0 raw37476step0Labels := by
      have hz : ∀ j, raw37476 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37476step0 = (fun i j => raw37476 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37476step0 raw37476; decide +kernel
      have hl : raw37476step0Labels = raw37476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37476 raw37476Labels permutation265 hz
    mixedMoment B raw37476step0 raw37476step0Labels = mixedMoment B raw37476step1 raw37476step1Labels := by
      have ha : raw37476step1 = (fun i j => raw37476step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37476step1 raw37476step0; decide +kernel
      have hl : raw37476step1Labels = raw37476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37476step0 raw37476step0Labels permutation50 permutation2
    mixedMoment B raw37476step1 raw37476step1Labels = mixedMoment B raw37476step2 raw37476step2Labels := by
      have ha : raw37476step2 = -raw37476step1 := by apply Matrix.ext; change ∀ i j, raw37476step2 i j = -(raw37476step1 i j); unfold raw37476step2 raw37476step1; decide +kernel
      have hl : raw37476step2Labels = raw37476step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1524 node1524Labels := by rfl

theorem canonical37477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37477 raw37477Labels = mixedMoment B node1501 node1501Labels := by
  calc
    mixedMoment B raw37477 raw37477Labels = mixedMoment B raw37477step0 raw37477step0Labels := by
      have ha : raw37477step0 = (fun i j => raw37477 (permutation184 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37477step0 raw37477; decide +kernel
      have hl : raw37477step0Labels = raw37477Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37477 raw37477Labels permutation184 permutation4
    mixedMoment B raw37477step0 raw37477step0Labels = mixedMoment B raw37477step1 raw37477step1Labels := by
      have ha : raw37477step1 = -raw37477step0 := by apply Matrix.ext; change ∀ i j, raw37477step1 i j = -(raw37477step0 i j); unfold raw37477step1 raw37477step0; decide +kernel
      have hl : raw37477step1Labels = raw37477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1501 node1501Labels := by rfl

theorem canonical37478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37478 raw37478Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw37478 raw37478Labels = mixedMoment B raw37478step0 raw37478step0Labels := by
      have hz : ∀ j, raw37478 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37478step0 = (fun i j => raw37478 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37478step0 raw37478; decide +kernel
      have hl : raw37478step0Labels = raw37478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37478 raw37478Labels permutation265 hz
    mixedMoment B raw37478step0 raw37478step0Labels = mixedMoment B raw37478step1 raw37478step1Labels := by
      have ha : raw37478step1 = (fun i j => raw37478step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37478step1 raw37478step0; decide +kernel
      have hl : raw37478step1Labels = raw37478step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37478step0 raw37478step0Labels permutation40 permutation4
    mixedMoment B raw37478step1 raw37478step1Labels = mixedMoment B raw37478step2 raw37478step2Labels := by
      have ha : raw37478step2 = -raw37478step1 := by apply Matrix.ext; change ∀ i j, raw37478step2 i j = -(raw37478step1 i j); unfold raw37478step2 raw37478step1; decide +kernel
      have hl : raw37478step2Labels = raw37478step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1507 node1507Labels := by rfl

theorem canonical37479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37479 raw37479Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw37479 raw37479Labels = mixedMoment B raw37479step0 raw37479step0Labels := by
      have hz : ∀ j, raw37479 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37479step0 = (fun i j => raw37479 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37479step0 raw37479; decide +kernel
      have hl : raw37479step0Labels = raw37479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37479 raw37479Labels permutation265 hz
    mixedMoment B raw37479step0 raw37479step0Labels = mixedMoment B raw37479step1 raw37479step1Labels := by
      have ha : raw37479step1 = (fun i j => raw37479step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37479step1 raw37479step0; decide +kernel
      have hl : raw37479step1Labels = raw37479step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37479step0 raw37479step0Labels permutation34 permutation4
    mixedMoment B raw37479step1 raw37479step1Labels = mixedMoment B raw37479step2 raw37479step2Labels := by
      have ha : raw37479step2 = -raw37479step1 := by apply Matrix.ext; change ∀ i j, raw37479step2 i j = -(raw37479step1 i j); unfold raw37479step2 raw37479step1; decide +kernel
      have hl : raw37479step2Labels = raw37479step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1507 node1507Labels := by rfl

theorem canonical37480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37480 raw37480Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw37480 raw37480Labels = mixedMoment B raw37480step0 raw37480step0Labels := by
      have hz : ∀ j, raw37480 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37480step0 = (fun i j => raw37480 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37480step0 raw37480; decide +kernel
      have hl : raw37480step0Labels = raw37480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37480 raw37480Labels permutation265 hz
    mixedMoment B raw37480step0 raw37480step0Labels = mixedMoment B raw37480step1 raw37480step1Labels := by
      have ha : raw37480step1 = (fun i j => raw37480step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37480step1 raw37480step0; decide +kernel
      have hl : raw37480step1Labels = raw37480step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37480step0 raw37480step0Labels permutation32 permutation4
    mixedMoment B raw37480step1 raw37480step1Labels = mixedMoment B raw37480step2 raw37480step2Labels := by
      have ha : raw37480step2 = -raw37480step1 := by apply Matrix.ext; change ∀ i j, raw37480step2 i j = -(raw37480step1 i j); unfold raw37480step2 raw37480step1; decide +kernel
      have hl : raw37480step2Labels = raw37480step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1507 node1507Labels := by rfl

theorem canonical37481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37481 raw37481Labels = mixedMoment B node1503 node1503Labels := by
  calc
    mixedMoment B raw37481 raw37481Labels = mixedMoment B raw37481step0 raw37481step0Labels := by
      have hz : ∀ j, raw37481 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37481step0 = (fun i j => raw37481 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37481step0 raw37481; decide +kernel
      have hl : raw37481step0Labels = raw37481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37481 raw37481Labels permutation265 hz
    mixedMoment B raw37481step0 raw37481step0Labels = mixedMoment B raw37481step1 raw37481step1Labels := by
      have ha : raw37481step1 = (fun i j => raw37481step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37481step1 raw37481step0; decide +kernel
      have hl : raw37481step1Labels = raw37481step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37481step0 raw37481step0Labels permutation32 permutation4
    mixedMoment B raw37481step1 raw37481step1Labels = mixedMoment B raw37481step2 raw37481step2Labels := by
      have ha : raw37481step2 = -raw37481step1 := by apply Matrix.ext; change ∀ i j, raw37481step2 i j = -(raw37481step1 i j); unfold raw37481step2 raw37481step1; decide +kernel
      have hl : raw37481step2Labels = raw37481step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1503 node1503Labels := by rfl

theorem canonical37482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37482 raw37482Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw37482 raw37482Labels = mixedMoment B raw37482step0 raw37482step0Labels := by
      have hz : ∀ j, raw37482 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37482step0 = (fun i j => raw37482 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37482step0 raw37482; decide +kernel
      have hl : raw37482step0Labels = raw37482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37482 raw37482Labels permutation265 hz
    mixedMoment B raw37482step0 raw37482step0Labels = mixedMoment B raw37482step1 raw37482step1Labels := by
      have ha : raw37482step1 = -raw37482step0 := by apply Matrix.ext; change ∀ i j, raw37482step1 i j = -(raw37482step0 i j); unfold raw37482step1 raw37482step0; decide +kernel
      have hl : raw37482step1Labels = raw37482step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4057 node4057Labels := by rfl

theorem canonical37483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37483 raw37483Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw37483 raw37483Labels = mixedMoment B raw37483step0 raw37483step0Labels := by
      have hz : ∀ j, raw37483 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37483step0 = (fun i j => raw37483 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37483step0 raw37483; decide +kernel
      have hl : raw37483step0Labels = raw37483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37483 raw37483Labels permutation265 hz
    mixedMoment B raw37483step0 raw37483step0Labels = mixedMoment B raw37483step1 raw37483step1Labels := by
      have ha : raw37483step1 = (fun i j => raw37483step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37483step1 raw37483step0; decide +kernel
      have hl : raw37483step1Labels = raw37483step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37483step0 raw37483step0Labels permutation44 permutation2
    mixedMoment B raw37483step1 raw37483step1Labels = mixedMoment B raw37483step2 raw37483step2Labels := by
      have ha : raw37483step2 = -raw37483step1 := by apply Matrix.ext; change ∀ i j, raw37483step2 i j = -(raw37483step1 i j); unfold raw37483step2 raw37483step1; decide +kernel
      have hl : raw37483step2Labels = raw37483step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1517 node1517Labels := by rfl

theorem canonical37484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37484 raw37484Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw37484 raw37484Labels = mixedMoment B raw37484step0 raw37484step0Labels := by
      have ha : raw37484step0 = (fun i j => raw37484 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37484step0 raw37484; decide +kernel
      have hl : raw37484step0Labels = raw37484Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37484 raw37484Labels permutation182 permutation4
    mixedMoment B raw37484step0 raw37484step0Labels = mixedMoment B raw37484step1 raw37484step1Labels := by
      have ha : raw37484step1 = -raw37484step0 := by apply Matrix.ext; change ∀ i j, raw37484step1 i j = -(raw37484step0 i j); unfold raw37484step1 raw37484step0; decide +kernel
      have hl : raw37484step1Labels = raw37484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1504 node1504Labels := by rfl

theorem canonical37485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37485 raw37485Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw37485 raw37485Labels = mixedMoment B raw37485step0 raw37485step0Labels := by
      have hz : ∀ j, raw37485 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37485step0 = (fun i j => raw37485 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37485step0 raw37485; decide +kernel
      have hl : raw37485step0Labels = raw37485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37485 raw37485Labels permutation265 hz
    mixedMoment B raw37485step0 raw37485step0Labels = mixedMoment B raw37485step1 raw37485step1Labels := by
      have ha : raw37485step1 = (fun i j => raw37485step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37485step1 raw37485step0; decide +kernel
      have hl : raw37485step1Labels = raw37485step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37485step0 raw37485step0Labels permutation38 permutation4
    mixedMoment B raw37485step1 raw37485step1Labels = mixedMoment B raw37485step2 raw37485step2Labels := by
      have ha : raw37485step2 = -raw37485step1 := by apply Matrix.ext; change ∀ i j, raw37485step2 i j = -(raw37485step1 i j); unfold raw37485step2 raw37485step1; decide +kernel
      have hl : raw37485step2Labels = raw37485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1517 node1517Labels := by rfl

theorem canonical37486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37486 raw37486Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw37486 raw37486Labels = mixedMoment B raw37486step0 raw37486step0Labels := by
      have hz : ∀ j, raw37486 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37486step0 = (fun i j => raw37486 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37486step0 raw37486; decide +kernel
      have hl : raw37486step0Labels = raw37486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37486 raw37486Labels permutation265 hz
    mixedMoment B raw37486step0 raw37486step0Labels = mixedMoment B raw37486step1 raw37486step1Labels := by
      have ha : raw37486step1 = (fun i j => raw37486step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37486step1 raw37486step0; decide +kernel
      have hl : raw37486step1Labels = raw37486step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37486step0 raw37486step0Labels permutation32 permutation4
    mixedMoment B raw37486step1 raw37486step1Labels = mixedMoment B raw37486step2 raw37486step2Labels := by
      have ha : raw37486step2 = -raw37486step1 := by apply Matrix.ext; change ∀ i j, raw37486step2 i j = -(raw37486step1 i j); unfold raw37486step2 raw37486step1; decide +kernel
      have hl : raw37486step2Labels = raw37486step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1517 node1517Labels := by rfl

theorem canonical37487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37487 raw37487Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw37487 raw37487Labels = mixedMoment B raw37487step0 raw37487step0Labels := by
      have hz : ∀ j, raw37487 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37487step0 = (fun i j => raw37487 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37487step0 raw37487; decide +kernel
      have hl : raw37487step0Labels = raw37487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37487 raw37487Labels permutation265 hz
    mixedMoment B raw37487step0 raw37487step0Labels = mixedMoment B raw37487step1 raw37487step1Labels := by
      have ha : raw37487step1 = (fun i j => raw37487step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37487step1 raw37487step0; decide +kernel
      have hl : raw37487step1Labels = raw37487step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37487step0 raw37487step0Labels permutation33 permutation4
    mixedMoment B raw37487step1 raw37487step1Labels = mixedMoment B raw37487step2 raw37487step2Labels := by
      have ha : raw37487step2 = -raw37487step1 := by apply Matrix.ext; change ∀ i j, raw37487step2 i j = -(raw37487step1 i j); unfold raw37487step2 raw37487step1; decide +kernel
      have hl : raw37487step2Labels = raw37487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1508 node1508Labels := by rfl

theorem canonical37488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37488 raw37488Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw37488 raw37488Labels = mixedMoment B raw37488step0 raw37488step0Labels := by
      have hz : ∀ j, raw37488 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37488step0 = (fun i j => raw37488 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37488step0 raw37488; decide +kernel
      have hl : raw37488step0Labels = raw37488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37488 raw37488Labels permutation265 hz
    mixedMoment B raw37488step0 raw37488step0Labels = mixedMoment B raw37488step1 raw37488step1Labels := by
      have ha : raw37488step1 = (fun i j => raw37488step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37488step1 raw37488step0; decide +kernel
      have hl : raw37488step1Labels = raw37488step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37488step0 raw37488step0Labels permutation40 permutation2
    mixedMoment B raw37488step1 raw37488step1Labels = mixedMoment B raw37488step2 raw37488step2Labels := by
      have ha : raw37488step2 = -raw37488step1 := by apply Matrix.ext; change ∀ i j, raw37488step2 i j = -(raw37488step1 i j); unfold raw37488step2 raw37488step1; decide +kernel
      have hl : raw37488step2Labels = raw37488step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1507 node1507Labels := by rfl

theorem canonical37489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37489 raw37489Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw37489 raw37489Labels = mixedMoment B raw37489step0 raw37489step0Labels := by
      have ha : raw37489step0 = (fun i j => raw37489 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37489step0 raw37489; decide +kernel
      have hl : raw37489step0Labels = raw37489Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37489 raw37489Labels permutation194 permutation4
    mixedMoment B raw37489step0 raw37489step0Labels = mixedMoment B raw37489step1 raw37489step1Labels := by
      have ha : raw37489step1 = -raw37489step0 := by apply Matrix.ext; change ∀ i j, raw37489step1 i j = -(raw37489step0 i j); unfold raw37489step1 raw37489step0; decide +kernel
      have hl : raw37489step1Labels = raw37489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1510 node1510Labels := by rfl

theorem canonical37490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37490 raw37490Labels = mixedMoment B node1524 node1524Labels := by
  calc
    mixedMoment B raw37490 raw37490Labels = mixedMoment B raw37490step0 raw37490step0Labels := by
      have hz : ∀ j, raw37490 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37490step0 = (fun i j => raw37490 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37490step0 raw37490; decide +kernel
      have hl : raw37490step0Labels = raw37490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37490 raw37490Labels permutation265 hz
    mixedMoment B raw37490step0 raw37490step0Labels = mixedMoment B raw37490step1 raw37490step1Labels := by
      have ha : raw37490step1 = (fun i j => raw37490step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37490step1 raw37490step0; decide +kernel
      have hl : raw37490step1Labels = raw37490step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37490step0 raw37490step0Labels permutation50 permutation4
    mixedMoment B raw37490step1 raw37490step1Labels = mixedMoment B raw37490step2 raw37490step2Labels := by
      have ha : raw37490step2 = -raw37490step1 := by apply Matrix.ext; change ∀ i j, raw37490step2 i j = -(raw37490step1 i j); unfold raw37490step2 raw37490step1; decide +kernel
      have hl : raw37490step2Labels = raw37490step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1524 node1524Labels := by rfl

theorem canonical37491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37491 raw37491Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw37491 raw37491Labels = mixedMoment B raw37491step0 raw37491step0Labels := by
      have hz : ∀ j, raw37491 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37491step0 = (fun i j => raw37491 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37491step0 raw37491; decide +kernel
      have hl : raw37491step0Labels = raw37491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37491 raw37491Labels permutation265 hz
    mixedMoment B raw37491step0 raw37491step0Labels = mixedMoment B raw37491step1 raw37491step1Labels := by
      have ha : raw37491step1 = (fun i j => raw37491step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37491step1 raw37491step0; decide +kernel
      have hl : raw37491step1Labels = raw37491step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37491step0 raw37491step0Labels permutation37 permutation4
    mixedMoment B raw37491step1 raw37491step1Labels = mixedMoment B raw37491step2 raw37491step2Labels := by
      have ha : raw37491step2 = -raw37491step1 := by apply Matrix.ext; change ∀ i j, raw37491step2 i j = -(raw37491step1 i j); unfold raw37491step2 raw37491step1; decide +kernel
      have hl : raw37491step2Labels = raw37491step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1512 node1512Labels := by rfl

theorem canonical37492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37492 raw37492Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw37492 raw37492Labels = mixedMoment B raw37492step0 raw37492step0Labels := by
      have hz : ∀ j, raw37492 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37492step0 = (fun i j => raw37492 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37492step0 raw37492; decide +kernel
      have hl : raw37492step0Labels = raw37492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37492 raw37492Labels permutation265 hz
    mixedMoment B raw37492step0 raw37492step0Labels = mixedMoment B raw37492step1 raw37492step1Labels := by
      have ha : raw37492step1 = (fun i j => raw37492step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37492step1 raw37492step0; decide +kernel
      have hl : raw37492step1Labels = raw37492step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37492step0 raw37492step0Labels permutation36 permutation4
    mixedMoment B raw37492step1 raw37492step1Labels = mixedMoment B raw37492step2 raw37492step2Labels := by
      have ha : raw37492step2 = -raw37492step1 := by apply Matrix.ext; change ∀ i j, raw37492step2 i j = -(raw37492step1 i j); unfold raw37492step2 raw37492step1; decide +kernel
      have hl : raw37492step2Labels = raw37492step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1512 node1512Labels := by rfl

theorem canonical37497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37497 raw37497Labels = mixedMoment B node687 node687Labels := by
  calc
    mixedMoment B raw37497 raw37497Labels = mixedMoment B raw37497step0 raw37497step0Labels := by
      have hz : ∀ j, raw37497 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37497step0 = (fun i j => raw37497 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37497step0 raw37497; decide +kernel
      have hl : raw37497step0Labels = raw37497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37497 raw37497Labels permutation265 hz
    mixedMoment B raw37497step0 raw37497step0Labels = mixedMoment B raw37497step1 raw37497step1Labels := by
      have ha : raw37497step1 = (fun i j => raw37497step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37497step1 raw37497step0; decide +kernel
      have hl : raw37497step1Labels = raw37497step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37497step0 raw37497step0Labels permutation32 permutation4
    mixedMoment B raw37497step1 raw37497step1Labels = mixedMoment B raw37497step2 raw37497step2Labels := by
      have ha : raw37497step2 = -raw37497step1 := by apply Matrix.ext; change ∀ i j, raw37497step2 i j = -(raw37497step1 i j); unfold raw37497step2 raw37497step1; decide +kernel
      have hl : raw37497step2Labels = raw37497step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node687 node687Labels := by rfl

theorem canonical37498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37498 raw37498Labels = mixedMoment B node1491 node1491Labels := by
  calc
    mixedMoment B raw37498 raw37498Labels = mixedMoment B raw37498step0 raw37498step0Labels := by
      have ha : raw37498step0 = (fun i j => raw37498 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37498step0 raw37498; decide +kernel
      have hl : raw37498step0Labels = raw37498Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37498 raw37498Labels permutation152 permutation4
    mixedMoment B raw37498step0 raw37498step0Labels = mixedMoment B raw37498step1 raw37498step1Labels := by
      have ha : raw37498step1 = -raw37498step0 := by apply Matrix.ext; change ∀ i j, raw37498step1 i j = -(raw37498step0 i j); unfold raw37498step1 raw37498step0; decide +kernel
      have hl : raw37498step1Labels = raw37498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1491 node1491Labels := by rfl

theorem canonical37499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37499 raw37499Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw37499 raw37499Labels = mixedMoment B raw37499step0 raw37499step0Labels := by
      have hz : ∀ j, raw37499 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37499step0 = (fun i j => raw37499 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37499step0 raw37499; decide +kernel
      have hl : raw37499step0Labels = raw37499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37499 raw37499Labels permutation265 hz
    mixedMoment B raw37499step0 raw37499step0Labels = mixedMoment B raw37499step1 raw37499step1Labels := by
      have ha : raw37499step1 = (fun i j => raw37499step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37499step1 raw37499step0; decide +kernel
      have hl : raw37499step1Labels = raw37499step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37499step0 raw37499step0Labels permutation44 permutation4
    mixedMoment B raw37499step1 raw37499step1Labels = mixedMoment B raw37499step2 raw37499step2Labels := by
      have ha : raw37499step2 = -raw37499step1 := by apply Matrix.ext; change ∀ i j, raw37499step2 i j = -(raw37499step1 i j); unfold raw37499step2 raw37499step1; decide +kernel
      have hl : raw37499step2Labels = raw37499step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1517 node1517Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical293
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37513 raw37513Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37513 raw37513Labels = mixedMoment B raw37513step0 raw37513step0Labels := by
      have ha : raw37513step0 = (fun i j => raw37513 (permutation240 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37513step0 raw37513; decide +kernel
      have hl : raw37513step0Labels = raw37513Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37513 raw37513Labels permutation240 permutation2
    mixedMoment B raw37513step0 raw37513step0Labels = mixedMoment B raw37513step1 raw37513step1Labels := by
      have ha : raw37513step1 = -raw37513step0 := by apply Matrix.ext; change ∀ i j, raw37513step1 i j = -(raw37513step0 i j); unfold raw37513step1 raw37513step0; decide +kernel
      have hl : raw37513step1Labels = raw37513step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

theorem canonical37514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37514 raw37514Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37514 raw37514Labels = mixedMoment B raw37514step0 raw37514step0Labels := by
      have ha : raw37514step0 = (fun i j => raw37514 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37514step0 raw37514; decide +kernel
      have hl : raw37514step0Labels = raw37514Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37514 raw37514Labels permutation182 permutation4
    mixedMoment B raw37514step0 raw37514step0Labels = mixedMoment B raw37514step1 raw37514step1Labels := by
      have ha : raw37514step1 = -raw37514step0 := by apply Matrix.ext; change ∀ i j, raw37514step1 i j = -(raw37514step0 i j); unfold raw37514step1 raw37514step0; decide +kernel
      have hl : raw37514step1Labels = raw37514step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

theorem canonical37515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37515 raw37515Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37515 raw37515Labels = mixedMoment B raw37515step0 raw37515step0Labels := by
      have ha : raw37515step0 = (fun i j => raw37515 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37515step0 raw37515; decide +kernel
      have hl : raw37515step0Labels = raw37515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37515 raw37515Labels permutation158 permutation4
    mixedMoment B raw37515step0 raw37515step0Labels = mixedMoment B raw37515step1 raw37515step1Labels := by
      have ha : raw37515step1 = -raw37515step0 := by apply Matrix.ext; change ∀ i j, raw37515step1 i j = -(raw37515step0 i j); unfold raw37515step1 raw37515step0; decide +kernel
      have hl : raw37515step1Labels = raw37515step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

theorem canonical37516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37516 raw37516Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37516 raw37516Labels = mixedMoment B raw37516step0 raw37516step0Labels := by
      have ha : raw37516step0 = (fun i j => raw37516 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37516step0 raw37516; decide +kernel
      have hl : raw37516step0Labels = raw37516Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37516 raw37516Labels permutation152 permutation4
    mixedMoment B raw37516step0 raw37516step0Labels = mixedMoment B raw37516step1 raw37516step1Labels := by
      have ha : raw37516step1 = -raw37516step0 := by apply Matrix.ext; change ∀ i j, raw37516step1 i j = -(raw37516step0 i j); unfold raw37516step1 raw37516step0; decide +kernel
      have hl : raw37516step1Labels = raw37516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

theorem canonical37517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37517 raw37517Labels = mixedMoment B node1502 node1502Labels := by
  calc
    mixedMoment B raw37517 raw37517Labels = mixedMoment B raw37517step0 raw37517step0Labels := by
      have ha : raw37517step0 = (fun i j => raw37517 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37517step0 raw37517; decide +kernel
      have hl : raw37517step0Labels = raw37517Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37517 raw37517Labels permutation153 permutation4
    mixedMoment B raw37517step0 raw37517step0Labels = mixedMoment B raw37517step1 raw37517step1Labels := by
      have ha : raw37517step1 = -raw37517step0 := by apply Matrix.ext; change ∀ i j, raw37517step1 i j = -(raw37517step0 i j); unfold raw37517step1 raw37517step0; decide +kernel
      have hl : raw37517step1Labels = raw37517step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1502 node1502Labels := by rfl

theorem canonical37518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37518 raw37518Labels = mixedMoment B node1502 node1502Labels := by
  calc
    mixedMoment B raw37518 raw37518Labels = mixedMoment B raw37518step0 raw37518step0Labels := by
      have ha : raw37518step0 = (fun i j => raw37518 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37518step0 raw37518; decide +kernel
      have hl : raw37518step0Labels = raw37518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37518 raw37518Labels permutation152 permutation4
    mixedMoment B raw37518step0 raw37518step0Labels = mixedMoment B raw37518step1 raw37518step1Labels := by
      have ha : raw37518step1 = -raw37518step0 := by apply Matrix.ext; change ∀ i j, raw37518step1 i j = -(raw37518step0 i j); unfold raw37518step1 raw37518step0; decide +kernel
      have hl : raw37518step1Labels = raw37518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1502 node1502Labels := by rfl

theorem canonical37519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37519 raw37519Labels = mixedMoment B node4056 node4056Labels := by
  calc
    mixedMoment B raw37519 raw37519Labels = mixedMoment B raw37519step0 raw37519step0Labels := by
      have ha : raw37519step0 = -raw37519 := by apply Matrix.ext; change ∀ i j, raw37519step0 i j = -(raw37519 i j); unfold raw37519step0 raw37519; decide +kernel
      have hl : raw37519step0Labels = raw37519Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4056 node4056Labels := by rfl

theorem canonical37520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37520 raw37520Labels = mixedMoment B node666 node666Labels := by
  calc
    mixedMoment B raw37520 raw37520Labels = mixedMoment B raw37520step0 raw37520step0Labels := by
      have ha : raw37520step0 = (fun i j => raw37520 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37520step0 raw37520; decide +kernel
      have hl : raw37520step0Labels = raw37520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37520 raw37520Labels permutation246 permutation4
    mixedMoment B raw37520step0 raw37520step0Labels = mixedMoment B raw37520step1 raw37520step1Labels := by
      have ha : raw37520step1 = -raw37520step0 := by apply Matrix.ext; change ∀ i j, raw37520step1 i j = -(raw37520step0 i j); unfold raw37520step1 raw37520step0; decide +kernel
      have hl : raw37520step1Labels = raw37520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node666 node666Labels := by rfl

theorem canonical37521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37521 raw37521Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37521 raw37521Labels = mixedMoment B raw37521step0 raw37521step0Labels := by
      have ha : raw37521step0 = (fun i j => raw37521 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37521step0 raw37521; decide +kernel
      have hl : raw37521step0Labels = raw37521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37521 raw37521Labels permutation170 permutation4
    mixedMoment B raw37521step0 raw37521step0Labels = mixedMoment B raw37521step1 raw37521step1Labels := by
      have ha : raw37521step1 = -raw37521step0 := by apply Matrix.ext; change ∀ i j, raw37521step1 i j = -(raw37521step0 i j); unfold raw37521step1 raw37521step0; decide +kernel
      have hl : raw37521step1Labels = raw37521step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

theorem canonical37522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37522 raw37522Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37522 raw37522Labels = mixedMoment B raw37522step0 raw37522step0Labels := by
      have ha : raw37522step0 = (fun i j => raw37522 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37522step0 raw37522; decide +kernel
      have hl : raw37522step0Labels = raw37522Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37522 raw37522Labels permutation194 permutation4
    mixedMoment B raw37522step0 raw37522step0Labels = mixedMoment B raw37522step1 raw37522step1Labels := by
      have ha : raw37522step1 = -raw37522step0 := by apply Matrix.ext; change ∀ i j, raw37522step1 i j = -(raw37522step0 i j); unfold raw37522step1 raw37522step0; decide +kernel
      have hl : raw37522step1Labels = raw37522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

theorem canonical37523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37523 raw37523Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37523 raw37523Labels = mixedMoment B raw37523step0 raw37523step0Labels := by
      have ha : raw37523step0 = (fun i j => raw37523 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37523step0 raw37523; decide +kernel
      have hl : raw37523step0Labels = raw37523Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37523 raw37523Labels permutation218 permutation4
    mixedMoment B raw37523step0 raw37523step0Labels = mixedMoment B raw37523step1 raw37523step1Labels := by
      have ha : raw37523step1 = -raw37523step0 := by apply Matrix.ext; change ∀ i j, raw37523step1 i j = -(raw37523step0 i j); unfold raw37523step1 raw37523step0; decide +kernel
      have hl : raw37523step1Labels = raw37523step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

theorem canonical37524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37524 raw37524Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37524 raw37524Labels = mixedMoment B raw37524step0 raw37524step0Labels := by
      have ha : raw37524step0 = (fun i j => raw37524 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37524step0 raw37524; decide +kernel
      have hl : raw37524step0Labels = raw37524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37524 raw37524Labels permutation240 permutation4
    mixedMoment B raw37524step0 raw37524step0Labels = mixedMoment B raw37524step1 raw37524step1Labels := by
      have ha : raw37524step1 = -raw37524step0 := by apply Matrix.ext; change ∀ i j, raw37524step1 i j = -(raw37524step0 i j); unfold raw37524step1 raw37524step0; decide +kernel
      have hl : raw37524step1Labels = raw37524step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

theorem canonical37525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37525 raw37525Labels = mixedMoment B node1497 node1497Labels := by
  calc
    mixedMoment B raw37525 raw37525Labels = mixedMoment B raw37525step0 raw37525step0Labels := by
      have ha : raw37525step0 = (fun i j => raw37525 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37525step0 raw37525; decide +kernel
      have hl : raw37525step0Labels = raw37525Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37525 raw37525Labels permutation246 permutation4
    mixedMoment B raw37525step0 raw37525step0Labels = mixedMoment B raw37525step1 raw37525step1Labels := by
      have ha : raw37525step1 = -raw37525step0 := by apply Matrix.ext; change ∀ i j, raw37525step1 i j = -(raw37525step0 i j); unfold raw37525step1 raw37525step0; decide +kernel
      have hl : raw37525step1Labels = raw37525step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1497 node1497Labels := by rfl

theorem canonical37530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37530 raw37530Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw37530 raw37530Labels = mixedMoment B raw37530step0 raw37530step0Labels := by
      have hz : ∀ j, raw37530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37530step0 = (fun i j => raw37530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37530step0 raw37530; decide +kernel
      have hl : raw37530step0Labels = raw37530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37530 raw37530Labels permutation434 hz
    mixedMoment B raw37530step0 raw37530step0Labels = mixedMoment B raw37530step1 raw37530step1Labels := by
      have hz : ∀ j, raw37530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37530step1 = (fun i j => raw37530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37530step1 raw37530step0; decide +kernel
      have hl : raw37530step1Labels = raw37530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37530step0 raw37530step0Labels permutation80 hz
    mixedMoment B raw37530step1 raw37530step1Labels = mixedMoment B raw37530step2 raw37530step2Labels := by
      have ha : raw37530step2 = (fun i j => raw37530step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37530step2 raw37530step1; decide +kernel
      have hl : raw37530step2Labels = raw37530step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37530step1 raw37530step1Labels permutation31 permutation2
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical37531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37531 raw37531Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw37531 raw37531Labels = mixedMoment B raw37531step0 raw37531step0Labels := by
      have hz : ∀ j, raw37531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37531step0 = (fun i j => raw37531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37531step0 raw37531; decide +kernel
      have hl : raw37531step0Labels = raw37531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37531 raw37531Labels permutation434 hz
    mixedMoment B raw37531step0 raw37531step0Labels = mixedMoment B raw37531step1 raw37531step1Labels := by
      have hz : ∀ j, raw37531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37531step1 = (fun i j => raw37531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37531step1 raw37531step0; decide +kernel
      have hl : raw37531step1Labels = raw37531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37531step0 raw37531step0Labels permutation80 hz
    mixedMoment B raw37531step1 raw37531step1Labels = mixedMoment B raw37531step2 raw37531step2Labels := by
      have ha : raw37531step2 = (fun i j => raw37531step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37531step2 raw37531step1; decide +kernel
      have hl : raw37531step2Labels = raw37531step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37531step1 raw37531step1Labels permutation30 permutation2
    _ = mixedMoment B node1695 node1695Labels := by rfl

theorem canonical37532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37532 raw37532Labels = mixedMoment B node1688 node1688Labels := by
  calc
    mixedMoment B raw37532 raw37532Labels = mixedMoment B raw37532step0 raw37532step0Labels := by
      have hz : ∀ j, raw37532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37532step0 = (fun i j => raw37532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37532step0 raw37532; decide +kernel
      have hl : raw37532step0Labels = raw37532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37532 raw37532Labels permutation434 hz
    mixedMoment B raw37532step0 raw37532step0Labels = mixedMoment B raw37532step1 raw37532step1Labels := by
      have ha : raw37532step1 = (fun i j => raw37532step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37532step1 raw37532step0; decide +kernel
      have hl : raw37532step1Labels = raw37532step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37532step0 raw37532step0Labels permutation151 permutation2
    _ = mixedMoment B node1688 node1688Labels := by rfl

theorem canonical37533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37533 raw37533Labels = mixedMoment B node1688 node1688Labels := by
  calc
    mixedMoment B raw37533 raw37533Labels = mixedMoment B raw37533step0 raw37533step0Labels := by
      have hz : ∀ j, raw37533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37533step0 = (fun i j => raw37533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37533step0 raw37533; decide +kernel
      have hl : raw37533step0Labels = raw37533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37533 raw37533Labels permutation346 hz
    mixedMoment B raw37533step0 raw37533step0Labels = mixedMoment B raw37533step1 raw37533step1Labels := by
      have ha : raw37533step1 = (fun i j => raw37533step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37533step1 raw37533step0; decide +kernel
      have hl : raw37533step1Labels = raw37533step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37533step0 raw37533step0Labels permutation151 permutation2
    _ = mixedMoment B node1688 node1688Labels := by rfl

theorem canonical37534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37534 raw37534Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw37534 raw37534Labels = mixedMoment B raw37534step0 raw37534step0Labels := by
      have hz : ∀ j, raw37534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37534step0 = (fun i j => raw37534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37534step0 raw37534; decide +kernel
      have hl : raw37534step0Labels = raw37534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37534 raw37534Labels permutation434 hz
    mixedMoment B raw37534step0 raw37534step0Labels = mixedMoment B raw37534step1 raw37534step1Labels := by
      have hz : ∀ j, raw37534step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37534step1 = (fun i j => raw37534step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37534step1 raw37534step0; decide +kernel
      have hl : raw37534step1Labels = raw37534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37534step0 raw37534step0Labels permutation80 hz
    mixedMoment B raw37534step1 raw37534step1Labels = mixedMoment B raw37534step2 raw37534step2Labels := by
      have ha : raw37534step2 = (fun i j => raw37534step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37534step2 raw37534step1; decide +kernel
      have hl : raw37534step2Labels = raw37534step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37534step1 raw37534step1Labels permutation9 permutation4
    mixedMoment B raw37534step2 raw37534step2Labels = mixedMoment B raw37534step3 raw37534step3Labels := by
      have ha : raw37534step3 = -raw37534step2 := by apply Matrix.ext; change ∀ i j, raw37534step3 i j = -(raw37534step2 i j); unfold raw37534step3 raw37534step2; decide +kernel
      have hl : raw37534step3Labels = raw37534step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1695 node1695Labels := by rfl

theorem canonical37535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37535 raw37535Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw37535 raw37535Labels = mixedMoment B raw37535step0 raw37535step0Labels := by
      have hz : ∀ j, raw37535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37535step0 = (fun i j => raw37535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37535step0 raw37535; decide +kernel
      have hl : raw37535step0Labels = raw37535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37535 raw37535Labels permutation434 hz
    mixedMoment B raw37535step0 raw37535step0Labels = mixedMoment B raw37535step1 raw37535step1Labels := by
      have hz : ∀ j, raw37535step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37535step1 = (fun i j => raw37535step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37535step1 raw37535step0; decide +kernel
      have hl : raw37535step1Labels = raw37535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37535step0 raw37535step0Labels permutation80 hz
    mixedMoment B raw37535step1 raw37535step1Labels = mixedMoment B raw37535step2 raw37535step2Labels := by
      have ha : raw37535step2 = (fun i j => raw37535step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37535step2 raw37535step1; decide +kernel
      have hl : raw37535step2Labels = raw37535step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37535step1 raw37535step1Labels permutation8 permutation4
    mixedMoment B raw37535step2 raw37535step2Labels = mixedMoment B raw37535step3 raw37535step3Labels := by
      have ha : raw37535step3 = -raw37535step2 := by apply Matrix.ext; change ∀ i j, raw37535step3 i j = -(raw37535step2 i j); unfold raw37535step3 raw37535step2; decide +kernel
      have hl : raw37535step3Labels = raw37535step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical37536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37536 raw37536Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw37536 raw37536Labels = mixedMoment B raw37536step0 raw37536step0Labels := by
      have hz : ∀ j, raw37536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37536step0 = (fun i j => raw37536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37536step0 raw37536; decide +kernel
      have hl : raw37536step0Labels = raw37536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37536 raw37536Labels permutation434 hz
    mixedMoment B raw37536step0 raw37536step0Labels = mixedMoment B raw37536step1 raw37536step1Labels := by
      have hz : ∀ j, raw37536step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37536step1 = (fun i j => raw37536step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37536step1 raw37536step0; decide +kernel
      have hl : raw37536step1Labels = raw37536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37536step0 raw37536step0Labels permutation80 hz
    mixedMoment B raw37536step1 raw37536step1Labels = mixedMoment B raw37536step2 raw37536step2Labels := by
      have ha : raw37536step2 = (fun i j => raw37536step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37536step2 raw37536step1; decide +kernel
      have hl : raw37536step2Labels = raw37536step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37536step1 raw37536step1Labels permutation31 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical37537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37537 raw37537Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw37537 raw37537Labels = mixedMoment B raw37537step0 raw37537step0Labels := by
      have hz : ∀ j, raw37537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37537step0 = (fun i j => raw37537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37537step0 raw37537; decide +kernel
      have hl : raw37537step0Labels = raw37537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37537 raw37537Labels permutation434 hz
    mixedMoment B raw37537step0 raw37537step0Labels = mixedMoment B raw37537step1 raw37537step1Labels := by
      have hz : ∀ j, raw37537step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37537step1 = (fun i j => raw37537step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37537step1 raw37537step0; decide +kernel
      have hl : raw37537step1Labels = raw37537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37537step0 raw37537step0Labels permutation80 hz
    mixedMoment B raw37537step1 raw37537step1Labels = mixedMoment B raw37537step2 raw37537step2Labels := by
      have ha : raw37537step2 = -raw37537step1 := by apply Matrix.ext; change ∀ i j, raw37537step2 i j = -(raw37537step1 i j); unfold raw37537step2 raw37537step1; decide +kernel
      have hl : raw37537step2Labels = raw37537step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical37538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37538 raw37538Labels = mixedMoment B node3275 node3275Labels := by
  calc
    mixedMoment B raw37538 raw37538Labels = mixedMoment B raw37538step0 raw37538step0Labels := by
      have hz : ∀ j, raw37538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37538step0 = (fun i j => raw37538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37538step0 raw37538; decide +kernel
      have hl : raw37538step0Labels = raw37538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37538 raw37538Labels permutation434 hz
    mixedMoment B raw37538step0 raw37538step0Labels = mixedMoment B raw37538step1 raw37538step1Labels := by
      have hz : ∀ j, raw37538step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37538step1 = (fun i j => raw37538step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37538step1 raw37538step0; decide +kernel
      have hl : raw37538step1Labels = raw37538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37538step0 raw37538step0Labels permutation80 hz
    mixedMoment B raw37538step1 raw37538step1Labels = mixedMoment B raw37538step2 raw37538step2Labels := by
      have ha : raw37538step2 = (fun i j => raw37538step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37538step2 raw37538step1; decide +kernel
      have hl : raw37538step2Labels = raw37538step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37538step1 raw37538step1Labels permutation31 permutation2
    _ = mixedMoment B node3275 node3275Labels := by rfl

theorem canonical37539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37539 raw37539Labels = mixedMoment B node3262 node3262Labels := by
  calc
    mixedMoment B raw37539 raw37539Labels = mixedMoment B raw37539step0 raw37539step0Labels := by
      have hz : ∀ j, raw37539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37539step0 = (fun i j => raw37539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37539step0 raw37539; decide +kernel
      have hl : raw37539step0Labels = raw37539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37539 raw37539Labels permutation434 hz
    mixedMoment B raw37539step0 raw37539step0Labels = mixedMoment B raw37539step1 raw37539step1Labels := by
      have ha : raw37539step1 = (fun i j => raw37539step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37539step1 raw37539step0; decide +kernel
      have hl : raw37539step1Labels = raw37539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37539step0 raw37539step0Labels permutation149 permutation2
    _ = mixedMoment B node3262 node3262Labels := by rfl

theorem canonical37540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37540 raw37540Labels = mixedMoment B node3262 node3262Labels := by
  calc
    mixedMoment B raw37540 raw37540Labels = mixedMoment B raw37540step0 raw37540step0Labels := by
      have hz : ∀ j, raw37540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37540step0 = (fun i j => raw37540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37540step0 raw37540; decide +kernel
      have hl : raw37540step0Labels = raw37540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37540 raw37540Labels permutation346 hz
    mixedMoment B raw37540step0 raw37540step0Labels = mixedMoment B raw37540step1 raw37540step1Labels := by
      have ha : raw37540step1 = (fun i j => raw37540step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37540step1 raw37540step0; decide +kernel
      have hl : raw37540step1Labels = raw37540step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37540step0 raw37540step0Labels permutation149 permutation2
    _ = mixedMoment B node3262 node3262Labels := by rfl

theorem canonical37541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37541 raw37541Labels = mixedMoment B node3275 node3275Labels := by
  calc
    mixedMoment B raw37541 raw37541Labels = mixedMoment B raw37541step0 raw37541step0Labels := by
      have hz : ∀ j, raw37541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37541step0 = (fun i j => raw37541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37541step0 raw37541; decide +kernel
      have hl : raw37541step0Labels = raw37541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37541 raw37541Labels permutation434 hz
    mixedMoment B raw37541step0 raw37541step0Labels = mixedMoment B raw37541step1 raw37541step1Labels := by
      have hz : ∀ j, raw37541step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37541step1 = (fun i j => raw37541step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37541step1 raw37541step0; decide +kernel
      have hl : raw37541step1Labels = raw37541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37541step0 raw37541step0Labels permutation80 hz
    mixedMoment B raw37541step1 raw37541step1Labels = mixedMoment B raw37541step2 raw37541step2Labels := by
      have ha : raw37541step2 = (fun i j => raw37541step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37541step2 raw37541step1; decide +kernel
      have hl : raw37541step2Labels = raw37541step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37541step1 raw37541step1Labels permutation31 permutation4
    _ = mixedMoment B node3275 node3275Labels := by rfl

theorem canonical37542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37542 raw37542Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw37542 raw37542Labels = mixedMoment B raw37542step0 raw37542step0Labels := by
      have hz : ∀ j, raw37542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37542step0 = (fun i j => raw37542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37542step0 raw37542; decide +kernel
      have hl : raw37542step0Labels = raw37542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37542 raw37542Labels permutation434 hz
    mixedMoment B raw37542step0 raw37542step0Labels = mixedMoment B raw37542step1 raw37542step1Labels := by
      have hz : ∀ j, raw37542step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37542step1 = (fun i j => raw37542step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37542step1 raw37542step0; decide +kernel
      have hl : raw37542step1Labels = raw37542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37542step0 raw37542step0Labels permutation80 hz
    mixedMoment B raw37542step1 raw37542step1Labels = mixedMoment B raw37542step2 raw37542step2Labels := by
      have ha : raw37542step2 = (fun i j => raw37542step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37542step2 raw37542step1; decide +kernel
      have hl : raw37542step2Labels = raw37542step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37542step1 raw37542step1Labels permutation31 permutation4
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical37552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37552 raw37552Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw37552 raw37552Labels = mixedMoment B raw37552step0 raw37552step0Labels := by
      have hz : ∀ j, raw37552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37552step0 = (fun i j => raw37552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37552step0 raw37552; decide +kernel
      have hl : raw37552step0Labels = raw37552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37552 raw37552Labels permutation434 hz
    mixedMoment B raw37552step0 raw37552step0Labels = mixedMoment B raw37552step1 raw37552step1Labels := by
      have hz : ∀ j, raw37552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37552step1 = (fun i j => raw37552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37552step1 raw37552step0; decide +kernel
      have hl : raw37552step1Labels = raw37552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37552step0 raw37552step0Labels permutation80 hz
    mixedMoment B raw37552step1 raw37552step1Labels = mixedMoment B raw37552step2 raw37552step2Labels := by
      have ha : raw37552step2 = (fun i j => raw37552step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37552step2 raw37552step1; decide +kernel
      have hl : raw37552step2Labels = raw37552step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37552step1 raw37552step1Labels permutation31 permutation2
    _ = mixedMoment B node2167 node2167Labels := by rfl

theorem canonical37553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37553 raw37553Labels = mixedMoment B node1743 node1743Labels := by
  calc
    mixedMoment B raw37553 raw37553Labels = mixedMoment B raw37553step0 raw37553step0Labels := by
      have hz : ∀ j, raw37553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37553step0 = (fun i j => raw37553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37553step0 raw37553; decide +kernel
      have hl : raw37553step0Labels = raw37553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37553 raw37553Labels permutation434 hz
    mixedMoment B raw37553step0 raw37553step0Labels = mixedMoment B raw37553step1 raw37553step1Labels := by
      have hz : ∀ j, raw37553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37553step1 = (fun i j => raw37553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37553step1 raw37553step0; decide +kernel
      have hl : raw37553step1Labels = raw37553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37553step0 raw37553step0Labels permutation80 hz
    mixedMoment B raw37553step1 raw37553step1Labels = mixedMoment B raw37553step2 raw37553step2Labels := by
      have ha : raw37553step2 = (fun i j => raw37553step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37553step2 raw37553step1; decide +kernel
      have hl : raw37553step2Labels = raw37553step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37553step1 raw37553step1Labels permutation12 permutation4
    mixedMoment B raw37553step2 raw37553step2Labels = mixedMoment B raw37553step3 raw37553step3Labels := by
      have ha : raw37553step3 = -raw37553step2 := by apply Matrix.ext; change ∀ i j, raw37553step3 i j = -(raw37553step2 i j); unfold raw37553step3 raw37553step2; decide +kernel
      have hl : raw37553step3Labels = raw37553step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1743 node1743Labels := by rfl

theorem canonical37554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37554 raw37554Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw37554 raw37554Labels = mixedMoment B raw37554step0 raw37554step0Labels := by
      have hz : ∀ j, raw37554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37554step0 = (fun i j => raw37554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37554step0 raw37554; decide +kernel
      have hl : raw37554step0Labels = raw37554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37554 raw37554Labels permutation434 hz
    mixedMoment B raw37554step0 raw37554step0Labels = mixedMoment B raw37554step1 raw37554step1Labels := by
      have ha : raw37554step1 = (fun i j => raw37554step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37554step1 raw37554step0; decide +kernel
      have hl : raw37554step1Labels = raw37554step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37554step0 raw37554step0Labels permutation36 permutation4
    mixedMoment B raw37554step1 raw37554step1Labels = mixedMoment B raw37554step2 raw37554step2Labels := by
      have ha : raw37554step2 = -raw37554step1 := by apply Matrix.ext; change ∀ i j, raw37554step2 i j = -(raw37554step1 i j); unfold raw37554step2 raw37554step1; decide +kernel
      have hl : raw37554step2Labels = raw37554step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1685 node1685Labels := by rfl

theorem canonical37555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37555 raw37555Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw37555 raw37555Labels = mixedMoment B raw37555step0 raw37555step0Labels := by
      have hz : ∀ j, raw37555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37555step0 = (fun i j => raw37555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37555step0 raw37555; decide +kernel
      have hl : raw37555step0Labels = raw37555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37555 raw37555Labels permutation346 hz
    mixedMoment B raw37555step0 raw37555step0Labels = mixedMoment B raw37555step1 raw37555step1Labels := by
      have ha : raw37555step1 = (fun i j => raw37555step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37555step1 raw37555step0; decide +kernel
      have hl : raw37555step1Labels = raw37555step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37555step0 raw37555step0Labels permutation36 permutation4
    mixedMoment B raw37555step1 raw37555step1Labels = mixedMoment B raw37555step2 raw37555step2Labels := by
      have ha : raw37555step2 = -raw37555step1 := by apply Matrix.ext; change ∀ i j, raw37555step2 i j = -(raw37555step1 i j); unfold raw37555step2 raw37555step1; decide +kernel
      have hl : raw37555step2Labels = raw37555step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1685 node1685Labels := by rfl

theorem canonical37556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37556 raw37556Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw37556 raw37556Labels = mixedMoment B raw37556step0 raw37556step0Labels := by
      have hz : ∀ j, raw37556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37556step0 = (fun i j => raw37556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37556step0 raw37556; decide +kernel
      have hl : raw37556step0Labels = raw37556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37556 raw37556Labels permutation434 hz
    mixedMoment B raw37556step0 raw37556step0Labels = mixedMoment B raw37556step1 raw37556step1Labels := by
      have hz : ∀ j, raw37556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37556step1 = (fun i j => raw37556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37556step1 raw37556step0; decide +kernel
      have hl : raw37556step1Labels = raw37556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37556step0 raw37556step0Labels permutation80 hz
    mixedMoment B raw37556step1 raw37556step1Labels = mixedMoment B raw37556step2 raw37556step2Labels := by
      have ha : raw37556step2 = (fun i j => raw37556step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37556step2 raw37556step1; decide +kernel
      have hl : raw37556step2Labels = raw37556step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37556step1 raw37556step1Labels permutation9 permutation4
    mixedMoment B raw37556step2 raw37556step2Labels = mixedMoment B raw37556step3 raw37556step3Labels := by
      have ha : raw37556step3 = -raw37556step2 := by apply Matrix.ext; change ∀ i j, raw37556step3 i j = -(raw37556step2 i j); unfold raw37556step3 raw37556step2; decide +kernel
      have hl : raw37556step3Labels = raw37556step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1687 node1687Labels := by rfl

theorem canonical37557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37557 raw37557Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw37557 raw37557Labels = mixedMoment B raw37557step0 raw37557step0Labels := by
      have hz : ∀ j, raw37557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37557step0 = (fun i j => raw37557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37557step0 raw37557; decide +kernel
      have hl : raw37557step0Labels = raw37557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37557 raw37557Labels permutation434 hz
    mixedMoment B raw37557step0 raw37557step0Labels = mixedMoment B raw37557step1 raw37557step1Labels := by
      have hz : ∀ j, raw37557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37557step1 = (fun i j => raw37557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37557step1 raw37557step0; decide +kernel
      have hl : raw37557step1Labels = raw37557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37557step0 raw37557step0Labels permutation80 hz
    mixedMoment B raw37557step1 raw37557step1Labels = mixedMoment B raw37557step2 raw37557step2Labels := by
      have ha : raw37557step2 = (fun i j => raw37557step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37557step2 raw37557step1; decide +kernel
      have hl : raw37557step2Labels = raw37557step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37557step1 raw37557step1Labels permutation9 permutation4
    mixedMoment B raw37557step2 raw37557step2Labels = mixedMoment B raw37557step3 raw37557step3Labels := by
      have ha : raw37557step3 = -raw37557step2 := by apply Matrix.ext; change ∀ i j, raw37557step3 i j = -(raw37557step2 i j); unfold raw37557step3 raw37557step2; decide +kernel
      have hl : raw37557step3Labels = raw37557step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1694 node1694Labels := by rfl

theorem canonical37558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37558 raw37558Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw37558 raw37558Labels = mixedMoment B raw37558step0 raw37558step0Labels := by
      have hz : ∀ j, raw37558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37558step0 = (fun i j => raw37558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37558step0 raw37558; decide +kernel
      have hl : raw37558step0Labels = raw37558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37558 raw37558Labels permutation434 hz
    mixedMoment B raw37558step0 raw37558step0Labels = mixedMoment B raw37558step1 raw37558step1Labels := by
      have hz : ∀ j, raw37558step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37558step1 = (fun i j => raw37558step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37558step1 raw37558step0; decide +kernel
      have hl : raw37558step1Labels = raw37558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37558step0 raw37558step0Labels permutation80 hz
    mixedMoment B raw37558step1 raw37558step1Labels = mixedMoment B raw37558step2 raw37558step2Labels := by
      have ha : raw37558step2 = -raw37558step1 := by apply Matrix.ext; change ∀ i j, raw37558step2 i j = -(raw37558step1 i j); unfold raw37558step2 raw37558step1; decide +kernel
      have hl : raw37558step2Labels = raw37558step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4067 node4067Labels := by rfl

theorem canonical37559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37559 raw37559Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw37559 raw37559Labels = mixedMoment B raw37559step0 raw37559step0Labels := by
      have hz : ∀ j, raw37559 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37559step0 = (fun i j => raw37559 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37559step0 raw37559; decide +kernel
      have hl : raw37559step0Labels = raw37559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37559 raw37559Labels permutation434 hz
    mixedMoment B raw37559step0 raw37559step0Labels = mixedMoment B raw37559step1 raw37559step1Labels := by
      have hz : ∀ j, raw37559step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37559step1 = (fun i j => raw37559step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37559step1 raw37559step0; decide +kernel
      have hl : raw37559step1Labels = raw37559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37559step0 raw37559step0Labels permutation80 hz
    mixedMoment B raw37559step1 raw37559step1Labels = mixedMoment B raw37559step2 raw37559step2Labels := by
      have ha : raw37559step2 = (fun i j => raw37559step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37559step2 raw37559step1; decide +kernel
      have hl : raw37559step2Labels = raw37559step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37559step1 raw37559step1Labels permutation9 permutation2
    mixedMoment B raw37559step2 raw37559step2Labels = mixedMoment B raw37559step3 raw37559step3Labels := by
      have ha : raw37559step3 = -raw37559step2 := by apply Matrix.ext; change ∀ i j, raw37559step3 i j = -(raw37559step2 i j); unfold raw37559step3 raw37559step2; decide +kernel
      have hl : raw37559step3Labels = raw37559step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3277 node3277Labels := by rfl

theorem canonical37560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37560 raw37560Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw37560 raw37560Labels = mixedMoment B raw37560step0 raw37560step0Labels := by
      have hz : ∀ j, raw37560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37560step0 = (fun i j => raw37560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37560step0 raw37560; decide +kernel
      have hl : raw37560step0Labels = raw37560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37560 raw37560Labels permutation434 hz
    mixedMoment B raw37560step0 raw37560step0Labels = mixedMoment B raw37560step1 raw37560step1Labels := by
      have hz : ∀ j, raw37560step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37560step1 = (fun i j => raw37560step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37560step1 raw37560step0; decide +kernel
      have hl : raw37560step1Labels = raw37560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37560step0 raw37560step0Labels permutation80 hz
    mixedMoment B raw37560step1 raw37560step1Labels = mixedMoment B raw37560step2 raw37560step2Labels := by
      have ha : raw37560step2 = (fun i j => raw37560step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37560step2 raw37560step1; decide +kernel
      have hl : raw37560step2Labels = raw37560step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37560step1 raw37560step1Labels permutation10 permutation4
    mixedMoment B raw37560step2 raw37560step2Labels = mixedMoment B raw37560step3 raw37560step3Labels := by
      have ha : raw37560step3 = -raw37560step2 := by apply Matrix.ext; change ∀ i j, raw37560step3 i j = -(raw37560step2 i j); unfold raw37560step3 raw37560step2; decide +kernel
      have hl : raw37560step3Labels = raw37560step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1735 node1735Labels := by rfl

theorem canonical37561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37561 raw37561Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw37561 raw37561Labels = mixedMoment B raw37561step0 raw37561step0Labels := by
      have hz : ∀ j, raw37561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37561step0 = (fun i j => raw37561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37561step0 raw37561; decide +kernel
      have hl : raw37561step0Labels = raw37561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37561 raw37561Labels permutation434 hz
    mixedMoment B raw37561step0 raw37561step0Labels = mixedMoment B raw37561step1 raw37561step1Labels := by
      have ha : raw37561step1 = (fun i j => raw37561step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37561step1 raw37561step0; decide +kernel
      have hl : raw37561step1Labels = raw37561step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37561step0 raw37561step0Labels permutation34 permutation4
    mixedMoment B raw37561step1 raw37561step1Labels = mixedMoment B raw37561step2 raw37561step2Labels := by
      have ha : raw37561step2 = -raw37561step1 := by apply Matrix.ext; change ∀ i j, raw37561step2 i j = -(raw37561step1 i j); unfold raw37561step2 raw37561step1; decide +kernel
      have hl : raw37561step2Labels = raw37561step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1679 node1679Labels := by rfl

theorem canonical37562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37562 raw37562Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw37562 raw37562Labels = mixedMoment B raw37562step0 raw37562step0Labels := by
      have hz : ∀ j, raw37562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37562step0 = (fun i j => raw37562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37562step0 raw37562; decide +kernel
      have hl : raw37562step0Labels = raw37562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37562 raw37562Labels permutation346 hz
    mixedMoment B raw37562step0 raw37562step0Labels = mixedMoment B raw37562step1 raw37562step1Labels := by
      have ha : raw37562step1 = (fun i j => raw37562step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37562step1 raw37562step0; decide +kernel
      have hl : raw37562step1Labels = raw37562step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37562step0 raw37562step0Labels permutation34 permutation4
    mixedMoment B raw37562step1 raw37562step1Labels = mixedMoment B raw37562step2 raw37562step2Labels := by
      have ha : raw37562step2 = -raw37562step1 := by apply Matrix.ext; change ∀ i j, raw37562step2 i j = -(raw37562step1 i j); unfold raw37562step2 raw37562step1; decide +kernel
      have hl : raw37562step2Labels = raw37562step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1679 node1679Labels := by rfl

theorem canonical37563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37563 raw37563Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw37563 raw37563Labels = mixedMoment B raw37563step0 raw37563step0Labels := by
      have hz : ∀ j, raw37563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37563step0 = (fun i j => raw37563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37563step0 raw37563; decide +kernel
      have hl : raw37563step0Labels = raw37563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37563 raw37563Labels permutation434 hz
    mixedMoment B raw37563step0 raw37563step0Labels = mixedMoment B raw37563step1 raw37563step1Labels := by
      have hz : ∀ j, raw37563step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37563step1 = (fun i j => raw37563step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37563step1 raw37563step0; decide +kernel
      have hl : raw37563step1Labels = raw37563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37563step0 raw37563step0Labels permutation80 hz
    mixedMoment B raw37563step1 raw37563step1Labels = mixedMoment B raw37563step2 raw37563step2Labels := by
      have ha : raw37563step2 = (fun i j => raw37563step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37563step2 raw37563step1; decide +kernel
      have hl : raw37563step2Labels = raw37563step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37563step1 raw37563step1Labels permutation8 permutation4
    mixedMoment B raw37563step2 raw37563step2Labels = mixedMoment B raw37563step3 raw37563step3Labels := by
      have ha : raw37563step3 = -raw37563step2 := by apply Matrix.ext; change ∀ i j, raw37563step3 i j = -(raw37563step2 i j); unfold raw37563step3 raw37563step2; decide +kernel
      have hl : raw37563step3Labels = raw37563step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1693 node1693Labels := by rfl

theorem canonical37564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37564 raw37564Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw37564 raw37564Labels = mixedMoment B raw37564step0 raw37564step0Labels := by
      have hz : ∀ j, raw37564 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37564step0 = (fun i j => raw37564 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37564step0 raw37564; decide +kernel
      have hl : raw37564step0Labels = raw37564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37564 raw37564Labels permutation434 hz
    mixedMoment B raw37564step0 raw37564step0Labels = mixedMoment B raw37564step1 raw37564step1Labels := by
      have hz : ∀ j, raw37564step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37564step1 = (fun i j => raw37564step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37564step1 raw37564step0; decide +kernel
      have hl : raw37564step1Labels = raw37564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37564step0 raw37564step0Labels permutation80 hz
    mixedMoment B raw37564step1 raw37564step1Labels = mixedMoment B raw37564step2 raw37564step2Labels := by
      have ha : raw37564step2 = (fun i j => raw37564step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37564step2 raw37564step1; decide +kernel
      have hl : raw37564step2Labels = raw37564step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37564step1 raw37564step1Labels permutation8 permutation4
    mixedMoment B raw37564step2 raw37564step2Labels = mixedMoment B raw37564step3 raw37564step3Labels := by
      have ha : raw37564step3 = -raw37564step2 := by apply Matrix.ext; change ∀ i j, raw37564step3 i j = -(raw37564step2 i j); unfold raw37564step3 raw37564step2; decide +kernel
      have hl : raw37564step3Labels = raw37564step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1683 node1683Labels := by rfl

theorem canonical37565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37565 raw37565Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw37565 raw37565Labels = mixedMoment B raw37565step0 raw37565step0Labels := by
      have hz : ∀ j, raw37565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37565step0 = (fun i j => raw37565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37565step0 raw37565; decide +kernel
      have hl : raw37565step0Labels = raw37565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37565 raw37565Labels permutation434 hz
    mixedMoment B raw37565step0 raw37565step0Labels = mixedMoment B raw37565step1 raw37565step1Labels := by
      have hz : ∀ j, raw37565step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37565step1 = (fun i j => raw37565step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37565step1 raw37565step0; decide +kernel
      have hl : raw37565step1Labels = raw37565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37565step0 raw37565step0Labels permutation80 hz
    mixedMoment B raw37565step1 raw37565step1Labels = mixedMoment B raw37565step2 raw37565step2Labels := by
      have ha : raw37565step2 = -raw37565step1 := by apply Matrix.ext; change ∀ i j, raw37565step2 i j = -(raw37565step1 i j); unfold raw37565step2 raw37565step1; decide +kernel
      have hl : raw37565step2Labels = raw37565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3276 node3276Labels := by rfl

theorem canonical37566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37566 raw37566Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw37566 raw37566Labels = mixedMoment B raw37566step0 raw37566step0Labels := by
      have hz : ∀ j, raw37566 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37566step0 = (fun i j => raw37566 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37566step0 raw37566; decide +kernel
      have hl : raw37566step0Labels = raw37566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37566 raw37566Labels permutation434 hz
    mixedMoment B raw37566step0 raw37566step0Labels = mixedMoment B raw37566step1 raw37566step1Labels := by
      have hz : ∀ j, raw37566step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37566step1 = (fun i j => raw37566step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37566step1 raw37566step0; decide +kernel
      have hl : raw37566step1Labels = raw37566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37566step0 raw37566step0Labels permutation80 hz
    mixedMoment B raw37566step1 raw37566step1Labels = mixedMoment B raw37566step2 raw37566step2Labels := by
      have ha : raw37566step2 = (fun i j => raw37566step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37566step2 raw37566step1; decide +kernel
      have hl : raw37566step2Labels = raw37566step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37566step1 raw37566step1Labels permutation8 permutation4
    mixedMoment B raw37566step2 raw37566step2Labels = mixedMoment B raw37566step3 raw37566step3Labels := by
      have ha : raw37566step3 = -raw37566step2 := by apply Matrix.ext; change ∀ i j, raw37566step3 i j = -(raw37566step2 i j); unfold raw37566step3 raw37566step2; decide +kernel
      have hl : raw37566step3Labels = raw37566step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1748 node1748Labels := by rfl

theorem canonical37567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37567 raw37567Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw37567 raw37567Labels = mixedMoment B raw37567step0 raw37567step0Labels := by
      have hz : ∀ j, raw37567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37567step0 = (fun i j => raw37567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37567step0 raw37567; decide +kernel
      have hl : raw37567step0Labels = raw37567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37567 raw37567Labels permutation434 hz
    mixedMoment B raw37567step0 raw37567step0Labels = mixedMoment B raw37567step1 raw37567step1Labels := by
      have ha : raw37567step1 = (fun i j => raw37567step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37567step1 raw37567step0; decide +kernel
      have hl : raw37567step1Labels = raw37567step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37567step0 raw37567step0Labels permutation32 permutation4
    mixedMoment B raw37567step1 raw37567step1Labels = mixedMoment B raw37567step2 raw37567step2Labels := by
      have ha : raw37567step2 = -raw37567step1 := by apply Matrix.ext; change ∀ i j, raw37567step2 i j = -(raw37567step1 i j); unfold raw37567step2 raw37567step1; decide +kernel
      have hl : raw37567step2Labels = raw37567step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical37568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37568 raw37568Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw37568 raw37568Labels = mixedMoment B raw37568step0 raw37568step0Labels := by
      have hz : ∀ j, raw37568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37568step0 = (fun i j => raw37568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37568step0 raw37568; decide +kernel
      have hl : raw37568step0Labels = raw37568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37568 raw37568Labels permutation346 hz
    mixedMoment B raw37568step0 raw37568step0Labels = mixedMoment B raw37568step1 raw37568step1Labels := by
      have ha : raw37568step1 = (fun i j => raw37568step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37568step1 raw37568step0; decide +kernel
      have hl : raw37568step1Labels = raw37568step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37568step0 raw37568step0Labels permutation32 permutation4
    mixedMoment B raw37568step1 raw37568step1Labels = mixedMoment B raw37568step2 raw37568step2Labels := by
      have ha : raw37568step2 = -raw37568step1 := by apply Matrix.ext; change ∀ i j, raw37568step2 i j = -(raw37568step1 i j); unfold raw37568step2 raw37568step1; decide +kernel
      have hl : raw37568step2Labels = raw37568step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical37569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37569 raw37569Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw37569 raw37569Labels = mixedMoment B raw37569step0 raw37569step0Labels := by
      have hz : ∀ j, raw37569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37569step0 = (fun i j => raw37569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37569step0 raw37569; decide +kernel
      have hl : raw37569step0Labels = raw37569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37569 raw37569Labels permutation434 hz
    mixedMoment B raw37569step0 raw37569step0Labels = mixedMoment B raw37569step1 raw37569step1Labels := by
      have hz : ∀ j, raw37569step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37569step1 = (fun i j => raw37569step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37569step1 raw37569step0; decide +kernel
      have hl : raw37569step1Labels = raw37569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37569step0 raw37569step0Labels permutation80 hz
    mixedMoment B raw37569step1 raw37569step1Labels = mixedMoment B raw37569step2 raw37569step2Labels := by
      have ha : raw37569step2 = -raw37569step1 := by apply Matrix.ext; change ∀ i j, raw37569step2 i j = -(raw37569step1 i j); unfold raw37569step2 raw37569step1; decide +kernel
      have hl : raw37569step2Labels = raw37569step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1683 node1683Labels := by rfl

theorem canonical37570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37570 raw37570Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw37570 raw37570Labels = mixedMoment B raw37570step0 raw37570step0Labels := by
      have hz : ∀ j, raw37570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37570step0 = (fun i j => raw37570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37570step0 raw37570; decide +kernel
      have hl : raw37570step0Labels = raw37570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37570 raw37570Labels permutation434 hz
    mixedMoment B raw37570step0 raw37570step0Labels = mixedMoment B raw37570step1 raw37570step1Labels := by
      have ha : raw37570step1 = (fun i j => raw37570step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37570step1 raw37570step0; decide +kernel
      have hl : raw37570step1Labels = raw37570step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37570step0 raw37570step0Labels permutation149 permutation2
    _ = mixedMoment B node2149 node2149Labels := by rfl

theorem canonical37571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37571 raw37571Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw37571 raw37571Labels = mixedMoment B raw37571step0 raw37571step0Labels := by
      have hz : ∀ j, raw37571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37571step0 = (fun i j => raw37571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37571step0 raw37571; decide +kernel
      have hl : raw37571step0Labels = raw37571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37571 raw37571Labels permutation346 hz
    mixedMoment B raw37571step0 raw37571step0Labels = mixedMoment B raw37571step1 raw37571step1Labels := by
      have ha : raw37571step1 = (fun i j => raw37571step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37571step1 raw37571step0; decide +kernel
      have hl : raw37571step1Labels = raw37571step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37571step0 raw37571step0Labels permutation149 permutation2
    _ = mixedMoment B node2149 node2149Labels := by rfl

theorem canonical37572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37572 raw37572Labels = mixedMoment B node2258 node2258Labels := by
  calc
    mixedMoment B raw37572 raw37572Labels = mixedMoment B raw37572step0 raw37572step0Labels := by
      have hz : ∀ j, raw37572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37572step0 = (fun i j => raw37572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37572step0 raw37572; decide +kernel
      have hl : raw37572step0Labels = raw37572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37572 raw37572Labels permutation434 hz
    mixedMoment B raw37572step0 raw37572step0Labels = mixedMoment B raw37572step1 raw37572step1Labels := by
      have hz : ∀ j, raw37572step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37572step1 = (fun i j => raw37572step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37572step1 raw37572step0; decide +kernel
      have hl : raw37572step1Labels = raw37572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37572step0 raw37572step0Labels permutation80 hz
    mixedMoment B raw37572step1 raw37572step1Labels = mixedMoment B raw37572step2 raw37572step2Labels := by
      have ha : raw37572step2 = (fun i j => raw37572step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37572step2 raw37572step1; decide +kernel
      have hl : raw37572step2Labels = raw37572step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37572step1 raw37572step1Labels permutation29 permutation2
    _ = mixedMoment B node2258 node2258Labels := by rfl

theorem canonical37573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37573 raw37573Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw37573 raw37573Labels = mixedMoment B raw37573step0 raw37573step0Labels := by
      have hz : ∀ j, raw37573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37573step0 = (fun i j => raw37573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37573step0 raw37573; decide +kernel
      have hl : raw37573step0Labels = raw37573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37573 raw37573Labels permutation434 hz
    mixedMoment B raw37573step0 raw37573step0Labels = mixedMoment B raw37573step1 raw37573step1Labels := by
      have hz : ∀ j, raw37573step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37573step1 = (fun i j => raw37573step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37573step1 raw37573step0; decide +kernel
      have hl : raw37573step1Labels = raw37573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37573step0 raw37573step0Labels permutation80 hz
    mixedMoment B raw37573step1 raw37573step1Labels = mixedMoment B raw37573step2 raw37573step2Labels := by
      have ha : raw37573step2 = (fun i j => raw37573step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37573step2 raw37573step1; decide +kernel
      have hl : raw37573step2Labels = raw37573step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37573step1 raw37573step1Labels permutation9 permutation4
    mixedMoment B raw37573step2 raw37573step2Labels = mixedMoment B raw37573step3 raw37573step3Labels := by
      have ha : raw37573step3 = -raw37573step2 := by apply Matrix.ext; change ∀ i j, raw37573step3 i j = -(raw37573step2 i j); unfold raw37573step3 raw37573step2; decide +kernel
      have hl : raw37573step3Labels = raw37573step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3277 node3277Labels := by rfl

theorem canonical37574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37574 raw37574Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw37574 raw37574Labels = mixedMoment B raw37574step0 raw37574step0Labels := by
      have hz : ∀ j, raw37574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37574step0 = (fun i j => raw37574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37574step0 raw37574; decide +kernel
      have hl : raw37574step0Labels = raw37574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37574 raw37574Labels permutation434 hz
    mixedMoment B raw37574step0 raw37574step0Labels = mixedMoment B raw37574step1 raw37574step1Labels := by
      have hz : ∀ j, raw37574step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37574step1 = (fun i j => raw37574step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37574step1 raw37574step0; decide +kernel
      have hl : raw37574step1Labels = raw37574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37574step0 raw37574step0Labels permutation80 hz
    mixedMoment B raw37574step1 raw37574step1Labels = mixedMoment B raw37574step2 raw37574step2Labels := by
      have ha : raw37574step2 = (fun i j => raw37574step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37574step2 raw37574step1; decide +kernel
      have hl : raw37574step2Labels = raw37574step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37574step1 raw37574step1Labels permutation9 permutation2
    mixedMoment B raw37574step2 raw37574step2Labels = mixedMoment B raw37574step3 raw37574step3Labels := by
      have ha : raw37574step3 = -raw37574step2 := by apply Matrix.ext; change ∀ i j, raw37574step3 i j = -(raw37574step2 i j); unfold raw37574step3 raw37574step2; decide +kernel
      have hl : raw37574step3Labels = raw37574step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1694 node1694Labels := by rfl

theorem canonical37575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37575 raw37575Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw37575 raw37575Labels = mixedMoment B raw37575step0 raw37575step0Labels := by
      have hz : ∀ j, raw37575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37575step0 = (fun i j => raw37575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37575step0 raw37575; decide +kernel
      have hl : raw37575step0Labels = raw37575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37575 raw37575Labels permutation434 hz
    mixedMoment B raw37575step0 raw37575step0Labels = mixedMoment B raw37575step1 raw37575step1Labels := by
      have ha : raw37575step1 = (fun i j => raw37575step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37575step1 raw37575step0; decide +kernel
      have hl : raw37575step1Labels = raw37575step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37575step0 raw37575step0Labels permutation34 permutation4
    mixedMoment B raw37575step1 raw37575step1Labels = mixedMoment B raw37575step2 raw37575step2Labels := by
      have ha : raw37575step2 = -raw37575step1 := by apply Matrix.ext; change ∀ i j, raw37575step2 i j = -(raw37575step1 i j); unfold raw37575step2 raw37575step1; decide +kernel
      have hl : raw37575step2Labels = raw37575step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3268 node3268Labels := by rfl

theorem canonical37576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37576 raw37576Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw37576 raw37576Labels = mixedMoment B raw37576step0 raw37576step0Labels := by
      have hz : ∀ j, raw37576 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37576step0 = (fun i j => raw37576 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37576step0 raw37576; decide +kernel
      have hl : raw37576step0Labels = raw37576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37576 raw37576Labels permutation346 hz
    mixedMoment B raw37576step0 raw37576step0Labels = mixedMoment B raw37576step1 raw37576step1Labels := by
      have ha : raw37576step1 = (fun i j => raw37576step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37576step1 raw37576step0; decide +kernel
      have hl : raw37576step1Labels = raw37576step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37576step0 raw37576step0Labels permutation34 permutation4
    mixedMoment B raw37576step1 raw37576step1Labels = mixedMoment B raw37576step2 raw37576step2Labels := by
      have ha : raw37576step2 = -raw37576step1 := by apply Matrix.ext; change ∀ i j, raw37576step2 i j = -(raw37576step1 i j); unfold raw37576step2 raw37576step1; decide +kernel
      have hl : raw37576step2Labels = raw37576step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3268 node3268Labels := by rfl

theorem canonical37577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37577 raw37577Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw37577 raw37577Labels = mixedMoment B raw37577step0 raw37577step0Labels := by
      have hz : ∀ j, raw37577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37577step0 = (fun i j => raw37577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37577step0 raw37577; decide +kernel
      have hl : raw37577step0Labels = raw37577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37577 raw37577Labels permutation434 hz
    mixedMoment B raw37577step0 raw37577step0Labels = mixedMoment B raw37577step1 raw37577step1Labels := by
      have hz : ∀ j, raw37577step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37577step1 = (fun i j => raw37577step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37577step1 raw37577step0; decide +kernel
      have hl : raw37577step1Labels = raw37577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37577step0 raw37577step0Labels permutation80 hz
    mixedMoment B raw37577step1 raw37577step1Labels = mixedMoment B raw37577step2 raw37577step2Labels := by
      have ha : raw37577step2 = (fun i j => raw37577step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37577step2 raw37577step1; decide +kernel
      have hl : raw37577step2Labels = raw37577step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37577step1 raw37577step1Labels permutation8 permutation4
    mixedMoment B raw37577step2 raw37577step2Labels = mixedMoment B raw37577step3 raw37577step3Labels := by
      have ha : raw37577step3 = -raw37577step2 := by apply Matrix.ext; change ∀ i j, raw37577step3 i j = -(raw37577step2 i j); unfold raw37577step3 raw37577step2; decide +kernel
      have hl : raw37577step3Labels = raw37577step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3276 node3276Labels := by rfl

theorem canonical37578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37578 raw37578Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw37578 raw37578Labels = mixedMoment B raw37578step0 raw37578step0Labels := by
      have hz : ∀ j, raw37578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37578step0 = (fun i j => raw37578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37578step0 raw37578; decide +kernel
      have hl : raw37578step0Labels = raw37578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37578 raw37578Labels permutation434 hz
    mixedMoment B raw37578step0 raw37578step0Labels = mixedMoment B raw37578step1 raw37578step1Labels := by
      have hz : ∀ j, raw37578step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37578step1 = (fun i j => raw37578step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37578step1 raw37578step0; decide +kernel
      have hl : raw37578step1Labels = raw37578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37578step0 raw37578step0Labels permutation80 hz
    mixedMoment B raw37578step1 raw37578step1Labels = mixedMoment B raw37578step2 raw37578step2Labels := by
      have ha : raw37578step2 = (fun i j => raw37578step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37578step2 raw37578step1; decide +kernel
      have hl : raw37578step2Labels = raw37578step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37578step1 raw37578step1Labels permutation31 permutation4
    _ = mixedMoment B node2167 node2167Labels := by rfl

theorem canonical37579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37579 raw37579Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw37579 raw37579Labels = mixedMoment B raw37579step0 raw37579step0Labels := by
      have hz : ∀ j, raw37579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37579step0 = (fun i j => raw37579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37579step0 raw37579; decide +kernel
      have hl : raw37579step0Labels = raw37579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37579 raw37579Labels permutation434 hz
    mixedMoment B raw37579step0 raw37579step0Labels = mixedMoment B raw37579step1 raw37579step1Labels := by
      have hz : ∀ j, raw37579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37579step1 = (fun i j => raw37579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37579step1 raw37579step0; decide +kernel
      have hl : raw37579step1Labels = raw37579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37579step0 raw37579step0Labels permutation80 hz
    mixedMoment B raw37579step1 raw37579step1Labels = mixedMoment B raw37579step2 raw37579step2Labels := by
      have ha : raw37579step2 = -raw37579step1 := by apply Matrix.ext; change ∀ i j, raw37579step2 i j = -(raw37579step1 i j); unfold raw37579step2 raw37579step1; decide +kernel
      have hl : raw37579step2Labels = raw37579step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1693 node1693Labels := by rfl

theorem canonical37580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37580 raw37580Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw37580 raw37580Labels = mixedMoment B raw37580step0 raw37580step0Labels := by
      have hz : ∀ j, raw37580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37580step0 = (fun i j => raw37580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37580step0 raw37580; decide +kernel
      have hl : raw37580step0Labels = raw37580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37580 raw37580Labels permutation434 hz
    mixedMoment B raw37580step0 raw37580step0Labels = mixedMoment B raw37580step1 raw37580step1Labels := by
      have ha : raw37580step1 = (fun i j => raw37580step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37580step1 raw37580step0; decide +kernel
      have hl : raw37580step1Labels = raw37580step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37580step0 raw37580step0Labels permutation32 permutation4
    mixedMoment B raw37580step1 raw37580step1Labels = mixedMoment B raw37580step2 raw37580step2Labels := by
      have ha : raw37580step2 = -raw37580step1 := by apply Matrix.ext; change ∀ i j, raw37580step2 i j = -(raw37580step1 i j); unfold raw37580step2 raw37580step1; decide +kernel
      have hl : raw37580step2Labels = raw37580step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3272 node3272Labels := by rfl

theorem canonical37581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37581 raw37581Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw37581 raw37581Labels = mixedMoment B raw37581step0 raw37581step0Labels := by
      have hz : ∀ j, raw37581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37581step0 = (fun i j => raw37581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37581step0 raw37581; decide +kernel
      have hl : raw37581step0Labels = raw37581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37581 raw37581Labels permutation346 hz
    mixedMoment B raw37581step0 raw37581step0Labels = mixedMoment B raw37581step1 raw37581step1Labels := by
      have ha : raw37581step1 = (fun i j => raw37581step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37581step1 raw37581step0; decide +kernel
      have hl : raw37581step1Labels = raw37581step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37581step0 raw37581step0Labels permutation32 permutation4
    mixedMoment B raw37581step1 raw37581step1Labels = mixedMoment B raw37581step2 raw37581step2Labels := by
      have ha : raw37581step2 = -raw37581step1 := by apply Matrix.ext; change ∀ i j, raw37581step2 i j = -(raw37581step1 i j); unfold raw37581step2 raw37581step1; decide +kernel
      have hl : raw37581step2Labels = raw37581step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3272 node3272Labels := by rfl

theorem canonical37585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37585 raw37585Labels = mixedMoment B node1579 node1579Labels := by
  calc
    mixedMoment B raw37585 raw37585Labels = mixedMoment B raw37585step0 raw37585step0Labels := by
      have hz : ∀ j, raw37585 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37585step0 = (fun i j => raw37585 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37585step0 raw37585; decide +kernel
      have hl : raw37585step0Labels = raw37585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37585 raw37585Labels permutation434 hz
    mixedMoment B raw37585step0 raw37585step0Labels = mixedMoment B raw37585step1 raw37585step1Labels := by
      have hz : ∀ j, raw37585step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37585step1 = (fun i j => raw37585step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37585step1 raw37585step0; decide +kernel
      have hl : raw37585step1Labels = raw37585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37585step0 raw37585step0Labels permutation80 hz
    mixedMoment B raw37585step1 raw37585step1Labels = mixedMoment B raw37585step2 raw37585step2Labels := by
      have ha : raw37585step2 = (fun i j => raw37585step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37585step2 raw37585step1; decide +kernel
      have hl : raw37585step2Labels = raw37585step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37585step1 raw37585step1Labels permutation8 permutation4
    mixedMoment B raw37585step2 raw37585step2Labels = mixedMoment B raw37585step3 raw37585step3Labels := by
      have ha : raw37585step3 = -raw37585step2 := by apply Matrix.ext; change ∀ i j, raw37585step3 i j = -(raw37585step2 i j); unfold raw37585step3 raw37585step2; decide +kernel
      have hl : raw37585step3Labels = raw37585step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1579 node1579Labels := by rfl

theorem canonical37586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37586 raw37586Labels = mixedMoment B node3237 node3237Labels := by
  calc
    mixedMoment B raw37586 raw37586Labels = mixedMoment B raw37586step0 raw37586step0Labels := by
      have hz : ∀ j, raw37586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37586step0 = (fun i j => raw37586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37586step0 raw37586; decide +kernel
      have hl : raw37586step0Labels = raw37586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37586 raw37586Labels permutation434 hz
    mixedMoment B raw37586step0 raw37586step0Labels = mixedMoment B raw37586step1 raw37586step1Labels := by
      have hz : ∀ j, raw37586step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37586step1 = (fun i j => raw37586step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37586step1 raw37586step0; decide +kernel
      have hl : raw37586step1Labels = raw37586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37586step0 raw37586step0Labels permutation80 hz
    mixedMoment B raw37586step1 raw37586step1Labels = mixedMoment B raw37586step2 raw37586step2Labels := by
      have ha : raw37586step2 = (fun i j => raw37586step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37586step2 raw37586step1; decide +kernel
      have hl : raw37586step2Labels = raw37586step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37586step1 raw37586step1Labels permutation8 permutation4
    mixedMoment B raw37586step2 raw37586step2Labels = mixedMoment B raw37586step3 raw37586step3Labels := by
      have ha : raw37586step3 = -raw37586step2 := by apply Matrix.ext; change ∀ i j, raw37586step3 i j = -(raw37586step2 i j); unfold raw37586step3 raw37586step2; decide +kernel
      have hl : raw37586step3Labels = raw37586step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3237 node3237Labels := by rfl

theorem canonical37587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37587 raw37587Labels = mixedMoment B node3252 node3252Labels := by
  calc
    mixedMoment B raw37587 raw37587Labels = mixedMoment B raw37587step0 raw37587step0Labels := by
      have hz : ∀ j, raw37587 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37587step0 = (fun i j => raw37587 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37587step0 raw37587; decide +kernel
      have hl : raw37587step0Labels = raw37587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37587 raw37587Labels permutation434 hz
    mixedMoment B raw37587step0 raw37587step0Labels = mixedMoment B raw37587step1 raw37587step1Labels := by
      have ha : raw37587step1 = (fun i j => raw37587step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37587step1 raw37587step0; decide +kernel
      have hl : raw37587step1Labels = raw37587step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37587step0 raw37587step0Labels permutation32 permutation4
    mixedMoment B raw37587step1 raw37587step1Labels = mixedMoment B raw37587step2 raw37587step2Labels := by
      have ha : raw37587step2 = -raw37587step1 := by apply Matrix.ext; change ∀ i j, raw37587step2 i j = -(raw37587step1 i j); unfold raw37587step2 raw37587step1; decide +kernel
      have hl : raw37587step2Labels = raw37587step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3252 node3252Labels := by rfl

theorem canonical37588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37588 raw37588Labels = mixedMoment B node3252 node3252Labels := by
  calc
    mixedMoment B raw37588 raw37588Labels = mixedMoment B raw37588step0 raw37588step0Labels := by
      have hz : ∀ j, raw37588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37588step0 = (fun i j => raw37588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37588step0 raw37588; decide +kernel
      have hl : raw37588step0Labels = raw37588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37588 raw37588Labels permutation346 hz
    mixedMoment B raw37588step0 raw37588step0Labels = mixedMoment B raw37588step1 raw37588step1Labels := by
      have ha : raw37588step1 = (fun i j => raw37588step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37588step1 raw37588step0; decide +kernel
      have hl : raw37588step1Labels = raw37588step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37588step0 raw37588step0Labels permutation32 permutation4
    mixedMoment B raw37588step1 raw37588step1Labels = mixedMoment B raw37588step2 raw37588step2Labels := by
      have ha : raw37588step2 = -raw37588step1 := by apply Matrix.ext; change ∀ i j, raw37588step2 i j = -(raw37588step1 i j); unfold raw37588step2 raw37588step1; decide +kernel
      have hl : raw37588step2Labels = raw37588step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3252 node3252Labels := by rfl

theorem canonical37591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37591 raw37591Labels = mixedMoment B node1576 node1576Labels := by
  calc
    mixedMoment B raw37591 raw37591Labels = mixedMoment B raw37591step0 raw37591step0Labels := by
      have hz : ∀ j, raw37591 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37591step0 = (fun i j => raw37591 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37591step0 raw37591; decide +kernel
      have hl : raw37591step0Labels = raw37591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37591 raw37591Labels permutation434 hz
    mixedMoment B raw37591step0 raw37591step0Labels = mixedMoment B raw37591step1 raw37591step1Labels := by
      have hz : ∀ j, raw37591step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37591step1 = (fun i j => raw37591step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37591step1 raw37591step0; decide +kernel
      have hl : raw37591step1Labels = raw37591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37591step0 raw37591step0Labels permutation80 hz
    mixedMoment B raw37591step1 raw37591step1Labels = mixedMoment B raw37591step2 raw37591step2Labels := by
      have ha : raw37591step2 = (fun i j => raw37591step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37591step2 raw37591step1; decide +kernel
      have hl : raw37591step2Labels = raw37591step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37591step1 raw37591step1Labels permutation8 permutation4
    mixedMoment B raw37591step2 raw37591step2Labels = mixedMoment B raw37591step3 raw37591step3Labels := by
      have ha : raw37591step3 = -raw37591step2 := by apply Matrix.ext; change ∀ i j, raw37591step3 i j = -(raw37591step2 i j); unfold raw37591step3 raw37591step2; decide +kernel
      have hl : raw37591step3Labels = raw37591step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1576 node1576Labels := by rfl

theorem canonical37592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37592 raw37592Labels = mixedMoment B node1858 node1858Labels := by
  calc
    mixedMoment B raw37592 raw37592Labels = mixedMoment B raw37592step0 raw37592step0Labels := by
      have hz : ∀ j, raw37592 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37592step0 = (fun i j => raw37592 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37592step0 raw37592; decide +kernel
      have hl : raw37592step0Labels = raw37592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37592 raw37592Labels permutation434 hz
    mixedMoment B raw37592step0 raw37592step0Labels = mixedMoment B raw37592step1 raw37592step1Labels := by
      have hz : ∀ j, raw37592step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37592step1 = (fun i j => raw37592step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37592step1 raw37592step0; decide +kernel
      have hl : raw37592step1Labels = raw37592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37592step0 raw37592step0Labels permutation80 hz
    mixedMoment B raw37592step1 raw37592step1Labels = mixedMoment B raw37592step2 raw37592step2Labels := by
      have ha : raw37592step2 = (fun i j => raw37592step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37592step2 raw37592step1; decide +kernel
      have hl : raw37592step2Labels = raw37592step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37592step1 raw37592step1Labels permutation31 permutation4
    _ = mixedMoment B node1858 node1858Labels := by rfl

theorem canonical37593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37593 raw37593Labels = mixedMoment B node1849 node1849Labels := by
  calc
    mixedMoment B raw37593 raw37593Labels = mixedMoment B raw37593step0 raw37593step0Labels := by
      have hz : ∀ j, raw37593 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37593step0 = (fun i j => raw37593 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37593step0 raw37593; decide +kernel
      have hl : raw37593step0Labels = raw37593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37593 raw37593Labels permutation434 hz
    mixedMoment B raw37593step0 raw37593step0Labels = mixedMoment B raw37593step1 raw37593step1Labels := by
      have ha : raw37593step1 = (fun i j => raw37593step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37593step1 raw37593step0; decide +kernel
      have hl : raw37593step1Labels = raw37593step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37593step0 raw37593step0Labels permutation151 permutation4
    _ = mixedMoment B node1849 node1849Labels := by rfl

theorem canonical37594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37594 raw37594Labels = mixedMoment B node1849 node1849Labels := by
  calc
    mixedMoment B raw37594 raw37594Labels = mixedMoment B raw37594step0 raw37594step0Labels := by
      have hz : ∀ j, raw37594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37594step0 = (fun i j => raw37594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37594step0 raw37594; decide +kernel
      have hl : raw37594step0Labels = raw37594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37594 raw37594Labels permutation346 hz
    mixedMoment B raw37594step0 raw37594step0Labels = mixedMoment B raw37594step1 raw37594step1Labels := by
      have ha : raw37594step1 = (fun i j => raw37594step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37594step1 raw37594step0; decide +kernel
      have hl : raw37594step1Labels = raw37594step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37594step0 raw37594step0Labels permutation151 permutation4
    _ = mixedMoment B node1849 node1849Labels := by rfl

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

theorem zero666 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node666 node666Labels = 0 := by
  exact mixedMoment_order_one B hB node666 node666Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node687 node687Labels = 0 := by
  exact mixedMoment_order_one B hB node687 node687Labels 1
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

theorem sound666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node666 node666Labels = Sparse.eval nodeValue666 (mixedVector B) := by
  simpa only [nodeValue666, Sparse.eval_nil] using zero666 B _hB _hF

theorem sound687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node687 node687Labels = Sparse.eval nodeValue687 (mixedVector B) := by
  simpa only [nodeValue687, Sparse.eval_nil] using zero687 B _hB _hF

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

theorem sound1491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1491 node1491Labels = Sparse.eval nodeValue1491 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1491) = mixedMoment B node1491 node1491Labels := rfl
  simpa [nodeValue1491, Sparse.eval] using hc.symm

theorem sound1497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1497 node1497Labels = Sparse.eval nodeValue1497 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1497) = mixedMoment B node1497 node1497Labels := rfl
  simpa [nodeValue1497, Sparse.eval] using hc.symm

theorem sound1501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1501 node1501Labels = Sparse.eval nodeValue1501 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1501) = mixedMoment B node1501 node1501Labels := rfl
  simpa [nodeValue1501, Sparse.eval] using hc.symm

theorem sound1502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1502 node1502Labels = Sparse.eval nodeValue1502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1502) = mixedMoment B node1502 node1502Labels := rfl
  simpa [nodeValue1502, Sparse.eval] using hc.symm

theorem sound1503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1503 node1503Labels = Sparse.eval nodeValue1503 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1503) = mixedMoment B node1503 node1503Labels := rfl
  simpa [nodeValue1503, Sparse.eval] using hc.symm

theorem sound1504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1504 node1504Labels = Sparse.eval nodeValue1504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1504) = mixedMoment B node1504 node1504Labels := rfl
  simpa [nodeValue1504, Sparse.eval] using hc.symm

theorem sound1506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1506 node1506Labels = Sparse.eval nodeValue1506 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1506) = mixedMoment B node1506 node1506Labels := rfl
  simpa [nodeValue1506, Sparse.eval] using hc.symm

theorem sound1507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1507 node1507Labels = Sparse.eval nodeValue1507 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1507) = mixedMoment B node1507 node1507Labels := rfl
  simpa [nodeValue1507, Sparse.eval] using hc.symm

theorem sound1508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1508 node1508Labels = Sparse.eval nodeValue1508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1508) = mixedMoment B node1508 node1508Labels := rfl
  simpa [nodeValue1508, Sparse.eval] using hc.symm

theorem sound1510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1510 node1510Labels = Sparse.eval nodeValue1510 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1510) = mixedMoment B node1510 node1510Labels := rfl
  simpa [nodeValue1510, Sparse.eval] using hc.symm

theorem sound1512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1512 node1512Labels = Sparse.eval nodeValue1512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1512) = mixedMoment B node1512 node1512Labels := rfl
  simpa [nodeValue1512, Sparse.eval] using hc.symm

theorem sound1517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1517 node1517Labels = Sparse.eval nodeValue1517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1517) = mixedMoment B node1517 node1517Labels := rfl
  simpa [nodeValue1517, Sparse.eval] using hc.symm

theorem sound1524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1524 node1524Labels = Sparse.eval nodeValue1524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1524) = mixedMoment B node1524 node1524Labels := rfl
  simpa [nodeValue1524, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1576 node1576Labels = 0 := by
  exact mixedMoment_order_one B hB node1576 node1576Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1579 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1579 node1579Labels = 0 := by
  exact mixedMoment_order_one B hB node1579 node1579Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1576 node1576Labels = Sparse.eval nodeValue1576 (mixedVector B) := by
  simpa only [nodeValue1576, Sparse.eval_nil] using zero1576 B _hB _hF

theorem sound1579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1579 node1579Labels = Sparse.eval nodeValue1579 (mixedVector B) := by
  simpa only [nodeValue1579, Sparse.eval_nil] using zero1579 B _hB _hF

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

theorem sound1679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1679 node1679Labels = Sparse.eval nodeValue1679 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1679) = mixedMoment B node1679 node1679Labels := rfl
  simpa [nodeValue1679, Sparse.eval] using hc.symm

theorem sound1683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1683 node1683Labels = Sparse.eval nodeValue1683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1683) = mixedMoment B node1683 node1683Labels := rfl
  simpa [nodeValue1683, Sparse.eval] using hc.symm

theorem sound1685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1685 node1685Labels = Sparse.eval nodeValue1685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1685) = mixedMoment B node1685 node1685Labels := rfl
  simpa [nodeValue1685, Sparse.eval] using hc.symm

theorem sound1687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1687 node1687Labels = Sparse.eval nodeValue1687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1687) = mixedMoment B node1687 node1687Labels := rfl
  simpa [nodeValue1687, Sparse.eval] using hc.symm

theorem sound1688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1688 node1688Labels = Sparse.eval nodeValue1688 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1688) = mixedMoment B node1688 node1688Labels := rfl
  simpa [nodeValue1688, Sparse.eval] using hc.symm

theorem sound1689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1689 node1689Labels = Sparse.eval nodeValue1689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1689) = mixedMoment B node1689 node1689Labels := rfl
  simpa [nodeValue1689, Sparse.eval] using hc.symm

theorem sound1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1692 node1692Labels = Sparse.eval nodeValue1692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1692) = mixedMoment B node1692 node1692Labels := rfl
  simpa [nodeValue1692, Sparse.eval] using hc.symm

theorem sound1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1693 node1693Labels = Sparse.eval nodeValue1693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1693) = mixedMoment B node1693 node1693Labels := rfl
  simpa [nodeValue1693, Sparse.eval] using hc.symm

theorem sound1694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1694 node1694Labels = Sparse.eval nodeValue1694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1694) = mixedMoment B node1694 node1694Labels := rfl
  simpa [nodeValue1694, Sparse.eval] using hc.symm

theorem sound1695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1695 node1695Labels = Sparse.eval nodeValue1695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1695) = mixedMoment B node1695 node1695Labels := rfl
  simpa [nodeValue1695, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1735 node1735Labels = Sparse.eval nodeValue1735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1735) = mixedMoment B node1735 node1735Labels := rfl
  simpa [nodeValue1735, Sparse.eval] using hc.symm

theorem sound1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1743 node1743Labels = Sparse.eval nodeValue1743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1743) = mixedMoment B node1743 node1743Labels := rfl
  simpa [nodeValue1743, Sparse.eval] using hc.symm

theorem sound1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1748 node1748Labels = Sparse.eval nodeValue1748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1748) = mixedMoment B node1748 node1748Labels := rfl
  simpa [nodeValue1748, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1849 node1849Labels = Sparse.eval nodeValue1849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1849) = mixedMoment B node1849 node1849Labels := rfl
  simpa [nodeValue1849, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1858 node1858Labels = Sparse.eval nodeValue1858 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1858) = mixedMoment B node1858 node1858Labels := rfl
  simpa [nodeValue1858, Sparse.eval] using hc.symm

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

theorem sound2149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2149 node2149Labels = Sparse.eval nodeValue2149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2149) = mixedMoment B node2149 node2149Labels := rfl
  simpa [nodeValue2149, Sparse.eval] using hc.symm

theorem sound2167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2167 node2167Labels = Sparse.eval nodeValue2167 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2167) = mixedMoment B node2167 node2167Labels := rfl
  simpa [nodeValue2167, Sparse.eval] using hc.symm

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

theorem sound2258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2258 node2258Labels = Sparse.eval nodeValue2258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2258) = mixedMoment B node2258 node2258Labels := rfl
  simpa [nodeValue2258, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3237 node3237Labels = Sparse.eval nodeValue3237 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3237) = mixedMoment B node3237 node3237Labels := rfl
  simpa [nodeValue3237, Sparse.eval] using hc.symm

theorem sound3252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3252 node3252Labels = Sparse.eval nodeValue3252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3252) = mixedMoment B node3252 node3252Labels := rfl
  simpa [nodeValue3252, Sparse.eval] using hc.symm

theorem sound3262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3262 node3262Labels = Sparse.eval nodeValue3262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3262) = mixedMoment B node3262 node3262Labels := rfl
  simpa [nodeValue3262, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3268 node3268Labels = Sparse.eval nodeValue3268 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3268) = mixedMoment B node3268 node3268Labels := rfl
  simpa [nodeValue3268, Sparse.eval] using hc.symm

theorem sound3272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3272 node3272Labels = Sparse.eval nodeValue3272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3272) = mixedMoment B node3272 node3272Labels := rfl
  simpa [nodeValue3272, Sparse.eval] using hc.symm

theorem sound3275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3275 node3275Labels = Sparse.eval nodeValue3275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3275) = mixedMoment B node3275 node3275Labels := rfl
  simpa [nodeValue3275, Sparse.eval] using hc.symm

theorem sound3276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3276 node3276Labels = Sparse.eval nodeValue3276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3276) = mixedMoment B node3276 node3276Labels := rfl
  simpa [nodeValue3276, Sparse.eval] using hc.symm

theorem sound3277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3277 node3277Labels = Sparse.eval nodeValue3277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3277) = mixedMoment B node3277 node3277Labels := rfl
  simpa [nodeValue3277, Sparse.eval] using hc.symm

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

theorem sound4056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4056 node4056Labels = Sparse.eval nodeValue4056 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4056) = mixedMoment B node4056 node4056Labels := rfl
  simpa [nodeValue4056, Sparse.eval] using hc.symm

theorem sound4057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4057 node4057Labels = Sparse.eval nodeValue4057 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4057) = mixedMoment B node4057 node4057Labels := rfl
  simpa [nodeValue4057, Sparse.eval] using hc.symm

theorem sound4066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4066 node4066Labels = Sparse.eval nodeValue4066 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4066) = mixedMoment B node4066 node4066Labels := rfl
  simpa [nodeValue4066, Sparse.eval] using hc.symm

theorem sound4067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4067 node4067Labels = Sparse.eval nodeValue4067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4067) = mixedMoment B node4067 node4067Labels := rfl
  simpa [nodeValue4067, Sparse.eval] using hc.symm

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

theorem sourceEq2687 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2687 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2687 + difference 0 5) (sourceB2687 + difference 5 0) sourceC2687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1524) := by
    have ha : (tripleCharges (sourceA2687 + difference 0 5) (sourceB2687 + difference 5 0) sourceC2687) = raw37476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2687 sourceB2687 sourceC2687 difference raw37476; decide +kernel
    rw [ha]
    exact (canonical37476 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2687 + difference 1 5) (sourceB2687 + difference 5 1) sourceC2687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1501) := by
    have ha : (tripleCharges (sourceA2687 + difference 1 5) (sourceB2687 + difference 5 1) sourceC2687) = raw37477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2687 sourceB2687 sourceC2687 difference raw37477; decide +kernel
    rw [ha]
    exact (canonical37477 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2687 + difference 2 5) (sourceB2687 + difference 5 2) sourceC2687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2687 + difference 2 5) (sourceB2687 + difference 5 2) sourceC2687) = raw37478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2687 sourceB2687 sourceC2687 difference raw37478; decide +kernel
    rw [ha]
    exact (canonical37478 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2687 + difference 3 5) (sourceB2687 + difference 5 3) sourceC2687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2687 + difference 3 5) (sourceB2687 + difference 5 3) sourceC2687) = raw37479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2687 sourceB2687 sourceC2687 difference raw37479; decide +kernel
    rw [ha]
    exact (canonical37479 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2687 + difference 4 5) (sourceB2687 + difference 5 4) sourceC2687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2687 + difference 4 5) (sourceB2687 + difference 5 4) sourceC2687) = raw37480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2687 sourceB2687 sourceC2687 difference raw37480; decide +kernel
    rw [ha]
    exact (canonical37480 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2687 + difference 5 5) (sourceB2687 + difference 5 5) sourceC2687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1503) := by
    have ha : (tripleCharges (sourceA2687 + difference 5 5) (sourceB2687 + difference 5 5) sourceC2687) = raw37481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2687 sourceB2687 sourceC2687 difference raw37481; decide +kernel
    rw [ha]
    exact (canonical37481 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2687 + sourceB2687) sourceC2687) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2687 + sourceB2687) sourceC2687) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2687 sourceB2687 sourceC2687 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2687 sourceB2687 sourceC2687
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2687, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources84
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2688 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2688 + difference 0 4) (sourceB2688 + difference 4 0) sourceC2688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2688 + difference 0 4) (sourceB2688 + difference 4 0) sourceC2688) = raw37483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2688 sourceB2688 sourceC2688 difference raw37483; decide +kernel
    rw [ha]
    exact (canonical37483 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2688 + difference 1 4) (sourceB2688 + difference 4 1) sourceC2688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA2688 + difference 1 4) (sourceB2688 + difference 4 1) sourceC2688) = raw37484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2688 sourceB2688 sourceC2688 difference raw37484; decide +kernel
    rw [ha]
    exact (canonical37484 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2688 + difference 2 4) (sourceB2688 + difference 4 2) sourceC2688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2688 + difference 2 4) (sourceB2688 + difference 4 2) sourceC2688) = raw37485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2688 sourceB2688 sourceC2688 difference raw37485; decide +kernel
    rw [ha]
    exact (canonical37485 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2688 + difference 3 4) (sourceB2688 + difference 4 3) sourceC2688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2688 + difference 3 4) (sourceB2688 + difference 4 3) sourceC2688) = raw37486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2688 sourceB2688 sourceC2688 difference raw37486; decide +kernel
    rw [ha]
    exact (canonical37486 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2688 + difference 4 4) (sourceB2688 + difference 4 4) sourceC2688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA2688 + difference 4 4) (sourceB2688 + difference 4 4) sourceC2688) = raw37487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2688 sourceB2688 sourceC2688 difference raw37487; decide +kernel
    rw [ha]
    exact (canonical37487 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2688 + difference 5 4) (sourceB2688 + difference 4 5) sourceC2688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2688 + difference 5 4) (sourceB2688 + difference 4 5) sourceC2688) = raw37480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2688 sourceB2688 sourceC2688 difference raw37480; decide +kernel
    rw [ha]
    exact (canonical37480 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2688 + sourceB2688) sourceC2688) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2688 + sourceB2688) sourceC2688) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2688 sourceB2688 sourceC2688 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2688 sourceB2688 sourceC2688
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2688, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2689 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2689 + difference 0 4) (sourceB2689 + difference 4 0) sourceC2689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2689 + difference 0 4) (sourceB2689 + difference 4 0) sourceC2689) = raw37488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2689 sourceB2689 sourceC2689 difference raw37488; decide +kernel
    rw [ha]
    exact (canonical37488 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2689 + difference 1 4) (sourceB2689 + difference 4 1) sourceC2689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1510) := by
    have ha : (tripleCharges (sourceA2689 + difference 1 4) (sourceB2689 + difference 4 1) sourceC2689) = raw37489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2689 sourceB2689 sourceC2689 difference raw37489; decide +kernel
    rw [ha]
    exact (canonical37489 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2689 + difference 2 4) (sourceB2689 + difference 4 2) sourceC2689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1524) := by
    have ha : (tripleCharges (sourceA2689 + difference 2 4) (sourceB2689 + difference 4 2) sourceC2689) = raw37490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2689 sourceB2689 sourceC2689 difference raw37490; decide +kernel
    rw [ha]
    exact (canonical37490 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2689 + difference 3 4) (sourceB2689 + difference 4 3) sourceC2689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA2689 + difference 3 4) (sourceB2689 + difference 4 3) sourceC2689) = raw37491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2689 sourceB2689 sourceC2689 difference raw37491; decide +kernel
    rw [ha]
    exact (canonical37491 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2689 + difference 4 4) (sourceB2689 + difference 4 4) sourceC2689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA2689 + difference 4 4) (sourceB2689 + difference 4 4) sourceC2689) = raw37492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2689 sourceB2689 sourceC2689 difference raw37492; decide +kernel
    rw [ha]
    exact (canonical37492 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2689 + difference 5 4) (sourceB2689 + difference 4 5) sourceC2689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2689 + difference 5 4) (sourceB2689 + difference 4 5) sourceC2689) = raw37486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2689 sourceB2689 sourceC2689 difference raw37486; decide +kernel
    rw [ha]
    exact (canonical37486 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2689 + sourceB2689) sourceC2689) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2689 + sourceB2689) sourceC2689) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2689 sourceB2689 sourceC2689 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2689 sourceB2689 sourceC2689
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2689, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2691 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2691 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2691 + difference 5 0) (sourceB2691 + difference 0 5) sourceC2691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 687) := by
    have ha : (tripleCharges (sourceA2691 + difference 5 0) (sourceB2691 + difference 0 5) sourceC2691) = raw37497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2691 sourceB2691 sourceC2691 difference raw37497; decide +kernel
    rw [ha]
    exact (canonical37497 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2691 + difference 5 1) (sourceB2691 + difference 1 5) sourceC2691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1491) := by
    have ha : (tripleCharges (sourceA2691 + difference 5 1) (sourceB2691 + difference 1 5) sourceC2691) = raw37498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2691 sourceB2691 sourceC2691 difference raw37498; decide +kernel
    rw [ha]
    exact (canonical37498 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2691 + difference 5 2) (sourceB2691 + difference 2 5) sourceC2691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2691 + difference 5 2) (sourceB2691 + difference 2 5) sourceC2691) = raw37486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2691 sourceB2691 sourceC2691 difference raw37486; decide +kernel
    rw [ha]
    exact (canonical37486 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2691 + difference 5 3) (sourceB2691 + difference 3 5) sourceC2691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2691 + difference 5 3) (sourceB2691 + difference 3 5) sourceC2691) = raw37485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2691 sourceB2691 sourceC2691 difference raw37485; decide +kernel
    rw [ha]
    exact (canonical37485 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2691 + difference 5 4) (sourceB2691 + difference 4 5) sourceC2691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2691 + difference 5 4) (sourceB2691 + difference 4 5) sourceC2691) = raw37499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2691 sourceB2691 sourceC2691 difference raw37499; decide +kernel
    rw [ha]
    exact (canonical37499 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2691 + difference 5 5) (sourceB2691 + difference 5 5) sourceC2691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1524) := by
    have ha : (tripleCharges (sourceA2691 + difference 5 5) (sourceB2691 + difference 5 5) sourceC2691) = raw37490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2691 sourceB2691 sourceC2691 difference raw37490; decide +kernel
    rw [ha]
    exact (canonical37490 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2691 + sourceB2691) sourceC2691) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2691 + sourceB2691) sourceC2691) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2691 sourceB2691 sourceC2691 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2691 sourceB2691 sourceC2691
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2691, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2696 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2696 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2696 + difference 0 5) (sourceB2696 + difference 5 0) sourceC2696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2696 + difference 0 5) (sourceB2696 + difference 5 0) sourceC2696) = raw37513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2696 sourceB2696 sourceC2696 difference raw37513; decide +kernel
    rw [ha]
    exact (canonical37513 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2696 + difference 1 5) (sourceB2696 + difference 5 1) sourceC2696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2696 + difference 1 5) (sourceB2696 + difference 5 1) sourceC2696) = raw37514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2696 sourceB2696 sourceC2696 difference raw37514; decide +kernel
    rw [ha]
    exact (canonical37514 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2696 + difference 2 5) (sourceB2696 + difference 5 2) sourceC2696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2696 + difference 2 5) (sourceB2696 + difference 5 2) sourceC2696) = raw37515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2696 sourceB2696 sourceC2696 difference raw37515; decide +kernel
    rw [ha]
    exact (canonical37515 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2696 + difference 3 5) (sourceB2696 + difference 5 3) sourceC2696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2696 + difference 3 5) (sourceB2696 + difference 5 3) sourceC2696) = raw37516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2696 sourceB2696 sourceC2696 difference raw37516; decide +kernel
    rw [ha]
    exact (canonical37516 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2696 + difference 4 5) (sourceB2696 + difference 5 4) sourceC2696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1502) := by
    have ha : (tripleCharges (sourceA2696 + difference 4 5) (sourceB2696 + difference 5 4) sourceC2696) = raw37517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2696 sourceB2696 sourceC2696 difference raw37517; decide +kernel
    rw [ha]
    exact (canonical37517 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2696 + difference 5 5) (sourceB2696 + difference 5 5) sourceC2696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1502) := by
    have ha : (tripleCharges (sourceA2696 + difference 5 5) (sourceB2696 + difference 5 5) sourceC2696) = raw37518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2696 sourceB2696 sourceC2696 difference raw37518; decide +kernel
    rw [ha]
    exact (canonical37518 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2696 + sourceB2696) sourceC2696) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4056) := by
    have ha : (doubleCharges (sourceA2696 + sourceB2696) sourceC2696) = raw37519 := by
      apply Matrix.ext; unfold doubleCharges sourceA2696 sourceB2696 sourceC2696 raw37519; decide +kernel
    rw [ha]
    exact (canonical37519 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2696 sourceB2696 sourceC2696
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2696, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2697 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2697 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2697 + difference 5 0) (sourceB2697 + difference 0 5) sourceC2697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 666) := by
    have ha : (tripleCharges (sourceA2697 + difference 5 0) (sourceB2697 + difference 0 5) sourceC2697) = raw37520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2697 sourceB2697 sourceC2697 difference raw37520; decide +kernel
    rw [ha]
    exact (canonical37520 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2697 + difference 5 1) (sourceB2697 + difference 1 5) sourceC2697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2697 + difference 5 1) (sourceB2697 + difference 1 5) sourceC2697) = raw37521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2697 sourceB2697 sourceC2697 difference raw37521; decide +kernel
    rw [ha]
    exact (canonical37521 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2697 + difference 5 2) (sourceB2697 + difference 2 5) sourceC2697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2697 + difference 5 2) (sourceB2697 + difference 2 5) sourceC2697) = raw37522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2697 sourceB2697 sourceC2697 difference raw37522; decide +kernel
    rw [ha]
    exact (canonical37522 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2697 + difference 5 3) (sourceB2697 + difference 3 5) sourceC2697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2697 + difference 5 3) (sourceB2697 + difference 3 5) sourceC2697) = raw37523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2697 sourceB2697 sourceC2697 difference raw37523; decide +kernel
    rw [ha]
    exact (canonical37523 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2697 + difference 5 4) (sourceB2697 + difference 4 5) sourceC2697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2697 + difference 5 4) (sourceB2697 + difference 4 5) sourceC2697) = raw37524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2697 sourceB2697 sourceC2697 difference raw37524; decide +kernel
    rw [ha]
    exact (canonical37524 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2697 + difference 5 5) (sourceB2697 + difference 5 5) sourceC2697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1497) := by
    have ha : (tripleCharges (sourceA2697 + difference 5 5) (sourceB2697 + difference 5 5) sourceC2697) = raw37525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2697 sourceB2697 sourceC2697 difference raw37525; decide +kernel
    rw [ha]
    exact (canonical37525 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2697 + sourceB2697) sourceC2697) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4056) := by
    have ha : (doubleCharges (sourceA2697 + sourceB2697) sourceC2697) = raw37519 := by
      apply Matrix.ext; unfold doubleCharges sourceA2697 sourceB2697 sourceC2697 raw37519; decide +kernel
    rw [ha]
    exact (canonical37519 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2697 sourceB2697 sourceC2697
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2697, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2699 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2699 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2699 + difference 0 4) (sourceB2699 + difference 4 0) sourceC2699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA2699 + difference 0 4) (sourceB2699 + difference 4 0) sourceC2699) = raw37530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2699 sourceB2699 sourceC2699 difference raw37530; decide +kernel
    rw [ha]
    exact (canonical37530 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2699 + difference 1 4) (sourceB2699 + difference 4 1) sourceC2699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA2699 + difference 1 4) (sourceB2699 + difference 4 1) sourceC2699) = raw37531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2699 sourceB2699 sourceC2699 difference raw37531; decide +kernel
    rw [ha]
    exact (canonical37531 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2699 + difference 2 4) (sourceB2699 + difference 4 2) sourceC2699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1688) := by
    have ha : (tripleCharges (sourceA2699 + difference 2 4) (sourceB2699 + difference 4 2) sourceC2699) = raw37532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2699 sourceB2699 sourceC2699 difference raw37532; decide +kernel
    rw [ha]
    exact (canonical37532 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2699 + difference 3 4) (sourceB2699 + difference 4 3) sourceC2699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1688) := by
    have ha : (tripleCharges (sourceA2699 + difference 3 4) (sourceB2699 + difference 4 3) sourceC2699) = raw37533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2699 sourceB2699 sourceC2699 difference raw37533; decide +kernel
    rw [ha]
    exact (canonical37533 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2699 + difference 4 4) (sourceB2699 + difference 4 4) sourceC2699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA2699 + difference 4 4) (sourceB2699 + difference 4 4) sourceC2699) = raw37534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2699 sourceB2699 sourceC2699 difference raw37534; decide +kernel
    rw [ha]
    exact (canonical37534 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2699 + difference 5 4) (sourceB2699 + difference 4 5) sourceC2699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA2699 + difference 5 4) (sourceB2699 + difference 4 5) sourceC2699) = raw37535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2699 sourceB2699 sourceC2699 difference raw37535; decide +kernel
    rw [ha]
    exact (canonical37535 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2699 + sourceB2699) sourceC2699) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (doubleCharges (sourceA2699 + sourceB2699) sourceC2699) = raw37536 := by
      apply Matrix.ext; unfold doubleCharges sourceA2699 sourceB2699 sourceC2699 raw37536; decide +kernel
    rw [ha]
    exact (canonical37536 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2699 sourceB2699 sourceC2699
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2699, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2700 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2700 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2700 + difference 0 3) (sourceB2700 + difference 3 0) sourceC2700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA2700 + difference 0 3) (sourceB2700 + difference 3 0) sourceC2700) = raw37537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2700 sourceB2700 sourceC2700 difference raw37537; decide +kernel
    rw [ha]
    exact (canonical37537 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2700 + difference 1 3) (sourceB2700 + difference 3 1) sourceC2700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3275) := by
    have ha : (tripleCharges (sourceA2700 + difference 1 3) (sourceB2700 + difference 3 1) sourceC2700) = raw37538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2700 sourceB2700 sourceC2700 difference raw37538; decide +kernel
    rw [ha]
    exact (canonical37538 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2700 + difference 2 3) (sourceB2700 + difference 3 2) sourceC2700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3262) := by
    have ha : (tripleCharges (sourceA2700 + difference 2 3) (sourceB2700 + difference 3 2) sourceC2700) = raw37539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2700 sourceB2700 sourceC2700 difference raw37539; decide +kernel
    rw [ha]
    exact (canonical37539 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2700 + difference 3 3) (sourceB2700 + difference 3 3) sourceC2700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3262) := by
    have ha : (tripleCharges (sourceA2700 + difference 3 3) (sourceB2700 + difference 3 3) sourceC2700) = raw37540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2700 sourceB2700 sourceC2700 difference raw37540; decide +kernel
    rw [ha]
    exact (canonical37540 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2700 + difference 4 3) (sourceB2700 + difference 3 4) sourceC2700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3275) := by
    have ha : (tripleCharges (sourceA2700 + difference 4 3) (sourceB2700 + difference 3 4) sourceC2700) = raw37541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2700 sourceB2700 sourceC2700 difference raw37541; decide +kernel
    rw [ha]
    exact (canonical37541 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2700 + difference 5 3) (sourceB2700 + difference 3 5) sourceC2700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA2700 + difference 5 3) (sourceB2700 + difference 3 5) sourceC2700) = raw37542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2700 sourceB2700 sourceC2700 difference raw37542; decide +kernel
    rw [ha]
    exact (canonical37542 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2700 + sourceB2700) sourceC2700) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (doubleCharges (sourceA2700 + sourceB2700) sourceC2700) = raw37536 := by
      apply Matrix.ext; unfold doubleCharges sourceA2700 sourceB2700 sourceC2700 raw37536; decide +kernel
    rw [ha]
    exact (canonical37536 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2700 sourceB2700 sourceC2700
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2700, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2703 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2703 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2703 + difference 0 4) (sourceB2703 + difference 4 0) sourceC2703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2703 + difference 0 4) (sourceB2703 + difference 4 0) sourceC2703) = raw37552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2703 sourceB2703 sourceC2703 difference raw37552; decide +kernel
    rw [ha]
    exact (canonical37552 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2703 + difference 1 4) (sourceB2703 + difference 4 1) sourceC2703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1743) := by
    have ha : (tripleCharges (sourceA2703 + difference 1 4) (sourceB2703 + difference 4 1) sourceC2703) = raw37553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2703 sourceB2703 sourceC2703 difference raw37553; decide +kernel
    rw [ha]
    exact (canonical37553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2703 + difference 2 4) (sourceB2703 + difference 4 2) sourceC2703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1685) := by
    have ha : (tripleCharges (sourceA2703 + difference 2 4) (sourceB2703 + difference 4 2) sourceC2703) = raw37554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2703 sourceB2703 sourceC2703 difference raw37554; decide +kernel
    rw [ha]
    exact (canonical37554 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2703 + difference 3 4) (sourceB2703 + difference 4 3) sourceC2703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1685) := by
    have ha : (tripleCharges (sourceA2703 + difference 3 4) (sourceB2703 + difference 4 3) sourceC2703) = raw37555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2703 sourceB2703 sourceC2703 difference raw37555; decide +kernel
    rw [ha]
    exact (canonical37555 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2703 + difference 4 4) (sourceB2703 + difference 4 4) sourceC2703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1687) := by
    have ha : (tripleCharges (sourceA2703 + difference 4 4) (sourceB2703 + difference 4 4) sourceC2703) = raw37556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2703 sourceB2703 sourceC2703 difference raw37556; decide +kernel
    rw [ha]
    exact (canonical37556 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2703 + difference 5 4) (sourceB2703 + difference 4 5) sourceC2703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2703 + difference 5 4) (sourceB2703 + difference 4 5) sourceC2703) = raw37557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2703 sourceB2703 sourceC2703 difference raw37557; decide +kernel
    rw [ha]
    exact (canonical37557 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2703 + sourceB2703) sourceC2703) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2703 + sourceB2703) sourceC2703) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2703 sourceB2703 sourceC2703 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2703 sourceB2703 sourceC2703
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2703, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2704 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2704 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2704 + difference 0 3) (sourceB2704 + difference 3 0) sourceC2704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2704 + difference 0 3) (sourceB2704 + difference 3 0) sourceC2704) = raw37559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2704 sourceB2704 sourceC2704 difference raw37559; decide +kernel
    rw [ha]
    exact (canonical37559 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2704 + difference 1 3) (sourceB2704 + difference 3 1) sourceC2704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1735) := by
    have ha : (tripleCharges (sourceA2704 + difference 1 3) (sourceB2704 + difference 3 1) sourceC2704) = raw37560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2704 sourceB2704 sourceC2704 difference raw37560; decide +kernel
    rw [ha]
    exact (canonical37560 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2704 + difference 2 3) (sourceB2704 + difference 3 2) sourceC2704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA2704 + difference 2 3) (sourceB2704 + difference 3 2) sourceC2704) = raw37561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2704 sourceB2704 sourceC2704 difference raw37561; decide +kernel
    rw [ha]
    exact (canonical37561 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2704 + difference 3 3) (sourceB2704 + difference 3 3) sourceC2704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA2704 + difference 3 3) (sourceB2704 + difference 3 3) sourceC2704) = raw37562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2704 sourceB2704 sourceC2704 difference raw37562; decide +kernel
    rw [ha]
    exact (canonical37562 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2704 + difference 4 3) (sourceB2704 + difference 3 4) sourceC2704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2704 + difference 4 3) (sourceB2704 + difference 3 4) sourceC2704) = raw37563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2704 sourceB2704 sourceC2704 difference raw37563; decide +kernel
    rw [ha]
    exact (canonical37563 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2704 + difference 5 3) (sourceB2704 + difference 3 5) sourceC2704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2704 + difference 5 3) (sourceB2704 + difference 3 5) sourceC2704) = raw37564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2704 sourceB2704 sourceC2704 difference raw37564; decide +kernel
    rw [ha]
    exact (canonical37564 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2704 + sourceB2704) sourceC2704) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2704 + sourceB2704) sourceC2704) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2704 sourceB2704 sourceC2704 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2704 sourceB2704 sourceC2704
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2704, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2705 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2705 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2705 + difference 0 3) (sourceB2705 + difference 3 0) sourceC2705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2705 + difference 0 3) (sourceB2705 + difference 3 0) sourceC2705) = raw37565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2705 sourceB2705 sourceC2705 difference raw37565; decide +kernel
    rw [ha]
    exact (canonical37565 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2705 + difference 1 3) (sourceB2705 + difference 3 1) sourceC2705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA2705 + difference 1 3) (sourceB2705 + difference 3 1) sourceC2705) = raw37566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2705 sourceB2705 sourceC2705 difference raw37566; decide +kernel
    rw [ha]
    exact (canonical37566 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2705 + difference 2 3) (sourceB2705 + difference 3 2) sourceC2705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA2705 + difference 2 3) (sourceB2705 + difference 3 2) sourceC2705) = raw37567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2705 sourceB2705 sourceC2705 difference raw37567; decide +kernel
    rw [ha]
    exact (canonical37567 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2705 + difference 3 3) (sourceB2705 + difference 3 3) sourceC2705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA2705 + difference 3 3) (sourceB2705 + difference 3 3) sourceC2705) = raw37568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2705 sourceB2705 sourceC2705 difference raw37568; decide +kernel
    rw [ha]
    exact (canonical37568 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2705 + difference 4 3) (sourceB2705 + difference 3 4) sourceC2705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2705 + difference 4 3) (sourceB2705 + difference 3 4) sourceC2705) = raw37557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2705 sourceB2705 sourceC2705 difference raw37557; decide +kernel
    rw [ha]
    exact (canonical37557 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2705 + difference 5 3) (sourceB2705 + difference 3 5) sourceC2705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2705 + difference 5 3) (sourceB2705 + difference 3 5) sourceC2705) = raw37563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2705 sourceB2705 sourceC2705 difference raw37563; decide +kernel
    rw [ha]
    exact (canonical37563 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2705 + sourceB2705) sourceC2705) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2705 + sourceB2705) sourceC2705) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2705 sourceB2705 sourceC2705 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2705 sourceB2705 sourceC2705
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2705, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2706 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2706 + difference 0 4) (sourceB2706 + difference 4 0) sourceC2706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2706 + difference 0 4) (sourceB2706 + difference 4 0) sourceC2706) = raw37569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2706 sourceB2706 sourceC2706 difference raw37569; decide +kernel
    rw [ha]
    exact (canonical37569 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2706 + difference 1 4) (sourceB2706 + difference 4 1) sourceC2706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2706 + difference 1 4) (sourceB2706 + difference 4 1) sourceC2706) = raw37552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2706 sourceB2706 sourceC2706 difference raw37552; decide +kernel
    rw [ha]
    exact (canonical37552 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2706 + difference 2 4) (sourceB2706 + difference 4 2) sourceC2706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2149) := by
    have ha : (tripleCharges (sourceA2706 + difference 2 4) (sourceB2706 + difference 4 2) sourceC2706) = raw37570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2706 sourceB2706 sourceC2706 difference raw37570; decide +kernel
    rw [ha]
    exact (canonical37570 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2706 + difference 3 4) (sourceB2706 + difference 4 3) sourceC2706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2149) := by
    have ha : (tripleCharges (sourceA2706 + difference 3 4) (sourceB2706 + difference 4 3) sourceC2706) = raw37571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2706 sourceB2706 sourceC2706 difference raw37571; decide +kernel
    rw [ha]
    exact (canonical37571 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2706 + difference 4 4) (sourceB2706 + difference 4 4) sourceC2706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2258) := by
    have ha : (tripleCharges (sourceA2706 + difference 4 4) (sourceB2706 + difference 4 4) sourceC2706) = raw37572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2706 sourceB2706 sourceC2706 difference raw37572; decide +kernel
    rw [ha]
    exact (canonical37572 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2706 + difference 5 4) (sourceB2706 + difference 4 5) sourceC2706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2706 + difference 5 4) (sourceB2706 + difference 4 5) sourceC2706) = raw37573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2706 sourceB2706 sourceC2706 difference raw37573; decide +kernel
    rw [ha]
    exact (canonical37573 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2706 + sourceB2706) sourceC2706) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2706 + sourceB2706) sourceC2706) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2706 sourceB2706 sourceC2706 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2706 sourceB2706 sourceC2706
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2706, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2707 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2707 + difference 0 3) (sourceB2707 + difference 3 0) sourceC2707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2707 + difference 0 3) (sourceB2707 + difference 3 0) sourceC2707) = raw37574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2707 sourceB2707 sourceC2707 difference raw37574; decide +kernel
    rw [ha]
    exact (canonical37574 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2707 + difference 1 3) (sourceB2707 + difference 3 1) sourceC2707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2707 + difference 1 3) (sourceB2707 + difference 3 1) sourceC2707) = raw37559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2707 sourceB2707 sourceC2707 difference raw37559; decide +kernel
    rw [ha]
    exact (canonical37559 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2707 + difference 2 3) (sourceB2707 + difference 3 2) sourceC2707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA2707 + difference 2 3) (sourceB2707 + difference 3 2) sourceC2707) = raw37575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2707 sourceB2707 sourceC2707 difference raw37575; decide +kernel
    rw [ha]
    exact (canonical37575 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2707 + difference 3 3) (sourceB2707 + difference 3 3) sourceC2707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA2707 + difference 3 3) (sourceB2707 + difference 3 3) sourceC2707) = raw37576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2707 sourceB2707 sourceC2707 difference raw37576; decide +kernel
    rw [ha]
    exact (canonical37576 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2707 + difference 4 3) (sourceB2707 + difference 3 4) sourceC2707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2707 + difference 4 3) (sourceB2707 + difference 3 4) sourceC2707) = raw37577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2707 sourceB2707 sourceC2707 difference raw37577; decide +kernel
    rw [ha]
    exact (canonical37577 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2707 + difference 5 3) (sourceB2707 + difference 3 5) sourceC2707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2707 + difference 5 3) (sourceB2707 + difference 3 5) sourceC2707) = raw37578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2707 sourceB2707 sourceC2707 difference raw37578; decide +kernel
    rw [ha]
    exact (canonical37578 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2707 + sourceB2707) sourceC2707) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2707 + sourceB2707) sourceC2707) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2707 sourceB2707 sourceC2707 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2707 sourceB2707 sourceC2707
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2707, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2708 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2708 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2708 + difference 0 3) (sourceB2708 + difference 3 0) sourceC2708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2708 + difference 0 3) (sourceB2708 + difference 3 0) sourceC2708) = raw37579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2708 sourceB2708 sourceC2708 difference raw37579; decide +kernel
    rw [ha]
    exact (canonical37579 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2708 + difference 1 3) (sourceB2708 + difference 3 1) sourceC2708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2708 + difference 1 3) (sourceB2708 + difference 3 1) sourceC2708) = raw37565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2708 sourceB2708 sourceC2708 difference raw37565; decide +kernel
    rw [ha]
    exact (canonical37565 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2708 + difference 2 3) (sourceB2708 + difference 3 2) sourceC2708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA2708 + difference 2 3) (sourceB2708 + difference 3 2) sourceC2708) = raw37580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2708 sourceB2708 sourceC2708 difference raw37580; decide +kernel
    rw [ha]
    exact (canonical37580 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2708 + difference 3 3) (sourceB2708 + difference 3 3) sourceC2708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA2708 + difference 3 3) (sourceB2708 + difference 3 3) sourceC2708) = raw37581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2708 sourceB2708 sourceC2708 difference raw37581; decide +kernel
    rw [ha]
    exact (canonical37581 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2708 + difference 4 3) (sourceB2708 + difference 3 4) sourceC2708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2708 + difference 4 3) (sourceB2708 + difference 3 4) sourceC2708) = raw37573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2708 sourceB2708 sourceC2708 difference raw37573; decide +kernel
    rw [ha]
    exact (canonical37573 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2708 + difference 5 3) (sourceB2708 + difference 3 5) sourceC2708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2708 + difference 5 3) (sourceB2708 + difference 3 5) sourceC2708) = raw37577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2708 sourceB2708 sourceC2708 difference raw37577; decide +kernel
    rw [ha]
    exact (canonical37577 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2708 + sourceB2708) sourceC2708) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2708 + sourceB2708) sourceC2708) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2708 sourceB2708 sourceC2708 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2708 sourceB2708 sourceC2708
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2708, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2710 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2710 + difference 5 0) (sourceB2710 + difference 0 5) sourceC2710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1579) := by
    have ha : (tripleCharges (sourceA2710 + difference 5 0) (sourceB2710 + difference 0 5) sourceC2710) = raw37585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2710 sourceB2710 sourceC2710 difference raw37585; decide +kernel
    rw [ha]
    exact (canonical37585 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2710 + difference 5 1) (sourceB2710 + difference 1 5) sourceC2710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3237) := by
    have ha : (tripleCharges (sourceA2710 + difference 5 1) (sourceB2710 + difference 1 5) sourceC2710) = raw37586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2710 sourceB2710 sourceC2710 difference raw37586; decide +kernel
    rw [ha]
    exact (canonical37586 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2710 + difference 5 2) (sourceB2710 + difference 2 5) sourceC2710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3252) := by
    have ha : (tripleCharges (sourceA2710 + difference 5 2) (sourceB2710 + difference 2 5) sourceC2710) = raw37587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2710 sourceB2710 sourceC2710 difference raw37587; decide +kernel
    rw [ha]
    exact (canonical37587 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2710 + difference 5 3) (sourceB2710 + difference 3 5) sourceC2710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3252) := by
    have ha : (tripleCharges (sourceA2710 + difference 5 3) (sourceB2710 + difference 3 5) sourceC2710) = raw37588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2710 sourceB2710 sourceC2710 difference raw37588; decide +kernel
    rw [ha]
    exact (canonical37588 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2710 + difference 5 4) (sourceB2710 + difference 4 5) sourceC2710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2710 + difference 5 4) (sourceB2710 + difference 4 5) sourceC2710) = raw37577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2710 sourceB2710 sourceC2710 difference raw37577; decide +kernel
    rw [ha]
    exact (canonical37577 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2710 + difference 5 5) (sourceB2710 + difference 5 5) sourceC2710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2710 + difference 5 5) (sourceB2710 + difference 5 5) sourceC2710) = raw37573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2710 sourceB2710 sourceC2710 difference raw37573; decide +kernel
    rw [ha]
    exact (canonical37573 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2710 + sourceB2710) sourceC2710) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2710 + sourceB2710) sourceC2710) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2710 sourceB2710 sourceC2710 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2710 sourceB2710 sourceC2710
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2710, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2712 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2712 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2712 + difference 5 0) (sourceB2712 + difference 0 5) sourceC2712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1576) := by
    have ha : (tripleCharges (sourceA2712 + difference 5 0) (sourceB2712 + difference 0 5) sourceC2712) = raw37591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2712 sourceB2712 sourceC2712 difference raw37591; decide +kernel
    rw [ha]
    exact (canonical37591 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2712 + difference 5 1) (sourceB2712 + difference 1 5) sourceC2712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1858) := by
    have ha : (tripleCharges (sourceA2712 + difference 5 1) (sourceB2712 + difference 1 5) sourceC2712) = raw37592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2712 sourceB2712 sourceC2712 difference raw37592; decide +kernel
    rw [ha]
    exact (canonical37592 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2712 + difference 5 2) (sourceB2712 + difference 2 5) sourceC2712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1849) := by
    have ha : (tripleCharges (sourceA2712 + difference 5 2) (sourceB2712 + difference 2 5) sourceC2712) = raw37593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2712 sourceB2712 sourceC2712 difference raw37593; decide +kernel
    rw [ha]
    exact (canonical37593 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2712 + difference 5 3) (sourceB2712 + difference 3 5) sourceC2712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1849) := by
    have ha : (tripleCharges (sourceA2712 + difference 5 3) (sourceB2712 + difference 3 5) sourceC2712) = raw37594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2712 sourceB2712 sourceC2712 difference raw37594; decide +kernel
    rw [ha]
    exact (canonical37594 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2712 + difference 5 4) (sourceB2712 + difference 4 5) sourceC2712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2712 + difference 5 4) (sourceB2712 + difference 4 5) sourceC2712) = raw37578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2712 sourceB2712 sourceC2712 difference raw37578; decide +kernel
    rw [ha]
    exact (canonical37578 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2712 + difference 5 5) (sourceB2712 + difference 5 5) sourceC2712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2712 + difference 5 5) (sourceB2712 + difference 5 5) sourceC2712) = raw37577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2712 sourceB2712 sourceC2712 difference raw37577; decide +kernel
    rw [ha]
    exact (canonical37577 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2712 + sourceB2712) sourceC2712) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2712 + sourceB2712) sourceC2712) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2712 sourceB2712 sourceC2712 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2712 sourceB2712 sourceC2712
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2712, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2128 : Integer.Sparse.reindex keyMap MixedData.row2128 = numericRow2128 := by decide +kernel

theorem numericCheck2128 (x : Master → ℝ) : Integer.Sparse.eval numericRow2128 x =
    (1 : ℝ) * reducedSource2128 x := by
  norm_num [numericRow2128, reducedSource2128, Integer.Sparse.eval, Sparse.eval, nodeValue1501, nodeValue1503, nodeValue1507, nodeValue1524, nodeValue4057]

theorem reindexCheck2129 : Integer.Sparse.reindex keyMap MixedData.row2129 = numericRow2129 := by decide +kernel

theorem numericCheck2129 (x : Master → ℝ) : Integer.Sparse.eval numericRow2129 x =
    (1 : ℝ) * reducedSource2129 x := by
  norm_num [numericRow2129, reducedSource2129, Integer.Sparse.eval, Sparse.eval, nodeValue1504, nodeValue1507, nodeValue1508, nodeValue1517, nodeValue4057]

theorem reindexCheck2130 : Integer.Sparse.reindex keyMap MixedData.row2130 = numericRow2130 := by decide +kernel

theorem numericCheck2130 (x : Master → ℝ) : Integer.Sparse.eval numericRow2130 x =
    (1 : ℝ) * reducedSource2130 x := by
  norm_num [numericRow2130, reducedSource2130, Integer.Sparse.eval, Sparse.eval, nodeValue1507, nodeValue1510, nodeValue1512, nodeValue1517, nodeValue1524, nodeValue4057]

theorem reindexCheck2131 : Integer.Sparse.reindex keyMap MixedData.row2131 = numericRow2131 := by decide +kernel

theorem numericCheck2131 (x : Master → ℝ) : Integer.Sparse.eval numericRow2131 x =
    (1 : ℝ) * reducedSource2131 x := by
  norm_num [numericRow2131, reducedSource2131, Integer.Sparse.eval, Sparse.eval, nodeValue687, nodeValue1491, nodeValue1517, nodeValue1524, nodeValue4057]

theorem reindexCheck2132 : Integer.Sparse.reindex keyMap MixedData.row2132 = numericRow2132 := by decide +kernel

theorem numericCheck2132 (x : Master → ℝ) : Integer.Sparse.eval numericRow2132 x =
    (1 : ℝ) * reducedSource2132 x := by
  norm_num [numericRow2132, reducedSource2132, Integer.Sparse.eval, Sparse.eval, nodeValue1502, nodeValue1506, nodeValue4056]

theorem reindexCheck2133 : Integer.Sparse.reindex keyMap MixedData.row2133 = numericRow2133 := by decide +kernel

theorem numericCheck2133 (x : Master → ℝ) : Integer.Sparse.eval numericRow2133 x =
    (1 : ℝ) * reducedSource2133 x := by
  norm_num [numericRow2133, reducedSource2133, Integer.Sparse.eval, Sparse.eval, nodeValue666, nodeValue1497, nodeValue1506, nodeValue4056]

theorem reindexCheck2134 : Integer.Sparse.reindex keyMap MixedData.row2134 = numericRow2134 := by decide +kernel

theorem numericCheck2134 (x : Master → ℝ) : Integer.Sparse.eval numericRow2134 x =
    (1 : ℝ) * reducedSource2134 x := by
  norm_num [numericRow2134, reducedSource2134, Integer.Sparse.eval, Sparse.eval, nodeValue1688, nodeValue1692, nodeValue1695, nodeValue4066]

theorem reindexCheck2135 : Integer.Sparse.reindex keyMap MixedData.row2135 = numericRow2135 := by decide +kernel

theorem numericCheck2135 (x : Master → ℝ) : Integer.Sparse.eval numericRow2135 x =
    (1 : ℝ) * reducedSource2135 x := by
  norm_num [numericRow2135, reducedSource2135, Integer.Sparse.eval, Sparse.eval, nodeValue1692, nodeValue3262, nodeValue3275, nodeValue4066]

theorem reindexCheck2136 : Integer.Sparse.reindex keyMap MixedData.row2136 = numericRow2136 := by decide +kernel

theorem numericCheck2136 (x : Master → ℝ) : Integer.Sparse.eval numericRow2136 x =
    (1 : ℝ) * reducedSource2136 x := by
  norm_num [numericRow2136, reducedSource2136, Integer.Sparse.eval, Sparse.eval, nodeValue1685, nodeValue1687, nodeValue1694, nodeValue1743, nodeValue2167, nodeValue4067]

theorem reindexCheck2137 : Integer.Sparse.reindex keyMap MixedData.row2137 = numericRow2137 := by decide +kernel

theorem numericCheck2137 (x : Master → ℝ) : Integer.Sparse.eval numericRow2137 x =
    (1 : ℝ) * reducedSource2137 x := by
  norm_num [numericRow2137, reducedSource2137, Integer.Sparse.eval, Sparse.eval, nodeValue1679, nodeValue1683, nodeValue1693, nodeValue1735, nodeValue3277, nodeValue4067]

theorem reindexCheck2138 : Integer.Sparse.reindex keyMap MixedData.row2138 = numericRow2138 := by decide +kernel

theorem numericCheck2138 (x : Master → ℝ) : Integer.Sparse.eval numericRow2138 x =
    (1 : ℝ) * reducedSource2138 x := by
  norm_num [numericRow2138, reducedSource2138, Integer.Sparse.eval, Sparse.eval, nodeValue1689, nodeValue1693, nodeValue1694, nodeValue1748, nodeValue3276, nodeValue4067]

theorem reindexCheck2139 : Integer.Sparse.reindex keyMap MixedData.row2139 = numericRow2139 := by decide +kernel

theorem numericCheck2139 (x : Master → ℝ) : Integer.Sparse.eval numericRow2139 x =
    (1 : ℝ) * reducedSource2139 x := by
  norm_num [numericRow2139, reducedSource2139, Integer.Sparse.eval, Sparse.eval, nodeValue1683, nodeValue2149, nodeValue2167, nodeValue2258, nodeValue3277, nodeValue4067]

theorem reindexCheck2140 : Integer.Sparse.reindex keyMap MixedData.row2140 = numericRow2140 := by decide +kernel

theorem numericCheck2140 (x : Master → ℝ) : Integer.Sparse.eval numericRow2140 x =
    (1 : ℝ) * reducedSource2140 x := by
  norm_num [numericRow2140, reducedSource2140, Integer.Sparse.eval, Sparse.eval, nodeValue1694, nodeValue2167, nodeValue3268, nodeValue3276, nodeValue3277, nodeValue4067]

theorem reindexCheck2141 : Integer.Sparse.reindex keyMap MixedData.row2141 = numericRow2141 := by decide +kernel

theorem numericCheck2141 (x : Master → ℝ) : Integer.Sparse.eval numericRow2141 x =
    (1 : ℝ) * reducedSource2141 x := by
  norm_num [numericRow2141, reducedSource2141, Integer.Sparse.eval, Sparse.eval, nodeValue1693, nodeValue3272, nodeValue3276, nodeValue3277, nodeValue4067]

theorem reindexCheck2142 : Integer.Sparse.reindex keyMap MixedData.row2142 = numericRow2142 := by decide +kernel

theorem numericCheck2142 (x : Master → ℝ) : Integer.Sparse.eval numericRow2142 x =
    (1 : ℝ) * reducedSource2142 x := by
  norm_num [numericRow2142, reducedSource2142, Integer.Sparse.eval, Sparse.eval, nodeValue1579, nodeValue3237, nodeValue3252, nodeValue3276, nodeValue3277, nodeValue4067]

theorem reindexCheck2143 : Integer.Sparse.reindex keyMap MixedData.row2143 = numericRow2143 := by decide +kernel

theorem numericCheck2143 (x : Master → ℝ) : Integer.Sparse.eval numericRow2143 x =
    (1 : ℝ) * reducedSource2143 x := by
  norm_num [numericRow2143, reducedSource2143, Integer.Sparse.eval, Sparse.eval, nodeValue1576, nodeValue1849, nodeValue1858, nodeValue2167, nodeValue3276, nodeValue4067]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2128 (mixedVector B) = 0 := by
  have h1501 : mixedVector B (Sum.inr 1501) = Sparse.eval nodeValue1501 (mixedVector B) := by
    change mixedMoment B node1501 node1501Labels = _
    exact sound1501 B hB hF
  have h1503 : mixedVector B (Sum.inr 1503) = Sparse.eval nodeValue1503 (mixedVector B) := by
    change mixedMoment B node1503 node1503Labels = _
    exact sound1503 B hB hF
  have h1507 : mixedVector B (Sum.inr 1507) = Sparse.eval nodeValue1507 (mixedVector B) := by
    change mixedMoment B node1507 node1507Labels = _
    exact sound1507 B hB hF
  have h1524 : mixedVector B (Sum.inr 1524) = Sparse.eval nodeValue1524 (mixedVector B) := by
    change mixedMoment B node1524 node1524Labels = _
    exact sound1524 B hB hF
  have h4057 : mixedVector B (Sum.inr 4057) = Sparse.eval nodeValue4057 (mixedVector B) := by
    change mixedMoment B node4057 node4057Labels = _
    exact sound4057 B hB hF
  simpa only [sourceForm2687, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1501, h1503, h1507, h1524, h4057, reducedSource2128] using sourceEq2687 B hB

theorem rowSound2128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2128 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2128, numericCheck2128, reducedZero2128 B hB hF, mul_zero]

theorem reducedZero2129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2129 (mixedVector B) = 0 := by
  have h1504 : mixedVector B (Sum.inr 1504) = Sparse.eval nodeValue1504 (mixedVector B) := by
    change mixedMoment B node1504 node1504Labels = _
    exact sound1504 B hB hF
  have h1507 : mixedVector B (Sum.inr 1507) = Sparse.eval nodeValue1507 (mixedVector B) := by
    change mixedMoment B node1507 node1507Labels = _
    exact sound1507 B hB hF
  have h1508 : mixedVector B (Sum.inr 1508) = Sparse.eval nodeValue1508 (mixedVector B) := by
    change mixedMoment B node1508 node1508Labels = _
    exact sound1508 B hB hF
  have h1517 : mixedVector B (Sum.inr 1517) = Sparse.eval nodeValue1517 (mixedVector B) := by
    change mixedMoment B node1517 node1517Labels = _
    exact sound1517 B hB hF
  have h4057 : mixedVector B (Sum.inr 4057) = Sparse.eval nodeValue4057 (mixedVector B) := by
    change mixedMoment B node4057 node4057Labels = _
    exact sound4057 B hB hF
  simpa only [sourceForm2688, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1504, h1507, h1508, h1517, h4057, reducedSource2129] using sourceEq2688 B hB

theorem rowSound2129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2129 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2129, numericCheck2129, reducedZero2129 B hB hF, mul_zero]

theorem reducedZero2130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2130 (mixedVector B) = 0 := by
  have h1507 : mixedVector B (Sum.inr 1507) = Sparse.eval nodeValue1507 (mixedVector B) := by
    change mixedMoment B node1507 node1507Labels = _
    exact sound1507 B hB hF
  have h1510 : mixedVector B (Sum.inr 1510) = Sparse.eval nodeValue1510 (mixedVector B) := by
    change mixedMoment B node1510 node1510Labels = _
    exact sound1510 B hB hF
  have h1512 : mixedVector B (Sum.inr 1512) = Sparse.eval nodeValue1512 (mixedVector B) := by
    change mixedMoment B node1512 node1512Labels = _
    exact sound1512 B hB hF
  have h1517 : mixedVector B (Sum.inr 1517) = Sparse.eval nodeValue1517 (mixedVector B) := by
    change mixedMoment B node1517 node1517Labels = _
    exact sound1517 B hB hF
  have h1524 : mixedVector B (Sum.inr 1524) = Sparse.eval nodeValue1524 (mixedVector B) := by
    change mixedMoment B node1524 node1524Labels = _
    exact sound1524 B hB hF
  have h4057 : mixedVector B (Sum.inr 4057) = Sparse.eval nodeValue4057 (mixedVector B) := by
    change mixedMoment B node4057 node4057Labels = _
    exact sound4057 B hB hF
  simpa only [sourceForm2689, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1507, h1510, h1512, h1517, h1524, h4057, reducedSource2130] using sourceEq2689 B hB

theorem rowSound2130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2130 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2130, numericCheck2130, reducedZero2130 B hB hF, mul_zero]

theorem reducedZero2131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2131 (mixedVector B) = 0 := by
  have h687 : mixedVector B (Sum.inr 687) = Sparse.eval nodeValue687 (mixedVector B) := by
    change mixedMoment B node687 node687Labels = _
    exact sound687 B hB hF
  have h1491 : mixedVector B (Sum.inr 1491) = Sparse.eval nodeValue1491 (mixedVector B) := by
    change mixedMoment B node1491 node1491Labels = _
    exact sound1491 B hB hF
  have h1517 : mixedVector B (Sum.inr 1517) = Sparse.eval nodeValue1517 (mixedVector B) := by
    change mixedMoment B node1517 node1517Labels = _
    exact sound1517 B hB hF
  have h1524 : mixedVector B (Sum.inr 1524) = Sparse.eval nodeValue1524 (mixedVector B) := by
    change mixedMoment B node1524 node1524Labels = _
    exact sound1524 B hB hF
  have h4057 : mixedVector B (Sum.inr 4057) = Sparse.eval nodeValue4057 (mixedVector B) := by
    change mixedMoment B node4057 node4057Labels = _
    exact sound4057 B hB hF
  simpa only [sourceForm2691, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h687, h1491, h1517, h1524, h4057, reducedSource2131] using sourceEq2691 B hB

theorem rowSound2131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2131 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2131, numericCheck2131, reducedZero2131 B hB hF, mul_zero]

theorem reducedZero2132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2132 (mixedVector B) = 0 := by
  have h1502 : mixedVector B (Sum.inr 1502) = Sparse.eval nodeValue1502 (mixedVector B) := by
    change mixedMoment B node1502 node1502Labels = _
    exact sound1502 B hB hF
  have h1506 : mixedVector B (Sum.inr 1506) = Sparse.eval nodeValue1506 (mixedVector B) := by
    change mixedMoment B node1506 node1506Labels = _
    exact sound1506 B hB hF
  have h4056 : mixedVector B (Sum.inr 4056) = Sparse.eval nodeValue4056 (mixedVector B) := by
    change mixedMoment B node4056 node4056Labels = _
    exact sound4056 B hB hF
  simpa only [sourceForm2696, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1502, h1506, h4056, reducedSource2132] using sourceEq2696 B hB

theorem rowSound2132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2132 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2132, numericCheck2132, reducedZero2132 B hB hF, mul_zero]

theorem reducedZero2133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2133 (mixedVector B) = 0 := by
  have h666 : mixedVector B (Sum.inr 666) = Sparse.eval nodeValue666 (mixedVector B) := by
    change mixedMoment B node666 node666Labels = _
    exact sound666 B hB hF
  have h1497 : mixedVector B (Sum.inr 1497) = Sparse.eval nodeValue1497 (mixedVector B) := by
    change mixedMoment B node1497 node1497Labels = _
    exact sound1497 B hB hF
  have h1506 : mixedVector B (Sum.inr 1506) = Sparse.eval nodeValue1506 (mixedVector B) := by
    change mixedMoment B node1506 node1506Labels = _
    exact sound1506 B hB hF
  have h4056 : mixedVector B (Sum.inr 4056) = Sparse.eval nodeValue4056 (mixedVector B) := by
    change mixedMoment B node4056 node4056Labels = _
    exact sound4056 B hB hF
  simpa only [sourceForm2697, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h666, h1497, h1506, h4056, reducedSource2133] using sourceEq2697 B hB

theorem rowSound2133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2133 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2133, numericCheck2133, reducedZero2133 B hB hF, mul_zero]

theorem reducedZero2134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2134 (mixedVector B) = 0 := by
  have h1688 : mixedVector B (Sum.inr 1688) = Sparse.eval nodeValue1688 (mixedVector B) := by
    change mixedMoment B node1688 node1688Labels = _
    exact sound1688 B hB hF
  have h1692 : mixedVector B (Sum.inr 1692) = Sparse.eval nodeValue1692 (mixedVector B) := by
    change mixedMoment B node1692 node1692Labels = _
    exact sound1692 B hB hF
  have h1695 : mixedVector B (Sum.inr 1695) = Sparse.eval nodeValue1695 (mixedVector B) := by
    change mixedMoment B node1695 node1695Labels = _
    exact sound1695 B hB hF
  have h4066 : mixedVector B (Sum.inr 4066) = Sparse.eval nodeValue4066 (mixedVector B) := by
    change mixedMoment B node4066 node4066Labels = _
    exact sound4066 B hB hF
  simpa only [sourceForm2699, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1688, h1692, h1695, h4066, reducedSource2134] using sourceEq2699 B hB

theorem rowSound2134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2134 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2134, numericCheck2134, reducedZero2134 B hB hF, mul_zero]

theorem reducedZero2135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2135 (mixedVector B) = 0 := by
  have h1692 : mixedVector B (Sum.inr 1692) = Sparse.eval nodeValue1692 (mixedVector B) := by
    change mixedMoment B node1692 node1692Labels = _
    exact sound1692 B hB hF
  have h3262 : mixedVector B (Sum.inr 3262) = Sparse.eval nodeValue3262 (mixedVector B) := by
    change mixedMoment B node3262 node3262Labels = _
    exact sound3262 B hB hF
  have h3275 : mixedVector B (Sum.inr 3275) = Sparse.eval nodeValue3275 (mixedVector B) := by
    change mixedMoment B node3275 node3275Labels = _
    exact sound3275 B hB hF
  have h4066 : mixedVector B (Sum.inr 4066) = Sparse.eval nodeValue4066 (mixedVector B) := by
    change mixedMoment B node4066 node4066Labels = _
    exact sound4066 B hB hF
  simpa only [sourceForm2700, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1692, h3262, h3275, h4066, reducedSource2135] using sourceEq2700 B hB

theorem rowSound2135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2135 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2135, numericCheck2135, reducedZero2135 B hB hF, mul_zero]

theorem reducedZero2136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2136 (mixedVector B) = 0 := by
  have h1685 : mixedVector B (Sum.inr 1685) = Sparse.eval nodeValue1685 (mixedVector B) := by
    change mixedMoment B node1685 node1685Labels = _
    exact sound1685 B hB hF
  have h1687 : mixedVector B (Sum.inr 1687) = Sparse.eval nodeValue1687 (mixedVector B) := by
    change mixedMoment B node1687 node1687Labels = _
    exact sound1687 B hB hF
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h1743 : mixedVector B (Sum.inr 1743) = Sparse.eval nodeValue1743 (mixedVector B) := by
    change mixedMoment B node1743 node1743Labels = _
    exact sound1743 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2703, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1685, h1687, h1694, h1743, h2167, h4067, reducedSource2136] using sourceEq2703 B hB

theorem rowSound2136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2136 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2136, numericCheck2136, reducedZero2136 B hB hF, mul_zero]

theorem reducedZero2137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2137 (mixedVector B) = 0 := by
  have h1679 : mixedVector B (Sum.inr 1679) = Sparse.eval nodeValue1679 (mixedVector B) := by
    change mixedMoment B node1679 node1679Labels = _
    exact sound1679 B hB hF
  have h1683 : mixedVector B (Sum.inr 1683) = Sparse.eval nodeValue1683 (mixedVector B) := by
    change mixedMoment B node1683 node1683Labels = _
    exact sound1683 B hB hF
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h1735 : mixedVector B (Sum.inr 1735) = Sparse.eval nodeValue1735 (mixedVector B) := by
    change mixedMoment B node1735 node1735Labels = _
    exact sound1735 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2704, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1679, h1683, h1693, h1735, h3277, h4067, reducedSource2137] using sourceEq2704 B hB

theorem rowSound2137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2137 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2137, numericCheck2137, reducedZero2137 B hB hF, mul_zero]

theorem reducedZero2138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2138 (mixedVector B) = 0 := by
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2705, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1689, h1693, h1694, h1748, h3276, h4067, reducedSource2138] using sourceEq2705 B hB

theorem rowSound2138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2138 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2138, numericCheck2138, reducedZero2138 B hB hF, mul_zero]

theorem reducedZero2139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2139 (mixedVector B) = 0 := by
  have h1683 : mixedVector B (Sum.inr 1683) = Sparse.eval nodeValue1683 (mixedVector B) := by
    change mixedMoment B node1683 node1683Labels = _
    exact sound1683 B hB hF
  have h2149 : mixedVector B (Sum.inr 2149) = Sparse.eval nodeValue2149 (mixedVector B) := by
    change mixedMoment B node2149 node2149Labels = _
    exact sound2149 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h2258 : mixedVector B (Sum.inr 2258) = Sparse.eval nodeValue2258 (mixedVector B) := by
    change mixedMoment B node2258 node2258Labels = _
    exact sound2258 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2706, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1683, h2149, h2167, h2258, h3277, h4067, reducedSource2139] using sourceEq2706 B hB

theorem rowSound2139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2139 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2139, numericCheck2139, reducedZero2139 B hB hF, mul_zero]

theorem reducedZero2140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2140 (mixedVector B) = 0 := by
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h3268 : mixedVector B (Sum.inr 3268) = Sparse.eval nodeValue3268 (mixedVector B) := by
    change mixedMoment B node3268 node3268Labels = _
    exact sound3268 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2707, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1694, h2167, h3268, h3276, h3277, h4067, reducedSource2140] using sourceEq2707 B hB

theorem rowSound2140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2140 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2140, numericCheck2140, reducedZero2140 B hB hF, mul_zero]

theorem reducedZero2141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2141 (mixedVector B) = 0 := by
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h3272 : mixedVector B (Sum.inr 3272) = Sparse.eval nodeValue3272 (mixedVector B) := by
    change mixedMoment B node3272 node3272Labels = _
    exact sound3272 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2708, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1693, h3272, h3276, h3277, h4067, reducedSource2141] using sourceEq2708 B hB

theorem rowSound2141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2141 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2141, numericCheck2141, reducedZero2141 B hB hF, mul_zero]

theorem reducedZero2142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2142 (mixedVector B) = 0 := by
  have h1579 : mixedVector B (Sum.inr 1579) = Sparse.eval nodeValue1579 (mixedVector B) := by
    change mixedMoment B node1579 node1579Labels = _
    exact sound1579 B hB hF
  have h3237 : mixedVector B (Sum.inr 3237) = Sparse.eval nodeValue3237 (mixedVector B) := by
    change mixedMoment B node3237 node3237Labels = _
    exact sound3237 B hB hF
  have h3252 : mixedVector B (Sum.inr 3252) = Sparse.eval nodeValue3252 (mixedVector B) := by
    change mixedMoment B node3252 node3252Labels = _
    exact sound3252 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2710, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1579, h3237, h3252, h3276, h3277, h4067, reducedSource2142] using sourceEq2710 B hB

theorem rowSound2142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2142 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2142, numericCheck2142, reducedZero2142 B hB hF, mul_zero]

theorem reducedZero2143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2143 (mixedVector B) = 0 := by
  have h1576 : mixedVector B (Sum.inr 1576) = Sparse.eval nodeValue1576 (mixedVector B) := by
    change mixedMoment B node1576 node1576Labels = _
    exact sound1576 B hB hF
  have h1849 : mixedVector B (Sum.inr 1849) = Sparse.eval nodeValue1849 (mixedVector B) := by
    change mixedMoment B node1849 node1849Labels = _
    exact sound1849 B hB hF
  have h1858 : mixedVector B (Sum.inr 1858) = Sparse.eval nodeValue1858 (mixedVector B) := by
    change mixedMoment B node1858 node1858Labels = _
    exact sound1858 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2712, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1576, h1849, h1858, h2167, h3276, h4067, reducedSource2143] using sourceEq2712 B hB

theorem rowSound2143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2143 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2143, numericCheck2143, reducedZero2143 B hB hF, mul_zero]

theorem sourceRowsAt2128 : MixedData.sourceRows (2128 : Fin 2425) =
    MixedData.row2128 := by decide +kernel

theorem sourceRowsAt2129 : MixedData.sourceRows (2129 : Fin 2425) =
    MixedData.row2129 := by decide +kernel

theorem sourceRowsAt2130 : MixedData.sourceRows (2130 : Fin 2425) =
    MixedData.row2130 := by decide +kernel

theorem sourceRowsAt2131 : MixedData.sourceRows (2131 : Fin 2425) =
    MixedData.row2131 := by decide +kernel

theorem sourceRowsAt2132 : MixedData.sourceRows (2132 : Fin 2425) =
    MixedData.row2132 := by decide +kernel

theorem sourceRowsAt2133 : MixedData.sourceRows (2133 : Fin 2425) =
    MixedData.row2133 := by decide +kernel

theorem sourceRowsAt2134 : MixedData.sourceRows (2134 : Fin 2425) =
    MixedData.row2134 := by decide +kernel

theorem sourceRowsAt2135 : MixedData.sourceRows (2135 : Fin 2425) =
    MixedData.row2135 := by decide +kernel

theorem sourceRowsAt2136 : MixedData.sourceRows (2136 : Fin 2425) =
    MixedData.row2136 := by decide +kernel

theorem sourceRowsAt2137 : MixedData.sourceRows (2137 : Fin 2425) =
    MixedData.row2137 := by decide +kernel

theorem sourceRowsAt2138 : MixedData.sourceRows (2138 : Fin 2425) =
    MixedData.row2138 := by decide +kernel

theorem sourceRowsAt2139 : MixedData.sourceRows (2139 : Fin 2425) =
    MixedData.row2139 := by decide +kernel

theorem sourceRowsAt2140 : MixedData.sourceRows (2140 : Fin 2425) =
    MixedData.row2140 := by decide +kernel

theorem sourceRowsAt2141 : MixedData.sourceRows (2141 : Fin 2425) =
    MixedData.row2141 := by decide +kernel

theorem sourceRowsAt2142 : MixedData.sourceRows (2142 : Fin 2425) =
    MixedData.row2142 := by decide +kernel

theorem sourceRowsAt2143 : MixedData.sourceRows (2143 : Fin 2425) =
    MixedData.row2143 := by decide +kernel

theorem chunkSound133_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 133) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2128 ∨ k.val = 2129 ∨ k.val = 2130 ∨ k.val = 2131 ∨ k.val = 2132 ∨ k.val = 2133 ∨ k.val = 2134 ∨ k.val = 2135 ∨ k.val = 2136 ∨ k.val = 2137 ∨ k.val = 2138 ∨ k.val = 2139 ∨ k.val = 2140 ∨ k.val = 2141 ∨ k.val = 2142 ∨ k.val = 2143 := by omega
  rcases heq with h2128 | h2129 | h2130 | h2131 | h2132 | h2133 | h2134 | h2135 | h2136 | h2137 | h2138 | h2139 | h2140 | h2141 | h2142 | h2143
  · have he : k = (2128 : Fin 2425) := Fin.ext h2128
    subst k
    rw [sourceRowsAt2128]
    exact rowSound2128 B hB hF
  · have he : k = (2129 : Fin 2425) := Fin.ext h2129
    subst k
    rw [sourceRowsAt2129]
    exact rowSound2129 B hB hF
  · have he : k = (2130 : Fin 2425) := Fin.ext h2130
    subst k
    rw [sourceRowsAt2130]
    exact rowSound2130 B hB hF
  · have he : k = (2131 : Fin 2425) := Fin.ext h2131
    subst k
    rw [sourceRowsAt2131]
    exact rowSound2131 B hB hF
  · have he : k = (2132 : Fin 2425) := Fin.ext h2132
    subst k
    rw [sourceRowsAt2132]
    exact rowSound2132 B hB hF
  · have he : k = (2133 : Fin 2425) := Fin.ext h2133
    subst k
    rw [sourceRowsAt2133]
    exact rowSound2133 B hB hF
  · have he : k = (2134 : Fin 2425) := Fin.ext h2134
    subst k
    rw [sourceRowsAt2134]
    exact rowSound2134 B hB hF
  · have he : k = (2135 : Fin 2425) := Fin.ext h2135
    subst k
    rw [sourceRowsAt2135]
    exact rowSound2135 B hB hF
  · have he : k = (2136 : Fin 2425) := Fin.ext h2136
    subst k
    rw [sourceRowsAt2136]
    exact rowSound2136 B hB hF
  · have he : k = (2137 : Fin 2425) := Fin.ext h2137
    subst k
    rw [sourceRowsAt2137]
    exact rowSound2137 B hB hF
  · have he : k = (2138 : Fin 2425) := Fin.ext h2138
    subst k
    rw [sourceRowsAt2138]
    exact rowSound2138 B hB hF
  · have he : k = (2139 : Fin 2425) := Fin.ext h2139
    subst k
    rw [sourceRowsAt2139]
    exact rowSound2139 B hB hF
  · have he : k = (2140 : Fin 2425) := Fin.ext h2140
    subst k
    rw [sourceRowsAt2140]
    exact rowSound2140 B hB hF
  · have he : k = (2141 : Fin 2425) := Fin.ext h2141
    subst k
    rw [sourceRowsAt2141]
    exact rowSound2141 B hB hF
  · have he : k = (2142 : Fin 2425) := Fin.ext h2142
    subst k
    rw [sourceRowsAt2142]
    exact rowSound2142 B hB hF
  · have he : k = (2143 : Fin 2425) := Fin.ext h2143
    subst k
    rw [sourceRowsAt2143]
    exact rowSound2143 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound133_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound133_e_oai
