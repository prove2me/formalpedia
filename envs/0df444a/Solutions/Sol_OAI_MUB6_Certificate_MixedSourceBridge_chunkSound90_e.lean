-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:41:11.762204+00:00
-- url     : https://prove2.me/submissions/e870ec64-4d0a-497c-8d07-fe3f6409bacb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1441_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1442_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21083 raw21083Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw21083 raw21083Labels = mixedMoment B raw21083step0 raw21083step0Labels := by
      have hz : ∀ j, raw21083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21083step0 = (fun i j => raw21083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21083step0 raw21083; decide +kernel
      have hl : raw21083step0Labels = raw21083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21083 raw21083Labels permutation434 hz
    mixedMoment B raw21083step0 raw21083step0Labels = mixedMoment B raw21083step1 raw21083step1Labels := by
      have hz : ∀ j, raw21083step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21083step1 = (fun i j => raw21083step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21083step1 raw21083step0; decide +kernel
      have hl : raw21083step1Labels = raw21083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21083step0 raw21083step0Labels permutation80 hz
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical21084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21084 raw21084Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw21084 raw21084Labels = mixedMoment B raw21084step0 raw21084step0Labels := by
      have hz : ∀ j, raw21084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21084step0 = (fun i j => raw21084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21084step0 raw21084; decide +kernel
      have hl : raw21084step0Labels = raw21084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21084 raw21084Labels permutation434 hz
    mixedMoment B raw21084step0 raw21084step0Labels = mixedMoment B raw21084step1 raw21084step1Labels := by
      have hz : ∀ j, raw21084step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21084step1 = (fun i j => raw21084step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21084step1 raw21084step0; decide +kernel
      have hl : raw21084step1Labels = raw21084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21084step0 raw21084step0Labels permutation80 hz
    mixedMoment B raw21084step1 raw21084step1Labels = mixedMoment B raw21084step2 raw21084step2Labels := by
      have ha : raw21084step2 = (fun i j => raw21084step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21084step2 raw21084step1; decide +kernel
      have hl : raw21084step2Labels = raw21084step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21084step1 raw21084step1Labels permutation10 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical21087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21087 raw21087Labels = mixedMoment B node1053 node1053Labels := by
  calc
    mixedMoment B raw21087 raw21087Labels = mixedMoment B raw21087step0 raw21087step0Labels := by
      have hz : ∀ j, raw21087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21087step0 = (fun i j => raw21087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21087step0 raw21087; decide +kernel
      have hl : raw21087step0Labels = raw21087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21087 raw21087Labels permutation346 hz
    mixedMoment B raw21087step0 raw21087step0Labels = mixedMoment B raw21087step1 raw21087step1Labels := by
      have ha : raw21087step1 = (fun i j => raw21087step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21087step1 raw21087step0; decide +kernel
      have hl : raw21087step1Labels = raw21087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21087step0 raw21087step0Labels permutation34 permutation2
    _ = mixedMoment B node1053 node1053Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical193
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24740 raw24740Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24740 raw24740Labels = mixedMoment B raw24740step0 raw24740step0Labels := by
      have hz : ∀ j, raw24740 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24740step0 = (fun i j => raw24740 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24740step0 raw24740; decide +kernel
      have hl : raw24740step0Labels = raw24740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24740 raw24740Labels permutation265 hz
    mixedMoment B raw24740step0 raw24740step0Labels = mixedMoment B raw24740step1 raw24740step1Labels := by
      have ha : raw24740step1 = (fun i j => raw24740step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24740step1 raw24740step0; decide +kernel
      have hl : raw24740step1Labels = raw24740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24740step0 raw24740step0Labels permutation34 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical24746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24746 raw24746Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw24746 raw24746Labels = mixedMoment B raw24746step0 raw24746step0Labels := by
      have hz : ∀ j, raw24746 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24746step0 = (fun i j => raw24746 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24746step0 raw24746; decide +kernel
      have hl : raw24746step0Labels = raw24746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24746 raw24746Labels permutation520 hz
    mixedMoment B raw24746step0 raw24746step0Labels = mixedMoment B raw24746step1 raw24746step1Labels := by
      have hz : ∀ j, raw24746step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24746step1 = (fun i j => raw24746step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24746step1 raw24746step0; decide +kernel
      have hl : raw24746step1Labels = raw24746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24746step0 raw24746step0Labels permutation56 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical24747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24747 raw24747Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw24747 raw24747Labels = mixedMoment B raw24747step0 raw24747step0Labels := by
      have ha : raw24747step0 = (fun i j => raw24747 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24747step0 raw24747; decide +kernel
      have hl : raw24747step0Labels = raw24747Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24747 raw24747Labels permutation154 permutation2
    _ = mixedMoment B node2553 node2553Labels := by rfl

theorem canonical24748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24748 raw24748Labels = mixedMoment B node1156 node1156Labels := by
  calc
    mixedMoment B raw24748 raw24748Labels = mixedMoment B raw24748step0 raw24748step0Labels := by
      have ha : raw24748step0 = (fun i j => raw24748 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24748step0 raw24748; decide +kernel
      have hl : raw24748step0Labels = raw24748Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24748 raw24748Labels permutation154 permutation2
    _ = mixedMoment B node1156 node1156Labels := by rfl

theorem canonical24749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24749 raw24749Labels = mixedMoment B node1149 node1149Labels := by
  calc
    mixedMoment B raw24749 raw24749Labels = mixedMoment B raw24749step0 raw24749step0Labels := by
      have ha : raw24749step0 = (fun i j => raw24749 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24749step0 raw24749; decide +kernel
      have hl : raw24749step0Labels = raw24749Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24749 raw24749Labels permutation154 permutation2
    _ = mixedMoment B node1149 node1149Labels := by rfl

theorem canonical24750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24750 raw24750Labels = mixedMoment B node1151 node1151Labels := by
  calc
    _ = mixedMoment B node1151 node1151Labels := by rfl

theorem canonical24751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24751 raw24751Labels = mixedMoment B node1148 node1148Labels := by
  calc
    mixedMoment B raw24751 raw24751Labels = mixedMoment B raw24751step0 raw24751step0Labels := by
      have ha : raw24751step0 = (fun i j => raw24751 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24751step0 raw24751; decide +kernel
      have hl : raw24751step0Labels = raw24751Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24751 raw24751Labels permutation154 permutation2
    _ = mixedMoment B node1148 node1148Labels := by rfl

theorem canonical24826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24826 raw24826Labels = mixedMoment B node1229 node1229Labels := by
  calc
    mixedMoment B raw24826 raw24826Labels = mixedMoment B raw24826step0 raw24826step0Labels := by
      have hz : ∀ j, raw24826 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24826step0 = (fun i j => raw24826 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24826step0 raw24826; decide +kernel
      have hl : raw24826step0Labels = raw24826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24826 raw24826Labels permutation265 hz
    mixedMoment B raw24826step0 raw24826step0Labels = mixedMoment B raw24826step1 raw24826step1Labels := by
      have ha : raw24826step1 = (fun i j => raw24826step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24826step1 raw24826step0; decide +kernel
      have hl : raw24826step1Labels = raw24826step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24826step0 raw24826step0Labels permutation34 permutation2
    _ = mixedMoment B node1229 node1229Labels := by rfl

theorem canonical24827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24827 raw24827Labels = mixedMoment B node2550 node2550Labels := by
  calc
    mixedMoment B raw24827 raw24827Labels = mixedMoment B raw24827step0 raw24827step0Labels := by
      have ha : raw24827step0 = (fun i j => raw24827 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24827step0 raw24827; decide +kernel
      have hl : raw24827step0Labels = raw24827Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24827 raw24827Labels permutation154 permutation2
    _ = mixedMoment B node2550 node2550Labels := by rfl

theorem canonical24828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24828 raw24828Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw24828 raw24828Labels = mixedMoment B raw24828step0 raw24828step0Labels := by
      have hz : ∀ j, raw24828 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24828step0 = (fun i j => raw24828 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24828step0 raw24828; decide +kernel
      have hl : raw24828step0Labels = raw24828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24828 raw24828Labels permutation265 hz
    mixedMoment B raw24828step0 raw24828step0Labels = mixedMoment B raw24828step1 raw24828step1Labels := by
      have ha : raw24828step1 = (fun i j => raw24828step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24828step1 raw24828step0; decide +kernel
      have hl : raw24828step1Labels = raw24828step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24828step0 raw24828step0Labels permutation34 permutation2
    _ = mixedMoment B node2504 node2504Labels := by rfl

theorem canonical24829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24829 raw24829Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw24829 raw24829Labels = mixedMoment B raw24829step0 raw24829step0Labels := by
      have hz : ∀ j, raw24829 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24829step0 = (fun i j => raw24829 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24829step0 raw24829; decide +kernel
      have hl : raw24829step0Labels = raw24829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24829 raw24829Labels permutation265 hz
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical24830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24830 raw24830Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw24830 raw24830Labels = mixedMoment B raw24830step0 raw24830step0Labels := by
      have hz : ∀ j, raw24830 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24830step0 = (fun i j => raw24830 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24830step0 raw24830; decide +kernel
      have hl : raw24830step0Labels = raw24830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24830 raw24830Labels permutation265 hz
    mixedMoment B raw24830step0 raw24830step0Labels = mixedMoment B raw24830step1 raw24830step1Labels := by
      have ha : raw24830step1 = (fun i j => raw24830step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24830step1 raw24830step0; decide +kernel
      have hl : raw24830step1Labels = raw24830step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24830step0 raw24830step0Labels permutation34 permutation2
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical24831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24831 raw24831Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw24831 raw24831Labels = mixedMoment B raw24831step0 raw24831step0Labels := by
      have hz : ∀ j, raw24831 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24831step0 = (fun i j => raw24831 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24831step0 raw24831; decide +kernel
      have hl : raw24831step0Labels = raw24831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24831 raw24831Labels permutation265 hz
    mixedMoment B raw24831step0 raw24831step0Labels = mixedMoment B raw24831step1 raw24831step1Labels := by
      have ha : raw24831step1 = (fun i j => raw24831step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24831step1 raw24831step0; decide +kernel
      have hl : raw24831step1Labels = raw24831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24831step0 raw24831step0Labels permutation34 permutation2
    _ = mixedMoment B node2735 node2735Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical194
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24832 raw24832Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24832 raw24832Labels = mixedMoment B raw24832step0 raw24832step0Labels := by
      have hz : ∀ j, raw24832 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24832step0 = (fun i j => raw24832 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24832step0 raw24832; decide +kernel
      have hl : raw24832step0Labels = raw24832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24832 raw24832Labels permutation265 hz
    mixedMoment B raw24832step0 raw24832step0Labels = mixedMoment B raw24832step1 raw24832step1Labels := by
      have ha : raw24832step1 = (fun i j => raw24832step0 (permutation143 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24832step1 raw24832step0; decide +kernel
      have hl : raw24832step1Labels = raw24832step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24832step0 raw24832step0Labels permutation143 permutation0
    mixedMoment B raw24832step1 raw24832step1Labels = mixedMoment B raw24832step2 raw24832step2Labels := by
      have ha : raw24832step2 = -raw24832step1 := by apply Matrix.ext; change ∀ i j, raw24832step2 i j = -(raw24832step1 i j); unfold raw24832step2 raw24832step1; decide +kernel
      have hl : raw24832step2Labels = raw24832step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical24833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24833 raw24833Labels = mixedMoment B node1189 node1189Labels := by
  calc
    mixedMoment B raw24833 raw24833Labels = mixedMoment B raw24833step0 raw24833step0Labels := by
      have hz : ∀ j, raw24833 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24833step0 = (fun i j => raw24833 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24833step0 raw24833; decide +kernel
      have hl : raw24833step0Labels = raw24833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24833 raw24833Labels permutation265 hz
    mixedMoment B raw24833step0 raw24833step0Labels = mixedMoment B raw24833step1 raw24833step1Labels := by
      have ha : raw24833step1 = (fun i j => raw24833step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24833step1 raw24833step0; decide +kernel
      have hl : raw24833step1Labels = raw24833step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24833step0 raw24833step0Labels permutation34 permutation2
    _ = mixedMoment B node1189 node1189Labels := by rfl

theorem canonical24838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24838 raw24838Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw24838 raw24838Labels = mixedMoment B raw24838step0 raw24838step0Labels := by
      have hz : ∀ j, raw24838 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24838step0 = (fun i j => raw24838 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24838step0 raw24838; decide +kernel
      have hl : raw24838step0Labels = raw24838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24838 raw24838Labels permutation265 hz
    mixedMoment B raw24838step0 raw24838step0Labels = mixedMoment B raw24838step1 raw24838step1Labels := by
      have ha : raw24838step1 = (fun i j => raw24838step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24838step1 raw24838step0; decide +kernel
      have hl : raw24838step1Labels = raw24838step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24838step0 raw24838step0Labels permutation35 permutation2
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical24839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24839 raw24839Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw24839 raw24839Labels = mixedMoment B raw24839step0 raw24839step0Labels := by
      have hz : ∀ j, raw24839 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24839step0 = (fun i j => raw24839 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24839step0 raw24839; decide +kernel
      have hl : raw24839step0Labels = raw24839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24839 raw24839Labels permutation265 hz
    mixedMoment B raw24839step0 raw24839step0Labels = mixedMoment B raw24839step1 raw24839step1Labels := by
      have ha : raw24839step1 = (fun i j => raw24839step0 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24839step1 raw24839step0; decide +kernel
      have hl : raw24839step1Labels = raw24839step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24839step0 raw24839step0Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical24840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24840 raw24840Labels = mixedMoment B node1183 node1183Labels := by
  calc
    mixedMoment B raw24840 raw24840Labels = mixedMoment B raw24840step0 raw24840step0Labels := by
      have ha : raw24840step0 = (fun i j => raw24840 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24840step0 raw24840; decide +kernel
      have hl : raw24840step0Labels = raw24840Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24840 raw24840Labels permutation179 permutation2
    _ = mixedMoment B node1183 node1183Labels := by rfl

theorem canonical24841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24841 raw24841Labels = mixedMoment B node1286 node1286Labels := by
  calc
    mixedMoment B raw24841 raw24841Labels = mixedMoment B raw24841step0 raw24841step0Labels := by
      have hz : ∀ j, raw24841 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24841step0 = (fun i j => raw24841 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24841step0 raw24841; decide +kernel
      have hl : raw24841step0Labels = raw24841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24841 raw24841Labels permutation265 hz
    mixedMoment B raw24841step0 raw24841step0Labels = mixedMoment B raw24841step1 raw24841step1Labels := by
      have ha : raw24841step1 = (fun i j => raw24841step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24841step1 raw24841step0; decide +kernel
      have hl : raw24841step1Labels = raw24841step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24841step0 raw24841step0Labels permutation35 permutation2
    _ = mixedMoment B node1286 node1286Labels := by rfl

theorem canonical24842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24842 raw24842Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw24842 raw24842Labels = mixedMoment B raw24842step0 raw24842step0Labels := by
      have hz : ∀ j, raw24842 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24842step0 = (fun i j => raw24842 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24842step0 raw24842; decide +kernel
      have hl : raw24842step0Labels = raw24842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24842 raw24842Labels permutation265 hz
    mixedMoment B raw24842step0 raw24842step0Labels = mixedMoment B raw24842step1 raw24842step1Labels := by
      have ha : raw24842step1 = (fun i j => raw24842step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24842step1 raw24842step0; decide +kernel
      have hl : raw24842step1Labels = raw24842step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24842step0 raw24842step0Labels permutation35 permutation2
    _ = mixedMoment B node1188 node1188Labels := by rfl

theorem canonical24843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24843 raw24843Labels = mixedMoment B node1189 node1189Labels := by
  calc
    mixedMoment B raw24843 raw24843Labels = mixedMoment B raw24843step0 raw24843step0Labels := by
      have hz : ∀ j, raw24843 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24843step0 = (fun i j => raw24843 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24843step0 raw24843; decide +kernel
      have hl : raw24843step0Labels = raw24843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24843 raw24843Labels permutation265 hz
    mixedMoment B raw24843step0 raw24843step0Labels = mixedMoment B raw24843step1 raw24843step1Labels := by
      have ha : raw24843step1 = (fun i j => raw24843step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24843step1 raw24843step0; decide +kernel
      have hl : raw24843step1Labels = raw24843step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24843step0 raw24843step0Labels permutation36 permutation2
    _ = mixedMoment B node1189 node1189Labels := by rfl

theorem canonical24844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24844 raw24844Labels = mixedMoment B node1185 node1185Labels := by
  calc
    mixedMoment B raw24844 raw24844Labels = mixedMoment B raw24844step0 raw24844step0Labels := by
      have hz : ∀ j, raw24844 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24844step0 = (fun i j => raw24844 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24844step0 raw24844; decide +kernel
      have hl : raw24844step0Labels = raw24844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24844 raw24844Labels permutation265 hz
    mixedMoment B raw24844step0 raw24844step0Labels = mixedMoment B raw24844step1 raw24844step1Labels := by
      have ha : raw24844step1 = (fun i j => raw24844step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24844step1 raw24844step0; decide +kernel
      have hl : raw24844step1Labels = raw24844step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24844step0 raw24844step0Labels permutation34 permutation2
    _ = mixedMoment B node1185 node1185Labels := by rfl

theorem canonical24845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24845 raw24845Labels = mixedMoment B node2535 node2535Labels := by
  calc
    mixedMoment B raw24845 raw24845Labels = mixedMoment B raw24845step0 raw24845step0Labels := by
      have ha : raw24845step0 = (fun i j => raw24845 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24845step0 raw24845; decide +kernel
      have hl : raw24845step0Labels = raw24845Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24845 raw24845Labels permutation154 permutation2
    _ = mixedMoment B node2535 node2535Labels := by rfl

theorem canonical24846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24846 raw24846Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw24846 raw24846Labels = mixedMoment B raw24846step0 raw24846step0Labels := by
      have hz : ∀ j, raw24846 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24846step0 = (fun i j => raw24846 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24846step0 raw24846; decide +kernel
      have hl : raw24846step0Labels = raw24846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24846 raw24846Labels permutation265 hz
    mixedMoment B raw24846step0 raw24846step0Labels = mixedMoment B raw24846step1 raw24846step1Labels := by
      have ha : raw24846step1 = (fun i j => raw24846step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24846step1 raw24846step0; decide +kernel
      have hl : raw24846step1Labels = raw24846step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24846step0 raw24846step0Labels permutation34 permutation2
    _ = mixedMoment B node2400 node2400Labels := by rfl

theorem canonical24847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24847 raw24847Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw24847 raw24847Labels = mixedMoment B raw24847step0 raw24847step0Labels := by
      have hz : ∀ j, raw24847 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24847step0 = (fun i j => raw24847 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24847step0 raw24847; decide +kernel
      have hl : raw24847step0Labels = raw24847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24847 raw24847Labels permutation265 hz
    _ = mixedMoment B node2677 node2677Labels := by rfl

theorem canonical24848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24848 raw24848Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw24848 raw24848Labels = mixedMoment B raw24848step0 raw24848step0Labels := by
      have hz : ∀ j, raw24848 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24848step0 = (fun i j => raw24848 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24848step0 raw24848; decide +kernel
      have hl : raw24848step0Labels = raw24848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24848 raw24848Labels permutation520 hz
    mixedMoment B raw24848step0 raw24848step0Labels = mixedMoment B raw24848step1 raw24848step1Labels := by
      have hz : ∀ j, raw24848step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24848step1 = (fun i j => raw24848step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24848step1 raw24848step0; decide +kernel
      have hl : raw24848step1Labels = raw24848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24848step0 raw24848step0Labels permutation56 hz
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical24849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24849 raw24849Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw24849 raw24849Labels = mixedMoment B raw24849step0 raw24849step0Labels := by
      have hz : ∀ j, raw24849 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24849step0 = (fun i j => raw24849 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24849step0 raw24849; decide +kernel
      have hl : raw24849step0Labels = raw24849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24849 raw24849Labels permutation265 hz
    mixedMoment B raw24849step0 raw24849step0Labels = mixedMoment B raw24849step1 raw24849step1Labels := by
      have ha : raw24849step1 = (fun i j => raw24849step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24849step1 raw24849step0; decide +kernel
      have hl : raw24849step1Labels = raw24849step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24849step0 raw24849step0Labels permutation34 permutation2
    _ = mixedMoment B node2682 node2682Labels := by rfl

theorem canonical24850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24850 raw24850Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw24850 raw24850Labels = mixedMoment B raw24850step0 raw24850step0Labels := by
      have hz : ∀ j, raw24850 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24850step0 = (fun i j => raw24850 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24850step0 raw24850; decide +kernel
      have hl : raw24850step0Labels = raw24850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24850 raw24850Labels permutation520 hz
    mixedMoment B raw24850step0 raw24850step0Labels = mixedMoment B raw24850step1 raw24850step1Labels := by
      have hz : ∀ j, raw24850step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24850step1 = (fun i j => raw24850step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24850step1 raw24850step0; decide +kernel
      have hl : raw24850step1Labels = raw24850step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24850step0 raw24850step0Labels permutation56 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

theorem canonical24851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24851 raw24851Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw24851 raw24851Labels = mixedMoment B raw24851step0 raw24851step0Labels := by
      have hz : ∀ j, raw24851 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24851step0 = (fun i j => raw24851 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24851step0 raw24851; decide +kernel
      have hl : raw24851step0Labels = raw24851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24851 raw24851Labels permutation265 hz
    _ = mixedMoment B node1188 node1188Labels := by rfl

theorem canonical24852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24852 raw24852Labels = mixedMoment B node2536 node2536Labels := by
  calc
    _ = mixedMoment B node2536 node2536Labels := by rfl

theorem canonical24853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24853 raw24853Labels = mixedMoment B node2403 node2403Labels := by
  calc
    mixedMoment B raw24853 raw24853Labels = mixedMoment B raw24853step0 raw24853step0Labels := by
      have hz : ∀ j, raw24853 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24853step0 = (fun i j => raw24853 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24853step0 raw24853; decide +kernel
      have hl : raw24853step0Labels = raw24853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24853 raw24853Labels permutation265 hz
    _ = mixedMoment B node2403 node2403Labels := by rfl

theorem canonical24854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24854 raw24854Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw24854 raw24854Labels = mixedMoment B raw24854step0 raw24854step0Labels := by
      have hz : ∀ j, raw24854 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24854step0 = (fun i j => raw24854 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24854step0 raw24854; decide +kernel
      have hl : raw24854step0Labels = raw24854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24854 raw24854Labels permutation265 hz
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical24855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24855 raw24855Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw24855 raw24855Labels = mixedMoment B raw24855step0 raw24855step0Labels := by
      have hz : ∀ j, raw24855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24855step0 = (fun i j => raw24855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24855step0 raw24855; decide +kernel
      have hl : raw24855step0Labels = raw24855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24855 raw24855Labels permutation265 hz
    mixedMoment B raw24855step0 raw24855step0Labels = mixedMoment B raw24855step1 raw24855step1Labels := by
      have ha : raw24855step1 = (fun i j => raw24855step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24855step1 raw24855step0; decide +kernel
      have hl : raw24855step1Labels = raw24855step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24855step0 raw24855step0Labels permutation34 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical24856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24856 raw24856Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw24856 raw24856Labels = mixedMoment B raw24856step0 raw24856step0Labels := by
      have hz : ∀ j, raw24856 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24856step0 = (fun i j => raw24856 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24856step0 raw24856; decide +kernel
      have hl : raw24856step0Labels = raw24856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24856 raw24856Labels permutation265 hz
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical24857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24857 raw24857Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw24857 raw24857Labels = mixedMoment B raw24857step0 raw24857step0Labels := by
      have hz : ∀ j, raw24857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24857step0 = (fun i j => raw24857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24857step0 raw24857; decide +kernel
      have hl : raw24857step0Labels = raw24857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24857 raw24857Labels permutation265 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical24868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24868 raw24868Labels = mixedMoment B node1184 node1184Labels := by
  calc
    mixedMoment B raw24868 raw24868Labels = mixedMoment B raw24868step0 raw24868step0Labels := by
      have hz : ∀ j, raw24868 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24868step0 = (fun i j => raw24868 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24868step0 raw24868; decide +kernel
      have hl : raw24868step0Labels = raw24868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24868 raw24868Labels permutation265 hz
    mixedMoment B raw24868step0 raw24868step0Labels = mixedMoment B raw24868step1 raw24868step1Labels := by
      have ha : raw24868step1 = (fun i j => raw24868step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24868step1 raw24868step0; decide +kernel
      have hl : raw24868step1Labels = raw24868step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24868step0 raw24868step0Labels permutation34 permutation2
    _ = mixedMoment B node1184 node1184Labels := by rfl

theorem canonical24869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24869 raw24869Labels = mixedMoment B node2534 node2534Labels := by
  calc
    mixedMoment B raw24869 raw24869Labels = mixedMoment B raw24869step0 raw24869step0Labels := by
      have ha : raw24869step0 = (fun i j => raw24869 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24869step0 raw24869; decide +kernel
      have hl : raw24869step0Labels = raw24869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24869 raw24869Labels permutation154 permutation2
    _ = mixedMoment B node2534 node2534Labels := by rfl

theorem canonical24870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24870 raw24870Labels = mixedMoment B node2399 node2399Labels := by
  calc
    mixedMoment B raw24870 raw24870Labels = mixedMoment B raw24870step0 raw24870step0Labels := by
      have hz : ∀ j, raw24870 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24870step0 = (fun i j => raw24870 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24870step0 raw24870; decide +kernel
      have hl : raw24870step0Labels = raw24870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24870 raw24870Labels permutation265 hz
    mixedMoment B raw24870step0 raw24870step0Labels = mixedMoment B raw24870step1 raw24870step1Labels := by
      have ha : raw24870step1 = (fun i j => raw24870step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24870step1 raw24870step0; decide +kernel
      have hl : raw24870step1Labels = raw24870step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24870step0 raw24870step0Labels permutation34 permutation2
    _ = mixedMoment B node2399 node2399Labels := by rfl

theorem canonical24871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24871 raw24871Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw24871 raw24871Labels = mixedMoment B raw24871step0 raw24871step0Labels := by
      have hz : ∀ j, raw24871 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24871step0 = (fun i j => raw24871 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24871step0 raw24871; decide +kernel
      have hl : raw24871step0Labels = raw24871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24871 raw24871Labels permutation265 hz
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical24872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24872 raw24872Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw24872 raw24872Labels = mixedMoment B raw24872step0 raw24872step0Labels := by
      have hz : ∀ j, raw24872 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24872step0 = (fun i j => raw24872 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24872step0 raw24872; decide +kernel
      have hl : raw24872step0Labels = raw24872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24872 raw24872Labels permutation520 hz
    mixedMoment B raw24872step0 raw24872step0Labels = mixedMoment B raw24872step1 raw24872step1Labels := by
      have hz : ∀ j, raw24872step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24872step1 = (fun i j => raw24872step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24872step1 raw24872step0; decide +kernel
      have hl : raw24872step1Labels = raw24872step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24872step0 raw24872step0Labels permutation56 hz
    _ = mixedMoment B node2685 node2685Labels := by rfl

theorem canonical24873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24873 raw24873Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw24873 raw24873Labels = mixedMoment B raw24873step0 raw24873step0Labels := by
      have hz : ∀ j, raw24873 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24873step0 = (fun i j => raw24873 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24873step0 raw24873; decide +kernel
      have hl : raw24873step0Labels = raw24873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24873 raw24873Labels permutation265 hz
    mixedMoment B raw24873step0 raw24873step0Labels = mixedMoment B raw24873step1 raw24873step1Labels := by
      have ha : raw24873step1 = (fun i j => raw24873step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24873step1 raw24873step0; decide +kernel
      have hl : raw24873step1Labels = raw24873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24873step0 raw24873step0Labels permutation34 permutation2
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical24874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24874 raw24874Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw24874 raw24874Labels = mixedMoment B raw24874step0 raw24874step0Labels := by
      have hz : ∀ j, raw24874 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24874step0 = (fun i j => raw24874 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24874step0 raw24874; decide +kernel
      have hl : raw24874step0Labels = raw24874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24874 raw24874Labels permutation520 hz
    mixedMoment B raw24874step0 raw24874step0Labels = mixedMoment B raw24874step1 raw24874step1Labels := by
      have hz : ∀ j, raw24874step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24874step1 = (fun i j => raw24874step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24874step1 raw24874step0; decide +kernel
      have hl : raw24874step1Labels = raw24874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24874step0 raw24874step0Labels permutation56 hz
    mixedMoment B raw24874step1 raw24874step1Labels = mixedMoment B raw24874step2 raw24874step2Labels := by
      have ha : raw24874step2 = (fun i j => raw24874step1 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24874step2 raw24874step1; decide +kernel
      have hl : raw24874step2Labels = raw24874step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24874step1 raw24874step1Labels permutation30 permutation0
    mixedMoment B raw24874step2 raw24874step2Labels = mixedMoment B raw24874step3 raw24874step3Labels := by
      have ha : raw24874step3 = -raw24874step2 := by apply Matrix.ext; change ∀ i j, raw24874step3 i j = -(raw24874step2 i j); unfold raw24874step3 raw24874step2; decide +kernel
      have hl : raw24874step3Labels = raw24874step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical24875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24875 raw24875Labels = mixedMoment B node1201 node1201Labels := by
  calc
    mixedMoment B raw24875 raw24875Labels = mixedMoment B raw24875step0 raw24875step0Labels := by
      have ha : raw24875step0 = (fun i j => raw24875 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24875step0 raw24875; decide +kernel
      have hl : raw24875step0Labels = raw24875Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24875 raw24875Labels permutation154 permutation2
    _ = mixedMoment B node1201 node1201Labels := by rfl

theorem canonical24880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24880 raw24880Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw24880 raw24880Labels = mixedMoment B raw24880step0 raw24880step0Labels := by
      have ha : raw24880step0 = (fun i j => raw24880 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24880step0 raw24880; decide +kernel
      have hl : raw24880step0Labels = raw24880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24880 raw24880Labels permutation155 permutation2
    _ = mixedMoment B node2703 node2703Labels := by rfl

theorem canonical24881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24881 raw24881Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw24881 raw24881Labels = mixedMoment B raw24881step0 raw24881step0Labels := by
      have ha : raw24881step0 = (fun i j => raw24881 (permutation155 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24881step0 raw24881; decide +kernel
      have hl : raw24881step0Labels = raw24881Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24881 raw24881Labels permutation155 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical24882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24882 raw24882Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw24882 raw24882Labels = mixedMoment B raw24882step0 raw24882step0Labels := by
      have ha : raw24882step0 = (fun i j => raw24882 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24882step0 raw24882; decide +kernel
      have hl : raw24882step0Labels = raw24882Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24882 raw24882Labels permutation179 permutation2
    _ = mixedMoment B node1228 node1228Labels := by rfl

theorem canonical24883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24883 raw24883Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw24883 raw24883Labels = mixedMoment B raw24883step0 raw24883step0Labels := by
      have ha : raw24883step0 = (fun i j => raw24883 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24883step0 raw24883; decide +kernel
      have hl : raw24883step0Labels = raw24883Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24883 raw24883Labels permutation155 permutation2
    _ = mixedMoment B node1228 node1228Labels := by rfl

theorem canonical24884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24884 raw24884Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw24884 raw24884Labels = mixedMoment B raw24884step0 raw24884step0Labels := by
      have ha : raw24884step0 = (fun i j => raw24884 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24884step0 raw24884; decide +kernel
      have hl : raw24884step0Labels = raw24884Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24884 raw24884Labels permutation155 permutation2
    _ = mixedMoment B node1200 node1200Labels := by rfl

theorem canonical24885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24885 raw24885Labels = mixedMoment B node1201 node1201Labels := by
  calc
    mixedMoment B raw24885 raw24885Labels = mixedMoment B raw24885step0 raw24885step0Labels := by
      have ha : raw24885step0 = (fun i j => raw24885 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24885step0 raw24885; decide +kernel
      have hl : raw24885step0Labels = raw24885Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24885 raw24885Labels permutation156 permutation2
    _ = mixedMoment B node1201 node1201Labels := by rfl

theorem canonical24886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24886 raw24886Labels = mixedMoment B node1198 node1198Labels := by
  calc
    mixedMoment B raw24886 raw24886Labels = mixedMoment B raw24886step0 raw24886step0Labels := by
      have ha : raw24886step0 = (fun i j => raw24886 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24886step0 raw24886; decide +kernel
      have hl : raw24886step0Labels = raw24886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24886 raw24886Labels permutation154 permutation2
    _ = mixedMoment B node1198 node1198Labels := by rfl

theorem canonical24887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24887 raw24887Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw24887 raw24887Labels = mixedMoment B raw24887step0 raw24887step0Labels := by
      have ha : raw24887step0 = (fun i j => raw24887 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24887step0 raw24887; decide +kernel
      have hl : raw24887step0Labels = raw24887Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24887 raw24887Labels permutation154 permutation2
    _ = mixedMoment B node2459 node2459Labels := by rfl

theorem canonical24888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24888 raw24888Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw24888 raw24888Labels = mixedMoment B raw24888step0 raw24888step0Labels := by
      have ha : raw24888step0 = (fun i j => raw24888 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24888step0 raw24888; decide +kernel
      have hl : raw24888step0Labels = raw24888Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24888 raw24888Labels permutation178 permutation2
    _ = mixedMoment B node2459 node2459Labels := by rfl

theorem canonical24889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24889 raw24889Labels = mixedMoment B node2697 node2697Labels := by
  calc
    _ = mixedMoment B node2697 node2697Labels := by rfl

theorem canonical24890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24890 raw24890Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw24890 raw24890Labels = mixedMoment B raw24890step0 raw24890step0Labels := by
      have hz : ∀ j, raw24890 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24890step0 = (fun i j => raw24890 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24890step0 raw24890; decide +kernel
      have hl : raw24890step0Labels = raw24890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24890 raw24890Labels permutation520 hz
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical24891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24891 raw24891Labels = mixedMoment B node2701 node2701Labels := by
  calc
    mixedMoment B raw24891 raw24891Labels = mixedMoment B raw24891step0 raw24891step0Labels := by
      have ha : raw24891step0 = (fun i j => raw24891 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24891step0 raw24891; decide +kernel
      have hl : raw24891step0Labels = raw24891Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24891 raw24891Labels permutation154 permutation2
    _ = mixedMoment B node2701 node2701Labels := by rfl

theorem canonical24892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24892 raw24892Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw24892 raw24892Labels = mixedMoment B raw24892step0 raw24892step0Labels := by
      have hz : ∀ j, raw24892 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24892step0 = (fun i j => raw24892 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24892step0 raw24892; decide +kernel
      have hl : raw24892step0Labels = raw24892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24892 raw24892Labels permutation520 hz
    mixedMoment B raw24892step0 raw24892step0Labels = mixedMoment B raw24892step1 raw24892step1Labels := by
      have ha : raw24892step1 = (fun i j => raw24892step0 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24892step1 raw24892step0; decide +kernel
      have hl : raw24892step1Labels = raw24892step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24892step0 raw24892step0Labels permutation125 permutation0
    mixedMoment B raw24892step1 raw24892step1Labels = mixedMoment B raw24892step2 raw24892step2Labels := by
      have ha : raw24892step2 = -raw24892step1 := by apply Matrix.ext; change ∀ i j, raw24892step2 i j = -(raw24892step1 i j); unfold raw24892step2 raw24892step1; decide +kernel
      have hl : raw24892step2Labels = raw24892step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical24893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24893 raw24893Labels = mixedMoment B node1200 node1200Labels := by
  calc
    _ = mixedMoment B node1200 node1200Labels := by rfl

theorem canonical24894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24894 raw24894Labels = mixedMoment B node2461 node2461Labels := by
  calc
    _ = mixedMoment B node2461 node2461Labels := by rfl

theorem canonical24895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24895 raw24895Labels = mixedMoment B node2461 node2461Labels := by
  calc
    mixedMoment B raw24895 raw24895Labels = mixedMoment B raw24895step0 raw24895step0Labels := by
      have ha : raw24895step0 = (fun i j => raw24895 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24895step0 raw24895; decide +kernel
      have hl : raw24895step0Labels = raw24895Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24895 raw24895Labels permutation176 permutation2
    _ = mixedMoment B node2461 node2461Labels := by rfl

theorem canonical24896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24896 raw24896Labels = mixedMoment B node2694 node2694Labels := by
  calc
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical24897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24897 raw24897Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw24897 raw24897Labels = mixedMoment B raw24897step0 raw24897step0Labels := by
      have ha : raw24897step0 = (fun i j => raw24897 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24897step0 raw24897; decide +kernel
      have hl : raw24897step0Labels = raw24897Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24897 raw24897Labels permutation154 permutation2
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical24898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24898 raw24898Labels = mixedMoment B node2703 node2703Labels := by
  calc
    _ = mixedMoment B node2703 node2703Labels := by rfl

theorem canonical24899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24899 raw24899Labels = mixedMoment B node4090 node4090Labels := by
  calc
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical24909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24909 raw24909Labels = mixedMoment B node1197 node1197Labels := by
  calc
    mixedMoment B raw24909 raw24909Labels = mixedMoment B raw24909step0 raw24909step0Labels := by
      have ha : raw24909step0 = (fun i j => raw24909 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24909step0 raw24909; decide +kernel
      have hl : raw24909step0Labels = raw24909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24909 raw24909Labels permutation154 permutation2
    _ = mixedMoment B node1197 node1197Labels := by rfl

theorem canonical24910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24910 raw24910Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw24910 raw24910Labels = mixedMoment B raw24910step0 raw24910step0Labels := by
      have ha : raw24910step0 = (fun i j => raw24910 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24910step0 raw24910; decide +kernel
      have hl : raw24910step0Labels = raw24910Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24910 raw24910Labels permutation154 permutation2
    _ = mixedMoment B node2458 node2458Labels := by rfl

theorem canonical24911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24911 raw24911Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw24911 raw24911Labels = mixedMoment B raw24911step0 raw24911step0Labels := by
      have ha : raw24911step0 = (fun i j => raw24911 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24911step0 raw24911; decide +kernel
      have hl : raw24911step0Labels = raw24911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24911 raw24911Labels permutation178 permutation2
    _ = mixedMoment B node2458 node2458Labels := by rfl

theorem canonical24912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24912 raw24912Labels = mixedMoment B node2693 node2693Labels := by
  calc
    _ = mixedMoment B node2693 node2693Labels := by rfl

theorem canonical24913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24913 raw24913Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw24913 raw24913Labels = mixedMoment B raw24913step0 raw24913step0Labels := by
      have hz : ∀ j, raw24913 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24913step0 = (fun i j => raw24913 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24913step0 raw24913; decide +kernel
      have hl : raw24913step0Labels = raw24913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24913 raw24913Labels permutation520 hz
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical24914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24914 raw24914Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw24914 raw24914Labels = mixedMoment B raw24914step0 raw24914step0Labels := by
      have ha : raw24914step0 = (fun i j => raw24914 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24914step0 raw24914; decide +kernel
      have hl : raw24914step0Labels = raw24914Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24914 raw24914Labels permutation154 permutation2
    _ = mixedMoment B node2700 node2700Labels := by rfl

theorem canonical24915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24915 raw24915Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24915 raw24915Labels = mixedMoment B raw24915step0 raw24915step0Labels := by
      have hz : ∀ j, raw24915 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24915step0 = (fun i j => raw24915 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24915step0 raw24915; decide +kernel
      have hl : raw24915step0Labels = raw24915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24915 raw24915Labels permutation520 hz
    mixedMoment B raw24915step0 raw24915step0Labels = mixedMoment B raw24915step1 raw24915step1Labels := by
      have ha : raw24915step1 = (fun i j => raw24915step0 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24915step1 raw24915step0; decide +kernel
      have hl : raw24915step1Labels = raw24915step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24915step0 raw24915step0Labels permutation149 permutation0
    mixedMoment B raw24915step1 raw24915step1Labels = mixedMoment B raw24915step2 raw24915step2Labels := by
      have ha : raw24915step2 = -raw24915step1 := by apply Matrix.ext; change ∀ i j, raw24915step2 i j = -(raw24915step1 i j); unfold raw24915step2 raw24915step1; decide +kernel
      have hl : raw24915step2Labels = raw24915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical24916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24916 raw24916Labels = mixedMoment B node1060 node1060Labels := by
  calc
    mixedMoment B raw24916 raw24916Labels = mixedMoment B raw24916step0 raw24916step0Labels := by
      have hz : ∀ j, raw24916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24916step0 = (fun i j => raw24916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24916step0 raw24916; decide +kernel
      have hl : raw24916step0Labels = raw24916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24916 raw24916Labels permutation346 hz
    _ = mixedMoment B node1060 node1060Labels := by rfl

theorem canonical24921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24921 raw24921Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw24921 raw24921Labels = mixedMoment B raw24921step0 raw24921step0Labels := by
      have hz : ∀ j, raw24921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24921step0 = (fun i j => raw24921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24921step0 raw24921; decide +kernel
      have hl : raw24921step0Labels = raw24921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24921 raw24921Labels permutation346 hz
    mixedMoment B raw24921step0 raw24921step0Labels = mixedMoment B raw24921step1 raw24921step1Labels := by
      have ha : raw24921step1 = (fun i j => raw24921step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24921step1 raw24921step0; decide +kernel
      have hl : raw24921step1Labels = raw24921step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24921step0 raw24921step0Labels permutation36 permutation2
    _ = mixedMoment B node2275 node2275Labels := by rfl

theorem canonical24922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24922 raw24922Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24922 raw24922Labels = mixedMoment B raw24922step0 raw24922step0Labels := by
      have hz : ∀ j, raw24922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24922step0 = (fun i j => raw24922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24922step0 raw24922; decide +kernel
      have hl : raw24922step0Labels = raw24922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24922 raw24922Labels permutation346 hz
    mixedMoment B raw24922step0 raw24922step0Labels = mixedMoment B raw24922step1 raw24922step1Labels := by
      have ha : raw24922step1 = (fun i j => raw24922step0 (permutation53 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24922step1 raw24922step0; decide +kernel
      have hl : raw24922step1Labels = raw24922step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24922step0 raw24922step0Labels permutation53 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical24923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24923 raw24923Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw24923 raw24923Labels = mixedMoment B raw24923step0 raw24923step0Labels := by
      have hz : ∀ j, raw24923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24923step0 = (fun i j => raw24923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24923step0 raw24923; decide +kernel
      have hl : raw24923step0Labels = raw24923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24923 raw24923Labels permutation346 hz
    mixedMoment B raw24923step0 raw24923step0Labels = mixedMoment B raw24923step1 raw24923step1Labels := by
      have ha : raw24923step1 = (fun i j => raw24923step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24923step1 raw24923step0; decide +kernel
      have hl : raw24923step1Labels = raw24923step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24923step0 raw24923step0Labels permutation53 permutation2
    _ = mixedMoment B node1073 node1073Labels := by rfl

theorem canonical24924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24924 raw24924Labels = mixedMoment B node1052 node1052Labels := by
  calc
    mixedMoment B raw24924 raw24924Labels = mixedMoment B raw24924step0 raw24924step0Labels := by
      have ha : raw24924step0 = (fun i j => raw24924 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24924step0 raw24924; decide +kernel
      have hl : raw24924step0Labels = raw24924Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24924 raw24924Labels permutation170 permutation2
    _ = mixedMoment B node1052 node1052Labels := by rfl

theorem canonical24925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24925 raw24925Labels = mixedMoment B node1054 node1054Labels := by
  calc
    mixedMoment B raw24925 raw24925Labels = mixedMoment B raw24925step0 raw24925step0Labels := by
      have hz : ∀ j, raw24925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24925step0 = (fun i j => raw24925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24925step0 raw24925; decide +kernel
      have hl : raw24925step0Labels = raw24925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24925 raw24925Labels permutation346 hz
    mixedMoment B raw24925step0 raw24925step0Labels = mixedMoment B raw24925step1 raw24925step1Labels := by
      have ha : raw24925step1 = (fun i j => raw24925step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24925step1 raw24925step0; decide +kernel
      have hl : raw24925step1Labels = raw24925step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24925step0 raw24925step0Labels permutation37 permutation2
    _ = mixedMoment B node1054 node1054Labels := by rfl

theorem canonical24926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24926 raw24926Labels = mixedMoment B node1054 node1054Labels := by
  calc
    mixedMoment B raw24926 raw24926Labels = mixedMoment B raw24926step0 raw24926step0Labels := by
      have hz : ∀ j, raw24926 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24926step0 = (fun i j => raw24926 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24926step0 raw24926; decide +kernel
      have hl : raw24926step0Labels = raw24926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24926 raw24926Labels permutation346 hz
    mixedMoment B raw24926step0 raw24926step0Labels = mixedMoment B raw24926step1 raw24926step1Labels := by
      have ha : raw24926step1 = (fun i j => raw24926step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24926step1 raw24926step0; decide +kernel
      have hl : raw24926step1Labels = raw24926step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24926step0 raw24926step0Labels permutation36 permutation2
    _ = mixedMoment B node1054 node1054Labels := by rfl

theorem canonical24927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24927 raw24927Labels = mixedMoment B node1054 node1054Labels := by
  calc
    mixedMoment B raw24927 raw24927Labels = mixedMoment B raw24927step0 raw24927step0Labels := by
      have hz : ∀ j, raw24927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24927step0 = (fun i j => raw24927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24927step0 raw24927; decide +kernel
      have hl : raw24927step0Labels = raw24927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24927 raw24927Labels permutation346 hz
    mixedMoment B raw24927step0 raw24927step0Labels = mixedMoment B raw24927step1 raw24927step1Labels := by
      have ha : raw24927step1 = (fun i j => raw24927step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24927step1 raw24927step0; decide +kernel
      have hl : raw24927step1Labels = raw24927step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24927step0 raw24927step0Labels permutation34 permutation2
    _ = mixedMoment B node1054 node1054Labels := by rfl

theorem canonical24928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24928 raw24928Labels = mixedMoment B node2129 node2129Labels := by
  calc
    mixedMoment B raw24928 raw24928Labels = mixedMoment B raw24928step0 raw24928step0Labels := by
      have hz : ∀ j, raw24928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24928step0 = (fun i j => raw24928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24928step0 raw24928; decide +kernel
      have hl : raw24928step0Labels = raw24928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24928 raw24928Labels permutation346 hz
    mixedMoment B raw24928step0 raw24928step0Labels = mixedMoment B raw24928step1 raw24928step1Labels := by
      have ha : raw24928step1 = (fun i j => raw24928step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24928step1 raw24928step0; decide +kernel
      have hl : raw24928step1Labels = raw24928step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24928step0 raw24928step0Labels permutation34 permutation2
    _ = mixedMoment B node2129 node2129Labels := by rfl

theorem canonical24929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24929 raw24929Labels = mixedMoment B node2031 node2031Labels := by
  calc
    mixedMoment B raw24929 raw24929Labels = mixedMoment B raw24929step0 raw24929step0Labels := by
      have ha : raw24929step0 = (fun i j => raw24929 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24929step0 raw24929; decide +kernel
      have hl : raw24929step0Labels = raw24929Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24929 raw24929Labels permutation178 permutation2
    _ = mixedMoment B node2031 node2031Labels := by rfl

theorem canonical24930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24930 raw24930Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw24930 raw24930Labels = mixedMoment B raw24930step0 raw24930step0Labels := by
      have hz : ∀ j, raw24930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24930step0 = (fun i j => raw24930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24930step0 raw24930; decide +kernel
      have hl : raw24930step0Labels = raw24930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24930 raw24930Labels permutation346 hz
    mixedMoment B raw24930step0 raw24930step0Labels = mixedMoment B raw24930step1 raw24930step1Labels := by
      have ha : raw24930step1 = (fun i j => raw24930step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24930step1 raw24930step0; decide +kernel
      have hl : raw24930step1Labels = raw24930step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24930step0 raw24930step0Labels permutation38 permutation2
    _ = mixedMoment B node2251 node2251Labels := by rfl

theorem canonical24931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24931 raw24931Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw24931 raw24931Labels = mixedMoment B raw24931step0 raw24931step0Labels := by
      have hz : ∀ j, raw24931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24931step0 = (fun i j => raw24931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24931step0 raw24931; decide +kernel
      have hl : raw24931step0Labels = raw24931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24931 raw24931Labels permutation346 hz
    mixedMoment B raw24931step0 raw24931step0Labels = mixedMoment B raw24931step1 raw24931step1Labels := by
      have ha : raw24931step1 = (fun i j => raw24931step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24931step1 raw24931step0; decide +kernel
      have hl : raw24931step1Labels = raw24931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24931step0 raw24931step0Labels permutation44 permutation2
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical24932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24932 raw24932Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw24932 raw24932Labels = mixedMoment B raw24932step0 raw24932step0Labels := by
      have hz : ∀ j, raw24932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24932step0 = (fun i j => raw24932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24932step0 raw24932; decide +kernel
      have hl : raw24932step0Labels = raw24932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24932 raw24932Labels permutation346 hz
    mixedMoment B raw24932step0 raw24932step0Labels = mixedMoment B raw24932step1 raw24932step1Labels := by
      have ha : raw24932step1 = (fun i j => raw24932step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24932step1 raw24932step0; decide +kernel
      have hl : raw24932step1Labels = raw24932step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24932step0 raw24932step0Labels permutation34 permutation2
    _ = mixedMoment B node2275 node2275Labels := by rfl

theorem canonical24933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24933 raw24933Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24933 raw24933Labels = mixedMoment B raw24933step0 raw24933step0Labels := by
      have hz : ∀ j, raw24933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24933step0 = (fun i j => raw24933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24933step0 raw24933; decide +kernel
      have hl : raw24933step0Labels = raw24933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24933 raw24933Labels permutation346 hz
    mixedMoment B raw24933step0 raw24933step0Labels = mixedMoment B raw24933step1 raw24933step1Labels := by
      have ha : raw24933step1 = (fun i j => raw24933step0 (permutation47 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24933step1 raw24933step0; decide +kernel
      have hl : raw24933step1Labels = raw24933step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24933step0 raw24933step0Labels permutation47 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical24934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24934 raw24934Labels = mixedMoment B node2128 node2128Labels := by
  calc
    mixedMoment B raw24934 raw24934Labels = mixedMoment B raw24934step0 raw24934step0Labels := by
      have hz : ∀ j, raw24934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24934step0 = (fun i j => raw24934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24934step0 raw24934; decide +kernel
      have hl : raw24934step0Labels = raw24934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24934 raw24934Labels permutation346 hz
    mixedMoment B raw24934step0 raw24934step0Labels = mixedMoment B raw24934step1 raw24934step1Labels := by
      have ha : raw24934step1 = (fun i j => raw24934step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24934step1 raw24934step0; decide +kernel
      have hl : raw24934step1Labels = raw24934step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24934step0 raw24934step0Labels permutation34 permutation2
    _ = mixedMoment B node2128 node2128Labels := by rfl

theorem canonical24935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24935 raw24935Labels = mixedMoment B node2030 node2030Labels := by
  calc
    mixedMoment B raw24935 raw24935Labels = mixedMoment B raw24935step0 raw24935step0Labels := by
      have ha : raw24935step0 = (fun i j => raw24935 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24935step0 raw24935; decide +kernel
      have hl : raw24935step0Labels = raw24935Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24935 raw24935Labels permutation178 permutation2
    _ = mixedMoment B node2030 node2030Labels := by rfl

theorem canonical24936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24936 raw24936Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw24936 raw24936Labels = mixedMoment B raw24936step0 raw24936step0Labels := by
      have hz : ∀ j, raw24936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24936step0 = (fun i j => raw24936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24936step0 raw24936; decide +kernel
      have hl : raw24936step0Labels = raw24936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24936 raw24936Labels permutation346 hz
    mixedMoment B raw24936step0 raw24936step0Labels = mixedMoment B raw24936step1 raw24936step1Labels := by
      have ha : raw24936step1 = (fun i j => raw24936step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24936step1 raw24936step0; decide +kernel
      have hl : raw24936step1Labels = raw24936step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24936step0 raw24936step0Labels permutation44 permutation2
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical24937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24937 raw24937Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw24937 raw24937Labels = mixedMoment B raw24937step0 raw24937step0Labels := by
      have hz : ∀ j, raw24937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24937step0 = (fun i j => raw24937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24937step0 raw24937; decide +kernel
      have hl : raw24937step0Labels = raw24937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24937 raw24937Labels permutation346 hz
    mixedMoment B raw24937step0 raw24937step0Labels = mixedMoment B raw24937step1 raw24937step1Labels := by
      have ha : raw24937step1 = (fun i j => raw24937step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24937step1 raw24937step0; decide +kernel
      have hl : raw24937step1Labels = raw24937step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24937step0 raw24937step0Labels permutation34 permutation2
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical24938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24938 raw24938Labels = mixedMoment B node990 node990Labels := by
  calc
    mixedMoment B raw24938 raw24938Labels = mixedMoment B raw24938step0 raw24938step0Labels := by
      have ha : raw24938step0 = (fun i j => raw24938 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24938step0 raw24938; decide +kernel
      have hl : raw24938step0Labels = raw24938Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24938 raw24938Labels permutation176 permutation2
    _ = mixedMoment B node990 node990Labels := by rfl

theorem canonical24943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24943 raw24943Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw24943 raw24943Labels = mixedMoment B raw24943step0 raw24943step0Labels := by
      have ha : raw24943step0 = (fun i j => raw24943 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24943step0 raw24943; decide +kernel
      have hl : raw24943step0Labels = raw24943Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24943 raw24943Labels permutation180 permutation2
    _ = mixedMoment B node2214 node2214Labels := by rfl

theorem canonical24944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24944 raw24944Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24944 raw24944Labels = mixedMoment B raw24944step0 raw24944step0Labels := by
      have hz : ∀ j, raw24944 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw24944step0 = (fun i j => raw24944 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw24944step0 raw24944; decide +kernel
      have hl : raw24944step0Labels = raw24944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24944 raw24944Labels permutation590 hz
    mixedMoment B raw24944step0 raw24944step0Labels = mixedMoment B raw24944step1 raw24944step1Labels := by
      have ha : raw24944step1 = (fun i j => raw24944step0 (permutation41 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24944step1 raw24944step0; decide +kernel
      have hl : raw24944step1Labels = raw24944step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24944step0 raw24944step0Labels permutation41 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical24945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24945 raw24945Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw24945 raw24945Labels = mixedMoment B raw24945step0 raw24945step0Labels := by
      have ha : raw24945step0 = (fun i j => raw24945 (permutation197 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24945step0 raw24945; decide +kernel
      have hl : raw24945step0Labels = raw24945Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24945 raw24945Labels permutation197 permutation2
    _ = mixedMoment B node998 node998Labels := by rfl

theorem canonical24946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24946 raw24946Labels = mixedMoment B node1052 node1052Labels := by
  calc
    mixedMoment B raw24946 raw24946Labels = mixedMoment B raw24946step0 raw24946step0Labels := by
      have ha : raw24946step0 = (fun i j => raw24946 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24946step0 raw24946; decide +kernel
      have hl : raw24946step0Labels = raw24946Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24946 raw24946Labels permutation156 permutation2
    _ = mixedMoment B node1052 node1052Labels := by rfl

theorem canonical24947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24947 raw24947Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw24947 raw24947Labels = mixedMoment B raw24947step0 raw24947step0Labels := by
      have ha : raw24947step0 = (fun i j => raw24947 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24947step0 raw24947; decide +kernel
      have hl : raw24947step0Labels = raw24947Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24947 raw24947Labels permutation181 permutation2
    _ = mixedMoment B node988 node988Labels := by rfl

theorem canonical24948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24948 raw24948Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw24948 raw24948Labels = mixedMoment B raw24948step0 raw24948step0Labels := by
      have ha : raw24948step0 = (fun i j => raw24948 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24948step0 raw24948; decide +kernel
      have hl : raw24948step0Labels = raw24948Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24948 raw24948Labels permutation180 permutation2
    _ = mixedMoment B node988 node988Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node988 node988Labels = Sparse.eval nodeValue988 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 988) = mixedMoment B node988 node988Labels := rfl
  simpa [nodeValue988, Sparse.eval] using hc.symm

theorem sound990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node990 node990Labels = Sparse.eval nodeValue990 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 990) = mixedMoment B node990 node990Labels := rfl
  simpa [nodeValue990, Sparse.eval] using hc.symm

theorem sound998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node998 node998Labels = Sparse.eval nodeValue998 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 998) = mixedMoment B node998 node998Labels := rfl
  simpa [nodeValue998, Sparse.eval] using hc.symm

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

theorem sound1052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1052 node1052Labels = Sparse.eval nodeValue1052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1052) = mixedMoment B node1052 node1052Labels := rfl
  simpa [nodeValue1052, Sparse.eval] using hc.symm

theorem sound1053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1053 node1053Labels = Sparse.eval nodeValue1053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1053) = mixedMoment B node1053 node1053Labels := rfl
  simpa [nodeValue1053, Sparse.eval] using hc.symm

theorem sound1054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1054 node1054Labels = Sparse.eval nodeValue1054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1054) = mixedMoment B node1054 node1054Labels := rfl
  simpa [nodeValue1054, Sparse.eval] using hc.symm

theorem sound1060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1060 node1060Labels = Sparse.eval nodeValue1060 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1060) = mixedMoment B node1060 node1060Labels := rfl
  simpa [nodeValue1060, Sparse.eval] using hc.symm

theorem sound1073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1073 node1073Labels = Sparse.eval nodeValue1073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1073) = mixedMoment B node1073 node1073Labels := rfl
  simpa [nodeValue1073, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1148 node1148Labels = Sparse.eval nodeValue1148 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1148) = mixedMoment B node1148 node1148Labels := rfl
  simpa [nodeValue1148, Sparse.eval] using hc.symm

theorem sound1149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1149 node1149Labels = Sparse.eval nodeValue1149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1149) = mixedMoment B node1149 node1149Labels := rfl
  simpa [nodeValue1149, Sparse.eval] using hc.symm

theorem sound1151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1151 node1151Labels = Sparse.eval nodeValue1151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1151) = mixedMoment B node1151 node1151Labels := rfl
  simpa [nodeValue1151, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1156 node1156Labels = Sparse.eval nodeValue1156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1156) = mixedMoment B node1156 node1156Labels := rfl
  simpa [nodeValue1156, Sparse.eval] using hc.symm

theorem sound1183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1183 node1183Labels = Sparse.eval nodeValue1183 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1183) = mixedMoment B node1183 node1183Labels := rfl
  simpa [nodeValue1183, Sparse.eval] using hc.symm

theorem sound1184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1184 node1184Labels = Sparse.eval nodeValue1184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1184) = mixedMoment B node1184 node1184Labels := rfl
  simpa [nodeValue1184, Sparse.eval] using hc.symm

theorem sound1185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1185 node1185Labels = Sparse.eval nodeValue1185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1185) = mixedMoment B node1185 node1185Labels := rfl
  simpa [nodeValue1185, Sparse.eval] using hc.symm

theorem sound1188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1188 node1188Labels = Sparse.eval nodeValue1188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1188) = mixedMoment B node1188 node1188Labels := rfl
  simpa [nodeValue1188, Sparse.eval] using hc.symm

theorem sound1189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1189 node1189Labels = Sparse.eval nodeValue1189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1189) = mixedMoment B node1189 node1189Labels := rfl
  simpa [nodeValue1189, Sparse.eval] using hc.symm

theorem sound1197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1197 node1197Labels = Sparse.eval nodeValue1197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1197) = mixedMoment B node1197 node1197Labels := rfl
  simpa [nodeValue1197, Sparse.eval] using hc.symm

theorem sound1198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1198 node1198Labels = Sparse.eval nodeValue1198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1198) = mixedMoment B node1198 node1198Labels := rfl
  simpa [nodeValue1198, Sparse.eval] using hc.symm

theorem sound1200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1200 node1200Labels = Sparse.eval nodeValue1200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1200) = mixedMoment B node1200 node1200Labels := rfl
  simpa [nodeValue1200, Sparse.eval] using hc.symm

theorem sound1201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1201 node1201Labels = Sparse.eval nodeValue1201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1201) = mixedMoment B node1201 node1201Labels := rfl
  simpa [nodeValue1201, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1228 node1228Labels = Sparse.eval nodeValue1228 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1228) = mixedMoment B node1228 node1228Labels := rfl
  simpa [nodeValue1228, Sparse.eval] using hc.symm

theorem sound1229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1229 node1229Labels = Sparse.eval nodeValue1229 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1229) = mixedMoment B node1229 node1229Labels := rfl
  simpa [nodeValue1229, Sparse.eval] using hc.symm

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1286 node1286Labels = Sparse.eval nodeValue1286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1286) = mixedMoment B node1286 node1286Labels := rfl
  simpa [nodeValue1286, Sparse.eval] using hc.symm

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

theorem sound2030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2030 node2030Labels = Sparse.eval nodeValue2030 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2030) = mixedMoment B node2030 node2030Labels := rfl
  simpa [nodeValue2030, Sparse.eval] using hc.symm

theorem sound2031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2031 node2031Labels = Sparse.eval nodeValue2031 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2031) = mixedMoment B node2031 node2031Labels := rfl
  simpa [nodeValue2031, Sparse.eval] using hc.symm

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

theorem sound2128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2128 node2128Labels = Sparse.eval nodeValue2128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2128) = mixedMoment B node2128 node2128Labels := rfl
  simpa [nodeValue2128, Sparse.eval] using hc.symm

theorem sound2129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2129 node2129Labels = Sparse.eval nodeValue2129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2129) = mixedMoment B node2129 node2129Labels := rfl
  simpa [nodeValue2129, Sparse.eval] using hc.symm

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

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

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

theorem sound2251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2251 node2251Labels = Sparse.eval nodeValue2251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2251) = mixedMoment B node2251 node2251Labels := rfl
  simpa [nodeValue2251, Sparse.eval] using hc.symm

theorem sound2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2274 node2274Labels = Sparse.eval nodeValue2274 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2274) = mixedMoment B node2274 node2274Labels := rfl
  simpa [nodeValue2274, Sparse.eval] using hc.symm

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

theorem sound2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2276 node2276Labels = Sparse.eval nodeValue2276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2276) = mixedMoment B node2276 node2276Labels := rfl
  simpa [nodeValue2276, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2403 node2403Labels = 0 := by
  exact mixedMoment_order_one B hB node2403 node2403Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2399 node2399Labels = Sparse.eval nodeValue2399 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2399) = mixedMoment B node2399 node2399Labels := rfl
  simpa [nodeValue2399, Sparse.eval] using hc.symm

theorem sound2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2400 node2400Labels = Sparse.eval nodeValue2400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2400) = mixedMoment B node2400 node2400Labels := rfl
  simpa [nodeValue2400, Sparse.eval] using hc.symm

theorem sound2403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2403 node2403Labels = Sparse.eval nodeValue2403 (mixedVector B) := by
  simpa only [nodeValue2403, Sparse.eval_nil] using zero2403 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2461 node2461Labels = 0 := by
  exact mixedMoment_order_one B hB node2461 node2461Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2458 node2458Labels = Sparse.eval nodeValue2458 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2458) = mixedMoment B node2458 node2458Labels := rfl
  simpa [nodeValue2458, Sparse.eval] using hc.symm

theorem sound2459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2459 node2459Labels = Sparse.eval nodeValue2459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2459) = mixedMoment B node2459 node2459Labels := rfl
  simpa [nodeValue2459, Sparse.eval] using hc.symm

theorem sound2461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2461 node2461Labels = Sparse.eval nodeValue2461 (mixedVector B) := by
  simpa only [nodeValue2461, Sparse.eval_nil] using zero2461 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2504 node2504Labels = Sparse.eval nodeValue2504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2504) = mixedMoment B node2504 node2504Labels := rfl
  simpa [nodeValue2504, Sparse.eval] using hc.symm

theorem sound2534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2534 node2534Labels = Sparse.eval nodeValue2534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2534) = mixedMoment B node2534 node2534Labels := rfl
  simpa [nodeValue2534, Sparse.eval] using hc.symm

theorem sound2535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2535 node2535Labels = Sparse.eval nodeValue2535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2535) = mixedMoment B node2535 node2535Labels := rfl
  simpa [nodeValue2535, Sparse.eval] using hc.symm

theorem sound2536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2536 node2536Labels = Sparse.eval nodeValue2536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2536) = mixedMoment B node2536 node2536Labels := rfl
  simpa [nodeValue2536, Sparse.eval] using hc.symm

theorem sound2550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2550 node2550Labels = Sparse.eval nodeValue2550 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2550) = mixedMoment B node2550 node2550Labels := rfl
  simpa [nodeValue2550, Sparse.eval] using hc.symm

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

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

theorem sound2670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2670 node2670Labels = Sparse.eval nodeValue2670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2670) = mixedMoment B node2670 node2670Labels := rfl
  simpa [nodeValue2670, Sparse.eval] using hc.symm

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

theorem sound2677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2677 node2677Labels = Sparse.eval nodeValue2677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2677) = mixedMoment B node2677 node2677Labels := rfl
  simpa [nodeValue2677, Sparse.eval] using hc.symm

theorem sound2681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2681 node2681Labels = Sparse.eval nodeValue2681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2681) = mixedMoment B node2681 node2681Labels := rfl
  simpa [nodeValue2681, Sparse.eval] using hc.symm

theorem sound2682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2682 node2682Labels = Sparse.eval nodeValue2682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2682) = mixedMoment B node2682 node2682Labels := rfl
  simpa [nodeValue2682, Sparse.eval] using hc.symm

theorem sound2684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2684 node2684Labels = Sparse.eval nodeValue2684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2684) = mixedMoment B node2684 node2684Labels := rfl
  simpa [nodeValue2684, Sparse.eval] using hc.symm

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

theorem sound2686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2686 node2686Labels = Sparse.eval nodeValue2686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2686) = mixedMoment B node2686 node2686Labels := rfl
  simpa [nodeValue2686, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2693 node2693Labels = 0 := by
  exact mixedMoment_alpha B hF node2693 node2693Labels 1 permutation213
    (by decide +kernel)

theorem zero2701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2701 node2701Labels = 0 := by
  exact mixedMoment_alpha B hF node2701 node2701Labels 1 permutation216
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2693 node2693Labels = Sparse.eval nodeValue2693 (mixedVector B) := by
  simpa only [nodeValue2693, Sparse.eval_nil] using zero2693 B _hB _hF

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

theorem sound2697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2697 node2697Labels = Sparse.eval nodeValue2697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2697) = mixedMoment B node2697 node2697Labels := rfl
  simpa [nodeValue2697, Sparse.eval] using hc.symm

theorem sound2700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2700 node2700Labels = Sparse.eval nodeValue2700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2700) = mixedMoment B node2700 node2700Labels := rfl
  simpa [nodeValue2700, Sparse.eval] using hc.symm

theorem sound2701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2701 node2701Labels = Sparse.eval nodeValue2701 (mixedVector B) := by
  simpa only [nodeValue2701, Sparse.eval_nil] using zero2701 B _hB _hF

theorem sound2703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2703 node2703Labels = Sparse.eval nodeValue2703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2703) = mixedMoment B node2703 node2703Labels := rfl
  simpa [nodeValue2703, Sparse.eval] using hc.symm

theorem sound2704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2704 node2704Labels = Sparse.eval nodeValue2704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2704) = mixedMoment B node2704 node2704Labels := rfl
  simpa [nodeValue2704, Sparse.eval] using hc.symm

theorem sound2705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2705 node2705Labels = Sparse.eval nodeValue2705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2705) = mixedMoment B node2705 node2705Labels := rfl
  simpa [nodeValue2705, Sparse.eval] using hc.symm

theorem sound2719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2719 node2719Labels = Sparse.eval nodeValue2719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2719) = mixedMoment B node2719 node2719Labels := rfl
  simpa [nodeValue2719, Sparse.eval] using hc.symm

theorem sound2735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2735 node2735Labels = Sparse.eval nodeValue2735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2735) = mixedMoment B node2735 node2735Labels := rfl
  simpa [nodeValue2735, Sparse.eval] using hc.symm

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

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

theorem sound4089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4089 node4089Labels = Sparse.eval nodeValue4089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4089) = mixedMoment B node4089 node4089Labels := rfl
  simpa [nodeValue4089, Sparse.eval] using hc.symm

theorem sound4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4090 node4090Labels = Sparse.eval nodeValue4090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4090) = mixedMoment B node4090 node4090Labels := rfl
  simpa [nodeValue4090, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources52
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1682 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1682 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1682 + difference 0 1) (sourceB1682 + difference 1 0) sourceC1682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA1682 + difference 0 1) (sourceB1682 + difference 1 0) sourceC1682) = raw24747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1682 sourceB1682 sourceC1682 difference raw24747; decide +kernel
    rw [ha]
    exact (canonical24747 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1682 + difference 1 1) (sourceB1682 + difference 1 1) sourceC1682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1682 + difference 1 1) (sourceB1682 + difference 1 1) sourceC1682) = raw24740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1682 sourceB1682 sourceC1682 difference raw24740; decide +kernel
    rw [ha]
    exact (canonical24740 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1682 + difference 2 1) (sourceB1682 + difference 1 2) sourceC1682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1156) := by
    have ha : (tripleCharges (sourceA1682 + difference 2 1) (sourceB1682 + difference 1 2) sourceC1682) = raw24748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1682 sourceB1682 sourceC1682 difference raw24748; decide +kernel
    rw [ha]
    exact (canonical24748 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1682 + difference 3 1) (sourceB1682 + difference 1 3) sourceC1682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1149) := by
    have ha : (tripleCharges (sourceA1682 + difference 3 1) (sourceB1682 + difference 1 3) sourceC1682) = raw24749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1682 sourceB1682 sourceC1682 difference raw24749; decide +kernel
    rw [ha]
    exact (canonical24749 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1682 + difference 4 1) (sourceB1682 + difference 1 4) sourceC1682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1151) := by
    have ha : (tripleCharges (sourceA1682 + difference 4 1) (sourceB1682 + difference 1 4) sourceC1682) = raw24750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1682 sourceB1682 sourceC1682 difference raw24750; decide +kernel
    rw [ha]
    exact (canonical24750 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1682 + difference 5 1) (sourceB1682 + difference 1 5) sourceC1682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1148) := by
    have ha : (tripleCharges (sourceA1682 + difference 5 1) (sourceB1682 + difference 1 5) sourceC1682) = raw24751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1682 sourceB1682 sourceC1682 difference raw24751; decide +kernel
    rw [ha]
    exact (canonical24751 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1682 + sourceB1682) sourceC1682) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1682 + sourceB1682) sourceC1682) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA1682 sourceB1682 sourceC1682 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1682 sourceB1682 sourceC1682
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1682, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1686 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1686 + difference 0 0) (sourceB1686 + difference 0 0) sourceC1686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1229) := by
    have ha : (tripleCharges (sourceA1686 + difference 0 0) (sourceB1686 + difference 0 0) sourceC1686) = raw24826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1686 sourceB1686 sourceC1686 difference raw24826; decide +kernel
    rw [ha]
    exact (canonical24826 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1686 + difference 0 1) (sourceB1686 + difference 1 0) sourceC1686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2550) := by
    have ha : (tripleCharges (sourceA1686 + difference 0 1) (sourceB1686 + difference 1 0) sourceC1686) = raw24827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1686 sourceB1686 sourceC1686 difference raw24827; decide +kernel
    rw [ha]
    exact (canonical24827 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1686 + difference 0 2) (sourceB1686 + difference 2 0) sourceC1686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2504) := by
    have ha : (tripleCharges (sourceA1686 + difference 0 2) (sourceB1686 + difference 2 0) sourceC1686) = raw24828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1686 sourceB1686 sourceC1686 difference raw24828; decide +kernel
    rw [ha]
    exact (canonical24828 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1686 + difference 0 3) (sourceB1686 + difference 3 0) sourceC1686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA1686 + difference 0 3) (sourceB1686 + difference 3 0) sourceC1686) = raw24829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1686 sourceB1686 sourceC1686 difference raw24829; decide +kernel
    rw [ha]
    exact (canonical24829 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1686 + difference 0 4) (sourceB1686 + difference 4 0) sourceC1686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA1686 + difference 0 4) (sourceB1686 + difference 4 0) sourceC1686) = raw24830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1686 sourceB1686 sourceC1686 difference raw24830; decide +kernel
    rw [ha]
    exact (canonical24830 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1686 + difference 0 5) (sourceB1686 + difference 5 0) sourceC1686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA1686 + difference 0 5) (sourceB1686 + difference 5 0) sourceC1686) = raw24831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1686 sourceB1686 sourceC1686 difference raw24831; decide +kernel
    rw [ha]
    exact (canonical24831 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1686 + sourceB1686) sourceC1686) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1686 + sourceB1686) sourceC1686) = raw24832 := by
      apply Matrix.ext; unfold doubleCharges sourceA1686 sourceB1686 sourceC1686 raw24832; decide +kernel
    rw [ha]
    exact (canonical24832 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1686 sourceB1686 sourceC1686
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1686, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1688 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1688 + difference 0 5) (sourceB1688 + difference 5 0) sourceC1688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA1688 + difference 0 5) (sourceB1688 + difference 5 0) sourceC1688) = raw24838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1688 sourceB1688 sourceC1688 difference raw24838; decide +kernel
    rw [ha]
    exact (canonical24838 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1688 + difference 1 5) (sourceB1688 + difference 5 1) sourceC1688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1183) := by
    have ha : (tripleCharges (sourceA1688 + difference 1 5) (sourceB1688 + difference 5 1) sourceC1688) = raw24840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1688 sourceB1688 sourceC1688 difference raw24840; decide +kernel
    rw [ha]
    exact (canonical24840 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1688 + difference 2 5) (sourceB1688 + difference 5 2) sourceC1688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1286) := by
    have ha : (tripleCharges (sourceA1688 + difference 2 5) (sourceB1688 + difference 5 2) sourceC1688) = raw24841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1688 sourceB1688 sourceC1688 difference raw24841; decide +kernel
    rw [ha]
    exact (canonical24841 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1688 + difference 3 5) (sourceB1688 + difference 5 3) sourceC1688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1688 + difference 3 5) (sourceB1688 + difference 5 3) sourceC1688) = raw24842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1688 sourceB1688 sourceC1688 difference raw24842; decide +kernel
    rw [ha]
    exact (canonical24842 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1688 + difference 4 5) (sourceB1688 + difference 5 4) sourceC1688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1189) := by
    have ha : (tripleCharges (sourceA1688 + difference 4 5) (sourceB1688 + difference 5 4) sourceC1688) = raw24843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1688 sourceB1688 sourceC1688 difference raw24843; decide +kernel
    rw [ha]
    exact (canonical24843 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1688 + difference 5 5) (sourceB1688 + difference 5 5) sourceC1688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1189) := by
    have ha : (tripleCharges (sourceA1688 + difference 5 5) (sourceB1688 + difference 5 5) sourceC1688) = raw24833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1688 sourceB1688 sourceC1688 difference raw24833; decide +kernel
    rw [ha]
    exact (canonical24833 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1688 + sourceB1688) sourceC1688) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1688 + sourceB1688) sourceC1688) = raw24839 := by
      apply Matrix.ext; unfold doubleCharges sourceA1688 sourceB1688 sourceC1688 raw24839; decide +kernel
    rw [ha]
    exact (canonical24839 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1688 sourceB1688 sourceC1688
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1688, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1689 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1689 + difference 0 0) (sourceB1689 + difference 0 0) sourceC1689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1185) := by
    have ha : (tripleCharges (sourceA1689 + difference 0 0) (sourceB1689 + difference 0 0) sourceC1689) = raw24844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1689 sourceB1689 sourceC1689 difference raw24844; decide +kernel
    rw [ha]
    exact (canonical24844 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1689 + difference 0 1) (sourceB1689 + difference 1 0) sourceC1689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2535) := by
    have ha : (tripleCharges (sourceA1689 + difference 0 1) (sourceB1689 + difference 1 0) sourceC1689) = raw24845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1689 sourceB1689 sourceC1689 difference raw24845; decide +kernel
    rw [ha]
    exact (canonical24845 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1689 + difference 0 2) (sourceB1689 + difference 2 0) sourceC1689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2400) := by
    have ha : (tripleCharges (sourceA1689 + difference 0 2) (sourceB1689 + difference 2 0) sourceC1689) = raw24846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1689 sourceB1689 sourceC1689 difference raw24846; decide +kernel
    rw [ha]
    exact (canonical24846 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1689 + difference 0 3) (sourceB1689 + difference 3 0) sourceC1689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA1689 + difference 0 3) (sourceB1689 + difference 3 0) sourceC1689) = raw24847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1689 sourceB1689 sourceC1689 difference raw24847; decide +kernel
    rw [ha]
    exact (canonical24847 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1689 + difference 0 4) (sourceB1689 + difference 4 0) sourceC1689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA1689 + difference 0 4) (sourceB1689 + difference 4 0) sourceC1689) = raw24848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1689 sourceB1689 sourceC1689 difference raw24848; decide +kernel
    rw [ha]
    exact (canonical24848 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1689 + difference 0 5) (sourceB1689 + difference 5 0) sourceC1689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA1689 + difference 0 5) (sourceB1689 + difference 5 0) sourceC1689) = raw24849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1689 sourceB1689 sourceC1689 difference raw24849; decide +kernel
    rw [ha]
    exact (canonical24849 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1689 + sourceB1689) sourceC1689) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA1689 + sourceB1689) sourceC1689) = raw24850 := by
      apply Matrix.ext; unfold doubleCharges sourceA1689 sourceB1689 sourceC1689 raw24850; decide +kernel
    rw [ha]
    exact (canonical24850 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1689 sourceB1689 sourceC1689
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1689, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1690 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1690 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1690 + difference 0 0) (sourceB1690 + difference 0 0) sourceC1690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1690 + difference 0 0) (sourceB1690 + difference 0 0) sourceC1690) = raw24851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1690 sourceB1690 sourceC1690 difference raw24851; decide +kernel
    rw [ha]
    exact (canonical24851 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1690 + difference 0 1) (sourceB1690 + difference 1 0) sourceC1690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2536) := by
    have ha : (tripleCharges (sourceA1690 + difference 0 1) (sourceB1690 + difference 1 0) sourceC1690) = raw24852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1690 sourceB1690 sourceC1690 difference raw24852; decide +kernel
    rw [ha]
    exact (canonical24852 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1690 + difference 0 2) (sourceB1690 + difference 2 0) sourceC1690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2403) := by
    have ha : (tripleCharges (sourceA1690 + difference 0 2) (sourceB1690 + difference 2 0) sourceC1690) = raw24853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1690 sourceB1690 sourceC1690 difference raw24853; decide +kernel
    rw [ha]
    exact (canonical24853 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1690 + difference 0 3) (sourceB1690 + difference 3 0) sourceC1690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1690 + difference 0 3) (sourceB1690 + difference 3 0) sourceC1690) = raw24854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1690 sourceB1690 sourceC1690 difference raw24854; decide +kernel
    rw [ha]
    exact (canonical24854 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1690 + difference 0 4) (sourceB1690 + difference 4 0) sourceC1690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1690 + difference 0 4) (sourceB1690 + difference 4 0) sourceC1690) = raw24855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1690 sourceB1690 sourceC1690 difference raw24855; decide +kernel
    rw [ha]
    exact (canonical24855 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1690 + difference 0 5) (sourceB1690 + difference 5 0) sourceC1690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA1690 + difference 0 5) (sourceB1690 + difference 5 0) sourceC1690) = raw24856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1690 sourceB1690 sourceC1690 difference raw24856; decide +kernel
    rw [ha]
    exact (canonical24856 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1690 + sourceB1690) sourceC1690) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1690 + sourceB1690) sourceC1690) = raw24857 := by
      apply Matrix.ext; unfold doubleCharges sourceA1690 sourceB1690 sourceC1690 raw24857; decide +kernel
    rw [ha]
    exact (canonical24857 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1690 sourceB1690 sourceC1690
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1690, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1693 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1693 + difference 0 0) (sourceB1693 + difference 0 0) sourceC1693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1184) := by
    have ha : (tripleCharges (sourceA1693 + difference 0 0) (sourceB1693 + difference 0 0) sourceC1693) = raw24868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1693 sourceB1693 sourceC1693 difference raw24868; decide +kernel
    rw [ha]
    exact (canonical24868 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1693 + difference 0 1) (sourceB1693 + difference 1 0) sourceC1693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2534) := by
    have ha : (tripleCharges (sourceA1693 + difference 0 1) (sourceB1693 + difference 1 0) sourceC1693) = raw24869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1693 sourceB1693 sourceC1693 difference raw24869; decide +kernel
    rw [ha]
    exact (canonical24869 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1693 + difference 0 2) (sourceB1693 + difference 2 0) sourceC1693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2399) := by
    have ha : (tripleCharges (sourceA1693 + difference 0 2) (sourceB1693 + difference 2 0) sourceC1693) = raw24870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1693 sourceB1693 sourceC1693 difference raw24870; decide +kernel
    rw [ha]
    exact (canonical24870 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1693 + difference 0 3) (sourceB1693 + difference 3 0) sourceC1693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA1693 + difference 0 3) (sourceB1693 + difference 3 0) sourceC1693) = raw24871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1693 sourceB1693 sourceC1693 difference raw24871; decide +kernel
    rw [ha]
    exact (canonical24871 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1693 + difference 0 4) (sourceB1693 + difference 4 0) sourceC1693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA1693 + difference 0 4) (sourceB1693 + difference 4 0) sourceC1693) = raw24872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1693 sourceB1693 sourceC1693 difference raw24872; decide +kernel
    rw [ha]
    exact (canonical24872 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1693 + difference 0 5) (sourceB1693 + difference 5 0) sourceC1693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA1693 + difference 0 5) (sourceB1693 + difference 5 0) sourceC1693) = raw24873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1693 sourceB1693 sourceC1693 difference raw24873; decide +kernel
    rw [ha]
    exact (canonical24873 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1693 + sourceB1693) sourceC1693) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1693 + sourceB1693) sourceC1693) = raw24874 := by
      apply Matrix.ext; unfold doubleCharges sourceA1693 sourceB1693 sourceC1693 raw24874; decide +kernel
    rw [ha]
    exact (canonical24874 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1693 sourceB1693 sourceC1693
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1693, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1695 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1695 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1695 + difference 0 5) (sourceB1695 + difference 5 0) sourceC1695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA1695 + difference 0 5) (sourceB1695 + difference 5 0) sourceC1695) = raw24880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1695 sourceB1695 sourceC1695 difference raw24880; decide +kernel
    rw [ha]
    exact (canonical24880 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1695 + difference 1 5) (sourceB1695 + difference 5 1) sourceC1695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA1695 + difference 1 5) (sourceB1695 + difference 5 1) sourceC1695) = raw24882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1695 sourceB1695 sourceC1695 difference raw24882; decide +kernel
    rw [ha]
    exact (canonical24882 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1695 + difference 2 5) (sourceB1695 + difference 5 2) sourceC1695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA1695 + difference 2 5) (sourceB1695 + difference 5 2) sourceC1695) = raw24883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1695 sourceB1695 sourceC1695 difference raw24883; decide +kernel
    rw [ha]
    exact (canonical24883 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1695 + difference 3 5) (sourceB1695 + difference 5 3) sourceC1695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1695 + difference 3 5) (sourceB1695 + difference 5 3) sourceC1695) = raw24884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1695 sourceB1695 sourceC1695 difference raw24884; decide +kernel
    rw [ha]
    exact (canonical24884 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1695 + difference 4 5) (sourceB1695 + difference 5 4) sourceC1695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1201) := by
    have ha : (tripleCharges (sourceA1695 + difference 4 5) (sourceB1695 + difference 5 4) sourceC1695) = raw24885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1695 sourceB1695 sourceC1695 difference raw24885; decide +kernel
    rw [ha]
    exact (canonical24885 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1695 + difference 5 5) (sourceB1695 + difference 5 5) sourceC1695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1201) := by
    have ha : (tripleCharges (sourceA1695 + difference 5 5) (sourceB1695 + difference 5 5) sourceC1695) = raw24875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1695 sourceB1695 sourceC1695 difference raw24875; decide +kernel
    rw [ha]
    exact (canonical24875 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1695 + sourceB1695) sourceC1695) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1695 + sourceB1695) sourceC1695) = raw24881 := by
      apply Matrix.ext; unfold doubleCharges sourceA1695 sourceB1695 sourceC1695 raw24881; decide +kernel
    rw [ha]
    exact (canonical24881 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1695 sourceB1695 sourceC1695
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1695, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources53
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1696 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1696 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1696 + difference 0 0) (sourceB1696 + difference 0 0) sourceC1696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1198) := by
    have ha : (tripleCharges (sourceA1696 + difference 0 0) (sourceB1696 + difference 0 0) sourceC1696) = raw24886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1696 sourceB1696 sourceC1696 difference raw24886; decide +kernel
    rw [ha]
    exact (canonical24886 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1696 + difference 0 1) (sourceB1696 + difference 1 0) sourceC1696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA1696 + difference 0 1) (sourceB1696 + difference 1 0) sourceC1696) = raw24887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1696 sourceB1696 sourceC1696 difference raw24887; decide +kernel
    rw [ha]
    exact (canonical24887 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1696 + difference 0 2) (sourceB1696 + difference 2 0) sourceC1696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA1696 + difference 0 2) (sourceB1696 + difference 2 0) sourceC1696) = raw24888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1696 sourceB1696 sourceC1696 difference raw24888; decide +kernel
    rw [ha]
    exact (canonical24888 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1696 + difference 0 3) (sourceB1696 + difference 3 0) sourceC1696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA1696 + difference 0 3) (sourceB1696 + difference 3 0) sourceC1696) = raw24889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1696 sourceB1696 sourceC1696 difference raw24889; decide +kernel
    rw [ha]
    exact (canonical24889 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1696 + difference 0 4) (sourceB1696 + difference 4 0) sourceC1696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA1696 + difference 0 4) (sourceB1696 + difference 4 0) sourceC1696) = raw24890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1696 sourceB1696 sourceC1696 difference raw24890; decide +kernel
    rw [ha]
    exact (canonical24890 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1696 + difference 0 5) (sourceB1696 + difference 5 0) sourceC1696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2701) := by
    have ha : (tripleCharges (sourceA1696 + difference 0 5) (sourceB1696 + difference 5 0) sourceC1696) = raw24891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1696 sourceB1696 sourceC1696 difference raw24891; decide +kernel
    rw [ha]
    exact (canonical24891 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1696 + sourceB1696) sourceC1696) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1696 + sourceB1696) sourceC1696) = raw24892 := by
      apply Matrix.ext; unfold doubleCharges sourceA1696 sourceB1696 sourceC1696 raw24892; decide +kernel
    rw [ha]
    exact (canonical24892 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1696 sourceB1696 sourceC1696
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1696, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1697 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1697 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1697 + difference 0 0) (sourceB1697 + difference 0 0) sourceC1697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1697 + difference 0 0) (sourceB1697 + difference 0 0) sourceC1697) = raw24893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1697 sourceB1697 sourceC1697 difference raw24893; decide +kernel
    rw [ha]
    exact (canonical24893 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1697 + difference 0 1) (sourceB1697 + difference 1 0) sourceC1697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2461) := by
    have ha : (tripleCharges (sourceA1697 + difference 0 1) (sourceB1697 + difference 1 0) sourceC1697) = raw24894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1697 sourceB1697 sourceC1697 difference raw24894; decide +kernel
    rw [ha]
    exact (canonical24894 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1697 + difference 0 2) (sourceB1697 + difference 2 0) sourceC1697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2461) := by
    have ha : (tripleCharges (sourceA1697 + difference 0 2) (sourceB1697 + difference 2 0) sourceC1697) = raw24895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1697 sourceB1697 sourceC1697 difference raw24895; decide +kernel
    rw [ha]
    exact (canonical24895 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1697 + difference 0 3) (sourceB1697 + difference 3 0) sourceC1697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1697 + difference 0 3) (sourceB1697 + difference 3 0) sourceC1697) = raw24896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1697 sourceB1697 sourceC1697 difference raw24896; decide +kernel
    rw [ha]
    exact (canonical24896 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1697 + difference 0 4) (sourceB1697 + difference 4 0) sourceC1697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1697 + difference 0 4) (sourceB1697 + difference 4 0) sourceC1697) = raw24897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1697 sourceB1697 sourceC1697 difference raw24897; decide +kernel
    rw [ha]
    exact (canonical24897 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1697 + difference 0 5) (sourceB1697 + difference 5 0) sourceC1697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA1697 + difference 0 5) (sourceB1697 + difference 5 0) sourceC1697) = raw24898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1697 sourceB1697 sourceC1697 difference raw24898; decide +kernel
    rw [ha]
    exact (canonical24898 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1697 + sourceB1697) sourceC1697) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1697 + sourceB1697) sourceC1697) = raw24899 := by
      apply Matrix.ext; unfold doubleCharges sourceA1697 sourceB1697 sourceC1697 raw24899; decide +kernel
    rw [ha]
    exact (canonical24899 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1697 sourceB1697 sourceC1697
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1697, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1700 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1700 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1700 + difference 0 0) (sourceB1700 + difference 0 0) sourceC1700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1197) := by
    have ha : (tripleCharges (sourceA1700 + difference 0 0) (sourceB1700 + difference 0 0) sourceC1700) = raw24909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1700 sourceB1700 sourceC1700 difference raw24909; decide +kernel
    rw [ha]
    exact (canonical24909 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1700 + difference 0 1) (sourceB1700 + difference 1 0) sourceC1700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2458) := by
    have ha : (tripleCharges (sourceA1700 + difference 0 1) (sourceB1700 + difference 1 0) sourceC1700) = raw24910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1700 sourceB1700 sourceC1700 difference raw24910; decide +kernel
    rw [ha]
    exact (canonical24910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1700 + difference 0 2) (sourceB1700 + difference 2 0) sourceC1700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2458) := by
    have ha : (tripleCharges (sourceA1700 + difference 0 2) (sourceB1700 + difference 2 0) sourceC1700) = raw24911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1700 sourceB1700 sourceC1700 difference raw24911; decide +kernel
    rw [ha]
    exact (canonical24911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1700 + difference 0 3) (sourceB1700 + difference 3 0) sourceC1700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA1700 + difference 0 3) (sourceB1700 + difference 3 0) sourceC1700) = raw24912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1700 sourceB1700 sourceC1700 difference raw24912; decide +kernel
    rw [ha]
    exact (canonical24912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1700 + difference 0 4) (sourceB1700 + difference 4 0) sourceC1700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA1700 + difference 0 4) (sourceB1700 + difference 4 0) sourceC1700) = raw24913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1700 sourceB1700 sourceC1700 difference raw24913; decide +kernel
    rw [ha]
    exact (canonical24913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1700 + difference 0 5) (sourceB1700 + difference 5 0) sourceC1700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA1700 + difference 0 5) (sourceB1700 + difference 5 0) sourceC1700) = raw24914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1700 sourceB1700 sourceC1700 difference raw24914; decide +kernel
    rw [ha]
    exact (canonical24914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1700 + sourceB1700) sourceC1700) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1700 + sourceB1700) sourceC1700) = raw24915 := by
      apply Matrix.ext; unfold doubleCharges sourceA1700 sourceB1700 sourceC1700 raw24915; decide +kernel
    rw [ha]
    exact (canonical24915 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1700 sourceB1700 sourceC1700
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1700, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1702 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1702 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1702 + difference 0 5) (sourceB1702 + difference 5 0) sourceC1702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA1702 + difference 0 5) (sourceB1702 + difference 5 0) sourceC1702) = raw24921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1702 sourceB1702 sourceC1702 difference raw24921; decide +kernel
    rw [ha]
    exact (canonical24921 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1702 + difference 1 5) (sourceB1702 + difference 5 1) sourceC1702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1702 + difference 1 5) (sourceB1702 + difference 5 1) sourceC1702) = raw24923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1702 sourceB1702 sourceC1702 difference raw24923; decide +kernel
    rw [ha]
    exact (canonical24923 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1702 + difference 2 5) (sourceB1702 + difference 5 2) sourceC1702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1052) := by
    have ha : (tripleCharges (sourceA1702 + difference 2 5) (sourceB1702 + difference 5 2) sourceC1702) = raw24924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1702 sourceB1702 sourceC1702 difference raw24924; decide +kernel
    rw [ha]
    exact (canonical24924 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1702 + difference 3 5) (sourceB1702 + difference 5 3) sourceC1702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1054) := by
    have ha : (tripleCharges (sourceA1702 + difference 3 5) (sourceB1702 + difference 5 3) sourceC1702) = raw24925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1702 sourceB1702 sourceC1702 difference raw24925; decide +kernel
    rw [ha]
    exact (canonical24925 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1702 + difference 4 5) (sourceB1702 + difference 5 4) sourceC1702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1054) := by
    have ha : (tripleCharges (sourceA1702 + difference 4 5) (sourceB1702 + difference 5 4) sourceC1702) = raw24926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1702 sourceB1702 sourceC1702 difference raw24926; decide +kernel
    rw [ha]
    exact (canonical24926 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1702 + difference 5 5) (sourceB1702 + difference 5 5) sourceC1702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1060) := by
    have ha : (tripleCharges (sourceA1702 + difference 5 5) (sourceB1702 + difference 5 5) sourceC1702) = raw24916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1702 sourceB1702 sourceC1702 difference raw24916; decide +kernel
    rw [ha]
    exact (canonical24916 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1702 + sourceB1702) sourceC1702) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1702 + sourceB1702) sourceC1702) = raw24922 := by
      apply Matrix.ext; unfold doubleCharges sourceA1702 sourceB1702 sourceC1702 raw24922; decide +kernel
    rw [ha]
    exact (canonical24922 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1702 sourceB1702 sourceC1702
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1702, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1703 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1703 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1703 + difference 0 0) (sourceB1703 + difference 0 0) sourceC1703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1054) := by
    have ha : (tripleCharges (sourceA1703 + difference 0 0) (sourceB1703 + difference 0 0) sourceC1703) = raw24927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1703 sourceB1703 sourceC1703 difference raw24927; decide +kernel
    rw [ha]
    exact (canonical24927 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1703 + difference 0 1) (sourceB1703 + difference 1 0) sourceC1703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2129) := by
    have ha : (tripleCharges (sourceA1703 + difference 0 1) (sourceB1703 + difference 1 0) sourceC1703) = raw24928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1703 sourceB1703 sourceC1703 difference raw24928; decide +kernel
    rw [ha]
    exact (canonical24928 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1703 + difference 0 2) (sourceB1703 + difference 2 0) sourceC1703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2031) := by
    have ha : (tripleCharges (sourceA1703 + difference 0 2) (sourceB1703 + difference 2 0) sourceC1703) = raw24929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1703 sourceB1703 sourceC1703 difference raw24929; decide +kernel
    rw [ha]
    exact (canonical24929 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1703 + difference 0 3) (sourceB1703 + difference 3 0) sourceC1703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA1703 + difference 0 3) (sourceB1703 + difference 3 0) sourceC1703) = raw24930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1703 sourceB1703 sourceC1703 difference raw24930; decide +kernel
    rw [ha]
    exact (canonical24930 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1703 + difference 0 4) (sourceB1703 + difference 4 0) sourceC1703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1703 + difference 0 4) (sourceB1703 + difference 4 0) sourceC1703) = raw24931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1703 sourceB1703 sourceC1703 difference raw24931; decide +kernel
    rw [ha]
    exact (canonical24931 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1703 + difference 0 5) (sourceB1703 + difference 5 0) sourceC1703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA1703 + difference 0 5) (sourceB1703 + difference 5 0) sourceC1703) = raw24932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1703 sourceB1703 sourceC1703 difference raw24932; decide +kernel
    rw [ha]
    exact (canonical24932 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1703 + sourceB1703) sourceC1703) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1703 + sourceB1703) sourceC1703) = raw24933 := by
      apply Matrix.ext; unfold doubleCharges sourceA1703 sourceB1703 sourceC1703 raw24933; decide +kernel
    rw [ha]
    exact (canonical24933 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1703 sourceB1703 sourceC1703
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1703, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1704 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1704 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1704 + difference 0 0) (sourceB1704 + difference 0 0) sourceC1704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1053) := by
    have ha : (tripleCharges (sourceA1704 + difference 0 0) (sourceB1704 + difference 0 0) sourceC1704) = raw21087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1704 sourceB1704 sourceC1704 difference raw21087; decide +kernel
    rw [ha]
    exact (canonical21087 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1704 + difference 0 1) (sourceB1704 + difference 1 0) sourceC1704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2128) := by
    have ha : (tripleCharges (sourceA1704 + difference 0 1) (sourceB1704 + difference 1 0) sourceC1704) = raw24934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1704 sourceB1704 sourceC1704 difference raw24934; decide +kernel
    rw [ha]
    exact (canonical24934 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1704 + difference 0 2) (sourceB1704 + difference 2 0) sourceC1704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2030) := by
    have ha : (tripleCharges (sourceA1704 + difference 0 2) (sourceB1704 + difference 2 0) sourceC1704) = raw24935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1704 sourceB1704 sourceC1704 difference raw24935; decide +kernel
    rw [ha]
    exact (canonical24935 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1704 + difference 0 3) (sourceB1704 + difference 3 0) sourceC1704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA1704 + difference 0 3) (sourceB1704 + difference 3 0) sourceC1704) = raw21083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1704 sourceB1704 sourceC1704 difference raw21083; decide +kernel
    rw [ha]
    exact (canonical21083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1704 + difference 0 4) (sourceB1704 + difference 4 0) sourceC1704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1704 + difference 0 4) (sourceB1704 + difference 4 0) sourceC1704) = raw24936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1704 sourceB1704 sourceC1704 difference raw24936; decide +kernel
    rw [ha]
    exact (canonical24936 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1704 + difference 0 5) (sourceB1704 + difference 5 0) sourceC1704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA1704 + difference 0 5) (sourceB1704 + difference 5 0) sourceC1704) = raw24937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1704 sourceB1704 sourceC1704 difference raw24937; decide +kernel
    rw [ha]
    exact (canonical24937 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1704 + sourceB1704) sourceC1704) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1704 + sourceB1704) sourceC1704) = raw21084 := by
      apply Matrix.ext; unfold doubleCharges sourceA1704 sourceB1704 sourceC1704 raw21084; decide +kernel
    rw [ha]
    exact (canonical21084 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1704 sourceB1704 sourceC1704
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1704, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1706 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1706 + difference 0 5) (sourceB1706 + difference 5 0) sourceC1706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA1706 + difference 0 5) (sourceB1706 + difference 5 0) sourceC1706) = raw24943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1706 sourceB1706 sourceC1706 difference raw24943; decide +kernel
    rw [ha]
    exact (canonical24943 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1706 + difference 1 5) (sourceB1706 + difference 5 1) sourceC1706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1706 + difference 1 5) (sourceB1706 + difference 5 1) sourceC1706) = raw24945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1706 sourceB1706 sourceC1706 difference raw24945; decide +kernel
    rw [ha]
    exact (canonical24945 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1706 + difference 2 5) (sourceB1706 + difference 5 2) sourceC1706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1052) := by
    have ha : (tripleCharges (sourceA1706 + difference 2 5) (sourceB1706 + difference 5 2) sourceC1706) = raw24946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1706 sourceB1706 sourceC1706 difference raw24946; decide +kernel
    rw [ha]
    exact (canonical24946 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1706 + difference 3 5) (sourceB1706 + difference 5 3) sourceC1706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA1706 + difference 3 5) (sourceB1706 + difference 5 3) sourceC1706) = raw24947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1706 sourceB1706 sourceC1706 difference raw24947; decide +kernel
    rw [ha]
    exact (canonical24947 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1706 + difference 4 5) (sourceB1706 + difference 5 4) sourceC1706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA1706 + difference 4 5) (sourceB1706 + difference 5 4) sourceC1706) = raw24948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1706 sourceB1706 sourceC1706 difference raw24948; decide +kernel
    rw [ha]
    exact (canonical24948 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1706 + difference 5 5) (sourceB1706 + difference 5 5) sourceC1706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 990) := by
    have ha : (tripleCharges (sourceA1706 + difference 5 5) (sourceB1706 + difference 5 5) sourceC1706) = raw24938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1706 sourceB1706 sourceC1706 difference raw24938; decide +kernel
    rw [ha]
    exact (canonical24938 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1706 + sourceB1706) sourceC1706) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1706 + sourceB1706) sourceC1706) = raw24944 := by
      apply Matrix.ext; unfold doubleCharges sourceA1706 sourceB1706 sourceC1706 raw24944; decide +kernel
    rw [ha]
    exact (canonical24944 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1706 sourceB1706 sourceC1706
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1706, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1440 : Integer.Sparse.reindex keyMap MixedData.row1440 = numericRow1440 := by decide +kernel

theorem numericCheck1440 (x : Master → ℝ) : Integer.Sparse.eval numericRow1440 x =
    (1 : ℝ) * reducedSource1440 x := by
  norm_num [numericRow1440, reducedSource1440, Integer.Sparse.eval, Sparse.eval, nodeValue1148, nodeValue1149, nodeValue1151, nodeValue1156, nodeValue1236, nodeValue2553, nodeValue4092]

theorem reindexCheck1443 : Integer.Sparse.reindex keyMap MixedData.row1443 = numericRow1443 := by decide +kernel

theorem numericCheck1443 (x : Master → ℝ) : Integer.Sparse.eval numericRow1443 x =
    (1 : ℝ) * reducedSource1443 x := by
  norm_num [numericRow1443, reducedSource1443, Integer.Sparse.eval, Sparse.eval, nodeValue1229, nodeValue2504, nodeValue2550, nodeValue2704, nodeValue2719, nodeValue2735, nodeValue4080]

theorem reindexCheck1444 : Integer.Sparse.reindex keyMap MixedData.row1444 = numericRow1444 := by decide +kernel

theorem numericCheck1444 (x : Master → ℝ) : Integer.Sparse.eval numericRow1444 x =
    (1 : ℝ) * reducedSource1444 x := by
  norm_num [numericRow1444, reducedSource1444, Integer.Sparse.eval, Sparse.eval, nodeValue1183, nodeValue1188, nodeValue1189, nodeValue1286, nodeValue2684, nodeValue4088]

theorem reindexCheck1445 : Integer.Sparse.reindex keyMap MixedData.row1445 = numericRow1445 := by decide +kernel

theorem numericCheck1445 (x : Master → ℝ) : Integer.Sparse.eval numericRow1445 x =
    (1 : ℝ) * reducedSource1445 x := by
  norm_num [numericRow1445, reducedSource1445, Integer.Sparse.eval, Sparse.eval, nodeValue1185, nodeValue2400, nodeValue2535, nodeValue2677, nodeValue2682, nodeValue2686, nodeValue4089]

theorem reindexCheck1446 : Integer.Sparse.reindex keyMap MixedData.row1446 = numericRow1446 := by decide +kernel

theorem numericCheck1446 (x : Master → ℝ) : Integer.Sparse.eval numericRow1446 x =
    (1 : ℝ) * reducedSource1446 x := by
  norm_num [numericRow1446, reducedSource1446, Integer.Sparse.eval, Sparse.eval, nodeValue1188, nodeValue2403, nodeValue2536, nodeValue2672, nodeValue2684, nodeValue4088]

theorem reindexCheck1447 : Integer.Sparse.reindex keyMap MixedData.row1447 = numericRow1447 := by decide +kernel

theorem numericCheck1447 (x : Master → ℝ) : Integer.Sparse.eval numericRow1447 x =
    (1 : ℝ) * reducedSource1447 x := by
  norm_num [numericRow1447, reducedSource1447, Integer.Sparse.eval, Sparse.eval, nodeValue1184, nodeValue2399, nodeValue2534, nodeValue2670, nodeValue2681, nodeValue2685, nodeValue4082]

theorem reindexCheck1448 : Integer.Sparse.reindex keyMap MixedData.row1448 = numericRow1448 := by decide +kernel

theorem numericCheck1448 (x : Master → ℝ) : Integer.Sparse.eval numericRow1448 x =
    (1 : ℝ) * reducedSource1448 x := by
  norm_num [numericRow1448, reducedSource1448, Integer.Sparse.eval, Sparse.eval, nodeValue1200, nodeValue1201, nodeValue1228, nodeValue2703, nodeValue4090]

theorem reindexCheck1449 : Integer.Sparse.reindex keyMap MixedData.row1449 = numericRow1449 := by decide +kernel

theorem numericCheck1449 (x : Master → ℝ) : Integer.Sparse.eval numericRow1449 x =
    (1 : ℝ) * reducedSource1449 x := by
  norm_num [numericRow1449, reducedSource1449, Integer.Sparse.eval, Sparse.eval, nodeValue1198, nodeValue2459, nodeValue2697, nodeValue2701, nodeValue2705, nodeValue4088]

theorem reindexCheck1450 : Integer.Sparse.reindex keyMap MixedData.row1450 = numericRow1450 := by decide +kernel

theorem numericCheck1450 (x : Master → ℝ) : Integer.Sparse.eval numericRow1450 x =
    (1 : ℝ) * reducedSource1450 x := by
  norm_num [numericRow1450, reducedSource1450, Integer.Sparse.eval, Sparse.eval, nodeValue1200, nodeValue2461, nodeValue2694, nodeValue2703, nodeValue4090]

theorem reindexCheck1451 : Integer.Sparse.reindex keyMap MixedData.row1451 = numericRow1451 := by decide +kernel

theorem numericCheck1451 (x : Master → ℝ) : Integer.Sparse.eval numericRow1451 x =
    (1 : ℝ) * reducedSource1451 x := by
  norm_num [numericRow1451, reducedSource1451, Integer.Sparse.eval, Sparse.eval, nodeValue1197, nodeValue2458, nodeValue2693, nodeValue2700, nodeValue2704, nodeValue4080]

theorem reindexCheck1452 : Integer.Sparse.reindex keyMap MixedData.row1452 = numericRow1452 := by decide +kernel

theorem numericCheck1452 (x : Master → ℝ) : Integer.Sparse.eval numericRow1452 x =
    (1 : ℝ) * reducedSource1452 x := by
  norm_num [numericRow1452, reducedSource1452, Integer.Sparse.eval, Sparse.eval, nodeValue1052, nodeValue1054, nodeValue1060, nodeValue1073, nodeValue2275, nodeValue4080]

theorem reindexCheck1453 : Integer.Sparse.reindex keyMap MixedData.row1453 = numericRow1453 := by decide +kernel

theorem numericCheck1453 (x : Master → ℝ) : Integer.Sparse.eval numericRow1453 x =
    (1 : ℝ) * reducedSource1453 x := by
  norm_num [numericRow1453, reducedSource1453, Integer.Sparse.eval, Sparse.eval, nodeValue1054, nodeValue2031, nodeValue2129, nodeValue2216, nodeValue2251, nodeValue2275, nodeValue4080]

theorem reindexCheck1454 : Integer.Sparse.reindex keyMap MixedData.row1454 = numericRow1454 := by decide +kernel

theorem numericCheck1454 (x : Master → ℝ) : Integer.Sparse.eval numericRow1454 x =
    (1 : ℝ) * reducedSource1454 x := by
  norm_num [numericRow1454, reducedSource1454, Integer.Sparse.eval, Sparse.eval, nodeValue1053, nodeValue2030, nodeValue2128, nodeValue2215, nodeValue2274, nodeValue2276, nodeValue4082]

theorem reindexCheck1455 : Integer.Sparse.reindex keyMap MixedData.row1455 = numericRow1455 := by decide +kernel

theorem numericCheck1455 (x : Master → ℝ) : Integer.Sparse.eval numericRow1455 x =
    (1 : ℝ) * reducedSource1455 x := by
  norm_num [numericRow1455, reducedSource1455, Integer.Sparse.eval, Sparse.eval, nodeValue988, nodeValue990, nodeValue998, nodeValue1052, nodeValue2214, nodeValue4080]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1440 (mixedVector B) = 0 := by
  have h1148 : mixedVector B (Sum.inr 1148) = Sparse.eval nodeValue1148 (mixedVector B) := by
    change mixedMoment B node1148 node1148Labels = _
    exact sound1148 B hB hF
  have h1149 : mixedVector B (Sum.inr 1149) = Sparse.eval nodeValue1149 (mixedVector B) := by
    change mixedMoment B node1149 node1149Labels = _
    exact sound1149 B hB hF
  have h1151 : mixedVector B (Sum.inr 1151) = Sparse.eval nodeValue1151 (mixedVector B) := by
    change mixedMoment B node1151 node1151Labels = _
    exact sound1151 B hB hF
  have h1156 : mixedVector B (Sum.inr 1156) = Sparse.eval nodeValue1156 (mixedVector B) := by
    change mixedMoment B node1156 node1156Labels = _
    exact sound1156 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1682, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1148, h1149, h1151, h1156, h1236, h2553, h4092, reducedSource1440] using sourceEq1682 B hB

theorem rowSound1440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1440 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1440, numericCheck1440, reducedZero1440 B hB hF, mul_zero]

theorem reducedZero1443 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1443 (mixedVector B) = 0 := by
  have h1229 : mixedVector B (Sum.inr 1229) = Sparse.eval nodeValue1229 (mixedVector B) := by
    change mixedMoment B node1229 node1229Labels = _
    exact sound1229 B hB hF
  have h2504 : mixedVector B (Sum.inr 2504) = Sparse.eval nodeValue2504 (mixedVector B) := by
    change mixedMoment B node2504 node2504Labels = _
    exact sound2504 B hB hF
  have h2550 : mixedVector B (Sum.inr 2550) = Sparse.eval nodeValue2550 (mixedVector B) := by
    change mixedMoment B node2550 node2550Labels = _
    exact sound2550 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1686, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1229, h2504, h2550, h2704, h2719, h2735, h4080, reducedSource1443] using sourceEq1686 B hB

theorem rowSound1443 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1443 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1443, numericCheck1443, reducedZero1443 B hB hF, mul_zero]

theorem reducedZero1444 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1444 (mixedVector B) = 0 := by
  have h1183 : mixedVector B (Sum.inr 1183) = Sparse.eval nodeValue1183 (mixedVector B) := by
    change mixedMoment B node1183 node1183Labels = _
    exact sound1183 B hB hF
  have h1188 : mixedVector B (Sum.inr 1188) = Sparse.eval nodeValue1188 (mixedVector B) := by
    change mixedMoment B node1188 node1188Labels = _
    exact sound1188 B hB hF
  have h1189 : mixedVector B (Sum.inr 1189) = Sparse.eval nodeValue1189 (mixedVector B) := by
    change mixedMoment B node1189 node1189Labels = _
    exact sound1189 B hB hF
  have h1286 : mixedVector B (Sum.inr 1286) = Sparse.eval nodeValue1286 (mixedVector B) := by
    change mixedMoment B node1286 node1286Labels = _
    exact sound1286 B hB hF
  have h2684 : mixedVector B (Sum.inr 2684) = Sparse.eval nodeValue2684 (mixedVector B) := by
    change mixedMoment B node2684 node2684Labels = _
    exact sound2684 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1688, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1183, h1188, h1189, h1286, h2684, h4088, reducedSource1444] using sourceEq1688 B hB

theorem rowSound1444 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1444 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1444, numericCheck1444, reducedZero1444 B hB hF, mul_zero]

theorem reducedZero1445 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1445 (mixedVector B) = 0 := by
  have h1185 : mixedVector B (Sum.inr 1185) = Sparse.eval nodeValue1185 (mixedVector B) := by
    change mixedMoment B node1185 node1185Labels = _
    exact sound1185 B hB hF
  have h2400 : mixedVector B (Sum.inr 2400) = Sparse.eval nodeValue2400 (mixedVector B) := by
    change mixedMoment B node2400 node2400Labels = _
    exact sound2400 B hB hF
  have h2535 : mixedVector B (Sum.inr 2535) = Sparse.eval nodeValue2535 (mixedVector B) := by
    change mixedMoment B node2535 node2535Labels = _
    exact sound2535 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h2682 : mixedVector B (Sum.inr 2682) = Sparse.eval nodeValue2682 (mixedVector B) := by
    change mixedMoment B node2682 node2682Labels = _
    exact sound2682 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm1689, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1185, h2400, h2535, h2677, h2682, h2686, h4089, reducedSource1445] using sourceEq1689 B hB

theorem rowSound1445 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1445 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1445, numericCheck1445, reducedZero1445 B hB hF, mul_zero]

theorem reducedZero1446 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1446 (mixedVector B) = 0 := by
  have h1188 : mixedVector B (Sum.inr 1188) = Sparse.eval nodeValue1188 (mixedVector B) := by
    change mixedMoment B node1188 node1188Labels = _
    exact sound1188 B hB hF
  have h2403 : mixedVector B (Sum.inr 2403) = Sparse.eval nodeValue2403 (mixedVector B) := by
    change mixedMoment B node2403 node2403Labels = _
    exact sound2403 B hB hF
  have h2536 : mixedVector B (Sum.inr 2536) = Sparse.eval nodeValue2536 (mixedVector B) := by
    change mixedMoment B node2536 node2536Labels = _
    exact sound2536 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2684 : mixedVector B (Sum.inr 2684) = Sparse.eval nodeValue2684 (mixedVector B) := by
    change mixedMoment B node2684 node2684Labels = _
    exact sound2684 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1690, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1188, h2403, h2536, h2672, h2684, h4088, reducedSource1446] using sourceEq1690 B hB

theorem rowSound1446 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1446 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1446, numericCheck1446, reducedZero1446 B hB hF, mul_zero]

theorem reducedZero1447 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1447 (mixedVector B) = 0 := by
  have h1184 : mixedVector B (Sum.inr 1184) = Sparse.eval nodeValue1184 (mixedVector B) := by
    change mixedMoment B node1184 node1184Labels = _
    exact sound1184 B hB hF
  have h2399 : mixedVector B (Sum.inr 2399) = Sparse.eval nodeValue2399 (mixedVector B) := by
    change mixedMoment B node2399 node2399Labels = _
    exact sound2399 B hB hF
  have h2534 : mixedVector B (Sum.inr 2534) = Sparse.eval nodeValue2534 (mixedVector B) := by
    change mixedMoment B node2534 node2534Labels = _
    exact sound2534 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1693, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1184, h2399, h2534, h2670, h2681, h2685, h4082, reducedSource1447] using sourceEq1693 B hB

theorem rowSound1447 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1447 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1447, numericCheck1447, reducedZero1447 B hB hF, mul_zero]

theorem reducedZero1448 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1448 (mixedVector B) = 0 := by
  have h1200 : mixedVector B (Sum.inr 1200) = Sparse.eval nodeValue1200 (mixedVector B) := by
    change mixedMoment B node1200 node1200Labels = _
    exact sound1200 B hB hF
  have h1201 : mixedVector B (Sum.inr 1201) = Sparse.eval nodeValue1201 (mixedVector B) := by
    change mixedMoment B node1201 node1201Labels = _
    exact sound1201 B hB hF
  have h1228 : mixedVector B (Sum.inr 1228) = Sparse.eval nodeValue1228 (mixedVector B) := by
    change mixedMoment B node1228 node1228Labels = _
    exact sound1228 B hB hF
  have h2703 : mixedVector B (Sum.inr 2703) = Sparse.eval nodeValue2703 (mixedVector B) := by
    change mixedMoment B node2703 node2703Labels = _
    exact sound2703 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1695, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1200, h1201, h1228, h2703, h4090, reducedSource1448] using sourceEq1695 B hB

theorem rowSound1448 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1448 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1448, numericCheck1448, reducedZero1448 B hB hF, mul_zero]

theorem reducedZero1449 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1449 (mixedVector B) = 0 := by
  have h1198 : mixedVector B (Sum.inr 1198) = Sparse.eval nodeValue1198 (mixedVector B) := by
    change mixedMoment B node1198 node1198Labels = _
    exact sound1198 B hB hF
  have h2459 : mixedVector B (Sum.inr 2459) = Sparse.eval nodeValue2459 (mixedVector B) := by
    change mixedMoment B node2459 node2459Labels = _
    exact sound2459 B hB hF
  have h2697 : mixedVector B (Sum.inr 2697) = Sparse.eval nodeValue2697 (mixedVector B) := by
    change mixedMoment B node2697 node2697Labels = _
    exact sound2697 B hB hF
  have h2701 : mixedVector B (Sum.inr 2701) = Sparse.eval nodeValue2701 (mixedVector B) := by
    change mixedMoment B node2701 node2701Labels = _
    exact sound2701 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1696, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1198, h2459, h2697, h2701, h2705, h4088, reducedSource1449] using sourceEq1696 B hB

theorem rowSound1449 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1449 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1449, numericCheck1449, reducedZero1449 B hB hF, mul_zero]

theorem reducedZero1450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1450 (mixedVector B) = 0 := by
  have h1200 : mixedVector B (Sum.inr 1200) = Sparse.eval nodeValue1200 (mixedVector B) := by
    change mixedMoment B node1200 node1200Labels = _
    exact sound1200 B hB hF
  have h2461 : mixedVector B (Sum.inr 2461) = Sparse.eval nodeValue2461 (mixedVector B) := by
    change mixedMoment B node2461 node2461Labels = _
    exact sound2461 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2703 : mixedVector B (Sum.inr 2703) = Sparse.eval nodeValue2703 (mixedVector B) := by
    change mixedMoment B node2703 node2703Labels = _
    exact sound2703 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1697, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1200, h2461, h2694, h2703, h4090, reducedSource1450] using sourceEq1697 B hB

theorem rowSound1450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1450 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1450, numericCheck1450, reducedZero1450 B hB hF, mul_zero]

theorem reducedZero1451 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1451 (mixedVector B) = 0 := by
  have h1197 : mixedVector B (Sum.inr 1197) = Sparse.eval nodeValue1197 (mixedVector B) := by
    change mixedMoment B node1197 node1197Labels = _
    exact sound1197 B hB hF
  have h2458 : mixedVector B (Sum.inr 2458) = Sparse.eval nodeValue2458 (mixedVector B) := by
    change mixedMoment B node2458 node2458Labels = _
    exact sound2458 B hB hF
  have h2693 : mixedVector B (Sum.inr 2693) = Sparse.eval nodeValue2693 (mixedVector B) := by
    change mixedMoment B node2693 node2693Labels = _
    exact sound2693 B hB hF
  have h2700 : mixedVector B (Sum.inr 2700) = Sparse.eval nodeValue2700 (mixedVector B) := by
    change mixedMoment B node2700 node2700Labels = _
    exact sound2700 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1700, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1197, h2458, h2693, h2700, h2704, h4080, reducedSource1451] using sourceEq1700 B hB

theorem rowSound1451 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1451 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1451, numericCheck1451, reducedZero1451 B hB hF, mul_zero]

theorem reducedZero1452 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1452 (mixedVector B) = 0 := by
  have h1052 : mixedVector B (Sum.inr 1052) = Sparse.eval nodeValue1052 (mixedVector B) := by
    change mixedMoment B node1052 node1052Labels = _
    exact sound1052 B hB hF
  have h1054 : mixedVector B (Sum.inr 1054) = Sparse.eval nodeValue1054 (mixedVector B) := by
    change mixedMoment B node1054 node1054Labels = _
    exact sound1054 B hB hF
  have h1060 : mixedVector B (Sum.inr 1060) = Sparse.eval nodeValue1060 (mixedVector B) := by
    change mixedMoment B node1060 node1060Labels = _
    exact sound1060 B hB hF
  have h1073 : mixedVector B (Sum.inr 1073) = Sparse.eval nodeValue1073 (mixedVector B) := by
    change mixedMoment B node1073 node1073Labels = _
    exact sound1073 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1702, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1052, h1054, h1060, h1073, h2275, h4080, reducedSource1452] using sourceEq1702 B hB

theorem rowSound1452 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1452 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1452, numericCheck1452, reducedZero1452 B hB hF, mul_zero]

theorem reducedZero1453 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1453 (mixedVector B) = 0 := by
  have h1054 : mixedVector B (Sum.inr 1054) = Sparse.eval nodeValue1054 (mixedVector B) := by
    change mixedMoment B node1054 node1054Labels = _
    exact sound1054 B hB hF
  have h2031 : mixedVector B (Sum.inr 2031) = Sparse.eval nodeValue2031 (mixedVector B) := by
    change mixedMoment B node2031 node2031Labels = _
    exact sound2031 B hB hF
  have h2129 : mixedVector B (Sum.inr 2129) = Sparse.eval nodeValue2129 (mixedVector B) := by
    change mixedMoment B node2129 node2129Labels = _
    exact sound2129 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1703, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1054, h2031, h2129, h2216, h2251, h2275, h4080, reducedSource1453] using sourceEq1703 B hB

theorem rowSound1453 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1453 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1453, numericCheck1453, reducedZero1453 B hB hF, mul_zero]

theorem reducedZero1454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1454 (mixedVector B) = 0 := by
  have h1053 : mixedVector B (Sum.inr 1053) = Sparse.eval nodeValue1053 (mixedVector B) := by
    change mixedMoment B node1053 node1053Labels = _
    exact sound1053 B hB hF
  have h2030 : mixedVector B (Sum.inr 2030) = Sparse.eval nodeValue2030 (mixedVector B) := by
    change mixedMoment B node2030 node2030Labels = _
    exact sound2030 B hB hF
  have h2128 : mixedVector B (Sum.inr 2128) = Sparse.eval nodeValue2128 (mixedVector B) := by
    change mixedMoment B node2128 node2128Labels = _
    exact sound2128 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1704, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1053, h2030, h2128, h2215, h2274, h2276, h4082, reducedSource1454] using sourceEq1704 B hB

theorem rowSound1454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1454 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1454, numericCheck1454, reducedZero1454 B hB hF, mul_zero]

theorem reducedZero1455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1455 (mixedVector B) = 0 := by
  have h988 : mixedVector B (Sum.inr 988) = Sparse.eval nodeValue988 (mixedVector B) := by
    change mixedMoment B node988 node988Labels = _
    exact sound988 B hB hF
  have h990 : mixedVector B (Sum.inr 990) = Sparse.eval nodeValue990 (mixedVector B) := by
    change mixedMoment B node990 node990Labels = _
    exact sound990 B hB hF
  have h998 : mixedVector B (Sum.inr 998) = Sparse.eval nodeValue998 (mixedVector B) := by
    change mixedMoment B node998 node998Labels = _
    exact sound998 B hB hF
  have h1052 : mixedVector B (Sum.inr 1052) = Sparse.eval nodeValue1052 (mixedVector B) := by
    change mixedMoment B node1052 node1052Labels = _
    exact sound1052 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1706, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h988, h990, h998, h1052, h2214, h4080, reducedSource1455] using sourceEq1706 B hB

theorem rowSound1455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1455 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1455, numericCheck1455, reducedZero1455 B hB hF, mul_zero]

theorem sourceRowsAt1440 : MixedData.sourceRows (1440 : Fin 2425) =
    MixedData.row1440 := by decide +kernel

theorem sourceRowsAt1441 : MixedData.sourceRows (1441 : Fin 2425) =
    MixedData.row1441 := by decide +kernel

theorem sourceRowsAt1442 : MixedData.sourceRows (1442 : Fin 2425) =
    MixedData.row1442 := by decide +kernel

theorem sourceRowsAt1443 : MixedData.sourceRows (1443 : Fin 2425) =
    MixedData.row1443 := by decide +kernel

theorem sourceRowsAt1444 : MixedData.sourceRows (1444 : Fin 2425) =
    MixedData.row1444 := by decide +kernel

theorem sourceRowsAt1445 : MixedData.sourceRows (1445 : Fin 2425) =
    MixedData.row1445 := by decide +kernel

theorem sourceRowsAt1446 : MixedData.sourceRows (1446 : Fin 2425) =
    MixedData.row1446 := by decide +kernel

theorem sourceRowsAt1447 : MixedData.sourceRows (1447 : Fin 2425) =
    MixedData.row1447 := by decide +kernel

theorem sourceRowsAt1448 : MixedData.sourceRows (1448 : Fin 2425) =
    MixedData.row1448 := by decide +kernel

theorem sourceRowsAt1449 : MixedData.sourceRows (1449 : Fin 2425) =
    MixedData.row1449 := by decide +kernel

theorem sourceRowsAt1450 : MixedData.sourceRows (1450 : Fin 2425) =
    MixedData.row1450 := by decide +kernel

theorem sourceRowsAt1451 : MixedData.sourceRows (1451 : Fin 2425) =
    MixedData.row1451 := by decide +kernel

theorem sourceRowsAt1452 : MixedData.sourceRows (1452 : Fin 2425) =
    MixedData.row1452 := by decide +kernel

theorem sourceRowsAt1453 : MixedData.sourceRows (1453 : Fin 2425) =
    MixedData.row1453 := by decide +kernel

theorem sourceRowsAt1454 : MixedData.sourceRows (1454 : Fin 2425) =
    MixedData.row1454 := by decide +kernel

theorem sourceRowsAt1455 : MixedData.sourceRows (1455 : Fin 2425) =
    MixedData.row1455 := by decide +kernel

theorem chunkSound90_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 90) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1440 ∨ k.val = 1441 ∨ k.val = 1442 ∨ k.val = 1443 ∨ k.val = 1444 ∨ k.val = 1445 ∨ k.val = 1446 ∨ k.val = 1447 ∨ k.val = 1448 ∨ k.val = 1449 ∨ k.val = 1450 ∨ k.val = 1451 ∨ k.val = 1452 ∨ k.val = 1453 ∨ k.val = 1454 ∨ k.val = 1455 := by omega
  rcases heq with h1440 | h1441 | h1442 | h1443 | h1444 | h1445 | h1446 | h1447 | h1448 | h1449 | h1450 | h1451 | h1452 | h1453 | h1454 | h1455
  · have he : k = (1440 : Fin 2425) := Fin.ext h1440
    subst k
    rw [sourceRowsAt1440]
    exact rowSound1440 B hB hF
  · have he : k = (1441 : Fin 2425) := Fin.ext h1441
    subst k
    rw [sourceRowsAt1441]
    exact rowSound1441_e B hB hF
  · have he : k = (1442 : Fin 2425) := Fin.ext h1442
    subst k
    rw [sourceRowsAt1442]
    exact rowSound1442_e B hB hF
  · have he : k = (1443 : Fin 2425) := Fin.ext h1443
    subst k
    rw [sourceRowsAt1443]
    exact rowSound1443 B hB hF
  · have he : k = (1444 : Fin 2425) := Fin.ext h1444
    subst k
    rw [sourceRowsAt1444]
    exact rowSound1444 B hB hF
  · have he : k = (1445 : Fin 2425) := Fin.ext h1445
    subst k
    rw [sourceRowsAt1445]
    exact rowSound1445 B hB hF
  · have he : k = (1446 : Fin 2425) := Fin.ext h1446
    subst k
    rw [sourceRowsAt1446]
    exact rowSound1446 B hB hF
  · have he : k = (1447 : Fin 2425) := Fin.ext h1447
    subst k
    rw [sourceRowsAt1447]
    exact rowSound1447 B hB hF
  · have he : k = (1448 : Fin 2425) := Fin.ext h1448
    subst k
    rw [sourceRowsAt1448]
    exact rowSound1448 B hB hF
  · have he : k = (1449 : Fin 2425) := Fin.ext h1449
    subst k
    rw [sourceRowsAt1449]
    exact rowSound1449 B hB hF
  · have he : k = (1450 : Fin 2425) := Fin.ext h1450
    subst k
    rw [sourceRowsAt1450]
    exact rowSound1450 B hB hF
  · have he : k = (1451 : Fin 2425) := Fin.ext h1451
    subst k
    rw [sourceRowsAt1451]
    exact rowSound1451 B hB hF
  · have he : k = (1452 : Fin 2425) := Fin.ext h1452
    subst k
    rw [sourceRowsAt1452]
    exact rowSound1452 B hB hF
  · have he : k = (1453 : Fin 2425) := Fin.ext h1453
    subst k
    rw [sourceRowsAt1453]
    exact rowSound1453 B hB hF
  · have he : k = (1454 : Fin 2425) := Fin.ext h1454
    subst k
    rw [sourceRowsAt1454]
    exact rowSound1454 B hB hF
  · have he : k = (1455 : Fin 2425) := Fin.ext h1455
    subst k
    rw [sourceRowsAt1455]
    exact rowSound1455 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90_e_oai
