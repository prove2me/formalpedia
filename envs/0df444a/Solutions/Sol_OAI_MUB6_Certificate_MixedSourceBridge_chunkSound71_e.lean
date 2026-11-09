-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound71_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:31:49.830211+00:00
-- url     : https://prove2.me/submissions/e2d7fbb2-d5c2-463a-a678-4f9dece185da

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E124
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

theorem canonical21013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21013 raw21013Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw21013 raw21013Labels = mixedMoment B raw21013step0 raw21013step0Labels := by
      have hz : ∀ j, raw21013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21013step0 = (fun i j => raw21013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21013step0 raw21013; decide +kernel
      have hl : raw21013step0Labels = raw21013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21013 raw21013Labels permutation346 hz
    mixedMoment B raw21013step0 raw21013step0Labels = mixedMoment B raw21013step1 raw21013step1Labels := by
      have hz : ∀ j, raw21013step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21013step1 = (fun i j => raw21013step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21013step1 raw21013step0; decide +kernel
      have hl : raw21013step1Labels = raw21013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21013step0 raw21013step0Labels permutation56 hz
    _ = mixedMoment B node1190 node1190Labels := by rfl

theorem canonical21014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21014 raw21014Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw21014 raw21014Labels = mixedMoment B raw21014step0 raw21014step0Labels := by
      have hz : ∀ j, raw21014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21014step0 = (fun i j => raw21014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21014step0 raw21014; decide +kernel
      have hl : raw21014step0Labels = raw21014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21014 raw21014Labels permutation346 hz
    mixedMoment B raw21014step0 raw21014step0Labels = mixedMoment B raw21014step1 raw21014step1Labels := by
      have ha : raw21014step1 = (fun i j => raw21014step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21014step1 raw21014step0; decide +kernel
      have hl : raw21014step1Labels = raw21014step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21014step0 raw21014step0Labels permutation151 permutation2
    mixedMoment B raw21014step1 raw21014step1Labels = mixedMoment B raw21014step2 raw21014step2Labels := by
      have ha : raw21014step2 = -raw21014step1 := by apply Matrix.ext; change ∀ i j, raw21014step2 i j = -(raw21014step1 i j); unfold raw21014step2 raw21014step1; decide +kernel
      have hl : raw21014step2Labels = raw21014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1924 node1924Labels := by rfl

theorem canonical21015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21015 raw21015Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw21015 raw21015Labels = mixedMoment B raw21015step0 raw21015step0Labels := by
      have hz : ∀ j, raw21015 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21015step0 = (fun i j => raw21015 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21015step0 raw21015; decide +kernel
      have hl : raw21015step0Labels = raw21015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21015 raw21015Labels permutation265 hz
    mixedMoment B raw21015step0 raw21015step0Labels = mixedMoment B raw21015step1 raw21015step1Labels := by
      have ha : raw21015step1 = (fun i j => raw21015step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21015step1 raw21015step0; decide +kernel
      have hl : raw21015step1Labels = raw21015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21015step0 raw21015step0Labels permutation151 permutation2
    mixedMoment B raw21015step1 raw21015step1Labels = mixedMoment B raw21015step2 raw21015step2Labels := by
      have ha : raw21015step2 = -raw21015step1 := by apply Matrix.ext; change ∀ i j, raw21015step2 i j = -(raw21015step1 i j); unfold raw21015step2 raw21015step1; decide +kernel
      have hl : raw21015step2Labels = raw21015step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1924 node1924Labels := by rfl

theorem canonical21016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21016 raw21016Labels = mixedMoment B node1950 node1950Labels := by
  calc
    mixedMoment B raw21016 raw21016Labels = mixedMoment B raw21016step0 raw21016step0Labels := by
      have hz : ∀ j, raw21016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21016step0 = (fun i j => raw21016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21016step0 raw21016; decide +kernel
      have hl : raw21016step0Labels = raw21016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21016 raw21016Labels permutation346 hz
    mixedMoment B raw21016step0 raw21016step0Labels = mixedMoment B raw21016step1 raw21016step1Labels := by
      have hz : ∀ j, raw21016step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21016step1 = (fun i j => raw21016step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21016step1 raw21016step0; decide +kernel
      have hl : raw21016step1Labels = raw21016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21016step0 raw21016step0Labels permutation56 hz
    mixedMoment B raw21016step1 raw21016step1Labels = mixedMoment B raw21016step2 raw21016step2Labels := by
      have ha : raw21016step2 = (fun i j => raw21016step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21016step2 raw21016step1; decide +kernel
      have hl : raw21016step2Labels = raw21016step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21016step1 raw21016step1Labels permutation31 permutation2
    mixedMoment B raw21016step2 raw21016step2Labels = mixedMoment B raw21016step3 raw21016step3Labels := by
      have ha : raw21016step3 = -raw21016step2 := by apply Matrix.ext; change ∀ i j, raw21016step3 i j = -(raw21016step2 i j); unfold raw21016step3 raw21016step2; decide +kernel
      have hl : raw21016step3Labels = raw21016step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1950 node1950Labels := by rfl

theorem canonical21017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21017 raw21017Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw21017 raw21017Labels = mixedMoment B raw21017step0 raw21017step0Labels := by
      have hz : ∀ j, raw21017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21017step0 = (fun i j => raw21017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21017step0 raw21017; decide +kernel
      have hl : raw21017step0Labels = raw21017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21017 raw21017Labels permutation346 hz
    mixedMoment B raw21017step0 raw21017step0Labels = mixedMoment B raw21017step1 raw21017step1Labels := by
      have hz : ∀ j, raw21017step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21017step1 = (fun i j => raw21017step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21017step1 raw21017step0; decide +kernel
      have hl : raw21017step1Labels = raw21017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21017step0 raw21017step0Labels permutation56 hz
    mixedMoment B raw21017step1 raw21017step1Labels = mixedMoment B raw21017step2 raw21017step2Labels := by
      have ha : raw21017step2 = (fun i j => raw21017step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21017step2 raw21017step1; decide +kernel
      have hl : raw21017step2Labels = raw21017step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21017step1 raw21017step1Labels permutation31 permutation2
    mixedMoment B raw21017step2 raw21017step2Labels = mixedMoment B raw21017step3 raw21017step3Labels := by
      have ha : raw21017step3 = -raw21017step2 := by apply Matrix.ext; change ∀ i j, raw21017step3 i j = -(raw21017step2 i j); unfold raw21017step3 raw21017step2; decide +kernel
      have hl : raw21017step3Labels = raw21017step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical21018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21018 raw21018Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw21018 raw21018Labels = mixedMoment B raw21018step0 raw21018step0Labels := by
      have hz : ∀ j, raw21018 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21018step0 = (fun i j => raw21018 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21018step0 raw21018; decide +kernel
      have hl : raw21018step0Labels = raw21018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21018 raw21018Labels permutation346 hz
    mixedMoment B raw21018step0 raw21018step0Labels = mixedMoment B raw21018step1 raw21018step1Labels := by
      have hz : ∀ j, raw21018step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21018step1 = (fun i j => raw21018step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21018step1 raw21018step0; decide +kernel
      have hl : raw21018step1Labels = raw21018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21018step0 raw21018step0Labels permutation56 hz
    _ = mixedMoment B node2685 node2685Labels := by rfl

theorem canonical21019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21019 raw21019Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw21019 raw21019Labels = mixedMoment B raw21019step0 raw21019step0Labels := by
      have hz : ∀ j, raw21019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21019step0 = (fun i j => raw21019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21019step0 raw21019; decide +kernel
      have hl : raw21019step0Labels = raw21019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21019 raw21019Labels permutation346 hz
    mixedMoment B raw21019step0 raw21019step0Labels = mixedMoment B raw21019step1 raw21019step1Labels := by
      have hz : ∀ j, raw21019step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21019step1 = (fun i j => raw21019step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21019step1 raw21019step0; decide +kernel
      have hl : raw21019step1Labels = raw21019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21019step0 raw21019step0Labels permutation56 hz
    mixedMoment B raw21019step1 raw21019step1Labels = mixedMoment B raw21019step2 raw21019step2Labels := by
      have ha : raw21019step2 = (fun i j => raw21019step1 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21019step2 raw21019step1; decide +kernel
      have hl : raw21019step2Labels = raw21019step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21019step1 raw21019step1Labels permutation30 permutation0
    mixedMoment B raw21019step2 raw21019step2Labels = mixedMoment B raw21019step3 raw21019step3Labels := by
      have ha : raw21019step3 = -raw21019step2 := by apply Matrix.ext; change ∀ i j, raw21019step3 i j = -(raw21019step2 i j); unfold raw21019step3 raw21019step2; decide +kernel
      have hl : raw21019step3Labels = raw21019step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical21020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21020 raw21020Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw21020 raw21020Labels = mixedMoment B raw21020step0 raw21020step0Labels := by
      have hz : ∀ j, raw21020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21020step0 = (fun i j => raw21020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21020step0 raw21020; decide +kernel
      have hl : raw21020step0Labels = raw21020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21020 raw21020Labels permutation346 hz
    mixedMoment B raw21020step0 raw21020step0Labels = mixedMoment B raw21020step1 raw21020step1Labels := by
      have ha : raw21020step1 = (fun i j => raw21020step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21020step1 raw21020step0; decide +kernel
      have hl : raw21020step1Labels = raw21020step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21020step0 raw21020step0Labels permutation38 permutation2
    _ = mixedMoment B node1098 node1098Labels := by rfl

theorem canonical21021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21021 raw21021Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw21021 raw21021Labels = mixedMoment B raw21021step0 raw21021step0Labels := by
      have hz : ∀ j, raw21021 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21021step0 = (fun i j => raw21021 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21021step0 raw21021; decide +kernel
      have hl : raw21021step0Labels = raw21021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21021 raw21021Labels permutation265 hz
    mixedMoment B raw21021step0 raw21021step0Labels = mixedMoment B raw21021step1 raw21021step1Labels := by
      have ha : raw21021step1 = (fun i j => raw21021step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21021step1 raw21021step0; decide +kernel
      have hl : raw21021step1Labels = raw21021step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21021step0 raw21021step0Labels permutation38 permutation2
    _ = mixedMoment B node1098 node1098Labels := by rfl

theorem canonical21022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21022 raw21022Labels = mixedMoment B node1103 node1103Labels := by
  calc
    mixedMoment B raw21022 raw21022Labels = mixedMoment B raw21022step0 raw21022step0Labels := by
      have hz : ∀ j, raw21022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21022step0 = (fun i j => raw21022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21022step0 raw21022; decide +kernel
      have hl : raw21022step0Labels = raw21022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21022 raw21022Labels permutation346 hz
    mixedMoment B raw21022step0 raw21022step0Labels = mixedMoment B raw21022step1 raw21022step1Labels := by
      have hz : ∀ j, raw21022step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21022step1 = (fun i j => raw21022step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21022step1 raw21022step0; decide +kernel
      have hl : raw21022step1Labels = raw21022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21022step0 raw21022step0Labels permutation56 hz
    _ = mixedMoment B node1103 node1103Labels := by rfl

theorem canonical21023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21023 raw21023Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw21023 raw21023Labels = mixedMoment B raw21023step0 raw21023step0Labels := by
      have hz : ∀ j, raw21023 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21023step0 = (fun i j => raw21023 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21023step0 raw21023; decide +kernel
      have hl : raw21023step0Labels = raw21023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21023 raw21023Labels permutation346 hz
    mixedMoment B raw21023step0 raw21023step0Labels = mixedMoment B raw21023step1 raw21023step1Labels := by
      have hz : ∀ j, raw21023step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21023step1 = (fun i j => raw21023step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21023step1 raw21023step0; decide +kernel
      have hl : raw21023step1Labels = raw21023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21023step0 raw21023step0Labels permutation56 hz
    mixedMoment B raw21023step1 raw21023step1Labels = mixedMoment B raw21023step2 raw21023step2Labels := by
      have ha : raw21023step2 = (fun i j => raw21023step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21023step2 raw21023step1; decide +kernel
      have hl : raw21023step2Labels = raw21023step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21023step1 raw21023step1Labels permutation31 permutation2
    mixedMoment B raw21023step2 raw21023step2Labels = mixedMoment B raw21023step3 raw21023step3Labels := by
      have ha : raw21023step3 = -raw21023step2 := by apply Matrix.ext; change ∀ i j, raw21023step3 i j = -(raw21023step2 i j); unfold raw21023step3 raw21023step2; decide +kernel
      have hl : raw21023step3Labels = raw21023step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node893 node893Labels := by rfl

theorem canonical21024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21024 raw21024Labels = mixedMoment B node1184 node1184Labels := by
  calc
    mixedMoment B raw21024 raw21024Labels = mixedMoment B raw21024step0 raw21024step0Labels := by
      have hz : ∀ j, raw21024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21024step0 = (fun i j => raw21024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21024step0 raw21024; decide +kernel
      have hl : raw21024step0Labels = raw21024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21024 raw21024Labels permutation346 hz
    mixedMoment B raw21024step0 raw21024step0Labels = mixedMoment B raw21024step1 raw21024step1Labels := by
      have ha : raw21024step1 = (fun i j => raw21024step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21024step1 raw21024step0; decide +kernel
      have hl : raw21024step1Labels = raw21024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21024step0 raw21024step0Labels permutation38 permutation2
    _ = mixedMoment B node1184 node1184Labels := by rfl

theorem canonical21025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21025 raw21025Labels = mixedMoment B node1184 node1184Labels := by
  calc
    mixedMoment B raw21025 raw21025Labels = mixedMoment B raw21025step0 raw21025step0Labels := by
      have hz : ∀ j, raw21025 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21025step0 = (fun i j => raw21025 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21025step0 raw21025; decide +kernel
      have hl : raw21025step0Labels = raw21025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21025 raw21025Labels permutation265 hz
    mixedMoment B raw21025step0 raw21025step0Labels = mixedMoment B raw21025step1 raw21025step1Labels := by
      have ha : raw21025step1 = (fun i j => raw21025step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21025step1 raw21025step0; decide +kernel
      have hl : raw21025step1Labels = raw21025step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21025step0 raw21025step0Labels permutation38 permutation2
    _ = mixedMoment B node1184 node1184Labels := by rfl

theorem canonical21026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21026 raw21026Labels = mixedMoment B node1287 node1287Labels := by
  calc
    mixedMoment B raw21026 raw21026Labels = mixedMoment B raw21026step0 raw21026step0Labels := by
      have hz : ∀ j, raw21026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21026step0 = (fun i j => raw21026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21026step0 raw21026; decide +kernel
      have hl : raw21026step0Labels = raw21026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21026 raw21026Labels permutation346 hz
    mixedMoment B raw21026step0 raw21026step0Labels = mixedMoment B raw21026step1 raw21026step1Labels := by
      have hz : ∀ j, raw21026step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21026step1 = (fun i j => raw21026step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21026step1 raw21026step0; decide +kernel
      have hl : raw21026step1Labels = raw21026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21026step0 raw21026step0Labels permutation56 hz
    _ = mixedMoment B node1287 node1287Labels := by rfl

theorem canonical21027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21027 raw21027Labels = mixedMoment B node1192 node1192Labels := by
  calc
    mixedMoment B raw21027 raw21027Labels = mixedMoment B raw21027step0 raw21027step0Labels := by
      have hz : ∀ j, raw21027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21027step0 = (fun i j => raw21027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21027step0 raw21027; decide +kernel
      have hl : raw21027step0Labels = raw21027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21027 raw21027Labels permutation346 hz
    mixedMoment B raw21027step0 raw21027step0Labels = mixedMoment B raw21027step1 raw21027step1Labels := by
      have hz : ∀ j, raw21027step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21027step1 = (fun i j => raw21027step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21027step1 raw21027step0; decide +kernel
      have hl : raw21027step1Labels = raw21027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21027step0 raw21027step0Labels permutation56 hz
    _ = mixedMoment B node1192 node1192Labels := by rfl

theorem canonical21033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21033 raw21033Labels = mixedMoment B node1186 node1186Labels := by
  calc
    mixedMoment B raw21033 raw21033Labels = mixedMoment B raw21033step0 raw21033step0Labels := by
      have hz : ∀ j, raw21033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21033step0 = (fun i j => raw21033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21033step0 raw21033; decide +kernel
      have hl : raw21033step0Labels = raw21033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21033 raw21033Labels permutation346 hz
    mixedMoment B raw21033step0 raw21033step0Labels = mixedMoment B raw21033step1 raw21033step1Labels := by
      have hz : ∀ j, raw21033step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21033step1 = (fun i j => raw21033step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21033step1 raw21033step0; decide +kernel
      have hl : raw21033step1Labels = raw21033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21033step0 raw21033step0Labels permutation56 hz
    _ = mixedMoment B node1186 node1186Labels := by rfl

theorem canonical21034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21034 raw21034Labels = mixedMoment B node1608 node1608Labels := by
  calc
    mixedMoment B raw21034 raw21034Labels = mixedMoment B raw21034step0 raw21034step0Labels := by
      have hz : ∀ j, raw21034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21034step0 = (fun i j => raw21034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21034step0 raw21034; decide +kernel
      have hl : raw21034step0Labels = raw21034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21034 raw21034Labels permutation346 hz
    mixedMoment B raw21034step0 raw21034step0Labels = mixedMoment B raw21034step1 raw21034step1Labels := by
      have ha : raw21034step1 = (fun i j => raw21034step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21034step1 raw21034step0; decide +kernel
      have hl : raw21034step1Labels = raw21034step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21034step0 raw21034step0Labels permutation151 permutation2
    mixedMoment B raw21034step1 raw21034step1Labels = mixedMoment B raw21034step2 raw21034step2Labels := by
      have ha : raw21034step2 = -raw21034step1 := by apply Matrix.ext; change ∀ i j, raw21034step2 i j = -(raw21034step1 i j); unfold raw21034step2 raw21034step1; decide +kernel
      have hl : raw21034step2Labels = raw21034step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1608 node1608Labels := by rfl

theorem canonical21035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21035 raw21035Labels = mixedMoment B node1608 node1608Labels := by
  calc
    mixedMoment B raw21035 raw21035Labels = mixedMoment B raw21035step0 raw21035step0Labels := by
      have hz : ∀ j, raw21035 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21035step0 = (fun i j => raw21035 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21035step0 raw21035; decide +kernel
      have hl : raw21035step0Labels = raw21035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21035 raw21035Labels permutation265 hz
    mixedMoment B raw21035step0 raw21035step0Labels = mixedMoment B raw21035step1 raw21035step1Labels := by
      have ha : raw21035step1 = (fun i j => raw21035step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21035step1 raw21035step0; decide +kernel
      have hl : raw21035step1Labels = raw21035step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21035step0 raw21035step0Labels permutation151 permutation2
    mixedMoment B raw21035step1 raw21035step1Labels = mixedMoment B raw21035step2 raw21035step2Labels := by
      have ha : raw21035step2 = -raw21035step1 := by apply Matrix.ext; change ∀ i j, raw21035step2 i j = -(raw21035step1 i j); unfold raw21035step2 raw21035step1; decide +kernel
      have hl : raw21035step2Labels = raw21035step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1608 node1608Labels := by rfl

theorem canonical21036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21036 raw21036Labels = mixedMoment B node1627 node1627Labels := by
  calc
    mixedMoment B raw21036 raw21036Labels = mixedMoment B raw21036step0 raw21036step0Labels := by
      have hz : ∀ j, raw21036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21036step0 = (fun i j => raw21036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21036step0 raw21036; decide +kernel
      have hl : raw21036step0Labels = raw21036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21036 raw21036Labels permutation346 hz
    mixedMoment B raw21036step0 raw21036step0Labels = mixedMoment B raw21036step1 raw21036step1Labels := by
      have hz : ∀ j, raw21036step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21036step1 = (fun i j => raw21036step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21036step1 raw21036step0; decide +kernel
      have hl : raw21036step1Labels = raw21036step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21036step0 raw21036step0Labels permutation56 hz
    mixedMoment B raw21036step1 raw21036step1Labels = mixedMoment B raw21036step2 raw21036step2Labels := by
      have ha : raw21036step2 = (fun i j => raw21036step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21036step2 raw21036step1; decide +kernel
      have hl : raw21036step2Labels = raw21036step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21036step1 raw21036step1Labels permutation31 permutation2
    mixedMoment B raw21036step2 raw21036step2Labels = mixedMoment B raw21036step3 raw21036step3Labels := by
      have ha : raw21036step3 = -raw21036step2 := by apply Matrix.ext; change ∀ i j, raw21036step3 i j = -(raw21036step2 i j); unfold raw21036step3 raw21036step2; decide +kernel
      have hl : raw21036step3Labels = raw21036step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1627 node1627Labels := by rfl

theorem canonical21037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21037 raw21037Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw21037 raw21037Labels = mixedMoment B raw21037step0 raw21037step0Labels := by
      have hz : ∀ j, raw21037 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21037step0 = (fun i j => raw21037 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21037step0 raw21037; decide +kernel
      have hl : raw21037step0Labels = raw21037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21037 raw21037Labels permutation520 hz
    mixedMoment B raw21037step0 raw21037step0Labels = mixedMoment B raw21037step1 raw21037step1Labels := by
      have hz : ∀ j, raw21037step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21037step1 = (fun i j => raw21037step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21037step1 raw21037step0; decide +kernel
      have hl : raw21037step1Labels = raw21037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21037step0 raw21037step0Labels permutation80 hz
    mixedMoment B raw21037step1 raw21037step1Labels = mixedMoment B raw21037step2 raw21037step2Labels := by
      have hz : ∀ j, raw21037step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21037step2 = (fun i j => raw21037step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21037step2 raw21037step1; decide +kernel
      have hl : raw21037step2Labels = raw21037step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21037step1 raw21037step1Labels permutation14 hz
    mixedMoment B raw21037step2 raw21037step2Labels = mixedMoment B raw21037step3 raw21037step3Labels := by
      have ha : raw21037step3 = (fun i j => raw21037step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21037step3 raw21037step2; decide +kernel
      have hl : raw21037step3Labels = raw21037step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21037step2 raw21037step2Labels permutation7 permutation2
    mixedMoment B raw21037step3 raw21037step3Labels = mixedMoment B raw21037step4 raw21037step4Labels := by
      have ha : raw21037step4 = -raw21037step3 := by apply Matrix.ext; change ∀ i j, raw21037step4 i j = -(raw21037step3 i j); unfold raw21037step4 raw21037step3; decide +kernel
      have hl : raw21037step4Labels = raw21037step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1741 node1741Labels := by rfl

theorem canonical21038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21038 raw21038Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw21038 raw21038Labels = mixedMoment B raw21038step0 raw21038step0Labels := by
      have hz : ∀ j, raw21038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21038step0 = (fun i j => raw21038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21038step0 raw21038; decide +kernel
      have hl : raw21038step0Labels = raw21038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21038 raw21038Labels permutation346 hz
    mixedMoment B raw21038step0 raw21038step0Labels = mixedMoment B raw21038step1 raw21038step1Labels := by
      have hz : ∀ j, raw21038step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21038step1 = (fun i j => raw21038step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21038step1 raw21038step0; decide +kernel
      have hl : raw21038step1Labels = raw21038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21038step0 raw21038step0Labels permutation56 hz
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical21039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21039 raw21039Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw21039 raw21039Labels = mixedMoment B raw21039step0 raw21039step0Labels := by
      have hz : ∀ j, raw21039 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21039step0 = (fun i j => raw21039 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21039step0 raw21039; decide +kernel
      have hl : raw21039step0Labels = raw21039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21039 raw21039Labels permutation520 hz
    mixedMoment B raw21039step0 raw21039step0Labels = mixedMoment B raw21039step1 raw21039step1Labels := by
      have hz : ∀ j, raw21039step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21039step1 = (fun i j => raw21039step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21039step1 raw21039step0; decide +kernel
      have hl : raw21039step1Labels = raw21039step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21039step0 raw21039step0Labels permutation80 hz
    mixedMoment B raw21039step1 raw21039step1Labels = mixedMoment B raw21039step2 raw21039step2Labels := by
      have hz : ∀ j, raw21039step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21039step2 = (fun i j => raw21039step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21039step2 raw21039step1; decide +kernel
      have hl : raw21039step2Labels = raw21039step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21039step1 raw21039step1Labels permutation14 hz
    mixedMoment B raw21039step2 raw21039step2Labels = mixedMoment B raw21039step3 raw21039step3Labels := by
      have ha : raw21039step3 = (fun i j => raw21039step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21039step3 raw21039step2; decide +kernel
      have hl : raw21039step3Labels = raw21039step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21039step2 raw21039step2Labels permutation6 permutation0
    mixedMoment B raw21039step3 raw21039step3Labels = mixedMoment B raw21039step4 raw21039step4Labels := by
      have ha : raw21039step4 = -raw21039step3 := by apply Matrix.ext; change ∀ i j, raw21039step4 i j = -(raw21039step3 i j); unfold raw21039step4 raw21039step3; decide +kernel
      have hl : raw21039step4Labels = raw21039step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4071 node4071Labels := by rfl

theorem canonical21040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21040 raw21040Labels = mixedMoment B node1203 node1203Labels := by
  calc
    mixedMoment B raw21040 raw21040Labels = mixedMoment B raw21040step0 raw21040step0Labels := by
      have hz : ∀ j, raw21040 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21040step0 = (fun i j => raw21040 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21040step0 raw21040; decide +kernel
      have hl : raw21040step0Labels = raw21040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21040 raw21040Labels permutation265 hz
    _ = mixedMoment B node1203 node1203Labels := by rfl

theorem canonical21041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21041 raw21041Labels = mixedMoment B node2377 node2377Labels := by
  calc
    mixedMoment B raw21041 raw21041Labels = mixedMoment B raw21041step0 raw21041step0Labels := by
      have ha : raw21041step0 = (fun i j => raw21041 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21041step0 raw21041; decide +kernel
      have hl : raw21041step0Labels = raw21041Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21041 raw21041Labels permutation682 permutation2
    mixedMoment B raw21041step0 raw21041step0Labels = mixedMoment B raw21041step1 raw21041step1Labels := by
      have ha : raw21041step1 = -raw21041step0 := by apply Matrix.ext; change ∀ i j, raw21041step1 i j = -(raw21041step0 i j); unfold raw21041step1 raw21041step0; decide +kernel
      have hl : raw21041step1Labels = raw21041step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2377 node2377Labels := by rfl

theorem canonical21042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21042 raw21042Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw21042 raw21042Labels = mixedMoment B raw21042step0 raw21042step0Labels := by
      have hz : ∀ j, raw21042 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21042step0 = (fun i j => raw21042 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21042step0 raw21042; decide +kernel
      have hl : raw21042step0Labels = raw21042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21042 raw21042Labels permutation265 hz
    mixedMoment B raw21042step0 raw21042step0Labels = mixedMoment B raw21042step1 raw21042step1Labels := by
      have ha : raw21042step1 = (fun i j => raw21042step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21042step1 raw21042step0; decide +kernel
      have hl : raw21042step1Labels = raw21042step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21042step0 raw21042step0Labels permutation151 permutation2
    mixedMoment B raw21042step1 raw21042step1Labels = mixedMoment B raw21042step2 raw21042step2Labels := by
      have ha : raw21042step2 = -raw21042step1 := by apply Matrix.ext; change ∀ i j, raw21042step2 i j = -(raw21042step1 i j); unfold raw21042step2 raw21042step1; decide +kernel
      have hl : raw21042step2Labels = raw21042step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2385 node2385Labels := by rfl

theorem canonical21043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21043 raw21043Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw21043 raw21043Labels = mixedMoment B raw21043step0 raw21043step0Labels := by
      have hz : ∀ j, raw21043 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21043step0 = (fun i j => raw21043 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21043step0 raw21043; decide +kernel
      have hl : raw21043step0Labels = raw21043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21043 raw21043Labels permutation265 hz
    mixedMoment B raw21043step0 raw21043step0Labels = mixedMoment B raw21043step1 raw21043step1Labels := by
      have ha : raw21043step1 = (fun i j => raw21043step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21043step1 raw21043step0; decide +kernel
      have hl : raw21043step1Labels = raw21043step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21043step0 raw21043step0Labels permutation149 permutation2
    mixedMoment B raw21043step1 raw21043step1Labels = mixedMoment B raw21043step2 raw21043step2Labels := by
      have ha : raw21043step2 = -raw21043step1 := by apply Matrix.ext; change ∀ i j, raw21043step2 i j = -(raw21043step1 i j); unfold raw21043step2 raw21043step1; decide +kernel
      have hl : raw21043step2Labels = raw21043step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2385 node2385Labels := by rfl

theorem canonical21044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21044 raw21044Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw21044 raw21044Labels = mixedMoment B raw21044step0 raw21044step0Labels := by
      have hz : ∀ j, raw21044 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21044step0 = (fun i j => raw21044 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21044step0 raw21044; decide +kernel
      have hl : raw21044step0Labels = raw21044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21044 raw21044Labels permutation265 hz
    mixedMoment B raw21044step0 raw21044step0Labels = mixedMoment B raw21044step1 raw21044step1Labels := by
      have ha : raw21044step1 = (fun i j => raw21044step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21044step1 raw21044step0; decide +kernel
      have hl : raw21044step1Labels = raw21044step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21044step0 raw21044step0Labels permutation149 permutation2
    mixedMoment B raw21044step1 raw21044step1Labels = mixedMoment B raw21044step2 raw21044step2Labels := by
      have ha : raw21044step2 = -raw21044step1 := by apply Matrix.ext; change ∀ i j, raw21044step2 i j = -(raw21044step1 i j); unfold raw21044step2 raw21044step1; decide +kernel
      have hl : raw21044step2Labels = raw21044step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2664 node2664Labels := by rfl

theorem canonical21045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21045 raw21045Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw21045 raw21045Labels = mixedMoment B raw21045step0 raw21045step0Labels := by
      have hz : ∀ j, raw21045 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21045step0 = (fun i j => raw21045 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21045step0 raw21045; decide +kernel
      have hl : raw21045step0Labels = raw21045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21045 raw21045Labels permutation265 hz
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical21046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21046 raw21046Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw21046 raw21046Labels = mixedMoment B raw21046step0 raw21046step0Labels := by
      have hz : ∀ j, raw21046 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21046step0 = (fun i j => raw21046 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21046step0 raw21046; decide +kernel
      have hl : raw21046step0Labels = raw21046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21046 raw21046Labels permutation265 hz
    mixedMoment B raw21046step0 raw21046step0Labels = mixedMoment B raw21046step1 raw21046step1Labels := by
      have ha : raw21046step1 = (fun i j => raw21046step0 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21046step1 raw21046step0; decide +kernel
      have hl : raw21046step1Labels = raw21046step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21046step0 raw21046step0Labels permutation125 permutation0
    mixedMoment B raw21046step1 raw21046step1Labels = mixedMoment B raw21046step2 raw21046step2Labels := by
      have ha : raw21046step2 = -raw21046step1 := by apply Matrix.ext; change ∀ i j, raw21046step2 i j = -(raw21046step1 i j); unfold raw21046step2 raw21046step1; decide +kernel
      have hl : raw21046step2Labels = raw21046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical21047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21047 raw21047Labels = mixedMoment B node1198 node1198Labels := by
  calc
    mixedMoment B raw21047 raw21047Labels = mixedMoment B raw21047step0 raw21047step0Labels := by
      have ha : raw21047step0 = (fun i j => raw21047 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21047step0 raw21047; decide +kernel
      have hl : raw21047step0Labels = raw21047Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21047 raw21047Labels permutation182 permutation2
    _ = mixedMoment B node1198 node1198Labels := by rfl

theorem canonical21048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21048 raw21048Labels = mixedMoment B node1230 node1230Labels := by
  calc
    mixedMoment B raw21048 raw21048Labels = mixedMoment B raw21048step0 raw21048step0Labels := by
      have hz : ∀ j, raw21048 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21048step0 = (fun i j => raw21048 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21048step0 raw21048; decide +kernel
      have hl : raw21048step0Labels = raw21048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21048 raw21048Labels permutation265 hz
    mixedMoment B raw21048step0 raw21048step0Labels = mixedMoment B raw21048step1 raw21048step1Labels := by
      have ha : raw21048step1 = (fun i j => raw21048step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21048step1 raw21048step0; decide +kernel
      have hl : raw21048step1Labels = raw21048step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21048step0 raw21048step0Labels permutation38 permutation2
    _ = mixedMoment B node1230 node1230Labels := by rfl

theorem canonical21049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21049 raw21049Labels = mixedMoment B node1230 node1230Labels := by
  calc
    mixedMoment B raw21049 raw21049Labels = mixedMoment B raw21049step0 raw21049step0Labels := by
      have hz : ∀ j, raw21049 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21049step0 = (fun i j => raw21049 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21049step0 raw21049; decide +kernel
      have hl : raw21049step0Labels = raw21049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21049 raw21049Labels permutation265 hz
    _ = mixedMoment B node1230 node1230Labels := by rfl

theorem canonical21050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21050 raw21050Labels = mixedMoment B node1205 node1205Labels := by
  calc
    mixedMoment B raw21050 raw21050Labels = mixedMoment B raw21050step0 raw21050step0Labels := by
      have hz : ∀ j, raw21050 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21050step0 = (fun i j => raw21050 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21050step0 raw21050; decide +kernel
      have hl : raw21050step0Labels = raw21050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21050 raw21050Labels permutation265 hz
    _ = mixedMoment B node1205 node1205Labels := by rfl

theorem canonical21051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21051 raw21051Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw21051 raw21051Labels = mixedMoment B raw21051step0 raw21051step0Labels := by
      have hz : ∀ j, raw21051 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21051step0 = (fun i j => raw21051 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21051step0 raw21051; decide +kernel
      have hl : raw21051step0Labels = raw21051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21051 raw21051Labels permutation265 hz
    _ = mixedMoment B node1202 node1202Labels := by rfl

theorem canonical21052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21052 raw21052Labels = mixedMoment B node1897 node1897Labels := by
  calc
    mixedMoment B raw21052 raw21052Labels = mixedMoment B raw21052step0 raw21052step0Labels := by
      have ha : raw21052step0 = (fun i j => raw21052 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21052step0 raw21052; decide +kernel
      have hl : raw21052step0Labels = raw21052Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21052 raw21052Labels permutation682 permutation2
    mixedMoment B raw21052step0 raw21052step0Labels = mixedMoment B raw21052step1 raw21052step1Labels := by
      have ha : raw21052step1 = -raw21052step0 := by apply Matrix.ext; change ∀ i j, raw21052step1 i j = -(raw21052step0 i j); unfold raw21052step1 raw21052step0; decide +kernel
      have hl : raw21052step1Labels = raw21052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1897 node1897Labels := by rfl

theorem canonical21053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21053 raw21053Labels = mixedMoment B node1914 node1914Labels := by
  calc
    mixedMoment B raw21053 raw21053Labels = mixedMoment B raw21053step0 raw21053step0Labels := by
      have hz : ∀ j, raw21053 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21053step0 = (fun i j => raw21053 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21053step0 raw21053; decide +kernel
      have hl : raw21053step0Labels = raw21053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21053 raw21053Labels permutation265 hz
    mixedMoment B raw21053step0 raw21053step0Labels = mixedMoment B raw21053step1 raw21053step1Labels := by
      have ha : raw21053step1 = (fun i j => raw21053step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21053step1 raw21053step0; decide +kernel
      have hl : raw21053step1Labels = raw21053step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21053step0 raw21053step0Labels permutation151 permutation2
    mixedMoment B raw21053step1 raw21053step1Labels = mixedMoment B raw21053step2 raw21053step2Labels := by
      have ha : raw21053step2 = -raw21053step1 := by apply Matrix.ext; change ∀ i j, raw21053step2 i j = -(raw21053step1 i j); unfold raw21053step2 raw21053step1; decide +kernel
      have hl : raw21053step2Labels = raw21053step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1914 node1914Labels := by rfl

theorem canonical21054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21054 raw21054Labels = mixedMoment B node1914 node1914Labels := by
  calc
    mixedMoment B raw21054 raw21054Labels = mixedMoment B raw21054step0 raw21054step0Labels := by
      have hz : ∀ j, raw21054 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21054step0 = (fun i j => raw21054 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21054step0 raw21054; decide +kernel
      have hl : raw21054step0Labels = raw21054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21054 raw21054Labels permutation265 hz
    mixedMoment B raw21054step0 raw21054step0Labels = mixedMoment B raw21054step1 raw21054step1Labels := by
      have ha : raw21054step1 = (fun i j => raw21054step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21054step1 raw21054step0; decide +kernel
      have hl : raw21054step1Labels = raw21054step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21054step0 raw21054step0Labels permutation149 permutation2
    mixedMoment B raw21054step1 raw21054step1Labels = mixedMoment B raw21054step2 raw21054step2Labels := by
      have ha : raw21054step2 = -raw21054step1 := by apply Matrix.ext; change ∀ i j, raw21054step2 i j = -(raw21054step1 i j); unfold raw21054step2 raw21054step1; decide +kernel
      have hl : raw21054step2Labels = raw21054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1914 node1914Labels := by rfl

theorem canonical21055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21055 raw21055Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw21055 raw21055Labels = mixedMoment B raw21055step0 raw21055step0Labels := by
      have hz : ∀ j, raw21055 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21055step0 = (fun i j => raw21055 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21055step0 raw21055; decide +kernel
      have hl : raw21055step0Labels = raw21055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21055 raw21055Labels permutation265 hz
    mixedMoment B raw21055step0 raw21055step0Labels = mixedMoment B raw21055step1 raw21055step1Labels := by
      have ha : raw21055step1 = (fun i j => raw21055step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21055step1 raw21055step0; decide +kernel
      have hl : raw21055step1Labels = raw21055step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21055step0 raw21055step0Labels permutation149 permutation2
    mixedMoment B raw21055step1 raw21055step1Labels = mixedMoment B raw21055step2 raw21055step2Labels := by
      have ha : raw21055step2 = -raw21055step1 := by apply Matrix.ext; change ∀ i j, raw21055step2 i j = -(raw21055step1 i j); unfold raw21055step2 raw21055step1; decide +kernel
      have hl : raw21055step2Labels = raw21055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical21056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21056 raw21056Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw21056 raw21056Labels = mixedMoment B raw21056step0 raw21056step0Labels := by
      have hz : ∀ j, raw21056 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21056step0 = (fun i j => raw21056 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21056step0 raw21056; decide +kernel
      have hl : raw21056step0Labels = raw21056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21056 raw21056Labels permutation265 hz
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical21057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21057 raw21057Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21057 raw21057Labels = mixedMoment B raw21057step0 raw21057step0Labels := by
      have hz : ∀ j, raw21057 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21057step0 = (fun i j => raw21057 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21057step0 raw21057; decide +kernel
      have hl : raw21057step0Labels = raw21057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21057 raw21057Labels permutation265 hz
    mixedMoment B raw21057step0 raw21057step0Labels = mixedMoment B raw21057step1 raw21057step1Labels := by
      have ha : raw21057step1 = (fun i j => raw21057step0 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21057step1 raw21057step0; decide +kernel
      have hl : raw21057step1Labels = raw21057step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21057step0 raw21057step0Labels permutation149 permutation0
    mixedMoment B raw21057step1 raw21057step1Labels = mixedMoment B raw21057step2 raw21057step2Labels := by
      have ha : raw21057step2 = -raw21057step1 := by apply Matrix.ext; change ∀ i j, raw21057step2 i j = -(raw21057step1 i j); unfold raw21057step2 raw21057step1; decide +kernel
      have hl : raw21057step2Labels = raw21057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical21058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21058 raw21058Labels = mixedMoment B node1105 node1105Labels := by
  calc
    mixedMoment B raw21058 raw21058Labels = mixedMoment B raw21058step0 raw21058step0Labels := by
      have ha : raw21058step0 = (fun i j => raw21058 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21058step0 raw21058; decide +kernel
      have hl : raw21058step0Labels = raw21058Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21058 raw21058Labels permutation182 permutation2
    _ = mixedMoment B node1105 node1105Labels := by rfl

theorem canonical21059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21059 raw21059Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw21059 raw21059Labels = mixedMoment B raw21059step0 raw21059step0Labels := by
      have hz : ∀ j, raw21059 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21059step0 = (fun i j => raw21059 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21059step0 raw21059; decide +kernel
      have hl : raw21059step0Labels = raw21059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21059 raw21059Labels permutation265 hz
    _ = mixedMoment B node1123 node1123Labels := by rfl

theorem canonical21060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21060 raw21060Labels = mixedMoment B node1109 node1109Labels := by
  calc
    mixedMoment B raw21060 raw21060Labels = mixedMoment B raw21060step0 raw21060step0Labels := by
      have hz : ∀ j, raw21060 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21060step0 = (fun i j => raw21060 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21060step0 raw21060; decide +kernel
      have hl : raw21060step0Labels = raw21060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21060 raw21060Labels permutation265 hz
    _ = mixedMoment B node1109 node1109Labels := by rfl

theorem canonical21061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21061 raw21061Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw21061 raw21061Labels = mixedMoment B raw21061step0 raw21061step0Labels := by
      have hz : ∀ j, raw21061 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21061step0 = (fun i j => raw21061 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21061step0 raw21061; decide +kernel
      have hl : raw21061step0Labels = raw21061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21061 raw21061Labels permutation265 hz
    mixedMoment B raw21061step0 raw21061step0Labels = mixedMoment B raw21061step1 raw21061step1Labels := by
      have ha : raw21061step1 = (fun i j => raw21061step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21061step1 raw21061step0; decide +kernel
      have hl : raw21061step1Labels = raw21061step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21061step0 raw21061step0Labels permutation151 permutation2
    mixedMoment B raw21061step1 raw21061step1Labels = mixedMoment B raw21061step2 raw21061step2Labels := by
      have ha : raw21061step2 = -raw21061step1 := by apply Matrix.ext; change ∀ i j, raw21061step2 i j = -(raw21061step1 i j); unfold raw21061step2 raw21061step1; decide +kernel
      have hl : raw21061step2Labels = raw21061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node871 node871Labels := by rfl

theorem canonical21062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21062 raw21062Labels = mixedMoment B node1197 node1197Labels := by
  calc
    mixedMoment B raw21062 raw21062Labels = mixedMoment B raw21062step0 raw21062step0Labels := by
      have ha : raw21062step0 = (fun i j => raw21062 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21062step0 raw21062; decide +kernel
      have hl : raw21062step0Labels = raw21062Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21062 raw21062Labels permutation182 permutation2
    _ = mixedMoment B node1197 node1197Labels := by rfl

theorem canonical21063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21063 raw21063Labels = mixedMoment B node1229 node1229Labels := by
  calc
    mixedMoment B raw21063 raw21063Labels = mixedMoment B raw21063step0 raw21063step0Labels := by
      have hz : ∀ j, raw21063 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21063step0 = (fun i j => raw21063 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21063step0 raw21063; decide +kernel
      have hl : raw21063step0Labels = raw21063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21063 raw21063Labels permutation265 hz
    mixedMoment B raw21063step0 raw21063step0Labels = mixedMoment B raw21063step1 raw21063step1Labels := by
      have ha : raw21063step1 = (fun i j => raw21063step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21063step1 raw21063step0; decide +kernel
      have hl : raw21063step1Labels = raw21063step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21063step0 raw21063step0Labels permutation38 permutation2
    _ = mixedMoment B node1229 node1229Labels := by rfl

theorem canonical21064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21064 raw21064Labels = mixedMoment B node1229 node1229Labels := by
  calc
    mixedMoment B raw21064 raw21064Labels = mixedMoment B raw21064step0 raw21064step0Labels := by
      have hz : ∀ j, raw21064 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21064step0 = (fun i j => raw21064 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21064step0 raw21064; decide +kernel
      have hl : raw21064step0Labels = raw21064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21064 raw21064Labels permutation265 hz
    _ = mixedMoment B node1229 node1229Labels := by rfl

theorem canonical21065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21065 raw21065Labels = mixedMoment B node1204 node1204Labels := by
  calc
    mixedMoment B raw21065 raw21065Labels = mixedMoment B raw21065step0 raw21065step0Labels := by
      have hz : ∀ j, raw21065 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21065step0 = (fun i j => raw21065 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21065step0 raw21065; decide +kernel
      have hl : raw21065step0Labels = raw21065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21065 raw21065Labels permutation265 hz
    _ = mixedMoment B node1204 node1204Labels := by rfl

theorem canonical21071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21071 raw21071Labels = mixedMoment B node1199 node1199Labels := by
  calc
    mixedMoment B raw21071 raw21071Labels = mixedMoment B raw21071step0 raw21071step0Labels := by
      have hz : ∀ j, raw21071 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21071step0 = (fun i j => raw21071 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21071step0 raw21071; decide +kernel
      have hl : raw21071step0Labels = raw21071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21071 raw21071Labels permutation265 hz
    _ = mixedMoment B node1199 node1199Labels := by rfl

theorem canonical21072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21072 raw21072Labels = mixedMoment B node1592 node1592Labels := by
  calc
    mixedMoment B raw21072 raw21072Labels = mixedMoment B raw21072step0 raw21072step0Labels := by
      have ha : raw21072step0 = (fun i j => raw21072 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21072step0 raw21072; decide +kernel
      have hl : raw21072step0Labels = raw21072Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21072 raw21072Labels permutation682 permutation2
    mixedMoment B raw21072step0 raw21072step0Labels = mixedMoment B raw21072step1 raw21072step1Labels := by
      have ha : raw21072step1 = -raw21072step0 := by apply Matrix.ext; change ∀ i j, raw21072step1 i j = -(raw21072step0 i j); unfold raw21072step1 raw21072step0; decide +kernel
      have hl : raw21072step1Labels = raw21072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1592 node1592Labels := by rfl

theorem canonical21073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21073 raw21073Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw21073 raw21073Labels = mixedMoment B raw21073step0 raw21073step0Labels := by
      have hz : ∀ j, raw21073 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21073step0 = (fun i j => raw21073 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21073step0 raw21073; decide +kernel
      have hl : raw21073step0Labels = raw21073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21073 raw21073Labels permutation265 hz
    mixedMoment B raw21073step0 raw21073step0Labels = mixedMoment B raw21073step1 raw21073step1Labels := by
      have ha : raw21073step1 = (fun i j => raw21073step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21073step1 raw21073step0; decide +kernel
      have hl : raw21073step1Labels = raw21073step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21073step0 raw21073step0Labels permutation151 permutation2
    mixedMoment B raw21073step1 raw21073step1Labels = mixedMoment B raw21073step2 raw21073step2Labels := by
      have ha : raw21073step2 = -raw21073step1 := by apply Matrix.ext; change ∀ i j, raw21073step2 i j = -(raw21073step1 i j); unfold raw21073step2 raw21073step1; decide +kernel
      have hl : raw21073step2Labels = raw21073step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1602 node1602Labels := by rfl

theorem canonical21074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21074 raw21074Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw21074 raw21074Labels = mixedMoment B raw21074step0 raw21074step0Labels := by
      have hz : ∀ j, raw21074 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21074step0 = (fun i j => raw21074 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21074step0 raw21074; decide +kernel
      have hl : raw21074step0Labels = raw21074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21074 raw21074Labels permutation265 hz
    mixedMoment B raw21074step0 raw21074step0Labels = mixedMoment B raw21074step1 raw21074step1Labels := by
      have ha : raw21074step1 = (fun i j => raw21074step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21074step1 raw21074step0; decide +kernel
      have hl : raw21074step1Labels = raw21074step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21074step0 raw21074step0Labels permutation149 permutation2
    mixedMoment B raw21074step1 raw21074step1Labels = mixedMoment B raw21074step2 raw21074step2Labels := by
      have ha : raw21074step2 = -raw21074step1 := by apply Matrix.ext; change ∀ i j, raw21074step2 i j = -(raw21074step1 i j); unfold raw21074step2 raw21074step1; decide +kernel
      have hl : raw21074step2Labels = raw21074step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1602 node1602Labels := by rfl

theorem canonical21075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21075 raw21075Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw21075 raw21075Labels = mixedMoment B raw21075step0 raw21075step0Labels := by
      have hz : ∀ j, raw21075 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21075step0 = (fun i j => raw21075 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21075step0 raw21075; decide +kernel
      have hl : raw21075step0Labels = raw21075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21075 raw21075Labels permutation520 hz
    mixedMoment B raw21075step0 raw21075step0Labels = mixedMoment B raw21075step1 raw21075step1Labels := by
      have hz : ∀ j, raw21075step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21075step1 = (fun i j => raw21075step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21075step1 raw21075step0; decide +kernel
      have hl : raw21075step1Labels = raw21075step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21075step0 raw21075step0Labels permutation56 hz
    mixedMoment B raw21075step1 raw21075step1Labels = mixedMoment B raw21075step2 raw21075step2Labels := by
      have ha : raw21075step2 = (fun i j => raw21075step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21075step2 raw21075step1; decide +kernel
      have hl : raw21075step2Labels = raw21075step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21075step1 raw21075step1Labels permutation29 permutation2
    mixedMoment B raw21075step2 raw21075step2Labels = mixedMoment B raw21075step3 raw21075step3Labels := by
      have ha : raw21075step3 = -raw21075step2 := by apply Matrix.ext; change ∀ i j, raw21075step3 i j = -(raw21075step2 i j); unfold raw21075step3 raw21075step2; decide +kernel
      have hl : raw21075step3Labels = raw21075step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical21076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21076 raw21076Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw21076 raw21076Labels = mixedMoment B raw21076step0 raw21076step0Labels := by
      have hz : ∀ j, raw21076 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21076step0 = (fun i j => raw21076 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21076step0 raw21076; decide +kernel
      have hl : raw21076step0Labels = raw21076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21076 raw21076Labels permutation265 hz
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical21077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21077 raw21077Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw21077 raw21077Labels = mixedMoment B raw21077step0 raw21077step0Labels := by
      have hz : ∀ j, raw21077 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21077step0 = (fun i j => raw21077 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21077step0 raw21077; decide +kernel
      have hl : raw21077step0Labels = raw21077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21077 raw21077Labels permutation520 hz
    mixedMoment B raw21077step0 raw21077step0Labels = mixedMoment B raw21077step1 raw21077step1Labels := by
      have hz : ∀ j, raw21077step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21077step1 = (fun i j => raw21077step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21077step1 raw21077step0; decide +kernel
      have hl : raw21077step1Labels = raw21077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21077step0 raw21077step0Labels permutation56 hz
    mixedMoment B raw21077step1 raw21077step1Labels = mixedMoment B raw21077step2 raw21077step2Labels := by
      have ha : raw21077step2 = (fun i j => raw21077step1 (permutation29 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21077step2 raw21077step1; decide +kernel
      have hl : raw21077step2Labels = raw21077step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21077step1 raw21077step1Labels permutation29 permutation0
    mixedMoment B raw21077step2 raw21077step2Labels = mixedMoment B raw21077step3 raw21077step3Labels := by
      have ha : raw21077step3 = -raw21077step2 := by apply Matrix.ext; change ∀ i j, raw21077step3 i j = -(raw21077step2 i j); unfold raw21077step3 raw21077step2; decide +kernel
      have hl : raw21077step3Labels = raw21077step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical21078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21078 raw21078Labels = mixedMoment B node1055 node1055Labels := by
  calc
    mixedMoment B raw21078 raw21078Labels = mixedMoment B raw21078step0 raw21078step0Labels := by
      have hz : ∀ j, raw21078 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21078step0 = (fun i j => raw21078 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21078step0 raw21078; decide +kernel
      have hl : raw21078step0Labels = raw21078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21078 raw21078Labels permutation434 hz
    mixedMoment B raw21078step0 raw21078step0Labels = mixedMoment B raw21078step1 raw21078step1Labels := by
      have hz : ∀ j, raw21078step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21078step1 = (fun i j => raw21078step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21078step1 raw21078step0; decide +kernel
      have hl : raw21078step1Labels = raw21078step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21078step0 raw21078step0Labels permutation80 hz
    _ = mixedMoment B node1055 node1055Labels := by rfl

theorem canonical21079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21079 raw21079Labels = mixedMoment B node2130 node2130Labels := by
  calc
    mixedMoment B raw21079 raw21079Labels = mixedMoment B raw21079step0 raw21079step0Labels := by
      have hz : ∀ j, raw21079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21079step0 = (fun i j => raw21079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21079step0 raw21079; decide +kernel
      have hl : raw21079step0Labels = raw21079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21079 raw21079Labels permutation434 hz
    mixedMoment B raw21079step0 raw21079step0Labels = mixedMoment B raw21079step1 raw21079step1Labels := by
      have hz : ∀ j, raw21079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21079step1 = (fun i j => raw21079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21079step1 raw21079step0; decide +kernel
      have hl : raw21079step1Labels = raw21079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21079step0 raw21079step0Labels permutation80 hz
    _ = mixedMoment B node2130 node2130Labels := by rfl

theorem canonical21080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21080 raw21080Labels = mixedMoment B node2032 node2032Labels := by
  calc
    mixedMoment B raw21080 raw21080Labels = mixedMoment B raw21080step0 raw21080step0Labels := by
      have hz : ∀ j, raw21080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21080step0 = (fun i j => raw21080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21080step0 raw21080; decide +kernel
      have hl : raw21080step0Labels = raw21080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21080 raw21080Labels permutation434 hz
    mixedMoment B raw21080step0 raw21080step0Labels = mixedMoment B raw21080step1 raw21080step1Labels := by
      have ha : raw21080step1 = (fun i j => raw21080step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21080step1 raw21080step0; decide +kernel
      have hl : raw21080step1Labels = raw21080step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21080step0 raw21080step0Labels permutation38 permutation2
    _ = mixedMoment B node2032 node2032Labels := by rfl

theorem canonical21081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21081 raw21081Labels = mixedMoment B node2032 node2032Labels := by
  calc
    mixedMoment B raw21081 raw21081Labels = mixedMoment B raw21081step0 raw21081step0Labels := by
      have hz : ∀ j, raw21081 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21081step0 = (fun i j => raw21081 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21081step0 raw21081; decide +kernel
      have hl : raw21081step0Labels = raw21081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21081 raw21081Labels permutation346 hz
    mixedMoment B raw21081step0 raw21081step0Labels = mixedMoment B raw21081step1 raw21081step1Labels := by
      have ha : raw21081step1 = (fun i j => raw21081step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21081step1 raw21081step0; decide +kernel
      have hl : raw21081step1Labels = raw21081step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21081step0 raw21081step0Labels permutation38 permutation2
    _ = mixedMoment B node2032 node2032Labels := by rfl

theorem canonical21082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21082 raw21082Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw21082 raw21082Labels = mixedMoment B raw21082step0 raw21082step0Labels := by
      have hz : ∀ j, raw21082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21082step0 = (fun i j => raw21082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21082step0 raw21082; decide +kernel
      have hl : raw21082step0Labels = raw21082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21082 raw21082Labels permutation434 hz
    mixedMoment B raw21082step0 raw21082step0Labels = mixedMoment B raw21082step1 raw21082step1Labels := by
      have hz : ∀ j, raw21082step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21082step1 = (fun i j => raw21082step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21082step1 raw21082step0; decide +kernel
      have hl : raw21082step1Labels = raw21082step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21082step0 raw21082step0Labels permutation80 hz
    mixedMoment B raw21082step1 raw21082step1Labels = mixedMoment B raw21082step2 raw21082step2Labels := by
      have ha : raw21082step2 = (fun i j => raw21082step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21082step2 raw21082step1; decide +kernel
      have hl : raw21082step2Labels = raw21082step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21082step1 raw21082step1Labels permutation10 permutation2
    _ = mixedMoment B node2218 node2218Labels := by rfl

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

theorem canonical21085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21085 raw21085Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw21085 raw21085Labels = mixedMoment B raw21085step0 raw21085step0Labels := by
      have hz : ∀ j, raw21085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21085step0 = (fun i j => raw21085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21085step0 raw21085; decide +kernel
      have hl : raw21085step0Labels = raw21085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21085 raw21085Labels permutation434 hz
    mixedMoment B raw21085step0 raw21085step0Labels = mixedMoment B raw21085step1 raw21085step1Labels := by
      have hz : ∀ j, raw21085step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21085step1 = (fun i j => raw21085step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21085step1 raw21085step0; decide +kernel
      have hl : raw21085step1Labels = raw21085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21085step0 raw21085step0Labels permutation80 hz
    mixedMoment B raw21085step1 raw21085step1Labels = mixedMoment B raw21085step2 raw21085step2Labels := by
      have ha : raw21085step2 = (fun i j => raw21085step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21085step2 raw21085step1; decide +kernel
      have hl : raw21085step2Labels = raw21085step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21085step1 raw21085step1Labels permutation10 permutation2
    _ = mixedMoment B node1075 node1075Labels := by rfl

theorem canonical21086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21086 raw21086Labels = mixedMoment B node1053 node1053Labels := by
  calc
    mixedMoment B raw21086 raw21086Labels = mixedMoment B raw21086step0 raw21086step0Labels := by
      have hz : ∀ j, raw21086 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21086step0 = (fun i j => raw21086 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21086step0 raw21086; decide +kernel
      have hl : raw21086step0Labels = raw21086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21086 raw21086Labels permutation434 hz
    mixedMoment B raw21086step0 raw21086step0Labels = mixedMoment B raw21086step1 raw21086step1Labels := by
      have ha : raw21086step1 = (fun i j => raw21086step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21086step1 raw21086step0; decide +kernel
      have hl : raw21086step1Labels = raw21086step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21086step0 raw21086step0Labels permutation34 permutation2
    _ = mixedMoment B node1053 node1053Labels := by rfl

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

theorem canonical21088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21088 raw21088Labels = mixedMoment B node1062 node1062Labels := by
  calc
    mixedMoment B raw21088 raw21088Labels = mixedMoment B raw21088step0 raw21088step0Labels := by
      have hz : ∀ j, raw21088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21088step0 = (fun i j => raw21088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21088step0 raw21088; decide +kernel
      have hl : raw21088step0Labels = raw21088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21088 raw21088Labels permutation434 hz
    mixedMoment B raw21088step0 raw21088step0Labels = mixedMoment B raw21088step1 raw21088step1Labels := by
      have hz : ∀ j, raw21088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21088step1 = (fun i j => raw21088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21088step1 raw21088step0; decide +kernel
      have hl : raw21088step1Labels = raw21088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21088step0 raw21088step0Labels permutation80 hz
    _ = mixedMoment B node1062 node1062Labels := by rfl

theorem canonical21089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21089 raw21089Labels = mixedMoment B node991 node991Labels := by
  calc
    mixedMoment B raw21089 raw21089Labels = mixedMoment B raw21089step0 raw21089step0Labels := by
      have hz : ∀ j, raw21089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21089step0 = (fun i j => raw21089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21089step0 raw21089; decide +kernel
      have hl : raw21089step0Labels = raw21089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21089 raw21089Labels permutation346 hz
    mixedMoment B raw21089step0 raw21089step0Labels = mixedMoment B raw21089step1 raw21089step1Labels := by
      have ha : raw21089step1 = (fun i j => raw21089step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21089step1 raw21089step0; decide +kernel
      have hl : raw21089step1Labels = raw21089step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21089step0 raw21089step0Labels permutation38 permutation2
    _ = mixedMoment B node991 node991Labels := by rfl

theorem canonical21090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21090 raw21090Labels = mixedMoment B node2121 node2121Labels := by
  calc
    mixedMoment B raw21090 raw21090Labels = mixedMoment B raw21090step0 raw21090step0Labels := by
      have hz : ∀ j, raw21090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21090step0 = (fun i j => raw21090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21090step0 raw21090; decide +kernel
      have hl : raw21090step0Labels = raw21090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21090 raw21090Labels permutation346 hz
    _ = mixedMoment B node2121 node2121Labels := by rfl

theorem canonical21091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21091 raw21091Labels = mixedMoment B node1992 node1992Labels := by
  calc
    mixedMoment B raw21091 raw21091Labels = mixedMoment B raw21091step0 raw21091step0Labels := by
      have ha : raw21091step0 = (fun i j => raw21091 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21091step0 raw21091; decide +kernel
      have hl : raw21091step0Labels = raw21091Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21091 raw21091Labels permutation182 permutation2
    _ = mixedMoment B node1992 node1992Labels := by rfl

theorem canonical21092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21092 raw21092Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw21092 raw21092Labels = mixedMoment B raw21092step0 raw21092step0Labels := by
      have hz : ∀ j, raw21092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21092step0 = (fun i j => raw21092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21092step0 raw21092; decide +kernel
      have hl : raw21092step0Labels = raw21092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21092 raw21092Labels permutation346 hz
    mixedMoment B raw21092step0 raw21092step0Labels = mixedMoment B raw21092step1 raw21092step1Labels := by
      have ha : raw21092step1 = (fun i j => raw21092step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21092step1 raw21092step0; decide +kernel
      have hl : raw21092step1Labels = raw21092step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21092step0 raw21092step0Labels permutation38 permutation2
    _ = mixedMoment B node1926 node1926Labels := by rfl

theorem canonical21093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21093 raw21093Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw21093 raw21093Labels = mixedMoment B raw21093step0 raw21093step0Labels := by
      have hz : ∀ j, raw21093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21093step0 = (fun i j => raw21093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21093step0 raw21093; decide +kernel
      have hl : raw21093step0Labels = raw21093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21093 raw21093Labels permutation346 hz
    mixedMoment B raw21093step0 raw21093step0Labels = mixedMoment B raw21093step1 raw21093step1Labels := by
      have ha : raw21093step1 = (fun i j => raw21093step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21093step1 raw21093step0; decide +kernel
      have hl : raw21093step1Labels = raw21093step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21093step0 raw21093step0Labels permutation40 permutation2
    _ = mixedMoment B node2197 node2197Labels := by rfl

theorem canonical21094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21094 raw21094Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw21094 raw21094Labels = mixedMoment B raw21094step0 raw21094step0Labels := by
      have hz : ∀ j, raw21094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21094step0 = (fun i j => raw21094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21094step0 raw21094; decide +kernel
      have hl : raw21094step0Labels = raw21094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21094 raw21094Labels permutation346 hz
    mixedMoment B raw21094step0 raw21094step0Labels = mixedMoment B raw21094step1 raw21094step1Labels := by
      have ha : raw21094step1 = (fun i j => raw21094step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21094step1 raw21094step0; decide +kernel
      have hl : raw21094step1Labels = raw21094step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21094step0 raw21094step0Labels permutation38 permutation2
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical21095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21095 raw21095Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21095 raw21095Labels = mixedMoment B raw21095step0 raw21095step0Labels := by
      have hz : ∀ j, raw21095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21095step0 = (fun i j => raw21095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21095step0 raw21095; decide +kernel
      have hl : raw21095step0Labels = raw21095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21095 raw21095Labels permutation346 hz
    mixedMoment B raw21095step0 raw21095step0Labels = mixedMoment B raw21095step1 raw21095step1Labels := by
      have ha : raw21095step1 = (fun i j => raw21095step0 (permutation41 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21095step1 raw21095step0; decide +kernel
      have hl : raw21095step1Labels = raw21095step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21095step0 raw21095step0Labels permutation41 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical21096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21096 raw21096Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw21096 raw21096Labels = mixedMoment B raw21096step0 raw21096step0Labels := by
      have hz : ∀ j, raw21096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21096step0 = (fun i j => raw21096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21096step0 raw21096; decide +kernel
      have hl : raw21096step0Labels = raw21096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21096 raw21096Labels permutation346 hz
    mixedMoment B raw21096step0 raw21096step0Labels = mixedMoment B raw21096step1 raw21096step1Labels := by
      have ha : raw21096step1 = (fun i j => raw21096step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21096step1 raw21096step0; decide +kernel
      have hl : raw21096step1Labels = raw21096step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21096step0 raw21096step0Labels permutation40 permutation2
    _ = mixedMoment B node1005 node1005Labels := by rfl

theorem canonical21097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21097 raw21097Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw21097 raw21097Labels = mixedMoment B raw21097step0 raw21097step0Labels := by
      have ha : raw21097step0 = (fun i j => raw21097 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21097step0 raw21097; decide +kernel
      have hl : raw21097step0Labels = raw21097Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21097 raw21097Labels permutation200 permutation2
    _ = mixedMoment B node988 node988Labels := by rfl

theorem canonical21098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21098 raw21098Labels = mixedMoment B node1054 node1054Labels := by
  calc
    mixedMoment B raw21098 raw21098Labels = mixedMoment B raw21098step0 raw21098step0Labels := by
      have hz : ∀ j, raw21098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21098step0 = (fun i j => raw21098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21098step0 raw21098; decide +kernel
      have hl : raw21098step0Labels = raw21098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21098 raw21098Labels permutation346 hz
    _ = mixedMoment B node1054 node1054Labels := by rfl

theorem canonical21099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21099 raw21099Labels = mixedMoment B node993 node993Labels := by
  calc
    mixedMoment B raw21099 raw21099Labels = mixedMoment B raw21099step0 raw21099step0Labels := by
      have hz : ∀ j, raw21099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21099step0 = (fun i j => raw21099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21099step0 raw21099; decide +kernel
      have hl : raw21099step0Labels = raw21099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21099 raw21099Labels permutation346 hz
    mixedMoment B raw21099step0 raw21099step0Labels = mixedMoment B raw21099step1 raw21099step1Labels := by
      have ha : raw21099step1 = (fun i j => raw21099step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21099step1 raw21099step0; decide +kernel
      have hl : raw21099step1Labels = raw21099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21099step0 raw21099step0Labels permutation38 permutation2
    _ = mixedMoment B node993 node993Labels := by rfl

theorem canonical21100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21100 raw21100Labels = mixedMoment B node989 node989Labels := by
  calc
    mixedMoment B raw21100 raw21100Labels = mixedMoment B raw21100step0 raw21100step0Labels := by
      have hz : ∀ j, raw21100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21100step0 = (fun i j => raw21100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21100step0 raw21100; decide +kernel
      have hl : raw21100step0Labels = raw21100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21100 raw21100Labels permutation346 hz
    mixedMoment B raw21100step0 raw21100step0Labels = mixedMoment B raw21100step1 raw21100step1Labels := by
      have ha : raw21100step1 = (fun i j => raw21100step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21100step1 raw21100step0; decide +kernel
      have hl : raw21100step1Labels = raw21100step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21100step0 raw21100step0Labels permutation38 permutation2
    _ = mixedMoment B node989 node989Labels := by rfl

theorem canonical21101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21101 raw21101Labels = mixedMoment B node2119 node2119Labels := by
  calc
    mixedMoment B raw21101 raw21101Labels = mixedMoment B raw21101step0 raw21101step0Labels := by
      have hz : ∀ j, raw21101 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21101step0 = (fun i j => raw21101 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21101step0 raw21101; decide +kernel
      have hl : raw21101step0Labels = raw21101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21101 raw21101Labels permutation346 hz
    _ = mixedMoment B node2119 node2119Labels := by rfl

theorem canonical21102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21102 raw21102Labels = mixedMoment B node1991 node1991Labels := by
  calc
    mixedMoment B raw21102 raw21102Labels = mixedMoment B raw21102step0 raw21102step0Labels := by
      have ha : raw21102step0 = (fun i j => raw21102 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21102step0 raw21102; decide +kernel
      have hl : raw21102step0Labels = raw21102Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21102 raw21102Labels permutation182 permutation2
    _ = mixedMoment B node1991 node1991Labels := by rfl

theorem canonical21103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21103 raw21103Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw21103 raw21103Labels = mixedMoment B raw21103step0 raw21103step0Labels := by
      have hz : ∀ j, raw21103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21103step0 = (fun i j => raw21103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21103step0 raw21103; decide +kernel
      have hl : raw21103step0Labels = raw21103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21103 raw21103Labels permutation346 hz
    mixedMoment B raw21103step0 raw21103step0Labels = mixedMoment B raw21103step1 raw21103step1Labels := by
      have ha : raw21103step1 = (fun i j => raw21103step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21103step1 raw21103step0; decide +kernel
      have hl : raw21103step1Labels = raw21103step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21103step0 raw21103step0Labels permutation38 permutation2
    _ = mixedMoment B node1924 node1924Labels := by rfl

theorem canonical21104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21104 raw21104Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw21104 raw21104Labels = mixedMoment B raw21104step0 raw21104step0Labels := by
      have hz : ∀ j, raw21104 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21104step0 = (fun i j => raw21104 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21104step0 raw21104; decide +kernel
      have hl : raw21104step0Labels = raw21104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21104 raw21104Labels permutation520 hz
    mixedMoment B raw21104step0 raw21104step0Labels = mixedMoment B raw21104step1 raw21104step1Labels := by
      have hz : ∀ j, raw21104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21104step1 = (fun i j => raw21104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21104step1 raw21104step0; decide +kernel
      have hl : raw21104step1Labels = raw21104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21104step0 raw21104step0Labels permutation80 hz
    mixedMoment B raw21104step1 raw21104step1Labels = mixedMoment B raw21104step2 raw21104step2Labels := by
      have ha : raw21104step2 = (fun i j => raw21104step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21104step2 raw21104step1; decide +kernel
      have hl : raw21104step2Labels = raw21104step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21104step1 raw21104step1Labels permutation10 permutation2
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical21105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21105 raw21105Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw21105 raw21105Labels = mixedMoment B raw21105step0 raw21105step0Labels := by
      have hz : ∀ j, raw21105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21105step0 = (fun i j => raw21105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21105step0 raw21105; decide +kernel
      have hl : raw21105step0Labels = raw21105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21105 raw21105Labels permutation346 hz
    mixedMoment B raw21105step0 raw21105step0Labels = mixedMoment B raw21105step1 raw21105step1Labels := by
      have ha : raw21105step1 = (fun i j => raw21105step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21105step1 raw21105step0; decide +kernel
      have hl : raw21105step1Labels = raw21105step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21105step0 raw21105step0Labels permutation38 permutation2
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical21106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21106 raw21106Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw21106 raw21106Labels = mixedMoment B raw21106step0 raw21106step0Labels := by
      have hz : ∀ j, raw21106 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21106step0 = (fun i j => raw21106 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21106step0 raw21106; decide +kernel
      have hl : raw21106step0Labels = raw21106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21106 raw21106Labels permutation520 hz
    mixedMoment B raw21106step0 raw21106step0Labels = mixedMoment B raw21106step1 raw21106step1Labels := by
      have hz : ∀ j, raw21106step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21106step1 = (fun i j => raw21106step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21106step1 raw21106step0; decide +kernel
      have hl : raw21106step1Labels = raw21106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21106step0 raw21106step0Labels permutation80 hz
    mixedMoment B raw21106step1 raw21106step1Labels = mixedMoment B raw21106step2 raw21106step2Labels := by
      have ha : raw21106step2 = (fun i j => raw21106step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21106step2 raw21106step1; decide +kernel
      have hl : raw21106step2Labels = raw21106step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21106step1 raw21106step1Labels permutation10 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical21107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21107 raw21107Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw21107 raw21107Labels = mixedMoment B raw21107step0 raw21107step0Labels := by
      have hz : ∀ j, raw21107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21107step0 = (fun i j => raw21107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21107step0 raw21107; decide +kernel
      have hl : raw21107step0Labels = raw21107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21107 raw21107Labels permutation346 hz
    mixedMoment B raw21107step0 raw21107step0Labels = mixedMoment B raw21107step1 raw21107step1Labels := by
      have ha : raw21107step1 = (fun i j => raw21107step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21107step1 raw21107step0; decide +kernel
      have hl : raw21107step1Labels = raw21107step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21107step0 raw21107step0Labels permutation40 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical21108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21108 raw21108Labels = mixedMoment B node987 node987Labels := by
  calc
    mixedMoment B raw21108 raw21108Labels = mixedMoment B raw21108step0 raw21108step0Labels := by
      have ha : raw21108step0 = (fun i j => raw21108 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21108step0 raw21108; decide +kernel
      have hl : raw21108step0Labels = raw21108Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21108 raw21108Labels permutation200 permutation2
    _ = mixedMoment B node987 node987Labels := by rfl

theorem canonical21109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21109 raw21109Labels = mixedMoment B node1053 node1053Labels := by
  calc
    mixedMoment B raw21109 raw21109Labels = mixedMoment B raw21109step0 raw21109step0Labels := by
      have hz : ∀ j, raw21109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21109step0 = (fun i j => raw21109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21109step0 raw21109; decide +kernel
      have hl : raw21109step0Labels = raw21109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21109 raw21109Labels permutation346 hz
    _ = mixedMoment B node1053 node1053Labels := by rfl

theorem canonical21110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21110 raw21110Labels = mixedMoment B node992 node992Labels := by
  calc
    mixedMoment B raw21110 raw21110Labels = mixedMoment B raw21110step0 raw21110step0Labels := by
      have hz : ∀ j, raw21110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21110step0 = (fun i j => raw21110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21110step0 raw21110; decide +kernel
      have hl : raw21110step0Labels = raw21110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21110 raw21110Labels permutation346 hz
    mixedMoment B raw21110step0 raw21110step0Labels = mixedMoment B raw21110step1 raw21110step1Labels := by
      have ha : raw21110step1 = (fun i j => raw21110step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21110step1 raw21110step0; decide +kernel
      have hl : raw21110step1Labels = raw21110step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21110step0 raw21110step0Labels permutation38 permutation2
    _ = mixedMoment B node992 node992Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node871 node871Labels = Sparse.eval nodeValue871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 871) = mixedMoment B node871 node871Labels := rfl
  simpa [nodeValue871, Sparse.eval] using hc.symm

theorem sound893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node893 node893Labels = Sparse.eval nodeValue893 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 893) = mixedMoment B node893 node893Labels := rfl
  simpa [nodeValue893, Sparse.eval] using hc.symm

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

theorem sound987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node987 node987Labels = Sparse.eval nodeValue987 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 987) = mixedMoment B node987 node987Labels := rfl
  simpa [nodeValue987, Sparse.eval] using hc.symm

theorem sound988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node988 node988Labels = Sparse.eval nodeValue988 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 988) = mixedMoment B node988 node988Labels := rfl
  simpa [nodeValue988, Sparse.eval] using hc.symm

theorem sound989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node989 node989Labels = Sparse.eval nodeValue989 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 989) = mixedMoment B node989 node989Labels := rfl
  simpa [nodeValue989, Sparse.eval] using hc.symm

theorem sound991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node991 node991Labels = Sparse.eval nodeValue991 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 991) = mixedMoment B node991 node991Labels := rfl
  simpa [nodeValue991, Sparse.eval] using hc.symm

theorem sound992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node992 node992Labels = Sparse.eval nodeValue992 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 992) = mixedMoment B node992 node992Labels := rfl
  simpa [nodeValue992, Sparse.eval] using hc.symm

theorem sound993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node993 node993Labels = Sparse.eval nodeValue993 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 993) = mixedMoment B node993 node993Labels := rfl
  simpa [nodeValue993, Sparse.eval] using hc.symm

theorem sound1000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1000 node1000Labels = Sparse.eval nodeValue1000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1000) = mixedMoment B node1000 node1000Labels := rfl
  simpa [nodeValue1000, Sparse.eval] using hc.symm

theorem sound1005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1005 node1005Labels = Sparse.eval nodeValue1005 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1005) = mixedMoment B node1005 node1005Labels := rfl
  simpa [nodeValue1005, Sparse.eval] using hc.symm

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

theorem sound1055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1055 node1055Labels = Sparse.eval nodeValue1055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1055) = mixedMoment B node1055 node1055Labels := rfl
  simpa [nodeValue1055, Sparse.eval] using hc.symm

theorem sound1062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1062 node1062Labels = Sparse.eval nodeValue1062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1062) = mixedMoment B node1062 node1062Labels := rfl
  simpa [nodeValue1062, Sparse.eval] using hc.symm

theorem sound1075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1075 node1075Labels = Sparse.eval nodeValue1075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1075) = mixedMoment B node1075 node1075Labels := rfl
  simpa [nodeValue1075, Sparse.eval] using hc.symm

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

theorem sound1098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1098 node1098Labels = Sparse.eval nodeValue1098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1098) = mixedMoment B node1098 node1098Labels := rfl
  simpa [nodeValue1098, Sparse.eval] using hc.symm

theorem sound1103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1103 node1103Labels = Sparse.eval nodeValue1103 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1103) = mixedMoment B node1103 node1103Labels := rfl
  simpa [nodeValue1103, Sparse.eval] using hc.symm

theorem sound1105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1105 node1105Labels = Sparse.eval nodeValue1105 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1105) = mixedMoment B node1105 node1105Labels := rfl
  simpa [nodeValue1105, Sparse.eval] using hc.symm

theorem sound1109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1109 node1109Labels = Sparse.eval nodeValue1109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1109) = mixedMoment B node1109 node1109Labels := rfl
  simpa [nodeValue1109, Sparse.eval] using hc.symm

theorem sound1123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1123 node1123Labels = Sparse.eval nodeValue1123 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1123) = mixedMoment B node1123 node1123Labels := rfl
  simpa [nodeValue1123, Sparse.eval] using hc.symm

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

theorem sound1184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1184 node1184Labels = Sparse.eval nodeValue1184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1184) = mixedMoment B node1184 node1184Labels := rfl
  simpa [nodeValue1184, Sparse.eval] using hc.symm

theorem sound1186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1186 node1186Labels = Sparse.eval nodeValue1186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1186) = mixedMoment B node1186 node1186Labels := rfl
  simpa [nodeValue1186, Sparse.eval] using hc.symm

theorem sound1190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1190 node1190Labels = Sparse.eval nodeValue1190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1190) = mixedMoment B node1190 node1190Labels := rfl
  simpa [nodeValue1190, Sparse.eval] using hc.symm

theorem sound1192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1192 node1192Labels = Sparse.eval nodeValue1192 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1192) = mixedMoment B node1192 node1192Labels := rfl
  simpa [nodeValue1192, Sparse.eval] using hc.symm

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

theorem sound1199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1199 node1199Labels = Sparse.eval nodeValue1199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1199) = mixedMoment B node1199 node1199Labels := rfl
  simpa [nodeValue1199, Sparse.eval] using hc.symm

theorem sound1202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1202 node1202Labels = Sparse.eval nodeValue1202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1202) = mixedMoment B node1202 node1202Labels := rfl
  simpa [nodeValue1202, Sparse.eval] using hc.symm

theorem sound1203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1203 node1203Labels = Sparse.eval nodeValue1203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1203) = mixedMoment B node1203 node1203Labels := rfl
  simpa [nodeValue1203, Sparse.eval] using hc.symm

theorem sound1204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1204 node1204Labels = Sparse.eval nodeValue1204 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1204) = mixedMoment B node1204 node1204Labels := rfl
  simpa [nodeValue1204, Sparse.eval] using hc.symm

theorem sound1205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1205 node1205Labels = Sparse.eval nodeValue1205 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1205) = mixedMoment B node1205 node1205Labels := rfl
  simpa [nodeValue1205, Sparse.eval] using hc.symm

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

theorem sound1229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1229 node1229Labels = Sparse.eval nodeValue1229 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1229) = mixedMoment B node1229 node1229Labels := rfl
  simpa [nodeValue1229, Sparse.eval] using hc.symm

theorem sound1230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1230 node1230Labels = Sparse.eval nodeValue1230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1230) = mixedMoment B node1230 node1230Labels := rfl
  simpa [nodeValue1230, Sparse.eval] using hc.symm

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

theorem sound1287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1287 node1287Labels = Sparse.eval nodeValue1287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1287) = mixedMoment B node1287 node1287Labels := rfl
  simpa [nodeValue1287, Sparse.eval] using hc.symm

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

theorem zero1592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1592 node1592Labels = 0 := by
  exact mixedMoment_alpha B hF node1592 node1592Labels 1 permutation434
    (by decide +kernel)

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

theorem sound1592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1592 node1592Labels = Sparse.eval nodeValue1592 (mixedVector B) := by
  simpa only [nodeValue1592, Sparse.eval_nil] using zero1592 B _hB _hF

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

theorem sound1602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1602 node1602Labels = Sparse.eval nodeValue1602 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1602) = mixedMoment B node1602 node1602Labels := rfl
  simpa [nodeValue1602, Sparse.eval] using hc.symm

theorem sound1608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1608 node1608Labels = Sparse.eval nodeValue1608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1608) = mixedMoment B node1608 node1608Labels := rfl
  simpa [nodeValue1608, Sparse.eval] using hc.symm

theorem sound1627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1627 node1627Labels = Sparse.eval nodeValue1627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1627) = mixedMoment B node1627 node1627Labels := rfl
  simpa [nodeValue1627, Sparse.eval] using hc.symm

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

theorem sound1710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1710 node1710Labels = Sparse.eval nodeValue1710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1710) = mixedMoment B node1710 node1710Labels := rfl
  simpa [nodeValue1710, Sparse.eval] using hc.symm

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

theorem sound1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1741 node1741Labels = Sparse.eval nodeValue1741 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1741) = mixedMoment B node1741 node1741Labels := rfl
  simpa [nodeValue1741, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1914 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1914 node1914Labels = 0 := by
  exact mixedMoment_order_one B hB node1914 node1914Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1897 node1897Labels = Sparse.eval nodeValue1897 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1897) = mixedMoment B node1897 node1897Labels := rfl
  simpa [nodeValue1897, Sparse.eval] using hc.symm

theorem sound1914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1914 node1914Labels = Sparse.eval nodeValue1914 (mixedVector B) := by
  simpa only [nodeValue1914, Sparse.eval_nil] using zero1914 B _hB _hF

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

theorem zero1950 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1950 node1950Labels = 0 := by
  exact mixedMoment_order_one B hB node1950 node1950Labels 1
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

theorem sound1924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1924 node1924Labels = Sparse.eval nodeValue1924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1924) = mixedMoment B node1924 node1924Labels := rfl
  simpa [nodeValue1924, Sparse.eval] using hc.symm

theorem sound1926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1926 node1926Labels = Sparse.eval nodeValue1926 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1926) = mixedMoment B node1926 node1926Labels := rfl
  simpa [nodeValue1926, Sparse.eval] using hc.symm

theorem sound1950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1950 node1950Labels = Sparse.eval nodeValue1950 (mixedVector B) := by
  simpa only [nodeValue1950, Sparse.eval_nil] using zero1950 B _hB _hF

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

theorem sound1991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1991 node1991Labels = Sparse.eval nodeValue1991 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1991) = mixedMoment B node1991 node1991Labels := rfl
  simpa [nodeValue1991, Sparse.eval] using hc.symm

theorem sound1992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1992 node1992Labels = Sparse.eval nodeValue1992 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1992) = mixedMoment B node1992 node1992Labels := rfl
  simpa [nodeValue1992, Sparse.eval] using hc.symm

theorem sound2032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2032 node2032Labels = Sparse.eval nodeValue2032 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2032) = mixedMoment B node2032 node2032Labels := rfl
  simpa [nodeValue2032, Sparse.eval] using hc.symm

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

theorem sound2119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2119 node2119Labels = Sparse.eval nodeValue2119 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2119) = mixedMoment B node2119 node2119Labels := rfl
  simpa [nodeValue2119, Sparse.eval] using hc.symm

theorem sound2121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2121 node2121Labels = Sparse.eval nodeValue2121 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2121) = mixedMoment B node2121 node2121Labels := rfl
  simpa [nodeValue2121, Sparse.eval] using hc.symm

theorem sound2130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2130 node2130Labels = Sparse.eval nodeValue2130 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2130) = mixedMoment B node2130 node2130Labels := rfl
  simpa [nodeValue2130, Sparse.eval] using hc.symm

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

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

theorem sound2197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2197 node2197Labels = Sparse.eval nodeValue2197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2197) = mixedMoment B node2197 node2197Labels := rfl
  simpa [nodeValue2197, Sparse.eval] using hc.symm

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

theorem sound2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2218 node2218Labels = Sparse.eval nodeValue2218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2218) = mixedMoment B node2218 node2218Labels := rfl
  simpa [nodeValue2218, Sparse.eval] using hc.symm

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

theorem zero2377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2377 node2377Labels = 0 := by
  exact mixedMoment_alpha B hF node2377 node2377Labels 1 permutation200
    (by decide +kernel)

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

theorem sound2377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2377 node2377Labels = Sparse.eval nodeValue2377 (mixedVector B) := by
  simpa only [nodeValue2377, Sparse.eval_nil] using zero2377 B _hB _hF

theorem sound2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2385 node2385Labels = Sparse.eval nodeValue2385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2385) = mixedMoment B node2385 node2385Labels := rfl
  simpa [nodeValue2385, Sparse.eval] using hc.symm

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

theorem sound2664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2664 node2664Labels = Sparse.eval nodeValue2664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2664) = mixedMoment B node2664 node2664Labels := rfl
  simpa [nodeValue2664, Sparse.eval] using hc.symm

theorem sound2683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2683 node2683Labels = Sparse.eval nodeValue2683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2683) = mixedMoment B node2683 node2683Labels := rfl
  simpa [nodeValue2683, Sparse.eval] using hc.symm

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

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

theorem sound2702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2702 node2702Labels = Sparse.eval nodeValue2702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2702) = mixedMoment B node2702 node2702Labels := rfl
  simpa [nodeValue2702, Sparse.eval] using hc.symm

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

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources40
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1311 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1311 + difference 0 0) (sourceB1311 + difference 0 0) sourceC1311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1311 + difference 0 0) (sourceB1311 + difference 0 0) sourceC1311) = raw21013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1311 sourceB1311 sourceC1311 difference raw21013; decide +kernel
    rw [ha]
    exact (canonical21013 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1311 + difference 0 1) (sourceB1311 + difference 1 0) sourceC1311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA1311 + difference 0 1) (sourceB1311 + difference 1 0) sourceC1311) = raw21014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1311 sourceB1311 sourceC1311 difference raw21014; decide +kernel
    rw [ha]
    exact (canonical21014 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1311 + difference 0 2) (sourceB1311 + difference 2 0) sourceC1311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA1311 + difference 0 2) (sourceB1311 + difference 2 0) sourceC1311) = raw21015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1311 sourceB1311 sourceC1311 difference raw21015; decide +kernel
    rw [ha]
    exact (canonical21015 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1311 + difference 0 3) (sourceB1311 + difference 3 0) sourceC1311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1950) := by
    have ha : (tripleCharges (sourceA1311 + difference 0 3) (sourceB1311 + difference 3 0) sourceC1311) = raw21016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1311 sourceB1311 sourceC1311 difference raw21016; decide +kernel
    rw [ha]
    exact (canonical21016 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1311 + difference 0 4) (sourceB1311 + difference 4 0) sourceC1311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1311 + difference 0 4) (sourceB1311 + difference 4 0) sourceC1311) = raw21017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1311 sourceB1311 sourceC1311 difference raw21017; decide +kernel
    rw [ha]
    exact (canonical21017 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1311 + difference 0 5) (sourceB1311 + difference 5 0) sourceC1311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA1311 + difference 0 5) (sourceB1311 + difference 5 0) sourceC1311) = raw21018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1311 sourceB1311 sourceC1311 difference raw21018; decide +kernel
    rw [ha]
    exact (canonical21018 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1311 + sourceB1311) sourceC1311) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1311 + sourceB1311) sourceC1311) = raw21019 := by
      apply Matrix.ext; unfold doubleCharges sourceA1311 sourceB1311 sourceC1311 raw21019; decide +kernel
    rw [ha]
    exact (canonical21019 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1311 sourceB1311 sourceC1311
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1311, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources41
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1312 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1312 + difference 0 3) (sourceB1312 + difference 3 0) sourceC1312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1950) := by
    have ha : (tripleCharges (sourceA1312 + difference 0 3) (sourceB1312 + difference 3 0) sourceC1312) = raw21016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1312 sourceB1312 sourceC1312 difference raw21016; decide +kernel
    rw [ha]
    exact (canonical21016 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1312 + difference 1 3) (sourceB1312 + difference 3 1) sourceC1312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1098) := by
    have ha : (tripleCharges (sourceA1312 + difference 1 3) (sourceB1312 + difference 3 1) sourceC1312) = raw21020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1312 sourceB1312 sourceC1312 difference raw21020; decide +kernel
    rw [ha]
    exact (canonical21020 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1312 + difference 2 3) (sourceB1312 + difference 3 2) sourceC1312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1098) := by
    have ha : (tripleCharges (sourceA1312 + difference 2 3) (sourceB1312 + difference 3 2) sourceC1312) = raw21021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1312 sourceB1312 sourceC1312 difference raw21021; decide +kernel
    rw [ha]
    exact (canonical21021 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1312 + difference 3 3) (sourceB1312 + difference 3 3) sourceC1312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1312 + difference 3 3) (sourceB1312 + difference 3 3) sourceC1312) = raw21013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1312 sourceB1312 sourceC1312 difference raw21013; decide +kernel
    rw [ha]
    exact (canonical21013 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1312 + difference 4 3) (sourceB1312 + difference 3 4) sourceC1312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1103) := by
    have ha : (tripleCharges (sourceA1312 + difference 4 3) (sourceB1312 + difference 3 4) sourceC1312) = raw21022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1312 sourceB1312 sourceC1312 difference raw21022; decide +kernel
    rw [ha]
    exact (canonical21022 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1312 + difference 5 3) (sourceB1312 + difference 3 5) sourceC1312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 893) := by
    have ha : (tripleCharges (sourceA1312 + difference 5 3) (sourceB1312 + difference 3 5) sourceC1312) = raw21023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1312 sourceB1312 sourceC1312 difference raw21023; decide +kernel
    rw [ha]
    exact (canonical21023 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1312 + sourceB1312) sourceC1312) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1312 + sourceB1312) sourceC1312) = raw21019 := by
      apply Matrix.ext; unfold doubleCharges sourceA1312 sourceB1312 sourceC1312 raw21019; decide +kernel
    rw [ha]
    exact (canonical21019 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1312 sourceB1312 sourceC1312
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1312, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1313 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1313 + difference 0 5) (sourceB1313 + difference 5 0) sourceC1313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA1313 + difference 0 5) (sourceB1313 + difference 5 0) sourceC1313) = raw21018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1313 sourceB1313 sourceC1313 difference raw21018; decide +kernel
    rw [ha]
    exact (canonical21018 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1313 + difference 1 5) (sourceB1313 + difference 5 1) sourceC1313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1184) := by
    have ha : (tripleCharges (sourceA1313 + difference 1 5) (sourceB1313 + difference 5 1) sourceC1313) = raw21024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1313 sourceB1313 sourceC1313 difference raw21024; decide +kernel
    rw [ha]
    exact (canonical21024 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1313 + difference 2 5) (sourceB1313 + difference 5 2) sourceC1313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1184) := by
    have ha : (tripleCharges (sourceA1313 + difference 2 5) (sourceB1313 + difference 5 2) sourceC1313) = raw21025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1313 sourceB1313 sourceC1313 difference raw21025; decide +kernel
    rw [ha]
    exact (canonical21025 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1313 + difference 3 5) (sourceB1313 + difference 5 3) sourceC1313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1287) := by
    have ha : (tripleCharges (sourceA1313 + difference 3 5) (sourceB1313 + difference 5 3) sourceC1313) = raw21026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1313 sourceB1313 sourceC1313 difference raw21026; decide +kernel
    rw [ha]
    exact (canonical21026 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1313 + difference 4 5) (sourceB1313 + difference 5 4) sourceC1313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1192) := by
    have ha : (tripleCharges (sourceA1313 + difference 4 5) (sourceB1313 + difference 5 4) sourceC1313) = raw21027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1313 sourceB1313 sourceC1313 difference raw21027; decide +kernel
    rw [ha]
    exact (canonical21027 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1313 + difference 5 5) (sourceB1313 + difference 5 5) sourceC1313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1313 + difference 5 5) (sourceB1313 + difference 5 5) sourceC1313) = raw21013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1313 sourceB1313 sourceC1313 difference raw21013; decide +kernel
    rw [ha]
    exact (canonical21013 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1313 + sourceB1313) sourceC1313) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1313 + sourceB1313) sourceC1313) = raw21019 := by
      apply Matrix.ext; unfold doubleCharges sourceA1313 sourceB1313 sourceC1313 raw21019; decide +kernel
    rw [ha]
    exact (canonical21019 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1313 sourceB1313 sourceC1313
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1313, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1315 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1315 + difference 0 0) (sourceB1315 + difference 0 0) sourceC1315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1186) := by
    have ha : (tripleCharges (sourceA1315 + difference 0 0) (sourceB1315 + difference 0 0) sourceC1315) = raw21033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1315 sourceB1315 sourceC1315 difference raw21033; decide +kernel
    rw [ha]
    exact (canonical21033 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1315 + difference 0 1) (sourceB1315 + difference 1 0) sourceC1315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1608) := by
    have ha : (tripleCharges (sourceA1315 + difference 0 1) (sourceB1315 + difference 1 0) sourceC1315) = raw21034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1315 sourceB1315 sourceC1315 difference raw21034; decide +kernel
    rw [ha]
    exact (canonical21034 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1315 + difference 0 2) (sourceB1315 + difference 2 0) sourceC1315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1608) := by
    have ha : (tripleCharges (sourceA1315 + difference 0 2) (sourceB1315 + difference 2 0) sourceC1315) = raw21035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1315 sourceB1315 sourceC1315 difference raw21035; decide +kernel
    rw [ha]
    exact (canonical21035 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1315 + difference 0 3) (sourceB1315 + difference 3 0) sourceC1315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1627) := by
    have ha : (tripleCharges (sourceA1315 + difference 0 3) (sourceB1315 + difference 3 0) sourceC1315) = raw21036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1315 sourceB1315 sourceC1315 difference raw21036; decide +kernel
    rw [ha]
    exact (canonical21036 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1315 + difference 0 4) (sourceB1315 + difference 4 0) sourceC1315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1315 + difference 0 4) (sourceB1315 + difference 4 0) sourceC1315) = raw21037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1315 sourceB1315 sourceC1315 difference raw21037; decide +kernel
    rw [ha]
    exact (canonical21037 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1315 + difference 0 5) (sourceB1315 + difference 5 0) sourceC1315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1315 + difference 0 5) (sourceB1315 + difference 5 0) sourceC1315) = raw21038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1315 sourceB1315 sourceC1315 difference raw21038; decide +kernel
    rw [ha]
    exact (canonical21038 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1315 + sourceB1315) sourceC1315) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1315 + sourceB1315) sourceC1315) = raw21039 := by
      apply Matrix.ext; unfold doubleCharges sourceA1315 sourceB1315 sourceC1315 raw21039; decide +kernel
    rw [ha]
    exact (canonical21039 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1315 sourceB1315 sourceC1315
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1315, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1316 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1316 + difference 0 0) (sourceB1316 + difference 0 0) sourceC1316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1203) := by
    have ha : (tripleCharges (sourceA1316 + difference 0 0) (sourceB1316 + difference 0 0) sourceC1316) = raw21040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1316 sourceB1316 sourceC1316 difference raw21040; decide +kernel
    rw [ha]
    exact (canonical21040 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1316 + difference 0 1) (sourceB1316 + difference 1 0) sourceC1316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2377) := by
    have ha : (tripleCharges (sourceA1316 + difference 0 1) (sourceB1316 + difference 1 0) sourceC1316) = raw21041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1316 sourceB1316 sourceC1316 difference raw21041; decide +kernel
    rw [ha]
    exact (canonical21041 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1316 + difference 0 2) (sourceB1316 + difference 2 0) sourceC1316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA1316 + difference 0 2) (sourceB1316 + difference 2 0) sourceC1316) = raw21042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1316 sourceB1316 sourceC1316 difference raw21042; decide +kernel
    rw [ha]
    exact (canonical21042 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1316 + difference 0 3) (sourceB1316 + difference 3 0) sourceC1316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA1316 + difference 0 3) (sourceB1316 + difference 3 0) sourceC1316) = raw21043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1316 sourceB1316 sourceC1316 difference raw21043; decide +kernel
    rw [ha]
    exact (canonical21043 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1316 + difference 0 4) (sourceB1316 + difference 4 0) sourceC1316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA1316 + difference 0 4) (sourceB1316 + difference 4 0) sourceC1316) = raw21044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1316 sourceB1316 sourceC1316 difference raw21044; decide +kernel
    rw [ha]
    exact (canonical21044 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1316 + difference 0 5) (sourceB1316 + difference 5 0) sourceC1316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA1316 + difference 0 5) (sourceB1316 + difference 5 0) sourceC1316) = raw21045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1316 sourceB1316 sourceC1316 difference raw21045; decide +kernel
    rw [ha]
    exact (canonical21045 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1316 + sourceB1316) sourceC1316) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1316 + sourceB1316) sourceC1316) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA1316 sourceB1316 sourceC1316 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1316 sourceB1316 sourceC1316
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1316, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1317 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1317 + difference 0 5) (sourceB1317 + difference 5 0) sourceC1317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA1317 + difference 0 5) (sourceB1317 + difference 5 0) sourceC1317) = raw21045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1317 sourceB1317 sourceC1317 difference raw21045; decide +kernel
    rw [ha]
    exact (canonical21045 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1317 + difference 1 5) (sourceB1317 + difference 5 1) sourceC1317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1198) := by
    have ha : (tripleCharges (sourceA1317 + difference 1 5) (sourceB1317 + difference 5 1) sourceC1317) = raw21047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1317 sourceB1317 sourceC1317 difference raw21047; decide +kernel
    rw [ha]
    exact (canonical21047 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1317 + difference 2 5) (sourceB1317 + difference 5 2) sourceC1317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1230) := by
    have ha : (tripleCharges (sourceA1317 + difference 2 5) (sourceB1317 + difference 5 2) sourceC1317) = raw21048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1317 sourceB1317 sourceC1317 difference raw21048; decide +kernel
    rw [ha]
    exact (canonical21048 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1317 + difference 3 5) (sourceB1317 + difference 5 3) sourceC1317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1230) := by
    have ha : (tripleCharges (sourceA1317 + difference 3 5) (sourceB1317 + difference 5 3) sourceC1317) = raw21049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1317 sourceB1317 sourceC1317 difference raw21049; decide +kernel
    rw [ha]
    exact (canonical21049 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1317 + difference 4 5) (sourceB1317 + difference 5 4) sourceC1317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1205) := by
    have ha : (tripleCharges (sourceA1317 + difference 4 5) (sourceB1317 + difference 5 4) sourceC1317) = raw21050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1317 sourceB1317 sourceC1317 difference raw21050; decide +kernel
    rw [ha]
    exact (canonical21050 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1317 + difference 5 5) (sourceB1317 + difference 5 5) sourceC1317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1203) := by
    have ha : (tripleCharges (sourceA1317 + difference 5 5) (sourceB1317 + difference 5 5) sourceC1317) = raw21040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1317 sourceB1317 sourceC1317 difference raw21040; decide +kernel
    rw [ha]
    exact (canonical21040 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1317 + sourceB1317) sourceC1317) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1317 + sourceB1317) sourceC1317) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA1317 sourceB1317 sourceC1317 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1317 sourceB1317 sourceC1317
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1317, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1318 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1318 + difference 0 0) (sourceB1318 + difference 0 0) sourceC1318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1318 + difference 0 0) (sourceB1318 + difference 0 0) sourceC1318) = raw21051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1318 sourceB1318 sourceC1318 difference raw21051; decide +kernel
    rw [ha]
    exact (canonical21051 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1318 + difference 0 1) (sourceB1318 + difference 1 0) sourceC1318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1897) := by
    have ha : (tripleCharges (sourceA1318 + difference 0 1) (sourceB1318 + difference 1 0) sourceC1318) = raw21052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1318 sourceB1318 sourceC1318 difference raw21052; decide +kernel
    rw [ha]
    exact (canonical21052 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1318 + difference 0 2) (sourceB1318 + difference 2 0) sourceC1318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA1318 + difference 0 2) (sourceB1318 + difference 2 0) sourceC1318) = raw21053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1318 sourceB1318 sourceC1318 difference raw21053; decide +kernel
    rw [ha]
    exact (canonical21053 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1318 + difference 0 3) (sourceB1318 + difference 3 0) sourceC1318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA1318 + difference 0 3) (sourceB1318 + difference 3 0) sourceC1318) = raw21054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1318 sourceB1318 sourceC1318 difference raw21054; decide +kernel
    rw [ha]
    exact (canonical21054 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1318 + difference 0 4) (sourceB1318 + difference 4 0) sourceC1318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1318 + difference 0 4) (sourceB1318 + difference 4 0) sourceC1318) = raw21055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1318 sourceB1318 sourceC1318 difference raw21055; decide +kernel
    rw [ha]
    exact (canonical21055 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1318 + difference 0 5) (sourceB1318 + difference 5 0) sourceC1318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA1318 + difference 0 5) (sourceB1318 + difference 5 0) sourceC1318) = raw21056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1318 sourceB1318 sourceC1318 difference raw21056; decide +kernel
    rw [ha]
    exact (canonical21056 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1318 + sourceB1318) sourceC1318) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1318 + sourceB1318) sourceC1318) = raw21057 := by
      apply Matrix.ext; unfold doubleCharges sourceA1318 sourceB1318 sourceC1318 raw21057; decide +kernel
    rw [ha]
    exact (canonical21057 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1318 sourceB1318 sourceC1318
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1318, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1319 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1319 + difference 0 2) (sourceB1319 + difference 2 0) sourceC1319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA1319 + difference 0 2) (sourceB1319 + difference 2 0) sourceC1319) = raw21053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1319 sourceB1319 sourceC1319 difference raw21053; decide +kernel
    rw [ha]
    exact (canonical21053 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1319 + difference 1 2) (sourceB1319 + difference 2 1) sourceC1319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1105) := by
    have ha : (tripleCharges (sourceA1319 + difference 1 2) (sourceB1319 + difference 2 1) sourceC1319) = raw21058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1319 sourceB1319 sourceC1319 difference raw21058; decide +kernel
    rw [ha]
    exact (canonical21058 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1319 + difference 2 2) (sourceB1319 + difference 2 2) sourceC1319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1319 + difference 2 2) (sourceB1319 + difference 2 2) sourceC1319) = raw21051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1319 sourceB1319 sourceC1319 difference raw21051; decide +kernel
    rw [ha]
    exact (canonical21051 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1319 + difference 3 2) (sourceB1319 + difference 2 3) sourceC1319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA1319 + difference 3 2) (sourceB1319 + difference 2 3) sourceC1319) = raw21059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1319 sourceB1319 sourceC1319 difference raw21059; decide +kernel
    rw [ha]
    exact (canonical21059 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1319 + difference 4 2) (sourceB1319 + difference 2 4) sourceC1319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1109) := by
    have ha : (tripleCharges (sourceA1319 + difference 4 2) (sourceB1319 + difference 2 4) sourceC1319) = raw21060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1319 sourceB1319 sourceC1319 difference raw21060; decide +kernel
    rw [ha]
    exact (canonical21060 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1319 + difference 5 2) (sourceB1319 + difference 2 5) sourceC1319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1319 + difference 5 2) (sourceB1319 + difference 2 5) sourceC1319) = raw21061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1319 sourceB1319 sourceC1319 difference raw21061; decide +kernel
    rw [ha]
    exact (canonical21061 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1319 + sourceB1319) sourceC1319) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1319 + sourceB1319) sourceC1319) = raw21057 := by
      apply Matrix.ext; unfold doubleCharges sourceA1319 sourceB1319 sourceC1319 raw21057; decide +kernel
    rw [ha]
    exact (canonical21057 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1319 sourceB1319 sourceC1319
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1319, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1320 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1320 + difference 0 5) (sourceB1320 + difference 5 0) sourceC1320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA1320 + difference 0 5) (sourceB1320 + difference 5 0) sourceC1320) = raw21056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1320 sourceB1320 sourceC1320 difference raw21056; decide +kernel
    rw [ha]
    exact (canonical21056 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1320 + difference 1 5) (sourceB1320 + difference 5 1) sourceC1320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1197) := by
    have ha : (tripleCharges (sourceA1320 + difference 1 5) (sourceB1320 + difference 5 1) sourceC1320) = raw21062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1320 sourceB1320 sourceC1320 difference raw21062; decide +kernel
    rw [ha]
    exact (canonical21062 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1320 + difference 2 5) (sourceB1320 + difference 5 2) sourceC1320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1229) := by
    have ha : (tripleCharges (sourceA1320 + difference 2 5) (sourceB1320 + difference 5 2) sourceC1320) = raw21063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1320 sourceB1320 sourceC1320 difference raw21063; decide +kernel
    rw [ha]
    exact (canonical21063 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1320 + difference 3 5) (sourceB1320 + difference 5 3) sourceC1320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1229) := by
    have ha : (tripleCharges (sourceA1320 + difference 3 5) (sourceB1320 + difference 5 3) sourceC1320) = raw21064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1320 sourceB1320 sourceC1320 difference raw21064; decide +kernel
    rw [ha]
    exact (canonical21064 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1320 + difference 4 5) (sourceB1320 + difference 5 4) sourceC1320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1204) := by
    have ha : (tripleCharges (sourceA1320 + difference 4 5) (sourceB1320 + difference 5 4) sourceC1320) = raw21065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1320 sourceB1320 sourceC1320 difference raw21065; decide +kernel
    rw [ha]
    exact (canonical21065 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1320 + difference 5 5) (sourceB1320 + difference 5 5) sourceC1320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1320 + difference 5 5) (sourceB1320 + difference 5 5) sourceC1320) = raw21051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1320 sourceB1320 sourceC1320 difference raw21051; decide +kernel
    rw [ha]
    exact (canonical21051 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1320 + sourceB1320) sourceC1320) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1320 + sourceB1320) sourceC1320) = raw21057 := by
      apply Matrix.ext; unfold doubleCharges sourceA1320 sourceB1320 sourceC1320 raw21057; decide +kernel
    rw [ha]
    exact (canonical21057 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1320 sourceB1320 sourceC1320
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1320, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1322 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1322 + difference 0 0) (sourceB1322 + difference 0 0) sourceC1322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1199) := by
    have ha : (tripleCharges (sourceA1322 + difference 0 0) (sourceB1322 + difference 0 0) sourceC1322) = raw21071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1322 sourceB1322 sourceC1322 difference raw21071; decide +kernel
    rw [ha]
    exact (canonical21071 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1322 + difference 0 1) (sourceB1322 + difference 1 0) sourceC1322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1592) := by
    have ha : (tripleCharges (sourceA1322 + difference 0 1) (sourceB1322 + difference 1 0) sourceC1322) = raw21072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1322 sourceB1322 sourceC1322 difference raw21072; decide +kernel
    rw [ha]
    exact (canonical21072 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1322 + difference 0 2) (sourceB1322 + difference 2 0) sourceC1322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1322 + difference 0 2) (sourceB1322 + difference 2 0) sourceC1322) = raw21073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1322 sourceB1322 sourceC1322 difference raw21073; decide +kernel
    rw [ha]
    exact (canonical21073 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1322 + difference 0 3) (sourceB1322 + difference 3 0) sourceC1322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1322 + difference 0 3) (sourceB1322 + difference 3 0) sourceC1322) = raw21074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1322 sourceB1322 sourceC1322 difference raw21074; decide +kernel
    rw [ha]
    exact (canonical21074 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1322 + difference 0 4) (sourceB1322 + difference 4 0) sourceC1322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1322 + difference 0 4) (sourceB1322 + difference 4 0) sourceC1322) = raw21075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1322 sourceB1322 sourceC1322 difference raw21075; decide +kernel
    rw [ha]
    exact (canonical21075 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1322 + difference 0 5) (sourceB1322 + difference 5 0) sourceC1322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1322 + difference 0 5) (sourceB1322 + difference 5 0) sourceC1322) = raw21076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1322 sourceB1322 sourceC1322 difference raw21076; decide +kernel
    rw [ha]
    exact (canonical21076 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1322 + sourceB1322) sourceC1322) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1322 + sourceB1322) sourceC1322) = raw21077 := by
      apply Matrix.ext; unfold doubleCharges sourceA1322 sourceB1322 sourceC1322 raw21077; decide +kernel
    rw [ha]
    exact (canonical21077 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1322 sourceB1322 sourceC1322
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1322, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1323 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1323 + difference 0 0) (sourceB1323 + difference 0 0) sourceC1323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1055) := by
    have ha : (tripleCharges (sourceA1323 + difference 0 0) (sourceB1323 + difference 0 0) sourceC1323) = raw21078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1323 sourceB1323 sourceC1323 difference raw21078; decide +kernel
    rw [ha]
    exact (canonical21078 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1323 + difference 0 1) (sourceB1323 + difference 1 0) sourceC1323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2130) := by
    have ha : (tripleCharges (sourceA1323 + difference 0 1) (sourceB1323 + difference 1 0) sourceC1323) = raw21079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1323 sourceB1323 sourceC1323 difference raw21079; decide +kernel
    rw [ha]
    exact (canonical21079 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1323 + difference 0 2) (sourceB1323 + difference 2 0) sourceC1323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2032) := by
    have ha : (tripleCharges (sourceA1323 + difference 0 2) (sourceB1323 + difference 2 0) sourceC1323) = raw21080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1323 sourceB1323 sourceC1323 difference raw21080; decide +kernel
    rw [ha]
    exact (canonical21080 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1323 + difference 0 3) (sourceB1323 + difference 3 0) sourceC1323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2032) := by
    have ha : (tripleCharges (sourceA1323 + difference 0 3) (sourceB1323 + difference 3 0) sourceC1323) = raw21081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1323 sourceB1323 sourceC1323 difference raw21081; decide +kernel
    rw [ha]
    exact (canonical21081 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1323 + difference 0 4) (sourceB1323 + difference 4 0) sourceC1323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1323 + difference 0 4) (sourceB1323 + difference 4 0) sourceC1323) = raw21082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1323 sourceB1323 sourceC1323 difference raw21082; decide +kernel
    rw [ha]
    exact (canonical21082 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1323 + difference 0 5) (sourceB1323 + difference 5 0) sourceC1323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA1323 + difference 0 5) (sourceB1323 + difference 5 0) sourceC1323) = raw21083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1323 sourceB1323 sourceC1323 difference raw21083; decide +kernel
    rw [ha]
    exact (canonical21083 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1323 + sourceB1323) sourceC1323) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1323 + sourceB1323) sourceC1323) = raw21084 := by
      apply Matrix.ext; unfold doubleCharges sourceA1323 sourceB1323 sourceC1323 raw21084; decide +kernel
    rw [ha]
    exact (canonical21084 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1323 sourceB1323 sourceC1323
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1323, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1324 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1324 + difference 0 5) (sourceB1324 + difference 5 0) sourceC1324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA1324 + difference 0 5) (sourceB1324 + difference 5 0) sourceC1324) = raw21083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1324 sourceB1324 sourceC1324 difference raw21083; decide +kernel
    rw [ha]
    exact (canonical21083 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1324 + difference 1 5) (sourceB1324 + difference 5 1) sourceC1324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1324 + difference 1 5) (sourceB1324 + difference 5 1) sourceC1324) = raw21085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1324 sourceB1324 sourceC1324 difference raw21085; decide +kernel
    rw [ha]
    exact (canonical21085 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1324 + difference 2 5) (sourceB1324 + difference 5 2) sourceC1324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1053) := by
    have ha : (tripleCharges (sourceA1324 + difference 2 5) (sourceB1324 + difference 5 2) sourceC1324) = raw21086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1324 sourceB1324 sourceC1324 difference raw21086; decide +kernel
    rw [ha]
    exact (canonical21086 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1324 + difference 3 5) (sourceB1324 + difference 5 3) sourceC1324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1053) := by
    have ha : (tripleCharges (sourceA1324 + difference 3 5) (sourceB1324 + difference 5 3) sourceC1324) = raw21087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1324 sourceB1324 sourceC1324 difference raw21087; decide +kernel
    rw [ha]
    exact (canonical21087 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1324 + difference 4 5) (sourceB1324 + difference 5 4) sourceC1324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1062) := by
    have ha : (tripleCharges (sourceA1324 + difference 4 5) (sourceB1324 + difference 5 4) sourceC1324) = raw21088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1324 sourceB1324 sourceC1324 difference raw21088; decide +kernel
    rw [ha]
    exact (canonical21088 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1324 + difference 5 5) (sourceB1324 + difference 5 5) sourceC1324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1055) := by
    have ha : (tripleCharges (sourceA1324 + difference 5 5) (sourceB1324 + difference 5 5) sourceC1324) = raw21078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1324 sourceB1324 sourceC1324 difference raw21078; decide +kernel
    rw [ha]
    exact (canonical21078 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1324 + sourceB1324) sourceC1324) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1324 + sourceB1324) sourceC1324) = raw21084 := by
      apply Matrix.ext; unfold doubleCharges sourceA1324 sourceB1324 sourceC1324 raw21084; decide +kernel
    rw [ha]
    exact (canonical21084 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1324 sourceB1324 sourceC1324
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1324, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1325 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1325 + difference 0 0) (sourceB1325 + difference 0 0) sourceC1325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 991) := by
    have ha : (tripleCharges (sourceA1325 + difference 0 0) (sourceB1325 + difference 0 0) sourceC1325) = raw21089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1325 sourceB1325 sourceC1325 difference raw21089; decide +kernel
    rw [ha]
    exact (canonical21089 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1325 + difference 0 1) (sourceB1325 + difference 1 0) sourceC1325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2121) := by
    have ha : (tripleCharges (sourceA1325 + difference 0 1) (sourceB1325 + difference 1 0) sourceC1325) = raw21090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1325 sourceB1325 sourceC1325 difference raw21090; decide +kernel
    rw [ha]
    exact (canonical21090 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1325 + difference 0 2) (sourceB1325 + difference 2 0) sourceC1325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1992) := by
    have ha : (tripleCharges (sourceA1325 + difference 0 2) (sourceB1325 + difference 2 0) sourceC1325) = raw21091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1325 sourceB1325 sourceC1325 difference raw21091; decide +kernel
    rw [ha]
    exact (canonical21091 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1325 + difference 0 3) (sourceB1325 + difference 3 0) sourceC1325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA1325 + difference 0 3) (sourceB1325 + difference 3 0) sourceC1325) = raw21092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1325 sourceB1325 sourceC1325 difference raw21092; decide +kernel
    rw [ha]
    exact (canonical21092 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1325 + difference 0 4) (sourceB1325 + difference 4 0) sourceC1325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA1325 + difference 0 4) (sourceB1325 + difference 4 0) sourceC1325) = raw21093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1325 sourceB1325 sourceC1325 difference raw21093; decide +kernel
    rw [ha]
    exact (canonical21093 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1325 + difference 0 5) (sourceB1325 + difference 5 0) sourceC1325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1325 + difference 0 5) (sourceB1325 + difference 5 0) sourceC1325) = raw21094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1325 sourceB1325 sourceC1325 difference raw21094; decide +kernel
    rw [ha]
    exact (canonical21094 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1325 + sourceB1325) sourceC1325) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1325 + sourceB1325) sourceC1325) = raw21095 := by
      apply Matrix.ext; unfold doubleCharges sourceA1325 sourceB1325 sourceC1325 raw21095; decide +kernel
    rw [ha]
    exact (canonical21095 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1325 sourceB1325 sourceC1325
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1325, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1326 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1326 + difference 0 5) (sourceB1326 + difference 5 0) sourceC1326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1326 + difference 0 5) (sourceB1326 + difference 5 0) sourceC1326) = raw21094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1326 sourceB1326 sourceC1326 difference raw21094; decide +kernel
    rw [ha]
    exact (canonical21094 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1326 + difference 1 5) (sourceB1326 + difference 5 1) sourceC1326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1326 + difference 1 5) (sourceB1326 + difference 5 1) sourceC1326) = raw21096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1326 sourceB1326 sourceC1326 difference raw21096; decide +kernel
    rw [ha]
    exact (canonical21096 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1326 + difference 2 5) (sourceB1326 + difference 5 2) sourceC1326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA1326 + difference 2 5) (sourceB1326 + difference 5 2) sourceC1326) = raw21097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1326 sourceB1326 sourceC1326 difference raw21097; decide +kernel
    rw [ha]
    exact (canonical21097 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1326 + difference 3 5) (sourceB1326 + difference 5 3) sourceC1326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1054) := by
    have ha : (tripleCharges (sourceA1326 + difference 3 5) (sourceB1326 + difference 5 3) sourceC1326) = raw21098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1326 sourceB1326 sourceC1326 difference raw21098; decide +kernel
    rw [ha]
    exact (canonical21098 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1326 + difference 4 5) (sourceB1326 + difference 5 4) sourceC1326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 993) := by
    have ha : (tripleCharges (sourceA1326 + difference 4 5) (sourceB1326 + difference 5 4) sourceC1326) = raw21099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1326 sourceB1326 sourceC1326 difference raw21099; decide +kernel
    rw [ha]
    exact (canonical21099 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1326 + difference 5 5) (sourceB1326 + difference 5 5) sourceC1326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 991) := by
    have ha : (tripleCharges (sourceA1326 + difference 5 5) (sourceB1326 + difference 5 5) sourceC1326) = raw21089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1326 sourceB1326 sourceC1326 difference raw21089; decide +kernel
    rw [ha]
    exact (canonical21089 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1326 + sourceB1326) sourceC1326) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1326 + sourceB1326) sourceC1326) = raw21095 := by
      apply Matrix.ext; unfold doubleCharges sourceA1326 sourceB1326 sourceC1326 raw21095; decide +kernel
    rw [ha]
    exact (canonical21095 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1326 sourceB1326 sourceC1326
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1326, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1327 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1327 + difference 0 0) (sourceB1327 + difference 0 0) sourceC1327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 989) := by
    have ha : (tripleCharges (sourceA1327 + difference 0 0) (sourceB1327 + difference 0 0) sourceC1327) = raw21100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1327 sourceB1327 sourceC1327 difference raw21100; decide +kernel
    rw [ha]
    exact (canonical21100 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1327 + difference 0 1) (sourceB1327 + difference 1 0) sourceC1327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2119) := by
    have ha : (tripleCharges (sourceA1327 + difference 0 1) (sourceB1327 + difference 1 0) sourceC1327) = raw21101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1327 sourceB1327 sourceC1327 difference raw21101; decide +kernel
    rw [ha]
    exact (canonical21101 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1327 + difference 0 2) (sourceB1327 + difference 2 0) sourceC1327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1991) := by
    have ha : (tripleCharges (sourceA1327 + difference 0 2) (sourceB1327 + difference 2 0) sourceC1327) = raw21102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1327 sourceB1327 sourceC1327 difference raw21102; decide +kernel
    rw [ha]
    exact (canonical21102 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1327 + difference 0 3) (sourceB1327 + difference 3 0) sourceC1327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA1327 + difference 0 3) (sourceB1327 + difference 3 0) sourceC1327) = raw21103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1327 sourceB1327 sourceC1327 difference raw21103; decide +kernel
    rw [ha]
    exact (canonical21103 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1327 + difference 0 4) (sourceB1327 + difference 4 0) sourceC1327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1327 + difference 0 4) (sourceB1327 + difference 4 0) sourceC1327) = raw21104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1327 sourceB1327 sourceC1327 difference raw21104; decide +kernel
    rw [ha]
    exact (canonical21104 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1327 + difference 0 5) (sourceB1327 + difference 5 0) sourceC1327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1327 + difference 0 5) (sourceB1327 + difference 5 0) sourceC1327) = raw21105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1327 sourceB1327 sourceC1327 difference raw21105; decide +kernel
    rw [ha]
    exact (canonical21105 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1327 + sourceB1327) sourceC1327) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1327 + sourceB1327) sourceC1327) = raw21106 := by
      apply Matrix.ext; unfold doubleCharges sourceA1327 sourceB1327 sourceC1327 raw21106; decide +kernel
    rw [ha]
    exact (canonical21106 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1327 sourceB1327 sourceC1327
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1327, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1328 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1328 + difference 0 5) (sourceB1328 + difference 5 0) sourceC1328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1328 + difference 0 5) (sourceB1328 + difference 5 0) sourceC1328) = raw21105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1328 sourceB1328 sourceC1328 difference raw21105; decide +kernel
    rw [ha]
    exact (canonical21105 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1328 + difference 1 5) (sourceB1328 + difference 5 1) sourceC1328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1328 + difference 1 5) (sourceB1328 + difference 5 1) sourceC1328) = raw21107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1328 sourceB1328 sourceC1328 difference raw21107; decide +kernel
    rw [ha]
    exact (canonical21107 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1328 + difference 2 5) (sourceB1328 + difference 5 2) sourceC1328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 987) := by
    have ha : (tripleCharges (sourceA1328 + difference 2 5) (sourceB1328 + difference 5 2) sourceC1328) = raw21108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1328 sourceB1328 sourceC1328 difference raw21108; decide +kernel
    rw [ha]
    exact (canonical21108 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1328 + difference 3 5) (sourceB1328 + difference 5 3) sourceC1328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1053) := by
    have ha : (tripleCharges (sourceA1328 + difference 3 5) (sourceB1328 + difference 5 3) sourceC1328) = raw21109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1328 sourceB1328 sourceC1328 difference raw21109; decide +kernel
    rw [ha]
    exact (canonical21109 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1328 + difference 4 5) (sourceB1328 + difference 5 4) sourceC1328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 992) := by
    have ha : (tripleCharges (sourceA1328 + difference 4 5) (sourceB1328 + difference 5 4) sourceC1328) = raw21110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1328 sourceB1328 sourceC1328 difference raw21110; decide +kernel
    rw [ha]
    exact (canonical21110 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1328 + difference 5 5) (sourceB1328 + difference 5 5) sourceC1328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 989) := by
    have ha : (tripleCharges (sourceA1328 + difference 5 5) (sourceB1328 + difference 5 5) sourceC1328) = raw21100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1328 sourceB1328 sourceC1328 difference raw21100; decide +kernel
    rw [ha]
    exact (canonical21100 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1328 + sourceB1328) sourceC1328) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1328 + sourceB1328) sourceC1328) = raw21106 := by
      apply Matrix.ext; unfold doubleCharges sourceA1328 sourceB1328 sourceC1328 raw21106; decide +kernel
    rw [ha]
    exact (canonical21106 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1328 sourceB1328 sourceC1328
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1328, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1136 : Integer.Sparse.reindex keyMap MixedData.row1136 = numericRow1136 := by decide +kernel

theorem numericCheck1136 (x : Master → ℝ) : Integer.Sparse.eval numericRow1136 x =
    (1 : ℝ) * reducedSource1136 x := by
  norm_num [numericRow1136, reducedSource1136, Integer.Sparse.eval, Sparse.eval, nodeValue1190, nodeValue1924, nodeValue1950, nodeValue2218, nodeValue2685, nodeValue4082]

theorem reindexCheck1137 : Integer.Sparse.reindex keyMap MixedData.row1137 = numericRow1137 := by decide +kernel

theorem numericCheck1137 (x : Master → ℝ) : Integer.Sparse.eval numericRow1137 x =
    (1 : ℝ) * reducedSource1137 x := by
  norm_num [numericRow1137, reducedSource1137, Integer.Sparse.eval, Sparse.eval, nodeValue893, nodeValue1098, nodeValue1103, nodeValue1190, nodeValue1950, nodeValue4082]

theorem reindexCheck1138 : Integer.Sparse.reindex keyMap MixedData.row1138 = numericRow1138 := by decide +kernel

theorem numericCheck1138 (x : Master → ℝ) : Integer.Sparse.eval numericRow1138 x =
    (1 : ℝ) * reducedSource1138 x := by
  norm_num [numericRow1138, reducedSource1138, Integer.Sparse.eval, Sparse.eval, nodeValue1184, nodeValue1190, nodeValue1192, nodeValue1287, nodeValue2685, nodeValue4082]

theorem reindexCheck1139 : Integer.Sparse.reindex keyMap MixedData.row1139 = numericRow1139 := by decide +kernel

theorem numericCheck1139 (x : Master → ℝ) : Integer.Sparse.eval numericRow1139 x =
    (1 : ℝ) * reducedSource1139 x := by
  norm_num [numericRow1139, reducedSource1139, Integer.Sparse.eval, Sparse.eval, nodeValue1186, nodeValue1608, nodeValue1627, nodeValue1741, nodeValue2683, nodeValue4071]

theorem reindexCheck1140 : Integer.Sparse.reindex keyMap MixedData.row1140 = numericRow1140 := by decide +kernel

theorem numericCheck1140 (x : Master → ℝ) : Integer.Sparse.eval numericRow1140 x =
    (1 : ℝ) * reducedSource1140 x := by
  norm_num [numericRow1140, reducedSource1140, Integer.Sparse.eval, Sparse.eval, nodeValue1203, nodeValue2377, nodeValue2385, nodeValue2664, nodeValue2705, nodeValue4088]

theorem reindexCheck1141 : Integer.Sparse.reindex keyMap MixedData.row1141 = numericRow1141 := by decide +kernel

theorem numericCheck1141 (x : Master → ℝ) : Integer.Sparse.eval numericRow1141 x =
    (1 : ℝ) * reducedSource1141 x := by
  norm_num [numericRow1141, reducedSource1141, Integer.Sparse.eval, Sparse.eval, nodeValue1198, nodeValue1203, nodeValue1205, nodeValue1230, nodeValue2705, nodeValue4088]

theorem reindexCheck1142 : Integer.Sparse.reindex keyMap MixedData.row1142 = numericRow1142 := by decide +kernel

theorem numericCheck1142 (x : Master → ℝ) : Integer.Sparse.eval numericRow1142 x =
    (1 : ℝ) * reducedSource1142 x := by
  norm_num [numericRow1142, reducedSource1142, Integer.Sparse.eval, Sparse.eval, nodeValue1202, nodeValue1897, nodeValue1914, nodeValue2193, nodeValue2704, nodeValue4080]

theorem reindexCheck1143 : Integer.Sparse.reindex keyMap MixedData.row1143 = numericRow1143 := by decide +kernel

theorem numericCheck1143 (x : Master → ℝ) : Integer.Sparse.eval numericRow1143 x =
    (1 : ℝ) * reducedSource1143 x := by
  norm_num [numericRow1143, reducedSource1143, Integer.Sparse.eval, Sparse.eval, nodeValue871, nodeValue1105, nodeValue1109, nodeValue1123, nodeValue1202, nodeValue1914, nodeValue4080]

theorem reindexCheck1144 : Integer.Sparse.reindex keyMap MixedData.row1144 = numericRow1144 := by decide +kernel

theorem numericCheck1144 (x : Master → ℝ) : Integer.Sparse.eval numericRow1144 x =
    (1 : ℝ) * reducedSource1144 x := by
  norm_num [numericRow1144, reducedSource1144, Integer.Sparse.eval, Sparse.eval, nodeValue1197, nodeValue1202, nodeValue1204, nodeValue1229, nodeValue2704, nodeValue4080]

theorem reindexCheck1145 : Integer.Sparse.reindex keyMap MixedData.row1145 = numericRow1145 := by decide +kernel

theorem numericCheck1145 (x : Master → ℝ) : Integer.Sparse.eval numericRow1145 x =
    (1 : ℝ) * reducedSource1145 x := by
  norm_num [numericRow1145, reducedSource1145, Integer.Sparse.eval, Sparse.eval, nodeValue1199, nodeValue1592, nodeValue1602, nodeValue1710, nodeValue2702, nodeValue4069]

theorem reindexCheck1146 : Integer.Sparse.reindex keyMap MixedData.row1146 = numericRow1146 := by decide +kernel

theorem numericCheck1146 (x : Master → ℝ) : Integer.Sparse.eval numericRow1146 x =
    (1 : ℝ) * reducedSource1146 x := by
  norm_num [numericRow1146, reducedSource1146, Integer.Sparse.eval, Sparse.eval, nodeValue1055, nodeValue2032, nodeValue2130, nodeValue2218, nodeValue2276, nodeValue4082]

theorem reindexCheck1147 : Integer.Sparse.reindex keyMap MixedData.row1147 = numericRow1147 := by decide +kernel

theorem numericCheck1147 (x : Master → ℝ) : Integer.Sparse.eval numericRow1147 x =
    (1 : ℝ) * reducedSource1147 x := by
  norm_num [numericRow1147, reducedSource1147, Integer.Sparse.eval, Sparse.eval, nodeValue1053, nodeValue1055, nodeValue1062, nodeValue1075, nodeValue2276, nodeValue4082]

theorem reindexCheck1148 : Integer.Sparse.reindex keyMap MixedData.row1148 = numericRow1148 := by decide +kernel

theorem numericCheck1148 (x : Master → ℝ) : Integer.Sparse.eval numericRow1148 x =
    (1 : ℝ) * reducedSource1148 x := by
  norm_num [numericRow1148, reducedSource1148, Integer.Sparse.eval, Sparse.eval, nodeValue991, nodeValue1926, nodeValue1992, nodeValue2121, nodeValue2197, nodeValue2216, nodeValue4080]

theorem reindexCheck1149 : Integer.Sparse.reindex keyMap MixedData.row1149 = numericRow1149 := by decide +kernel

theorem numericCheck1149 (x : Master → ℝ) : Integer.Sparse.eval numericRow1149 x =
    (1 : ℝ) * reducedSource1149 x := by
  norm_num [numericRow1149, reducedSource1149, Integer.Sparse.eval, Sparse.eval, nodeValue988, nodeValue991, nodeValue993, nodeValue1005, nodeValue1054, nodeValue2216, nodeValue4080]

theorem reindexCheck1150 : Integer.Sparse.reindex keyMap MixedData.row1150 = numericRow1150 := by decide +kernel

theorem numericCheck1150 (x : Master → ℝ) : Integer.Sparse.eval numericRow1150 x =
    (1 : ℝ) * reducedSource1150 x := by
  norm_num [numericRow1150, reducedSource1150, Integer.Sparse.eval, Sparse.eval, nodeValue989, nodeValue1924, nodeValue1991, nodeValue2119, nodeValue2215, nodeValue2218, nodeValue4082]

theorem reindexCheck1151 : Integer.Sparse.reindex keyMap MixedData.row1151 = numericRow1151 := by decide +kernel

theorem numericCheck1151 (x : Master → ℝ) : Integer.Sparse.eval numericRow1151 x =
    (1 : ℝ) * reducedSource1151 x := by
  norm_num [numericRow1151, reducedSource1151, Integer.Sparse.eval, Sparse.eval, nodeValue987, nodeValue989, nodeValue992, nodeValue1000, nodeValue1053, nodeValue2215, nodeValue4082]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1136 (mixedVector B) = 0 := by
  have h1190 : mixedVector B (Sum.inr 1190) = Sparse.eval nodeValue1190 (mixedVector B) := by
    change mixedMoment B node1190 node1190Labels = _
    exact sound1190 B hB hF
  have h1924 : mixedVector B (Sum.inr 1924) = Sparse.eval nodeValue1924 (mixedVector B) := by
    change mixedMoment B node1924 node1924Labels = _
    exact sound1924 B hB hF
  have h1950 : mixedVector B (Sum.inr 1950) = Sparse.eval nodeValue1950 (mixedVector B) := by
    change mixedMoment B node1950 node1950Labels = _
    exact sound1950 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1311, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1190, h1924, h1950, h2218, h2685, h4082, reducedSource1136] using sourceEq1311 B hB

theorem rowSound1136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1136 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1136, numericCheck1136, reducedZero1136 B hB hF, mul_zero]

theorem reducedZero1137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1137 (mixedVector B) = 0 := by
  have h893 : mixedVector B (Sum.inr 893) = Sparse.eval nodeValue893 (mixedVector B) := by
    change mixedMoment B node893 node893Labels = _
    exact sound893 B hB hF
  have h1098 : mixedVector B (Sum.inr 1098) = Sparse.eval nodeValue1098 (mixedVector B) := by
    change mixedMoment B node1098 node1098Labels = _
    exact sound1098 B hB hF
  have h1103 : mixedVector B (Sum.inr 1103) = Sparse.eval nodeValue1103 (mixedVector B) := by
    change mixedMoment B node1103 node1103Labels = _
    exact sound1103 B hB hF
  have h1190 : mixedVector B (Sum.inr 1190) = Sparse.eval nodeValue1190 (mixedVector B) := by
    change mixedMoment B node1190 node1190Labels = _
    exact sound1190 B hB hF
  have h1950 : mixedVector B (Sum.inr 1950) = Sparse.eval nodeValue1950 (mixedVector B) := by
    change mixedMoment B node1950 node1950Labels = _
    exact sound1950 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1312, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h893, h1098, h1103, h1190, h1950, h4082, reducedSource1137] using sourceEq1312 B hB

theorem rowSound1137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1137 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1137, numericCheck1137, reducedZero1137 B hB hF, mul_zero]

theorem reducedZero1138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1138 (mixedVector B) = 0 := by
  have h1184 : mixedVector B (Sum.inr 1184) = Sparse.eval nodeValue1184 (mixedVector B) := by
    change mixedMoment B node1184 node1184Labels = _
    exact sound1184 B hB hF
  have h1190 : mixedVector B (Sum.inr 1190) = Sparse.eval nodeValue1190 (mixedVector B) := by
    change mixedMoment B node1190 node1190Labels = _
    exact sound1190 B hB hF
  have h1192 : mixedVector B (Sum.inr 1192) = Sparse.eval nodeValue1192 (mixedVector B) := by
    change mixedMoment B node1192 node1192Labels = _
    exact sound1192 B hB hF
  have h1287 : mixedVector B (Sum.inr 1287) = Sparse.eval nodeValue1287 (mixedVector B) := by
    change mixedMoment B node1287 node1287Labels = _
    exact sound1287 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1313, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1184, h1190, h1192, h1287, h2685, h4082, reducedSource1138] using sourceEq1313 B hB

theorem rowSound1138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1138 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1138, numericCheck1138, reducedZero1138 B hB hF, mul_zero]

theorem reducedZero1139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1139 (mixedVector B) = 0 := by
  have h1186 : mixedVector B (Sum.inr 1186) = Sparse.eval nodeValue1186 (mixedVector B) := by
    change mixedMoment B node1186 node1186Labels = _
    exact sound1186 B hB hF
  have h1608 : mixedVector B (Sum.inr 1608) = Sparse.eval nodeValue1608 (mixedVector B) := by
    change mixedMoment B node1608 node1608Labels = _
    exact sound1608 B hB hF
  have h1627 : mixedVector B (Sum.inr 1627) = Sparse.eval nodeValue1627 (mixedVector B) := by
    change mixedMoment B node1627 node1627Labels = _
    exact sound1627 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1315, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1186, h1608, h1627, h1741, h2683, h4071, reducedSource1139] using sourceEq1315 B hB

theorem rowSound1139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1139 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1139, numericCheck1139, reducedZero1139 B hB hF, mul_zero]

theorem reducedZero1140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1140 (mixedVector B) = 0 := by
  have h1203 : mixedVector B (Sum.inr 1203) = Sparse.eval nodeValue1203 (mixedVector B) := by
    change mixedMoment B node1203 node1203Labels = _
    exact sound1203 B hB hF
  have h2377 : mixedVector B (Sum.inr 2377) = Sparse.eval nodeValue2377 (mixedVector B) := by
    change mixedMoment B node2377 node2377Labels = _
    exact sound2377 B hB hF
  have h2385 : mixedVector B (Sum.inr 2385) = Sparse.eval nodeValue2385 (mixedVector B) := by
    change mixedMoment B node2385 node2385Labels = _
    exact sound2385 B hB hF
  have h2664 : mixedVector B (Sum.inr 2664) = Sparse.eval nodeValue2664 (mixedVector B) := by
    change mixedMoment B node2664 node2664Labels = _
    exact sound2664 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1316, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1203, h2377, h2385, h2664, h2705, h4088, reducedSource1140] using sourceEq1316 B hB

theorem rowSound1140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1140 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1140, numericCheck1140, reducedZero1140 B hB hF, mul_zero]

theorem reducedZero1141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1141 (mixedVector B) = 0 := by
  have h1198 : mixedVector B (Sum.inr 1198) = Sparse.eval nodeValue1198 (mixedVector B) := by
    change mixedMoment B node1198 node1198Labels = _
    exact sound1198 B hB hF
  have h1203 : mixedVector B (Sum.inr 1203) = Sparse.eval nodeValue1203 (mixedVector B) := by
    change mixedMoment B node1203 node1203Labels = _
    exact sound1203 B hB hF
  have h1205 : mixedVector B (Sum.inr 1205) = Sparse.eval nodeValue1205 (mixedVector B) := by
    change mixedMoment B node1205 node1205Labels = _
    exact sound1205 B hB hF
  have h1230 : mixedVector B (Sum.inr 1230) = Sparse.eval nodeValue1230 (mixedVector B) := by
    change mixedMoment B node1230 node1230Labels = _
    exact sound1230 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1317, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1198, h1203, h1205, h1230, h2705, h4088, reducedSource1141] using sourceEq1317 B hB

theorem rowSound1141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1141 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1141, numericCheck1141, reducedZero1141 B hB hF, mul_zero]

theorem reducedZero1142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1142 (mixedVector B) = 0 := by
  have h1202 : mixedVector B (Sum.inr 1202) = Sparse.eval nodeValue1202 (mixedVector B) := by
    change mixedMoment B node1202 node1202Labels = _
    exact sound1202 B hB hF
  have h1897 : mixedVector B (Sum.inr 1897) = Sparse.eval nodeValue1897 (mixedVector B) := by
    change mixedMoment B node1897 node1897Labels = _
    exact sound1897 B hB hF
  have h1914 : mixedVector B (Sum.inr 1914) = Sparse.eval nodeValue1914 (mixedVector B) := by
    change mixedMoment B node1914 node1914Labels = _
    exact sound1914 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1318, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1202, h1897, h1914, h2193, h2704, h4080, reducedSource1142] using sourceEq1318 B hB

theorem rowSound1142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1142 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1142, numericCheck1142, reducedZero1142 B hB hF, mul_zero]

theorem reducedZero1143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1143 (mixedVector B) = 0 := by
  have h871 : mixedVector B (Sum.inr 871) = Sparse.eval nodeValue871 (mixedVector B) := by
    change mixedMoment B node871 node871Labels = _
    exact sound871 B hB hF
  have h1105 : mixedVector B (Sum.inr 1105) = Sparse.eval nodeValue1105 (mixedVector B) := by
    change mixedMoment B node1105 node1105Labels = _
    exact sound1105 B hB hF
  have h1109 : mixedVector B (Sum.inr 1109) = Sparse.eval nodeValue1109 (mixedVector B) := by
    change mixedMoment B node1109 node1109Labels = _
    exact sound1109 B hB hF
  have h1123 : mixedVector B (Sum.inr 1123) = Sparse.eval nodeValue1123 (mixedVector B) := by
    change mixedMoment B node1123 node1123Labels = _
    exact sound1123 B hB hF
  have h1202 : mixedVector B (Sum.inr 1202) = Sparse.eval nodeValue1202 (mixedVector B) := by
    change mixedMoment B node1202 node1202Labels = _
    exact sound1202 B hB hF
  have h1914 : mixedVector B (Sum.inr 1914) = Sparse.eval nodeValue1914 (mixedVector B) := by
    change mixedMoment B node1914 node1914Labels = _
    exact sound1914 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1319, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h871, h1105, h1109, h1123, h1202, h1914, h4080, reducedSource1143] using sourceEq1319 B hB

theorem rowSound1143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1143 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1143, numericCheck1143, reducedZero1143 B hB hF, mul_zero]

theorem reducedZero1144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1144 (mixedVector B) = 0 := by
  have h1197 : mixedVector B (Sum.inr 1197) = Sparse.eval nodeValue1197 (mixedVector B) := by
    change mixedMoment B node1197 node1197Labels = _
    exact sound1197 B hB hF
  have h1202 : mixedVector B (Sum.inr 1202) = Sparse.eval nodeValue1202 (mixedVector B) := by
    change mixedMoment B node1202 node1202Labels = _
    exact sound1202 B hB hF
  have h1204 : mixedVector B (Sum.inr 1204) = Sparse.eval nodeValue1204 (mixedVector B) := by
    change mixedMoment B node1204 node1204Labels = _
    exact sound1204 B hB hF
  have h1229 : mixedVector B (Sum.inr 1229) = Sparse.eval nodeValue1229 (mixedVector B) := by
    change mixedMoment B node1229 node1229Labels = _
    exact sound1229 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1320, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1197, h1202, h1204, h1229, h2704, h4080, reducedSource1144] using sourceEq1320 B hB

theorem rowSound1144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1144 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1144, numericCheck1144, reducedZero1144 B hB hF, mul_zero]

theorem reducedZero1145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1145 (mixedVector B) = 0 := by
  have h1199 : mixedVector B (Sum.inr 1199) = Sparse.eval nodeValue1199 (mixedVector B) := by
    change mixedMoment B node1199 node1199Labels = _
    exact sound1199 B hB hF
  have h1592 : mixedVector B (Sum.inr 1592) = Sparse.eval nodeValue1592 (mixedVector B) := by
    change mixedMoment B node1592 node1592Labels = _
    exact sound1592 B hB hF
  have h1602 : mixedVector B (Sum.inr 1602) = Sparse.eval nodeValue1602 (mixedVector B) := by
    change mixedMoment B node1602 node1602Labels = _
    exact sound1602 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1322, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1199, h1592, h1602, h1710, h2702, h4069, reducedSource1145] using sourceEq1322 B hB

theorem rowSound1145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1145 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1145, numericCheck1145, reducedZero1145 B hB hF, mul_zero]

theorem reducedZero1146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1146 (mixedVector B) = 0 := by
  have h1055 : mixedVector B (Sum.inr 1055) = Sparse.eval nodeValue1055 (mixedVector B) := by
    change mixedMoment B node1055 node1055Labels = _
    exact sound1055 B hB hF
  have h2032 : mixedVector B (Sum.inr 2032) = Sparse.eval nodeValue2032 (mixedVector B) := by
    change mixedMoment B node2032 node2032Labels = _
    exact sound2032 B hB hF
  have h2130 : mixedVector B (Sum.inr 2130) = Sparse.eval nodeValue2130 (mixedVector B) := by
    change mixedMoment B node2130 node2130Labels = _
    exact sound2130 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1323, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1055, h2032, h2130, h2218, h2276, h4082, reducedSource1146] using sourceEq1323 B hB

theorem rowSound1146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1146 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1146, numericCheck1146, reducedZero1146 B hB hF, mul_zero]

theorem reducedZero1147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1147 (mixedVector B) = 0 := by
  have h1053 : mixedVector B (Sum.inr 1053) = Sparse.eval nodeValue1053 (mixedVector B) := by
    change mixedMoment B node1053 node1053Labels = _
    exact sound1053 B hB hF
  have h1055 : mixedVector B (Sum.inr 1055) = Sparse.eval nodeValue1055 (mixedVector B) := by
    change mixedMoment B node1055 node1055Labels = _
    exact sound1055 B hB hF
  have h1062 : mixedVector B (Sum.inr 1062) = Sparse.eval nodeValue1062 (mixedVector B) := by
    change mixedMoment B node1062 node1062Labels = _
    exact sound1062 B hB hF
  have h1075 : mixedVector B (Sum.inr 1075) = Sparse.eval nodeValue1075 (mixedVector B) := by
    change mixedMoment B node1075 node1075Labels = _
    exact sound1075 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1324, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1053, h1055, h1062, h1075, h2276, h4082, reducedSource1147] using sourceEq1324 B hB

theorem rowSound1147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1147 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1147, numericCheck1147, reducedZero1147 B hB hF, mul_zero]

theorem reducedZero1148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1148 (mixedVector B) = 0 := by
  have h991 : mixedVector B (Sum.inr 991) = Sparse.eval nodeValue991 (mixedVector B) := by
    change mixedMoment B node991 node991Labels = _
    exact sound991 B hB hF
  have h1926 : mixedVector B (Sum.inr 1926) = Sparse.eval nodeValue1926 (mixedVector B) := by
    change mixedMoment B node1926 node1926Labels = _
    exact sound1926 B hB hF
  have h1992 : mixedVector B (Sum.inr 1992) = Sparse.eval nodeValue1992 (mixedVector B) := by
    change mixedMoment B node1992 node1992Labels = _
    exact sound1992 B hB hF
  have h2121 : mixedVector B (Sum.inr 2121) = Sparse.eval nodeValue2121 (mixedVector B) := by
    change mixedMoment B node2121 node2121Labels = _
    exact sound2121 B hB hF
  have h2197 : mixedVector B (Sum.inr 2197) = Sparse.eval nodeValue2197 (mixedVector B) := by
    change mixedMoment B node2197 node2197Labels = _
    exact sound2197 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1325, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h991, h1926, h1992, h2121, h2197, h2216, h4080, reducedSource1148] using sourceEq1325 B hB

theorem rowSound1148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1148 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1148, numericCheck1148, reducedZero1148 B hB hF, mul_zero]

theorem reducedZero1149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1149 (mixedVector B) = 0 := by
  have h988 : mixedVector B (Sum.inr 988) = Sparse.eval nodeValue988 (mixedVector B) := by
    change mixedMoment B node988 node988Labels = _
    exact sound988 B hB hF
  have h991 : mixedVector B (Sum.inr 991) = Sparse.eval nodeValue991 (mixedVector B) := by
    change mixedMoment B node991 node991Labels = _
    exact sound991 B hB hF
  have h993 : mixedVector B (Sum.inr 993) = Sparse.eval nodeValue993 (mixedVector B) := by
    change mixedMoment B node993 node993Labels = _
    exact sound993 B hB hF
  have h1005 : mixedVector B (Sum.inr 1005) = Sparse.eval nodeValue1005 (mixedVector B) := by
    change mixedMoment B node1005 node1005Labels = _
    exact sound1005 B hB hF
  have h1054 : mixedVector B (Sum.inr 1054) = Sparse.eval nodeValue1054 (mixedVector B) := by
    change mixedMoment B node1054 node1054Labels = _
    exact sound1054 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1326, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h988, h991, h993, h1005, h1054, h2216, h4080, reducedSource1149] using sourceEq1326 B hB

theorem rowSound1149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1149 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1149, numericCheck1149, reducedZero1149 B hB hF, mul_zero]

theorem reducedZero1150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1150 (mixedVector B) = 0 := by
  have h989 : mixedVector B (Sum.inr 989) = Sparse.eval nodeValue989 (mixedVector B) := by
    change mixedMoment B node989 node989Labels = _
    exact sound989 B hB hF
  have h1924 : mixedVector B (Sum.inr 1924) = Sparse.eval nodeValue1924 (mixedVector B) := by
    change mixedMoment B node1924 node1924Labels = _
    exact sound1924 B hB hF
  have h1991 : mixedVector B (Sum.inr 1991) = Sparse.eval nodeValue1991 (mixedVector B) := by
    change mixedMoment B node1991 node1991Labels = _
    exact sound1991 B hB hF
  have h2119 : mixedVector B (Sum.inr 2119) = Sparse.eval nodeValue2119 (mixedVector B) := by
    change mixedMoment B node2119 node2119Labels = _
    exact sound2119 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1327, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h989, h1924, h1991, h2119, h2215, h2218, h4082, reducedSource1150] using sourceEq1327 B hB

theorem rowSound1150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1150 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1150, numericCheck1150, reducedZero1150 B hB hF, mul_zero]

theorem reducedZero1151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1151 (mixedVector B) = 0 := by
  have h987 : mixedVector B (Sum.inr 987) = Sparse.eval nodeValue987 (mixedVector B) := by
    change mixedMoment B node987 node987Labels = _
    exact sound987 B hB hF
  have h989 : mixedVector B (Sum.inr 989) = Sparse.eval nodeValue989 (mixedVector B) := by
    change mixedMoment B node989 node989Labels = _
    exact sound989 B hB hF
  have h992 : mixedVector B (Sum.inr 992) = Sparse.eval nodeValue992 (mixedVector B) := by
    change mixedMoment B node992 node992Labels = _
    exact sound992 B hB hF
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1053 : mixedVector B (Sum.inr 1053) = Sparse.eval nodeValue1053 (mixedVector B) := by
    change mixedMoment B node1053 node1053Labels = _
    exact sound1053 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1328, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h987, h989, h992, h1000, h1053, h2215, h4082, reducedSource1151] using sourceEq1328 B hB

theorem rowSound1151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1151 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1151, numericCheck1151, reducedZero1151 B hB hF, mul_zero]

theorem sourceRowsAt1136 : MixedData.sourceRows (1136 : Fin 2425) =
    MixedData.row1136 := by decide +kernel

theorem sourceRowsAt1137 : MixedData.sourceRows (1137 : Fin 2425) =
    MixedData.row1137 := by decide +kernel

theorem sourceRowsAt1138 : MixedData.sourceRows (1138 : Fin 2425) =
    MixedData.row1138 := by decide +kernel

theorem sourceRowsAt1139 : MixedData.sourceRows (1139 : Fin 2425) =
    MixedData.row1139 := by decide +kernel

theorem sourceRowsAt1140 : MixedData.sourceRows (1140 : Fin 2425) =
    MixedData.row1140 := by decide +kernel

theorem sourceRowsAt1141 : MixedData.sourceRows (1141 : Fin 2425) =
    MixedData.row1141 := by decide +kernel

theorem sourceRowsAt1142 : MixedData.sourceRows (1142 : Fin 2425) =
    MixedData.row1142 := by decide +kernel

theorem sourceRowsAt1143 : MixedData.sourceRows (1143 : Fin 2425) =
    MixedData.row1143 := by decide +kernel

theorem sourceRowsAt1144 : MixedData.sourceRows (1144 : Fin 2425) =
    MixedData.row1144 := by decide +kernel

theorem sourceRowsAt1145 : MixedData.sourceRows (1145 : Fin 2425) =
    MixedData.row1145 := by decide +kernel

theorem sourceRowsAt1146 : MixedData.sourceRows (1146 : Fin 2425) =
    MixedData.row1146 := by decide +kernel

theorem sourceRowsAt1147 : MixedData.sourceRows (1147 : Fin 2425) =
    MixedData.row1147 := by decide +kernel

theorem sourceRowsAt1148 : MixedData.sourceRows (1148 : Fin 2425) =
    MixedData.row1148 := by decide +kernel

theorem sourceRowsAt1149 : MixedData.sourceRows (1149 : Fin 2425) =
    MixedData.row1149 := by decide +kernel

theorem sourceRowsAt1150 : MixedData.sourceRows (1150 : Fin 2425) =
    MixedData.row1150 := by decide +kernel

theorem sourceRowsAt1151 : MixedData.sourceRows (1151 : Fin 2425) =
    MixedData.row1151 := by decide +kernel

theorem chunkSound71_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 71) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1136 ∨ k.val = 1137 ∨ k.val = 1138 ∨ k.val = 1139 ∨ k.val = 1140 ∨ k.val = 1141 ∨ k.val = 1142 ∨ k.val = 1143 ∨ k.val = 1144 ∨ k.val = 1145 ∨ k.val = 1146 ∨ k.val = 1147 ∨ k.val = 1148 ∨ k.val = 1149 ∨ k.val = 1150 ∨ k.val = 1151 := by omega
  rcases heq with h1136 | h1137 | h1138 | h1139 | h1140 | h1141 | h1142 | h1143 | h1144 | h1145 | h1146 | h1147 | h1148 | h1149 | h1150 | h1151
  · have he : k = (1136 : Fin 2425) := Fin.ext h1136
    subst k
    rw [sourceRowsAt1136]
    exact rowSound1136 B hB hF
  · have he : k = (1137 : Fin 2425) := Fin.ext h1137
    subst k
    rw [sourceRowsAt1137]
    exact rowSound1137 B hB hF
  · have he : k = (1138 : Fin 2425) := Fin.ext h1138
    subst k
    rw [sourceRowsAt1138]
    exact rowSound1138 B hB hF
  · have he : k = (1139 : Fin 2425) := Fin.ext h1139
    subst k
    rw [sourceRowsAt1139]
    exact rowSound1139 B hB hF
  · have he : k = (1140 : Fin 2425) := Fin.ext h1140
    subst k
    rw [sourceRowsAt1140]
    exact rowSound1140 B hB hF
  · have he : k = (1141 : Fin 2425) := Fin.ext h1141
    subst k
    rw [sourceRowsAt1141]
    exact rowSound1141 B hB hF
  · have he : k = (1142 : Fin 2425) := Fin.ext h1142
    subst k
    rw [sourceRowsAt1142]
    exact rowSound1142 B hB hF
  · have he : k = (1143 : Fin 2425) := Fin.ext h1143
    subst k
    rw [sourceRowsAt1143]
    exact rowSound1143 B hB hF
  · have he : k = (1144 : Fin 2425) := Fin.ext h1144
    subst k
    rw [sourceRowsAt1144]
    exact rowSound1144 B hB hF
  · have he : k = (1145 : Fin 2425) := Fin.ext h1145
    subst k
    rw [sourceRowsAt1145]
    exact rowSound1145 B hB hF
  · have he : k = (1146 : Fin 2425) := Fin.ext h1146
    subst k
    rw [sourceRowsAt1146]
    exact rowSound1146 B hB hF
  · have he : k = (1147 : Fin 2425) := Fin.ext h1147
    subst k
    rw [sourceRowsAt1147]
    exact rowSound1147 B hB hF
  · have he : k = (1148 : Fin 2425) := Fin.ext h1148
    subst k
    rw [sourceRowsAt1148]
    exact rowSound1148 B hB hF
  · have he : k = (1149 : Fin 2425) := Fin.ext h1149
    subst k
    rw [sourceRowsAt1149]
    exact rowSound1149 B hB hF
  · have he : k = (1150 : Fin 2425) := Fin.ext h1150
    subst k
    rw [sourceRowsAt1150]
    exact rowSound1150 B hB hF
  · have he : k = (1151 : Fin 2425) := Fin.ext h1151
    subst k
    rw [sourceRowsAt1151]
    exact rowSound1151 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound71_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound71_e_oai
