-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:35:02.006105+00:00
-- url     : https://prove2.me/submissions/380d867c-4d48-45d5-b4c8-f6f684b153e9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1702_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1703_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1708_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1709_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1710_e

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

theorem transition_cross_normSq {m : ℕ} (B : Fin m → Basis) (hB : IsMUBFamily B)
    (ref : Basis) (s t : Fin m) (hst : s ≠ t) (k l : Coord) :
    Complex.normSq (∑ i, conj (transition ref (B s) i k) * transition ref (B t) i l) = 6 := by
  rw [transition_column_inner, map_mul, hB s t hst k l]
  norm_num [Complex.normSq_ofNat]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_OffDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem offDiagSum_add_diag {V : Type*} [AddCommMonoid V] (f : Coord → Coord → V) :
    offDiagSum f + (∑ i, f i i) = ∑ i, ∑ j, f i j := by
  rw [offDiagSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

theorem offDiagSum_sum {V ι : Type*} [AddCommMonoid V] [Fintype ι]
    (f : Coord → Coord → ι → V) :
    offDiagSum (fun i j => ∑ k, f i j k) =
      ∑ k, offDiagSum (fun i j => f i j k) := by
  unfold offDiagSum
  calc
    _ = ∑ i, ∑ k, ∑ j ∈ Finset.univ.erase i, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem offDiagSum_mul (c : ℂ) (f : Coord → Coord → ℂ) :
    offDiagSum (fun i j => c * f i j) = c * offDiagSum f := by
  simp only [offDiagSum, Finset.mul_sum]

theorem sum_mul_conj (z : Coord → ℂ) :
    (∑ i, ∑ j, z i * conj (z j)) = (Complex.normSq (∑ i, z i) : ℂ) := by
  rw [← Complex.mul_conj, map_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_DifferentMatrices
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem difference_reverse (i j : Coord) : difference j i = -difference i j := by
  simp [difference, neg_sub]

theorem cross_character_gram (x y : Coord → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) (hy : ∀ i, Complex.normSq (y i) = 1) :
    (∑ i, ∑ j, character x (difference i j) * character y (-difference i j)) =
      (Complex.normSq (∑ i, x i * conj (y i)) : ℂ) := by
  rw [← sum_mul_conj]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [character_neg y hy, character_difference x hx, character_difference y hy]
  simp only [map_mul, starRingEnd_apply, star_star]
  ring

theorem cross_character_offdiag (x y : Coord → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) (hy : ∀ i, Complex.normSq (y i) = 1)
    (hc : Complex.normSq (∑ i, x i * conj (y i)) = 6) :
    offDiagSum (fun i j => character x (difference i j) * character y (-difference i j)) = 0 := by
  have h := offDiagSum_add_diag
    (fun i j => character x (difference i j) * character y (-difference i j))
  rw [cross_character_gram x y hx hy, hc] at h
  have hd : (∑ i, character x (difference i i) * character y (-difference i i)) = (6 : ℂ) := by
    simp [difference]
  rw [hd] at h
  exact add_right_cancel (show _ + (6 : ℂ) = 0 + 6 by simpa using h)

theorem weighted_cross_character (x y : Coord → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) (hy : ∀ i, Complex.normSq (y i) = 1)
    (hc : Complex.normSq (∑ i, x i * conj (y i)) = 6) (a b : Charge) :
    offDiagSum (fun i j =>
      character x (a + difference i j) * character y (b + difference j i)) = 0 := by
  have he (i j : Coord) :
      character x (a + difference i j) * character y (b + difference j i) =
        (character x a * character y b) *
          (character x (difference i j) * character y (-difference i j)) := by
    rw [character_add x (fun i => unit_ne_zero (hx i)),
      character_add y (fun i => unit_ne_zero (hy i)), difference_reverse j i]
    ring_nf
  simp_rw [he]
  rw [offDiagSum_mul, cross_character_offdiag x y hx hy hc, mul_zero]

theorem g_product_expand (H K : CMatrix) (a b : Charge) :
    g H a * g K b = (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
      ∑ k, ∑ l, character (fun i => H i k) a * character (fun i => K i l) b := by
  unfold g
  calc
    _ = (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
      ((∑ k, character (fun i => H i k) a) * ∑ l, character (fun i => K i l) b) := by ring
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- The different-matrix Fourier identity from unbiasedness of every pair of
columns. The off-diagonal indexing lists each difference `e_i-e_j` once. -/
theorem different_matrices_identity {H K : CMatrix} (hH : IsHadamard H) (hK : IsHadamard K)
    (hc : ∀ k l, Complex.normSq (∑ i, H i k * conj (K i l)) = 6) (a b : Charge) :
    offDiagSum (fun i j => g H (a + difference i j) * g K (b + difference j i)) = 0 := by
  simp_rw [g_product_expand]
  rw [offDiagSum_mul, offDiagSum_sum]
  simp_rw [offDiagSum_sum]
  have hz : (∑ k, ∑ l, offDiagSum (fun i j =>
      character (fun r => H r k) (a + difference i j) *
        character (fun r => K r l) (b + difference j i))) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    exact weighted_cross_character _ _ (fun i => hH.1 i k) (fun i => hK.1 i l) (hc k l) a b
  rw [hz, mul_zero]

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

theorem relativeMatrix_cross (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s t : Coord) (hst : s ≠ t) (k l : Coord) :
    Complex.normSq (∑ i, relativeMatrix B r s i k * conj (relativeMatrix B r t i l)) = 6 := by
  have ht : r.succAbove t ≠ r.succAbove s := by
    intro h
    exact hst (Fin.succAbove_right_injective h.symm)
  simpa only [relativeMatrix, mul_comm] using
    transition_cross_normSq B hB (B r) (r.succAbove t) (r.succAbove s) ht l k

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

theorem average_add (f g : ι → ℝ) :
    average (fun i => f i + g i) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

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

theorem mixedMoment_label_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin l)) :
    mixedMoment B A (σ ∘ label) = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  have h (τ : Fin l ↪ Coord) : mixedIntegrand B A (σ ∘ label) r ρ τ =
      mixedIntegrand B A label r ρ (Equiv.embeddingCongr σ.symm (Equiv.refl Coord) τ) := by
    rfl
  simp_rw [h]
  exact average_equiv (Equiv.embeddingCongr σ.symm (Equiv.refl Coord))
    (fun τ : Fin l ↪ Coord => (mixedIntegrand B A label r ρ τ).re)

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

theorem mixedMoment_unused_first_label {p n l : ℕ} (hl : l < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) :
    mixedMoment B A (Fin.succ ∘ label) = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  change average (fun τ : Fin (l + 1) ↪ Coord =>
    (mixedIntegrand B A label r ρ (Sampling.dropFirst τ)).re) = _
  exact Sampling.average_dropFirst hl
    (fun τ : Fin l ↪ Coord => (mixedIntegrand B A label r ρ τ).re)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedLabelEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

/-- Injective renaming, including adding unused labels, preserves the moment. -/
theorem mixedMoment_label_embedding {p n l k : ℕ} (hk : k ≤ 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (e : Fin l ↪ Fin k) (label : Fin n → Fin l) :
    mixedMoment B A (e ∘ label) = mixedMoment B A label := by
  have hcard : l ≤ k := by
    simpa using Fintype.card_le_of_injective e e.injective
  induction k generalizing l with
  | zero =>
      have hl : l = 0 := Nat.eq_zero_of_le_zero hcard
      subst l
      have he : e ∘ label = label := funext fun j => Fin.elim0 (label j)
      rw [he]
  | succ k ih =>
      by_cases hl : l = k + 1
      · subst l
        let σ : Equiv.Perm (Fin (k + 1)) := Equiv.ofBijective e
          ⟨e.injective, Finite.surjective_of_injective e.injective⟩
        exact mixedMoment_label_permutation B A label σ
      · have hlk : l ≤ k := by omega
        let f : Fin l ↪ Fin k := Fin.castLEEmb hlk
        obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
          (fun i => (f i).succ) e (fun _ _ h => f.injective (Fin.succ_inj.mp h)) e.injective
        have he : e ∘ label = σ ∘ (Fin.succ ∘ (f ∘ label)) := by
          funext j
          exact (hσ (label j)).symm
        rw [he, mixedMoment_label_permutation,
          mixedMoment_unused_first_label (show k < 6 by omega)]
        exact ih (by omega) f label hlk

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

theorem sampledMatrix_cross (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (ρ : Coord ↪ Coord) (s t : Coord) (hst : s ≠ t) (k l : Coord) :
    Complex.normSq (∑ i, sampledMatrix B r ρ s i k * conj (sampledMatrix B r ρ t i l)) = 6 := by
  let e : Equiv.Perm Coord := Equiv.ofBijective ρ
    ⟨ρ.injective, Finite.surjective_of_injective ρ.injective⟩
  change Complex.normSq (∑ i, relativeMatrix B r s (e i) k * conj (relativeMatrix B r t (e i) l)) = 6
  rw [Equiv.sum_comp e (fun i => relativeMatrix B r s i k * conj (relativeMatrix B r t i l))]
  exact relativeMatrix_cross B hB r s t hst k l

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

theorem average_finset_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : ι → κ → ℝ) :
    average (fun i => ∑ k ∈ s, f i k) = ∑ k ∈ s, average (fun i => f i k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih => simp only [Finset.sum_insert hk, average_add, ih]

theorem average_offDiagSum {ι : Type*} [Fintype ι] (f : ι → Coord → Coord → ℝ) :
    average (fun k => offDiagSum (f k)) = offDiagSum (fun i j => average (fun k => f k i j)) := by
  simp only [offDiagSum, average_sum, average_finset_sum]

theorem mixedMoment_different {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s t u : Fin l) (hst : s ≠ t) :
    offDiagSum (fun i j =>
      mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, t, u]) = 0 := by
  simp only [mixedMoment, ← average_offDiagSum]
  have hz (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
      offDiagSum (fun i j =>
        (mixedIntegrand B (tripleCharges (a + difference i j) (b + difference j i) c)
          ![s, t, u] r ρ τ).re) = 0 := by
    simp only [mixedIntegrand_three, offDiagSum, ← Complex.re_sum, ← Finset.sum_mul]
    change (offDiagSum (fun i j =>
      g (sampledMatrix B r ρ (τ s)) (a + difference i j) *
        g (sampledMatrix B r ρ (τ t)) (b + difference j i)) *
          g (sampledMatrix B r ρ (τ u)) c).re = 0
    rw [different_matrices_identity (sampledMatrix_isHadamard B hB r ρ _)
      (sampledMatrix_isHadamard B hB r ρ _)
      (sampledMatrix_cross B hB r ρ _ _ (fun h => hst (τ.injective h))) a b]
    simp
  simp only [hz, average_zero]

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

theorem rename_labels {p n l k : ℕ} (hk : k ≤ 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (small : Fin n → Fin l) (e : Fin l ↪ Fin k) (h : label = e ∘ small) :
    mixedMoment B A label = mixedMoment B A small := by
  rw [h]
  exact mixedMoment_label_embedding hk B A e small

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19681 raw19681Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw19681 raw19681Labels = mixedMoment B raw19681step0 raw19681step0Labels := by
      have hz : ∀ j, raw19681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19681step0 = (fun i j => raw19681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19681step0 raw19681; decide +kernel
      have hl : raw19681step0Labels = raw19681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19681 raw19681Labels permutation434 hz
    mixedMoment B raw19681step0 raw19681step0Labels = mixedMoment B raw19681step1 raw19681step1Labels := by
      have hz : ∀ j, raw19681step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19681step1 = (fun i j => raw19681step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19681step1 raw19681step0; decide +kernel
      have hl : raw19681step1Labels = raw19681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19681step0 raw19681step0Labels permutation80 hz
    mixedMoment B raw19681step1 raw19681step1Labels = mixedMoment B raw19681step2 raw19681step2Labels := by
      have ha : raw19681step2 = (fun i j => raw19681step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19681step2 raw19681step1; decide +kernel
      have hl : raw19681step2Labels = raw19681step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19681step1 raw19681step1Labels permutation29 permutation7
    mixedMoment B raw19681step2 raw19681step2Labels = mixedMoment B raw19681step3 raw19681step3Labels := by
      have ha : raw19681step3 = raw19681step2 := by apply Matrix.ext; unfold raw19681step3 raw19681step2; decide +kernel
      have hl : raw19681step2Labels = labelEmbedding1 ∘ raw19681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19681step2 raw19681step2Labels raw19681step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20345 raw20345Labels = mixedMoment B node2008 node2008Labels := by
  calc
    mixedMoment B raw20345 raw20345Labels = mixedMoment B raw20345step0 raw20345step0Labels := by
      have ha : raw20345step0 = (fun i j => raw20345 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20345step0 raw20345; decide +kernel
      have hl : raw20345step0Labels = raw20345Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20345 raw20345Labels permutation682 permutation2
    mixedMoment B raw20345step0 raw20345step0Labels = mixedMoment B raw20345step1 raw20345step1Labels := by
      have ha : raw20345step1 = -raw20345step0 := by apply Matrix.ext; change ∀ i j, raw20345step1 i j = -(raw20345step0 i j); unfold raw20345step1 raw20345step0; decide +kernel
      have hl : raw20345step1Labels = raw20345step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2008 node2008Labels := by rfl

theorem canonical20350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20350 raw20350Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw20350 raw20350Labels = mixedMoment B raw20350step0 raw20350step0Labels := by
      have hz : ∀ j, raw20350 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20350step0 = (fun i j => raw20350 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20350step0 raw20350; decide +kernel
      have hl : raw20350step0Labels = raw20350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20350 raw20350Labels permutation520 hz
    mixedMoment B raw20350step0 raw20350step0Labels = mixedMoment B raw20350step1 raw20350step1Labels := by
      have ha : raw20350step1 = (fun i j => raw20350step0 (permutation137 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20350step1 raw20350step0; decide +kernel
      have hl : raw20350step1Labels = raw20350step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20350step0 raw20350step0Labels permutation137 permutation0
    mixedMoment B raw20350step1 raw20350step1Labels = mixedMoment B raw20350step2 raw20350step2Labels := by
      have ha : raw20350step2 = -raw20350step1 := by apply Matrix.ext; change ∀ i j, raw20350step2 i j = -(raw20350step1 i j); unfold raw20350step2 raw20350step1; decide +kernel
      have hl : raw20350step2Labels = raw20350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20515 raw20515Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20515 raw20515Labels = mixedMoment B raw20515step0 raw20515step0Labels := by
      have hz : ∀ j, raw20515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20515step0 = (fun i j => raw20515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20515step0 raw20515; decide +kernel
      have hl : raw20515step0Labels = raw20515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20515 raw20515Labels permutation434 hz
    mixedMoment B raw20515step0 raw20515step0Labels = mixedMoment B raw20515step1 raw20515step1Labels := by
      have ha : raw20515step1 = (fun i j => raw20515step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20515step1 raw20515step0; decide +kernel
      have hl : raw20515step1Labels = raw20515step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20515step0 raw20515step0Labels permutation143 permutation7
    mixedMoment B raw20515step1 raw20515step1Labels = mixedMoment B raw20515step2 raw20515step2Labels := by
      have ha : raw20515step2 = raw20515step1 := by apply Matrix.ext; unfold raw20515step2 raw20515step1; decide +kernel
      have hl : raw20515step1Labels = labelEmbedding1 ∘ raw20515step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20515step1 raw20515step1Labels raw20515step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

theorem canonical20518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20518 raw20518Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20518 raw20518Labels = mixedMoment B raw20518step0 raw20518step0Labels := by
      have hz : ∀ j, raw20518 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20518step0 = (fun i j => raw20518 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20518step0 raw20518; decide +kernel
      have hl : raw20518step0Labels = raw20518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20518 raw20518Labels permutation346 hz
    mixedMoment B raw20518step0 raw20518step0Labels = mixedMoment B raw20518step1 raw20518step1Labels := by
      have ha : raw20518step1 = (fun i j => raw20518step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20518step1 raw20518step0; decide +kernel
      have hl : raw20518step1Labels = raw20518step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20518step0 raw20518step0Labels permutation143 permutation7
    mixedMoment B raw20518step1 raw20518step1Labels = mixedMoment B raw20518step2 raw20518step2Labels := by
      have ha : raw20518step2 = raw20518step1 := by apply Matrix.ext; unfold raw20518step2 raw20518step1; decide +kernel
      have hl : raw20518step1Labels = labelEmbedding1 ∘ raw20518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20518step1 raw20518step1Labels raw20518step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

theorem canonical20521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20521 raw20521Labels = mixedMoment B node2258 node2258Labels := by
  calc
    mixedMoment B raw20521 raw20521Labels = mixedMoment B raw20521step0 raw20521step0Labels := by
      have hz : ∀ j, raw20521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20521step0 = (fun i j => raw20521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20521step0 raw20521; decide +kernel
      have hl : raw20521step0Labels = raw20521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20521 raw20521Labels permutation434 hz
    mixedMoment B raw20521step0 raw20521step0Labels = mixedMoment B raw20521step1 raw20521step1Labels := by
      have hz : ∀ j, raw20521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20521step1 = (fun i j => raw20521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20521step1 raw20521step0; decide +kernel
      have hl : raw20521step1Labels = raw20521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20521step0 raw20521step0Labels permutation80 hz
    mixedMoment B raw20521step1 raw20521step1Labels = mixedMoment B raw20521step2 raw20521step2Labels := by
      have ha : raw20521step2 = (fun i j => raw20521step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20521step2 raw20521step1; decide +kernel
      have hl : raw20521step2Labels = raw20521step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20521step1 raw20521step1Labels permutation29 permutation7
    mixedMoment B raw20521step2 raw20521step2Labels = mixedMoment B raw20521step3 raw20521step3Labels := by
      have ha : raw20521step3 = raw20521step2 := by apply Matrix.ext; unfold raw20521step3 raw20521step2; decide +kernel
      have hl : raw20521step2Labels = labelEmbedding1 ∘ raw20521step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20521step2 raw20521step2Labels raw20521step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2258 node2258Labels := by rfl

theorem canonical20531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20531 raw20531Labels = mixedMoment B node1157 node1157Labels := by
  calc
    mixedMoment B raw20531 raw20531Labels = mixedMoment B raw20531step0 raw20531step0Labels := by
      have hz : ∀ j, raw20531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20531step0 = (fun i j => raw20531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20531step0 raw20531; decide +kernel
      have hl : raw20531step0Labels = raw20531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20531 raw20531Labels permutation434 hz
    mixedMoment B raw20531step0 raw20531step0Labels = mixedMoment B raw20531step1 raw20531step1Labels := by
      have ha : raw20531step1 = (fun i j => raw20531step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20531step1 raw20531step0; decide +kernel
      have hl : raw20531step1Labels = raw20531step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20531step0 raw20531step0Labels permutation34 permutation2
    _ = mixedMoment B node1157 node1157Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20703 raw20703Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw20703 raw20703Labels = mixedMoment B raw20703step0 raw20703step0Labels := by
      have hz : ∀ j, raw20703 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20703step0 = (fun i j => raw20703 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20703step0 raw20703; decide +kernel
      have hl : raw20703step0Labels = raw20703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20703 raw20703Labels permutation265 hz
    mixedMoment B raw20703step0 raw20703step0Labels = mixedMoment B raw20703step1 raw20703step1Labels := by
      have ha : raw20703step1 = (fun i j => raw20703step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20703step1 raw20703step0; decide +kernel
      have hl : raw20703step1Labels = raw20703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20703step0 raw20703step0Labels permutation149 permutation7
    mixedMoment B raw20703step1 raw20703step1Labels = mixedMoment B raw20703step2 raw20703step2Labels := by
      have ha : raw20703step2 = raw20703step1 := by apply Matrix.ext; unfold raw20703step2 raw20703step1; decide +kernel
      have hl : raw20703step1Labels = labelEmbedding1 ∘ raw20703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20703step1 raw20703step1Labels raw20703step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical20704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20704 raw20704Labels = mixedMoment B node3484 node3484Labels := by
  calc
    mixedMoment B raw20704 raw20704Labels = mixedMoment B raw20704step0 raw20704step0Labels := by
      have hz : ∀ j, raw20704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20704step0 = (fun i j => raw20704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20704step0 raw20704; decide +kernel
      have hl : raw20704step0Labels = raw20704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20704 raw20704Labels permutation346 hz
    mixedMoment B raw20704step0 raw20704step0Labels = mixedMoment B raw20704step1 raw20704step1Labels := by
      have hz : ∀ j, raw20704step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20704step1 = (fun i j => raw20704step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20704step1 raw20704step0; decide +kernel
      have hl : raw20704step1Labels = raw20704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20704step0 raw20704step0Labels permutation56 hz
    mixedMoment B raw20704step1 raw20704step1Labels = mixedMoment B raw20704step2 raw20704step2Labels := by
      have ha : raw20704step2 = (fun i j => raw20704step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20704step2 raw20704step1; decide +kernel
      have hl : raw20704step2Labels = raw20704step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20704step1 raw20704step1Labels permutation31 permutation7
    mixedMoment B raw20704step2 raw20704step2Labels = mixedMoment B raw20704step3 raw20704step3Labels := by
      have ha : raw20704step3 = raw20704step2 := by apply Matrix.ext; unfold raw20704step3 raw20704step2; decide +kernel
      have hl : raw20704step2Labels = labelEmbedding1 ∘ raw20704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20704step2 raw20704step2Labels raw20704step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3484 node3484Labels := by rfl

theorem canonical20705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20705 raw20705Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw20705 raw20705Labels = mixedMoment B raw20705step0 raw20705step0Labels := by
      have hz : ∀ j, raw20705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20705step0 = (fun i j => raw20705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20705step0 raw20705; decide +kernel
      have hl : raw20705step0Labels = raw20705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20705 raw20705Labels permutation346 hz
    mixedMoment B raw20705step0 raw20705step0Labels = mixedMoment B raw20705step1 raw20705step1Labels := by
      have hz : ∀ j, raw20705step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20705step1 = (fun i j => raw20705step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20705step1 raw20705step0; decide +kernel
      have hl : raw20705step1Labels = raw20705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20705step0 raw20705step0Labels permutation56 hz
    mixedMoment B raw20705step1 raw20705step1Labels = mixedMoment B raw20705step2 raw20705step2Labels := by
      have ha : raw20705step2 = (fun i j => raw20705step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20705step2 raw20705step1; decide +kernel
      have hl : raw20705step2Labels = raw20705step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20705step1 raw20705step1Labels permutation31 permutation7
    mixedMoment B raw20705step2 raw20705step2Labels = mixedMoment B raw20705step3 raw20705step3Labels := by
      have ha : raw20705step3 = raw20705step2 := by apply Matrix.ext; unfold raw20705step3 raw20705step2; decide +kernel
      have hl : raw20705step2Labels = labelEmbedding1 ∘ raw20705step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20705step2 raw20705step2Labels raw20705step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3545 node3545Labels := by rfl

theorem canonical20706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20706 raw20706Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw20706 raw20706Labels = mixedMoment B raw20706step0 raw20706step0Labels := by
      have hz : ∀ j, raw20706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20706step0 = (fun i j => raw20706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20706step0 raw20706; decide +kernel
      have hl : raw20706step0Labels = raw20706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20706 raw20706Labels permutation346 hz
    mixedMoment B raw20706step0 raw20706step0Labels = mixedMoment B raw20706step1 raw20706step1Labels := by
      have hz : ∀ j, raw20706step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20706step1 = (fun i j => raw20706step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20706step1 raw20706step0; decide +kernel
      have hl : raw20706step1Labels = raw20706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20706step0 raw20706step0Labels permutation56 hz
    mixedMoment B raw20706step1 raw20706step1Labels = mixedMoment B raw20706step2 raw20706step2Labels := by
      have ha : raw20706step2 = (fun i j => raw20706step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20706step2 raw20706step1; decide +kernel
      have hl : raw20706step2Labels = raw20706step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20706step1 raw20706step1Labels permutation8 permutation7
    mixedMoment B raw20706step2 raw20706step2Labels = mixedMoment B raw20706step3 raw20706step3Labels := by
      have ha : raw20706step3 = -raw20706step2 := by apply Matrix.ext; change ∀ i j, raw20706step3 i j = -(raw20706step2 i j); unfold raw20706step3 raw20706step2; decide +kernel
      have hl : raw20706step3Labels = raw20706step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20706step3 raw20706step3Labels = mixedMoment B raw20706step4 raw20706step4Labels := by
      have ha : raw20706step4 = raw20706step3 := by apply Matrix.ext; unfold raw20706step4 raw20706step3; decide +kernel
      have hl : raw20706step3Labels = labelEmbedding1 ∘ raw20706step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20706step3 raw20706step3Labels raw20706step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical20713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20713 raw20713Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw20713 raw20713Labels = mixedMoment B raw20713step0 raw20713step0Labels := by
      have ha : raw20713step0 = (fun i j => raw20713 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20713step0 raw20713; decide +kernel
      have hl : raw20713step0Labels = raw20713Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20713 raw20713Labels permutation166 permutation5
    mixedMoment B raw20713step0 raw20713step0Labels = mixedMoment B raw20713step1 raw20713step1Labels := by
      have ha : raw20713step1 = -raw20713step0 := by apply Matrix.ext; change ∀ i j, raw20713step1 i j = -(raw20713step0 i j); unfold raw20713step1 raw20713step0; decide +kernel
      have hl : raw20713step1Labels = raw20713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20713step1 raw20713step1Labels = mixedMoment B raw20713step2 raw20713step2Labels := by
      have ha : raw20713step2 = raw20713step1 := by apply Matrix.ext; unfold raw20713step2 raw20713step1; decide +kernel
      have hl : raw20713step1Labels = labelEmbedding1 ∘ raw20713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20713step1 raw20713step1Labels raw20713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

theorem canonical20718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20718 raw20718Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw20718 raw20718Labels = mixedMoment B raw20718step0 raw20718step0Labels := by
      have hz : ∀ j, raw20718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20718step0 = (fun i j => raw20718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20718step0 raw20718; decide +kernel
      have hl : raw20718step0Labels = raw20718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20718 raw20718Labels permutation346 hz
    mixedMoment B raw20718step0 raw20718step0Labels = mixedMoment B raw20718step1 raw20718step1Labels := by
      have ha : raw20718step1 = (fun i j => raw20718step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20718step1 raw20718step0; decide +kernel
      have hl : raw20718step1Labels = raw20718step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20718step0 raw20718step0Labels permutation35 permutation5
    mixedMoment B raw20718step1 raw20718step1Labels = mixedMoment B raw20718step2 raw20718step2Labels := by
      have ha : raw20718step2 = -raw20718step1 := by apply Matrix.ext; change ∀ i j, raw20718step2 i j = -(raw20718step1 i j); unfold raw20718step2 raw20718step1; decide +kernel
      have hl : raw20718step2Labels = raw20718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20718step2 raw20718step2Labels = mixedMoment B raw20718step3 raw20718step3Labels := by
      have ha : raw20718step3 = raw20718step2 := by apply Matrix.ext; unfold raw20718step3 raw20718step2; decide +kernel
      have hl : raw20718step2Labels = labelEmbedding1 ∘ raw20718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20718step2 raw20718step2Labels raw20718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

theorem canonical20723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20723 raw20723Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw20723 raw20723Labels = mixedMoment B raw20723step0 raw20723step0Labels := by
      have hz : ∀ j, raw20723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20723step0 = (fun i j => raw20723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20723step0 raw20723; decide +kernel
      have hl : raw20723step0Labels = raw20723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20723 raw20723Labels permutation346 hz
    mixedMoment B raw20723step0 raw20723step0Labels = mixedMoment B raw20723step1 raw20723step1Labels := by
      have ha : raw20723step1 = (fun i j => raw20723step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20723step1 raw20723step0; decide +kernel
      have hl : raw20723step1Labels = raw20723step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20723step0 raw20723step0Labels permutation32 permutation5
    mixedMoment B raw20723step1 raw20723step1Labels = mixedMoment B raw20723step2 raw20723step2Labels := by
      have ha : raw20723step2 = -raw20723step1 := by apply Matrix.ext; change ∀ i j, raw20723step2 i j = -(raw20723step1 i j); unfold raw20723step2 raw20723step1; decide +kernel
      have hl : raw20723step2Labels = raw20723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20723step2 raw20723step2Labels = mixedMoment B raw20723step3 raw20723step3Labels := by
      have ha : raw20723step3 = raw20723step2 := by apply Matrix.ext; unfold raw20723step3 raw20723step2; decide +kernel
      have hl : raw20723step2Labels = labelEmbedding1 ∘ raw20723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20723step2 raw20723step2Labels raw20723step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

theorem canonical20728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20728 raw20728Labels = mixedMoment B node3262 node3262Labels := by
  calc
    mixedMoment B raw20728 raw20728Labels = mixedMoment B raw20728step0 raw20728step0Labels := by
      have hz : ∀ j, raw20728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20728step0 = (fun i j => raw20728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20728step0 raw20728; decide +kernel
      have hl : raw20728step0Labels = raw20728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20728 raw20728Labels permutation346 hz
    mixedMoment B raw20728step0 raw20728step0Labels = mixedMoment B raw20728step1 raw20728step1Labels := by
      have ha : raw20728step1 = (fun i j => raw20728step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20728step1 raw20728step0; decide +kernel
      have hl : raw20728step1Labels = raw20728step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20728step0 raw20728step0Labels permutation34 permutation5
    mixedMoment B raw20728step1 raw20728step1Labels = mixedMoment B raw20728step2 raw20728step2Labels := by
      have ha : raw20728step2 = -raw20728step1 := by apply Matrix.ext; change ∀ i j, raw20728step2 i j = -(raw20728step1 i j); unfold raw20728step2 raw20728step1; decide +kernel
      have hl : raw20728step2Labels = raw20728step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20728step2 raw20728step2Labels = mixedMoment B raw20728step3 raw20728step3Labels := by
      have ha : raw20728step3 = raw20728step2 := by apply Matrix.ext; unfold raw20728step3 raw20728step2; decide +kernel
      have hl : raw20728step2Labels = labelEmbedding1 ∘ raw20728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20728step2 raw20728step2Labels raw20728step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3262 node3262Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical222
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28525 raw28525Labels = mixedMoment B node2011 node2011Labels := by
  calc
    mixedMoment B raw28525 raw28525Labels = mixedMoment B raw28525step0 raw28525step0Labels := by
      have ha : raw28525step0 = (fun i j => raw28525 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28525step0 raw28525; decide +kernel
      have hl : raw28525step0Labels = raw28525Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28525 raw28525Labels permutation682 permutation2
    mixedMoment B raw28525step0 raw28525step0Labels = mixedMoment B raw28525step1 raw28525step1Labels := by
      have ha : raw28525step1 = -raw28525step0 := by apply Matrix.ext; change ∀ i j, raw28525step1 i j = -(raw28525step0 i j); unfold raw28525step1 raw28525step0; decide +kernel
      have hl : raw28525step1Labels = raw28525step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2011 node2011Labels := by rfl

theorem canonical28526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28526 raw28526Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw28526 raw28526Labels = mixedMoment B raw28526step0 raw28526step0Labels := by
      have ha : raw28526step0 = (fun i j => raw28526 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28526step0 raw28526; decide +kernel
      have hl : raw28526step0Labels = raw28526Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28526 raw28526Labels permutation686 permutation2
    mixedMoment B raw28526step0 raw28526step0Labels = mixedMoment B raw28526step1 raw28526step1Labels := by
      have ha : raw28526step1 = -raw28526step0 := by apply Matrix.ext; change ∀ i j, raw28526step1 i j = -(raw28526step0 i j); unfold raw28526step1 raw28526step0; decide +kernel
      have hl : raw28526step1Labels = raw28526step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2016 node2016Labels := by rfl

theorem canonical28527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28527 raw28527Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw28527 raw28527Labels = mixedMoment B raw28527step0 raw28527step0Labels := by
      have ha : raw28527step0 = (fun i j => raw28527 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28527step0 raw28527; decide +kernel
      have hl : raw28527step0Labels = raw28527Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28527 raw28527Labels permutation680 permutation2
    mixedMoment B raw28527step0 raw28527step0Labels = mixedMoment B raw28527step1 raw28527step1Labels := by
      have ha : raw28527step1 = -raw28527step0 := by apply Matrix.ext; change ∀ i j, raw28527step1 i j = -(raw28527step0 i j); unfold raw28527step1 raw28527step0; decide +kernel
      have hl : raw28527step1Labels = raw28527step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2016 node2016Labels := by rfl

theorem canonical28528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28528 raw28528Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw28528 raw28528Labels = mixedMoment B raw28528step0 raw28528step0Labels := by
      have hz : ∀ j, raw28528 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28528step0 = (fun i j => raw28528 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28528step0 raw28528; decide +kernel
      have hl : raw28528step0Labels = raw28528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28528 raw28528Labels permutation520 hz
    mixedMoment B raw28528step0 raw28528step0Labels = mixedMoment B raw28528step1 raw28528step1Labels := by
      have ha : raw28528step1 = (fun i j => raw28528step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28528step1 raw28528step0; decide +kernel
      have hl : raw28528step1Labels = raw28528step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28528step0 raw28528step0Labels permutation145 permutation2
    mixedMoment B raw28528step1 raw28528step1Labels = mixedMoment B raw28528step2 raw28528step2Labels := by
      have ha : raw28528step2 = -raw28528step1 := by apply Matrix.ext; change ∀ i j, raw28528step2 i j = -(raw28528step1 i j); unfold raw28528step2 raw28528step1; decide +kernel
      have hl : raw28528step2Labels = raw28528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical28529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28529 raw28529Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw28529 raw28529Labels = mixedMoment B raw28529step0 raw28529step0Labels := by
      have ha : raw28529step0 = (fun i j => raw28529 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28529step0 raw28529; decide +kernel
      have hl : raw28529step0Labels = raw28529Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28529 raw28529Labels permutation682 permutation2
    mixedMoment B raw28529step0 raw28529step0Labels = mixedMoment B raw28529step1 raw28529step1Labels := by
      have ha : raw28529step1 = -raw28529step0 := by apply Matrix.ext; change ∀ i j, raw28529step1 i j = -(raw28529step0 i j); unfold raw28529step1 raw28529step0; decide +kernel
      have hl : raw28529step1Labels = raw28529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3524 node3524Labels := by rfl

theorem canonical28530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28530 raw28530Labels = mixedMoment B node2119 node2119Labels := by
  calc
    mixedMoment B raw28530 raw28530Labels = mixedMoment B raw28530step0 raw28530step0Labels := by
      have hz : ∀ j, raw28530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28530step0 = (fun i j => raw28530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28530step0 raw28530; decide +kernel
      have hl : raw28530step0Labels = raw28530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28530 raw28530Labels permutation434 hz
    mixedMoment B raw28530step0 raw28530step0Labels = mixedMoment B raw28530step1 raw28530step1Labels := by
      have ha : raw28530step1 = (fun i j => raw28530step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28530step1 raw28530step0; decide +kernel
      have hl : raw28530step1Labels = raw28530step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28530step0 raw28530step0Labels permutation151 permutation2
    mixedMoment B raw28530step1 raw28530step1Labels = mixedMoment B raw28530step2 raw28530step2Labels := by
      have ha : raw28530step2 = -raw28530step1 := by apply Matrix.ext; change ∀ i j, raw28530step2 i j = -(raw28530step1 i j); unfold raw28530step2 raw28530step1; decide +kernel
      have hl : raw28530step2Labels = raw28530step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2119 node2119Labels := by rfl

theorem canonical28531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28531 raw28531Labels = mixedMoment B node2122 node2122Labels := by
  calc
    mixedMoment B raw28531 raw28531Labels = mixedMoment B raw28531step0 raw28531step0Labels := by
      have hz : ∀ j, raw28531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28531step0 = (fun i j => raw28531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28531step0 raw28531; decide +kernel
      have hl : raw28531step0Labels = raw28531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28531 raw28531Labels permutation434 hz
    mixedMoment B raw28531step0 raw28531step0Labels = mixedMoment B raw28531step1 raw28531step1Labels := by
      have ha : raw28531step1 = (fun i j => raw28531step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28531step1 raw28531step0; decide +kernel
      have hl : raw28531step1Labels = raw28531step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28531step0 raw28531step0Labels permutation151 permutation2
    mixedMoment B raw28531step1 raw28531step1Labels = mixedMoment B raw28531step2 raw28531step2Labels := by
      have ha : raw28531step2 = -raw28531step1 := by apply Matrix.ext; change ∀ i j, raw28531step2 i j = -(raw28531step1 i j); unfold raw28531step2 raw28531step1; decide +kernel
      have hl : raw28531step2Labels = raw28531step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2122 node2122Labels := by rfl

theorem canonical28532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28532 raw28532Labels = mixedMoment B node2128 node2128Labels := by
  calc
    mixedMoment B raw28532 raw28532Labels = mixedMoment B raw28532step0 raw28532step0Labels := by
      have hz : ∀ j, raw28532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28532step0 = (fun i j => raw28532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28532step0 raw28532; decide +kernel
      have hl : raw28532step0Labels = raw28532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28532 raw28532Labels permutation434 hz
    mixedMoment B raw28532step0 raw28532step0Labels = mixedMoment B raw28532step1 raw28532step1Labels := by
      have ha : raw28532step1 = (fun i j => raw28532step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28532step1 raw28532step0; decide +kernel
      have hl : raw28532step1Labels = raw28532step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28532step0 raw28532step0Labels permutation151 permutation2
    mixedMoment B raw28532step1 raw28532step1Labels = mixedMoment B raw28532step2 raw28532step2Labels := by
      have ha : raw28532step2 = -raw28532step1 := by apply Matrix.ext; change ∀ i j, raw28532step2 i j = -(raw28532step1 i j); unfold raw28532step2 raw28532step1; decide +kernel
      have hl : raw28532step2Labels = raw28532step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2128 node2128Labels := by rfl

theorem canonical28533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28533 raw28533Labels = mixedMoment B node2117 node2117Labels := by
  calc
    mixedMoment B raw28533 raw28533Labels = mixedMoment B raw28533step0 raw28533step0Labels := by
      have ha : raw28533step0 = (fun i j => raw28533 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28533step0 raw28533; decide +kernel
      have hl : raw28533step0Labels = raw28533Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28533 raw28533Labels permutation680 permutation2
    mixedMoment B raw28533step0 raw28533step0Labels = mixedMoment B raw28533step1 raw28533step1Labels := by
      have ha : raw28533step1 = -raw28533step0 := by apply Matrix.ext; change ∀ i j, raw28533step1 i j = -(raw28533step0 i j); unfold raw28533step1 raw28533step0; decide +kernel
      have hl : raw28533step1Labels = raw28533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2117 node2117Labels := by rfl

theorem canonical28534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28534 raw28534Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw28534 raw28534Labels = mixedMoment B raw28534step0 raw28534step0Labels := by
      have hz : ∀ j, raw28534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28534step0 = (fun i j => raw28534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28534step0 raw28534; decide +kernel
      have hl : raw28534step0Labels = raw28534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28534 raw28534Labels permutation434 hz
    mixedMoment B raw28534step0 raw28534step0Labels = mixedMoment B raw28534step1 raw28534step1Labels := by
      have ha : raw28534step1 = (fun i j => raw28534step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28534step1 raw28534step0; decide +kernel
      have hl : raw28534step1Labels = raw28534step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28534step0 raw28534step0Labels permutation145 permutation2
    mixedMoment B raw28534step1 raw28534step1Labels = mixedMoment B raw28534step2 raw28534step2Labels := by
      have ha : raw28534step2 = -raw28534step1 := by apply Matrix.ext; change ∀ i j, raw28534step2 i j = -(raw28534step1 i j); unfold raw28534step2 raw28534step1; decide +kernel
      have hl : raw28534step2Labels = raw28534step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical28535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28535 raw28535Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw28535 raw28535Labels = mixedMoment B raw28535step0 raw28535step0Labels := by
      have hz : ∀ j, raw28535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28535step0 = (fun i j => raw28535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28535step0 raw28535; decide +kernel
      have hl : raw28535step0Labels = raw28535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28535 raw28535Labels permutation434 hz
    mixedMoment B raw28535step0 raw28535step0Labels = mixedMoment B raw28535step1 raw28535step1Labels := by
      have ha : raw28535step1 = (fun i j => raw28535step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28535step1 raw28535step0; decide +kernel
      have hl : raw28535step1Labels = raw28535step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28535step0 raw28535step0Labels permutation104 permutation4
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical28536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28536 raw28536Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw28536 raw28536Labels = mixedMoment B raw28536step0 raw28536step0Labels := by
      have hz : ∀ j, raw28536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28536step0 = (fun i j => raw28536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28536step0 raw28536; decide +kernel
      have hl : raw28536step0Labels = raw28536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28536 raw28536Labels permutation434 hz
    mixedMoment B raw28536step0 raw28536step0Labels = mixedMoment B raw28536step1 raw28536step1Labels := by
      have hz : ∀ j, raw28536step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw28536step1 = (fun i j => raw28536step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw28536step1 raw28536step0; decide +kernel
      have hl : raw28536step1Labels = raw28536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28536step0 raw28536step0Labels permutation56 hz
    mixedMoment B raw28536step1 raw28536step1Labels = mixedMoment B raw28536step2 raw28536step2Labels := by
      have ha : raw28536step2 = (fun i j => raw28536step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28536step2 raw28536step1; decide +kernel
      have hl : raw28536step2Labels = raw28536step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28536step1 raw28536step1Labels permutation28 permutation0
    mixedMoment B raw28536step2 raw28536step2Labels = mixedMoment B raw28536step3 raw28536step3Labels := by
      have ha : raw28536step3 = -raw28536step2 := by apply Matrix.ext; change ∀ i j, raw28536step3 i j = -(raw28536step2 i j); unfold raw28536step3 raw28536step2; decide +kernel
      have hl : raw28536step3Labels = raw28536step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical28537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28537 raw28537Labels = mixedMoment B node2070 node2070Labels := by
  calc
    mixedMoment B raw28537 raw28537Labels = mixedMoment B raw28537step0 raw28537step0Labels := by
      have ha : raw28537step0 = (fun i j => raw28537 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28537step0 raw28537; decide +kernel
      have hl : raw28537step0Labels = raw28537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28537 raw28537Labels permutation682 permutation2
    mixedMoment B raw28537step0 raw28537step0Labels = mixedMoment B raw28537step1 raw28537step1Labels := by
      have ha : raw28537step1 = -raw28537step0 := by apply Matrix.ext; change ∀ i j, raw28537step1 i j = -(raw28537step0 i j); unfold raw28537step1 raw28537step0; decide +kernel
      have hl : raw28537step1Labels = raw28537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2070 node2070Labels := by rfl

theorem canonical28538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28538 raw28538Labels = mixedMoment B node2072 node2072Labels := by
  calc
    mixedMoment B raw28538 raw28538Labels = mixedMoment B raw28538step0 raw28538step0Labels := by
      have ha : raw28538step0 = (fun i j => raw28538 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28538step0 raw28538; decide +kernel
      have hl : raw28538step0Labels = raw28538Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28538 raw28538Labels permutation682 permutation2
    mixedMoment B raw28538step0 raw28538step0Labels = mixedMoment B raw28538step1 raw28538step1Labels := by
      have ha : raw28538step1 = -raw28538step0 := by apply Matrix.ext; change ∀ i j, raw28538step1 i j = -(raw28538step0 i j); unfold raw28538step1 raw28538step0; decide +kernel
      have hl : raw28538step1Labels = raw28538step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2072 node2072Labels := by rfl

theorem canonical28539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28539 raw28539Labels = mixedMoment B node2085 node2085Labels := by
  calc
    mixedMoment B raw28539 raw28539Labels = mixedMoment B raw28539step0 raw28539step0Labels := by
      have ha : raw28539step0 = (fun i j => raw28539 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28539step0 raw28539; decide +kernel
      have hl : raw28539step0Labels = raw28539Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28539 raw28539Labels permutation688 permutation2
    mixedMoment B raw28539step0 raw28539step0Labels = mixedMoment B raw28539step1 raw28539step1Labels := by
      have ha : raw28539step1 = -raw28539step0 := by apply Matrix.ext; change ∀ i j, raw28539step1 i j = -(raw28539step0 i j); unfold raw28539step1 raw28539step0; decide +kernel
      have hl : raw28539step1Labels = raw28539step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2085 node2085Labels := by rfl

theorem canonical28540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28540 raw28540Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw28540 raw28540Labels = mixedMoment B raw28540step0 raw28540step0Labels := by
      have ha : raw28540step0 = (fun i j => raw28540 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28540step0 raw28540; decide +kernel
      have hl : raw28540step0Labels = raw28540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28540 raw28540Labels permutation680 permutation2
    mixedMoment B raw28540step0 raw28540step0Labels = mixedMoment B raw28540step1 raw28540step1Labels := by
      have ha : raw28540step1 = -raw28540step0 := by apply Matrix.ext; change ∀ i j, raw28540step1 i j = -(raw28540step0 i j); unfold raw28540step1 raw28540step0; decide +kernel
      have hl : raw28540step1Labels = raw28540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2075 node2075Labels := by rfl

theorem canonical28541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28541 raw28541Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw28541 raw28541Labels = mixedMoment B raw28541step0 raw28541step0Labels := by
      have ha : raw28541step0 = (fun i j => raw28541 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28541step0 raw28541; decide +kernel
      have hl : raw28541step0Labels = raw28541Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28541 raw28541Labels permutation640 permutation2
    mixedMoment B raw28541step0 raw28541step0Labels = mixedMoment B raw28541step1 raw28541step1Labels := by
      have ha : raw28541step1 = -raw28541step0 := by apply Matrix.ext; change ∀ i j, raw28541step1 i j = -(raw28541step0 i j); unfold raw28541step1 raw28541step0; decide +kernel
      have hl : raw28541step1Labels = raw28541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2190 node2190Labels := by rfl

theorem canonical28542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28542 raw28542Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw28542 raw28542Labels = mixedMoment B raw28542step0 raw28542step0Labels := by
      have ha : raw28542step0 = (fun i j => raw28542 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28542step0 raw28542; decide +kernel
      have hl : raw28542step0Labels = raw28542Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28542 raw28542Labels permutation682 permutation2
    mixedMoment B raw28542step0 raw28542step0Labels = mixedMoment B raw28542step1 raw28542step1Labels := by
      have ha : raw28542step1 = -raw28542step0 := by apply Matrix.ext; change ∀ i j, raw28542step1 i j = -(raw28542step0 i j); unfold raw28542step1 raw28542step0; decide +kernel
      have hl : raw28542step1Labels = raw28542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical28543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28543 raw28543Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw28543 raw28543Labels = mixedMoment B raw28543step0 raw28543step0Labels := by
      have hz : ∀ j, raw28543 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw28543step0 = (fun i j => raw28543 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw28543step0 raw28543; decide +kernel
      have hl : raw28543step0Labels = raw28543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28543 raw28543Labels permutation265 hz
    mixedMoment B raw28543step0 raw28543step0Labels = mixedMoment B raw28543step1 raw28543step1Labels := by
      have ha : raw28543step1 = (fun i j => raw28543step0 (permutation137 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28543step1 raw28543step0; decide +kernel
      have hl : raw28543step1Labels = raw28543step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28543step0 raw28543step0Labels permutation137 permutation0
    mixedMoment B raw28543step1 raw28543step1Labels = mixedMoment B raw28543step2 raw28543step2Labels := by
      have ha : raw28543step2 = -raw28543step1 := by apply Matrix.ext; change ∀ i j, raw28543step2 i j = -(raw28543step1 i j); unfold raw28543step2 raw28543step1; decide +kernel
      have hl : raw28543step2Labels = raw28543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical223
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28544 raw28544Labels = mixedMoment B node2453 node2453Labels := by
  calc
    mixedMoment B raw28544 raw28544Labels = mixedMoment B raw28544step0 raw28544step0Labels := by
      have ha : raw28544step0 = (fun i j => raw28544 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28544step0 raw28544; decide +kernel
      have hl : raw28544step0Labels = raw28544Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28544 raw28544Labels permutation682 permutation2
    mixedMoment B raw28544step0 raw28544step0Labels = mixedMoment B raw28544step1 raw28544step1Labels := by
      have ha : raw28544step1 = -raw28544step0 := by apply Matrix.ext; change ∀ i j, raw28544step1 i j = -(raw28544step0 i j); unfold raw28544step1 raw28544step0; decide +kernel
      have hl : raw28544step1Labels = raw28544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2453 node2453Labels := by rfl

theorem canonical28545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28545 raw28545Labels = mixedMoment B node2455 node2455Labels := by
  calc
    mixedMoment B raw28545 raw28545Labels = mixedMoment B raw28545step0 raw28545step0Labels := by
      have ha : raw28545step0 = (fun i j => raw28545 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28545step0 raw28545; decide +kernel
      have hl : raw28545step0Labels = raw28545Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28545 raw28545Labels permutation682 permutation2
    mixedMoment B raw28545step0 raw28545step0Labels = mixedMoment B raw28545step1 raw28545step1Labels := by
      have ha : raw28545step1 = -raw28545step0 := by apply Matrix.ext; change ∀ i j, raw28545step1 i j = -(raw28545step0 i j); unfold raw28545step1 raw28545step0; decide +kernel
      have hl : raw28545step1Labels = raw28545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2455 node2455Labels := by rfl

theorem canonical28546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28546 raw28546Labels = mixedMoment B node2490 node2490Labels := by
  calc
    mixedMoment B raw28546 raw28546Labels = mixedMoment B raw28546step0 raw28546step0Labels := by
      have ha : raw28546step0 = (fun i j => raw28546 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28546step0 raw28546; decide +kernel
      have hl : raw28546step0Labels = raw28546Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28546 raw28546Labels permutation688 permutation2
    mixedMoment B raw28546step0 raw28546step0Labels = mixedMoment B raw28546step1 raw28546step1Labels := by
      have ha : raw28546step1 = -raw28546step0 := by apply Matrix.ext; change ∀ i j, raw28546step1 i j = -(raw28546step0 i j); unfold raw28546step1 raw28546step0; decide +kernel
      have hl : raw28546step1Labels = raw28546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2490 node2490Labels := by rfl

theorem canonical28547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28547 raw28547Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw28547 raw28547Labels = mixedMoment B raw28547step0 raw28547step0Labels := by
      have ha : raw28547step0 = (fun i j => raw28547 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28547step0 raw28547; decide +kernel
      have hl : raw28547step0Labels = raw28547Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28547 raw28547Labels permutation680 permutation2
    mixedMoment B raw28547step0 raw28547step0Labels = mixedMoment B raw28547step1 raw28547step1Labels := by
      have ha : raw28547step1 = -raw28547step0 := by apply Matrix.ext; change ∀ i j, raw28547step1 i j = -(raw28547step0 i j); unfold raw28547step1 raw28547step0; decide +kernel
      have hl : raw28547step1Labels = raw28547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2459 node2459Labels := by rfl

theorem canonical28548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28548 raw28548Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw28548 raw28548Labels = mixedMoment B raw28548step0 raw28548step0Labels := by
      have ha : raw28548step0 = (fun i j => raw28548 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28548step0 raw28548; decide +kernel
      have hl : raw28548step0Labels = raw28548Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28548 raw28548Labels permutation646 permutation2
    mixedMoment B raw28548step0 raw28548step0Labels = mixedMoment B raw28548step1 raw28548step1Labels := by
      have ha : raw28548step1 = -raw28548step0 := by apply Matrix.ext; change ∀ i j, raw28548step1 i j = -(raw28548step0 i j); unfold raw28548step1 raw28548step0; decide +kernel
      have hl : raw28548step1Labels = raw28548step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2697 node2697Labels := by rfl

theorem canonical28549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28549 raw28549Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw28549 raw28549Labels = mixedMoment B raw28549step0 raw28549step0Labels := by
      have ha : raw28549step0 = (fun i j => raw28549 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28549step0 raw28549; decide +kernel
      have hl : raw28549step0Labels = raw28549Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28549 raw28549Labels permutation682 permutation2
    mixedMoment B raw28549step0 raw28549step0Labels = mixedMoment B raw28549step1 raw28549step1Labels := by
      have ha : raw28549step1 = -raw28549step0 := by apply Matrix.ext; change ∀ i j, raw28549step1 i j = -(raw28549step0 i j); unfold raw28549step1 raw28549step0; decide +kernel
      have hl : raw28549step1Labels = raw28549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical28550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28550 raw28550Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw28550 raw28550Labels = mixedMoment B raw28550step0 raw28550step0Labels := by
      have hz : ∀ j, raw28550 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw28550step0 = (fun i j => raw28550 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw28550step0 raw28550; decide +kernel
      have hl : raw28550step0Labels = raw28550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28550 raw28550Labels permutation265 hz
    mixedMoment B raw28550step0 raw28550step0Labels = mixedMoment B raw28550step1 raw28550step1Labels := by
      have ha : raw28550step1 = (fun i j => raw28550step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28550step1 raw28550step0; decide +kernel
      have hl : raw28550step1Labels = raw28550step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28550step0 raw28550step0Labels permutation38 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical28551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28551 raw28551Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw28551 raw28551Labels = mixedMoment B raw28551step0 raw28551step0Labels := by
      have hz : ∀ j, raw28551 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw28551step0 = (fun i j => raw28551 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw28551step0 raw28551; decide +kernel
      have hl : raw28551step0Labels = raw28551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28551 raw28551Labels permutation265 hz
    mixedMoment B raw28551step0 raw28551step0Labels = mixedMoment B raw28551step1 raw28551step1Labels := by
      have ha : raw28551step1 = (fun i j => raw28551step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28551step1 raw28551step0; decide +kernel
      have hl : raw28551step1Labels = raw28551step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28551step0 raw28551step0Labels permutation38 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical28552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28552 raw28552Labels = mixedMoment B node2536 node2536Labels := by
  calc
    mixedMoment B raw28552 raw28552Labels = mixedMoment B raw28552step0 raw28552step0Labels := by
      have ha : raw28552step0 = (fun i j => raw28552 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28552step0 raw28552; decide +kernel
      have hl : raw28552step0Labels = raw28552Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28552 raw28552Labels permutation158 permutation2
    _ = mixedMoment B node2536 node2536Labels := by rfl

theorem canonical28553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28553 raw28553Labels = mixedMoment B node2565 node2565Labels := by
  calc
    _ = mixedMoment B node2565 node2565Labels := by rfl

theorem canonical28554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28554 raw28554Labels = mixedMoment B node2533 node2533Labels := by
  calc
    mixedMoment B raw28554 raw28554Labels = mixedMoment B raw28554step0 raw28554step0Labels := by
      have ha : raw28554step0 = (fun i j => raw28554 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28554step0 raw28554; decide +kernel
      have hl : raw28554step0Labels = raw28554Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28554 raw28554Labels permutation158 permutation2
    _ = mixedMoment B node2533 node2533Labels := by rfl

theorem canonical28555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28555 raw28555Labels = mixedMoment B node1991 node1991Labels := by
  calc
    mixedMoment B raw28555 raw28555Labels = mixedMoment B raw28555step0 raw28555step0Labels := by
      have ha : raw28555step0 = (fun i j => raw28555 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28555step0 raw28555; decide +kernel
      have hl : raw28555step0Labels = raw28555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28555 raw28555Labels permutation682 permutation2
    mixedMoment B raw28555step0 raw28555step0Labels = mixedMoment B raw28555step1 raw28555step1Labels := by
      have ha : raw28555step1 = -raw28555step0 := by apply Matrix.ext; change ∀ i j, raw28555step1 i j = -(raw28555step0 i j); unfold raw28555step1 raw28555step0; decide +kernel
      have hl : raw28555step1Labels = raw28555step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1991 node1991Labels := by rfl

theorem canonical28556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28556 raw28556Labels = mixedMoment B node1993 node1993Labels := by
  calc
    mixedMoment B raw28556 raw28556Labels = mixedMoment B raw28556step0 raw28556step0Labels := by
      have ha : raw28556step0 = (fun i j => raw28556 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28556step0 raw28556; decide +kernel
      have hl : raw28556step0Labels = raw28556Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28556 raw28556Labels permutation682 permutation2
    mixedMoment B raw28556step0 raw28556step0Labels = mixedMoment B raw28556step1 raw28556step1Labels := by
      have ha : raw28556step1 = -raw28556step0 := by apply Matrix.ext; change ∀ i j, raw28556step1 i j = -(raw28556step0 i j); unfold raw28556step1 raw28556step0; decide +kernel
      have hl : raw28556step1Labels = raw28556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1993 node1993Labels := by rfl

theorem canonical28557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28557 raw28557Labels = mixedMoment B node2030 node2030Labels := by
  calc
    mixedMoment B raw28557 raw28557Labels = mixedMoment B raw28557step0 raw28557step0Labels := by
      have ha : raw28557step0 = (fun i j => raw28557 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28557step0 raw28557; decide +kernel
      have hl : raw28557step0Labels = raw28557Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28557 raw28557Labels permutation688 permutation2
    mixedMoment B raw28557step0 raw28557step0Labels = mixedMoment B raw28557step1 raw28557step1Labels := by
      have ha : raw28557step1 = -raw28557step0 := by apply Matrix.ext; change ∀ i j, raw28557step1 i j = -(raw28557step0 i j); unfold raw28557step1 raw28557step0; decide +kernel
      have hl : raw28557step1Labels = raw28557step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2030 node2030Labels := by rfl

theorem canonical28558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28558 raw28558Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw28558 raw28558Labels = mixedMoment B raw28558step0 raw28558step0Labels := by
      have ha : raw28558step0 = (fun i j => raw28558 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28558step0 raw28558; decide +kernel
      have hl : raw28558step0Labels = raw28558Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28558 raw28558Labels permutation680 permutation2
    mixedMoment B raw28558step0 raw28558step0Labels = mixedMoment B raw28558step1 raw28558step1Labels := by
      have ha : raw28558step1 = -raw28558step0 := by apply Matrix.ext; change ∀ i j, raw28558step1 i j = -(raw28558step0 i j); unfold raw28558step1 raw28558step0; decide +kernel
      have hl : raw28558step1Labels = raw28558step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1997 node1997Labels := by rfl

theorem canonical28559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28559 raw28559Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw28559 raw28559Labels = mixedMoment B raw28559step0 raw28559step0Labels := by
      have hz : ∀ j, raw28559 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28559step0 = (fun i j => raw28559 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28559step0 raw28559; decide +kernel
      have hl : raw28559step0Labels = raw28559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28559 raw28559Labels permutation520 hz
    mixedMoment B raw28559step0 raw28559step0Labels = mixedMoment B raw28559step1 raw28559step1Labels := by
      have ha : raw28559step1 = (fun i j => raw28559step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28559step1 raw28559step0; decide +kernel
      have hl : raw28559step1Labels = raw28559step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28559step0 raw28559step0Labels permutation145 permutation2
    mixedMoment B raw28559step1 raw28559step1Labels = mixedMoment B raw28559step2 raw28559step2Labels := by
      have ha : raw28559step2 = -raw28559step1 := by apply Matrix.ext; change ∀ i j, raw28559step2 i j = -(raw28559step1 i j); unfold raw28559step2 raw28559step1; decide +kernel
      have hl : raw28559step2Labels = raw28559step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical28560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28560 raw28560Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw28560 raw28560Labels = mixedMoment B raw28560step0 raw28560step0Labels := by
      have ha : raw28560step0 = (fun i j => raw28560 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28560step0 raw28560; decide +kernel
      have hl : raw28560step0Labels = raw28560Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28560 raw28560Labels permutation682 permutation2
    mixedMoment B raw28560step0 raw28560step0Labels = mixedMoment B raw28560step1 raw28560step1Labels := by
      have ha : raw28560step1 = -raw28560step0 := by apply Matrix.ext; change ∀ i j, raw28560step1 i j = -(raw28560step0 i j); unfold raw28560step1 raw28560step0; decide +kernel
      have hl : raw28560step1Labels = raw28560step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical28561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28561 raw28561Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw28561 raw28561Labels = mixedMoment B raw28561step0 raw28561step0Labels := by
      have hz : ∀ j, raw28561 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28561step0 = (fun i j => raw28561 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28561step0 raw28561; decide +kernel
      have hl : raw28561step0Labels = raw28561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28561 raw28561Labels permutation520 hz
    mixedMoment B raw28561step0 raw28561step0Labels = mixedMoment B raw28561step1 raw28561step1Labels := by
      have hz : ∀ j, raw28561step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw28561step1 = (fun i j => raw28561step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw28561step1 raw28561step0; decide +kernel
      have hl : raw28561step1Labels = raw28561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28561step0 raw28561step0Labels permutation56 hz
    mixedMoment B raw28561step1 raw28561step1Labels = mixedMoment B raw28561step2 raw28561step2Labels := by
      have ha : raw28561step2 = (fun i j => raw28561step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28561step2 raw28561step1; decide +kernel
      have hl : raw28561step2Labels = raw28561step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28561step1 raw28561step1Labels permutation28 permutation0
    mixedMoment B raw28561step2 raw28561step2Labels = mixedMoment B raw28561step3 raw28561step3Labels := by
      have ha : raw28561step3 = -raw28561step2 := by apply Matrix.ext; change ∀ i j, raw28561step3 i j = -(raw28561step2 i j); unfold raw28561step3 raw28561step2; decide +kernel
      have hl : raw28561step3Labels = raw28561step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical28591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28591 raw28591Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw28591 raw28591Labels = mixedMoment B raw28591step0 raw28591step0Labels := by
      have hz : ∀ j, raw28591 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28591step0 = (fun i j => raw28591 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28591step0 raw28591; decide +kernel
      have hl : raw28591step0Labels = raw28591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28591 raw28591Labels permutation434 hz
    mixedMoment B raw28591step0 raw28591step0Labels = mixedMoment B raw28591step1 raw28591step1Labels := by
      have hz : ∀ j, raw28591step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28591step1 = (fun i j => raw28591step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28591step1 raw28591step0; decide +kernel
      have hl : raw28591step1Labels = raw28591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28591step0 raw28591step0Labels permutation80 hz
    mixedMoment B raw28591step1 raw28591step1Labels = mixedMoment B raw28591step2 raw28591step2Labels := by
      have ha : raw28591step2 = (fun i j => raw28591step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28591step2 raw28591step1; decide +kernel
      have hl : raw28591step2Labels = raw28591step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28591step1 raw28591step1Labels permutation29 permutation7
    mixedMoment B raw28591step2 raw28591step2Labels = mixedMoment B raw28591step3 raw28591step3Labels := by
      have ha : raw28591step3 = raw28591step2 := by apply Matrix.ext; unfold raw28591step3 raw28591step2; decide +kernel
      have hl : raw28591step2Labels = labelEmbedding1 ∘ raw28591step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28591step2 raw28591step2Labels raw28591step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical28592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28592 raw28592Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw28592 raw28592Labels = mixedMoment B raw28592step0 raw28592step0Labels := by
      have hz : ∀ j, raw28592 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28592step0 = (fun i j => raw28592 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28592step0 raw28592; decide +kernel
      have hl : raw28592step0Labels = raw28592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28592 raw28592Labels permutation434 hz
    mixedMoment B raw28592step0 raw28592step0Labels = mixedMoment B raw28592step1 raw28592step1Labels := by
      have ha : raw28592step1 = (fun i j => raw28592step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28592step1 raw28592step0; decide +kernel
      have hl : raw28592step1Labels = raw28592step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28592step0 raw28592step0Labels permutation137 permutation7
    mixedMoment B raw28592step1 raw28592step1Labels = mixedMoment B raw28592step2 raw28592step2Labels := by
      have ha : raw28592step2 = raw28592step1 := by apply Matrix.ext; unfold raw28592step2 raw28592step1; decide +kernel
      have hl : raw28592step1Labels = labelEmbedding1 ∘ raw28592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28592step1 raw28592step1Labels raw28592step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical28593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28593 raw28593Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw28593 raw28593Labels = mixedMoment B raw28593step0 raw28593step0Labels := by
      have hz : ∀ j, raw28593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28593step0 = (fun i j => raw28593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28593step0 raw28593; decide +kernel
      have hl : raw28593step0Labels = raw28593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28593 raw28593Labels permutation346 hz
    mixedMoment B raw28593step0 raw28593step0Labels = mixedMoment B raw28593step1 raw28593step1Labels := by
      have ha : raw28593step1 = (fun i j => raw28593step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28593step1 raw28593step0; decide +kernel
      have hl : raw28593step1Labels = raw28593step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28593step0 raw28593step0Labels permutation137 permutation7
    mixedMoment B raw28593step1 raw28593step1Labels = mixedMoment B raw28593step2 raw28593step2Labels := by
      have ha : raw28593step2 = raw28593step1 := by apply Matrix.ext; unfold raw28593step2 raw28593step1; decide +kernel
      have hl : raw28593step1Labels = labelEmbedding1 ∘ raw28593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28593step1 raw28593step1Labels raw28593step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical28594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28594 raw28594Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw28594 raw28594Labels = mixedMoment B raw28594step0 raw28594step0Labels := by
      have hz : ∀ j, raw28594 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28594step0 = (fun i j => raw28594 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28594step0 raw28594; decide +kernel
      have hl : raw28594step0Labels = raw28594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28594 raw28594Labels permutation434 hz
    mixedMoment B raw28594step0 raw28594step0Labels = mixedMoment B raw28594step1 raw28594step1Labels := by
      have ha : raw28594step1 = (fun i j => raw28594step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28594step1 raw28594step0; decide +kernel
      have hl : raw28594step1Labels = raw28594step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28594step0 raw28594step0Labels permutation143 permutation7
    mixedMoment B raw28594step1 raw28594step1Labels = mixedMoment B raw28594step2 raw28594step2Labels := by
      have ha : raw28594step2 = raw28594step1 := by apply Matrix.ext; unfold raw28594step2 raw28594step1; decide +kernel
      have hl : raw28594step1Labels = labelEmbedding1 ∘ raw28594step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28594step1 raw28594step1Labels raw28594step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

theorem canonical28595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28595 raw28595Labels = mixedMoment B node2189 node2189Labels := by
  calc
    mixedMoment B raw28595 raw28595Labels = mixedMoment B raw28595step0 raw28595step0Labels := by
      have ha : raw28595step0 = (fun i j => raw28595 (permutation632 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28595step0 raw28595; decide +kernel
      have hl : raw28595step0Labels = raw28595Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28595 raw28595Labels permutation632 permutation7
    mixedMoment B raw28595step0 raw28595step0Labels = mixedMoment B raw28595step1 raw28595step1Labels := by
      have ha : raw28595step1 = raw28595step0 := by apply Matrix.ext; unfold raw28595step1 raw28595step0; decide +kernel
      have hl : raw28595step0Labels = labelEmbedding1 ∘ raw28595step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28595step0 raw28595step0Labels raw28595step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2189 node2189Labels := by rfl

theorem canonical28596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28596 raw28596Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw28596 raw28596Labels = mixedMoment B raw28596step0 raw28596step0Labels := by
      have hz : ∀ j, raw28596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28596step0 = (fun i j => raw28596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28596step0 raw28596; decide +kernel
      have hl : raw28596step0Labels = raw28596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28596 raw28596Labels permutation346 hz
    mixedMoment B raw28596step0 raw28596step0Labels = mixedMoment B raw28596step1 raw28596step1Labels := by
      have ha : raw28596step1 = (fun i j => raw28596step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28596step1 raw28596step0; decide +kernel
      have hl : raw28596step1Labels = raw28596step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28596step0 raw28596step0Labels permutation143 permutation7
    mixedMoment B raw28596step1 raw28596step1Labels = mixedMoment B raw28596step2 raw28596step2Labels := by
      have ha : raw28596step2 = raw28596step1 := by apply Matrix.ext; unfold raw28596step2 raw28596step1; decide +kernel
      have hl : raw28596step1Labels = labelEmbedding1 ∘ raw28596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28596step1 raw28596step1Labels raw28596step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

theorem canonical28597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28597 raw28597Labels = mixedMoment B node2189 node2189Labels := by
  calc
    mixedMoment B raw28597 raw28597Labels = mixedMoment B raw28597step0 raw28597step0Labels := by
      have ha : raw28597step0 = (fun i j => raw28597 (permutation653 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28597step0 raw28597; decide +kernel
      have hl : raw28597step0Labels = raw28597Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28597 raw28597Labels permutation653 permutation7
    mixedMoment B raw28597step0 raw28597step0Labels = mixedMoment B raw28597step1 raw28597step1Labels := by
      have ha : raw28597step1 = raw28597step0 := by apply Matrix.ext; unfold raw28597step1 raw28597step0; decide +kernel
      have hl : raw28597step0Labels = labelEmbedding1 ∘ raw28597step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28597step0 raw28597step0Labels raw28597step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2189 node2189Labels := by rfl

theorem canonical28598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28598 raw28598Labels = mixedMoment B node2273 node2273Labels := by
  calc
    mixedMoment B raw28598 raw28598Labels = mixedMoment B raw28598step0 raw28598step0Labels := by
      have hz : ∀ j, raw28598 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28598step0 = (fun i j => raw28598 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28598step0 raw28598; decide +kernel
      have hl : raw28598step0Labels = raw28598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28598 raw28598Labels permutation434 hz
    mixedMoment B raw28598step0 raw28598step0Labels = mixedMoment B raw28598step1 raw28598step1Labels := by
      have hz : ∀ j, raw28598step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28598step1 = (fun i j => raw28598step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28598step1 raw28598step0; decide +kernel
      have hl : raw28598step1Labels = raw28598step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28598step0 raw28598step0Labels permutation80 hz
    mixedMoment B raw28598step1 raw28598step1Labels = mixedMoment B raw28598step2 raw28598step2Labels := by
      have ha : raw28598step2 = (fun i j => raw28598step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28598step2 raw28598step1; decide +kernel
      have hl : raw28598step2Labels = raw28598step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28598step1 raw28598step1Labels permutation29 permutation7
    mixedMoment B raw28598step2 raw28598step2Labels = mixedMoment B raw28598step3 raw28598step3Labels := by
      have ha : raw28598step3 = raw28598step2 := by apply Matrix.ext; unfold raw28598step3 raw28598step2; decide +kernel
      have hl : raw28598step2Labels = labelEmbedding1 ∘ raw28598step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28598step2 raw28598step2Labels raw28598step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2273 node2273Labels := by rfl

theorem canonical28599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28599 raw28599Labels = mixedMoment B node2239 node2239Labels := by
  calc
    mixedMoment B raw28599 raw28599Labels = mixedMoment B raw28599step0 raw28599step0Labels := by
      have hz : ∀ j, raw28599 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28599step0 = (fun i j => raw28599 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28599step0 raw28599; decide +kernel
      have hl : raw28599step0Labels = raw28599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28599 raw28599Labels permutation434 hz
    mixedMoment B raw28599step0 raw28599step0Labels = mixedMoment B raw28599step1 raw28599step1Labels := by
      have ha : raw28599step1 = (fun i j => raw28599step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28599step1 raw28599step0; decide +kernel
      have hl : raw28599step1Labels = raw28599step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28599step0 raw28599step0Labels permutation137 permutation7
    mixedMoment B raw28599step1 raw28599step1Labels = mixedMoment B raw28599step2 raw28599step2Labels := by
      have ha : raw28599step2 = raw28599step1 := by apply Matrix.ext; unfold raw28599step2 raw28599step1; decide +kernel
      have hl : raw28599step1Labels = labelEmbedding1 ∘ raw28599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28599step1 raw28599step1Labels raw28599step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2239 node2239Labels := by rfl

theorem canonical28600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28600 raw28600Labels = mixedMoment B node2239 node2239Labels := by
  calc
    mixedMoment B raw28600 raw28600Labels = mixedMoment B raw28600step0 raw28600step0Labels := by
      have hz : ∀ j, raw28600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28600step0 = (fun i j => raw28600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28600step0 raw28600; decide +kernel
      have hl : raw28600step0Labels = raw28600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28600 raw28600Labels permutation346 hz
    mixedMoment B raw28600step0 raw28600step0Labels = mixedMoment B raw28600step1 raw28600step1Labels := by
      have ha : raw28600step1 = (fun i j => raw28600step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28600step1 raw28600step0; decide +kernel
      have hl : raw28600step1Labels = raw28600step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28600step0 raw28600step0Labels permutation137 permutation7
    mixedMoment B raw28600step1 raw28600step1Labels = mixedMoment B raw28600step2 raw28600step2Labels := by
      have ha : raw28600step2 = raw28600step1 := by apply Matrix.ext; unfold raw28600step2 raw28600step1; decide +kernel
      have hl : raw28600step1Labels = labelEmbedding1 ∘ raw28600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28600step1 raw28600step1Labels raw28600step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2239 node2239Labels := by rfl

theorem canonical28601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28601 raw28601Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw28601 raw28601Labels = mixedMoment B raw28601step0 raw28601step0Labels := by
      have hz : ∀ j, raw28601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28601step0 = (fun i j => raw28601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28601step0 raw28601; decide +kernel
      have hl : raw28601step0Labels = raw28601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28601 raw28601Labels permutation434 hz
    mixedMoment B raw28601step0 raw28601step0Labels = mixedMoment B raw28601step1 raw28601step1Labels := by
      have hz : ∀ j, raw28601step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28601step1 = (fun i j => raw28601step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28601step1 raw28601step0; decide +kernel
      have hl : raw28601step1Labels = raw28601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28601step0 raw28601step0Labels permutation80 hz
    mixedMoment B raw28601step1 raw28601step1Labels = mixedMoment B raw28601step2 raw28601step2Labels := by
      have ha : raw28601step2 = (fun i j => raw28601step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28601step2 raw28601step1; decide +kernel
      have hl : raw28601step2Labels = raw28601step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28601step1 raw28601step1Labels permutation29 permutation7
    mixedMoment B raw28601step2 raw28601step2Labels = mixedMoment B raw28601step3 raw28601step3Labels := by
      have ha : raw28601step3 = raw28601step2 := by apply Matrix.ext; unfold raw28601step3 raw28601step2; decide +kernel
      have hl : raw28601step2Labels = labelEmbedding1 ∘ raw28601step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28601step2 raw28601step2Labels raw28601step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1735 node1735Labels := by rfl

theorem canonical28602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28602 raw28602Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw28602 raw28602Labels = mixedMoment B raw28602step0 raw28602step0Labels := by
      have hz : ∀ j, raw28602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28602step0 = (fun i j => raw28602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28602step0 raw28602; decide +kernel
      have hl : raw28602step0Labels = raw28602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28602 raw28602Labels permutation434 hz
    mixedMoment B raw28602step0 raw28602step0Labels = mixedMoment B raw28602step1 raw28602step1Labels := by
      have ha : raw28602step1 = (fun i j => raw28602step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28602step1 raw28602step0; decide +kernel
      have hl : raw28602step1Labels = raw28602step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28602step0 raw28602step0Labels permutation137 permutation7
    mixedMoment B raw28602step1 raw28602step1Labels = mixedMoment B raw28602step2 raw28602step2Labels := by
      have ha : raw28602step2 = raw28602step1 := by apply Matrix.ext; unfold raw28602step2 raw28602step1; decide +kernel
      have hl : raw28602step1Labels = labelEmbedding1 ∘ raw28602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28602step1 raw28602step1Labels raw28602step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

theorem canonical28603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28603 raw28603Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw28603 raw28603Labels = mixedMoment B raw28603step0 raw28603step0Labels := by
      have hz : ∀ j, raw28603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28603step0 = (fun i j => raw28603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28603step0 raw28603; decide +kernel
      have hl : raw28603step0Labels = raw28603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28603 raw28603Labels permutation346 hz
    mixedMoment B raw28603step0 raw28603step0Labels = mixedMoment B raw28603step1 raw28603step1Labels := by
      have ha : raw28603step1 = (fun i j => raw28603step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28603step1 raw28603step0; decide +kernel
      have hl : raw28603step1Labels = raw28603step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28603step0 raw28603step0Labels permutation137 permutation7
    mixedMoment B raw28603step1 raw28603step1Labels = mixedMoment B raw28603step2 raw28603step2Labels := by
      have ha : raw28603step2 = raw28603step1 := by apply Matrix.ext; unfold raw28603step2 raw28603step1; decide +kernel
      have hl : raw28603step1Labels = labelEmbedding1 ∘ raw28603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28603step1 raw28603step1Labels raw28603step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

theorem canonical28604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28604 raw28604Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw28604 raw28604Labels = mixedMoment B raw28604step0 raw28604step0Labels := by
      have hz : ∀ j, raw28604 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28604step0 = (fun i j => raw28604 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28604step0 raw28604; decide +kernel
      have hl : raw28604step0Labels = raw28604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28604 raw28604Labels permutation434 hz
    mixedMoment B raw28604step0 raw28604step0Labels = mixedMoment B raw28604step1 raw28604step1Labels := by
      have hz : ∀ j, raw28604step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28604step1 = (fun i j => raw28604step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28604step1 raw28604step0; decide +kernel
      have hl : raw28604step1Labels = raw28604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28604step0 raw28604step0Labels permutation80 hz
    mixedMoment B raw28604step1 raw28604step1Labels = mixedMoment B raw28604step2 raw28604step2Labels := by
      have ha : raw28604step2 = (fun i j => raw28604step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28604step2 raw28604step1; decide +kernel
      have hl : raw28604step2Labels = raw28604step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28604step1 raw28604step1Labels permutation31 permutation2
    mixedMoment B raw28604step2 raw28604step2Labels = mixedMoment B raw28604step3 raw28604step3Labels := by
      have ha : raw28604step3 = -raw28604step2 := by apply Matrix.ext; change ∀ i j, raw28604step3 i j = -(raw28604step2 i j); unfold raw28604step3 raw28604step2; decide +kernel
      have hl : raw28604step3Labels = raw28604step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2115 node2115Labels := by rfl

theorem canonical28605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28605 raw28605Labels = mixedMoment B node1978 node1978Labels := by
  calc
    mixedMoment B raw28605 raw28605Labels = mixedMoment B raw28605step0 raw28605step0Labels := by
      have hz : ∀ j, raw28605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28605step0 = (fun i j => raw28605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28605step0 raw28605; decide +kernel
      have hl : raw28605step0Labels = raw28605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28605 raw28605Labels permutation434 hz
    mixedMoment B raw28605step0 raw28605step0Labels = mixedMoment B raw28605step1 raw28605step1Labels := by
      have ha : raw28605step1 = (fun i j => raw28605step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28605step1 raw28605step0; decide +kernel
      have hl : raw28605step1Labels = raw28605step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28605step0 raw28605step0Labels permutation145 permutation2
    mixedMoment B raw28605step1 raw28605step1Labels = mixedMoment B raw28605step2 raw28605step2Labels := by
      have ha : raw28605step2 = -raw28605step1 := by apply Matrix.ext; change ∀ i j, raw28605step2 i j = -(raw28605step1 i j); unfold raw28605step2 raw28605step1; decide +kernel
      have hl : raw28605step2Labels = raw28605step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1978 node1978Labels := by rfl

theorem canonical28606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28606 raw28606Labels = mixedMoment B node1978 node1978Labels := by
  calc
    mixedMoment B raw28606 raw28606Labels = mixedMoment B raw28606step0 raw28606step0Labels := by
      have hz : ∀ j, raw28606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28606step0 = (fun i j => raw28606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28606step0 raw28606; decide +kernel
      have hl : raw28606step0Labels = raw28606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28606 raw28606Labels permutation346 hz
    mixedMoment B raw28606step0 raw28606step0Labels = mixedMoment B raw28606step1 raw28606step1Labels := by
      have ha : raw28606step1 = (fun i j => raw28606step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28606step1 raw28606step0; decide +kernel
      have hl : raw28606step1Labels = raw28606step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28606step0 raw28606step0Labels permutation145 permutation2
    mixedMoment B raw28606step1 raw28606step1Labels = mixedMoment B raw28606step2 raw28606step2Labels := by
      have ha : raw28606step2 = -raw28606step1 := by apply Matrix.ext; change ∀ i j, raw28606step2 i j = -(raw28606step1 i j); unfold raw28606step2 raw28606step1; decide +kernel
      have hl : raw28606step2Labels = raw28606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1978 node1978Labels := by rfl

theorem canonical28607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28607 raw28607Labels = mixedMoment B node1830 node1830Labels := by
  calc
    mixedMoment B raw28607 raw28607Labels = mixedMoment B raw28607step0 raw28607step0Labels := by
      have hz : ∀ j, raw28607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28607step0 = (fun i j => raw28607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28607step0 raw28607; decide +kernel
      have hl : raw28607step0Labels = raw28607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28607 raw28607Labels permutation434 hz
    mixedMoment B raw28607step0 raw28607step0Labels = mixedMoment B raw28607step1 raw28607step1Labels := by
      have hz : ∀ j, raw28607step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28607step1 = (fun i j => raw28607step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28607step1 raw28607step0; decide +kernel
      have hl : raw28607step1Labels = raw28607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28607step0 raw28607step0Labels permutation80 hz
    mixedMoment B raw28607step1 raw28607step1Labels = mixedMoment B raw28607step2 raw28607step2Labels := by
      have ha : raw28607step2 = (fun i j => raw28607step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28607step2 raw28607step1; decide +kernel
      have hl : raw28607step2Labels = raw28607step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28607step1 raw28607step1Labels permutation31 permutation2
    mixedMoment B raw28607step2 raw28607step2Labels = mixedMoment B raw28607step3 raw28607step3Labels := by
      have ha : raw28607step3 = -raw28607step2 := by apply Matrix.ext; change ∀ i j, raw28607step3 i j = -(raw28607step2 i j); unfold raw28607step3 raw28607step2; decide +kernel
      have hl : raw28607step3Labels = raw28607step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1830 node1830Labels := by rfl

theorem canonical28608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28608 raw28608Labels = mixedMoment B node952 node952Labels := by
  calc
    mixedMoment B raw28608 raw28608Labels = mixedMoment B raw28608step0 raw28608step0Labels := by
      have hz : ∀ j, raw28608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28608step0 = (fun i j => raw28608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28608step0 raw28608; decide +kernel
      have hl : raw28608step0Labels = raw28608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28608 raw28608Labels permutation434 hz
    mixedMoment B raw28608step0 raw28608step0Labels = mixedMoment B raw28608step1 raw28608step1Labels := by
      have hz : ∀ j, raw28608step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28608step1 = (fun i j => raw28608step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28608step1 raw28608step0; decide +kernel
      have hl : raw28608step1Labels = raw28608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28608step0 raw28608step0Labels permutation80 hz
    mixedMoment B raw28608step1 raw28608step1Labels = mixedMoment B raw28608step2 raw28608step2Labels := by
      have ha : raw28608step2 = (fun i j => raw28608step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28608step2 raw28608step1; decide +kernel
      have hl : raw28608step2Labels = raw28608step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28608step1 raw28608step1Labels permutation31 permutation2
    mixedMoment B raw28608step2 raw28608step2Labels = mixedMoment B raw28608step3 raw28608step3Labels := by
      have ha : raw28608step3 = -raw28608step2 := by apply Matrix.ext; change ∀ i j, raw28608step3 i j = -(raw28608step2 i j); unfold raw28608step3 raw28608step2; decide +kernel
      have hl : raw28608step3Labels = raw28608step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node952 node952Labels := by rfl

theorem canonical28609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28609 raw28609Labels = mixedMoment B node1972 node1972Labels := by
  calc
    mixedMoment B raw28609 raw28609Labels = mixedMoment B raw28609step0 raw28609step0Labels := by
      have ha : raw28609step0 = (fun i j => raw28609 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28609step0 raw28609; decide +kernel
      have hl : raw28609step0Labels = raw28609Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28609 raw28609Labels permutation644 permutation2
    mixedMoment B raw28609step0 raw28609step0Labels = mixedMoment B raw28609step1 raw28609step1Labels := by
      have ha : raw28609step1 = -raw28609step0 := by apply Matrix.ext; change ∀ i j, raw28609step1 i j = -(raw28609step0 i j); unfold raw28609step1 raw28609step0; decide +kernel
      have hl : raw28609step1Labels = raw28609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1972 node1972Labels := by rfl

theorem canonical28610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28610 raw28610Labels = mixedMoment B node2588 node2588Labels := by
  calc
    mixedMoment B raw28610 raw28610Labels = mixedMoment B raw28610step0 raw28610step0Labels := by
      have hz : ∀ j, raw28610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28610step0 = (fun i j => raw28610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28610step0 raw28610; decide +kernel
      have hl : raw28610step0Labels = raw28610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28610 raw28610Labels permutation434 hz
    mixedMoment B raw28610step0 raw28610step0Labels = mixedMoment B raw28610step1 raw28610step1Labels := by
      have ha : raw28610step1 = (fun i j => raw28610step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28610step1 raw28610step0; decide +kernel
      have hl : raw28610step1Labels = raw28610step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28610step0 raw28610step0Labels permutation34 permutation2
    _ = mixedMoment B node2588 node2588Labels := by rfl

theorem canonical28611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28611 raw28611Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw28611 raw28611Labels = mixedMoment B raw28611step0 raw28611step0Labels := by
      have hz : ∀ j, raw28611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28611step0 = (fun i j => raw28611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28611step0 raw28611; decide +kernel
      have hl : raw28611step0Labels = raw28611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28611 raw28611Labels permutation434 hz
    mixedMoment B raw28611step0 raw28611step0Labels = mixedMoment B raw28611step1 raw28611step1Labels := by
      have ha : raw28611step1 = (fun i j => raw28611step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28611step1 raw28611step0; decide +kernel
      have hl : raw28611step1Labels = raw28611step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28611step0 raw28611step0Labels permutation149 permutation2
    mixedMoment B raw28611step1 raw28611step1Labels = mixedMoment B raw28611step2 raw28611step2Labels := by
      have ha : raw28611step2 = -raw28611step1 := by apply Matrix.ext; change ∀ i j, raw28611step2 i j = -(raw28611step1 i j); unfold raw28611step2 raw28611step1; decide +kernel
      have hl : raw28611step2Labels = raw28611step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical28612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28612 raw28612Labels = mixedMoment B node1972 node1972Labels := by
  calc
    mixedMoment B raw28612 raw28612Labels = mixedMoment B raw28612step0 raw28612step0Labels := by
      have ha : raw28612step0 = (fun i j => raw28612 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28612step0 raw28612; decide +kernel
      have hl : raw28612step0Labels = raw28612Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28612 raw28612Labels permutation662 permutation2
    mixedMoment B raw28612step0 raw28612step0Labels = mixedMoment B raw28612step1 raw28612step1Labels := by
      have ha : raw28612step1 = -raw28612step0 := by apply Matrix.ext; change ∀ i j, raw28612step1 i j = -(raw28612step0 i j); unfold raw28612step1 raw28612step0; decide +kernel
      have hl : raw28612step1Labels = raw28612step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1972 node1972Labels := by rfl

theorem canonical28613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28613 raw28613Labels = mixedMoment B node1823 node1823Labels := by
  calc
    mixedMoment B raw28613 raw28613Labels = mixedMoment B raw28613step0 raw28613step0Labels := by
      have hz : ∀ j, raw28613 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28613step0 = (fun i j => raw28613 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28613step0 raw28613; decide +kernel
      have hl : raw28613step0Labels = raw28613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28613 raw28613Labels permutation434 hz
    mixedMoment B raw28613step0 raw28613step0Labels = mixedMoment B raw28613step1 raw28613step1Labels := by
      have ha : raw28613step1 = (fun i j => raw28613step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28613step1 raw28613step0; decide +kernel
      have hl : raw28613step1Labels = raw28613step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28613step0 raw28613step0Labels permutation149 permutation2
    mixedMoment B raw28613step1 raw28613step1Labels = mixedMoment B raw28613step2 raw28613step2Labels := by
      have ha : raw28613step2 = -raw28613step1 := by apply Matrix.ext; change ∀ i j, raw28613step2 i j = -(raw28613step1 i j); unfold raw28613step2 raw28613step1; decide +kernel
      have hl : raw28613step2Labels = raw28613step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1823 node1823Labels := by rfl

theorem canonical28614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28614 raw28614Labels = mixedMoment B node943 node943Labels := by
  calc
    mixedMoment B raw28614 raw28614Labels = mixedMoment B raw28614step0 raw28614step0Labels := by
      have hz : ∀ j, raw28614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28614step0 = (fun i j => raw28614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28614step0 raw28614; decide +kernel
      have hl : raw28614step0Labels = raw28614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28614 raw28614Labels permutation434 hz
    mixedMoment B raw28614step0 raw28614step0Labels = mixedMoment B raw28614step1 raw28614step1Labels := by
      have ha : raw28614step1 = (fun i j => raw28614step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28614step1 raw28614step0; decide +kernel
      have hl : raw28614step1Labels = raw28614step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28614step0 raw28614step0Labels permutation149 permutation2
    mixedMoment B raw28614step1 raw28614step1Labels = mixedMoment B raw28614step2 raw28614step2Labels := by
      have ha : raw28614step2 = -raw28614step1 := by apply Matrix.ext; change ∀ i j, raw28614step2 i j = -(raw28614step1 i j); unfold raw28614step2 raw28614step1; decide +kernel
      have hl : raw28614step2Labels = raw28614step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node943 node943Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical224
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28728 raw28728Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw28728 raw28728Labels = mixedMoment B raw28728step0 raw28728step0Labels := by
      have hz : ∀ j, raw28728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28728step0 = (fun i j => raw28728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28728step0 raw28728; decide +kernel
      have hl : raw28728step0Labels = raw28728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28728 raw28728Labels permutation346 hz
    mixedMoment B raw28728step0 raw28728step0Labels = mixedMoment B raw28728step1 raw28728step1Labels := by
      have ha : raw28728step1 = (fun i j => raw28728step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28728step1 raw28728step0; decide +kernel
      have hl : raw28728step1Labels = raw28728step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28728step0 raw28728step0Labels permutation149 permutation7
    mixedMoment B raw28728step1 raw28728step1Labels = mixedMoment B raw28728step2 raw28728step2Labels := by
      have ha : raw28728step2 = raw28728step1 := by apply Matrix.ext; unfold raw28728step2 raw28728step1; decide +kernel
      have hl : raw28728step1Labels = labelEmbedding1 ∘ raw28728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28728step1 raw28728step1Labels raw28728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical28729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28729 raw28729Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw28729 raw28729Labels = mixedMoment B raw28729step0 raw28729step0Labels := by
      have ha : raw28729step0 = (fun i j => raw28729 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28729step0 raw28729; decide +kernel
      have hl : raw28729step0Labels = raw28729Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28729 raw28729Labels permutation674 permutation7
    mixedMoment B raw28729step0 raw28729step0Labels = mixedMoment B raw28729step1 raw28729step1Labels := by
      have ha : raw28729step1 = raw28729step0 := by apply Matrix.ext; unfold raw28729step1 raw28729step0; decide +kernel
      have hl : raw28729step0Labels = labelEmbedding1 ∘ raw28729step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28729step0 raw28729step0Labels raw28729step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

theorem canonical28730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28730 raw28730Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw28730 raw28730Labels = mixedMoment B raw28730step0 raw28730step0Labels := by
      have hz : ∀ j, raw28730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28730step0 = (fun i j => raw28730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28730step0 raw28730; decide +kernel
      have hl : raw28730step0Labels = raw28730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28730 raw28730Labels permutation346 hz
    mixedMoment B raw28730step0 raw28730step0Labels = mixedMoment B raw28730step1 raw28730step1Labels := by
      have ha : raw28730step1 = (fun i j => raw28730step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28730step1 raw28730step0; decide +kernel
      have hl : raw28730step1Labels = raw28730step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28730step0 raw28730step0Labels permutation149 permutation7
    mixedMoment B raw28730step1 raw28730step1Labels = mixedMoment B raw28730step2 raw28730step2Labels := by
      have ha : raw28730step2 = raw28730step1 := by apply Matrix.ext; unfold raw28730step2 raw28730step1; decide +kernel
      have hl : raw28730step1Labels = labelEmbedding1 ∘ raw28730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28730step1 raw28730step1Labels raw28730step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

theorem canonical28731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28731 raw28731Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw28731 raw28731Labels = mixedMoment B raw28731step0 raw28731step0Labels := by
      have hz : ∀ j, raw28731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28731step0 = (fun i j => raw28731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28731step0 raw28731; decide +kernel
      have hl : raw28731step0Labels = raw28731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28731 raw28731Labels permutation346 hz
    mixedMoment B raw28731step0 raw28731step0Labels = mixedMoment B raw28731step1 raw28731step1Labels := by
      have ha : raw28731step1 = (fun i j => raw28731step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28731step1 raw28731step0; decide +kernel
      have hl : raw28731step1Labels = raw28731step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28731step0 raw28731step0Labels permutation149 permutation7
    mixedMoment B raw28731step1 raw28731step1Labels = mixedMoment B raw28731step2 raw28731step2Labels := by
      have ha : raw28731step2 = raw28731step1 := by apply Matrix.ext; unfold raw28731step2 raw28731step1; decide +kernel
      have hl : raw28731step1Labels = labelEmbedding1 ∘ raw28731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28731step1 raw28731step1Labels raw28731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical28732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28732 raw28732Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw28732 raw28732Labels = mixedMoment B raw28732step0 raw28732step0Labels := by
      have hz : ∀ j, raw28732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28732step0 = (fun i j => raw28732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28732step0 raw28732; decide +kernel
      have hl : raw28732step0Labels = raw28732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28732 raw28732Labels permutation346 hz
    mixedMoment B raw28732step0 raw28732step0Labels = mixedMoment B raw28732step1 raw28732step1Labels := by
      have ha : raw28732step1 = (fun i j => raw28732step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28732step1 raw28732step0; decide +kernel
      have hl : raw28732step1Labels = raw28732step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28732step0 raw28732step0Labels permutation149 permutation7
    mixedMoment B raw28732step1 raw28732step1Labels = mixedMoment B raw28732step2 raw28732step2Labels := by
      have ha : raw28732step2 = raw28732step1 := by apply Matrix.ext; unfold raw28732step2 raw28732step1; decide +kernel
      have hl : raw28732step1Labels = labelEmbedding1 ∘ raw28732step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28732step1 raw28732step1Labels raw28732step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical28733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28733 raw28733Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw28733 raw28733Labels = mixedMoment B raw28733step0 raw28733step0Labels := by
      have hz : ∀ j, raw28733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28733step0 = (fun i j => raw28733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28733step0 raw28733; decide +kernel
      have hl : raw28733step0Labels = raw28733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28733 raw28733Labels permutation346 hz
    mixedMoment B raw28733step0 raw28733step0Labels = mixedMoment B raw28733step1 raw28733step1Labels := by
      have hz : ∀ j, raw28733step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw28733step1 = (fun i j => raw28733step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw28733step1 raw28733step0; decide +kernel
      have hl : raw28733step1Labels = raw28733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28733step0 raw28733step0Labels permutation56 hz
    mixedMoment B raw28733step1 raw28733step1Labels = mixedMoment B raw28733step2 raw28733step2Labels := by
      have ha : raw28733step2 = (fun i j => raw28733step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28733step2 raw28733step1; decide +kernel
      have hl : raw28733step2Labels = raw28733step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28733step1 raw28733step1Labels permutation8 permutation7
    mixedMoment B raw28733step2 raw28733step2Labels = mixedMoment B raw28733step3 raw28733step3Labels := by
      have ha : raw28733step3 = -raw28733step2 := by apply Matrix.ext; change ∀ i j, raw28733step3 i j = -(raw28733step2 i j); unfold raw28733step3 raw28733step2; decide +kernel
      have hl : raw28733step3Labels = raw28733step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28733step3 raw28733step3Labels = mixedMoment B raw28733step4 raw28733step4Labels := by
      have ha : raw28733step4 = raw28733step3 := by apply Matrix.ext; unfold raw28733step4 raw28733step3; decide +kernel
      have hl : raw28733step3Labels = labelEmbedding1 ∘ raw28733step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28733step3 raw28733step3Labels raw28733step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical28734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28734 raw28734Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw28734 raw28734Labels = mixedMoment B raw28734step0 raw28734step0Labels := by
      have ha : raw28734step0 = (fun i j => raw28734 (permutation680 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28734step0 raw28734; decide +kernel
      have hl : raw28734step0Labels = raw28734Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28734 raw28734Labels permutation680 permutation7
    mixedMoment B raw28734step0 raw28734step0Labels = mixedMoment B raw28734step1 raw28734step1Labels := by
      have ha : raw28734step1 = raw28734step0 := by apply Matrix.ext; unfold raw28734step1 raw28734step0; decide +kernel
      have hl : raw28734step0Labels = labelEmbedding1 ∘ raw28734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28734step0 raw28734step0Labels raw28734step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

theorem canonical28735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28735 raw28735Labels = mixedMoment B node3449 node3449Labels := by
  calc
    mixedMoment B raw28735 raw28735Labels = mixedMoment B raw28735step0 raw28735step0Labels := by
      have ha : raw28735step0 = (fun i j => raw28735 (permutation680 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28735step0 raw28735; decide +kernel
      have hl : raw28735step0Labels = raw28735Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28735 raw28735Labels permutation680 permutation7
    mixedMoment B raw28735step0 raw28735step0Labels = mixedMoment B raw28735step1 raw28735step1Labels := by
      have ha : raw28735step1 = raw28735step0 := by apply Matrix.ext; unfold raw28735step1 raw28735step0; decide +kernel
      have hl : raw28735step0Labels = labelEmbedding1 ∘ raw28735step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28735step0 raw28735step0Labels raw28735step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3449 node3449Labels := by rfl

theorem canonical28736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28736 raw28736Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw28736 raw28736Labels = mixedMoment B raw28736step0 raw28736step0Labels := by
      have ha : raw28736step0 = (fun i j => raw28736 (permutation680 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28736step0 raw28736; decide +kernel
      have hl : raw28736step0Labels = raw28736Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28736 raw28736Labels permutation680 permutation7
    mixedMoment B raw28736step0 raw28736step0Labels = mixedMoment B raw28736step1 raw28736step1Labels := by
      have ha : raw28736step1 = raw28736step0 := by apply Matrix.ext; unfold raw28736step1 raw28736step0; decide +kernel
      have hl : raw28736step0Labels = labelEmbedding1 ∘ raw28736step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28736step0 raw28736step0Labels raw28736step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3513 node3513Labels := by rfl

theorem canonical28737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28737 raw28737Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw28737 raw28737Labels = mixedMoment B raw28737step0 raw28737step0Labels := by
      have ha : raw28737step0 = (fun i j => raw28737 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28737step0 raw28737; decide +kernel
      have hl : raw28737step0Labels = raw28737Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28737 raw28737Labels permutation200 permutation7
    mixedMoment B raw28737step0 raw28737step0Labels = mixedMoment B raw28737step1 raw28737step1Labels := by
      have ha : raw28737step1 = -raw28737step0 := by apply Matrix.ext; change ∀ i j, raw28737step1 i j = -(raw28737step0 i j); unfold raw28737step1 raw28737step0; decide +kernel
      have hl : raw28737step1Labels = raw28737step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28737step1 raw28737step1Labels = mixedMoment B raw28737step2 raw28737step2Labels := by
      have ha : raw28737step2 = raw28737step1 := by apply Matrix.ext; unfold raw28737step2 raw28737step1; decide +kernel
      have hl : raw28737step1Labels = labelEmbedding1 ∘ raw28737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28737step1 raw28737step1Labels raw28737step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical28738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28738 raw28738Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw28738 raw28738Labels = mixedMoment B raw28738step0 raw28738step0Labels := by
      have hz : ∀ j, raw28738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28738step0 = (fun i j => raw28738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28738step0 raw28738; decide +kernel
      have hl : raw28738step0Labels = raw28738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28738 raw28738Labels permutation346 hz
    mixedMoment B raw28738step0 raw28738step0Labels = mixedMoment B raw28738step1 raw28738step1Labels := by
      have ha : raw28738step1 = (fun i j => raw28738step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28738step1 raw28738step0; decide +kernel
      have hl : raw28738step1Labels = raw28738step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28738step0 raw28738step0Labels permutation149 permutation7
    mixedMoment B raw28738step1 raw28738step1Labels = mixedMoment B raw28738step2 raw28738step2Labels := by
      have ha : raw28738step2 = raw28738step1 := by apply Matrix.ext; unfold raw28738step2 raw28738step1; decide +kernel
      have hl : raw28738step1Labels = labelEmbedding1 ∘ raw28738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28738step1 raw28738step1Labels raw28738step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

theorem canonical28739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28739 raw28739Labels = mixedMoment B node3458 node3458Labels := by
  calc
    mixedMoment B raw28739 raw28739Labels = mixedMoment B raw28739step0 raw28739step0Labels := by
      have ha : raw28739step0 = (fun i j => raw28739 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28739step0 raw28739; decide +kernel
      have hl : raw28739step0Labels = raw28739Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28739 raw28739Labels permutation674 permutation7
    mixedMoment B raw28739step0 raw28739step0Labels = mixedMoment B raw28739step1 raw28739step1Labels := by
      have ha : raw28739step1 = raw28739step0 := by apply Matrix.ext; unfold raw28739step1 raw28739step0; decide +kernel
      have hl : raw28739step0Labels = labelEmbedding1 ∘ raw28739step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28739step0 raw28739step0Labels raw28739step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3458 node3458Labels := by rfl

theorem canonical28740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28740 raw28740Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw28740 raw28740Labels = mixedMoment B raw28740step0 raw28740step0Labels := by
      have hz : ∀ j, raw28740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28740step0 = (fun i j => raw28740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28740step0 raw28740; decide +kernel
      have hl : raw28740step0Labels = raw28740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28740 raw28740Labels permutation346 hz
    mixedMoment B raw28740step0 raw28740step0Labels = mixedMoment B raw28740step1 raw28740step1Labels := by
      have ha : raw28740step1 = (fun i j => raw28740step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28740step1 raw28740step0; decide +kernel
      have hl : raw28740step1Labels = raw28740step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28740step0 raw28740step0Labels permutation149 permutation7
    mixedMoment B raw28740step1 raw28740step1Labels = mixedMoment B raw28740step2 raw28740step2Labels := by
      have ha : raw28740step2 = raw28740step1 := by apply Matrix.ext; unfold raw28740step2 raw28740step1; decide +kernel
      have hl : raw28740step1Labels = labelEmbedding1 ∘ raw28740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28740step1 raw28740step1Labels raw28740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical28741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28741 raw28741Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw28741 raw28741Labels = mixedMoment B raw28741step0 raw28741step0Labels := by
      have hz : ∀ j, raw28741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28741step0 = (fun i j => raw28741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28741step0 raw28741; decide +kernel
      have hl : raw28741step0Labels = raw28741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28741 raw28741Labels permutation346 hz
    mixedMoment B raw28741step0 raw28741step0Labels = mixedMoment B raw28741step1 raw28741step1Labels := by
      have ha : raw28741step1 = (fun i j => raw28741step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28741step1 raw28741step0; decide +kernel
      have hl : raw28741step1Labels = raw28741step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28741step0 raw28741step0Labels permutation38 permutation7
    mixedMoment B raw28741step1 raw28741step1Labels = mixedMoment B raw28741step2 raw28741step2Labels := by
      have ha : raw28741step2 = -raw28741step1 := by apply Matrix.ext; change ∀ i j, raw28741step2 i j = -(raw28741step1 i j); unfold raw28741step2 raw28741step1; decide +kernel
      have hl : raw28741step2Labels = raw28741step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28741step2 raw28741step2Labels = mixedMoment B raw28741step3 raw28741step3Labels := by
      have ha : raw28741step3 = raw28741step2 := by apply Matrix.ext; unfold raw28741step3 raw28741step2; decide +kernel
      have hl : raw28741step2Labels = labelEmbedding1 ∘ raw28741step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28741step2 raw28741step2Labels raw28741step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical28742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28742 raw28742Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw28742 raw28742Labels = mixedMoment B raw28742step0 raw28742step0Labels := by
      have hz : ∀ j, raw28742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28742step0 = (fun i j => raw28742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28742step0 raw28742; decide +kernel
      have hl : raw28742step0Labels = raw28742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28742 raw28742Labels permutation346 hz
    mixedMoment B raw28742step0 raw28742step0Labels = mixedMoment B raw28742step1 raw28742step1Labels := by
      have ha : raw28742step1 = (fun i j => raw28742step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28742step1 raw28742step0; decide +kernel
      have hl : raw28742step1Labels = raw28742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28742step0 raw28742step0Labels permutation149 permutation7
    mixedMoment B raw28742step1 raw28742step1Labels = mixedMoment B raw28742step2 raw28742step2Labels := by
      have ha : raw28742step2 = raw28742step1 := by apply Matrix.ext; unfold raw28742step2 raw28742step1; decide +kernel
      have hl : raw28742step1Labels = labelEmbedding1 ∘ raw28742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28742step1 raw28742step1Labels raw28742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

theorem canonical28743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28743 raw28743Labels = mixedMoment B node3403 node3403Labels := by
  calc
    mixedMoment B raw28743 raw28743Labels = mixedMoment B raw28743step0 raw28743step0Labels := by
      have ha : raw28743step0 = (fun i j => raw28743 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28743step0 raw28743; decide +kernel
      have hl : raw28743step0Labels = raw28743Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28743 raw28743Labels permutation674 permutation7
    mixedMoment B raw28743step0 raw28743step0Labels = mixedMoment B raw28743step1 raw28743step1Labels := by
      have ha : raw28743step1 = raw28743step0 := by apply Matrix.ext; unfold raw28743step1 raw28743step0; decide +kernel
      have hl : raw28743step0Labels = labelEmbedding1 ∘ raw28743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28743step0 raw28743step0Labels raw28743step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3403 node3403Labels := by rfl

theorem canonical28744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28744 raw28744Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw28744 raw28744Labels = mixedMoment B raw28744step0 raw28744step0Labels := by
      have hz : ∀ j, raw28744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28744step0 = (fun i j => raw28744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28744step0 raw28744; decide +kernel
      have hl : raw28744step0Labels = raw28744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28744 raw28744Labels permutation346 hz
    mixedMoment B raw28744step0 raw28744step0Labels = mixedMoment B raw28744step1 raw28744step1Labels := by
      have ha : raw28744step1 = (fun i j => raw28744step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28744step1 raw28744step0; decide +kernel
      have hl : raw28744step1Labels = raw28744step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28744step0 raw28744step0Labels permutation149 permutation7
    mixedMoment B raw28744step1 raw28744step1Labels = mixedMoment B raw28744step2 raw28744step2Labels := by
      have ha : raw28744step2 = raw28744step1 := by apply Matrix.ext; unfold raw28744step2 raw28744step1; decide +kernel
      have hl : raw28744step1Labels = labelEmbedding1 ∘ raw28744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28744step1 raw28744step1Labels raw28744step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

theorem canonical28745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28745 raw28745Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw28745 raw28745Labels = mixedMoment B raw28745step0 raw28745step0Labels := by
      have hz : ∀ j, raw28745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28745step0 = (fun i j => raw28745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28745step0 raw28745; decide +kernel
      have hl : raw28745step0Labels = raw28745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28745 raw28745Labels permutation346 hz
    mixedMoment B raw28745step0 raw28745step0Labels = mixedMoment B raw28745step1 raw28745step1Labels := by
      have ha : raw28745step1 = (fun i j => raw28745step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28745step1 raw28745step0; decide +kernel
      have hl : raw28745step1Labels = raw28745step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28745step0 raw28745step0Labels permutation38 permutation7
    mixedMoment B raw28745step1 raw28745step1Labels = mixedMoment B raw28745step2 raw28745step2Labels := by
      have ha : raw28745step2 = -raw28745step1 := by apply Matrix.ext; change ∀ i j, raw28745step2 i j = -(raw28745step1 i j); unfold raw28745step2 raw28745step1; decide +kernel
      have hl : raw28745step2Labels = raw28745step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28745step2 raw28745step2Labels = mixedMoment B raw28745step3 raw28745step3Labels := by
      have ha : raw28745step3 = raw28745step2 := by apply Matrix.ext; unfold raw28745step3 raw28745step2; decide +kernel
      have hl : raw28745step2Labels = labelEmbedding1 ∘ raw28745step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28745step2 raw28745step2Labels raw28745step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical28746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28746 raw28746Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw28746 raw28746Labels = mixedMoment B raw28746step0 raw28746step0Labels := by
      have hz : ∀ j, raw28746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28746step0 = (fun i j => raw28746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28746step0 raw28746; decide +kernel
      have hl : raw28746step0Labels = raw28746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28746 raw28746Labels permutation346 hz
    mixedMoment B raw28746step0 raw28746step0Labels = mixedMoment B raw28746step1 raw28746step1Labels := by
      have ha : raw28746step1 = (fun i j => raw28746step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28746step1 raw28746step0; decide +kernel
      have hl : raw28746step1Labels = raw28746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28746step0 raw28746step0Labels permutation149 permutation7
    mixedMoment B raw28746step1 raw28746step1Labels = mixedMoment B raw28746step2 raw28746step2Labels := by
      have ha : raw28746step2 = raw28746step1 := by apply Matrix.ext; unfold raw28746step2 raw28746step1; decide +kernel
      have hl : raw28746step1Labels = labelEmbedding1 ∘ raw28746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28746step1 raw28746step1Labels raw28746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

theorem canonical28747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28747 raw28747Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw28747 raw28747Labels = mixedMoment B raw28747step0 raw28747step0Labels := by
      have ha : raw28747step0 = (fun i j => raw28747 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28747step0 raw28747; decide +kernel
      have hl : raw28747step0Labels = raw28747Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28747 raw28747Labels permutation674 permutation7
    mixedMoment B raw28747step0 raw28747step0Labels = mixedMoment B raw28747step1 raw28747step1Labels := by
      have ha : raw28747step1 = raw28747step0 := by apply Matrix.ext; unfold raw28747step1 raw28747step0; decide +kernel
      have hl : raw28747step0Labels = labelEmbedding1 ∘ raw28747step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28747step0 raw28747step0Labels raw28747step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3255 node3255Labels := by rfl

theorem canonical28748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28748 raw28748Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw28748 raw28748Labels = mixedMoment B raw28748step0 raw28748step0Labels := by
      have hz : ∀ j, raw28748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28748step0 = (fun i j => raw28748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28748step0 raw28748; decide +kernel
      have hl : raw28748step0Labels = raw28748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28748 raw28748Labels permutation346 hz
    mixedMoment B raw28748step0 raw28748step0Labels = mixedMoment B raw28748step1 raw28748step1Labels := by
      have ha : raw28748step1 = (fun i j => raw28748step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28748step1 raw28748step0; decide +kernel
      have hl : raw28748step1Labels = raw28748step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28748step0 raw28748step0Labels permutation149 permutation7
    mixedMoment B raw28748step1 raw28748step1Labels = mixedMoment B raw28748step2 raw28748step2Labels := by
      have ha : raw28748step2 = raw28748step1 := by apply Matrix.ext; unfold raw28748step2 raw28748step1; decide +kernel
      have hl : raw28748step1Labels = labelEmbedding1 ∘ raw28748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28748step1 raw28748step1Labels raw28748step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

theorem canonical28749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28749 raw28749Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw28749 raw28749Labels = mixedMoment B raw28749step0 raw28749step0Labels := by
      have hz : ∀ j, raw28749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28749step0 = (fun i j => raw28749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28749step0 raw28749; decide +kernel
      have hl : raw28749step0Labels = raw28749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28749 raw28749Labels permutation346 hz
    mixedMoment B raw28749step0 raw28749step0Labels = mixedMoment B raw28749step1 raw28749step1Labels := by
      have ha : raw28749step1 = (fun i j => raw28749step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28749step1 raw28749step0; decide +kernel
      have hl : raw28749step1Labels = raw28749step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28749step0 raw28749step0Labels permutation149 permutation7
    mixedMoment B raw28749step1 raw28749step1Labels = mixedMoment B raw28749step2 raw28749step2Labels := by
      have ha : raw28749step2 = raw28749step1 := by apply Matrix.ext; unfold raw28749step2 raw28749step1; decide +kernel
      have hl : raw28749step1Labels = labelEmbedding1 ∘ raw28749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28749step1 raw28749step1Labels raw28749step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5131 raw5131Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw5131 raw5131Labels = mixedMoment B raw5131step0 raw5131step0Labels := by
      have hz : ∀ j, raw5131 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5131step0 = (fun i j => raw5131 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5131step0 raw5131; decide +kernel
      have hl : raw5131step0Labels = raw5131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5131 raw5131Labels permutation434 hz
    mixedMoment B raw5131step0 raw5131step0Labels = mixedMoment B raw5131step1 raw5131step1Labels := by
      have hz : ∀ j, raw5131step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5131step1 = (fun i j => raw5131step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5131step1 raw5131step0; decide +kernel
      have hl : raw5131step1Labels = raw5131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5131step0 raw5131step0Labels permutation80 hz
    mixedMoment B raw5131step1 raw5131step1Labels = mixedMoment B raw5131step2 raw5131step2Labels := by
      have ha : raw5131step2 = (fun i j => raw5131step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5131step2 raw5131step1; decide +kernel
      have hl : raw5131step2Labels = raw5131step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5131step1 raw5131step1Labels permutation29 permutation7
    mixedMoment B raw5131step2 raw5131step2Labels = mixedMoment B raw5131step3 raw5131step3Labels := by
      have ha : raw5131step3 = raw5131step2 := by apply Matrix.ext; unfold raw5131step3 raw5131step2; decide +kernel
      have hl : raw5131step2Labels = labelEmbedding1 ∘ raw5131step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5131step2 raw5131step2Labels raw5131step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical5142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5142 raw5142Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5142 raw5142Labels = mixedMoment B raw5142step0 raw5142step0Labels := by
      have hz : ∀ j, raw5142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5142step0 = (fun i j => raw5142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5142step0 raw5142; decide +kernel
      have hl : raw5142step0Labels = raw5142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5142 raw5142Labels permutation434 hz
    mixedMoment B raw5142step0 raw5142step0Labels = mixedMoment B raw5142step1 raw5142step1Labels := by
      have ha : raw5142step1 = (fun i j => raw5142step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5142step1 raw5142step0; decide +kernel
      have hl : raw5142step1Labels = raw5142step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5142step0 raw5142step0Labels permutation143 permutation7
    mixedMoment B raw5142step1 raw5142step1Labels = mixedMoment B raw5142step2 raw5142step2Labels := by
      have ha : raw5142step2 = raw5142step1 := by apply Matrix.ext; unfold raw5142step2 raw5142step1; decide +kernel
      have hl : raw5142step1Labels = labelEmbedding1 ∘ raw5142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5142step1 raw5142step1Labels raw5142step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical5147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5147 raw5147Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5147 raw5147Labels = mixedMoment B raw5147step0 raw5147step0Labels := by
      have hz : ∀ j, raw5147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5147step0 = (fun i j => raw5147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5147step0 raw5147; decide +kernel
      have hl : raw5147step0Labels = raw5147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5147 raw5147Labels permutation346 hz
    mixedMoment B raw5147step0 raw5147step0Labels = mixedMoment B raw5147step1 raw5147step1Labels := by
      have ha : raw5147step1 = (fun i j => raw5147step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5147step1 raw5147step0; decide +kernel
      have hl : raw5147step1Labels = raw5147step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5147step0 raw5147step0Labels permutation143 permutation7
    mixedMoment B raw5147step1 raw5147step1Labels = mixedMoment B raw5147step2 raw5147step2Labels := by
      have ha : raw5147step2 = raw5147step1 := by apply Matrix.ext; unfold raw5147step2 raw5147step1; decide +kernel
      have hl : raw5147step1Labels = labelEmbedding1 ∘ raw5147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5147step1 raw5147step1Labels raw5147step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical5151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5151 raw5151Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw5151 raw5151Labels = mixedMoment B raw5151step0 raw5151step0Labels := by
      have hz : ∀ j, raw5151 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5151step0 = (fun i j => raw5151 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5151step0 raw5151; decide +kernel
      have hl : raw5151step0Labels = raw5151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151 raw5151Labels permutation434 hz
    mixedMoment B raw5151step0 raw5151step0Labels = mixedMoment B raw5151step1 raw5151step1Labels := by
      have hz : ∀ j, raw5151step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5151step1 = (fun i j => raw5151step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5151step1 raw5151step0; decide +kernel
      have hl : raw5151step1Labels = raw5151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151step0 raw5151step0Labels permutation80 hz
    mixedMoment B raw5151step1 raw5151step1Labels = mixedMoment B raw5151step2 raw5151step2Labels := by
      have hz : ∀ j, raw5151step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5151step2 = (fun i j => raw5151step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5151step2 raw5151step1; decide +kernel
      have hl : raw5151step2Labels = raw5151step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151step1 raw5151step1Labels permutation14 hz
    mixedMoment B raw5151step2 raw5151step2Labels = mixedMoment B raw5151step3 raw5151step3Labels := by
      have ha : raw5151step3 = (fun i j => raw5151step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5151step3 raw5151step2; decide +kernel
      have hl : raw5151step3Labels = raw5151step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5151step2 raw5151step2Labels permutation7 permutation7
    mixedMoment B raw5151step3 raw5151step3Labels = mixedMoment B raw5151step4 raw5151step4Labels := by
      have ha : raw5151step4 = raw5151step3 := by apply Matrix.ext; unfold raw5151step4 raw5151step3; decide +kernel
      have hl : raw5151step3Labels = labelEmbedding1 ∘ raw5151step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5151step3 raw5151step3Labels raw5151step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

theorem canonical5153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5153 raw5153Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw5153 raw5153Labels = mixedMoment B raw5153step0 raw5153step0Labels := by
      have hz : ∀ j, raw5153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5153step0 = (fun i j => raw5153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5153step0 raw5153; decide +kernel
      have hl : raw5153step0Labels = raw5153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5153 raw5153Labels permutation434 hz
    mixedMoment B raw5153step0 raw5153step0Labels = mixedMoment B raw5153step1 raw5153step1Labels := by
      have hz : ∀ j, raw5153step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5153step1 = (fun i j => raw5153step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5153step1 raw5153step0; decide +kernel
      have hl : raw5153step1Labels = raw5153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5153step0 raw5153step0Labels permutation56 hz
    mixedMoment B raw5153step1 raw5153step1Labels = mixedMoment B raw5153step2 raw5153step2Labels := by
      have ha : raw5153step2 = (fun i j => raw5153step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5153step2 raw5153step1; decide +kernel
      have hl : raw5153step2Labels = raw5153step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5153step1 raw5153step1Labels permutation29 permutation7
    mixedMoment B raw5153step2 raw5153step2Labels = mixedMoment B raw5153step3 raw5153step3Labels := by
      have ha : raw5153step3 = raw5153step2 := by apply Matrix.ext; unfold raw5153step3 raw5153step2; decide +kernel
      have hl : raw5153step2Labels = labelEmbedding1 ∘ raw5153step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5153step2 raw5153step2Labels raw5153step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical5154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5154 raw5154Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw5154 raw5154Labels = mixedMoment B raw5154step0 raw5154step0Labels := by
      have hz : ∀ j, raw5154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5154step0 = (fun i j => raw5154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5154step0 raw5154; decide +kernel
      have hl : raw5154step0Labels = raw5154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5154 raw5154Labels permutation346 hz
    mixedMoment B raw5154step0 raw5154step0Labels = mixedMoment B raw5154step1 raw5154step1Labels := by
      have hz : ∀ j, raw5154step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5154step1 = (fun i j => raw5154step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5154step1 raw5154step0; decide +kernel
      have hl : raw5154step1Labels = raw5154step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5154step0 raw5154step0Labels permutation56 hz
    mixedMoment B raw5154step1 raw5154step1Labels = mixedMoment B raw5154step2 raw5154step2Labels := by
      have ha : raw5154step2 = (fun i j => raw5154step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5154step2 raw5154step1; decide +kernel
      have hl : raw5154step2Labels = raw5154step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5154step1 raw5154step1Labels permutation29 permutation7
    mixedMoment B raw5154step2 raw5154step2Labels = mixedMoment B raw5154step3 raw5154step3Labels := by
      have ha : raw5154step3 = raw5154step2 := by apply Matrix.ext; unfold raw5154step3 raw5154step2; decide +kernel
      have hl : raw5154step2Labels = labelEmbedding1 ∘ raw5154step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5154step2 raw5154step2Labels raw5154step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical5155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5155 raw5155Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw5155 raw5155Labels = mixedMoment B raw5155step0 raw5155step0Labels := by
      have hz : ∀ j, raw5155 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5155step0 = (fun i j => raw5155 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5155step0 raw5155; decide +kernel
      have hl : raw5155step0Labels = raw5155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5155 raw5155Labels permutation434 hz
    mixedMoment B raw5155step0 raw5155step0Labels = mixedMoment B raw5155step1 raw5155step1Labels := by
      have hz : ∀ j, raw5155step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5155step1 = (fun i j => raw5155step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5155step1 raw5155step0; decide +kernel
      have hl : raw5155step1Labels = raw5155step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5155step0 raw5155step0Labels permutation80 hz
    mixedMoment B raw5155step1 raw5155step1Labels = mixedMoment B raw5155step2 raw5155step2Labels := by
      have hz : ∀ j, raw5155step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5155step2 = (fun i j => raw5155step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5155step2 raw5155step1; decide +kernel
      have hl : raw5155step2Labels = raw5155step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5155step1 raw5155step1Labels permutation14 hz
    mixedMoment B raw5155step2 raw5155step2Labels = mixedMoment B raw5155step3 raw5155step3Labels := by
      have ha : raw5155step3 = (fun i j => raw5155step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5155step3 raw5155step2; decide +kernel
      have hl : raw5155step3Labels = raw5155step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5155step2 raw5155step2Labels permutation7 permutation7
    mixedMoment B raw5155step3 raw5155step3Labels = mixedMoment B raw5155step4 raw5155step4Labels := by
      have ha : raw5155step4 = raw5155step3 := by apply Matrix.ext; unfold raw5155step4 raw5155step3; decide +kernel
      have hl : raw5155step3Labels = labelEmbedding1 ∘ raw5155step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5155step3 raw5155step3Labels raw5155step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical5157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5157 raw5157Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw5157 raw5157Labels = mixedMoment B raw5157step0 raw5157step0Labels := by
      have hz : ∀ j, raw5157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5157step0 = (fun i j => raw5157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5157step0 raw5157; decide +kernel
      have hl : raw5157step0Labels = raw5157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5157 raw5157Labels permutation434 hz
    mixedMoment B raw5157step0 raw5157step0Labels = mixedMoment B raw5157step1 raw5157step1Labels := by
      have hz : ∀ j, raw5157step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5157step1 = (fun i j => raw5157step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5157step1 raw5157step0; decide +kernel
      have hl : raw5157step1Labels = raw5157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5157step0 raw5157step0Labels permutation80 hz
    mixedMoment B raw5157step1 raw5157step1Labels = mixedMoment B raw5157step2 raw5157step2Labels := by
      have ha : raw5157step2 = (fun i j => raw5157step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5157step2 raw5157step1; decide +kernel
      have hl : raw5157step2Labels = raw5157step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5157step1 raw5157step1Labels permutation29 permutation7
    mixedMoment B raw5157step2 raw5157step2Labels = mixedMoment B raw5157step3 raw5157step3Labels := by
      have ha : raw5157step3 = raw5157step2 := by apply Matrix.ext; unfold raw5157step3 raw5157step2; decide +kernel
      have hl : raw5157step2Labels = labelEmbedding1 ∘ raw5157step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5157step2 raw5157step2Labels raw5157step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical5167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5167 raw5167Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5167 raw5167Labels = mixedMoment B raw5167step0 raw5167step0Labels := by
      have hz : ∀ j, raw5167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5167step0 = (fun i j => raw5167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5167step0 raw5167; decide +kernel
      have hl : raw5167step0Labels = raw5167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5167 raw5167Labels permutation434 hz
    mixedMoment B raw5167step0 raw5167step0Labels = mixedMoment B raw5167step1 raw5167step1Labels := by
      have hz : ∀ j, raw5167step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5167step1 = (fun i j => raw5167step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5167step1 raw5167step0; decide +kernel
      have hl : raw5167step1Labels = raw5167step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5167step0 raw5167step0Labels permutation80 hz
    mixedMoment B raw5167step1 raw5167step1Labels = mixedMoment B raw5167step2 raw5167step2Labels := by
      have hz : ∀ j, raw5167step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5167step2 = (fun i j => raw5167step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5167step2 raw5167step1; decide +kernel
      have hl : raw5167step2Labels = raw5167step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5167step1 raw5167step1Labels permutation14 hz
    mixedMoment B raw5167step2 raw5167step2Labels = mixedMoment B raw5167step3 raw5167step3Labels := by
      have ha : raw5167step3 = (fun i j => raw5167step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5167step3 raw5167step2; decide +kernel
      have hl : raw5167step3Labels = raw5167step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5167step2 raw5167step2Labels permutation7 permutation0
    mixedMoment B raw5167step3 raw5167step3Labels = mixedMoment B raw5167step4 raw5167step4Labels := by
      have ha : raw5167step4 = -raw5167step3 := by apply Matrix.ext; change ∀ i j, raw5167step4 i j = -(raw5167step3 i j); unfold raw5167step4 raw5167step3; decide +kernel
      have hl : raw5167step4Labels = raw5167step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical5173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5173 raw5173Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw5173 raw5173Labels = mixedMoment B raw5173step0 raw5173step0Labels := by
      have hz : ∀ j, raw5173 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5173step0 = (fun i j => raw5173 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5173step0 raw5173; decide +kernel
      have hl : raw5173step0Labels = raw5173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5173 raw5173Labels permutation434 hz
    mixedMoment B raw5173step0 raw5173step0Labels = mixedMoment B raw5173step1 raw5173step1Labels := by
      have ha : raw5173step1 = (fun i j => raw5173step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5173step1 raw5173step0; decide +kernel
      have hl : raw5173step1Labels = raw5173step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5173step0 raw5173step0Labels permutation145 permutation2
    mixedMoment B raw5173step1 raw5173step1Labels = mixedMoment B raw5173step2 raw5173step2Labels := by
      have ha : raw5173step2 = -raw5173step1 := by apply Matrix.ext; change ∀ i j, raw5173step2 i j = -(raw5173step1 i j); unfold raw5173step2 raw5173step1; decide +kernel
      have hl : raw5173step2Labels = raw5173step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical5175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5175 raw5175Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw5175 raw5175Labels = mixedMoment B raw5175step0 raw5175step0Labels := by
      have hz : ∀ j, raw5175 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5175step0 = (fun i j => raw5175 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5175step0 raw5175; decide +kernel
      have hl : raw5175step0Labels = raw5175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5175 raw5175Labels permutation434 hz
    mixedMoment B raw5175step0 raw5175step0Labels = mixedMoment B raw5175step1 raw5175step1Labels := by
      have hz : ∀ j, raw5175step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5175step1 = (fun i j => raw5175step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5175step1 raw5175step0; decide +kernel
      have hl : raw5175step1Labels = raw5175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5175step0 raw5175step0Labels permutation80 hz
    mixedMoment B raw5175step1 raw5175step1Labels = mixedMoment B raw5175step2 raw5175step2Labels := by
      have ha : raw5175step2 = (fun i j => raw5175step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5175step2 raw5175step1; decide +kernel
      have hl : raw5175step2Labels = raw5175step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5175step1 raw5175step1Labels permutation31 permutation2
    mixedMoment B raw5175step2 raw5175step2Labels = mixedMoment B raw5175step3 raw5175step3Labels := by
      have ha : raw5175step3 = -raw5175step2 := by apply Matrix.ext; change ∀ i j, raw5175step3 i j = -(raw5175step2 i j); unfold raw5175step3 raw5175step2; decide +kernel
      have hl : raw5175step3Labels = raw5175step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical5177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5177 raw5177Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw5177 raw5177Labels = mixedMoment B raw5177step0 raw5177step0Labels := by
      have hz : ∀ j, raw5177 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5177step0 = (fun i j => raw5177 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5177step0 raw5177; decide +kernel
      have hl : raw5177step0Labels = raw5177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5177 raw5177Labels permutation434 hz
    mixedMoment B raw5177step0 raw5177step0Labels = mixedMoment B raw5177step1 raw5177step1Labels := by
      have hz : ∀ j, raw5177step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5177step1 = (fun i j => raw5177step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5177step1 raw5177step0; decide +kernel
      have hl : raw5177step1Labels = raw5177step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5177step0 raw5177step0Labels permutation56 hz
    mixedMoment B raw5177step1 raw5177step1Labels = mixedMoment B raw5177step2 raw5177step2Labels := by
      have ha : raw5177step2 = (fun i j => raw5177step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5177step2 raw5177step1; decide +kernel
      have hl : raw5177step2Labels = raw5177step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5177step1 raw5177step1Labels permutation31 permutation2
    mixedMoment B raw5177step2 raw5177step2Labels = mixedMoment B raw5177step3 raw5177step3Labels := by
      have ha : raw5177step3 = -raw5177step2 := by apply Matrix.ext; change ∀ i j, raw5177step3 i j = -(raw5177step2 i j); unfold raw5177step3 raw5177step2; decide +kernel
      have hl : raw5177step3Labels = raw5177step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10290 raw10290Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw10290 raw10290Labels = mixedMoment B raw10290step0 raw10290step0Labels := by
      have hz : ∀ j, raw10290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10290step0 = (fun i j => raw10290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10290step0 raw10290; decide +kernel
      have hl : raw10290step0Labels = raw10290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10290 raw10290Labels permutation434 hz
    mixedMoment B raw10290step0 raw10290step0Labels = mixedMoment B raw10290step1 raw10290step1Labels := by
      have hz : ∀ j, raw10290step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10290step1 = (fun i j => raw10290step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10290step1 raw10290step0; decide +kernel
      have hl : raw10290step1Labels = raw10290step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10290step0 raw10290step0Labels permutation80 hz
    mixedMoment B raw10290step1 raw10290step1Labels = mixedMoment B raw10290step2 raw10290step2Labels := by
      have ha : raw10290step2 = (fun i j => raw10290step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10290step2 raw10290step1; decide +kernel
      have hl : raw10290step2Labels = raw10290step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10290step1 raw10290step1Labels permutation29 permutation7
    mixedMoment B raw10290step2 raw10290step2Labels = mixedMoment B raw10290step3 raw10290step3Labels := by
      have ha : raw10290step3 = raw10290step2 := by apply Matrix.ext; unfold raw10290step3 raw10290step2; decide +kernel
      have hl : raw10290step2Labels = labelEmbedding1 ∘ raw10290step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10290step2 raw10290step2Labels raw10290step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical10299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10299 raw10299Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10299 raw10299Labels = mixedMoment B raw10299step0 raw10299step0Labels := by
      have hz : ∀ j, raw10299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10299step0 = (fun i j => raw10299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10299step0 raw10299; decide +kernel
      have hl : raw10299step0Labels = raw10299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10299 raw10299Labels permutation434 hz
    mixedMoment B raw10299step0 raw10299step0Labels = mixedMoment B raw10299step1 raw10299step1Labels := by
      have ha : raw10299step1 = (fun i j => raw10299step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10299step1 raw10299step0; decide +kernel
      have hl : raw10299step1Labels = raw10299step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10299step0 raw10299step0Labels permutation143 permutation7
    mixedMoment B raw10299step1 raw10299step1Labels = mixedMoment B raw10299step2 raw10299step2Labels := by
      have ha : raw10299step2 = raw10299step1 := by apply Matrix.ext; unfold raw10299step2 raw10299step1; decide +kernel
      have hl : raw10299step1Labels = labelEmbedding1 ∘ raw10299step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10299step1 raw10299step1Labels raw10299step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical10303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10303 raw10303Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10303 raw10303Labels = mixedMoment B raw10303step0 raw10303step0Labels := by
      have hz : ∀ j, raw10303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10303step0 = (fun i j => raw10303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10303step0 raw10303; decide +kernel
      have hl : raw10303step0Labels = raw10303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10303 raw10303Labels permutation346 hz
    mixedMoment B raw10303step0 raw10303step0Labels = mixedMoment B raw10303step1 raw10303step1Labels := by
      have ha : raw10303step1 = (fun i j => raw10303step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10303step1 raw10303step0; decide +kernel
      have hl : raw10303step1Labels = raw10303step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10303step0 raw10303step0Labels permutation143 permutation7
    mixedMoment B raw10303step1 raw10303step1Labels = mixedMoment B raw10303step2 raw10303step2Labels := by
      have ha : raw10303step2 = raw10303step1 := by apply Matrix.ext; unfold raw10303step2 raw10303step1; decide +kernel
      have hl : raw10303step1Labels = labelEmbedding1 ∘ raw10303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10303step1 raw10303step1Labels raw10303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical10307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10307 raw10307Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw10307 raw10307Labels = mixedMoment B raw10307step0 raw10307step0Labels := by
      have hz : ∀ j, raw10307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10307step0 = (fun i j => raw10307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10307step0 raw10307; decide +kernel
      have hl : raw10307step0Labels = raw10307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10307 raw10307Labels permutation434 hz
    mixedMoment B raw10307step0 raw10307step0Labels = mixedMoment B raw10307step1 raw10307step1Labels := by
      have hz : ∀ j, raw10307step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10307step1 = (fun i j => raw10307step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10307step1 raw10307step0; decide +kernel
      have hl : raw10307step1Labels = raw10307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10307step0 raw10307step0Labels permutation80 hz
    mixedMoment B raw10307step1 raw10307step1Labels = mixedMoment B raw10307step2 raw10307step2Labels := by
      have ha : raw10307step2 = (fun i j => raw10307step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10307step2 raw10307step1; decide +kernel
      have hl : raw10307step2Labels = raw10307step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10307step1 raw10307step1Labels permutation29 permutation7
    mixedMoment B raw10307step2 raw10307step2Labels = mixedMoment B raw10307step3 raw10307step3Labels := by
      have ha : raw10307step3 = raw10307step2 := by apply Matrix.ext; unfold raw10307step3 raw10307step2; decide +kernel
      have hl : raw10307step2Labels = labelEmbedding1 ∘ raw10307step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10307step2 raw10307step2Labels raw10307step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical10311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10311 raw10311Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw10311 raw10311Labels = mixedMoment B raw10311step0 raw10311step0Labels := by
      have hz : ∀ j, raw10311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10311step0 = (fun i j => raw10311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10311step0 raw10311; decide +kernel
      have hl : raw10311step0Labels = raw10311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10311 raw10311Labels permutation434 hz
    mixedMoment B raw10311step0 raw10311step0Labels = mixedMoment B raw10311step1 raw10311step1Labels := by
      have hz : ∀ j, raw10311step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10311step1 = (fun i j => raw10311step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10311step1 raw10311step0; decide +kernel
      have hl : raw10311step1Labels = raw10311step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10311step0 raw10311step0Labels permutation80 hz
    mixedMoment B raw10311step1 raw10311step1Labels = mixedMoment B raw10311step2 raw10311step2Labels := by
      have hz : ∀ j, raw10311step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10311step2 = (fun i j => raw10311step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10311step2 raw10311step1; decide +kernel
      have hl : raw10311step2Labels = raw10311step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10311step1 raw10311step1Labels permutation14 hz
    mixedMoment B raw10311step2 raw10311step2Labels = mixedMoment B raw10311step3 raw10311step3Labels := by
      have ha : raw10311step3 = (fun i j => raw10311step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10311step3 raw10311step2; decide +kernel
      have hl : raw10311step3Labels = raw10311step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10311step2 raw10311step2Labels permutation7 permutation7
    mixedMoment B raw10311step3 raw10311step3Labels = mixedMoment B raw10311step4 raw10311step4Labels := by
      have ha : raw10311step4 = raw10311step3 := by apply Matrix.ext; unfold raw10311step4 raw10311step3; decide +kernel
      have hl : raw10311step3Labels = labelEmbedding1 ∘ raw10311step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10311step3 raw10311step3Labels raw10311step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node943 node943Labels = Sparse.eval nodeValue943 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 943) = mixedMoment B node943 node943Labels := rfl
  simpa [nodeValue943, Sparse.eval] using hc.symm

theorem sound952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node952 node952Labels = Sparse.eval nodeValue952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 952) = mixedMoment B node952 node952Labels := rfl
  simpa [nodeValue952, Sparse.eval] using hc.symm

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

theorem sound1157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1157 node1157Labels = Sparse.eval nodeValue1157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1157) = mixedMoment B node1157 node1157Labels := rfl
  simpa [nodeValue1157, Sparse.eval] using hc.symm

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

theorem sound1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1704 node1704Labels = Sparse.eval nodeValue1704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1704) = mixedMoment B node1704 node1704Labels := rfl
  simpa [nodeValue1704, Sparse.eval] using hc.symm

theorem sound1722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1722 node1722Labels = Sparse.eval nodeValue1722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1722) = mixedMoment B node1722 node1722Labels := rfl
  simpa [nodeValue1722, Sparse.eval] using hc.symm

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

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

theorem sound1823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1823 node1823Labels = Sparse.eval nodeValue1823 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1823) = mixedMoment B node1823 node1823Labels := rfl
  simpa [nodeValue1823, Sparse.eval] using hc.symm

theorem sound1830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1830 node1830Labels = Sparse.eval nodeValue1830 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1830) = mixedMoment B node1830 node1830Labels := rfl
  simpa [nodeValue1830, Sparse.eval] using hc.symm

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

theorem sound1972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1972 node1972Labels = Sparse.eval nodeValue1972 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1972) = mixedMoment B node1972 node1972Labels := rfl
  simpa [nodeValue1972, Sparse.eval] using hc.symm

theorem sound1978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1978 node1978Labels = Sparse.eval nodeValue1978 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1978) = mixedMoment B node1978 node1978Labels := rfl
  simpa [nodeValue1978, Sparse.eval] using hc.symm

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

theorem sound1993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1993 node1993Labels = Sparse.eval nodeValue1993 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1993) = mixedMoment B node1993 node1993Labels := rfl
  simpa [nodeValue1993, Sparse.eval] using hc.symm

theorem sound1997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1997 node1997Labels = Sparse.eval nodeValue1997 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1997) = mixedMoment B node1997 node1997Labels := rfl
  simpa [nodeValue1997, Sparse.eval] using hc.symm

theorem sound2008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2008 node2008Labels = Sparse.eval nodeValue2008 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2008) = mixedMoment B node2008 node2008Labels := rfl
  simpa [nodeValue2008, Sparse.eval] using hc.symm

theorem sound2011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2011 node2011Labels = Sparse.eval nodeValue2011 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2011) = mixedMoment B node2011 node2011Labels := rfl
  simpa [nodeValue2011, Sparse.eval] using hc.symm

theorem sound2016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2016 node2016Labels = Sparse.eval nodeValue2016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2016) = mixedMoment B node2016 node2016Labels := rfl
  simpa [nodeValue2016, Sparse.eval] using hc.symm

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

theorem sound2030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2030 node2030Labels = Sparse.eval nodeValue2030 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2030) = mixedMoment B node2030 node2030Labels := rfl
  simpa [nodeValue2030, Sparse.eval] using hc.symm

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

theorem sound2070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2070 node2070Labels = Sparse.eval nodeValue2070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2070) = mixedMoment B node2070 node2070Labels := rfl
  simpa [nodeValue2070, Sparse.eval] using hc.symm

theorem sound2072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2072 node2072Labels = Sparse.eval nodeValue2072 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2072) = mixedMoment B node2072 node2072Labels := rfl
  simpa [nodeValue2072, Sparse.eval] using hc.symm

theorem sound2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2075 node2075Labels = Sparse.eval nodeValue2075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2075) = mixedMoment B node2075 node2075Labels := rfl
  simpa [nodeValue2075, Sparse.eval] using hc.symm

theorem sound2085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2085 node2085Labels = Sparse.eval nodeValue2085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2085) = mixedMoment B node2085 node2085Labels := rfl
  simpa [nodeValue2085, Sparse.eval] using hc.symm

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

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

theorem sound2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2115 node2115Labels = Sparse.eval nodeValue2115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2115) = mixedMoment B node2115 node2115Labels := rfl
  simpa [nodeValue2115, Sparse.eval] using hc.symm

theorem sound2117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2117 node2117Labels = Sparse.eval nodeValue2117 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2117) = mixedMoment B node2117 node2117Labels := rfl
  simpa [nodeValue2117, Sparse.eval] using hc.symm

theorem sound2119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2119 node2119Labels = Sparse.eval nodeValue2119 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2119) = mixedMoment B node2119 node2119Labels := rfl
  simpa [nodeValue2119, Sparse.eval] using hc.symm

theorem sound2122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2122 node2122Labels = Sparse.eval nodeValue2122 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2122) = mixedMoment B node2122 node2122Labels := rfl
  simpa [nodeValue2122, Sparse.eval] using hc.symm

theorem sound2128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2128 node2128Labels = Sparse.eval nodeValue2128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2128) = mixedMoment B node2128 node2128Labels := rfl
  simpa [nodeValue2128, Sparse.eval] using hc.symm

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

theorem sound2189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2189 node2189Labels = Sparse.eval nodeValue2189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2189) = mixedMoment B node2189 node2189Labels := rfl
  simpa [nodeValue2189, Sparse.eval] using hc.symm

theorem sound2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2190 node2190Labels = Sparse.eval nodeValue2190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2190) = mixedMoment B node2190 node2190Labels := rfl
  simpa [nodeValue2190, Sparse.eval] using hc.symm

theorem sound2200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2200 node2200Labels = Sparse.eval nodeValue2200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2200) = mixedMoment B node2200 node2200Labels := rfl
  simpa [nodeValue2200, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2212 node2212Labels = Sparse.eval nodeValue2212 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2212) = mixedMoment B node2212 node2212Labels := rfl
  simpa [nodeValue2212, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

theorem sound2239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2239 node2239Labels = Sparse.eval nodeValue2239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2239) = mixedMoment B node2239 node2239Labels := rfl
  simpa [nodeValue2239, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = 0 := by
  exact mixedMoment_order_one B hB node2264 node2264Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = 0 := by
  exact mixedMoment_order_one B hB node2292 node2292Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

theorem sound2258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2258 node2258Labels = Sparse.eval nodeValue2258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2258) = mixedMoment B node2258 node2258Labels := rfl
  simpa [nodeValue2258, Sparse.eval] using hc.symm

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2273 node2273Labels = Sparse.eval nodeValue2273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2273) = mixedMoment B node2273 node2273Labels := rfl
  simpa [nodeValue2273, Sparse.eval] using hc.symm

theorem sound2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2276 node2276Labels = Sparse.eval nodeValue2276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2276) = mixedMoment B node2276 node2276Labels := rfl
  simpa [nodeValue2276, Sparse.eval] using hc.symm

theorem sound2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2289 node2289Labels = Sparse.eval nodeValue2289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2289) = mixedMoment B node2289 node2289Labels := rfl
  simpa [nodeValue2289, Sparse.eval] using hc.symm

theorem sound2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = Sparse.eval nodeValue2292 (mixedVector B) := by
  simpa only [nodeValue2292, Sparse.eval_nil] using zero2292 B _hB _hF

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

theorem sound2453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2453 node2453Labels = Sparse.eval nodeValue2453 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2453) = mixedMoment B node2453 node2453Labels := rfl
  simpa [nodeValue2453, Sparse.eval] using hc.symm

theorem sound2455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2455 node2455Labels = Sparse.eval nodeValue2455 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2455) = mixedMoment B node2455 node2455Labels := rfl
  simpa [nodeValue2455, Sparse.eval] using hc.symm

theorem sound2459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2459 node2459Labels = Sparse.eval nodeValue2459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2459) = mixedMoment B node2459 node2459Labels := rfl
  simpa [nodeValue2459, Sparse.eval] using hc.symm

theorem sound2490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2490 node2490Labels = Sparse.eval nodeValue2490 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2490) = mixedMoment B node2490 node2490Labels := rfl
  simpa [nodeValue2490, Sparse.eval] using hc.symm

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

theorem sound2533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2533 node2533Labels = Sparse.eval nodeValue2533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2533) = mixedMoment B node2533 node2533Labels := rfl
  simpa [nodeValue2533, Sparse.eval] using hc.symm

theorem sound2536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2536 node2536Labels = Sparse.eval nodeValue2536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2536) = mixedMoment B node2536 node2536Labels := rfl
  simpa [nodeValue2536, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2565 node2565Labels = Sparse.eval nodeValue2565 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2565) = mixedMoment B node2565 node2565Labels := rfl
  simpa [nodeValue2565, Sparse.eval] using hc.symm

theorem sound2588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2588 node2588Labels = Sparse.eval nodeValue2588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2588) = mixedMoment B node2588 node2588Labels := rfl
  simpa [nodeValue2588, Sparse.eval] using hc.symm

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

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

theorem sound2681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2681 node2681Labels = Sparse.eval nodeValue2681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2681) = mixedMoment B node2681 node2681Labels := rfl
  simpa [nodeValue2681, Sparse.eval] using hc.symm

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

theorem sound2697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2697 node2697Labels = Sparse.eval nodeValue2697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2697) = mixedMoment B node2697 node2697Labels := rfl
  simpa [nodeValue2697, Sparse.eval] using hc.symm

theorem sound2719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2719 node2719Labels = Sparse.eval nodeValue2719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2719) = mixedMoment B node2719 node2719Labels := rfl
  simpa [nodeValue2719, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2761 node2761Labels = Sparse.eval nodeValue2761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2761) = mixedMoment B node2761 node2761Labels := rfl
  simpa [nodeValue2761, Sparse.eval] using hc.symm

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

theorem sound2783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2783 node2783Labels = Sparse.eval nodeValue2783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2783) = mixedMoment B node2783 node2783Labels := rfl
  simpa [nodeValue2783, Sparse.eval] using hc.symm

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

theorem sound3255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3255 node3255Labels = Sparse.eval nodeValue3255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3255) = mixedMoment B node3255 node3255Labels := rfl
  simpa [nodeValue3255, Sparse.eval] using hc.symm

theorem sound3260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3260 node3260Labels = Sparse.eval nodeValue3260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3260) = mixedMoment B node3260 node3260Labels := rfl
  simpa [nodeValue3260, Sparse.eval] using hc.symm

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

theorem sound3264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3264 node3264Labels = Sparse.eval nodeValue3264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3264) = mixedMoment B node3264 node3264Labels := rfl
  simpa [nodeValue3264, Sparse.eval] using hc.symm

theorem sound3266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3266 node3266Labels = Sparse.eval nodeValue3266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3266) = mixedMoment B node3266 node3266Labels := rfl
  simpa [nodeValue3266, Sparse.eval] using hc.symm

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

theorem sound3291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3291 node3291Labels = Sparse.eval nodeValue3291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3291) = mixedMoment B node3291 node3291Labels := rfl
  simpa [nodeValue3291, Sparse.eval] using hc.symm

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3403 node3403Labels = 0 := by
  exact mixedMoment_alpha B hF node3403 node3403Labels 1 permutation485
    (by decide +kernel)

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

theorem sound3403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3403 node3403Labels = Sparse.eval nodeValue3403 (mixedVector B) := by
  simpa only [nodeValue3403, Sparse.eval_nil] using zero3403 B _hB _hF

theorem sound3411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3411 node3411Labels = Sparse.eval nodeValue3411 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3411) = mixedMoment B node3411 node3411Labels := rfl
  simpa [nodeValue3411, Sparse.eval] using hc.symm

theorem sound3415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3415 node3415Labels = Sparse.eval nodeValue3415 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3415) = mixedMoment B node3415 node3415Labels := rfl
  simpa [nodeValue3415, Sparse.eval] using hc.symm

theorem sound3449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3449 node3449Labels = Sparse.eval nodeValue3449 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3449) = mixedMoment B node3449 node3449Labels := rfl
  simpa [nodeValue3449, Sparse.eval] using hc.symm

theorem sound3452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3452 node3452Labels = Sparse.eval nodeValue3452 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3452) = mixedMoment B node3452 node3452Labels := rfl
  simpa [nodeValue3452, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3470 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3470 node3470Labels = 0 := by
  exact mixedMoment_order_one B hB node3470 node3470Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3484 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3484 node3484Labels = 0 := by
  exact mixedMoment_order_one B hB node3484 node3484Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3513 node3513Labels = 0 := by
  exact mixedMoment_alpha B hF node3513 node3513Labels 1 permutation444
    (by decide +kernel)

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

theorem sound3458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3458 node3458Labels = Sparse.eval nodeValue3458 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3458) = mixedMoment B node3458 node3458Labels := rfl
  simpa [nodeValue3458, Sparse.eval] using hc.symm

theorem sound3459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3459 node3459Labels = Sparse.eval nodeValue3459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3459) = mixedMoment B node3459 node3459Labels := rfl
  simpa [nodeValue3459, Sparse.eval] using hc.symm

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3470 node3470Labels = Sparse.eval nodeValue3470 (mixedVector B) := by
  simpa only [nodeValue3470, Sparse.eval_nil] using zero3470 B _hB _hF

theorem sound3475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3475 node3475Labels = Sparse.eval nodeValue3475 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3475) = mixedMoment B node3475 node3475Labels := rfl
  simpa [nodeValue3475, Sparse.eval] using hc.symm

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

theorem sound3484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3484 node3484Labels = Sparse.eval nodeValue3484 (mixedVector B) := by
  simpa only [nodeValue3484, Sparse.eval_nil] using zero3484 B _hB _hF

theorem sound3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3513 node3513Labels = Sparse.eval nodeValue3513 (mixedVector B) := by
  simpa only [nodeValue3513, Sparse.eval_nil] using zero3513 B _hB _hF

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

theorem sound3516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3516 node3516Labels = Sparse.eval nodeValue3516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3516) = mixedMoment B node3516 node3516Labels := rfl
  simpa [nodeValue3516, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = 0 := by
  exact mixedMoment_order_one B hB node3547 node3547Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

theorem sound3524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3524 node3524Labels = Sparse.eval nodeValue3524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3524) = mixedMoment B node3524 node3524Labels := rfl
  simpa [nodeValue3524, Sparse.eval] using hc.symm

theorem sound3530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3530 node3530Labels = Sparse.eval nodeValue3530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3530) = mixedMoment B node3530 node3530Labels := rfl
  simpa [nodeValue3530, Sparse.eval] using hc.symm

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3545 node3545Labels = Sparse.eval nodeValue3545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3545) = mixedMoment B node3545 node3545Labels := rfl
  simpa [nodeValue3545, Sparse.eval] using hc.symm

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

theorem sound3557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3557 node3557Labels = Sparse.eval nodeValue3557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3557) = mixedMoment B node3557 node3557Labels := rfl
  simpa [nodeValue3557, Sparse.eval] using hc.symm

theorem sound3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3564 node3564Labels = Sparse.eval nodeValue3564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3564) = mixedMoment B node3564 node3564Labels := rfl
  simpa [nodeValue3564, Sparse.eval] using hc.symm

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

theorem zero3807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = 0 := by
  exact mixedMoment_order_one B hB node3807 node3807Labels 1
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

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

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

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SourceRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.MixedSemantics

theorem offDiagSum_explicit (f : Coord → Coord → ℝ) :
    offDiagSum f =
      f 0 1 + f 0 2 + f 0 3 + f 0 4 + f 0 5 +
      f 1 0 + f 1 2 + f 1 3 + f 1 4 + f 1 5 +
      f 2 0 + f 2 1 + f 2 3 + f 2 4 + f 2 5 +
      f 3 0 + f 3 1 + f 3 2 + f 3 4 + f 3 5 +
      f 4 0 + f 4 1 + f 4 2 + f 4 3 + f 4 5 +
      f 5 0 + f 5 1 + f 5 2 + f 5 3 + f 5 4 := by
  unfold offDiagSum
  simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]
  simp only [Fin.succ, Nat.reduceAdd]
  ring_nf
  rfl

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources62
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2015 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2015 + difference 0 0) (sourceB2015 + difference 0 0) sourceC2015) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2008) := by
    have ha : (tripleCharges (sourceA2015 + difference 0 0) (sourceB2015 + difference 0 0) sourceC2015) = raw20345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2015 sourceB2015 sourceC2015 difference raw20345; decide +kernel
    rw [ha]
    exact (canonical20345 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2015 + difference 0 1) (sourceB2015 + difference 1 0) sourceC2015) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2011) := by
    have ha : (tripleCharges (sourceA2015 + difference 0 1) (sourceB2015 + difference 1 0) sourceC2015) = raw28525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2015 sourceB2015 sourceC2015 difference raw28525; decide +kernel
    rw [ha]
    exact (canonical28525 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2015 + difference 0 2) (sourceB2015 + difference 2 0) sourceC2015) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2016) := by
    have ha : (tripleCharges (sourceA2015 + difference 0 2) (sourceB2015 + difference 2 0) sourceC2015) = raw28526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2015 sourceB2015 sourceC2015 difference raw28526; decide +kernel
    rw [ha]
    exact (canonical28526 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2015 + difference 0 3) (sourceB2015 + difference 3 0) sourceC2015) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2016) := by
    have ha : (tripleCharges (sourceA2015 + difference 0 3) (sourceB2015 + difference 3 0) sourceC2015) = raw28527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2015 sourceB2015 sourceC2015 difference raw28527; decide +kernel
    rw [ha]
    exact (canonical28527 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2015 + difference 0 4) (sourceB2015 + difference 4 0) sourceC2015) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2015 + difference 0 4) (sourceB2015 + difference 4 0) sourceC2015) = raw28528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2015 sourceB2015 sourceC2015 difference raw28528; decide +kernel
    rw [ha]
    exact (canonical28528 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2015 + difference 0 5) (sourceB2015 + difference 5 0) sourceC2015) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA2015 + difference 0 5) (sourceB2015 + difference 5 0) sourceC2015) = raw28529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2015 sourceB2015 sourceC2015 difference raw28529; decide +kernel
    rw [ha]
    exact (canonical28529 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2015 + sourceB2015) sourceC2015) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2015 + sourceB2015) sourceC2015) = raw20350 := by
      apply Matrix.ext; unfold doubleCharges sourceA2015 sourceB2015 sourceC2015 raw20350; decide +kernel
    rw [ha]
    exact (canonical20350 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2015 sourceB2015 sourceC2015
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2015, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources63
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2016 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2016 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2016 + difference 0 0) (sourceB2016 + difference 0 0) sourceC2016) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2119) := by
    have ha : (tripleCharges (sourceA2016 + difference 0 0) (sourceB2016 + difference 0 0) sourceC2016) = raw28530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2016 sourceB2016 sourceC2016 difference raw28530; decide +kernel
    rw [ha]
    exact (canonical28530 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2016 + difference 0 1) (sourceB2016 + difference 1 0) sourceC2016) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2122) := by
    have ha : (tripleCharges (sourceA2016 + difference 0 1) (sourceB2016 + difference 1 0) sourceC2016) = raw28531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2016 sourceB2016 sourceC2016 difference raw28531; decide +kernel
    rw [ha]
    exact (canonical28531 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2016 + difference 0 2) (sourceB2016 + difference 2 0) sourceC2016) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2128) := by
    have ha : (tripleCharges (sourceA2016 + difference 0 2) (sourceB2016 + difference 2 0) sourceC2016) = raw28532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2016 sourceB2016 sourceC2016 difference raw28532; decide +kernel
    rw [ha]
    exact (canonical28532 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2016 + difference 0 3) (sourceB2016 + difference 3 0) sourceC2016) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2117) := by
    have ha : (tripleCharges (sourceA2016 + difference 0 3) (sourceB2016 + difference 3 0) sourceC2016) = raw28533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2016 sourceB2016 sourceC2016 difference raw28533; decide +kernel
    rw [ha]
    exact (canonical28533 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2016 + difference 0 4) (sourceB2016 + difference 4 0) sourceC2016) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2016 + difference 0 4) (sourceB2016 + difference 4 0) sourceC2016) = raw28534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2016 sourceB2016 sourceC2016 difference raw28534; decide +kernel
    rw [ha]
    exact (canonical28534 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2016 + difference 0 5) (sourceB2016 + difference 5 0) sourceC2016) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA2016 + difference 0 5) (sourceB2016 + difference 5 0) sourceC2016) = raw28535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2016 sourceB2016 sourceC2016 difference raw28535; decide +kernel
    rw [ha]
    exact (canonical28535 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2016 + sourceB2016) sourceC2016) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2016 + sourceB2016) sourceC2016) = raw28536 := by
      apply Matrix.ext; unfold doubleCharges sourceA2016 sourceB2016 sourceC2016 raw28536; decide +kernel
    rw [ha]
    exact (canonical28536 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2016 sourceB2016 sourceC2016
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2016, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2017 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2017 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2017 + difference 0 0) (sourceB2017 + difference 0 0) sourceC2017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2070) := by
    have ha : (tripleCharges (sourceA2017 + difference 0 0) (sourceB2017 + difference 0 0) sourceC2017) = raw28537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2017 sourceB2017 sourceC2017 difference raw28537; decide +kernel
    rw [ha]
    exact (canonical28537 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2017 + difference 0 1) (sourceB2017 + difference 1 0) sourceC2017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2072) := by
    have ha : (tripleCharges (sourceA2017 + difference 0 1) (sourceB2017 + difference 1 0) sourceC2017) = raw28538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2017 sourceB2017 sourceC2017 difference raw28538; decide +kernel
    rw [ha]
    exact (canonical28538 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2017 + difference 0 2) (sourceB2017 + difference 2 0) sourceC2017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2085) := by
    have ha : (tripleCharges (sourceA2017 + difference 0 2) (sourceB2017 + difference 2 0) sourceC2017) = raw28539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2017 sourceB2017 sourceC2017 difference raw28539; decide +kernel
    rw [ha]
    exact (canonical28539 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2017 + difference 0 3) (sourceB2017 + difference 3 0) sourceC2017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2075) := by
    have ha : (tripleCharges (sourceA2017 + difference 0 3) (sourceB2017 + difference 3 0) sourceC2017) = raw28540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2017 sourceB2017 sourceC2017 difference raw28540; decide +kernel
    rw [ha]
    exact (canonical28540 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2017 + difference 0 4) (sourceB2017 + difference 4 0) sourceC2017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA2017 + difference 0 4) (sourceB2017 + difference 4 0) sourceC2017) = raw28541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2017 sourceB2017 sourceC2017 difference raw28541; decide +kernel
    rw [ha]
    exact (canonical28541 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2017 + difference 0 5) (sourceB2017 + difference 5 0) sourceC2017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA2017 + difference 0 5) (sourceB2017 + difference 5 0) sourceC2017) = raw28542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2017 sourceB2017 sourceC2017 difference raw28542; decide +kernel
    rw [ha]
    exact (canonical28542 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2017 + sourceB2017) sourceC2017) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2017 + sourceB2017) sourceC2017) = raw28543 := by
      apply Matrix.ext; unfold doubleCharges sourceA2017 sourceB2017 sourceC2017 raw28543; decide +kernel
    rw [ha]
    exact (canonical28543 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2017 sourceB2017 sourceC2017
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2017, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2018 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2018 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2018 + difference 0 0) (sourceB2018 + difference 0 0) sourceC2018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2453) := by
    have ha : (tripleCharges (sourceA2018 + difference 0 0) (sourceB2018 + difference 0 0) sourceC2018) = raw28544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2018 sourceB2018 sourceC2018 difference raw28544; decide +kernel
    rw [ha]
    exact (canonical28544 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2018 + difference 0 1) (sourceB2018 + difference 1 0) sourceC2018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2455) := by
    have ha : (tripleCharges (sourceA2018 + difference 0 1) (sourceB2018 + difference 1 0) sourceC2018) = raw28545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2018 sourceB2018 sourceC2018 difference raw28545; decide +kernel
    rw [ha]
    exact (canonical28545 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2018 + difference 0 2) (sourceB2018 + difference 2 0) sourceC2018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2490) := by
    have ha : (tripleCharges (sourceA2018 + difference 0 2) (sourceB2018 + difference 2 0) sourceC2018) = raw28546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2018 sourceB2018 sourceC2018 difference raw28546; decide +kernel
    rw [ha]
    exact (canonical28546 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2018 + difference 0 3) (sourceB2018 + difference 3 0) sourceC2018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA2018 + difference 0 3) (sourceB2018 + difference 3 0) sourceC2018) = raw28547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2018 sourceB2018 sourceC2018 difference raw28547; decide +kernel
    rw [ha]
    exact (canonical28547 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2018 + difference 0 4) (sourceB2018 + difference 4 0) sourceC2018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA2018 + difference 0 4) (sourceB2018 + difference 4 0) sourceC2018) = raw28548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2018 sourceB2018 sourceC2018 difference raw28548; decide +kernel
    rw [ha]
    exact (canonical28548 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2018 + difference 0 5) (sourceB2018 + difference 5 0) sourceC2018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2018 + difference 0 5) (sourceB2018 + difference 5 0) sourceC2018) = raw28549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2018 sourceB2018 sourceC2018 difference raw28549; decide +kernel
    rw [ha]
    exact (canonical28549 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2018 + sourceB2018) sourceC2018) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2018 + sourceB2018) sourceC2018) = raw28550 := by
      apply Matrix.ext; unfold doubleCharges sourceA2018 sourceB2018 sourceC2018 raw28550; decide +kernel
    rw [ha]
    exact (canonical28550 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2018 sourceB2018 sourceC2018
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2018, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2019 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2019 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2019 + difference 0 5) (sourceB2019 + difference 5 0) sourceC2019) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2019 + difference 0 5) (sourceB2019 + difference 5 0) sourceC2019) = raw28549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2019 sourceB2019 sourceC2019 difference raw28549; decide +kernel
    rw [ha]
    exact (canonical28549 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2019 + difference 1 5) (sourceB2019 + difference 5 1) sourceC2019) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2019 + difference 1 5) (sourceB2019 + difference 5 1) sourceC2019) = raw28551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2019 sourceB2019 sourceC2019 difference raw28551; decide +kernel
    rw [ha]
    exact (canonical28551 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2019 + difference 2 5) (sourceB2019 + difference 5 2) sourceC2019) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2536) := by
    have ha : (tripleCharges (sourceA2019 + difference 2 5) (sourceB2019 + difference 5 2) sourceC2019) = raw28552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2019 sourceB2019 sourceC2019 difference raw28552; decide +kernel
    rw [ha]
    exact (canonical28552 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2019 + difference 3 5) (sourceB2019 + difference 5 3) sourceC2019) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2565) := by
    have ha : (tripleCharges (sourceA2019 + difference 3 5) (sourceB2019 + difference 5 3) sourceC2019) = raw28553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2019 sourceB2019 sourceC2019 difference raw28553; decide +kernel
    rw [ha]
    exact (canonical28553 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2019 + difference 4 5) (sourceB2019 + difference 5 4) sourceC2019) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2533) := by
    have ha : (tripleCharges (sourceA2019 + difference 4 5) (sourceB2019 + difference 5 4) sourceC2019) = raw28554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2019 sourceB2019 sourceC2019 difference raw28554; decide +kernel
    rw [ha]
    exact (canonical28554 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2019 + difference 5 5) (sourceB2019 + difference 5 5) sourceC2019) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2453) := by
    have ha : (tripleCharges (sourceA2019 + difference 5 5) (sourceB2019 + difference 5 5) sourceC2019) = raw28544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2019 sourceB2019 sourceC2019 difference raw28544; decide +kernel
    rw [ha]
    exact (canonical28544 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2019 + sourceB2019) sourceC2019) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2019 + sourceB2019) sourceC2019) = raw28550 := by
      apply Matrix.ext; unfold doubleCharges sourceA2019 sourceB2019 sourceC2019 raw28550; decide +kernel
    rw [ha]
    exact (canonical28550 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2019 sourceB2019 sourceC2019
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2019, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2020 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2020 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2020 + difference 0 0) (sourceB2020 + difference 0 0) sourceC2020) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1991) := by
    have ha : (tripleCharges (sourceA2020 + difference 0 0) (sourceB2020 + difference 0 0) sourceC2020) = raw28555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2020 sourceB2020 sourceC2020 difference raw28555; decide +kernel
    rw [ha]
    exact (canonical28555 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2020 + difference 0 1) (sourceB2020 + difference 1 0) sourceC2020) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1993) := by
    have ha : (tripleCharges (sourceA2020 + difference 0 1) (sourceB2020 + difference 1 0) sourceC2020) = raw28556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2020 sourceB2020 sourceC2020 difference raw28556; decide +kernel
    rw [ha]
    exact (canonical28556 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2020 + difference 0 2) (sourceB2020 + difference 2 0) sourceC2020) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2030) := by
    have ha : (tripleCharges (sourceA2020 + difference 0 2) (sourceB2020 + difference 2 0) sourceC2020) = raw28557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2020 sourceB2020 sourceC2020 difference raw28557; decide +kernel
    rw [ha]
    exact (canonical28557 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2020 + difference 0 3) (sourceB2020 + difference 3 0) sourceC2020) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1997) := by
    have ha : (tripleCharges (sourceA2020 + difference 0 3) (sourceB2020 + difference 3 0) sourceC2020) = raw28558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2020 sourceB2020 sourceC2020 difference raw28558; decide +kernel
    rw [ha]
    exact (canonical28558 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2020 + difference 0 4) (sourceB2020 + difference 4 0) sourceC2020) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2020 + difference 0 4) (sourceB2020 + difference 4 0) sourceC2020) = raw28559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2020 sourceB2020 sourceC2020 difference raw28559; decide +kernel
    rw [ha]
    exact (canonical28559 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2020 + difference 0 5) (sourceB2020 + difference 5 0) sourceC2020) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2020 + difference 0 5) (sourceB2020 + difference 5 0) sourceC2020) = raw28560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2020 sourceB2020 sourceC2020 difference raw28560; decide +kernel
    rw [ha]
    exact (canonical28560 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2020 + sourceB2020) sourceC2020) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2020 + sourceB2020) sourceC2020) = raw28561 := by
      apply Matrix.ext; unfold doubleCharges sourceA2020 sourceB2020 sourceC2020 raw28561; decide +kernel
    rw [ha]
    exact (canonical28561 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2020 sourceB2020 sourceC2020
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2020, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2023 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2023 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2023 + difference 0 1) (sourceB2023 + difference 1 0) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2023 + difference 0 1) (sourceB2023 + difference 1 0) sourceC2023) = raw28591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28591; decide +kernel
    rw [ha]
    exact (canonical28591 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2023 + difference 0 2) (sourceB2023 + difference 2 0) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2023 + difference 0 2) (sourceB2023 + difference 2 0) sourceC2023) = raw28592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28592; decide +kernel
    rw [ha]
    exact (canonical28592 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2023 + difference 0 3) (sourceB2023 + difference 3 0) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2023 + difference 0 3) (sourceB2023 + difference 3 0) sourceC2023) = raw28593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28593; decide +kernel
    rw [ha]
    exact (canonical28593 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2023 + difference 0 4) (sourceB2023 + difference 4 0) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2023 + difference 0 4) (sourceB2023 + difference 4 0) sourceC2023) = raw5131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5131; decide +kernel
    rw [ha]
    exact (canonical5131 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2023 + difference 0 5) (sourceB2023 + difference 5 0) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA2023 + difference 0 5) (sourceB2023 + difference 5 0) sourceC2023) = raw10290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw10290; decide +kernel
    rw [ha]
    exact (canonical10290 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2023 + difference 1 0) (sourceB2023 + difference 0 1) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA2023 + difference 1 0) (sourceB2023 + difference 0 1) sourceC2023) = raw5151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5151; decide +kernel
    rw [ha]
    exact (canonical5151 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2023 + difference 1 2) (sourceB2023 + difference 2 1) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA2023 + difference 1 2) (sourceB2023 + difference 2 1) sourceC2023) = raw5153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5153; decide +kernel
    rw [ha]
    exact (canonical5153 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2023 + difference 1 3) (sourceB2023 + difference 3 1) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA2023 + difference 1 3) (sourceB2023 + difference 3 1) sourceC2023) = raw5154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5154; decide +kernel
    rw [ha]
    exact (canonical5154 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2023 + difference 1 4) (sourceB2023 + difference 4 1) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA2023 + difference 1 4) (sourceB2023 + difference 4 1) sourceC2023) = raw10311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw10311; decide +kernel
    rw [ha]
    exact (canonical10311 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2023 + difference 1 5) (sourceB2023 + difference 5 1) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA2023 + difference 1 5) (sourceB2023 + difference 5 1) sourceC2023) = raw5155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5155; decide +kernel
    rw [ha]
    exact (canonical5155 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2023 + difference 2 0) (sourceB2023 + difference 0 2) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA2023 + difference 2 0) (sourceB2023 + difference 0 2) sourceC2023) = raw20515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw20515; decide +kernel
    rw [ha]
    exact (canonical20515 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2023 + difference 2 1) (sourceB2023 + difference 1 2) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2023 + difference 2 1) (sourceB2023 + difference 1 2) sourceC2023) = raw28594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28594; decide +kernel
    rw [ha]
    exact (canonical28594 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2023 + difference 2 3) (sourceB2023 + difference 3 2) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2189) := by
    have ha : (tripleCharges (sourceA2023 + difference 2 3) (sourceB2023 + difference 3 2) sourceC2023) = raw28595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28595; decide +kernel
    rw [ha]
    exact (canonical28595 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2023 + difference 2 4) (sourceB2023 + difference 4 2) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2023 + difference 2 4) (sourceB2023 + difference 4 2) sourceC2023) = raw5142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5142; decide +kernel
    rw [ha]
    exact (canonical5142 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2023 + difference 2 5) (sourceB2023 + difference 5 2) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA2023 + difference 2 5) (sourceB2023 + difference 5 2) sourceC2023) = raw10299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw10299; decide +kernel
    rw [ha]
    exact (canonical10299 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2023 + difference 3 0) (sourceB2023 + difference 0 3) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA2023 + difference 3 0) (sourceB2023 + difference 0 3) sourceC2023) = raw20518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw20518; decide +kernel
    rw [ha]
    exact (canonical20518 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2023 + difference 3 1) (sourceB2023 + difference 1 3) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2023 + difference 3 1) (sourceB2023 + difference 1 3) sourceC2023) = raw28596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28596; decide +kernel
    rw [ha]
    exact (canonical28596 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2023 + difference 3 2) (sourceB2023 + difference 2 3) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2189) := by
    have ha : (tripleCharges (sourceA2023 + difference 3 2) (sourceB2023 + difference 2 3) sourceC2023) = raw28597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28597; decide +kernel
    rw [ha]
    exact (canonical28597 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2023 + difference 3 4) (sourceB2023 + difference 4 3) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2023 + difference 3 4) (sourceB2023 + difference 4 3) sourceC2023) = raw5147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5147; decide +kernel
    rw [ha]
    exact (canonical5147 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2023 + difference 3 5) (sourceB2023 + difference 5 3) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA2023 + difference 3 5) (sourceB2023 + difference 5 3) sourceC2023) = raw10303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw10303; decide +kernel
    rw [ha]
    exact (canonical10303 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2023 + difference 4 0) (sourceB2023 + difference 0 4) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2258) := by
    have ha : (tripleCharges (sourceA2023 + difference 4 0) (sourceB2023 + difference 0 4) sourceC2023) = raw20521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw20521; decide +kernel
    rw [ha]
    exact (canonical20521 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2023 + difference 4 1) (sourceB2023 + difference 1 4) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2273) := by
    have ha : (tripleCharges (sourceA2023 + difference 4 1) (sourceB2023 + difference 1 4) sourceC2023) = raw28598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28598; decide +kernel
    rw [ha]
    exact (canonical28598 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2023 + difference 4 2) (sourceB2023 + difference 2 4) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2239) := by
    have ha : (tripleCharges (sourceA2023 + difference 4 2) (sourceB2023 + difference 2 4) sourceC2023) = raw28599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28599; decide +kernel
    rw [ha]
    exact (canonical28599 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2023 + difference 4 3) (sourceB2023 + difference 3 4) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2239) := by
    have ha : (tripleCharges (sourceA2023 + difference 4 3) (sourceB2023 + difference 3 4) sourceC2023) = raw28600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28600; decide +kernel
    rw [ha]
    exact (canonical28600 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2023 + difference 4 5) (sourceB2023 + difference 5 4) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA2023 + difference 4 5) (sourceB2023 + difference 5 4) sourceC2023) = raw10307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw10307; decide +kernel
    rw [ha]
    exact (canonical10307 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2023 + difference 5 0) (sourceB2023 + difference 0 5) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA2023 + difference 5 0) (sourceB2023 + difference 0 5) sourceC2023) = raw19681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw19681; decide +kernel
    rw [ha]
    exact (canonical19681 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2023 + difference 5 1) (sourceB2023 + difference 1 5) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1735) := by
    have ha : (tripleCharges (sourceA2023 + difference 5 1) (sourceB2023 + difference 1 5) sourceC2023) = raw28601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28601; decide +kernel
    rw [ha]
    exact (canonical28601 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2023 + difference 5 2) (sourceB2023 + difference 2 5) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA2023 + difference 5 2) (sourceB2023 + difference 2 5) sourceC2023) = raw28602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28602; decide +kernel
    rw [ha]
    exact (canonical28602 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2023 + difference 5 3) (sourceB2023 + difference 3 5) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA2023 + difference 5 3) (sourceB2023 + difference 3 5) sourceC2023) = raw28603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28603; decide +kernel
    rw [ha]
    exact (canonical28603 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2023 + difference 5 4) (sourceB2023 + difference 4 5) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA2023 + difference 5 4) (sourceB2023 + difference 4 5) sourceC2023) = raw5157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5157; decide +kernel
    rw [ha]
    exact (canonical5157 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2023 sourceB2023 sourceC2023
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2023, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2024 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2024 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2024 + difference 0 1) (sourceB2024 + difference 1 0) sourceC2024) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA2024 + difference 0 1) (sourceB2024 + difference 1 0) sourceC2024) = raw28604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2024 sourceB2024 sourceC2024 difference raw28604; decide +kernel
    rw [ha]
    exact (canonical28604 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2024 + difference 1 1) (sourceB2024 + difference 1 1) sourceC2024) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2024 + difference 1 1) (sourceB2024 + difference 1 1) sourceC2024) = raw5175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2024 sourceB2024 sourceC2024 difference raw5175; decide +kernel
    rw [ha]
    exact (canonical5175 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2024 + difference 2 1) (sourceB2024 + difference 1 2) sourceC2024) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1978) := by
    have ha : (tripleCharges (sourceA2024 + difference 2 1) (sourceB2024 + difference 1 2) sourceC2024) = raw28605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2024 sourceB2024 sourceC2024 difference raw28605; decide +kernel
    rw [ha]
    exact (canonical28605 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2024 + difference 3 1) (sourceB2024 + difference 1 3) sourceC2024) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1978) := by
    have ha : (tripleCharges (sourceA2024 + difference 3 1) (sourceB2024 + difference 1 3) sourceC2024) = raw28606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2024 sourceB2024 sourceC2024 difference raw28606; decide +kernel
    rw [ha]
    exact (canonical28606 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2024 + difference 4 1) (sourceB2024 + difference 1 4) sourceC2024) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1830) := by
    have ha : (tripleCharges (sourceA2024 + difference 4 1) (sourceB2024 + difference 1 4) sourceC2024) = raw28607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2024 sourceB2024 sourceC2024 difference raw28607; decide +kernel
    rw [ha]
    exact (canonical28607 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2024 + difference 5 1) (sourceB2024 + difference 1 5) sourceC2024) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 952) := by
    have ha : (tripleCharges (sourceA2024 + difference 5 1) (sourceB2024 + difference 1 5) sourceC2024) = raw28608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2024 sourceB2024 sourceC2024 difference raw28608; decide +kernel
    rw [ha]
    exact (canonical28608 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2024 + sourceB2024) sourceC2024) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2024 + sourceB2024) sourceC2024) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA2024 sourceB2024 sourceC2024 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2024 sourceB2024 sourceC2024
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2024, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2025 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2025 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2025 + difference 2 0) (sourceB2025 + difference 0 2) sourceC2025) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1157) := by
    have ha : (tripleCharges (sourceA2025 + difference 2 0) (sourceB2025 + difference 0 2) sourceC2025) = raw20531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2025 sourceB2025 sourceC2025 difference raw20531; decide +kernel
    rw [ha]
    exact (canonical20531 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2025 + difference 2 1) (sourceB2025 + difference 1 2) sourceC2025) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1978) := by
    have ha : (tripleCharges (sourceA2025 + difference 2 1) (sourceB2025 + difference 1 2) sourceC2025) = raw28605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2025 sourceB2025 sourceC2025 difference raw28605; decide +kernel
    rw [ha]
    exact (canonical28605 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2025 + difference 2 2) (sourceB2025 + difference 2 2) sourceC2025) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2025 + difference 2 2) (sourceB2025 + difference 2 2) sourceC2025) = raw5175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2025 sourceB2025 sourceC2025 difference raw5175; decide +kernel
    rw [ha]
    exact (canonical5175 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2025 + difference 2 3) (sourceB2025 + difference 3 2) sourceC2025) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1972) := by
    have ha : (tripleCharges (sourceA2025 + difference 2 3) (sourceB2025 + difference 3 2) sourceC2025) = raw28609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2025 sourceB2025 sourceC2025 difference raw28609; decide +kernel
    rw [ha]
    exact (canonical28609 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2025 + difference 2 4) (sourceB2025 + difference 4 2) sourceC2025) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2025 + difference 2 4) (sourceB2025 + difference 4 2) sourceC2025) = raw5173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2025 sourceB2025 sourceC2025 difference raw5173; decide +kernel
    rw [ha]
    exact (canonical5173 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2025 + difference 2 5) (sourceB2025 + difference 5 2) sourceC2025) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2588) := by
    have ha : (tripleCharges (sourceA2025 + difference 2 5) (sourceB2025 + difference 5 2) sourceC2025) = raw28610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2025 sourceB2025 sourceC2025 difference raw28610; decide +kernel
    rw [ha]
    exact (canonical28610 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2025 + sourceB2025) sourceC2025) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2025 + sourceB2025) sourceC2025) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA2025 sourceB2025 sourceC2025 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2025 sourceB2025 sourceC2025
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2025, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2026 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2026 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2026 + difference 0 2) (sourceB2026 + difference 2 0) sourceC2026) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2026 + difference 0 2) (sourceB2026 + difference 2 0) sourceC2026) = raw28611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2026 sourceB2026 sourceC2026 difference raw28611; decide +kernel
    rw [ha]
    exact (canonical28611 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2026 + difference 1 2) (sourceB2026 + difference 2 1) sourceC2026) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2026 + difference 1 2) (sourceB2026 + difference 2 1) sourceC2026) = raw5177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2026 sourceB2026 sourceC2026 difference raw5177; decide +kernel
    rw [ha]
    exact (canonical5177 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2026 + difference 2 2) (sourceB2026 + difference 2 2) sourceC2026) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2026 + difference 2 2) (sourceB2026 + difference 2 2) sourceC2026) = raw5175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2026 sourceB2026 sourceC2026 difference raw5175; decide +kernel
    rw [ha]
    exact (canonical5175 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2026 + difference 3 2) (sourceB2026 + difference 2 3) sourceC2026) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1972) := by
    have ha : (tripleCharges (sourceA2026 + difference 3 2) (sourceB2026 + difference 2 3) sourceC2026) = raw28612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2026 sourceB2026 sourceC2026 difference raw28612; decide +kernel
    rw [ha]
    exact (canonical28612 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2026 + difference 4 2) (sourceB2026 + difference 2 4) sourceC2026) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1823) := by
    have ha : (tripleCharges (sourceA2026 + difference 4 2) (sourceB2026 + difference 2 4) sourceC2026) = raw28613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2026 sourceB2026 sourceC2026 difference raw28613; decide +kernel
    rw [ha]
    exact (canonical28613 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2026 + difference 5 2) (sourceB2026 + difference 2 5) sourceC2026) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 943) := by
    have ha : (tripleCharges (sourceA2026 + difference 5 2) (sourceB2026 + difference 2 5) sourceC2026) = raw28614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2026 sourceB2026 sourceC2026 difference raw28614; decide +kernel
    rw [ha]
    exact (canonical28614 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2026 + sourceB2026) sourceC2026) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2026 + sourceB2026) sourceC2026) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA2026 sourceB2026 sourceC2026 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2026 sourceB2026 sourceC2026
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2026, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2032 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2032 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2032 + difference 0 1) (sourceB2032 + difference 1 0) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2032 + difference 0 1) (sourceB2032 + difference 1 0) sourceC2032) = raw28728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28728; decide +kernel
    rw [ha]
    exact (canonical28728 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2032 + difference 0 2) (sourceB2032 + difference 2 0) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA2032 + difference 0 2) (sourceB2032 + difference 2 0) sourceC2032) = raw28729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28729; decide +kernel
    rw [ha]
    exact (canonical28729 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2032 + difference 0 3) (sourceB2032 + difference 3 0) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2032 + difference 0 3) (sourceB2032 + difference 3 0) sourceC2032) = raw28730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28730; decide +kernel
    rw [ha]
    exact (canonical28730 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2032 + difference 0 4) (sourceB2032 + difference 4 0) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA2032 + difference 0 4) (sourceB2032 + difference 4 0) sourceC2032) = raw28731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28731; decide +kernel
    rw [ha]
    exact (canonical28731 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2032 + difference 0 5) (sourceB2032 + difference 5 0) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2032 + difference 0 5) (sourceB2032 + difference 5 0) sourceC2032) = raw28732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28732; decide +kernel
    rw [ha]
    exact (canonical28732 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2032 + difference 1 0) (sourceB2032 + difference 0 1) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA2032 + difference 1 0) (sourceB2032 + difference 0 1) sourceC2032) = raw28733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28733; decide +kernel
    rw [ha]
    exact (canonical28733 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2032 + difference 1 2) (sourceB2032 + difference 2 1) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2032 + difference 1 2) (sourceB2032 + difference 2 1) sourceC2032) = raw20703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20703; decide +kernel
    rw [ha]
    exact (canonical20703 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2032 + difference 1 3) (sourceB2032 + difference 3 1) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3484) := by
    have ha : (tripleCharges (sourceA2032 + difference 1 3) (sourceB2032 + difference 3 1) sourceC2032) = raw20704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20704; decide +kernel
    rw [ha]
    exact (canonical20704 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2032 + difference 1 4) (sourceB2032 + difference 4 1) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA2032 + difference 1 4) (sourceB2032 + difference 4 1) sourceC2032) = raw20705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20705; decide +kernel
    rw [ha]
    exact (canonical20705 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2032 + difference 1 5) (sourceB2032 + difference 5 1) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA2032 + difference 1 5) (sourceB2032 + difference 5 1) sourceC2032) = raw20706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20706; decide +kernel
    rw [ha]
    exact (canonical20706 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2032 + difference 2 0) (sourceB2032 + difference 0 2) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA2032 + difference 2 0) (sourceB2032 + difference 0 2) sourceC2032) = raw20713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20713; decide +kernel
    rw [ha]
    exact (canonical20713 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2032 + difference 2 1) (sourceB2032 + difference 1 2) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3452) := by
    have ha : (tripleCharges (sourceA2032 + difference 2 1) (sourceB2032 + difference 1 2) sourceC2032) = raw28734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28734; decide +kernel
    rw [ha]
    exact (canonical28734 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2032 + difference 2 3) (sourceB2032 + difference 3 2) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3449) := by
    have ha : (tripleCharges (sourceA2032 + difference 2 3) (sourceB2032 + difference 3 2) sourceC2032) = raw28735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28735; decide +kernel
    rw [ha]
    exact (canonical28735 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2032 + difference 2 4) (sourceB2032 + difference 4 2) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA2032 + difference 2 4) (sourceB2032 + difference 4 2) sourceC2032) = raw28736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28736; decide +kernel
    rw [ha]
    exact (canonical28736 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2032 + difference 2 5) (sourceB2032 + difference 5 2) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA2032 + difference 2 5) (sourceB2032 + difference 5 2) sourceC2032) = raw28737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28737; decide +kernel
    rw [ha]
    exact (canonical28737 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2032 + difference 3 0) (sourceB2032 + difference 0 3) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA2032 + difference 3 0) (sourceB2032 + difference 0 3) sourceC2032) = raw20718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20718; decide +kernel
    rw [ha]
    exact (canonical20718 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2032 + difference 3 1) (sourceB2032 + difference 1 3) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2032 + difference 3 1) (sourceB2032 + difference 1 3) sourceC2032) = raw28738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28738; decide +kernel
    rw [ha]
    exact (canonical28738 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2032 + difference 3 2) (sourceB2032 + difference 2 3) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3458) := by
    have ha : (tripleCharges (sourceA2032 + difference 3 2) (sourceB2032 + difference 2 3) sourceC2032) = raw28739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28739; decide +kernel
    rw [ha]
    exact (canonical28739 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2032 + difference 3 4) (sourceB2032 + difference 4 3) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA2032 + difference 3 4) (sourceB2032 + difference 4 3) sourceC2032) = raw28740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28740; decide +kernel
    rw [ha]
    exact (canonical28740 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2032 + difference 3 5) (sourceB2032 + difference 5 3) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2032 + difference 3 5) (sourceB2032 + difference 5 3) sourceC2032) = raw28741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28741; decide +kernel
    rw [ha]
    exact (canonical28741 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2032 + difference 4 0) (sourceB2032 + difference 0 4) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA2032 + difference 4 0) (sourceB2032 + difference 0 4) sourceC2032) = raw20723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20723; decide +kernel
    rw [ha]
    exact (canonical20723 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2032 + difference 4 1) (sourceB2032 + difference 1 4) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2032 + difference 4 1) (sourceB2032 + difference 1 4) sourceC2032) = raw28742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28742; decide +kernel
    rw [ha]
    exact (canonical28742 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2032 + difference 4 2) (sourceB2032 + difference 2 4) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3403) := by
    have ha : (tripleCharges (sourceA2032 + difference 4 2) (sourceB2032 + difference 2 4) sourceC2032) = raw28743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28743; decide +kernel
    rw [ha]
    exact (canonical28743 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2032 + difference 4 3) (sourceB2032 + difference 3 4) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2032 + difference 4 3) (sourceB2032 + difference 3 4) sourceC2032) = raw28744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28744; decide +kernel
    rw [ha]
    exact (canonical28744 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2032 + difference 4 5) (sourceB2032 + difference 5 4) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2032 + difference 4 5) (sourceB2032 + difference 5 4) sourceC2032) = raw28745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28745; decide +kernel
    rw [ha]
    exact (canonical28745 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2032 + difference 5 0) (sourceB2032 + difference 0 5) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3262) := by
    have ha : (tripleCharges (sourceA2032 + difference 5 0) (sourceB2032 + difference 0 5) sourceC2032) = raw20728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20728; decide +kernel
    rw [ha]
    exact (canonical20728 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2032 + difference 5 1) (sourceB2032 + difference 1 5) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA2032 + difference 5 1) (sourceB2032 + difference 1 5) sourceC2032) = raw28746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28746; decide +kernel
    rw [ha]
    exact (canonical28746 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2032 + difference 5 2) (sourceB2032 + difference 2 5) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3255) := by
    have ha : (tripleCharges (sourceA2032 + difference 5 2) (sourceB2032 + difference 2 5) sourceC2032) = raw28747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28747; decide +kernel
    rw [ha]
    exact (canonical28747 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2032 + difference 5 3) (sourceB2032 + difference 3 5) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3264) := by
    have ha : (tripleCharges (sourceA2032 + difference 5 3) (sourceB2032 + difference 3 5) sourceC2032) = raw28748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28748; decide +kernel
    rw [ha]
    exact (canonical28748 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2032 + difference 5 4) (sourceB2032 + difference 4 5) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA2032 + difference 5 4) (sourceB2032 + difference 4 5) sourceC2032) = raw28749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28749; decide +kernel
    rw [ha]
    exact (canonical28749 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2032 sourceB2032 sourceC2032
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2032, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1696 : Integer.Sparse.reindex keyMap MixedData.row1696 = numericRow1696 := by decide +kernel

theorem numericCheck1696 (x : Master → ℝ) : Integer.Sparse.eval numericRow1696 x =
    (1 : ℝ) * reducedSource1696 x := by
  norm_num [numericRow1696, reducedSource1696, Integer.Sparse.eval, Sparse.eval, nodeValue2008, nodeValue2011, nodeValue2016, nodeValue2242, nodeValue3524, nodeValue4080]

theorem reindexCheck1697 : Integer.Sparse.reindex keyMap MixedData.row1697 = numericRow1697 := by decide +kernel

theorem numericCheck1697 (x : Master → ℝ) : Integer.Sparse.eval numericRow1697 x =
    (1 : ℝ) * reducedSource1697 x := by
  norm_num [numericRow1697, reducedSource1697, Integer.Sparse.eval, Sparse.eval, nodeValue2117, nodeValue2119, nodeValue2122, nodeValue2128, nodeValue2215, nodeValue2681, nodeValue4082]

theorem reindexCheck1698 : Integer.Sparse.reindex keyMap MixedData.row1698 = numericRow1698 := by decide +kernel

theorem numericCheck1698 (x : Master → ℝ) : Integer.Sparse.eval numericRow1698 x =
    (1 : ℝ) * reducedSource1698 x := by
  norm_num [numericRow1698, reducedSource1698, Integer.Sparse.eval, Sparse.eval, nodeValue2070, nodeValue2072, nodeValue2075, nodeValue2085, nodeValue2190, nodeValue3557, nodeValue4080]

theorem reindexCheck1699 : Integer.Sparse.reindex keyMap MixedData.row1699 = numericRow1699 := by decide +kernel

theorem numericCheck1699 (x : Master → ℝ) : Integer.Sparse.eval numericRow1699 x =
    (1 : ℝ) * reducedSource1699 x := by
  norm_num [numericRow1699, reducedSource1699, Integer.Sparse.eval, Sparse.eval, nodeValue2453, nodeValue2455, nodeValue2459, nodeValue2490, nodeValue2697, nodeValue3795, nodeValue4088]

theorem reindexCheck1700 : Integer.Sparse.reindex keyMap MixedData.row1700 = numericRow1700 := by decide +kernel

theorem numericCheck1700 (x : Master → ℝ) : Integer.Sparse.eval numericRow1700 x =
    (1 : ℝ) * reducedSource1700 x := by
  norm_num [numericRow1700, reducedSource1700, Integer.Sparse.eval, Sparse.eval, nodeValue2453, nodeValue2533, nodeValue2536, nodeValue2565, nodeValue2672, nodeValue3795, nodeValue4088]

theorem reindexCheck1701 : Integer.Sparse.reindex keyMap MixedData.row1701 = numericRow1701 := by decide +kernel

theorem numericCheck1701 (x : Master → ℝ) : Integer.Sparse.eval numericRow1701 x =
    (1 : ℝ) * reducedSource1701 x := by
  norm_num [numericRow1701, reducedSource1701, Integer.Sparse.eval, Sparse.eval, nodeValue1991, nodeValue1993, nodeValue1997, nodeValue2030, nodeValue2215, nodeValue3516, nodeValue4082]

theorem reindexCheck1704 : Integer.Sparse.reindex keyMap MixedData.row1704 = numericRow1704 := by decide +kernel

theorem numericCheck1704 (x : Master → ℝ) : Integer.Sparse.eval numericRow1704 x =
    (1 : ℝ) * reducedSource1704 x := by
  norm_num [numericRow1704, reducedSource1704, Integer.Sparse.eval, Sparse.eval, nodeValue1704, nodeValue1722, nodeValue1725, nodeValue1735, nodeValue2189, nodeValue2200, nodeValue2203, nodeValue2212, nodeValue2239, nodeValue2242, nodeValue2258, nodeValue2261, nodeValue2264, nodeValue2273, nodeValue2276, nodeValue2289, nodeValue2292, nodeValue2719, nodeValue2761, nodeValue2765, nodeValue2783]

theorem reindexCheck1705 : Integer.Sparse.reindex keyMap MixedData.row1705 = numericRow1705 := by decide +kernel

theorem numericCheck1705 (x : Master → ℝ) : Integer.Sparse.eval numericRow1705 x =
    (1 : ℝ) * reducedSource1705 x := by
  norm_num [numericRow1705, reducedSource1705, Integer.Sparse.eval, Sparse.eval, nodeValue952, nodeValue1830, nodeValue1978, nodeValue2109, nodeValue2115, nodeValue4084]

theorem reindexCheck1706 : Integer.Sparse.reindex keyMap MixedData.row1706 = numericRow1706 := by decide +kernel

theorem numericCheck1706 (x : Master → ℝ) : Integer.Sparse.eval numericRow1706 x =
    (1 : ℝ) * reducedSource1706 x := by
  norm_num [numericRow1706, reducedSource1706, Integer.Sparse.eval, Sparse.eval, nodeValue1157, nodeValue1972, nodeValue1978, nodeValue2022, nodeValue2109, nodeValue2588, nodeValue4084]

theorem reindexCheck1707 : Integer.Sparse.reindex keyMap MixedData.row1707 = numericRow1707 := by decide +kernel

theorem numericCheck1707 (x : Master → ℝ) : Integer.Sparse.eval numericRow1707 x =
    (1 : ℝ) * reducedSource1707 x := by
  norm_num [numericRow1707, reducedSource1707, Integer.Sparse.eval, Sparse.eval, nodeValue943, nodeValue1823, nodeValue1972, nodeValue2106, nodeValue2109, nodeValue4084]

theorem reindexCheck1711 : Integer.Sparse.reindex keyMap MixedData.row1711 = numericRow1711 := by decide +kernel

theorem numericCheck1711 (x : Master → ℝ) : Integer.Sparse.eval numericRow1711 x =
    (1 : ℝ) * reducedSource1711 x := by
  norm_num [numericRow1711, reducedSource1711, Integer.Sparse.eval, Sparse.eval, nodeValue3255, nodeValue3260, nodeValue3262, nodeValue3264, nodeValue3266, nodeValue3268, nodeValue3272, nodeValue3291, nodeValue3300, nodeValue3403, nodeValue3411, nodeValue3415, nodeValue3449, nodeValue3452, nodeValue3458, nodeValue3459, nodeValue3468, nodeValue3470, nodeValue3475, nodeValue3478, nodeValue3484, nodeValue3513, nodeValue3514, nodeValue3522, nodeValue3530, nodeValue3533, nodeValue3545, nodeValue3547, nodeValue3564, nodeValue3807]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1696 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1696 (mixedVector B) = 0 := by
  have h2008 : mixedVector B (Sum.inr 2008) = Sparse.eval nodeValue2008 (mixedVector B) := by
    change mixedMoment B node2008 node2008Labels = _
    exact sound2008 B hB hF
  have h2011 : mixedVector B (Sum.inr 2011) = Sparse.eval nodeValue2011 (mixedVector B) := by
    change mixedMoment B node2011 node2011Labels = _
    exact sound2011 B hB hF
  have h2016 : mixedVector B (Sum.inr 2016) = Sparse.eval nodeValue2016 (mixedVector B) := by
    change mixedMoment B node2016 node2016Labels = _
    exact sound2016 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h3524 : mixedVector B (Sum.inr 3524) = Sparse.eval nodeValue3524 (mixedVector B) := by
    change mixedMoment B node3524 node3524Labels = _
    exact sound3524 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2015, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2008, h2011, h2016, h2242, h3524, h4080, reducedSource1696] using sourceEq2015 B hB

theorem rowSound1696 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1696 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1696, numericCheck1696, reducedZero1696 B hB hF, mul_zero]

theorem reducedZero1697 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1697 (mixedVector B) = 0 := by
  have h2117 : mixedVector B (Sum.inr 2117) = Sparse.eval nodeValue2117 (mixedVector B) := by
    change mixedMoment B node2117 node2117Labels = _
    exact sound2117 B hB hF
  have h2119 : mixedVector B (Sum.inr 2119) = Sparse.eval nodeValue2119 (mixedVector B) := by
    change mixedMoment B node2119 node2119Labels = _
    exact sound2119 B hB hF
  have h2122 : mixedVector B (Sum.inr 2122) = Sparse.eval nodeValue2122 (mixedVector B) := by
    change mixedMoment B node2122 node2122Labels = _
    exact sound2122 B hB hF
  have h2128 : mixedVector B (Sum.inr 2128) = Sparse.eval nodeValue2128 (mixedVector B) := by
    change mixedMoment B node2128 node2128Labels = _
    exact sound2128 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2016, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2117, h2119, h2122, h2128, h2215, h2681, h4082, reducedSource1697] using sourceEq2016 B hB

theorem rowSound1697 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1697 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1697, numericCheck1697, reducedZero1697 B hB hF, mul_zero]

theorem reducedZero1698 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1698 (mixedVector B) = 0 := by
  have h2070 : mixedVector B (Sum.inr 2070) = Sparse.eval nodeValue2070 (mixedVector B) := by
    change mixedMoment B node2070 node2070Labels = _
    exact sound2070 B hB hF
  have h2072 : mixedVector B (Sum.inr 2072) = Sparse.eval nodeValue2072 (mixedVector B) := by
    change mixedMoment B node2072 node2072Labels = _
    exact sound2072 B hB hF
  have h2075 : mixedVector B (Sum.inr 2075) = Sparse.eval nodeValue2075 (mixedVector B) := by
    change mixedMoment B node2075 node2075Labels = _
    exact sound2075 B hB hF
  have h2085 : mixedVector B (Sum.inr 2085) = Sparse.eval nodeValue2085 (mixedVector B) := by
    change mixedMoment B node2085 node2085Labels = _
    exact sound2085 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2017, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2070, h2072, h2075, h2085, h2190, h3557, h4080, reducedSource1698] using sourceEq2017 B hB

theorem rowSound1698 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1698 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1698, numericCheck1698, reducedZero1698 B hB hF, mul_zero]

theorem reducedZero1699 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1699 (mixedVector B) = 0 := by
  have h2453 : mixedVector B (Sum.inr 2453) = Sparse.eval nodeValue2453 (mixedVector B) := by
    change mixedMoment B node2453 node2453Labels = _
    exact sound2453 B hB hF
  have h2455 : mixedVector B (Sum.inr 2455) = Sparse.eval nodeValue2455 (mixedVector B) := by
    change mixedMoment B node2455 node2455Labels = _
    exact sound2455 B hB hF
  have h2459 : mixedVector B (Sum.inr 2459) = Sparse.eval nodeValue2459 (mixedVector B) := by
    change mixedMoment B node2459 node2459Labels = _
    exact sound2459 B hB hF
  have h2490 : mixedVector B (Sum.inr 2490) = Sparse.eval nodeValue2490 (mixedVector B) := by
    change mixedMoment B node2490 node2490Labels = _
    exact sound2490 B hB hF
  have h2697 : mixedVector B (Sum.inr 2697) = Sparse.eval nodeValue2697 (mixedVector B) := by
    change mixedMoment B node2697 node2697Labels = _
    exact sound2697 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2018, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2453, h2455, h2459, h2490, h2697, h3795, h4088, reducedSource1699] using sourceEq2018 B hB

theorem rowSound1699 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1699 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1699, numericCheck1699, reducedZero1699 B hB hF, mul_zero]

theorem reducedZero1700 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1700 (mixedVector B) = 0 := by
  have h2453 : mixedVector B (Sum.inr 2453) = Sparse.eval nodeValue2453 (mixedVector B) := by
    change mixedMoment B node2453 node2453Labels = _
    exact sound2453 B hB hF
  have h2533 : mixedVector B (Sum.inr 2533) = Sparse.eval nodeValue2533 (mixedVector B) := by
    change mixedMoment B node2533 node2533Labels = _
    exact sound2533 B hB hF
  have h2536 : mixedVector B (Sum.inr 2536) = Sparse.eval nodeValue2536 (mixedVector B) := by
    change mixedMoment B node2536 node2536Labels = _
    exact sound2536 B hB hF
  have h2565 : mixedVector B (Sum.inr 2565) = Sparse.eval nodeValue2565 (mixedVector B) := by
    change mixedMoment B node2565 node2565Labels = _
    exact sound2565 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2019, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2453, h2533, h2536, h2565, h2672, h3795, h4088, reducedSource1700] using sourceEq2019 B hB

theorem rowSound1700 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1700 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1700, numericCheck1700, reducedZero1700 B hB hF, mul_zero]

theorem reducedZero1701 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1701 (mixedVector B) = 0 := by
  have h1991 : mixedVector B (Sum.inr 1991) = Sparse.eval nodeValue1991 (mixedVector B) := by
    change mixedMoment B node1991 node1991Labels = _
    exact sound1991 B hB hF
  have h1993 : mixedVector B (Sum.inr 1993) = Sparse.eval nodeValue1993 (mixedVector B) := by
    change mixedMoment B node1993 node1993Labels = _
    exact sound1993 B hB hF
  have h1997 : mixedVector B (Sum.inr 1997) = Sparse.eval nodeValue1997 (mixedVector B) := by
    change mixedMoment B node1997 node1997Labels = _
    exact sound1997 B hB hF
  have h2030 : mixedVector B (Sum.inr 2030) = Sparse.eval nodeValue2030 (mixedVector B) := by
    change mixedMoment B node2030 node2030Labels = _
    exact sound2030 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2020, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1991, h1993, h1997, h2030, h2215, h3516, h4082, reducedSource1701] using sourceEq2020 B hB

theorem rowSound1701 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1701 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1701, numericCheck1701, reducedZero1701 B hB hF, mul_zero]

theorem reducedZero1704 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1704 (mixedVector B) = 0 := by
  have h1704 : mixedVector B (Sum.inr 1704) = Sparse.eval nodeValue1704 (mixedVector B) := by
    change mixedMoment B node1704 node1704Labels = _
    exact sound1704 B hB hF
  have h1722 : mixedVector B (Sum.inr 1722) = Sparse.eval nodeValue1722 (mixedVector B) := by
    change mixedMoment B node1722 node1722Labels = _
    exact sound1722 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1735 : mixedVector B (Sum.inr 1735) = Sparse.eval nodeValue1735 (mixedVector B) := by
    change mixedMoment B node1735 node1735Labels = _
    exact sound1735 B hB hF
  have h2189 : mixedVector B (Sum.inr 2189) = Sparse.eval nodeValue2189 (mixedVector B) := by
    change mixedMoment B node2189 node2189Labels = _
    exact sound2189 B hB hF
  have h2200 : mixedVector B (Sum.inr 2200) = Sparse.eval nodeValue2200 (mixedVector B) := by
    change mixedMoment B node2200 node2200Labels = _
    exact sound2200 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2212 : mixedVector B (Sum.inr 2212) = Sparse.eval nodeValue2212 (mixedVector B) := by
    change mixedMoment B node2212 node2212Labels = _
    exact sound2212 B hB hF
  have h2239 : mixedVector B (Sum.inr 2239) = Sparse.eval nodeValue2239 (mixedVector B) := by
    change mixedMoment B node2239 node2239Labels = _
    exact sound2239 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2258 : mixedVector B (Sum.inr 2258) = Sparse.eval nodeValue2258 (mixedVector B) := by
    change mixedMoment B node2258 node2258Labels = _
    exact sound2258 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2273 : mixedVector B (Sum.inr 2273) = Sparse.eval nodeValue2273 (mixedVector B) := by
    change mixedMoment B node2273 node2273Labels = _
    exact sound2273 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h2761 : mixedVector B (Sum.inr 2761) = Sparse.eval nodeValue2761 (mixedVector B) := by
    change mixedMoment B node2761 node2761Labels = _
    exact sound2761 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  simpa only [sourceForm2023, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1704, h1722, h1725, h1735, h2189, h2200, h2203, h2212, h2239, h2242, h2258, h2261, h2264, h2273, h2276, h2289, h2292, h2719, h2761, h2765, h2783, reducedSource1704] using sourceEq2023 B hB

theorem rowSound1704 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1704 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1704, numericCheck1704, reducedZero1704 B hB hF, mul_zero]

theorem reducedZero1705 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1705 (mixedVector B) = 0 := by
  have h952 : mixedVector B (Sum.inr 952) = Sparse.eval nodeValue952 (mixedVector B) := by
    change mixedMoment B node952 node952Labels = _
    exact sound952 B hB hF
  have h1830 : mixedVector B (Sum.inr 1830) = Sparse.eval nodeValue1830 (mixedVector B) := by
    change mixedMoment B node1830 node1830Labels = _
    exact sound1830 B hB hF
  have h1978 : mixedVector B (Sum.inr 1978) = Sparse.eval nodeValue1978 (mixedVector B) := by
    change mixedMoment B node1978 node1978Labels = _
    exact sound1978 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2024, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h952, h1830, h1978, h2109, h2115, h4084, reducedSource1705] using sourceEq2024 B hB

theorem rowSound1705 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1705 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1705, numericCheck1705, reducedZero1705 B hB hF, mul_zero]

theorem reducedZero1706 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1706 (mixedVector B) = 0 := by
  have h1157 : mixedVector B (Sum.inr 1157) = Sparse.eval nodeValue1157 (mixedVector B) := by
    change mixedMoment B node1157 node1157Labels = _
    exact sound1157 B hB hF
  have h1972 : mixedVector B (Sum.inr 1972) = Sparse.eval nodeValue1972 (mixedVector B) := by
    change mixedMoment B node1972 node1972Labels = _
    exact sound1972 B hB hF
  have h1978 : mixedVector B (Sum.inr 1978) = Sparse.eval nodeValue1978 (mixedVector B) := by
    change mixedMoment B node1978 node1978Labels = _
    exact sound1978 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h2588 : mixedVector B (Sum.inr 2588) = Sparse.eval nodeValue2588 (mixedVector B) := by
    change mixedMoment B node2588 node2588Labels = _
    exact sound2588 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2025, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1157, h1972, h1978, h2022, h2109, h2588, h4084, reducedSource1706] using sourceEq2025 B hB

theorem rowSound1706 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1706 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1706, numericCheck1706, reducedZero1706 B hB hF, mul_zero]

theorem reducedZero1707 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1707 (mixedVector B) = 0 := by
  have h943 : mixedVector B (Sum.inr 943) = Sparse.eval nodeValue943 (mixedVector B) := by
    change mixedMoment B node943 node943Labels = _
    exact sound943 B hB hF
  have h1823 : mixedVector B (Sum.inr 1823) = Sparse.eval nodeValue1823 (mixedVector B) := by
    change mixedMoment B node1823 node1823Labels = _
    exact sound1823 B hB hF
  have h1972 : mixedVector B (Sum.inr 1972) = Sparse.eval nodeValue1972 (mixedVector B) := by
    change mixedMoment B node1972 node1972Labels = _
    exact sound1972 B hB hF
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2026, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h943, h1823, h1972, h2106, h2109, h4084, reducedSource1707] using sourceEq2026 B hB

theorem rowSound1707 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1707 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1707, numericCheck1707, reducedZero1707 B hB hF, mul_zero]

theorem reducedZero1711 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1711 (mixedVector B) = 0 := by
  have h3255 : mixedVector B (Sum.inr 3255) = Sparse.eval nodeValue3255 (mixedVector B) := by
    change mixedMoment B node3255 node3255Labels = _
    exact sound3255 B hB hF
  have h3260 : mixedVector B (Sum.inr 3260) = Sparse.eval nodeValue3260 (mixedVector B) := by
    change mixedMoment B node3260 node3260Labels = _
    exact sound3260 B hB hF
  have h3262 : mixedVector B (Sum.inr 3262) = Sparse.eval nodeValue3262 (mixedVector B) := by
    change mixedMoment B node3262 node3262Labels = _
    exact sound3262 B hB hF
  have h3264 : mixedVector B (Sum.inr 3264) = Sparse.eval nodeValue3264 (mixedVector B) := by
    change mixedMoment B node3264 node3264Labels = _
    exact sound3264 B hB hF
  have h3266 : mixedVector B (Sum.inr 3266) = Sparse.eval nodeValue3266 (mixedVector B) := by
    change mixedMoment B node3266 node3266Labels = _
    exact sound3266 B hB hF
  have h3268 : mixedVector B (Sum.inr 3268) = Sparse.eval nodeValue3268 (mixedVector B) := by
    change mixedMoment B node3268 node3268Labels = _
    exact sound3268 B hB hF
  have h3272 : mixedVector B (Sum.inr 3272) = Sparse.eval nodeValue3272 (mixedVector B) := by
    change mixedMoment B node3272 node3272Labels = _
    exact sound3272 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3403 : mixedVector B (Sum.inr 3403) = Sparse.eval nodeValue3403 (mixedVector B) := by
    change mixedMoment B node3403 node3403Labels = _
    exact sound3403 B hB hF
  have h3411 : mixedVector B (Sum.inr 3411) = Sparse.eval nodeValue3411 (mixedVector B) := by
    change mixedMoment B node3411 node3411Labels = _
    exact sound3411 B hB hF
  have h3415 : mixedVector B (Sum.inr 3415) = Sparse.eval nodeValue3415 (mixedVector B) := by
    change mixedMoment B node3415 node3415Labels = _
    exact sound3415 B hB hF
  have h3449 : mixedVector B (Sum.inr 3449) = Sparse.eval nodeValue3449 (mixedVector B) := by
    change mixedMoment B node3449 node3449Labels = _
    exact sound3449 B hB hF
  have h3452 : mixedVector B (Sum.inr 3452) = Sparse.eval nodeValue3452 (mixedVector B) := by
    change mixedMoment B node3452 node3452Labels = _
    exact sound3452 B hB hF
  have h3458 : mixedVector B (Sum.inr 3458) = Sparse.eval nodeValue3458 (mixedVector B) := by
    change mixedMoment B node3458 node3458Labels = _
    exact sound3458 B hB hF
  have h3459 : mixedVector B (Sum.inr 3459) = Sparse.eval nodeValue3459 (mixedVector B) := by
    change mixedMoment B node3459 node3459Labels = _
    exact sound3459 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3470 : mixedVector B (Sum.inr 3470) = Sparse.eval nodeValue3470 (mixedVector B) := by
    change mixedMoment B node3470 node3470Labels = _
    exact sound3470 B hB hF
  have h3475 : mixedVector B (Sum.inr 3475) = Sparse.eval nodeValue3475 (mixedVector B) := by
    change mixedMoment B node3475 node3475Labels = _
    exact sound3475 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3484 : mixedVector B (Sum.inr 3484) = Sparse.eval nodeValue3484 (mixedVector B) := by
    change mixedMoment B node3484 node3484Labels = _
    exact sound3484 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  simpa only [sourceForm2032, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3255, h3260, h3262, h3264, h3266, h3268, h3272, h3291, h3300, h3403, h3411, h3415, h3449, h3452, h3458, h3459, h3468, h3470, h3475, h3478, h3484, h3513, h3514, h3522, h3530, h3533, h3545, h3547, h3564, h3807, reducedSource1711] using sourceEq2032 B hB

theorem rowSound1711 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1711 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1711, numericCheck1711, reducedZero1711 B hB hF, mul_zero]

theorem sourceRowsAt1696 : MixedData.sourceRows (1696 : Fin 2425) =
    MixedData.row1696 := by decide +kernel

theorem sourceRowsAt1697 : MixedData.sourceRows (1697 : Fin 2425) =
    MixedData.row1697 := by decide +kernel

theorem sourceRowsAt1698 : MixedData.sourceRows (1698 : Fin 2425) =
    MixedData.row1698 := by decide +kernel

theorem sourceRowsAt1699 : MixedData.sourceRows (1699 : Fin 2425) =
    MixedData.row1699 := by decide +kernel

theorem sourceRowsAt1700 : MixedData.sourceRows (1700 : Fin 2425) =
    MixedData.row1700 := by decide +kernel

theorem sourceRowsAt1701 : MixedData.sourceRows (1701 : Fin 2425) =
    MixedData.row1701 := by decide +kernel

theorem sourceRowsAt1702 : MixedData.sourceRows (1702 : Fin 2425) =
    MixedData.row1702 := by decide +kernel

theorem sourceRowsAt1703 : MixedData.sourceRows (1703 : Fin 2425) =
    MixedData.row1703 := by decide +kernel

theorem sourceRowsAt1704 : MixedData.sourceRows (1704 : Fin 2425) =
    MixedData.row1704 := by decide +kernel

theorem sourceRowsAt1705 : MixedData.sourceRows (1705 : Fin 2425) =
    MixedData.row1705 := by decide +kernel

theorem sourceRowsAt1706 : MixedData.sourceRows (1706 : Fin 2425) =
    MixedData.row1706 := by decide +kernel

theorem sourceRowsAt1707 : MixedData.sourceRows (1707 : Fin 2425) =
    MixedData.row1707 := by decide +kernel

theorem sourceRowsAt1708 : MixedData.sourceRows (1708 : Fin 2425) =
    MixedData.row1708 := by decide +kernel

theorem sourceRowsAt1709 : MixedData.sourceRows (1709 : Fin 2425) =
    MixedData.row1709 := by decide +kernel

theorem sourceRowsAt1710 : MixedData.sourceRows (1710 : Fin 2425) =
    MixedData.row1710 := by decide +kernel

theorem sourceRowsAt1711 : MixedData.sourceRows (1711 : Fin 2425) =
    MixedData.row1711 := by decide +kernel

theorem chunkSound106_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 106) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1696 ∨ k.val = 1697 ∨ k.val = 1698 ∨ k.val = 1699 ∨ k.val = 1700 ∨ k.val = 1701 ∨ k.val = 1702 ∨ k.val = 1703 ∨ k.val = 1704 ∨ k.val = 1705 ∨ k.val = 1706 ∨ k.val = 1707 ∨ k.val = 1708 ∨ k.val = 1709 ∨ k.val = 1710 ∨ k.val = 1711 := by omega
  rcases heq with h1696 | h1697 | h1698 | h1699 | h1700 | h1701 | h1702 | h1703 | h1704 | h1705 | h1706 | h1707 | h1708 | h1709 | h1710 | h1711
  · have he : k = (1696 : Fin 2425) := Fin.ext h1696
    subst k
    rw [sourceRowsAt1696]
    exact rowSound1696 B hB hF
  · have he : k = (1697 : Fin 2425) := Fin.ext h1697
    subst k
    rw [sourceRowsAt1697]
    exact rowSound1697 B hB hF
  · have he : k = (1698 : Fin 2425) := Fin.ext h1698
    subst k
    rw [sourceRowsAt1698]
    exact rowSound1698 B hB hF
  · have he : k = (1699 : Fin 2425) := Fin.ext h1699
    subst k
    rw [sourceRowsAt1699]
    exact rowSound1699 B hB hF
  · have he : k = (1700 : Fin 2425) := Fin.ext h1700
    subst k
    rw [sourceRowsAt1700]
    exact rowSound1700 B hB hF
  · have he : k = (1701 : Fin 2425) := Fin.ext h1701
    subst k
    rw [sourceRowsAt1701]
    exact rowSound1701 B hB hF
  · have he : k = (1702 : Fin 2425) := Fin.ext h1702
    subst k
    rw [sourceRowsAt1702]
    exact rowSound1702_e B hB hF
  · have he : k = (1703 : Fin 2425) := Fin.ext h1703
    subst k
    rw [sourceRowsAt1703]
    exact rowSound1703_e B hB hF
  · have he : k = (1704 : Fin 2425) := Fin.ext h1704
    subst k
    rw [sourceRowsAt1704]
    exact rowSound1704 B hB hF
  · have he : k = (1705 : Fin 2425) := Fin.ext h1705
    subst k
    rw [sourceRowsAt1705]
    exact rowSound1705 B hB hF
  · have he : k = (1706 : Fin 2425) := Fin.ext h1706
    subst k
    rw [sourceRowsAt1706]
    exact rowSound1706 B hB hF
  · have he : k = (1707 : Fin 2425) := Fin.ext h1707
    subst k
    rw [sourceRowsAt1707]
    exact rowSound1707 B hB hF
  · have he : k = (1708 : Fin 2425) := Fin.ext h1708
    subst k
    rw [sourceRowsAt1708]
    exact rowSound1708_e B hB hF
  · have he : k = (1709 : Fin 2425) := Fin.ext h1709
    subst k
    rw [sourceRowsAt1709]
    exact rowSound1709_e B hB hF
  · have he : k = (1710 : Fin 2425) := Fin.ext h1710
    subst k
    rw [sourceRowsAt1710]
    exact rowSound1710_e B hB hF
  · have he : k = (1711 : Fin 2425) := Fin.ext h1711
    subst k
    rw [sourceRowsAt1711]
    exact rowSound1711 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106_e_oai
