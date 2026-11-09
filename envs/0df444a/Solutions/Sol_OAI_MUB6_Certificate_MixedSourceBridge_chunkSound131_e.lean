-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:55:50.439614+00:00
-- url     : https://prove2.me/submissions/762cbaf9-7747-4501-95f0-25d05f461b10

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2096_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2097_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2099_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2100_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2102_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2103_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2105_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2107_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2108_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2109_e

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

theorem mixedMoment_zero_first_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (hA : ∀ i, A i 0 = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i j.succ) (fun j => label j.succ) := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  unfold mixedIntegrand
  rw [Fin.prod_univ_succ]
  have hz : (fun i => A i 0) = 0 := funext hA
  rw [hz, rowFourier_zero, one_mul]

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

theorem delete_zero_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (σ : Equiv.Perm (Fin (n + 1))) (hz : ∀ i, A i (σ 0) = 0) :
    mixedMoment B A label =
      mixedMoment B (fun i j => A i (σ j.succ)) (fun j => label (σ j.succ)) := by
  rw [← mixedMoment_factor_permutation B A label σ]
  exact mixedMoment_zero_first_factor B _ _ hz

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14365 raw14365Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw14365 raw14365Labels = mixedMoment B raw14365step0 raw14365step0Labels := by
      have hz : ∀ i, raw14365 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14365step0 = (fun i j => raw14365 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14365step0 raw14365; decide +kernel
      have hl : raw14365step0Labels = (fun j => raw14365Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14365 raw14365Labels permutation6 hz
    _ = mixedMoment B node4079 node4079Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18335 raw18335Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw18335 raw18335Labels = mixedMoment B raw18335step0 raw18335step0Labels := by
      have hz : ∀ j, raw18335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18335step0 = (fun i j => raw18335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18335step0 raw18335; decide +kernel
      have hl : raw18335step0Labels = raw18335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18335 raw18335Labels permutation434 hz
    mixedMoment B raw18335step0 raw18335step0Labels = mixedMoment B raw18335step1 raw18335step1Labels := by
      have hz : ∀ i, raw18335step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18335step1 = (fun i j => raw18335step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18335step1 raw18335step0; decide +kernel
      have hl : raw18335step1Labels = (fun j => raw18335step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18335step0 raw18335step0Labels permutation6 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical18337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18337 raw18337Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw18337 raw18337Labels = mixedMoment B raw18337step0 raw18337step0Labels := by
      have hz : ∀ j, raw18337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18337step0 = (fun i j => raw18337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18337step0 raw18337; decide +kernel
      have hl : raw18337step0Labels = raw18337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18337 raw18337Labels permutation346 hz
    mixedMoment B raw18337step0 raw18337step0Labels = mixedMoment B raw18337step1 raw18337step1Labels := by
      have hz : ∀ i, raw18337step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18337step1 = (fun i j => raw18337step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18337step1 raw18337step0; decide +kernel
      have hl : raw18337step1Labels = (fun j => raw18337step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18337step0 raw18337step0Labels permutation6 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical18338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18338 raw18338Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw18338 raw18338Labels = mixedMoment B raw18338step0 raw18338step0Labels := by
      have hz : ∀ i, raw18338 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18338step0 = (fun i j => raw18338 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18338step0 raw18338; decide +kernel
      have hl : raw18338step0Labels = (fun j => raw18338Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18338 raw18338Labels permutation6 hz
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical18339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18339 raw18339Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw18339 raw18339Labels = mixedMoment B raw18339step0 raw18339step0Labels := by
      have hz : ∀ j, raw18339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18339step0 = (fun i j => raw18339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18339step0 raw18339; decide +kernel
      have hl : raw18339step0Labels = raw18339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18339 raw18339Labels permutation434 hz
    mixedMoment B raw18339step0 raw18339step0Labels = mixedMoment B raw18339step1 raw18339step1Labels := by
      have hz : ∀ j, raw18339step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18339step1 = (fun i j => raw18339step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18339step1 raw18339step0; decide +kernel
      have hl : raw18339step1Labels = raw18339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18339step0 raw18339step0Labels permutation80 hz
    mixedMoment B raw18339step1 raw18339step1Labels = mixedMoment B raw18339step2 raw18339step2Labels := by
      have hz : ∀ i, raw18339step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18339step2 = (fun i j => raw18339step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18339step2 raw18339step1; decide +kernel
      have hl : raw18339step2Labels = (fun j => raw18339step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18339step1 raw18339step1Labels permutation6 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

theorem canonical18340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18340 raw18340Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw18340 raw18340Labels = mixedMoment B raw18340step0 raw18340step0Labels := by
      have hz : ∀ j, raw18340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18340step0 = (fun i j => raw18340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18340step0 raw18340; decide +kernel
      have hl : raw18340step0Labels = raw18340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18340 raw18340Labels permutation434 hz
    mixedMoment B raw18340step0 raw18340step0Labels = mixedMoment B raw18340step1 raw18340step1Labels := by
      have hz : ∀ i, raw18340step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18340step1 = (fun i j => raw18340step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18340step1 raw18340step0; decide +kernel
      have hl : raw18340step1Labels = (fun j => raw18340step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18340step0 raw18340step0Labels permutation6 hz
    mixedMoment B raw18340step1 raw18340step1Labels = mixedMoment B raw18340step2 raw18340step2Labels := by
      have ha : raw18340step2 = (fun i j => raw18340step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18340step2 raw18340step1; decide +kernel
      have hl : raw18340step2Labels = raw18340step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18340step1 raw18340step1Labels permutation125 permutation0
    mixedMoment B raw18340step2 raw18340step2Labels = mixedMoment B raw18340step3 raw18340step3Labels := by
      have ha : raw18340step3 = -raw18340step2 := by apply Matrix.ext; change ∀ i j, raw18340step3 i j = -(raw18340step2 i j); unfold raw18340step3 raw18340step2; decide +kernel
      have hl : raw18340step3Labels = raw18340step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical18342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18342 raw18342Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw18342 raw18342Labels = mixedMoment B raw18342step0 raw18342step0Labels := by
      have hz : ∀ j, raw18342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18342step0 = (fun i j => raw18342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18342step0 raw18342; decide +kernel
      have hl : raw18342step0Labels = raw18342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18342 raw18342Labels permutation434 hz
    mixedMoment B raw18342step0 raw18342step0Labels = mixedMoment B raw18342step1 raw18342step1Labels := by
      have hz : ∀ j, raw18342step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18342step1 = (fun i j => raw18342step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18342step1 raw18342step0; decide +kernel
      have hl : raw18342step1Labels = raw18342step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18342step0 raw18342step0Labels permutation80 hz
    mixedMoment B raw18342step1 raw18342step1Labels = mixedMoment B raw18342step2 raw18342step2Labels := by
      have hz : ∀ i, raw18342step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18342step2 = (fun i j => raw18342step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18342step2 raw18342step1; decide +kernel
      have hl : raw18342step2Labels = (fun j => raw18342step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18342step1 raw18342step1Labels permutation6 hz
    mixedMoment B raw18342step2 raw18342step2Labels = mixedMoment B raw18342step3 raw18342step3Labels := by
      have ha : raw18342step3 = (fun i j => raw18342step2 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18342step3 raw18342step2; decide +kernel
      have hl : raw18342step3Labels = raw18342step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18342step2 raw18342step2Labels permutation30 permutation0
    mixedMoment B raw18342step3 raw18342step3Labels = mixedMoment B raw18342step4 raw18342step4Labels := by
      have ha : raw18342step4 = -raw18342step3 := by apply Matrix.ext; change ∀ i j, raw18342step4 i j = -(raw18342step3 i j); unfold raw18342step4 raw18342step3; decide +kernel
      have hl : raw18342step4Labels = raw18342step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical18343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18343 raw18343Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw18343 raw18343Labels = mixedMoment B raw18343step0 raw18343step0Labels := by
      have hz : ∀ j, raw18343 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18343step0 = (fun i j => raw18343 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18343step0 raw18343; decide +kernel
      have hl : raw18343step0Labels = raw18343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18343 raw18343Labels permutation434 hz
    mixedMoment B raw18343step0 raw18343step0Labels = mixedMoment B raw18343step1 raw18343step1Labels := by
      have hz : ∀ i, raw18343step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18343step1 = (fun i j => raw18343step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18343step1 raw18343step0; decide +kernel
      have hl : raw18343step1Labels = (fun j => raw18343step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18343step0 raw18343step0Labels permutation6 hz
    mixedMoment B raw18343step1 raw18343step1Labels = mixedMoment B raw18343step2 raw18343step2Labels := by
      have ha : raw18343step2 = (fun i j => raw18343step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18343step2 raw18343step1; decide +kernel
      have hl : raw18343step2Labels = raw18343step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18343step1 raw18343step1Labels permutation149 permutation0
    mixedMoment B raw18343step2 raw18343step2Labels = mixedMoment B raw18343step3 raw18343step3Labels := by
      have ha : raw18343step3 = -raw18343step2 := by apply Matrix.ext; change ∀ i j, raw18343step3 i j = -(raw18343step2 i j); unfold raw18343step3 raw18343step2; decide +kernel
      have hl : raw18343step3Labels = raw18343step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19360 raw19360Labels = mixedMoment B node4087 node4087Labels := by
  calc
    mixedMoment B raw19360 raw19360Labels = mixedMoment B raw19360step0 raw19360step0Labels := by
      have hz : ∀ i, raw19360 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19360step0 = (fun i j => raw19360 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19360step0 raw19360; decide +kernel
      have hl : raw19360step0Labels = (fun j => raw19360Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19360 raw19360Labels permutation6 hz
    _ = mixedMoment B node4087 node4087Labels := by rfl

theorem canonical19361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19361 raw19361Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19361 raw19361Labels = mixedMoment B raw19361step0 raw19361step0Labels := by
      have hz : ∀ j, raw19361 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19361step0 = (fun i j => raw19361 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19361step0 raw19361; decide +kernel
      have hl : raw19361step0Labels = raw19361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19361 raw19361Labels permutation520 hz
    mixedMoment B raw19361step0 raw19361step0Labels = mixedMoment B raw19361step1 raw19361step1Labels := by
      have hz : ∀ i, raw19361step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19361step1 = (fun i j => raw19361step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19361step1 raw19361step0; decide +kernel
      have hl : raw19361step1Labels = (fun j => raw19361step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19361step0 raw19361step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical19362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19362 raw19362Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19362 raw19362Labels = mixedMoment B raw19362step0 raw19362step0Labels := by
      have hz : ∀ j, raw19362 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19362step0 = (fun i j => raw19362 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19362step0 raw19362; decide +kernel
      have hl : raw19362step0Labels = raw19362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19362 raw19362Labels permutation590 hz
    mixedMoment B raw19362step0 raw19362step0Labels = mixedMoment B raw19362step1 raw19362step1Labels := by
      have hz : ∀ i, raw19362step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19362step1 = (fun i j => raw19362step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19362step1 raw19362step0; decide +kernel
      have hl : raw19362step1Labels = (fun j => raw19362step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19362step0 raw19362step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical19363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19363 raw19363Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw19363 raw19363Labels = mixedMoment B raw19363step0 raw19363step0Labels := by
      have hz : ∀ j, raw19363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19363step0 = (fun i j => raw19363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19363step0 raw19363; decide +kernel
      have hl : raw19363step0Labels = raw19363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19363 raw19363Labels permutation346 hz
    mixedMoment B raw19363step0 raw19363step0Labels = mixedMoment B raw19363step1 raw19363step1Labels := by
      have hz : ∀ i, raw19363step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19363step1 = (fun i j => raw19363step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19363step1 raw19363step0; decide +kernel
      have hl : raw19363step1Labels = (fun j => raw19363step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19363step0 raw19363step0Labels permutation6 hz
    mixedMoment B raw19363step1 raw19363step1Labels = mixedMoment B raw19363step2 raw19363step2Labels := by
      have ha : raw19363step2 = (fun i j => raw19363step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19363step2 raw19363step1; decide +kernel
      have hl : raw19363step2Labels = raw19363step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19363step1 raw19363step1Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical19364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19364 raw19364Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19364 raw19364Labels = mixedMoment B raw19364step0 raw19364step0Labels := by
      have hz : ∀ i, raw19364 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19364step0 = (fun i j => raw19364 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19364step0 raw19364; decide +kernel
      have hl : raw19364step0Labels = (fun j => raw19364Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19364 raw19364Labels permutation6 hz
    mixedMoment B raw19364step0 raw19364step0Labels = mixedMoment B raw19364step1 raw19364step1Labels := by
      have ha : raw19364step1 = (fun i j => raw19364step0 (permutation155 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19364step1 raw19364step0; decide +kernel
      have hl : raw19364step1Labels = raw19364step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19364step0 raw19364step0Labels permutation155 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical19367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19367 raw19367Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw19367 raw19367Labels = mixedMoment B raw19367step0 raw19367step0Labels := by
      have hz : ∀ j, raw19367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19367step0 = (fun i j => raw19367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19367step0 raw19367; decide +kernel
      have hl : raw19367step0Labels = raw19367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19367 raw19367Labels permutation346 hz
    mixedMoment B raw19367step0 raw19367step0Labels = mixedMoment B raw19367step1 raw19367step1Labels := by
      have hz : ∀ i, raw19367step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19367step1 = (fun i j => raw19367step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19367step1 raw19367step0; decide +kernel
      have hl : raw19367step1Labels = (fun j => raw19367step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19367step0 raw19367step0Labels permutation6 hz
    mixedMoment B raw19367step1 raw19367step1Labels = mixedMoment B raw19367step2 raw19367step2Labels := by
      have ha : raw19367step2 = (fun i j => raw19367step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19367step2 raw19367step1; decide +kernel
      have hl : raw19367step2Labels = raw19367step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19367step1 raw19367step1Labels permutation33 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical19368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19368 raw19368Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19368 raw19368Labels = mixedMoment B raw19368step0 raw19368step0Labels := by
      have hz : ∀ i, raw19368 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19368step0 = (fun i j => raw19368 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19368step0 raw19368; decide +kernel
      have hl : raw19368step0Labels = (fun j => raw19368Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19368 raw19368Labels permutation6 hz
    mixedMoment B raw19368step0 raw19368step0Labels = mixedMoment B raw19368step1 raw19368step1Labels := by
      have ha : raw19368step1 = (fun i j => raw19368step0 (permutation153 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19368step1 raw19368step0; decide +kernel
      have hl : raw19368step1Labels = raw19368step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19368step0 raw19368step0Labels permutation153 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical19404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19404 raw19404Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19404 raw19404Labels = mixedMoment B raw19404step0 raw19404step0Labels := by
      have hz : ∀ i, raw19404 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19404step0 = (fun i j => raw19404 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19404step0 raw19404; decide +kernel
      have hl : raw19404step0Labels = (fun j => raw19404Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19404 raw19404Labels permutation6 hz
    mixedMoment B raw19404step0 raw19404step0Labels = mixedMoment B raw19404step1 raw19404step1Labels := by
      have ha : raw19404step1 = (fun i j => raw19404step0 (permutation265 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19404step1 raw19404step0; decide +kernel
      have hl : raw19404step1Labels = raw19404step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19404step0 raw19404step0Labels permutation265 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical19405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19405 raw19405Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19405 raw19405Labels = mixedMoment B raw19405step0 raw19405step0Labels := by
      have hz : ∀ i, raw19405 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19405step0 = (fun i j => raw19405 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19405step0 raw19405; decide +kernel
      have hl : raw19405step0Labels = (fun j => raw19405Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19405 raw19405Labels permutation6 hz
    mixedMoment B raw19405step0 raw19405step0Labels = mixedMoment B raw19405step1 raw19405step1Labels := by
      have ha : raw19405step1 = (fun i j => raw19405step0 (permutation346 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19405step1 raw19405step0; decide +kernel
      have hl : raw19405step1Labels = raw19405step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19405step0 raw19405step0Labels permutation346 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical19406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19406 raw19406Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19406 raw19406Labels = mixedMoment B raw19406step0 raw19406step0Labels := by
      have hz : ∀ j, raw19406 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19406step0 = (fun i j => raw19406 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19406step0 raw19406; decide +kernel
      have hl : raw19406step0Labels = raw19406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19406 raw19406Labels permutation520 hz
    mixedMoment B raw19406step0 raw19406step0Labels = mixedMoment B raw19406step1 raw19406step1Labels := by
      have hz : ∀ i, raw19406step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19406step1 = (fun i j => raw19406step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19406step1 raw19406step0; decide +kernel
      have hl : raw19406step1Labels = (fun j => raw19406step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19406step0 raw19406step0Labels permutation6 hz
    mixedMoment B raw19406step1 raw19406step1Labels = mixedMoment B raw19406step2 raw19406step2Labels := by
      have ha : raw19406step2 = (fun i j => raw19406step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19406step2 raw19406step1; decide +kernel
      have hl : raw19406step2Labels = raw19406step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19406step1 raw19406step1Labels permutation146 permutation0
    mixedMoment B raw19406step2 raw19406step2Labels = mixedMoment B raw19406step3 raw19406step3Labels := by
      have ha : raw19406step3 = -raw19406step2 := by apply Matrix.ext; change ∀ i j, raw19406step3 i j = -(raw19406step2 i j); unfold raw19406step3 raw19406step2; decide +kernel
      have hl : raw19406step3Labels = raw19406step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2925 raw2925Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2925 raw2925Labels = mixedMoment B raw2925step0 raw2925step0Labels := by
      have hz : ∀ j, raw2925 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2925step0 = (fun i j => raw2925 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2925step0 raw2925; decide +kernel
      have hl : raw2925step0Labels = raw2925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2925 raw2925Labels permutation520 hz
    mixedMoment B raw2925step0 raw2925step0Labels = mixedMoment B raw2925step1 raw2925step1Labels := by
      have hz : ∀ j, raw2925step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2925step1 = (fun i j => raw2925step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2925step1 raw2925step0; decide +kernel
      have hl : raw2925step1Labels = raw2925step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2925step0 raw2925step0Labels permutation80 hz
    mixedMoment B raw2925step1 raw2925step1Labels = mixedMoment B raw2925step2 raw2925step2Labels := by
      have hz : ∀ i, raw2925step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2925step2 = (fun i j => raw2925step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2925step2 raw2925step1; decide +kernel
      have hl : raw2925step2Labels = (fun j => raw2925step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2925step1 raw2925step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2926 raw2926Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2926 raw2926Labels = mixedMoment B raw2926step0 raw2926step0Labels := by
      have hz : ∀ j, raw2926 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2926step0 = (fun i j => raw2926 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2926step0 raw2926; decide +kernel
      have hl : raw2926step0Labels = raw2926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2926 raw2926Labels permutation520 hz
    mixedMoment B raw2926step0 raw2926step0Labels = mixedMoment B raw2926step1 raw2926step1Labels := by
      have hz : ∀ j, raw2926step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2926step1 = (fun i j => raw2926step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2926step1 raw2926step0; decide +kernel
      have hl : raw2926step1Labels = raw2926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2926step0 raw2926step0Labels permutation56 hz
    mixedMoment B raw2926step1 raw2926step1Labels = mixedMoment B raw2926step2 raw2926step2Labels := by
      have hz : ∀ i, raw2926step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2926step2 = (fun i j => raw2926step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2926step2 raw2926step1; decide +kernel
      have hl : raw2926step2Labels = (fun j => raw2926step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2926step1 raw2926step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2930 raw2930Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2930 raw2930Labels = mixedMoment B raw2930step0 raw2930step0Labels := by
      have hz : ∀ j, raw2930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2930step0 = (fun i j => raw2930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2930step0 raw2930; decide +kernel
      have hl : raw2930step0Labels = raw2930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930 raw2930Labels permutation434 hz
    mixedMoment B raw2930step0 raw2930step0Labels = mixedMoment B raw2930step1 raw2930step1Labels := by
      have hz : ∀ j, raw2930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2930step1 = (fun i j => raw2930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2930step1 raw2930step0; decide +kernel
      have hl : raw2930step1Labels = raw2930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930step0 raw2930step0Labels permutation80 hz
    mixedMoment B raw2930step1 raw2930step1Labels = mixedMoment B raw2930step2 raw2930step2Labels := by
      have hz : ∀ i, raw2930step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2930step2 = (fun i j => raw2930step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2930step2 raw2930step1; decide +kernel
      have hl : raw2930step2Labels = (fun j => raw2930step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2930step1 raw2930step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2931 raw2931Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2931 raw2931Labels = mixedMoment B raw2931step0 raw2931step0Labels := by
      have hz : ∀ j, raw2931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2931step0 = (fun i j => raw2931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2931step0 raw2931; decide +kernel
      have hl : raw2931step0Labels = raw2931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2931 raw2931Labels permutation434 hz
    mixedMoment B raw2931step0 raw2931step0Labels = mixedMoment B raw2931step1 raw2931step1Labels := by
      have hz : ∀ j, raw2931step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2931step1 = (fun i j => raw2931step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2931step1 raw2931step0; decide +kernel
      have hl : raw2931step1Labels = raw2931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2931step0 raw2931step0Labels permutation56 hz
    mixedMoment B raw2931step1 raw2931step1Labels = mixedMoment B raw2931step2 raw2931step2Labels := by
      have hz : ∀ i, raw2931step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2931step2 = (fun i j => raw2931step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2931step2 raw2931step1; decide +kernel
      have hl : raw2931step2Labels = (fun j => raw2931step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2931step1 raw2931step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical228
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29297 raw29297Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw29297 raw29297Labels = mixedMoment B raw29297step0 raw29297step0Labels := by
      have hz : ∀ j, raw29297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29297step0 = (fun i j => raw29297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29297step0 raw29297; decide +kernel
      have hl : raw29297step0Labels = raw29297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29297 raw29297Labels permutation346 hz
    mixedMoment B raw29297step0 raw29297step0Labels = mixedMoment B raw29297step1 raw29297step1Labels := by
      have hz : ∀ i, raw29297step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29297step1 = (fun i j => raw29297step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29297step1 raw29297step0; decide +kernel
      have hl : raw29297step1Labels = (fun j => raw29297step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29297step0 raw29297step0Labels permutation6 hz
    _ = mixedMoment B node4074 node4074Labels := by rfl

theorem canonical29298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29298 raw29298Labels = mixedMoment B node4077 node4077Labels := by
  calc
    mixedMoment B raw29298 raw29298Labels = mixedMoment B raw29298step0 raw29298step0Labels := by
      have hz : ∀ i, raw29298 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29298step0 = (fun i j => raw29298 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29298step0 raw29298; decide +kernel
      have hl : raw29298step0Labels = (fun j => raw29298Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29298 raw29298Labels permutation6 hz
    _ = mixedMoment B node4077 node4077Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31880 raw31880Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw31880 raw31880Labels = mixedMoment B raw31880step0 raw31880step0Labels := by
      have hz : ∀ j, raw31880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31880step0 = (fun i j => raw31880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31880step0 raw31880; decide +kernel
      have hl : raw31880step0Labels = raw31880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31880 raw31880Labels permutation346 hz
    mixedMoment B raw31880step0 raw31880step0Labels = mixedMoment B raw31880step1 raw31880step1Labels := by
      have hz : ∀ i, raw31880step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31880step1 = (fun i j => raw31880step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31880step1 raw31880step0; decide +kernel
      have hl : raw31880step1Labels = (fun j => raw31880step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31880step0 raw31880step0Labels permutation6 hz
    _ = mixedMoment B node4075 node4075Labels := by rfl

theorem canonical31881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31881 raw31881Labels = mixedMoment B node4078 node4078Labels := by
  calc
    mixedMoment B raw31881 raw31881Labels = mixedMoment B raw31881step0 raw31881step0Labels := by
      have hz : ∀ i, raw31881 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31881step0 = (fun i j => raw31881 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31881step0 raw31881; decide +kernel
      have hl : raw31881step0Labels = (fun j => raw31881Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31881 raw31881Labels permutation6 hz
    _ = mixedMoment B node4078 node4078Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3328 raw3328Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3328 raw3328Labels = mixedMoment B raw3328step0 raw3328step0Labels := by
      have hz : ∀ j, raw3328 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3328step0 = (fun i j => raw3328 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3328step0 raw3328; decide +kernel
      have hl : raw3328step0Labels = raw3328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3328 raw3328Labels permutation434 hz
    mixedMoment B raw3328step0 raw3328step0Labels = mixedMoment B raw3328step1 raw3328step1Labels := by
      have hz : ∀ i, raw3328step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3328step1 = (fun i j => raw3328step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3328step1 raw3328step0; decide +kernel
      have hl : raw3328step1Labels = (fun j => raw3328step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3328step0 raw3328step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3332 raw3332Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3332 raw3332Labels = mixedMoment B raw3332step0 raw3332step0Labels := by
      have hz : ∀ j, raw3332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3332step0 = (fun i j => raw3332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3332step0 raw3332; decide +kernel
      have hl : raw3332step0Labels = raw3332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3332 raw3332Labels permutation346 hz
    mixedMoment B raw3332step0 raw3332step0Labels = mixedMoment B raw3332step1 raw3332step1Labels := by
      have hz : ∀ i, raw3332step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3332step1 = (fun i j => raw3332step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3332step1 raw3332step0; decide +kernel
      have hl : raw3332step1Labels = (fun j => raw3332step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3332step0 raw3332step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3333 raw3333Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3333 raw3333Labels = mixedMoment B raw3333step0 raw3333step0Labels := by
      have hz : ∀ j, raw3333 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3333step0 = (fun i j => raw3333 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3333step0 raw3333; decide +kernel
      have hl : raw3333step0Labels = raw3333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3333 raw3333Labels permutation265 hz
    mixedMoment B raw3333step0 raw3333step0Labels = mixedMoment B raw3333step1 raw3333step1Labels := by
      have hz : ∀ i, raw3333step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3333step1 = (fun i j => raw3333step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3333step1 raw3333step0; decide +kernel
      have hl : raw3333step1Labels = (fun j => raw3333step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3333step0 raw3333step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3436 raw3436Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3436 raw3436Labels = mixedMoment B raw3436step0 raw3436step0Labels := by
      have hz : ∀ j, raw3436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3436step0 = (fun i j => raw3436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3436step0 raw3436; decide +kernel
      have hl : raw3436step0Labels = raw3436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3436 raw3436Labels permutation434 hz
    mixedMoment B raw3436step0 raw3436step0Labels = mixedMoment B raw3436step1 raw3436step1Labels := by
      have hz : ∀ i, raw3436step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3436step1 = (fun i j => raw3436step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3436step1 raw3436step0; decide +kernel
      have hl : raw3436step1Labels = (fun j => raw3436step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3436step0 raw3436step0Labels permutation6 hz
    mixedMoment B raw3436step1 raw3436step1Labels = mixedMoment B raw3436step2 raw3436step2Labels := by
      have ha : raw3436step2 = (fun i j => raw3436step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3436step2 raw3436step1; decide +kernel
      have hl : raw3436step2Labels = raw3436step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3436step1 raw3436step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3440 raw3440Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3440 raw3440Labels = mixedMoment B raw3440step0 raw3440step0Labels := by
      have hz : ∀ j, raw3440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3440step0 = (fun i j => raw3440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3440step0 raw3440; decide +kernel
      have hl : raw3440step0Labels = raw3440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3440 raw3440Labels permutation346 hz
    mixedMoment B raw3440step0 raw3440step0Labels = mixedMoment B raw3440step1 raw3440step1Labels := by
      have hz : ∀ i, raw3440step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3440step1 = (fun i j => raw3440step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3440step1 raw3440step0; decide +kernel
      have hl : raw3440step1Labels = (fun j => raw3440step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3440step0 raw3440step0Labels permutation6 hz
    mixedMoment B raw3440step1 raw3440step1Labels = mixedMoment B raw3440step2 raw3440step2Labels := by
      have ha : raw3440step2 = (fun i j => raw3440step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3440step2 raw3440step1; decide +kernel
      have hl : raw3440step2Labels = raw3440step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3440step1 raw3440step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3441 raw3441Labels = mixedMoment B node4095 node4095Labels := by
  calc
    mixedMoment B raw3441 raw3441Labels = mixedMoment B raw3441step0 raw3441step0Labels := by
      have hz : ∀ i, raw3441 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3441step0 = (fun i j => raw3441 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3441step0 raw3441; decide +kernel
      have hl : raw3441step0Labels = (fun j => raw3441Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3441 raw3441Labels permutation6 hz
    _ = mixedMoment B node4095 node4095Labels := by rfl

theorem canonical3448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3448 raw3448Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3448 raw3448Labels = mixedMoment B raw3448step0 raw3448step0Labels := by
      have hz : ∀ j, raw3448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3448step0 = (fun i j => raw3448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3448step0 raw3448; decide +kernel
      have hl : raw3448step0Labels = raw3448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3448 raw3448Labels permutation434 hz
    mixedMoment B raw3448step0 raw3448step0Labels = mixedMoment B raw3448step1 raw3448step1Labels := by
      have hz : ∀ j, raw3448step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3448step1 = (fun i j => raw3448step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3448step1 raw3448step0; decide +kernel
      have hl : raw3448step1Labels = raw3448step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3448step0 raw3448step0Labels permutation80 hz
    mixedMoment B raw3448step1 raw3448step1Labels = mixedMoment B raw3448step2 raw3448step2Labels := by
      have hz : ∀ i, raw3448step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3448step2 = (fun i j => raw3448step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3448step2 raw3448step1; decide +kernel
      have hl : raw3448step2Labels = (fun j => raw3448step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3448step1 raw3448step1Labels permutation6 hz
    mixedMoment B raw3448step2 raw3448step2Labels = mixedMoment B raw3448step3 raw3448step3Labels := by
      have ha : raw3448step3 = (fun i j => raw3448step2 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3448step3 raw3448step2; decide +kernel
      have hl : raw3448step3Labels = raw3448step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3448step2 raw3448step2Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical3449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3449 raw3449Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3449 raw3449Labels = mixedMoment B raw3449step0 raw3449step0Labels := by
      have hz : ∀ j, raw3449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3449step0 = (fun i j => raw3449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3449step0 raw3449; decide +kernel
      have hl : raw3449step0Labels = raw3449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3449 raw3449Labels permutation434 hz
    mixedMoment B raw3449step0 raw3449step0Labels = mixedMoment B raw3449step1 raw3449step1Labels := by
      have hz : ∀ i, raw3449step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3449step1 = (fun i j => raw3449step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3449step1 raw3449step0; decide +kernel
      have hl : raw3449step1Labels = (fun j => raw3449step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3449step0 raw3449step0Labels permutation6 hz
    mixedMoment B raw3449step1 raw3449step1Labels = mixedMoment B raw3449step2 raw3449step2Labels := by
      have ha : raw3449step2 = (fun i j => raw3449step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3449step2 raw3449step1; decide +kernel
      have hl : raw3449step2Labels = raw3449step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3449step1 raw3449step1Labels permutation146 permutation0
    mixedMoment B raw3449step2 raw3449step2Labels = mixedMoment B raw3449step3 raw3449step3Labels := by
      have ha : raw3449step3 = -raw3449step2 := by apply Matrix.ext; change ∀ i j, raw3449step3 i j = -(raw3449step2 i j); unfold raw3449step3 raw3449step2; decide +kernel
      have hl : raw3449step3Labels = raw3449step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical268
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34405 raw34405Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw34405 raw34405Labels = mixedMoment B raw34405step0 raw34405step0Labels := by
      have hz : ∀ i, raw34405 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34405step0 = (fun i j => raw34405 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34405step0 raw34405; decide +kernel
      have hl : raw34405step0Labels = (fun j => raw34405Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34405 raw34405Labels permutation6 hz
    _ = mixedMoment B node4073 node4073Labels := by rfl

theorem canonical34407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34407 raw34407Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw34407 raw34407Labels = mixedMoment B raw34407step0 raw34407step0Labels := by
      have hz : ∀ j, raw34407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34407step0 = (fun i j => raw34407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34407step0 raw34407; decide +kernel
      have hl : raw34407step0Labels = raw34407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34407 raw34407Labels permutation346 hz
    mixedMoment B raw34407step0 raw34407step0Labels = mixedMoment B raw34407step1 raw34407step1Labels := by
      have hz : ∀ i, raw34407step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34407step1 = (fun i j => raw34407step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34407step1 raw34407step0; decide +kernel
      have hl : raw34407step1Labels = (fun j => raw34407step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34407step0 raw34407step0Labels permutation6 hz
    mixedMoment B raw34407step1 raw34407step1Labels = mixedMoment B raw34407step2 raw34407step2Labels := by
      have ha : raw34407step2 = (fun i j => raw34407step1 (permutation34 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34407step2 raw34407step1; decide +kernel
      have hl : raw34407step2Labels = raw34407step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34407step1 raw34407step1Labels permutation34 permutation0
    _ = mixedMoment B node4075 node4075Labels := by rfl

theorem canonical34408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34408 raw34408Labels = mixedMoment B node4078 node4078Labels := by
  calc
    mixedMoment B raw34408 raw34408Labels = mixedMoment B raw34408step0 raw34408step0Labels := by
      have hz : ∀ i, raw34408 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34408step0 = (fun i j => raw34408 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34408step0 raw34408; decide +kernel
      have hl : raw34408step0Labels = (fun j => raw34408Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34408 raw34408Labels permutation6 hz
    mixedMoment B raw34408step0 raw34408step0Labels = mixedMoment B raw34408step1 raw34408step1Labels := by
      have ha : raw34408step1 = (fun i j => raw34408step0 (permutation154 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34408step1 raw34408step0; decide +kernel
      have hl : raw34408step1Labels = raw34408step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34408step0 raw34408step0Labels permutation154 permutation0
    _ = mixedMoment B node4078 node4078Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical271
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34724 raw34724Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw34724 raw34724Labels = mixedMoment B raw34724step0 raw34724step0Labels := by
      have hz : ∀ i, raw34724 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34724step0 = (fun i j => raw34724 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34724step0 raw34724; decide +kernel
      have hl : raw34724step0Labels = (fun j => raw34724Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34724 raw34724Labels permutation6 hz
    mixedMoment B raw34724step0 raw34724step0Labels = mixedMoment B raw34724step1 raw34724step1Labels := by
      have ha : raw34724step1 = (fun i j => raw34724step0 (permutation161 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34724step1 raw34724step0; decide +kernel
      have hl : raw34724step1Labels = raw34724step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34724step0 raw34724step0Labels permutation161 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

theorem canonical34728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34728 raw34728Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw34728 raw34728Labels = mixedMoment B raw34728step0 raw34728step0Labels := by
      have hz : ∀ i, raw34728 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34728step0 = (fun i j => raw34728 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34728step0 raw34728; decide +kernel
      have hl : raw34728step0Labels = (fun j => raw34728Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34728 raw34728Labels permutation6 hz
    mixedMoment B raw34728step0 raw34728step0Labels = mixedMoment B raw34728step1 raw34728step1Labels := by
      have ha : raw34728step1 = (fun i j => raw34728step0 (permutation155 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34728step1 raw34728step0; decide +kernel
      have hl : raw34728step1Labels = raw34728step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34728step0 raw34728step0Labels permutation155 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

theorem canonical34731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34731 raw34731Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw34731 raw34731Labels = mixedMoment B raw34731step0 raw34731step0Labels := by
      have hz : ∀ i, raw34731 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34731step0 = (fun i j => raw34731 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34731step0 raw34731; decide +kernel
      have hl : raw34731step0Labels = (fun j => raw34731Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34731 raw34731Labels permutation6 hz
    mixedMoment B raw34731step0 raw34731step0Labels = mixedMoment B raw34731step1 raw34731step1Labels := by
      have ha : raw34731step1 = (fun i j => raw34731step0 (permutation153 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34731step1 raw34731step0; decide +kernel
      have hl : raw34731step1Labels = raw34731step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34731step0 raw34731step0Labels permutation153 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical277
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35539 raw35539Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw35539 raw35539Labels = mixedMoment B raw35539step0 raw35539step0Labels := by
      have hz : ∀ j, raw35539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35539step0 = (fun i j => raw35539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35539step0 raw35539; decide +kernel
      have hl : raw35539step0Labels = raw35539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35539 raw35539Labels permutation434 hz
    mixedMoment B raw35539step0 raw35539step0Labels = mixedMoment B raw35539step1 raw35539step1Labels := by
      have hz : ∀ i, raw35539step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35539step1 = (fun i j => raw35539step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35539step1 raw35539step0; decide +kernel
      have hl : raw35539step1Labels = (fun j => raw35539step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35539step0 raw35539step0Labels permutation6 hz
    mixedMoment B raw35539step1 raw35539step1Labels = mixedMoment B raw35539step2 raw35539step2Labels := by
      have ha : raw35539step2 = (fun i j => raw35539step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35539step2 raw35539step1; decide +kernel
      have hl : raw35539step2Labels = raw35539step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35539step1 raw35539step1Labels permutation33 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical35540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35540 raw35540Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw35540 raw35540Labels = mixedMoment B raw35540step0 raw35540step0Labels := by
      have hz : ∀ j, raw35540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35540step0 = (fun i j => raw35540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35540step0 raw35540; decide +kernel
      have hl : raw35540step0Labels = raw35540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35540 raw35540Labels permutation346 hz
    mixedMoment B raw35540step0 raw35540step0Labels = mixedMoment B raw35540step1 raw35540step1Labels := by
      have hz : ∀ i, raw35540step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35540step1 = (fun i j => raw35540step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35540step1 raw35540step0; decide +kernel
      have hl : raw35540step1Labels = (fun j => raw35540step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35540step0 raw35540step0Labels permutation6 hz
    mixedMoment B raw35540step1 raw35540step1Labels = mixedMoment B raw35540step2 raw35540step2Labels := by
      have ha : raw35540step2 = (fun i j => raw35540step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35540step2 raw35540step1; decide +kernel
      have hl : raw35540step2Labels = raw35540step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35540step1 raw35540step1Labels permutation56 permutation0
    _ = mixedMoment B node4075 node4075Labels := by rfl

theorem canonical35541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35541 raw35541Labels = mixedMoment B node4086 node4086Labels := by
  calc
    mixedMoment B raw35541 raw35541Labels = mixedMoment B raw35541step0 raw35541step0Labels := by
      have hz : ∀ i, raw35541 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35541step0 = (fun i j => raw35541 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35541step0 raw35541; decide +kernel
      have hl : raw35541step0Labels = (fun j => raw35541Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35541 raw35541Labels permutation6 hz
    _ = mixedMoment B node4086 node4086Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical289
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37017 raw37017Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw37017 raw37017Labels = mixedMoment B raw37017step0 raw37017step0Labels := by
      have hz : ∀ j, raw37017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37017step0 = (fun i j => raw37017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37017step0 raw37017; decide +kernel
      have hl : raw37017step0Labels = raw37017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37017 raw37017Labels permutation346 hz
    mixedMoment B raw37017step0 raw37017step0Labels = mixedMoment B raw37017step1 raw37017step1Labels := by
      have hz : ∀ i, raw37017step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37017step1 = (fun i j => raw37017step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37017step1 raw37017step0; decide +kernel
      have hl : raw37017step1Labels = (fun j => raw37017step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37017step0 raw37017step0Labels permutation6 hz
    mixedMoment B raw37017step1 raw37017step1Labels = mixedMoment B raw37017step2 raw37017step2Labels := by
      have ha : raw37017step2 = (fun i j => raw37017step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37017step2 raw37017step1; decide +kernel
      have hl : raw37017step2Labels = raw37017step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37017step1 raw37017step1Labels permutation56 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical37018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37018 raw37018Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw37018 raw37018Labels = mixedMoment B raw37018step0 raw37018step0Labels := by
      have hz : ∀ j, raw37018 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37018step0 = (fun i j => raw37018 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37018step0 raw37018; decide +kernel
      have hl : raw37018step0Labels = raw37018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37018 raw37018Labels permutation520 hz
    mixedMoment B raw37018step0 raw37018step0Labels = mixedMoment B raw37018step1 raw37018step1Labels := by
      have hz : ∀ j, raw37018step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37018step1 = (fun i j => raw37018step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37018step1 raw37018step0; decide +kernel
      have hl : raw37018step1Labels = raw37018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37018step0 raw37018step0Labels permutation80 hz
    mixedMoment B raw37018step1 raw37018step1Labels = mixedMoment B raw37018step2 raw37018step2Labels := by
      have hz : ∀ i, raw37018step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37018step2 = (fun i j => raw37018step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37018step2 raw37018step1; decide +kernel
      have hl : raw37018step2Labels = (fun j => raw37018step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37018step1 raw37018step1Labels permutation6 hz
    mixedMoment B raw37018step2 raw37018step2Labels = mixedMoment B raw37018step3 raw37018step3Labels := by
      have ha : raw37018step3 = (fun i j => raw37018step2 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37018step3 raw37018step2; decide +kernel
      have hl : raw37018step3Labels = raw37018step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37018step2 raw37018step2Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical37019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37019 raw37019Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw37019 raw37019Labels = mixedMoment B raw37019step0 raw37019step0Labels := by
      have hz : ∀ i, raw37019 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37019step0 = (fun i j => raw37019 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37019step0 raw37019; decide +kernel
      have hl : raw37019step0Labels = (fun j => raw37019Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37019 raw37019Labels permutation6 hz
    mixedMoment B raw37019step0 raw37019step0Labels = mixedMoment B raw37019step1 raw37019step1Labels := by
      have ha : raw37019step1 = (fun i j => raw37019step0 (permutation265 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37019step1 raw37019step0; decide +kernel
      have hl : raw37019step1Labels = raw37019step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37019step0 raw37019step0Labels permutation265 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

theorem canonical37020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37020 raw37020Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37020 raw37020Labels = mixedMoment B raw37020step0 raw37020step0Labels := by
      have hz : ∀ j, raw37020 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37020step0 = (fun i j => raw37020 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37020step0 raw37020; decide +kernel
      have hl : raw37020step0Labels = raw37020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37020 raw37020Labels permutation520 hz
    mixedMoment B raw37020step0 raw37020step0Labels = mixedMoment B raw37020step1 raw37020step1Labels := by
      have hz : ∀ i, raw37020step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37020step1 = (fun i j => raw37020step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37020step1 raw37020step0; decide +kernel
      have hl : raw37020step1Labels = (fun j => raw37020step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37020step0 raw37020step0Labels permutation6 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical37021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37021 raw37021Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw37021 raw37021Labels = mixedMoment B raw37021step0 raw37021step0Labels := by
      have hz : ∀ j, raw37021 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37021step0 = (fun i j => raw37021 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37021step0 raw37021; decide +kernel
      have hl : raw37021step0Labels = raw37021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37021 raw37021Labels permutation346 hz
    mixedMoment B raw37021step0 raw37021step0Labels = mixedMoment B raw37021step1 raw37021step1Labels := by
      have hz : ∀ i, raw37021step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37021step1 = (fun i j => raw37021step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37021step1 raw37021step0; decide +kernel
      have hl : raw37021step1Labels = (fun j => raw37021step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37021step0 raw37021step0Labels permutation6 hz
    mixedMoment B raw37021step1 raw37021step1Labels = mixedMoment B raw37021step2 raw37021step2Labels := by
      have ha : raw37021step2 = (fun i j => raw37021step1 (permutation58 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37021step2 raw37021step1; decide +kernel
      have hl : raw37021step2Labels = raw37021step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37021step1 raw37021step1Labels permutation58 permutation0
    _ = mixedMoment B node4075 node4075Labels := by rfl

theorem canonical37022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37022 raw37022Labels = mixedMoment B node4086 node4086Labels := by
  calc
    mixedMoment B raw37022 raw37022Labels = mixedMoment B raw37022step0 raw37022step0Labels := by
      have hz : ∀ i, raw37022 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37022step0 = (fun i j => raw37022 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37022step0 raw37022; decide +kernel
      have hl : raw37022step0Labels = (fun j => raw37022Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37022 raw37022Labels permutation6 hz
    mixedMoment B raw37022step0 raw37022step0Labels = mixedMoment B raw37022step1 raw37022step1Labels := by
      have ha : raw37022step1 = (fun i j => raw37022step0 (permutation154 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37022step1 raw37022step0; decide +kernel
      have hl : raw37022step1Labels = raw37022step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37022step0 raw37022step0Labels permutation154 permutation0
    _ = mixedMoment B node4086 node4086Labels := by rfl

theorem canonical37023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37023 raw37023Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw37023 raw37023Labels = mixedMoment B raw37023step0 raw37023step0Labels := by
      have hz : ∀ j, raw37023 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37023step0 = (fun i j => raw37023 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37023step0 raw37023; decide +kernel
      have hl : raw37023step0Labels = raw37023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37023 raw37023Labels permutation520 hz
    mixedMoment B raw37023step0 raw37023step0Labels = mixedMoment B raw37023step1 raw37023step1Labels := by
      have hz : ∀ j, raw37023step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37023step1 = (fun i j => raw37023step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37023step1 raw37023step0; decide +kernel
      have hl : raw37023step1Labels = raw37023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37023step0 raw37023step0Labels permutation80 hz
    mixedMoment B raw37023step1 raw37023step1Labels = mixedMoment B raw37023step2 raw37023step2Labels := by
      have hz : ∀ i, raw37023step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37023step2 = (fun i j => raw37023step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37023step2 raw37023step1; decide +kernel
      have hl : raw37023step2Labels = (fun j => raw37023step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37023step1 raw37023step1Labels permutation6 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

theorem canonical37024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37024 raw37024Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw37024 raw37024Labels = mixedMoment B raw37024step0 raw37024step0Labels := by
      have hz : ∀ j, raw37024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37024step0 = (fun i j => raw37024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37024step0 raw37024; decide +kernel
      have hl : raw37024step0Labels = raw37024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37024 raw37024Labels permutation346 hz
    mixedMoment B raw37024step0 raw37024step0Labels = mixedMoment B raw37024step1 raw37024step1Labels := by
      have hz : ∀ i, raw37024step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37024step1 = (fun i j => raw37024step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37024step1 raw37024step0; decide +kernel
      have hl : raw37024step1Labels = (fun j => raw37024step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37024step0 raw37024step0Labels permutation6 hz
    mixedMoment B raw37024step1 raw37024step1Labels = mixedMoment B raw37024step2 raw37024step2Labels := by
      have ha : raw37024step2 = (fun i j => raw37024step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37024step2 raw37024step1; decide +kernel
      have hl : raw37024step2Labels = raw37024step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37024step1 raw37024step1Labels permutation56 permutation0
    _ = mixedMoment B node4074 node4074Labels := by rfl

theorem canonical37025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37025 raw37025Labels = mixedMoment B node4078 node4078Labels := by
  calc
    mixedMoment B raw37025 raw37025Labels = mixedMoment B raw37025step0 raw37025step0Labels := by
      have hz : ∀ i, raw37025 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37025step0 = (fun i j => raw37025 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37025step0 raw37025; decide +kernel
      have hl : raw37025step0Labels = (fun j => raw37025Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37025 raw37025Labels permutation6 hz
    mixedMoment B raw37025step0 raw37025step0Labels = mixedMoment B raw37025step1 raw37025step1Labels := by
      have ha : raw37025step1 = (fun i j => raw37025step0 (permutation663 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37025step1 raw37025step0; decide +kernel
      have hl : raw37025step1Labels = raw37025step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37025step0 raw37025step0Labels permutation663 permutation0
    mixedMoment B raw37025step1 raw37025step1Labels = mixedMoment B raw37025step2 raw37025step2Labels := by
      have ha : raw37025step2 = -raw37025step1 := by apply Matrix.ext; change ∀ i j, raw37025step2 i j = -(raw37025step1 i j); unfold raw37025step2 raw37025step1; decide +kernel
      have hl : raw37025step2Labels = raw37025step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4078 node4078Labels := by rfl

theorem canonical37026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37026 raw37026Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw37026 raw37026Labels = mixedMoment B raw37026step0 raw37026step0Labels := by
      have hz : ∀ j, raw37026 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37026step0 = (fun i j => raw37026 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37026step0 raw37026; decide +kernel
      have hl : raw37026step0Labels = raw37026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37026 raw37026Labels permutation520 hz
    mixedMoment B raw37026step0 raw37026step0Labels = mixedMoment B raw37026step1 raw37026step1Labels := by
      have hz : ∀ j, raw37026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37026step1 = (fun i j => raw37026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37026step1 raw37026step0; decide +kernel
      have hl : raw37026step1Labels = raw37026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37026step0 raw37026step0Labels permutation80 hz
    mixedMoment B raw37026step1 raw37026step1Labels = mixedMoment B raw37026step2 raw37026step2Labels := by
      have hz : ∀ i, raw37026step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37026step2 = (fun i j => raw37026step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37026step2 raw37026step1; decide +kernel
      have hl : raw37026step2Labels = (fun j => raw37026step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37026step1 raw37026step1Labels permutation6 hz
    mixedMoment B raw37026step2 raw37026step2Labels = mixedMoment B raw37026step3 raw37026step3Labels := by
      have ha : raw37026step3 = (fun i j => raw37026step2 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37026step3 raw37026step2; decide +kernel
      have hl : raw37026step3Labels = raw37026step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37026step2 raw37026step2Labels permutation30 permutation0
    mixedMoment B raw37026step3 raw37026step3Labels = mixedMoment B raw37026step4 raw37026step4Labels := by
      have ha : raw37026step4 = -raw37026step3 := by apply Matrix.ext; change ∀ i j, raw37026step4 i j = -(raw37026step3 i j); unfold raw37026step4 raw37026step3; decide +kernel
      have hl : raw37026step4Labels = raw37026step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical37070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37070 raw37070Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw37070 raw37070Labels = mixedMoment B raw37070step0 raw37070step0Labels := by
      have ha : raw37070step0 = (fun i j => raw37070 (permutation333 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37070step0 raw37070; decide +kernel
      have hl : raw37070step0Labels = raw37070Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37070 raw37070Labels permutation333 permutation7
    mixedMoment B raw37070step0 raw37070step0Labels = mixedMoment B raw37070step1 raw37070step1Labels := by
      have ha : raw37070step1 = -raw37070step0 := by apply Matrix.ext; change ∀ i j, raw37070step1 i j = -(raw37070step0 i j); unfold raw37070step1 raw37070step0; decide +kernel
      have hl : raw37070step1Labels = raw37070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37070step1 raw37070step1Labels = mixedMoment B raw37070step2 raw37070step2Labels := by
      have ha : raw37070step2 = raw37070step1 := by apply Matrix.ext; unfold raw37070step2 raw37070step1; decide +kernel
      have hl : raw37070step1Labels = labelEmbedding1 ∘ raw37070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37070step1 raw37070step1Labels raw37070step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

theorem canonical37071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37071 raw37071Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw37071 raw37071Labels = mixedMoment B raw37071step0 raw37071step0Labels := by
      have ha : raw37071step0 = (fun i j => raw37071 (permutation333 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37071step0 raw37071; decide +kernel
      have hl : raw37071step0Labels = raw37071Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37071 raw37071Labels permutation333 permutation7
    mixedMoment B raw37071step0 raw37071step0Labels = mixedMoment B raw37071step1 raw37071step1Labels := by
      have ha : raw37071step1 = -raw37071step0 := by apply Matrix.ext; change ∀ i j, raw37071step1 i j = -(raw37071step0 i j); unfold raw37071step1 raw37071step0; decide +kernel
      have hl : raw37071step1Labels = raw37071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37071step1 raw37071step1Labels = mixedMoment B raw37071step2 raw37071step2Labels := by
      have ha : raw37071step2 = raw37071step1 := by apply Matrix.ext; unfold raw37071step2 raw37071step1; decide +kernel
      have hl : raw37071step1Labels = labelEmbedding1 ∘ raw37071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37071step1 raw37071step1Labels raw37071step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical37072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37072 raw37072Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw37072 raw37072Labels = mixedMoment B raw37072step0 raw37072step0Labels := by
      have ha : raw37072step0 = (fun i j => raw37072 (permutation335 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37072step0 raw37072; decide +kernel
      have hl : raw37072step0Labels = raw37072Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37072 raw37072Labels permutation335 permutation7
    mixedMoment B raw37072step0 raw37072step0Labels = mixedMoment B raw37072step1 raw37072step1Labels := by
      have ha : raw37072step1 = -raw37072step0 := by apply Matrix.ext; change ∀ i j, raw37072step1 i j = -(raw37072step0 i j); unfold raw37072step1 raw37072step0; decide +kernel
      have hl : raw37072step1Labels = raw37072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37072step1 raw37072step1Labels = mixedMoment B raw37072step2 raw37072step2Labels := by
      have ha : raw37072step2 = raw37072step1 := by apply Matrix.ext; unfold raw37072step2 raw37072step1; decide +kernel
      have hl : raw37072step1Labels = labelEmbedding1 ∘ raw37072step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37072step1 raw37072step1Labels raw37072step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical37073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37073 raw37073Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw37073 raw37073Labels = mixedMoment B raw37073step0 raw37073step0Labels := by
      have ha : raw37073step0 = (fun i j => raw37073 (permutation337 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37073step0 raw37073; decide +kernel
      have hl : raw37073step0Labels = raw37073Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37073 raw37073Labels permutation337 permutation7
    mixedMoment B raw37073step0 raw37073step0Labels = mixedMoment B raw37073step1 raw37073step1Labels := by
      have ha : raw37073step1 = -raw37073step0 := by apply Matrix.ext; change ∀ i j, raw37073step1 i j = -(raw37073step0 i j); unfold raw37073step1 raw37073step0; decide +kernel
      have hl : raw37073step1Labels = raw37073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37073step1 raw37073step1Labels = mixedMoment B raw37073step2 raw37073step2Labels := by
      have ha : raw37073step2 = raw37073step1 := by apply Matrix.ext; unfold raw37073step2 raw37073step1; decide +kernel
      have hl : raw37073step1Labels = labelEmbedding1 ∘ raw37073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37073step1 raw37073step1Labels raw37073step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical37074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37074 raw37074Labels = mixedMoment B node3844 node3844Labels := by
  calc
    mixedMoment B raw37074 raw37074Labels = mixedMoment B raw37074step0 raw37074step0Labels := by
      have ha : raw37074step0 = (fun i j => raw37074 (permutation333 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37074step0 raw37074; decide +kernel
      have hl : raw37074step0Labels = raw37074Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37074 raw37074Labels permutation333 permutation7
    mixedMoment B raw37074step0 raw37074step0Labels = mixedMoment B raw37074step1 raw37074step1Labels := by
      have ha : raw37074step1 = -raw37074step0 := by apply Matrix.ext; change ∀ i j, raw37074step1 i j = -(raw37074step0 i j); unfold raw37074step1 raw37074step0; decide +kernel
      have hl : raw37074step1Labels = raw37074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37074step1 raw37074step1Labels = mixedMoment B raw37074step2 raw37074step2Labels := by
      have ha : raw37074step2 = raw37074step1 := by apply Matrix.ext; unfold raw37074step2 raw37074step1; decide +kernel
      have hl : raw37074step1Labels = labelEmbedding1 ∘ raw37074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37074step1 raw37074step1Labels raw37074step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3844 node3844Labels := by rfl

theorem canonical37075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37075 raw37075Labels = mixedMoment B node2232 node2232Labels := by
  calc
    mixedMoment B raw37075 raw37075Labels = mixedMoment B raw37075step0 raw37075step0Labels := by
      have ha : raw37075step0 = (fun i j => raw37075 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37075step0 raw37075; decide +kernel
      have hl : raw37075step0Labels = raw37075Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37075 raw37075Labels permutation184 permutation5
    mixedMoment B raw37075step0 raw37075step0Labels = mixedMoment B raw37075step1 raw37075step1Labels := by
      have ha : raw37075step1 = -raw37075step0 := by apply Matrix.ext; change ∀ i j, raw37075step1 i j = -(raw37075step0 i j); unfold raw37075step1 raw37075step0; decide +kernel
      have hl : raw37075step1Labels = raw37075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37075step1 raw37075step1Labels = mixedMoment B raw37075step2 raw37075step2Labels := by
      have ha : raw37075step2 = raw37075step1 := by apply Matrix.ext; unfold raw37075step2 raw37075step1; decide +kernel
      have hl : raw37075step1Labels = labelEmbedding1 ∘ raw37075step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37075step1 raw37075step1Labels raw37075step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2232 node2232Labels := by rfl

theorem canonical37076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37076 raw37076Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw37076 raw37076Labels = mixedMoment B raw37076step0 raw37076step0Labels := by
      have ha : raw37076step0 = (fun i j => raw37076 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37076step0 raw37076; decide +kernel
      have hl : raw37076step0Labels = raw37076Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37076 raw37076Labels permutation184 permutation5
    mixedMoment B raw37076step0 raw37076step0Labels = mixedMoment B raw37076step1 raw37076step1Labels := by
      have ha : raw37076step1 = -raw37076step0 := by apply Matrix.ext; change ∀ i j, raw37076step1 i j = -(raw37076step0 i j); unfold raw37076step1 raw37076step0; decide +kernel
      have hl : raw37076step1Labels = raw37076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37076step1 raw37076step1Labels = mixedMoment B raw37076step2 raw37076step2Labels := by
      have ha : raw37076step2 = raw37076step1 := by apply Matrix.ext; unfold raw37076step2 raw37076step1; decide +kernel
      have hl : raw37076step1Labels = labelEmbedding1 ∘ raw37076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37076step1 raw37076step1Labels raw37076step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical37077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37077 raw37077Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw37077 raw37077Labels = mixedMoment B raw37077step0 raw37077step0Labels := by
      have ha : raw37077step0 = (fun i j => raw37077 (permutation208 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37077step0 raw37077; decide +kernel
      have hl : raw37077step0Labels = raw37077Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37077 raw37077Labels permutation208 permutation5
    mixedMoment B raw37077step0 raw37077step0Labels = mixedMoment B raw37077step1 raw37077step1Labels := by
      have ha : raw37077step1 = -raw37077step0 := by apply Matrix.ext; change ∀ i j, raw37077step1 i j = -(raw37077step0 i j); unfold raw37077step1 raw37077step0; decide +kernel
      have hl : raw37077step1Labels = raw37077step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37077step1 raw37077step1Labels = mixedMoment B raw37077step2 raw37077step2Labels := by
      have ha : raw37077step2 = raw37077step1 := by apply Matrix.ext; unfold raw37077step2 raw37077step1; decide +kernel
      have hl : raw37077step1Labels = labelEmbedding1 ∘ raw37077step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37077step1 raw37077step1Labels raw37077step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical37078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37078 raw37078Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw37078 raw37078Labels = mixedMoment B raw37078step0 raw37078step0Labels := by
      have ha : raw37078step0 = (fun i j => raw37078 (permutation232 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37078step0 raw37078; decide +kernel
      have hl : raw37078step0Labels = raw37078Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37078 raw37078Labels permutation232 permutation5
    mixedMoment B raw37078step0 raw37078step0Labels = mixedMoment B raw37078step1 raw37078step1Labels := by
      have ha : raw37078step1 = -raw37078step0 := by apply Matrix.ext; change ∀ i j, raw37078step1 i j = -(raw37078step0 i j); unfold raw37078step1 raw37078step0; decide +kernel
      have hl : raw37078step1Labels = raw37078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37078step1 raw37078step1Labels = mixedMoment B raw37078step2 raw37078step2Labels := by
      have ha : raw37078step2 = raw37078step1 := by apply Matrix.ext; unfold raw37078step2 raw37078step1; decide +kernel
      have hl : raw37078step1Labels = labelEmbedding1 ∘ raw37078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37078step1 raw37078step1Labels raw37078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical37079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37079 raw37079Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw37079 raw37079Labels = mixedMoment B raw37079step0 raw37079step0Labels := by
      have ha : raw37079step0 = (fun i j => raw37079 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37079step0 raw37079; decide +kernel
      have hl : raw37079step0Labels = raw37079Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37079 raw37079Labels permutation184 permutation5
    mixedMoment B raw37079step0 raw37079step0Labels = mixedMoment B raw37079step1 raw37079step1Labels := by
      have ha : raw37079step1 = -raw37079step0 := by apply Matrix.ext; change ∀ i j, raw37079step1 i j = -(raw37079step0 i j); unfold raw37079step1 raw37079step0; decide +kernel
      have hl : raw37079step1Labels = raw37079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37079step1 raw37079step1Labels = mixedMoment B raw37079step2 raw37079step2Labels := by
      have ha : raw37079step2 = raw37079step1 := by apply Matrix.ext; unfold raw37079step2 raw37079step1; decide +kernel
      have hl : raw37079step1Labels = labelEmbedding1 ∘ raw37079step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37079step1 raw37079step1Labels raw37079step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

theorem canonical37080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37080 raw37080Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw37080 raw37080Labels = mixedMoment B raw37080step0 raw37080step0Labels := by
      have ha : raw37080step0 = (fun i j => raw37080 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37080step0 raw37080; decide +kernel
      have hl : raw37080step0Labels = raw37080Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37080 raw37080Labels permutation160 permutation5
    mixedMoment B raw37080step0 raw37080step0Labels = mixedMoment B raw37080step1 raw37080step1Labels := by
      have ha : raw37080step1 = -raw37080step0 := by apply Matrix.ext; change ∀ i j, raw37080step1 i j = -(raw37080step0 i j); unfold raw37080step1 raw37080step0; decide +kernel
      have hl : raw37080step1Labels = raw37080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37080step1 raw37080step1Labels = mixedMoment B raw37080step2 raw37080step2Labels := by
      have ha : raw37080step2 = raw37080step1 := by apply Matrix.ext; unfold raw37080step2 raw37080step1; decide +kernel
      have hl : raw37080step1Labels = labelEmbedding1 ∘ raw37080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37080step1 raw37080step1Labels raw37080step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

theorem canonical37081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37081 raw37081Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw37081 raw37081Labels = mixedMoment B raw37081step0 raw37081step0Labels := by
      have ha : raw37081step0 = (fun i j => raw37081 (permutation336 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37081step0 raw37081; decide +kernel
      have hl : raw37081step0Labels = raw37081Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37081 raw37081Labels permutation336 permutation7
    mixedMoment B raw37081step0 raw37081step0Labels = mixedMoment B raw37081step1 raw37081step1Labels := by
      have ha : raw37081step1 = -raw37081step0 := by apply Matrix.ext; change ∀ i j, raw37081step1 i j = -(raw37081step0 i j); unfold raw37081step1 raw37081step0; decide +kernel
      have hl : raw37081step1Labels = raw37081step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37081step1 raw37081step1Labels = mixedMoment B raw37081step2 raw37081step2Labels := by
      have ha : raw37081step2 = raw37081step1 := by apply Matrix.ext; unfold raw37081step2 raw37081step1; decide +kernel
      have hl : raw37081step1Labels = labelEmbedding1 ∘ raw37081step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37081step1 raw37081step1Labels raw37081step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

theorem canonical37082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37082 raw37082Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw37082 raw37082Labels = mixedMoment B raw37082step0 raw37082step0Labels := by
      have ha : raw37082step0 = (fun i j => raw37082 (permutation202 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37082step0 raw37082; decide +kernel
      have hl : raw37082step0Labels = raw37082Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37082 raw37082Labels permutation202 permutation5
    mixedMoment B raw37082step0 raw37082step0Labels = mixedMoment B raw37082step1 raw37082step1Labels := by
      have ha : raw37082step1 = -raw37082step0 := by apply Matrix.ext; change ∀ i j, raw37082step1 i j = -(raw37082step0 i j); unfold raw37082step1 raw37082step0; decide +kernel
      have hl : raw37082step1Labels = raw37082step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37082step1 raw37082step1Labels = mixedMoment B raw37082step2 raw37082step2Labels := by
      have ha : raw37082step2 = raw37082step1 := by apply Matrix.ext; unfold raw37082step2 raw37082step1; decide +kernel
      have hl : raw37082step1Labels = labelEmbedding1 ∘ raw37082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37082step1 raw37082step1Labels raw37082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical37083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37083 raw37083Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw37083 raw37083Labels = mixedMoment B raw37083step0 raw37083step0Labels := by
      have ha : raw37083step0 = (fun i j => raw37083 (permutation226 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37083step0 raw37083; decide +kernel
      have hl : raw37083step0Labels = raw37083Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37083 raw37083Labels permutation226 permutation5
    mixedMoment B raw37083step0 raw37083step0Labels = mixedMoment B raw37083step1 raw37083step1Labels := by
      have ha : raw37083step1 = -raw37083step0 := by apply Matrix.ext; change ∀ i j, raw37083step1 i j = -(raw37083step0 i j); unfold raw37083step1 raw37083step0; decide +kernel
      have hl : raw37083step1Labels = raw37083step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37083step1 raw37083step1Labels = mixedMoment B raw37083step2 raw37083step2Labels := by
      have ha : raw37083step2 = raw37083step1 := by apply Matrix.ext; unfold raw37083step2 raw37083step1; decide +kernel
      have hl : raw37083step1Labels = labelEmbedding1 ∘ raw37083step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37083step1 raw37083step1Labels raw37083step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical37084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37084 raw37084Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw37084 raw37084Labels = mixedMoment B raw37084step0 raw37084step0Labels := by
      have ha : raw37084step0 = (fun i j => raw37084 (permutation336 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37084step0 raw37084; decide +kernel
      have hl : raw37084step0Labels = raw37084Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37084 raw37084Labels permutation336 permutation7
    mixedMoment B raw37084step0 raw37084step0Labels = mixedMoment B raw37084step1 raw37084step1Labels := by
      have ha : raw37084step1 = -raw37084step0 := by apply Matrix.ext; change ∀ i j, raw37084step1 i j = -(raw37084step0 i j); unfold raw37084step1 raw37084step0; decide +kernel
      have hl : raw37084step1Labels = raw37084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37084step1 raw37084step1Labels = mixedMoment B raw37084step2 raw37084step2Labels := by
      have ha : raw37084step2 = raw37084step1 := by apply Matrix.ext; unfold raw37084step2 raw37084step1; decide +kernel
      have hl : raw37084step1Labels = labelEmbedding1 ∘ raw37084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37084step1 raw37084step1Labels raw37084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

theorem canonical37085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37085 raw37085Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw37085 raw37085Labels = mixedMoment B raw37085step0 raw37085step0Labels := by
      have ha : raw37085step0 = (fun i j => raw37085 (permutation154 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37085step0 raw37085; decide +kernel
      have hl : raw37085step0Labels = raw37085Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37085 raw37085Labels permutation154 permutation5
    mixedMoment B raw37085step0 raw37085step0Labels = mixedMoment B raw37085step1 raw37085step1Labels := by
      have ha : raw37085step1 = -raw37085step0 := by apply Matrix.ext; change ∀ i j, raw37085step1 i j = -(raw37085step0 i j); unfold raw37085step1 raw37085step0; decide +kernel
      have hl : raw37085step1Labels = raw37085step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37085step1 raw37085step1Labels = mixedMoment B raw37085step2 raw37085step2Labels := by
      have ha : raw37085step2 = raw37085step1 := by apply Matrix.ext; unfold raw37085step2 raw37085step1; decide +kernel
      have hl : raw37085step1Labels = labelEmbedding1 ∘ raw37085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37085step1 raw37085step1Labels raw37085step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

theorem canonical37086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37086 raw37086Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw37086 raw37086Labels = mixedMoment B raw37086step0 raw37086step0Labels := by
      have ha : raw37086step0 = (fun i j => raw37086 (permutation334 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37086step0 raw37086; decide +kernel
      have hl : raw37086step0Labels = raw37086Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37086 raw37086Labels permutation334 permutation7
    mixedMoment B raw37086step0 raw37086step0Labels = mixedMoment B raw37086step1 raw37086step1Labels := by
      have ha : raw37086step1 = -raw37086step0 := by apply Matrix.ext; change ∀ i j, raw37086step1 i j = -(raw37086step0 i j); unfold raw37086step1 raw37086step0; decide +kernel
      have hl : raw37086step1Labels = raw37086step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37086step1 raw37086step1Labels = mixedMoment B raw37086step2 raw37086step2Labels := by
      have ha : raw37086step2 = raw37086step1 := by apply Matrix.ext; unfold raw37086step2 raw37086step1; decide +kernel
      have hl : raw37086step1Labels = labelEmbedding1 ∘ raw37086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37086step1 raw37086step1Labels raw37086step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

theorem canonical37087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37087 raw37087Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw37087 raw37087Labels = mixedMoment B raw37087step0 raw37087step0Labels := by
      have ha : raw37087step0 = (fun i j => raw37087 (permutation178 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37087step0 raw37087; decide +kernel
      have hl : raw37087step0Labels = raw37087Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37087 raw37087Labels permutation178 permutation5
    mixedMoment B raw37087step0 raw37087step0Labels = mixedMoment B raw37087step1 raw37087step1Labels := by
      have ha : raw37087step1 = -raw37087step0 := by apply Matrix.ext; change ∀ i j, raw37087step1 i j = -(raw37087step0 i j); unfold raw37087step1 raw37087step0; decide +kernel
      have hl : raw37087step1Labels = raw37087step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37087step1 raw37087step1Labels = mixedMoment B raw37087step2 raw37087step2Labels := by
      have ha : raw37087step2 = raw37087step1 := by apply Matrix.ext; unfold raw37087step2 raw37087step1; decide +kernel
      have hl : raw37087step1Labels = labelEmbedding1 ∘ raw37087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37087step1 raw37087step1Labels raw37087step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical37088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37088 raw37088Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw37088 raw37088Labels = mixedMoment B raw37088step0 raw37088step0Labels := by
      have ha : raw37088step0 = (fun i j => raw37088 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37088step0 raw37088; decide +kernel
      have hl : raw37088step0Labels = raw37088Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37088 raw37088Labels permutation224 permutation5
    mixedMoment B raw37088step0 raw37088step0Labels = mixedMoment B raw37088step1 raw37088step1Labels := by
      have ha : raw37088step1 = -raw37088step0 := by apply Matrix.ext; change ∀ i j, raw37088step1 i j = -(raw37088step0 i j); unfold raw37088step1 raw37088step0; decide +kernel
      have hl : raw37088step1Labels = raw37088step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37088step1 raw37088step1Labels = mixedMoment B raw37088step2 raw37088step2Labels := by
      have ha : raw37088step2 = raw37088step1 := by apply Matrix.ext; unfold raw37088step2 raw37088step1; decide +kernel
      have hl : raw37088step1Labels = labelEmbedding1 ∘ raw37088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37088step1 raw37088step1Labels raw37088step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical37089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37089 raw37089Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw37089 raw37089Labels = mixedMoment B raw37089step0 raw37089step0Labels := by
      have ha : raw37089step0 = (fun i j => raw37089 (permutation334 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37089step0 raw37089; decide +kernel
      have hl : raw37089step0Labels = raw37089Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37089 raw37089Labels permutation334 permutation7
    mixedMoment B raw37089step0 raw37089step0Labels = mixedMoment B raw37089step1 raw37089step1Labels := by
      have ha : raw37089step1 = -raw37089step0 := by apply Matrix.ext; change ∀ i j, raw37089step1 i j = -(raw37089step0 i j); unfold raw37089step1 raw37089step0; decide +kernel
      have hl : raw37089step1Labels = raw37089step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37089step1 raw37089step1Labels = mixedMoment B raw37089step2 raw37089step2Labels := by
      have ha : raw37089step2 = raw37089step1 := by apply Matrix.ext; unfold raw37089step2 raw37089step1; decide +kernel
      have hl : raw37089step1Labels = labelEmbedding1 ∘ raw37089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37089step1 raw37089step1Labels raw37089step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

theorem canonical37090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37090 raw37090Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw37090 raw37090Labels = mixedMoment B raw37090step0 raw37090step0Labels := by
      have ha : raw37090step0 = (fun i j => raw37090 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37090step0 raw37090; decide +kernel
      have hl : raw37090step0Labels = raw37090Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37090 raw37090Labels permutation152 permutation5
    mixedMoment B raw37090step0 raw37090step0Labels = mixedMoment B raw37090step1 raw37090step1Labels := by
      have ha : raw37090step1 = -raw37090step0 := by apply Matrix.ext; change ∀ i j, raw37090step1 i j = -(raw37090step0 i j); unfold raw37090step1 raw37090step0; decide +kernel
      have hl : raw37090step1Labels = raw37090step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37090step1 raw37090step1Labels = mixedMoment B raw37090step2 raw37090step2Labels := by
      have ha : raw37090step2 = raw37090step1 := by apply Matrix.ext; unfold raw37090step2 raw37090step1; decide +kernel
      have hl : raw37090step1Labels = labelEmbedding1 ∘ raw37090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37090step1 raw37090step1Labels raw37090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

theorem canonical37091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37091 raw37091Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw37091 raw37091Labels = mixedMoment B raw37091step0 raw37091step0Labels := by
      have ha : raw37091step0 = (fun i j => raw37091 (permutation333 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37091step0 raw37091; decide +kernel
      have hl : raw37091step0Labels = raw37091Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37091 raw37091Labels permutation333 permutation7
    mixedMoment B raw37091step0 raw37091step0Labels = mixedMoment B raw37091step1 raw37091step1Labels := by
      have ha : raw37091step1 = -raw37091step0 := by apply Matrix.ext; change ∀ i j, raw37091step1 i j = -(raw37091step0 i j); unfold raw37091step1 raw37091step0; decide +kernel
      have hl : raw37091step1Labels = raw37091step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37091step1 raw37091step1Labels = mixedMoment B raw37091step2 raw37091step2Labels := by
      have ha : raw37091step2 = raw37091step1 := by apply Matrix.ext; unfold raw37091step2 raw37091step1; decide +kernel
      have hl : raw37091step1Labels = labelEmbedding1 ∘ raw37091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37091step1 raw37091step1Labels raw37091step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

theorem canonical37092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37092 raw37092Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw37092 raw37092Labels = mixedMoment B raw37092step0 raw37092step0Labels := by
      have ha : raw37092step0 = (fun i j => raw37092 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37092step0 raw37092; decide +kernel
      have hl : raw37092step0Labels = raw37092Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37092 raw37092Labels permutation176 permutation5
    mixedMoment B raw37092step0 raw37092step0Labels = mixedMoment B raw37092step1 raw37092step1Labels := by
      have ha : raw37092step1 = -raw37092step0 := by apply Matrix.ext; change ∀ i j, raw37092step1 i j = -(raw37092step0 i j); unfold raw37092step1 raw37092step0; decide +kernel
      have hl : raw37092step1Labels = raw37092step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37092step1 raw37092step1Labels = mixedMoment B raw37092step2 raw37092step2Labels := by
      have ha : raw37092step2 = raw37092step1 := by apply Matrix.ext; unfold raw37092step2 raw37092step1; decide +kernel
      have hl : raw37092step1Labels = labelEmbedding1 ∘ raw37092step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37092step1 raw37092step1Labels raw37092step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical37093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37093 raw37093Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw37093 raw37093Labels = mixedMoment B raw37093step0 raw37093step0Labels := by
      have ha : raw37093step0 = (fun i j => raw37093 (permutation200 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37093step0 raw37093; decide +kernel
      have hl : raw37093step0Labels = raw37093Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37093 raw37093Labels permutation200 permutation5
    mixedMoment B raw37093step0 raw37093step0Labels = mixedMoment B raw37093step1 raw37093step1Labels := by
      have ha : raw37093step1 = -raw37093step0 := by apply Matrix.ext; change ∀ i j, raw37093step1 i j = -(raw37093step0 i j); unfold raw37093step1 raw37093step0; decide +kernel
      have hl : raw37093step1Labels = raw37093step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37093step1 raw37093step1Labels = mixedMoment B raw37093step2 raw37093step2Labels := by
      have ha : raw37093step2 = raw37093step1 := by apply Matrix.ext; unfold raw37093step2 raw37093step1; decide +kernel
      have hl : raw37093step1Labels = labelEmbedding1 ∘ raw37093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37093step1 raw37093step1Labels raw37093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical37094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37094 raw37094Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw37094 raw37094Labels = mixedMoment B raw37094step0 raw37094step0Labels := by
      have ha : raw37094step0 = (fun i j => raw37094 (permutation333 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37094step0 raw37094; decide +kernel
      have hl : raw37094step0Labels = raw37094Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37094 raw37094Labels permutation333 permutation7
    mixedMoment B raw37094step0 raw37094step0Labels = mixedMoment B raw37094step1 raw37094step1Labels := by
      have ha : raw37094step1 = -raw37094step0 := by apply Matrix.ext; change ∀ i j, raw37094step1 i j = -(raw37094step0 i j); unfold raw37094step1 raw37094step0; decide +kernel
      have hl : raw37094step1Labels = raw37094step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37094step1 raw37094step1Labels = mixedMoment B raw37094step2 raw37094step2Labels := by
      have ha : raw37094step2 = raw37094step1 := by apply Matrix.ext; unfold raw37094step2 raw37094step1; decide +kernel
      have hl : raw37094step1Labels = labelEmbedding1 ∘ raw37094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37094step1 raw37094step1Labels raw37094step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

theorem canonical37095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37095 raw37095Labels = mixedMoment B node2139 node2139Labels := by
  calc
    mixedMoment B raw37095 raw37095Labels = mixedMoment B raw37095step0 raw37095step0Labels := by
      have ha : raw37095step0 = (fun i j => raw37095 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37095step0 raw37095; decide +kernel
      have hl : raw37095step0Labels = raw37095Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37095 raw37095Labels permutation152 permutation5
    mixedMoment B raw37095step0 raw37095step0Labels = mixedMoment B raw37095step1 raw37095step1Labels := by
      have ha : raw37095step1 = -raw37095step0 := by apply Matrix.ext; change ∀ i j, raw37095step1 i j = -(raw37095step0 i j); unfold raw37095step1 raw37095step0; decide +kernel
      have hl : raw37095step1Labels = raw37095step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37095step1 raw37095step1Labels = mixedMoment B raw37095step2 raw37095step2Labels := by
      have ha : raw37095step2 = raw37095step1 := by apply Matrix.ext; unfold raw37095step2 raw37095step1; decide +kernel
      have hl : raw37095step1Labels = labelEmbedding1 ∘ raw37095step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37095step1 raw37095step1Labels raw37095step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2139 node2139Labels := by rfl

theorem canonical37096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37096 raw37096Labels = mixedMoment B node2690 node2690Labels := by
  calc
    mixedMoment B raw37096 raw37096Labels = mixedMoment B raw37096step0 raw37096step0Labels := by
      have ha : raw37096step0 = (fun i j => raw37096 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37096step0 raw37096; decide +kernel
      have hl : raw37096step0Labels = raw37096Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37096 raw37096Labels permutation640 permutation5
    mixedMoment B raw37096step0 raw37096step0Labels = mixedMoment B raw37096step1 raw37096step1Labels := by
      have ha : raw37096step1 = raw37096step0 := by apply Matrix.ext; unfold raw37096step1 raw37096step0; decide +kernel
      have hl : raw37096step0Labels = labelEmbedding1 ∘ raw37096step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37096step0 raw37096step0Labels raw37096step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2690 node2690Labels := by rfl

theorem canonical37097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37097 raw37097Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw37097 raw37097Labels = mixedMoment B raw37097step0 raw37097step0Labels := by
      have ha : raw37097step0 = (fun i j => raw37097 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37097step0 raw37097; decide +kernel
      have hl : raw37097step0Labels = raw37097Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37097 raw37097Labels permutation662 permutation5
    mixedMoment B raw37097step0 raw37097step0Labels = mixedMoment B raw37097step1 raw37097step1Labels := by
      have ha : raw37097step1 = raw37097step0 := by apply Matrix.ext; unfold raw37097step1 raw37097step0; decide +kernel
      have hl : raw37097step0Labels = labelEmbedding1 ∘ raw37097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37097step0 raw37097step0Labels raw37097step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

theorem canonical37098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37098 raw37098Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw37098 raw37098Labels = mixedMoment B raw37098step0 raw37098step0Labels := by
      have ha : raw37098step0 = (fun i j => raw37098 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37098step0 raw37098; decide +kernel
      have hl : raw37098step0Labels = raw37098Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37098 raw37098Labels permutation644 permutation5
    mixedMoment B raw37098step0 raw37098step0Labels = mixedMoment B raw37098step1 raw37098step1Labels := by
      have ha : raw37098step1 = raw37098step0 := by apply Matrix.ext; unfold raw37098step1 raw37098step0; decide +kernel
      have hl : raw37098step0Labels = labelEmbedding1 ∘ raw37098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37098step0 raw37098step0Labels raw37098step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

theorem canonical37099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37099 raw37099Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw37099 raw37099Labels = mixedMoment B raw37099step0 raw37099step0Labels := by
      have ha : raw37099step0 = (fun i j => raw37099 (permutation638 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37099step0 raw37099; decide +kernel
      have hl : raw37099step0Labels = raw37099Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37099 raw37099Labels permutation638 permutation5
    mixedMoment B raw37099step0 raw37099step0Labels = mixedMoment B raw37099step1 raw37099step1Labels := by
      have ha : raw37099step1 = raw37099step0 := by apply Matrix.ext; unfold raw37099step1 raw37099step0; decide +kernel
      have hl : raw37099step0Labels = labelEmbedding1 ∘ raw37099step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37099step0 raw37099step0Labels raw37099step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical290
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37156 raw37156Labels = mixedMoment B node2204 node2204Labels := by
  calc
    mixedMoment B raw37156 raw37156Labels = mixedMoment B raw37156step0 raw37156step0Labels := by
      have ha : raw37156step0 = (fun i j => raw37156 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37156step0 raw37156; decide +kernel
      have hl : raw37156step0Labels = raw37156Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37156 raw37156Labels permutation283 permutation7
    mixedMoment B raw37156step0 raw37156step0Labels = mixedMoment B raw37156step1 raw37156step1Labels := by
      have ha : raw37156step1 = -raw37156step0 := by apply Matrix.ext; change ∀ i j, raw37156step1 i j = -(raw37156step0 i j); unfold raw37156step1 raw37156step0; decide +kernel
      have hl : raw37156step1Labels = raw37156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37156step1 raw37156step1Labels = mixedMoment B raw37156step2 raw37156step2Labels := by
      have ha : raw37156step2 = raw37156step1 := by apply Matrix.ext; unfold raw37156step2 raw37156step1; decide +kernel
      have hl : raw37156step1Labels = labelEmbedding1 ∘ raw37156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37156step1 raw37156step1Labels raw37156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2204 node2204Labels := by rfl

theorem canonical37157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37157 raw37157Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw37157 raw37157Labels = mixedMoment B raw37157step0 raw37157step0Labels := by
      have ha : raw37157step0 = (fun i j => raw37157 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37157step0 raw37157; decide +kernel
      have hl : raw37157step0Labels = raw37157Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37157 raw37157Labels permutation283 permutation7
    mixedMoment B raw37157step0 raw37157step0Labels = mixedMoment B raw37157step1 raw37157step1Labels := by
      have ha : raw37157step1 = -raw37157step0 := by apply Matrix.ext; change ∀ i j, raw37157step1 i j = -(raw37157step0 i j); unfold raw37157step1 raw37157step0; decide +kernel
      have hl : raw37157step1Labels = raw37157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37157step1 raw37157step1Labels = mixedMoment B raw37157step2 raw37157step2Labels := by
      have ha : raw37157step2 = raw37157step1 := by apply Matrix.ext; unfold raw37157step2 raw37157step1; decide +kernel
      have hl : raw37157step1Labels = labelEmbedding1 ∘ raw37157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37157step1 raw37157step1Labels raw37157step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical37158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37158 raw37158Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw37158 raw37158Labels = mixedMoment B raw37158step0 raw37158step0Labels := by
      have ha : raw37158step0 = (fun i j => raw37158 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37158step0 raw37158; decide +kernel
      have hl : raw37158step0Labels = raw37158Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37158 raw37158Labels permutation285 permutation7
    mixedMoment B raw37158step0 raw37158step0Labels = mixedMoment B raw37158step1 raw37158step1Labels := by
      have ha : raw37158step1 = -raw37158step0 := by apply Matrix.ext; change ∀ i j, raw37158step1 i j = -(raw37158step0 i j); unfold raw37158step1 raw37158step0; decide +kernel
      have hl : raw37158step1Labels = raw37158step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37158step1 raw37158step1Labels = mixedMoment B raw37158step2 raw37158step2Labels := by
      have ha : raw37158step2 = raw37158step1 := by apply Matrix.ext; unfold raw37158step2 raw37158step1; decide +kernel
      have hl : raw37158step1Labels = labelEmbedding1 ∘ raw37158step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37158step1 raw37158step1Labels raw37158step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical37159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37159 raw37159Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw37159 raw37159Labels = mixedMoment B raw37159step0 raw37159step0Labels := by
      have ha : raw37159step0 = (fun i j => raw37159 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37159step0 raw37159; decide +kernel
      have hl : raw37159step0Labels = raw37159Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37159 raw37159Labels permutation287 permutation7
    mixedMoment B raw37159step0 raw37159step0Labels = mixedMoment B raw37159step1 raw37159step1Labels := by
      have ha : raw37159step1 = -raw37159step0 := by apply Matrix.ext; change ∀ i j, raw37159step1 i j = -(raw37159step0 i j); unfold raw37159step1 raw37159step0; decide +kernel
      have hl : raw37159step1Labels = raw37159step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37159step1 raw37159step1Labels = mixedMoment B raw37159step2 raw37159step2Labels := by
      have ha : raw37159step2 = raw37159step1 := by apply Matrix.ext; unfold raw37159step2 raw37159step1; decide +kernel
      have hl : raw37159step1Labels = labelEmbedding1 ∘ raw37159step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37159step1 raw37159step1Labels raw37159step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical37160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37160 raw37160Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw37160 raw37160Labels = mixedMoment B raw37160step0 raw37160step0Labels := by
      have hz : ∀ j, raw37160 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37160step0 = (fun i j => raw37160 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37160step0 raw37160; decide +kernel
      have hl : raw37160step0Labels = raw37160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37160 raw37160Labels permutation590 hz
    mixedMoment B raw37160step0 raw37160step0Labels = mixedMoment B raw37160step1 raw37160step1Labels := by
      have ha : raw37160step1 = (fun i j => raw37160step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37160step1 raw37160step0; decide +kernel
      have hl : raw37160step1Labels = raw37160step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37160step0 raw37160step0Labels permutation56 permutation7
    mixedMoment B raw37160step1 raw37160step1Labels = mixedMoment B raw37160step2 raw37160step2Labels := by
      have ha : raw37160step2 = -raw37160step1 := by apply Matrix.ext; change ∀ i j, raw37160step2 i j = -(raw37160step1 i j); unfold raw37160step2 raw37160step1; decide +kernel
      have hl : raw37160step2Labels = raw37160step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37160step2 raw37160step2Labels = mixedMoment B raw37160step3 raw37160step3Labels := by
      have ha : raw37160step3 = raw37160step2 := by apply Matrix.ext; unfold raw37160step3 raw37160step2; decide +kernel
      have hl : raw37160step2Labels = labelEmbedding1 ∘ raw37160step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37160step2 raw37160step2Labels raw37160step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2741 node2741Labels := by rfl

theorem canonical37161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37161 raw37161Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw37161 raw37161Labels = mixedMoment B raw37161step0 raw37161step0Labels := by
      have ha : raw37161step0 = (fun i j => raw37161 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37161step0 raw37161; decide +kernel
      have hl : raw37161step0Labels = raw37161Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37161 raw37161Labels permutation185 permutation5
    mixedMoment B raw37161step0 raw37161step0Labels = mixedMoment B raw37161step1 raw37161step1Labels := by
      have ha : raw37161step1 = -raw37161step0 := by apply Matrix.ext; change ∀ i j, raw37161step1 i j = -(raw37161step0 i j); unfold raw37161step1 raw37161step0; decide +kernel
      have hl : raw37161step1Labels = raw37161step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37161step1 raw37161step1Labels = mixedMoment B raw37161step2 raw37161step2Labels := by
      have ha : raw37161step2 = raw37161step1 := by apply Matrix.ext; unfold raw37161step2 raw37161step1; decide +kernel
      have hl : raw37161step1Labels = labelEmbedding1 ∘ raw37161step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37161step1 raw37161step1Labels raw37161step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2234 node2234Labels := by rfl

theorem canonical37162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37162 raw37162Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw37162 raw37162Labels = mixedMoment B raw37162step0 raw37162step0Labels := by
      have ha : raw37162step0 = (fun i j => raw37162 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37162step0 raw37162; decide +kernel
      have hl : raw37162step0Labels = raw37162Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37162 raw37162Labels permutation283 permutation7
    mixedMoment B raw37162step0 raw37162step0Labels = mixedMoment B raw37162step1 raw37162step1Labels := by
      have ha : raw37162step1 = -raw37162step0 := by apply Matrix.ext; change ∀ i j, raw37162step1 i j = -(raw37162step0 i j); unfold raw37162step1 raw37162step0; decide +kernel
      have hl : raw37162step1Labels = raw37162step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37162step1 raw37162step1Labels = mixedMoment B raw37162step2 raw37162step2Labels := by
      have ha : raw37162step2 = raw37162step1 := by apply Matrix.ext; unfold raw37162step2 raw37162step1; decide +kernel
      have hl : raw37162step1Labels = labelEmbedding1 ∘ raw37162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37162step1 raw37162step1Labels raw37162step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical37163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37163 raw37163Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw37163 raw37163Labels = mixedMoment B raw37163step0 raw37163step0Labels := by
      have ha : raw37163step0 = (fun i j => raw37163 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37163step0 raw37163; decide +kernel
      have hl : raw37163step0Labels = raw37163Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37163 raw37163Labels permutation285 permutation7
    mixedMoment B raw37163step0 raw37163step0Labels = mixedMoment B raw37163step1 raw37163step1Labels := by
      have ha : raw37163step1 = -raw37163step0 := by apply Matrix.ext; change ∀ i j, raw37163step1 i j = -(raw37163step0 i j); unfold raw37163step1 raw37163step0; decide +kernel
      have hl : raw37163step1Labels = raw37163step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37163step1 raw37163step1Labels = mixedMoment B raw37163step2 raw37163step2Labels := by
      have ha : raw37163step2 = raw37163step1 := by apply Matrix.ext; unfold raw37163step2 raw37163step1; decide +kernel
      have hl : raw37163step1Labels = labelEmbedding1 ∘ raw37163step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37163step1 raw37163step1Labels raw37163step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical37164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37164 raw37164Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw37164 raw37164Labels = mixedMoment B raw37164step0 raw37164step0Labels := by
      have ha : raw37164step0 = (fun i j => raw37164 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37164step0 raw37164; decide +kernel
      have hl : raw37164step0Labels = raw37164Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37164 raw37164Labels permutation287 permutation7
    mixedMoment B raw37164step0 raw37164step0Labels = mixedMoment B raw37164step1 raw37164step1Labels := by
      have ha : raw37164step1 = -raw37164step0 := by apply Matrix.ext; change ∀ i j, raw37164step1 i j = -(raw37164step0 i j); unfold raw37164step1 raw37164step0; decide +kernel
      have hl : raw37164step1Labels = raw37164step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37164step1 raw37164step1Labels = mixedMoment B raw37164step2 raw37164step2Labels := by
      have ha : raw37164step2 = raw37164step1 := by apply Matrix.ext; unfold raw37164step2 raw37164step1; decide +kernel
      have hl : raw37164step1Labels = labelEmbedding1 ∘ raw37164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37164step1 raw37164step1Labels raw37164step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical37165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37165 raw37165Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw37165 raw37165Labels = mixedMoment B raw37165step0 raw37165step0Labels := by
      have hz : ∀ j, raw37165 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37165step0 = (fun i j => raw37165 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37165step0 raw37165; decide +kernel
      have hl : raw37165step0Labels = raw37165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37165 raw37165Labels permutation590 hz
    mixedMoment B raw37165step0 raw37165step0Labels = mixedMoment B raw37165step1 raw37165step1Labels := by
      have ha : raw37165step1 = (fun i j => raw37165step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37165step1 raw37165step0; decide +kernel
      have hl : raw37165step1Labels = raw37165step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37165step0 raw37165step0Labels permutation56 permutation7
    mixedMoment B raw37165step1 raw37165step1Labels = mixedMoment B raw37165step2 raw37165step2Labels := by
      have ha : raw37165step2 = -raw37165step1 := by apply Matrix.ext; change ∀ i j, raw37165step2 i j = -(raw37165step1 i j); unfold raw37165step2 raw37165step1; decide +kernel
      have hl : raw37165step2Labels = raw37165step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37165step2 raw37165step2Labels = mixedMoment B raw37165step3 raw37165step3Labels := by
      have ha : raw37165step3 = raw37165step2 := by apply Matrix.ext; unfold raw37165step3 raw37165step2; decide +kernel
      have hl : raw37165step2Labels = labelEmbedding1 ∘ raw37165step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37165step2 raw37165step2Labels raw37165step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical37166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37166 raw37166Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw37166 raw37166Labels = mixedMoment B raw37166step0 raw37166step0Labels := by
      have ha : raw37166step0 = (fun i j => raw37166 (permutation213 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37166step0 raw37166; decide +kernel
      have hl : raw37166step0Labels = raw37166Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37166 raw37166Labels permutation213 permutation5
    mixedMoment B raw37166step0 raw37166step0Labels = mixedMoment B raw37166step1 raw37166step1Labels := by
      have ha : raw37166step1 = -raw37166step0 := by apply Matrix.ext; change ∀ i j, raw37166step1 i j = -(raw37166step0 i j); unfold raw37166step1 raw37166step0; decide +kernel
      have hl : raw37166step1Labels = raw37166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37166step1 raw37166step1Labels = mixedMoment B raw37166step2 raw37166step2Labels := by
      have ha : raw37166step2 = raw37166step1 := by apply Matrix.ext; unfold raw37166step2 raw37166step1; decide +kernel
      have hl : raw37166step1Labels = labelEmbedding1 ∘ raw37166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37166step1 raw37166step1Labels raw37166step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

theorem canonical37167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37167 raw37167Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw37167 raw37167Labels = mixedMoment B raw37167step0 raw37167step0Labels := by
      have ha : raw37167step0 = (fun i j => raw37167 (permutation286 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37167step0 raw37167; decide +kernel
      have hl : raw37167step0Labels = raw37167Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37167 raw37167Labels permutation286 permutation7
    mixedMoment B raw37167step0 raw37167step0Labels = mixedMoment B raw37167step1 raw37167step1Labels := by
      have ha : raw37167step1 = -raw37167step0 := by apply Matrix.ext; change ∀ i j, raw37167step1 i j = -(raw37167step0 i j); unfold raw37167step1 raw37167step0; decide +kernel
      have hl : raw37167step1Labels = raw37167step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37167step1 raw37167step1Labels = mixedMoment B raw37167step2 raw37167step2Labels := by
      have ha : raw37167step2 = raw37167step1 := by apply Matrix.ext; unfold raw37167step2 raw37167step1; decide +kernel
      have hl : raw37167step1Labels = labelEmbedding1 ∘ raw37167step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37167step1 raw37167step1Labels raw37167step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

theorem canonical37168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37168 raw37168Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw37168 raw37168Labels = mixedMoment B raw37168step0 raw37168step0Labels := by
      have ha : raw37168step0 = (fun i j => raw37168 (permutation286 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37168step0 raw37168; decide +kernel
      have hl : raw37168step0Labels = raw37168Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37168 raw37168Labels permutation286 permutation7
    mixedMoment B raw37168step0 raw37168step0Labels = mixedMoment B raw37168step1 raw37168step1Labels := by
      have ha : raw37168step1 = -raw37168step0 := by apply Matrix.ext; change ∀ i j, raw37168step1 i j = -(raw37168step0 i j); unfold raw37168step1 raw37168step0; decide +kernel
      have hl : raw37168step1Labels = raw37168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37168step1 raw37168step1Labels = mixedMoment B raw37168step2 raw37168step2Labels := by
      have ha : raw37168step2 = raw37168step1 := by apply Matrix.ext; unfold raw37168step2 raw37168step1; decide +kernel
      have hl : raw37168step1Labels = labelEmbedding1 ∘ raw37168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37168step1 raw37168step1Labels raw37168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical37169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37169 raw37169Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw37169 raw37169Labels = mixedMoment B raw37169step0 raw37169step0Labels := by
      have ha : raw37169step0 = (fun i j => raw37169 (permutation288 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37169step0 raw37169; decide +kernel
      have hl : raw37169step0Labels = raw37169Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37169 raw37169Labels permutation288 permutation7
    mixedMoment B raw37169step0 raw37169step0Labels = mixedMoment B raw37169step1 raw37169step1Labels := by
      have ha : raw37169step1 = -raw37169step0 := by apply Matrix.ext; change ∀ i j, raw37169step1 i j = -(raw37169step0 i j); unfold raw37169step1 raw37169step0; decide +kernel
      have hl : raw37169step1Labels = raw37169step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37169step1 raw37169step1Labels = mixedMoment B raw37169step2 raw37169step2Labels := by
      have ha : raw37169step2 = raw37169step1 := by apply Matrix.ext; unfold raw37169step2 raw37169step1; decide +kernel
      have hl : raw37169step1Labels = labelEmbedding1 ∘ raw37169step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37169step1 raw37169step1Labels raw37169step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical37170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37170 raw37170Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw37170 raw37170Labels = mixedMoment B raw37170step0 raw37170step0Labels := by
      have hz : ∀ j, raw37170 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37170step0 = (fun i j => raw37170 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37170step0 raw37170; decide +kernel
      have hl : raw37170step0Labels = raw37170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37170 raw37170Labels permutation590 hz
    mixedMoment B raw37170step0 raw37170step0Labels = mixedMoment B raw37170step1 raw37170step1Labels := by
      have ha : raw37170step1 = (fun i j => raw37170step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37170step1 raw37170step0; decide +kernel
      have hl : raw37170step1Labels = raw37170step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37170step0 raw37170step0Labels permutation59 permutation7
    mixedMoment B raw37170step1 raw37170step1Labels = mixedMoment B raw37170step2 raw37170step2Labels := by
      have ha : raw37170step2 = -raw37170step1 := by apply Matrix.ext; change ∀ i j, raw37170step2 i j = -(raw37170step1 i j); unfold raw37170step2 raw37170step1; decide +kernel
      have hl : raw37170step2Labels = raw37170step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37170step2 raw37170step2Labels = mixedMoment B raw37170step3 raw37170step3Labels := by
      have ha : raw37170step3 = raw37170step2 := by apply Matrix.ext; unfold raw37170step3 raw37170step2; decide +kernel
      have hl : raw37170step2Labels = labelEmbedding1 ∘ raw37170step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37170step2 raw37170step2Labels raw37170step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical37171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37171 raw37171Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw37171 raw37171Labels = mixedMoment B raw37171step0 raw37171step0Labels := by
      have ha : raw37171step0 = (fun i j => raw37171 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37171step0 raw37171; decide +kernel
      have hl : raw37171step0Labels = raw37171Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37171 raw37171Labels permutation189 permutation5
    mixedMoment B raw37171step0 raw37171step0Labels = mixedMoment B raw37171step1 raw37171step1Labels := by
      have ha : raw37171step1 = -raw37171step0 := by apply Matrix.ext; change ∀ i j, raw37171step1 i j = -(raw37171step0 i j); unfold raw37171step1 raw37171step0; decide +kernel
      have hl : raw37171step1Labels = raw37171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37171step1 raw37171step1Labels = mixedMoment B raw37171step2 raw37171step2Labels := by
      have ha : raw37171step2 = raw37171step1 := by apply Matrix.ext; unfold raw37171step2 raw37171step1; decide +kernel
      have hl : raw37171step1Labels = labelEmbedding1 ∘ raw37171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37171step1 raw37171step1Labels raw37171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

theorem canonical37172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37172 raw37172Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw37172 raw37172Labels = mixedMoment B raw37172step0 raw37172step0Labels := by
      have ha : raw37172step0 = (fun i j => raw37172 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37172step0 raw37172; decide +kernel
      have hl : raw37172step0Labels = raw37172Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37172 raw37172Labels permutation284 permutation7
    mixedMoment B raw37172step0 raw37172step0Labels = mixedMoment B raw37172step1 raw37172step1Labels := by
      have ha : raw37172step1 = -raw37172step0 := by apply Matrix.ext; change ∀ i j, raw37172step1 i j = -(raw37172step0 i j); unfold raw37172step1 raw37172step0; decide +kernel
      have hl : raw37172step1Labels = raw37172step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37172step1 raw37172step1Labels = mixedMoment B raw37172step2 raw37172step2Labels := by
      have ha : raw37172step2 = raw37172step1 := by apply Matrix.ext; unfold raw37172step2 raw37172step1; decide +kernel
      have hl : raw37172step1Labels = labelEmbedding1 ∘ raw37172step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37172step1 raw37172step1Labels raw37172step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

theorem canonical37173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37173 raw37173Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw37173 raw37173Labels = mixedMoment B raw37173step0 raw37173step0Labels := by
      have ha : raw37173step0 = (fun i j => raw37173 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37173step0 raw37173; decide +kernel
      have hl : raw37173step0Labels = raw37173Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37173 raw37173Labels permutation284 permutation7
    mixedMoment B raw37173step0 raw37173step0Labels = mixedMoment B raw37173step1 raw37173step1Labels := by
      have ha : raw37173step1 = -raw37173step0 := by apply Matrix.ext; change ∀ i j, raw37173step1 i j = -(raw37173step0 i j); unfold raw37173step1 raw37173step0; decide +kernel
      have hl : raw37173step1Labels = raw37173step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37173step1 raw37173step1Labels = mixedMoment B raw37173step2 raw37173step2Labels := by
      have ha : raw37173step2 = raw37173step1 := by apply Matrix.ext; unfold raw37173step2 raw37173step1; decide +kernel
      have hl : raw37173step1Labels = labelEmbedding1 ∘ raw37173step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37173step1 raw37173step1Labels raw37173step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical37174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37174 raw37174Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw37174 raw37174Labels = mixedMoment B raw37174step0 raw37174step0Labels := by
      have ha : raw37174step0 = (fun i j => raw37174 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37174step0 raw37174; decide +kernel
      have hl : raw37174step0Labels = raw37174Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37174 raw37174Labels permutation287 permutation7
    mixedMoment B raw37174step0 raw37174step0Labels = mixedMoment B raw37174step1 raw37174step1Labels := by
      have ha : raw37174step1 = -raw37174step0 := by apply Matrix.ext; change ∀ i j, raw37174step1 i j = -(raw37174step0 i j); unfold raw37174step1 raw37174step0; decide +kernel
      have hl : raw37174step1Labels = raw37174step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37174step1 raw37174step1Labels = mixedMoment B raw37174step2 raw37174step2Labels := by
      have ha : raw37174step2 = raw37174step1 := by apply Matrix.ext; unfold raw37174step2 raw37174step1; decide +kernel
      have hl : raw37174step1Labels = labelEmbedding1 ∘ raw37174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37174step1 raw37174step1Labels raw37174step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical37175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37175 raw37175Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw37175 raw37175Labels = mixedMoment B raw37175step0 raw37175step0Labels := by
      have hz : ∀ j, raw37175 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37175step0 = (fun i j => raw37175 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37175step0 raw37175; decide +kernel
      have hl : raw37175step0Labels = raw37175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37175 raw37175Labels permutation590 hz
    mixedMoment B raw37175step0 raw37175step0Labels = mixedMoment B raw37175step1 raw37175step1Labels := by
      have ha : raw37175step1 = (fun i j => raw37175step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37175step1 raw37175step0; decide +kernel
      have hl : raw37175step1Labels = raw37175step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37175step0 raw37175step0Labels permutation57 permutation7
    mixedMoment B raw37175step1 raw37175step1Labels = mixedMoment B raw37175step2 raw37175step2Labels := by
      have ha : raw37175step2 = -raw37175step1 := by apply Matrix.ext; change ∀ i j, raw37175step2 i j = -(raw37175step1 i j); unfold raw37175step2 raw37175step1; decide +kernel
      have hl : raw37175step2Labels = raw37175step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37175step2 raw37175step2Labels = mixedMoment B raw37175step3 raw37175step3Labels := by
      have ha : raw37175step3 = raw37175step2 := by apply Matrix.ext; unfold raw37175step3 raw37175step2; decide +kernel
      have hl : raw37175step2Labels = labelEmbedding1 ∘ raw37175step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37175step2 raw37175step2Labels raw37175step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical37176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37176 raw37176Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw37176 raw37176Labels = mixedMoment B raw37176step0 raw37176step0Labels := by
      have ha : raw37176step0 = (fun i j => raw37176 (permutation183 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37176step0 raw37176; decide +kernel
      have hl : raw37176step0Labels = raw37176Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37176 raw37176Labels permutation183 permutation5
    mixedMoment B raw37176step0 raw37176step0Labels = mixedMoment B raw37176step1 raw37176step1Labels := by
      have ha : raw37176step1 = -raw37176step0 := by apply Matrix.ext; change ∀ i j, raw37176step1 i j = -(raw37176step0 i j); unfold raw37176step1 raw37176step0; decide +kernel
      have hl : raw37176step1Labels = raw37176step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37176step1 raw37176step1Labels = mixedMoment B raw37176step2 raw37176step2Labels := by
      have ha : raw37176step2 = raw37176step1 := by apply Matrix.ext; unfold raw37176step2 raw37176step1; decide +kernel
      have hl : raw37176step1Labels = labelEmbedding1 ∘ raw37176step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37176step1 raw37176step1Labels raw37176step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

theorem canonical37177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37177 raw37177Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw37177 raw37177Labels = mixedMoment B raw37177step0 raw37177step0Labels := by
      have ha : raw37177step0 = (fun i j => raw37177 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37177step0 raw37177; decide +kernel
      have hl : raw37177step0Labels = raw37177Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37177 raw37177Labels permutation283 permutation7
    mixedMoment B raw37177step0 raw37177step0Labels = mixedMoment B raw37177step1 raw37177step1Labels := by
      have ha : raw37177step1 = -raw37177step0 := by apply Matrix.ext; change ∀ i j, raw37177step1 i j = -(raw37177step0 i j); unfold raw37177step1 raw37177step0; decide +kernel
      have hl : raw37177step1Labels = raw37177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37177step1 raw37177step1Labels = mixedMoment B raw37177step2 raw37177step2Labels := by
      have ha : raw37177step2 = raw37177step1 := by apply Matrix.ext; unfold raw37177step2 raw37177step1; decide +kernel
      have hl : raw37177step1Labels = labelEmbedding1 ∘ raw37177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37177step1 raw37177step1Labels raw37177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

theorem canonical37178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37178 raw37178Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw37178 raw37178Labels = mixedMoment B raw37178step0 raw37178step0Labels := by
      have ha : raw37178step0 = (fun i j => raw37178 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37178step0 raw37178; decide +kernel
      have hl : raw37178step0Labels = raw37178Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37178 raw37178Labels permutation283 permutation7
    mixedMoment B raw37178step0 raw37178step0Labels = mixedMoment B raw37178step1 raw37178step1Labels := by
      have ha : raw37178step1 = -raw37178step0 := by apply Matrix.ext; change ∀ i j, raw37178step1 i j = -(raw37178step0 i j); unfold raw37178step1 raw37178step0; decide +kernel
      have hl : raw37178step1Labels = raw37178step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37178step1 raw37178step1Labels = mixedMoment B raw37178step2 raw37178step2Labels := by
      have ha : raw37178step2 = raw37178step1 := by apply Matrix.ext; unfold raw37178step2 raw37178step1; decide +kernel
      have hl : raw37178step1Labels = labelEmbedding1 ∘ raw37178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37178step1 raw37178step1Labels raw37178step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical37179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37179 raw37179Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw37179 raw37179Labels = mixedMoment B raw37179step0 raw37179step0Labels := by
      have ha : raw37179step0 = (fun i j => raw37179 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37179step0 raw37179; decide +kernel
      have hl : raw37179step0Labels = raw37179Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37179 raw37179Labels permutation285 permutation7
    mixedMoment B raw37179step0 raw37179step0Labels = mixedMoment B raw37179step1 raw37179step1Labels := by
      have ha : raw37179step1 = -raw37179step0 := by apply Matrix.ext; change ∀ i j, raw37179step1 i j = -(raw37179step0 i j); unfold raw37179step1 raw37179step0; decide +kernel
      have hl : raw37179step1Labels = raw37179step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37179step1 raw37179step1Labels = mixedMoment B raw37179step2 raw37179step2Labels := by
      have ha : raw37179step2 = raw37179step1 := by apply Matrix.ext; unfold raw37179step2 raw37179step1; decide +kernel
      have hl : raw37179step1Labels = labelEmbedding1 ∘ raw37179step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37179step1 raw37179step1Labels raw37179step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical37180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37180 raw37180Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw37180 raw37180Labels = mixedMoment B raw37180step0 raw37180step0Labels := by
      have hz : ∀ j, raw37180 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37180step0 = (fun i j => raw37180 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37180step0 raw37180; decide +kernel
      have hl : raw37180step0Labels = raw37180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37180 raw37180Labels permutation590 hz
    mixedMoment B raw37180step0 raw37180step0Labels = mixedMoment B raw37180step1 raw37180step1Labels := by
      have ha : raw37180step1 = (fun i j => raw37180step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37180step1 raw37180step0; decide +kernel
      have hl : raw37180step1Labels = raw37180step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37180step0 raw37180step0Labels permutation56 permutation7
    mixedMoment B raw37180step1 raw37180step1Labels = mixedMoment B raw37180step2 raw37180step2Labels := by
      have ha : raw37180step2 = -raw37180step1 := by apply Matrix.ext; change ∀ i j, raw37180step2 i j = -(raw37180step1 i j); unfold raw37180step2 raw37180step1; decide +kernel
      have hl : raw37180step2Labels = raw37180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37180step2 raw37180step2Labels = mixedMoment B raw37180step3 raw37180step3Labels := by
      have ha : raw37180step3 = raw37180step2 := by apply Matrix.ext; unfold raw37180step3 raw37180step2; decide +kernel
      have hl : raw37180step2Labels = labelEmbedding1 ∘ raw37180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37180step2 raw37180step2Labels raw37180step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical37181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37181 raw37181Labels = mixedMoment B node2231 node2231Labels := by
  calc
    mixedMoment B raw37181 raw37181Labels = mixedMoment B raw37181step0 raw37181step0Labels := by
      have ha : raw37181step0 = (fun i j => raw37181 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37181step0 raw37181; decide +kernel
      have hl : raw37181step0Labels = raw37181Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37181 raw37181Labels permutation184 permutation5
    mixedMoment B raw37181step0 raw37181step0Labels = mixedMoment B raw37181step1 raw37181step1Labels := by
      have ha : raw37181step1 = -raw37181step0 := by apply Matrix.ext; change ∀ i j, raw37181step1 i j = -(raw37181step0 i j); unfold raw37181step1 raw37181step0; decide +kernel
      have hl : raw37181step1Labels = raw37181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37181step1 raw37181step1Labels = mixedMoment B raw37181step2 raw37181step2Labels := by
      have ha : raw37181step2 = raw37181step1 := by apply Matrix.ext; unfold raw37181step2 raw37181step1; decide +kernel
      have hl : raw37181step1Labels = labelEmbedding1 ∘ raw37181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37181step1 raw37181step1Labels raw37181step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2231 node2231Labels := by rfl

theorem canonical37182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37182 raw37182Labels = mixedMoment B node2156 node2156Labels := by
  calc
    mixedMoment B raw37182 raw37182Labels = mixedMoment B raw37182step0 raw37182step0Labels := by
      have ha : raw37182step0 = (fun i j => raw37182 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37182step0 raw37182; decide +kernel
      have hl : raw37182step0Labels = raw37182Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37182 raw37182Labels permutation283 permutation7
    mixedMoment B raw37182step0 raw37182step0Labels = mixedMoment B raw37182step1 raw37182step1Labels := by
      have ha : raw37182step1 = -raw37182step0 := by apply Matrix.ext; change ∀ i j, raw37182step1 i j = -(raw37182step0 i j); unfold raw37182step1 raw37182step0; decide +kernel
      have hl : raw37182step1Labels = raw37182step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37182step1 raw37182step1Labels = mixedMoment B raw37182step2 raw37182step2Labels := by
      have ha : raw37182step2 = raw37182step1 := by apply Matrix.ext; unfold raw37182step2 raw37182step1; decide +kernel
      have hl : raw37182step1Labels = labelEmbedding1 ∘ raw37182step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37182step1 raw37182step1Labels raw37182step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2156 node2156Labels := by rfl

theorem canonical37183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37183 raw37183Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw37183 raw37183Labels = mixedMoment B raw37183step0 raw37183step0Labels := by
      have ha : raw37183step0 = (fun i j => raw37183 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37183step0 raw37183; decide +kernel
      have hl : raw37183step0Labels = raw37183Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37183 raw37183Labels permutation283 permutation7
    mixedMoment B raw37183step0 raw37183step0Labels = mixedMoment B raw37183step1 raw37183step1Labels := by
      have ha : raw37183step1 = -raw37183step0 := by apply Matrix.ext; change ∀ i j, raw37183step1 i j = -(raw37183step0 i j); unfold raw37183step1 raw37183step0; decide +kernel
      have hl : raw37183step1Labels = raw37183step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37183step1 raw37183step1Labels = mixedMoment B raw37183step2 raw37183step2Labels := by
      have ha : raw37183step2 = raw37183step1 := by apply Matrix.ext; unfold raw37183step2 raw37183step1; decide +kernel
      have hl : raw37183step1Labels = labelEmbedding1 ∘ raw37183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37183step1 raw37183step1Labels raw37183step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

theorem canonical37184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37184 raw37184Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw37184 raw37184Labels = mixedMoment B raw37184step0 raw37184step0Labels := by
      have ha : raw37184step0 = (fun i j => raw37184 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37184step0 raw37184; decide +kernel
      have hl : raw37184step0Labels = raw37184Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37184 raw37184Labels permutation285 permutation7
    mixedMoment B raw37184step0 raw37184step0Labels = mixedMoment B raw37184step1 raw37184step1Labels := by
      have ha : raw37184step1 = -raw37184step0 := by apply Matrix.ext; change ∀ i j, raw37184step1 i j = -(raw37184step0 i j); unfold raw37184step1 raw37184step0; decide +kernel
      have hl : raw37184step1Labels = raw37184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37184step1 raw37184step1Labels = mixedMoment B raw37184step2 raw37184step2Labels := by
      have ha : raw37184step2 = raw37184step1 := by apply Matrix.ext; unfold raw37184step2 raw37184step1; decide +kernel
      have hl : raw37184step1Labels = labelEmbedding1 ∘ raw37184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37184step1 raw37184step1Labels raw37184step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

theorem canonical37185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37185 raw37185Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw37185 raw37185Labels = mixedMoment B raw37185step0 raw37185step0Labels := by
      have ha : raw37185step0 = (fun i j => raw37185 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37185step0 raw37185; decide +kernel
      have hl : raw37185step0Labels = raw37185Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37185 raw37185Labels permutation287 permutation7
    mixedMoment B raw37185step0 raw37185step0Labels = mixedMoment B raw37185step1 raw37185step1Labels := by
      have ha : raw37185step1 = -raw37185step0 := by apply Matrix.ext; change ∀ i j, raw37185step1 i j = -(raw37185step0 i j); unfold raw37185step1 raw37185step0; decide +kernel
      have hl : raw37185step1Labels = raw37185step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37185step1 raw37185step1Labels = mixedMoment B raw37185step2 raw37185step2Labels := by
      have ha : raw37185step2 = raw37185step1 := by apply Matrix.ext; unfold raw37185step2 raw37185step1; decide +kernel
      have hl : raw37185step1Labels = labelEmbedding1 ∘ raw37185step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37185step1 raw37185step1Labels raw37185step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

theorem canonical37232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37232 raw37232Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw37232 raw37232Labels = mixedMoment B raw37232step0 raw37232step0Labels := by
      have hz : ∀ i, raw37232 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37232step0 = (fun i j => raw37232 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37232step0 raw37232; decide +kernel
      have hl : raw37232step0Labels = (fun j => raw37232Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37232 raw37232Labels permutation6 hz
    mixedMoment B raw37232step0 raw37232step0Labels = mixedMoment B raw37232step1 raw37232step1Labels := by
      have ha : raw37232step1 = (fun i j => raw37232step0 (permutation265 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37232step1 raw37232step0; decide +kernel
      have hl : raw37232step1Labels = raw37232step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37232step0 raw37232step0Labels permutation265 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

theorem canonical37233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37233 raw37233Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw37233 raw37233Labels = mixedMoment B raw37233step0 raw37233step0Labels := by
      have hz : ∀ j, raw37233 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37233step0 = (fun i j => raw37233 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37233step0 raw37233; decide +kernel
      have hl : raw37233step0Labels = raw37233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37233 raw37233Labels permutation520 hz
    mixedMoment B raw37233step0 raw37233step0Labels = mixedMoment B raw37233step1 raw37233step1Labels := by
      have hz : ∀ i, raw37233step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37233step1 = (fun i j => raw37233step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37233step1 raw37233step0; decide +kernel
      have hl : raw37233step1Labels = (fun j => raw37233step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37233step0 raw37233step0Labels permutation6 hz
    mixedMoment B raw37233step1 raw37233step1Labels = mixedMoment B raw37233step2 raw37233step2Labels := by
      have ha : raw37233step2 = (fun i j => raw37233step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37233step2 raw37233step1; decide +kernel
      have hl : raw37233step2Labels = raw37233step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37233step1 raw37233step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical37234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37234 raw37234Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw37234 raw37234Labels = mixedMoment B raw37234step0 raw37234step0Labels := by
      have hz : ∀ j, raw37234 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37234step0 = (fun i j => raw37234 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37234step0 raw37234; decide +kernel
      have hl : raw37234step0Labels = raw37234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37234 raw37234Labels permutation590 hz
    mixedMoment B raw37234step0 raw37234step0Labels = mixedMoment B raw37234step1 raw37234step1Labels := by
      have hz : ∀ i, raw37234step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37234step1 = (fun i j => raw37234step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37234step1 raw37234step0; decide +kernel
      have hl : raw37234step1Labels = (fun j => raw37234step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37234step0 raw37234step0Labels permutation6 hz
    mixedMoment B raw37234step1 raw37234step1Labels = mixedMoment B raw37234step2 raw37234step2Labels := by
      have ha : raw37234step2 = (fun i j => raw37234step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37234step2 raw37234step1; decide +kernel
      have hl : raw37234step2Labels = raw37234step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37234step1 raw37234step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical37235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37235 raw37235Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw37235 raw37235Labels = mixedMoment B raw37235step0 raw37235step0Labels := by
      have hz : ∀ i, raw37235 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37235step0 = (fun i j => raw37235 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37235step0 raw37235; decide +kernel
      have hl : raw37235step0Labels = (fun j => raw37235Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37235 raw37235Labels permutation6 hz
    mixedMoment B raw37235step0 raw37235step0Labels = mixedMoment B raw37235step1 raw37235step1Labels := by
      have ha : raw37235step1 = (fun i j => raw37235step0 (permutation274 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37235step1 raw37235step0; decide +kernel
      have hl : raw37235step1Labels = raw37235step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37235step0 raw37235step0Labels permutation274 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

theorem canonical37236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37236 raw37236Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37236 raw37236Labels = mixedMoment B raw37236step0 raw37236step0Labels := by
      have hz : ∀ j, raw37236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37236step0 = (fun i j => raw37236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37236step0 raw37236; decide +kernel
      have hl : raw37236step0Labels = raw37236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37236 raw37236Labels permutation434 hz
    mixedMoment B raw37236step0 raw37236step0Labels = mixedMoment B raw37236step1 raw37236step1Labels := by
      have hz : ∀ i, raw37236step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37236step1 = (fun i j => raw37236step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37236step1 raw37236step0; decide +kernel
      have hl : raw37236step1Labels = (fun j => raw37236step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37236step0 raw37236step0Labels permutation6 hz
    mixedMoment B raw37236step1 raw37236step1Labels = mixedMoment B raw37236step2 raw37236step2Labels := by
      have ha : raw37236step2 = (fun i j => raw37236step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37236step2 raw37236step1; decide +kernel
      have hl : raw37236step2Labels = raw37236step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37236step1 raw37236step1Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical37237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37237 raw37237Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37237 raw37237Labels = mixedMoment B raw37237step0 raw37237step0Labels := by
      have hz : ∀ j, raw37237 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37237step0 = (fun i j => raw37237 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37237step0 raw37237; decide +kernel
      have hl : raw37237step0Labels = raw37237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37237 raw37237Labels permutation520 hz
    mixedMoment B raw37237step0 raw37237step0Labels = mixedMoment B raw37237step1 raw37237step1Labels := by
      have hz : ∀ i, raw37237step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37237step1 = (fun i j => raw37237step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37237step1 raw37237step0; decide +kernel
      have hl : raw37237step1Labels = (fun j => raw37237step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37237step0 raw37237step0Labels permutation6 hz
    mixedMoment B raw37237step1 raw37237step1Labels = mixedMoment B raw37237step2 raw37237step2Labels := by
      have ha : raw37237step2 = (fun i j => raw37237step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37237step2 raw37237step1; decide +kernel
      have hl : raw37237step2Labels = raw37237step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37237step1 raw37237step1Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical37238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37238 raw37238Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37238 raw37238Labels = mixedMoment B raw37238step0 raw37238step0Labels := by
      have hz : ∀ j, raw37238 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37238step0 = (fun i j => raw37238 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37238step0 raw37238; decide +kernel
      have hl : raw37238step0Labels = raw37238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37238 raw37238Labels permutation590 hz
    mixedMoment B raw37238step0 raw37238step0Labels = mixedMoment B raw37238step1 raw37238step1Labels := by
      have hz : ∀ i, raw37238step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37238step1 = (fun i j => raw37238step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37238step1 raw37238step0; decide +kernel
      have hl : raw37238step1Labels = (fun j => raw37238step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37238step0 raw37238step0Labels permutation6 hz
    mixedMoment B raw37238step1 raw37238step1Labels = mixedMoment B raw37238step2 raw37238step2Labels := by
      have ha : raw37238step2 = (fun i j => raw37238step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37238step2 raw37238step1; decide +kernel
      have hl : raw37238step2Labels = raw37238step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37238step1 raw37238step1Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical37239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37239 raw37239Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw37239 raw37239Labels = mixedMoment B raw37239step0 raw37239step0Labels := by
      have hz : ∀ i, raw37239 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37239step0 = (fun i j => raw37239 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37239step0 raw37239; decide +kernel
      have hl : raw37239step0Labels = (fun j => raw37239Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37239 raw37239Labels permutation6 hz
    mixedMoment B raw37239step0 raw37239step0Labels = mixedMoment B raw37239step1 raw37239step1Labels := by
      have ha : raw37239step1 = (fun i j => raw37239step0 (permutation268 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37239step1 raw37239step0; decide +kernel
      have hl : raw37239step1Labels = raw37239step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37239step0 raw37239step0Labels permutation268 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

theorem canonical37240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37240 raw37240Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37240 raw37240Labels = mixedMoment B raw37240step0 raw37240step0Labels := by
      have hz : ∀ j, raw37240 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37240step0 = (fun i j => raw37240 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37240step0 raw37240; decide +kernel
      have hl : raw37240step0Labels = raw37240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37240 raw37240Labels permutation520 hz
    mixedMoment B raw37240step0 raw37240step0Labels = mixedMoment B raw37240step1 raw37240step1Labels := by
      have hz : ∀ i, raw37240step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37240step1 = (fun i j => raw37240step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37240step1 raw37240step0; decide +kernel
      have hl : raw37240step1Labels = (fun j => raw37240step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37240step0 raw37240step0Labels permutation6 hz
    mixedMoment B raw37240step1 raw37240step1Labels = mixedMoment B raw37240step2 raw37240step2Labels := by
      have ha : raw37240step2 = (fun i j => raw37240step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37240step2 raw37240step1; decide +kernel
      have hl : raw37240step2Labels = raw37240step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37240step1 raw37240step1Labels permutation33 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical37241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37241 raw37241Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37241 raw37241Labels = mixedMoment B raw37241step0 raw37241step0Labels := by
      have hz : ∀ j, raw37241 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37241step0 = (fun i j => raw37241 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37241step0 raw37241; decide +kernel
      have hl : raw37241step0Labels = raw37241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37241 raw37241Labels permutation590 hz
    mixedMoment B raw37241step0 raw37241step0Labels = mixedMoment B raw37241step1 raw37241step1Labels := by
      have hz : ∀ i, raw37241step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37241step1 = (fun i j => raw37241step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37241step1 raw37241step0; decide +kernel
      have hl : raw37241step1Labels = (fun j => raw37241step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37241step0 raw37241step0Labels permutation6 hz
    mixedMoment B raw37241step1 raw37241step1Labels = mixedMoment B raw37241step2 raw37241step2Labels := by
      have ha : raw37241step2 = (fun i j => raw37241step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37241step2 raw37241step1; decide +kernel
      have hl : raw37241step2Labels = raw37241step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37241step1 raw37241step1Labels permutation33 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical37242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37242 raw37242Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw37242 raw37242Labels = mixedMoment B raw37242step0 raw37242step0Labels := by
      have hz : ∀ i, raw37242 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37242step0 = (fun i j => raw37242 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37242step0 raw37242; decide +kernel
      have hl : raw37242step0Labels = (fun j => raw37242Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37242 raw37242Labels permutation6 hz
    mixedMoment B raw37242step0 raw37242step0Labels = mixedMoment B raw37242step1 raw37242step1Labels := by
      have ha : raw37242step1 = (fun i j => raw37242step0 (permutation266 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37242step1 raw37242step0; decide +kernel
      have hl : raw37242step1Labels = raw37242step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37242step0 raw37242step0Labels permutation266 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

theorem canonical37243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37243 raw37243Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37243 raw37243Labels = mixedMoment B raw37243step0 raw37243step0Labels := by
      have hz : ∀ j, raw37243 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37243step0 = (fun i j => raw37243 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37243step0 raw37243; decide +kernel
      have hl : raw37243step0Labels = raw37243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37243 raw37243Labels permutation590 hz
    mixedMoment B raw37243step0 raw37243step0Labels = mixedMoment B raw37243step1 raw37243step1Labels := by
      have hz : ∀ i, raw37243step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37243step1 = (fun i j => raw37243step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37243step1 raw37243step0; decide +kernel
      have hl : raw37243step1Labels = (fun j => raw37243step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37243step0 raw37243step0Labels permutation6 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical37294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37294 raw37294Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw37294 raw37294Labels = mixedMoment B raw37294step0 raw37294step0Labels := by
      have ha : raw37294step0 = (fun i j => raw37294 (permutation651 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37294step0 raw37294; decide +kernel
      have hl : raw37294step0Labels = raw37294Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37294 raw37294Labels permutation651 permutation7
    mixedMoment B raw37294step0 raw37294step0Labels = mixedMoment B raw37294step1 raw37294step1Labels := by
      have ha : raw37294step1 = raw37294step0 := by apply Matrix.ext; unfold raw37294step1 raw37294step0; decide +kernel
      have hl : raw37294step0Labels = labelEmbedding1 ∘ raw37294step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37294step0 raw37294step0Labels raw37294step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical37295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37295 raw37295Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw37295 raw37295Labels = mixedMoment B raw37295step0 raw37295step0Labels := by
      have ha : raw37295step0 = (fun i j => raw37295 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37295step0 raw37295; decide +kernel
      have hl : raw37295step0Labels = raw37295Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37295 raw37295Labels permutation650 permutation7
    mixedMoment B raw37295step0 raw37295step0Labels = mixedMoment B raw37295step1 raw37295step1Labels := by
      have ha : raw37295step1 = raw37295step0 := by apply Matrix.ext; unfold raw37295step1 raw37295step0; decide +kernel
      have hl : raw37295step0Labels = labelEmbedding1 ∘ raw37295step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37295step0 raw37295step0Labels raw37295step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical37296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37296 raw37296Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw37296 raw37296Labels = mixedMoment B raw37296step0 raw37296step0Labels := by
      have ha : raw37296step0 = (fun i j => raw37296 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37296step0 raw37296; decide +kernel
      have hl : raw37296step0Labels = raw37296Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37296 raw37296Labels permutation650 permutation7
    mixedMoment B raw37296step0 raw37296step0Labels = mixedMoment B raw37296step1 raw37296step1Labels := by
      have ha : raw37296step1 = raw37296step0 := by apply Matrix.ext; unfold raw37296step1 raw37296step0; decide +kernel
      have hl : raw37296step0Labels = labelEmbedding1 ∘ raw37296step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37296step0 raw37296step0Labels raw37296step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical37297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37297 raw37297Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw37297 raw37297Labels = mixedMoment B raw37297step0 raw37297step0Labels := by
      have ha : raw37297step0 = (fun i j => raw37297 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37297step0 raw37297; decide +kernel
      have hl : raw37297step0Labels = raw37297Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37297 raw37297Labels permutation650 permutation7
    mixedMoment B raw37297step0 raw37297step0Labels = mixedMoment B raw37297step1 raw37297step1Labels := by
      have ha : raw37297step1 = raw37297step0 := by apply Matrix.ext; unfold raw37297step1 raw37297step0; decide +kernel
      have hl : raw37297step0Labels = labelEmbedding1 ∘ raw37297step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37297step0 raw37297step0Labels raw37297step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

theorem canonical37298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37298 raw37298Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw37298 raw37298Labels = mixedMoment B raw37298step0 raw37298step0Labels := by
      have ha : raw37298step0 = (fun i j => raw37298 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37298step0 raw37298; decide +kernel
      have hl : raw37298step0Labels = raw37298Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37298 raw37298Labels permutation650 permutation7
    mixedMoment B raw37298step0 raw37298step0Labels = mixedMoment B raw37298step1 raw37298step1Labels := by
      have ha : raw37298step1 = raw37298step0 := by apply Matrix.ext; unfold raw37298step1 raw37298step0; decide +kernel
      have hl : raw37298step0Labels = labelEmbedding1 ∘ raw37298step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37298step0 raw37298step0Labels raw37298step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3979 node3979Labels := by rfl

theorem canonical37299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37299 raw37299Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw37299 raw37299Labels = mixedMoment B raw37299step0 raw37299step0Labels := by
      have ha : raw37299step0 = (fun i j => raw37299 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37299step0 raw37299; decide +kernel
      have hl : raw37299step0Labels = raw37299Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37299 raw37299Labels permutation186 permutation5
    mixedMoment B raw37299step0 raw37299step0Labels = mixedMoment B raw37299step1 raw37299step1Labels := by
      have ha : raw37299step1 = -raw37299step0 := by apply Matrix.ext; change ∀ i j, raw37299step1 i j = -(raw37299step0 i j); unfold raw37299step1 raw37299step0; decide +kernel
      have hl : raw37299step1Labels = raw37299step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37299step1 raw37299step1Labels = mixedMoment B raw37299step2 raw37299step2Labels := by
      have ha : raw37299step2 = raw37299step1 := by apply Matrix.ext; unfold raw37299step2 raw37299step1; decide +kernel
      have hl : raw37299step1Labels = labelEmbedding1 ∘ raw37299step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37299step1 raw37299step1Labels raw37299step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical37300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37300 raw37300Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw37300 raw37300Labels = mixedMoment B raw37300step0 raw37300step0Labels := by
      have ha : raw37300step0 = (fun i j => raw37300 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37300step0 raw37300; decide +kernel
      have hl : raw37300step0Labels = raw37300Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37300 raw37300Labels permutation186 permutation5
    mixedMoment B raw37300step0 raw37300step0Labels = mixedMoment B raw37300step1 raw37300step1Labels := by
      have ha : raw37300step1 = -raw37300step0 := by apply Matrix.ext; change ∀ i j, raw37300step1 i j = -(raw37300step0 i j); unfold raw37300step1 raw37300step0; decide +kernel
      have hl : raw37300step1Labels = raw37300step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37300step1 raw37300step1Labels = mixedMoment B raw37300step2 raw37300step2Labels := by
      have ha : raw37300step2 = raw37300step1 := by apply Matrix.ext; unfold raw37300step2 raw37300step1; decide +kernel
      have hl : raw37300step1Labels = labelEmbedding1 ∘ raw37300step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37300step1 raw37300step1Labels raw37300step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

theorem canonical37301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37301 raw37301Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw37301 raw37301Labels = mixedMoment B raw37301step0 raw37301step0Labels := by
      have ha : raw37301step0 = (fun i j => raw37301 (permutation210 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37301step0 raw37301; decide +kernel
      have hl : raw37301step0Labels = raw37301Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37301 raw37301Labels permutation210 permutation5
    mixedMoment B raw37301step0 raw37301step0Labels = mixedMoment B raw37301step1 raw37301step1Labels := by
      have ha : raw37301step1 = -raw37301step0 := by apply Matrix.ext; change ∀ i j, raw37301step1 i j = -(raw37301step0 i j); unfold raw37301step1 raw37301step0; decide +kernel
      have hl : raw37301step1Labels = raw37301step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37301step1 raw37301step1Labels = mixedMoment B raw37301step2 raw37301step2Labels := by
      have ha : raw37301step2 = raw37301step1 := by apply Matrix.ext; unfold raw37301step2 raw37301step1; decide +kernel
      have hl : raw37301step1Labels = labelEmbedding1 ∘ raw37301step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37301step1 raw37301step1Labels raw37301step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical37302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37302 raw37302Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw37302 raw37302Labels = mixedMoment B raw37302step0 raw37302step0Labels := by
      have ha : raw37302step0 = (fun i j => raw37302 (permutation648 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37302step0 raw37302; decide +kernel
      have hl : raw37302step0Labels = raw37302Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37302 raw37302Labels permutation648 permutation7
    mixedMoment B raw37302step0 raw37302step0Labels = mixedMoment B raw37302step1 raw37302step1Labels := by
      have ha : raw37302step1 = raw37302step0 := by apply Matrix.ext; unfold raw37302step1 raw37302step0; decide +kernel
      have hl : raw37302step0Labels = labelEmbedding1 ∘ raw37302step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37302step0 raw37302step0Labels raw37302step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical37303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37303 raw37303Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw37303 raw37303Labels = mixedMoment B raw37303step0 raw37303step0Labels := by
      have ha : raw37303step0 = (fun i j => raw37303 (permutation254 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37303step0 raw37303; decide +kernel
      have hl : raw37303step0Labels = raw37303Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37303 raw37303Labels permutation254 permutation5
    mixedMoment B raw37303step0 raw37303step0Labels = mixedMoment B raw37303step1 raw37303step1Labels := by
      have ha : raw37303step1 = -raw37303step0 := by apply Matrix.ext; change ∀ i j, raw37303step1 i j = -(raw37303step0 i j); unfold raw37303step1 raw37303step0; decide +kernel
      have hl : raw37303step1Labels = raw37303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37303step1 raw37303step1Labels = mixedMoment B raw37303step2 raw37303step2Labels := by
      have ha : raw37303step2 = raw37303step1 := by apply Matrix.ext; unfold raw37303step2 raw37303step1; decide +kernel
      have hl : raw37303step1Labels = labelEmbedding1 ∘ raw37303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37303step1 raw37303step1Labels raw37303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical37304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37304 raw37304Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw37304 raw37304Labels = mixedMoment B raw37304step0 raw37304step0Labels := by
      have ha : raw37304step0 = (fun i j => raw37304 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37304step0 raw37304; decide +kernel
      have hl : raw37304step0Labels = raw37304Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37304 raw37304Labels permutation162 permutation5
    mixedMoment B raw37304step0 raw37304step0Labels = mixedMoment B raw37304step1 raw37304step1Labels := by
      have ha : raw37304step1 = -raw37304step0 := by apply Matrix.ext; change ∀ i j, raw37304step1 i j = -(raw37304step0 i j); unfold raw37304step1 raw37304step0; decide +kernel
      have hl : raw37304step1Labels = raw37304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37304step1 raw37304step1Labels = mixedMoment B raw37304step2 raw37304step2Labels := by
      have ha : raw37304step2 = raw37304step1 := by apply Matrix.ext; unfold raw37304step2 raw37304step1; decide +kernel
      have hl : raw37304step1Labels = labelEmbedding1 ∘ raw37304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37304step1 raw37304step1Labels raw37304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical37305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37305 raw37305Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw37305 raw37305Labels = mixedMoment B raw37305step0 raw37305step0Labels := by
      have ha : raw37305step0 = (fun i j => raw37305 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37305step0 raw37305; decide +kernel
      have hl : raw37305step0Labels = raw37305Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37305 raw37305Labels permutation162 permutation5
    mixedMoment B raw37305step0 raw37305step0Labels = mixedMoment B raw37305step1 raw37305step1Labels := by
      have ha : raw37305step1 = -raw37305step0 := by apply Matrix.ext; change ∀ i j, raw37305step1 i j = -(raw37305step0 i j); unfold raw37305step1 raw37305step0; decide +kernel
      have hl : raw37305step1Labels = raw37305step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37305step1 raw37305step1Labels = mixedMoment B raw37305step2 raw37305step2Labels := by
      have ha : raw37305step2 = raw37305step1 := by apply Matrix.ext; unfold raw37305step2 raw37305step1; decide +kernel
      have hl : raw37305step1Labels = labelEmbedding1 ∘ raw37305step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37305step1 raw37305step1Labels raw37305step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

theorem canonical37306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37306 raw37306Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw37306 raw37306Labels = mixedMoment B raw37306step0 raw37306step0Labels := by
      have ha : raw37306step0 = (fun i j => raw37306 (permutation204 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37306step0 raw37306; decide +kernel
      have hl : raw37306step0Labels = raw37306Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37306 raw37306Labels permutation204 permutation5
    mixedMoment B raw37306step0 raw37306step0Labels = mixedMoment B raw37306step1 raw37306step1Labels := by
      have ha : raw37306step1 = -raw37306step0 := by apply Matrix.ext; change ∀ i j, raw37306step1 i j = -(raw37306step0 i j); unfold raw37306step1 raw37306step0; decide +kernel
      have hl : raw37306step1Labels = raw37306step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37306step1 raw37306step1Labels = mixedMoment B raw37306step2 raw37306step2Labels := by
      have ha : raw37306step2 = raw37306step1 := by apply Matrix.ext; unfold raw37306step2 raw37306step1; decide +kernel
      have hl : raw37306step1Labels = labelEmbedding1 ∘ raw37306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37306step1 raw37306step1Labels raw37306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical37307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37307 raw37307Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw37307 raw37307Labels = mixedMoment B raw37307step0 raw37307step0Labels := by
      have ha : raw37307step0 = (fun i j => raw37307 (permutation649 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37307step0 raw37307; decide +kernel
      have hl : raw37307step0Labels = raw37307Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37307 raw37307Labels permutation649 permutation7
    mixedMoment B raw37307step0 raw37307step0Labels = mixedMoment B raw37307step1 raw37307step1Labels := by
      have ha : raw37307step1 = raw37307step0 := by apply Matrix.ext; unfold raw37307step1 raw37307step0; decide +kernel
      have hl : raw37307step0Labels = labelEmbedding1 ∘ raw37307step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37307step0 raw37307step0Labels raw37307step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical37308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37308 raw37308Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw37308 raw37308Labels = mixedMoment B raw37308step0 raw37308step0Labels := by
      have ha : raw37308step0 = (fun i j => raw37308 (permutation248 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37308step0 raw37308; decide +kernel
      have hl : raw37308step0Labels = raw37308Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37308 raw37308Labels permutation248 permutation5
    mixedMoment B raw37308step0 raw37308step0Labels = mixedMoment B raw37308step1 raw37308step1Labels := by
      have ha : raw37308step1 = -raw37308step0 := by apply Matrix.ext; change ∀ i j, raw37308step1 i j = -(raw37308step0 i j); unfold raw37308step1 raw37308step0; decide +kernel
      have hl : raw37308step1Labels = raw37308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37308step1 raw37308step1Labels = mixedMoment B raw37308step2 raw37308step2Labels := by
      have ha : raw37308step2 = raw37308step1 := by apply Matrix.ext; unfold raw37308step2 raw37308step1; decide +kernel
      have hl : raw37308step1Labels = labelEmbedding1 ∘ raw37308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37308step1 raw37308step1Labels raw37308step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical37309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37309 raw37309Labels = mixedMoment B node2178 node2178Labels := by
  calc
    mixedMoment B raw37309 raw37309Labels = mixedMoment B raw37309step0 raw37309step0Labels := by
      have ha : raw37309step0 = (fun i j => raw37309 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37309step0 raw37309; decide +kernel
      have hl : raw37309step0Labels = raw37309Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37309 raw37309Labels permutation156 permutation5
    mixedMoment B raw37309step0 raw37309step0Labels = mixedMoment B raw37309step1 raw37309step1Labels := by
      have ha : raw37309step1 = -raw37309step0 := by apply Matrix.ext; change ∀ i j, raw37309step1 i j = -(raw37309step0 i j); unfold raw37309step1 raw37309step0; decide +kernel
      have hl : raw37309step1Labels = raw37309step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37309step1 raw37309step1Labels = mixedMoment B raw37309step2 raw37309step2Labels := by
      have ha : raw37309step2 = raw37309step1 := by apply Matrix.ext; unfold raw37309step2 raw37309step1; decide +kernel
      have hl : raw37309step1Labels = labelEmbedding1 ∘ raw37309step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37309step1 raw37309step1Labels raw37309step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2178 node2178Labels := by rfl

theorem canonical37310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37310 raw37310Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw37310 raw37310Labels = mixedMoment B raw37310step0 raw37310step0Labels := by
      have ha : raw37310step0 = (fun i j => raw37310 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37310step0 raw37310; decide +kernel
      have hl : raw37310step0Labels = raw37310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37310 raw37310Labels permutation156 permutation5
    mixedMoment B raw37310step0 raw37310step0Labels = mixedMoment B raw37310step1 raw37310step1Labels := by
      have ha : raw37310step1 = -raw37310step0 := by apply Matrix.ext; change ∀ i j, raw37310step1 i j = -(raw37310step0 i j); unfold raw37310step1 raw37310step0; decide +kernel
      have hl : raw37310step1Labels = raw37310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37310step1 raw37310step1Labels = mixedMoment B raw37310step2 raw37310step2Labels := by
      have ha : raw37310step2 = raw37310step1 := by apply Matrix.ext; unfold raw37310step2 raw37310step1; decide +kernel
      have hl : raw37310step1Labels = labelEmbedding1 ∘ raw37310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37310step1 raw37310step1Labels raw37310step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

theorem canonical37311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37311 raw37311Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw37311 raw37311Labels = mixedMoment B raw37311step0 raw37311step0Labels := by
      have ha : raw37311step0 = (fun i j => raw37311 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37311step0 raw37311; decide +kernel
      have hl : raw37311step0Labels = raw37311Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37311 raw37311Labels permutation180 permutation5
    mixedMoment B raw37311step0 raw37311step0Labels = mixedMoment B raw37311step1 raw37311step1Labels := by
      have ha : raw37311step1 = -raw37311step0 := by apply Matrix.ext; change ∀ i j, raw37311step1 i j = -(raw37311step0 i j); unfold raw37311step1 raw37311step0; decide +kernel
      have hl : raw37311step1Labels = raw37311step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37311step1 raw37311step1Labels = mixedMoment B raw37311step2 raw37311step2Labels := by
      have ha : raw37311step2 = raw37311step1 := by apply Matrix.ext; unfold raw37311step2 raw37311step1; decide +kernel
      have hl : raw37311step1Labels = labelEmbedding1 ∘ raw37311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37311step1 raw37311step1Labels raw37311step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

theorem canonical37312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37312 raw37312Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw37312 raw37312Labels = mixedMoment B raw37312step0 raw37312step0Labels := by
      have ha : raw37312step0 = (fun i j => raw37312 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37312step0 raw37312; decide +kernel
      have hl : raw37312step0Labels = raw37312Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37312 raw37312Labels permutation650 permutation7
    mixedMoment B raw37312step0 raw37312step0Labels = mixedMoment B raw37312step1 raw37312step1Labels := by
      have ha : raw37312step1 = raw37312step0 := by apply Matrix.ext; unfold raw37312step1 raw37312step0; decide +kernel
      have hl : raw37312step0Labels = labelEmbedding1 ∘ raw37312step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37312step0 raw37312step0Labels raw37312step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

theorem canonical37313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37313 raw37313Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw37313 raw37313Labels = mixedMoment B raw37313step0 raw37313step0Labels := by
      have ha : raw37313step0 = (fun i j => raw37313 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37313step0 raw37313; decide +kernel
      have hl : raw37313step0Labels = raw37313Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37313 raw37313Labels permutation246 permutation5
    mixedMoment B raw37313step0 raw37313step0Labels = mixedMoment B raw37313step1 raw37313step1Labels := by
      have ha : raw37313step1 = -raw37313step0 := by apply Matrix.ext; change ∀ i j, raw37313step1 i j = -(raw37313step0 i j); unfold raw37313step1 raw37313step0; decide +kernel
      have hl : raw37313step1Labels = raw37313step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37313step1 raw37313step1Labels = mixedMoment B raw37313step2 raw37313step2Labels := by
      have ha : raw37313step2 = raw37313step1 := by apply Matrix.ext; unfold raw37313step2 raw37313step1; decide +kernel
      have hl : raw37313step1Labels = labelEmbedding1 ∘ raw37313step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37313step1 raw37313step1Labels raw37313step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

theorem canonical37314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37314 raw37314Labels = mixedMoment B node2171 node2171Labels := by
  calc
    mixedMoment B raw37314 raw37314Labels = mixedMoment B raw37314step0 raw37314step0Labels := by
      have ha : raw37314step0 = (fun i j => raw37314 (permutation153 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37314step0 raw37314; decide +kernel
      have hl : raw37314step0Labels = raw37314Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37314 raw37314Labels permutation153 permutation5
    mixedMoment B raw37314step0 raw37314step0Labels = mixedMoment B raw37314step1 raw37314step1Labels := by
      have ha : raw37314step1 = -raw37314step0 := by apply Matrix.ext; change ∀ i j, raw37314step1 i j = -(raw37314step0 i j); unfold raw37314step1 raw37314step0; decide +kernel
      have hl : raw37314step1Labels = raw37314step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37314step1 raw37314step1Labels = mixedMoment B raw37314step2 raw37314step2Labels := by
      have ha : raw37314step2 = raw37314step1 := by apply Matrix.ext; unfold raw37314step2 raw37314step1; decide +kernel
      have hl : raw37314step1Labels = labelEmbedding1 ∘ raw37314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37314step1 raw37314step1Labels raw37314step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2171 node2171Labels := by rfl

theorem canonical37315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37315 raw37315Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw37315 raw37315Labels = mixedMoment B raw37315step0 raw37315step0Labels := by
      have ha : raw37315step0 = (fun i j => raw37315 (permutation589 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37315step0 raw37315; decide +kernel
      have hl : raw37315step0Labels = raw37315Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37315 raw37315Labels permutation589 permutation5
    mixedMoment B raw37315step0 raw37315step0Labels = mixedMoment B raw37315step1 raw37315step1Labels := by
      have ha : raw37315step1 = raw37315step0 := by apply Matrix.ext; unfold raw37315step1 raw37315step0; decide +kernel
      have hl : raw37315step0Labels = labelEmbedding1 ∘ raw37315step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37315step0 raw37315step0Labels raw37315step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

theorem canonical37316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37316 raw37316Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw37316 raw37316Labels = mixedMoment B raw37316step0 raw37316step0Labels := by
      have ha : raw37316step0 = (fun i j => raw37316 (permutation587 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37316step0 raw37316; decide +kernel
      have hl : raw37316step0Labels = raw37316Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37316 raw37316Labels permutation587 permutation5
    mixedMoment B raw37316step0 raw37316step0Labels = mixedMoment B raw37316step1 raw37316step1Labels := by
      have ha : raw37316step1 = raw37316step0 := by apply Matrix.ext; unfold raw37316step1 raw37316step0; decide +kernel
      have hl : raw37316step0Labels = labelEmbedding1 ∘ raw37316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37316step0 raw37316step0Labels raw37316step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

theorem canonical37317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37317 raw37317Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw37317 raw37317Labels = mixedMoment B raw37317step0 raw37317step0Labels := by
      have ha : raw37317step0 = (fun i j => raw37317 (permutation577 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37317step0 raw37317; decide +kernel
      have hl : raw37317step0Labels = raw37317Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37317 raw37317Labels permutation577 permutation5
    mixedMoment B raw37317step0 raw37317step0Labels = mixedMoment B raw37317step1 raw37317step1Labels := by
      have ha : raw37317step1 = raw37317step0 := by apply Matrix.ext; unfold raw37317step1 raw37317step0; decide +kernel
      have hl : raw37317step0Labels = labelEmbedding1 ∘ raw37317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37317step0 raw37317step0Labels raw37317step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

theorem canonical37318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37318 raw37318Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw37318 raw37318Labels = mixedMoment B raw37318step0 raw37318step0Labels := by
      have ha : raw37318step0 = (fun i j => raw37318 (permutation557 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37318step0 raw37318; decide +kernel
      have hl : raw37318step0Labels = raw37318Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37318 raw37318Labels permutation557 permutation5
    mixedMoment B raw37318step0 raw37318step0Labels = mixedMoment B raw37318step1 raw37318step1Labels := by
      have ha : raw37318step1 = raw37318step0 := by apply Matrix.ext; unfold raw37318step1 raw37318step0; decide +kernel
      have hl : raw37318step0Labels = labelEmbedding1 ∘ raw37318step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37318step0 raw37318step0Labels raw37318step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2708 node2708Labels := by rfl

theorem canonical37319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37319 raw37319Labels = mixedMoment B node2175 node2175Labels := by
  calc
    mixedMoment B raw37319 raw37319Labels = mixedMoment B raw37319step0 raw37319step0Labels := by
      have ha : raw37319step0 = (fun i j => raw37319 (permutation153 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37319step0 raw37319; decide +kernel
      have hl : raw37319step0Labels = raw37319Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37319 raw37319Labels permutation153 permutation5
    mixedMoment B raw37319step0 raw37319step0Labels = mixedMoment B raw37319step1 raw37319step1Labels := by
      have ha : raw37319step1 = -raw37319step0 := by apply Matrix.ext; change ∀ i j, raw37319step1 i j = -(raw37319step0 i j); unfold raw37319step1 raw37319step0; decide +kernel
      have hl : raw37319step1Labels = raw37319step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37319step1 raw37319step1Labels = mixedMoment B raw37319step2 raw37319step2Labels := by
      have ha : raw37319step2 = raw37319step1 := by apply Matrix.ext; unfold raw37319step2 raw37319step1; decide +kernel
      have hl : raw37319step1Labels = labelEmbedding1 ∘ raw37319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37319step1 raw37319step1Labels raw37319step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2175 node2175Labels := by rfl

theorem canonical37320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37320 raw37320Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw37320 raw37320Labels = mixedMoment B raw37320step0 raw37320step0Labels := by
      have ha : raw37320step0 = (fun i j => raw37320 (permutation651 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37320step0 raw37320; decide +kernel
      have hl : raw37320step0Labels = raw37320Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37320 raw37320Labels permutation651 permutation7
    mixedMoment B raw37320step0 raw37320step0Labels = mixedMoment B raw37320step1 raw37320step1Labels := by
      have ha : raw37320step1 = raw37320step0 := by apply Matrix.ext; unfold raw37320step1 raw37320step0; decide +kernel
      have hl : raw37320step0Labels = labelEmbedding1 ∘ raw37320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37320step0 raw37320step0Labels raw37320step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

theorem canonical37321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37321 raw37321Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw37321 raw37321Labels = mixedMoment B raw37321step0 raw37321step0Labels := by
      have ha : raw37321step0 = (fun i j => raw37321 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37321step0 raw37321; decide +kernel
      have hl : raw37321step0Labels = raw37321Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37321 raw37321Labels permutation650 permutation7
    mixedMoment B raw37321step0 raw37321step0Labels = mixedMoment B raw37321step1 raw37321step1Labels := by
      have ha : raw37321step1 = raw37321step0 := by apply Matrix.ext; unfold raw37321step1 raw37321step0; decide +kernel
      have hl : raw37321step0Labels = labelEmbedding1 ∘ raw37321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37321step0 raw37321step0Labels raw37321step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

theorem canonical37322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37322 raw37322Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw37322 raw37322Labels = mixedMoment B raw37322step0 raw37322step0Labels := by
      have ha : raw37322step0 = (fun i j => raw37322 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37322step0 raw37322; decide +kernel
      have hl : raw37322step0Labels = raw37322Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37322 raw37322Labels permutation650 permutation7
    mixedMoment B raw37322step0 raw37322step0Labels = mixedMoment B raw37322step1 raw37322step1Labels := by
      have ha : raw37322step1 = raw37322step0 := by apply Matrix.ext; unfold raw37322step1 raw37322step0; decide +kernel
      have hl : raw37322step0Labels = labelEmbedding1 ∘ raw37322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37322step0 raw37322step0Labels raw37322step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

theorem canonical37323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37323 raw37323Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw37323 raw37323Labels = mixedMoment B raw37323step0 raw37323step0Labels := by
      have ha : raw37323step0 = (fun i j => raw37323 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37323step0 raw37323; decide +kernel
      have hl : raw37323step0Labels = raw37323Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37323 raw37323Labels permutation650 permutation7
    mixedMoment B raw37323step0 raw37323step0Labels = mixedMoment B raw37323step1 raw37323step1Labels := by
      have ha : raw37323step1 = raw37323step0 := by apply Matrix.ext; unfold raw37323step1 raw37323step0; decide +kernel
      have hl : raw37323step0Labels = labelEmbedding1 ∘ raw37323step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37323step0 raw37323step0Labels raw37323step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

theorem canonical37324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37324 raw37324Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37324 raw37324Labels = mixedMoment B raw37324step0 raw37324step0Labels := by
      have hz : ∀ j, raw37324 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37324step0 = (fun i j => raw37324 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37324step0 raw37324; decide +kernel
      have hl : raw37324step0Labels = raw37324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37324 raw37324Labels permutation265 hz
    mixedMoment B raw37324step0 raw37324step0Labels = mixedMoment B raw37324step1 raw37324step1Labels := by
      have hz : ∀ i, raw37324step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37324step1 = (fun i j => raw37324step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37324step1 raw37324step0; decide +kernel
      have hl : raw37324step1Labels = (fun j => raw37324step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37324step0 raw37324step0Labels permutation6 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical37325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37325 raw37325Labels = mixedMoment B node4086 node4086Labels := by
  calc
    mixedMoment B raw37325 raw37325Labels = mixedMoment B raw37325step0 raw37325step0Labels := by
      have hz : ∀ i, raw37325 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37325step0 = (fun i j => raw37325 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37325step0 raw37325; decide +kernel
      have hl : raw37325step0Labels = (fun j => raw37325Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37325 raw37325Labels permutation6 hz
    mixedMoment B raw37325step0 raw37325step0Labels = mixedMoment B raw37325step1 raw37325step1Labels := by
      have ha : raw37325step1 = (fun i j => raw37325step0 (permutation178 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37325step1 raw37325step0; decide +kernel
      have hl : raw37325step1Labels = raw37325step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37325step0 raw37325step0Labels permutation178 permutation0
    _ = mixedMoment B node4086 node4086Labels := by rfl

theorem canonical37326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37326 raw37326Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37326 raw37326Labels = mixedMoment B raw37326step0 raw37326step0Labels := by
      have hz : ∀ j, raw37326 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37326step0 = (fun i j => raw37326 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37326step0 raw37326; decide +kernel
      have hl : raw37326step0Labels = raw37326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37326 raw37326Labels permutation520 hz
    mixedMoment B raw37326step0 raw37326step0Labels = mixedMoment B raw37326step1 raw37326step1Labels := by
      have hz : ∀ i, raw37326step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37326step1 = (fun i j => raw37326step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37326step1 raw37326step0; decide +kernel
      have hl : raw37326step1Labels = (fun j => raw37326step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37326step0 raw37326step0Labels permutation6 hz
    mixedMoment B raw37326step1 raw37326step1Labels = mixedMoment B raw37326step2 raw37326step2Labels := by
      have ha : raw37326step2 = (fun i j => raw37326step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37326step2 raw37326step1; decide +kernel
      have hl : raw37326step2Labels = raw37326step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37326step1 raw37326step1Labels permutation125 permutation0
    mixedMoment B raw37326step2 raw37326step2Labels = mixedMoment B raw37326step3 raw37326step3Labels := by
      have ha : raw37326step3 = -raw37326step2 := by apply Matrix.ext; change ∀ i j, raw37326step3 i j = -(raw37326step2 i j); unfold raw37326step3 raw37326step2; decide +kernel
      have hl : raw37326step3Labels = raw37326step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical37327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37327 raw37327Labels = mixedMoment B node4086 node4086Labels := by
  calc
    mixedMoment B raw37327 raw37327Labels = mixedMoment B raw37327step0 raw37327step0Labels := by
      have hz : ∀ i, raw37327 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37327step0 = (fun i j => raw37327 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37327step0 raw37327; decide +kernel
      have hl : raw37327step0Labels = (fun j => raw37327Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37327 raw37327Labels permutation6 hz
    mixedMoment B raw37327step0 raw37327step0Labels = mixedMoment B raw37327step1 raw37327step1Labels := by
      have ha : raw37327step1 = (fun i j => raw37327step0 (permutation176 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37327step1 raw37327step0; decide +kernel
      have hl : raw37327step1Labels = raw37327step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37327step0 raw37327step0Labels permutation176 permutation0
    _ = mixedMoment B node4086 node4086Labels := by rfl

theorem canonical37328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37328 raw37328Labels = mixedMoment B node4078 node4078Labels := by
  calc
    mixedMoment B raw37328 raw37328Labels = mixedMoment B raw37328step0 raw37328step0Labels := by
      have hz : ∀ i, raw37328 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37328step0 = (fun i j => raw37328 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37328step0 raw37328; decide +kernel
      have hl : raw37328step0Labels = (fun j => raw37328Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37328 raw37328Labels permutation6 hz
    mixedMoment B raw37328step0 raw37328step0Labels = mixedMoment B raw37328step1 raw37328step1Labels := by
      have ha : raw37328step1 = (fun i j => raw37328step0 (permutation661 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37328step1 raw37328step0; decide +kernel
      have hl : raw37328step1Labels = raw37328step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37328step0 raw37328step0Labels permutation661 permutation0
    mixedMoment B raw37328step1 raw37328step1Labels = mixedMoment B raw37328step2 raw37328step2Labels := by
      have ha : raw37328step2 = -raw37328step1 := by apply Matrix.ext; change ∀ i j, raw37328step2 i j = -(raw37328step1 i j); unfold raw37328step2 raw37328step1; decide +kernel
      have hl : raw37328step2Labels = raw37328step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4078 node4078Labels := by rfl

theorem canonical37329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37329 raw37329Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw37329 raw37329Labels = mixedMoment B raw37329step0 raw37329step0Labels := by
      have hz : ∀ j, raw37329 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37329step0 = (fun i j => raw37329 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37329step0 raw37329; decide +kernel
      have hl : raw37329step0Labels = raw37329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37329 raw37329Labels permutation520 hz
    mixedMoment B raw37329step0 raw37329step0Labels = mixedMoment B raw37329step1 raw37329step1Labels := by
      have hz : ∀ i, raw37329step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37329step1 = (fun i j => raw37329step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37329step1 raw37329step0; decide +kernel
      have hl : raw37329step1Labels = (fun j => raw37329step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37329step0 raw37329step0Labels permutation6 hz
    mixedMoment B raw37329step1 raw37329step1Labels = mixedMoment B raw37329step2 raw37329step2Labels := by
      have ha : raw37329step2 = (fun i j => raw37329step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37329step2 raw37329step1; decide +kernel
      have hl : raw37329step2Labels = raw37329step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37329step1 raw37329step1Labels permutation149 permutation0
    mixedMoment B raw37329step2 raw37329step2Labels = mixedMoment B raw37329step3 raw37329step3Labels := by
      have ha : raw37329step3 = -raw37329step2 := by apply Matrix.ext; change ∀ i j, raw37329step3 i j = -(raw37329step2 i j); unfold raw37329step3 raw37329step2; decide +kernel
      have hl : raw37329step3Labels = raw37329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11538 raw11538Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11538 raw11538Labels = mixedMoment B raw11538step0 raw11538step0Labels := by
      have hz : ∀ j, raw11538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11538step0 = (fun i j => raw11538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11538step0 raw11538; decide +kernel
      have hl : raw11538step0Labels = raw11538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11538 raw11538Labels permutation346 hz
    mixedMoment B raw11538step0 raw11538step0Labels = mixedMoment B raw11538step1 raw11538step1Labels := by
      have hz : ∀ i, raw11538step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11538step1 = (fun i j => raw11538step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11538step1 raw11538step0; decide +kernel
      have hl : raw11538step1Labels = (fun j => raw11538step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11538step0 raw11538step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical11539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11539 raw11539Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11539 raw11539Labels = mixedMoment B raw11539step0 raw11539step0Labels := by
      have hz : ∀ j, raw11539 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11539step0 = (fun i j => raw11539 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11539step0 raw11539; decide +kernel
      have hl : raw11539step0Labels = raw11539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11539 raw11539Labels permutation265 hz
    mixedMoment B raw11539step0 raw11539step0Labels = mixedMoment B raw11539step1 raw11539step1Labels := by
      have hz : ∀ i, raw11539step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11539step1 = (fun i j => raw11539step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11539step1 raw11539step0; decide +kernel
      have hl : raw11539step1Labels = (fun j => raw11539step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11539step0 raw11539step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2139 node2139Labels = Sparse.eval nodeValue2139 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2139) = mixedMoment B node2139 node2139Labels := rfl
  simpa [nodeValue2139, Sparse.eval] using hc.symm

theorem sound2142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2142 node2142Labels = Sparse.eval nodeValue2142 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2142) = mixedMoment B node2142 node2142Labels := rfl
  simpa [nodeValue2142, Sparse.eval] using hc.symm

theorem sound2150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2150 node2150Labels = Sparse.eval nodeValue2150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2150) = mixedMoment B node2150 node2150Labels := rfl
  simpa [nodeValue2150, Sparse.eval] using hc.symm

theorem sound2156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2156 node2156Labels = Sparse.eval nodeValue2156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2156) = mixedMoment B node2156 node2156Labels := rfl
  simpa [nodeValue2156, Sparse.eval] using hc.symm

theorem sound2171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2171 node2171Labels = Sparse.eval nodeValue2171 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2171) = mixedMoment B node2171 node2171Labels := rfl
  simpa [nodeValue2171, Sparse.eval] using hc.symm

theorem sound2175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2175 node2175Labels = Sparse.eval nodeValue2175 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2175) = mixedMoment B node2175 node2175Labels := rfl
  simpa [nodeValue2175, Sparse.eval] using hc.symm

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

theorem zero2204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2204 node2204Labels = 0 := by
  exact mixedMoment_order_one B hB node2204 node2204Labels 1
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

theorem sound2178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2178 node2178Labels = Sparse.eval nodeValue2178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2178) = mixedMoment B node2178 node2178Labels := rfl
  simpa [nodeValue2178, Sparse.eval] using hc.symm

theorem sound2195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2195 node2195Labels = Sparse.eval nodeValue2195 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2195) = mixedMoment B node2195 node2195Labels := rfl
  simpa [nodeValue2195, Sparse.eval] using hc.symm

theorem sound2204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2204 node2204Labels = Sparse.eval nodeValue2204 (mixedVector B) := by
  simpa only [nodeValue2204, Sparse.eval_nil] using zero2204 B _hB _hF

theorem sound2231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2231 node2231Labels = Sparse.eval nodeValue2231 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2231) = mixedMoment B node2231 node2231Labels := rfl
  simpa [nodeValue2231, Sparse.eval] using hc.symm

theorem sound2232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2232 node2232Labels = Sparse.eval nodeValue2232 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2232) = mixedMoment B node2232 node2232Labels := rfl
  simpa [nodeValue2232, Sparse.eval] using hc.symm

theorem sound2234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2234 node2234Labels = Sparse.eval nodeValue2234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2234) = mixedMoment B node2234 node2234Labels := rfl
  simpa [nodeValue2234, Sparse.eval] using hc.symm

theorem sound2238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2238 node2238Labels = Sparse.eval nodeValue2238 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2238) = mixedMoment B node2238 node2238Labels := rfl
  simpa [nodeValue2238, Sparse.eval] using hc.symm

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

theorem sound2653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2653 node2653Labels = Sparse.eval nodeValue2653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2653) = mixedMoment B node2653 node2653Labels := rfl
  simpa [nodeValue2653, Sparse.eval] using hc.symm

theorem sound2661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2661 node2661Labels = Sparse.eval nodeValue2661 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2661) = mixedMoment B node2661 node2661Labels := rfl
  simpa [nodeValue2661, Sparse.eval] using hc.symm

theorem sound2669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2669 node2669Labels = Sparse.eval nodeValue2669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2669) = mixedMoment B node2669 node2669Labels := rfl
  simpa [nodeValue2669, Sparse.eval] using hc.symm

theorem sound2676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2676 node2676Labels = Sparse.eval nodeValue2676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2676) = mixedMoment B node2676 node2676Labels := rfl
  simpa [nodeValue2676, Sparse.eval] using hc.symm

theorem sound2684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2684 node2684Labels = Sparse.eval nodeValue2684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2684) = mixedMoment B node2684 node2684Labels := rfl
  simpa [nodeValue2684, Sparse.eval] using hc.symm

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

theorem zero2741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2741 node2741Labels = 0 := by
  exact mixedMoment_order_one B hB node2741 node2741Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2690 node2690Labels = Sparse.eval nodeValue2690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2690) = mixedMoment B node2690 node2690Labels := rfl
  simpa [nodeValue2690, Sparse.eval] using hc.symm

theorem sound2697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2697 node2697Labels = Sparse.eval nodeValue2697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2697) = mixedMoment B node2697 node2697Labels := rfl
  simpa [nodeValue2697, Sparse.eval] using hc.symm

theorem sound2708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2708 node2708Labels = Sparse.eval nodeValue2708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2708) = mixedMoment B node2708 node2708Labels := rfl
  simpa [nodeValue2708, Sparse.eval] using hc.symm

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

theorem sound2741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2741 node2741Labels = Sparse.eval nodeValue2741 (mixedVector B) := by
  simpa only [nodeValue2741, Sparse.eval_nil] using zero2741 B _hB _hF

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

theorem sound3037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3037 node3037Labels = Sparse.eval nodeValue3037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3037) = mixedMoment B node3037 node3037Labels := rfl
  simpa [nodeValue3037, Sparse.eval] using hc.symm

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

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

theorem sound3474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3474 node3474Labels = Sparse.eval nodeValue3474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3474) = mixedMoment B node3474 node3474Labels := rfl
  simpa [nodeValue3474, Sparse.eval] using hc.symm

theorem sound3477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3477 node3477Labels = Sparse.eval nodeValue3477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3477) = mixedMoment B node3477 node3477Labels := rfl
  simpa [nodeValue3477, Sparse.eval] using hc.symm

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

theorem sound3537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3537 node3537Labels = Sparse.eval nodeValue3537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3537) = mixedMoment B node3537 node3537Labels := rfl
  simpa [nodeValue3537, Sparse.eval] using hc.symm

theorem sound3554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3554 node3554Labels = Sparse.eval nodeValue3554 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3554) = mixedMoment B node3554 node3554Labels := rfl
  simpa [nodeValue3554, Sparse.eval] using hc.symm

theorem sound3563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3563 node3563Labels = Sparse.eval nodeValue3563 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3563) = mixedMoment B node3563 node3563Labels := rfl
  simpa [nodeValue3563, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3755 node3755Labels = Sparse.eval nodeValue3755 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3755) = mixedMoment B node3755 node3755Labels := rfl
  simpa [nodeValue3755, Sparse.eval] using hc.symm

theorem sound3761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3761 node3761Labels = Sparse.eval nodeValue3761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3761) = mixedMoment B node3761 node3761Labels := rfl
  simpa [nodeValue3761, Sparse.eval] using hc.symm

theorem sound3769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3769 node3769Labels = Sparse.eval nodeValue3769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3769) = mixedMoment B node3769 node3769Labels := rfl
  simpa [nodeValue3769, Sparse.eval] using hc.symm

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

theorem zero3806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = 0 := by
  exact mixedMoment_order_one B hB node3806 node3806Labels 1
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

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = Sparse.eval nodeValue3806 (mixedVector B) := by
  simpa only [nodeValue3806, Sparse.eval_nil] using zero3806 B _hB _hF

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

theorem sound3832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3832 node3832Labels = Sparse.eval nodeValue3832 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3832) = mixedMoment B node3832 node3832Labels := rfl
  simpa [nodeValue3832, Sparse.eval] using hc.symm

theorem sound3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3836 node3836Labels = Sparse.eval nodeValue3836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3836) = mixedMoment B node3836 node3836Labels := rfl
  simpa [nodeValue3836, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3844 node3844Labels = 0 := by
  exact mixedMoment_order_one B hB node3844 node3844Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3840 node3840Labels = Sparse.eval nodeValue3840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3840) = mixedMoment B node3840 node3840Labels := rfl
  simpa [nodeValue3840, Sparse.eval] using hc.symm

theorem sound3844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3844 node3844Labels = Sparse.eval nodeValue3844 (mixedVector B) := by
  simpa only [nodeValue3844, Sparse.eval_nil] using zero3844 B _hB _hF

theorem sound3846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3846 node3846Labels = Sparse.eval nodeValue3846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3846) = mixedMoment B node3846 node3846Labels := rfl
  simpa [nodeValue3846, Sparse.eval] using hc.symm

theorem sound3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3849 node3849Labels = Sparse.eval nodeValue3849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3849) = mixedMoment B node3849 node3849Labels := rfl
  simpa [nodeValue3849, Sparse.eval] using hc.symm

theorem sound3869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3869 node3869Labels = Sparse.eval nodeValue3869 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3869) = mixedMoment B node3869 node3869Labels := rfl
  simpa [nodeValue3869, Sparse.eval] using hc.symm

theorem sound3871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3871 node3871Labels = Sparse.eval nodeValue3871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3871) = mixedMoment B node3871 node3871Labels := rfl
  simpa [nodeValue3871, Sparse.eval] using hc.symm

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

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

theorem sound3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3909 node3909Labels = Sparse.eval nodeValue3909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3909) = mixedMoment B node3909 node3909Labels := rfl
  simpa [nodeValue3909, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3979 node3979Labels = 0 := by
  exact mixedMoment_alpha B hF node3979 node3979Labels 2 permutation158
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3979 node3979Labels = Sparse.eval nodeValue3979 (mixedVector B) := by
  simpa only [nodeValue3979, Sparse.eval_nil] using zero3979 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4095 node4095Labels = 0 := by
  exact mixedMoment_alpha B hF node4095 node4095Labels 0 permutation499
    (by decide +kernel)

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

theorem sound4073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4073 node4073Labels = Sparse.eval nodeValue4073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4073) = mixedMoment B node4073 node4073Labels := rfl
  simpa [nodeValue4073, Sparse.eval] using hc.symm

theorem sound4074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4074 node4074Labels = Sparse.eval nodeValue4074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4074) = mixedMoment B node4074 node4074Labels := rfl
  simpa [nodeValue4074, Sparse.eval] using hc.symm

theorem sound4075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4075 node4075Labels = Sparse.eval nodeValue4075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4075) = mixedMoment B node4075 node4075Labels := rfl
  simpa [nodeValue4075, Sparse.eval] using hc.symm

theorem sound4077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4077 node4077Labels = Sparse.eval nodeValue4077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4077) = mixedMoment B node4077 node4077Labels := rfl
  simpa [nodeValue4077, Sparse.eval] using hc.symm

theorem sound4078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4078 node4078Labels = Sparse.eval nodeValue4078 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4078) = mixedMoment B node4078 node4078Labels := rfl
  simpa [nodeValue4078, Sparse.eval] using hc.symm

theorem sound4079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4079 node4079Labels = Sparse.eval nodeValue4079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4079) = mixedMoment B node4079 node4079Labels := rfl
  simpa [nodeValue4079, Sparse.eval] using hc.symm

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

theorem sound4086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4086 node4086Labels = Sparse.eval nodeValue4086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4086) = mixedMoment B node4086 node4086Labels := rfl
  simpa [nodeValue4086, Sparse.eval] using hc.symm

theorem sound4087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4087 node4087Labels = Sparse.eval nodeValue4087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4087) = mixedMoment B node4087 node4087Labels := rfl
  simpa [nodeValue4087, Sparse.eval] using hc.symm

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

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

theorem sound4095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4095 node4095Labels = Sparse.eval nodeValue4095 (mixedVector B) := by
  simpa only [nodeValue4095, Sparse.eval_nil] using zero4095 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2638 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2638 + difference 0 1) (sourceB2638 + difference 1 0) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2638 + difference 0 1) (sourceB2638 + difference 1 0) sourceC2638) = raw37017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37017; decide +kernel
    rw [ha]
    exact (canonical37017 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2638 + difference 0 2) (sourceB2638 + difference 2 0) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2638 + difference 0 2) (sourceB2638 + difference 2 0) sourceC2638) = raw19404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw19404; decide +kernel
    rw [ha]
    exact (canonical19404 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2638 + difference 0 3) (sourceB2638 + difference 3 0) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2638 + difference 0 3) (sourceB2638 + difference 3 0) sourceC2638) = raw3448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw3448; decide +kernel
    rw [ha]
    exact (canonical3448 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2638 + difference 0 4) (sourceB2638 + difference 4 0) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2638 + difference 0 4) (sourceB2638 + difference 4 0) sourceC2638) = raw37018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37018; decide +kernel
    rw [ha]
    exact (canonical37018 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2638 + difference 0 5) (sourceB2638 + difference 5 0) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2638 + difference 0 5) (sourceB2638 + difference 5 0) sourceC2638) = raw3440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw3440; decide +kernel
    rw [ha]
    exact (canonical3440 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2638 + difference 1 0) (sourceB2638 + difference 0 1) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2638 + difference 1 0) (sourceB2638 + difference 0 1) sourceC2638) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2638 + difference 1 2) (sourceB2638 + difference 2 1) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2638 + difference 1 2) (sourceB2638 + difference 2 1) sourceC2638) = raw18338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw18338; decide +kernel
    rw [ha]
    exact (canonical18338 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2638 + difference 1 3) (sourceB2638 + difference 3 1) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2638 + difference 1 3) (sourceB2638 + difference 3 1) sourceC2638) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2638 + difference 1 4) (sourceB2638 + difference 4 1) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2638 + difference 1 4) (sourceB2638 + difference 4 1) sourceC2638) = raw2925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw2925; decide +kernel
    rw [ha]
    exact (canonical2925 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2638 + difference 1 5) (sourceB2638 + difference 5 1) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2638 + difference 1 5) (sourceB2638 + difference 5 1) sourceC2638) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2638 + difference 2 0) (sourceB2638 + difference 0 2) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2638 + difference 2 0) (sourceB2638 + difference 0 2) sourceC2638) = raw34405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw34405; decide +kernel
    rw [ha]
    exact (canonical34405 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2638 + difference 2 1) (sourceB2638 + difference 1 2) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2638 + difference 2 1) (sourceB2638 + difference 1 2) sourceC2638) = raw37019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37019; decide +kernel
    rw [ha]
    exact (canonical37019 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2638 + difference 2 3) (sourceB2638 + difference 3 2) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2638 + difference 2 3) (sourceB2638 + difference 3 2) sourceC2638) = raw18335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw18335; decide +kernel
    rw [ha]
    exact (canonical18335 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2638 + difference 2 4) (sourceB2638 + difference 4 2) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2638 + difference 2 4) (sourceB2638 + difference 4 2) sourceC2638) = raw37020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37020; decide +kernel
    rw [ha]
    exact (canonical37020 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2638 + difference 2 5) (sourceB2638 + difference 5 2) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (tripleCharges (sourceA2638 + difference 2 5) (sourceB2638 + difference 5 2) sourceC2638) = raw19360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw19360; decide +kernel
    rw [ha]
    exact (canonical19360 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2638 + difference 3 0) (sourceB2638 + difference 0 3) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2638 + difference 3 0) (sourceB2638 + difference 0 3) sourceC2638) = raw34407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw34407; decide +kernel
    rw [ha]
    exact (canonical34407 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2638 + difference 3 1) (sourceB2638 + difference 1 3) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2638 + difference 3 1) (sourceB2638 + difference 1 3) sourceC2638) = raw37021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37021; decide +kernel
    rw [ha]
    exact (canonical37021 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2638 + difference 3 2) (sourceB2638 + difference 2 3) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2638 + difference 3 2) (sourceB2638 + difference 2 3) sourceC2638) = raw37022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37022; decide +kernel
    rw [ha]
    exact (canonical37022 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2638 + difference 3 4) (sourceB2638 + difference 4 3) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (tripleCharges (sourceA2638 + difference 3 4) (sourceB2638 + difference 4 3) sourceC2638) = raw37023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37023; decide +kernel
    rw [ha]
    exact (canonical37023 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2638 + difference 3 5) (sourceB2638 + difference 5 3) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2638 + difference 3 5) (sourceB2638 + difference 5 3) sourceC2638) = raw19363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw19363; decide +kernel
    rw [ha]
    exact (canonical19363 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2638 + difference 4 0) (sourceB2638 + difference 0 4) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2638 + difference 4 0) (sourceB2638 + difference 0 4) sourceC2638) = raw31880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw31880; decide +kernel
    rw [ha]
    exact (canonical31880 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2638 + difference 4 1) (sourceB2638 + difference 1 4) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2638 + difference 4 1) (sourceB2638 + difference 1 4) sourceC2638) = raw35540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw35540; decide +kernel
    rw [ha]
    exact (canonical35540 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2638 + difference 4 2) (sourceB2638 + difference 2 4) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2638 + difference 4 2) (sourceB2638 + difference 2 4) sourceC2638) = raw35541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw35541; decide +kernel
    rw [ha]
    exact (canonical35541 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2638 + difference 4 3) (sourceB2638 + difference 3 4) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (tripleCharges (sourceA2638 + difference 4 3) (sourceB2638 + difference 3 4) sourceC2638) = raw18339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw18339; decide +kernel
    rw [ha]
    exact (canonical18339 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2638 + difference 4 5) (sourceB2638 + difference 5 4) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2638 + difference 4 5) (sourceB2638 + difference 5 4) sourceC2638) = raw19367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw19367; decide +kernel
    rw [ha]
    exact (canonical19367 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2638 + difference 5 0) (sourceB2638 + difference 0 5) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2638 + difference 5 0) (sourceB2638 + difference 0 5) sourceC2638) = raw29297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw29297; decide +kernel
    rw [ha]
    exact (canonical29297 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2638 + difference 5 1) (sourceB2638 + difference 1 5) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2638 + difference 5 1) (sourceB2638 + difference 1 5) sourceC2638) = raw37024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37024; decide +kernel
    rw [ha]
    exact (canonical37024 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2638 + difference 5 2) (sourceB2638 + difference 2 5) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2638 + difference 5 2) (sourceB2638 + difference 2 5) sourceC2638) = raw37025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37025; decide +kernel
    rw [ha]
    exact (canonical37025 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2638 + difference 5 3) (sourceB2638 + difference 3 5) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2638 + difference 5 3) (sourceB2638 + difference 3 5) sourceC2638) = raw18342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw18342; decide +kernel
    rw [ha]
    exact (canonical18342 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2638 + difference 5 4) (sourceB2638 + difference 4 5) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2638 + difference 5 4) (sourceB2638 + difference 4 5) sourceC2638) = raw37026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37026; decide +kernel
    rw [ha]
    exact (canonical37026 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2638 sourceB2638 sourceC2638
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2638, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2641 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2641 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2641 + difference 0 1) (sourceB2641 + difference 1 0) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3563) := by
    have ha : (tripleCharges (sourceA2641 + difference 0 1) (sourceB2641 + difference 1 0) sourceC2641) = raw37070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37070; decide +kernel
    rw [ha]
    exact (canonical37070 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2641 + difference 0 2) (sourceB2641 + difference 2 0) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA2641 + difference 0 2) (sourceB2641 + difference 2 0) sourceC2641) = raw37071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37071; decide +kernel
    rw [ha]
    exact (canonical37071 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2641 + difference 0 3) (sourceB2641 + difference 3 0) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA2641 + difference 0 3) (sourceB2641 + difference 3 0) sourceC2641) = raw37072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37072; decide +kernel
    rw [ha]
    exact (canonical37072 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2641 + difference 0 4) (sourceB2641 + difference 4 0) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA2641 + difference 0 4) (sourceB2641 + difference 4 0) sourceC2641) = raw37073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37073; decide +kernel
    rw [ha]
    exact (canonical37073 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2641 + difference 0 5) (sourceB2641 + difference 5 0) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3844) := by
    have ha : (tripleCharges (sourceA2641 + difference 0 5) (sourceB2641 + difference 5 0) sourceC2641) = raw37074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37074; decide +kernel
    rw [ha]
    exact (canonical37074 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2641 + difference 1 0) (sourceB2641 + difference 0 1) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2232) := by
    have ha : (tripleCharges (sourceA2641 + difference 1 0) (sourceB2641 + difference 0 1) sourceC2641) = raw37075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37075; decide +kernel
    rw [ha]
    exact (canonical37075 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2641 + difference 1 2) (sourceB2641 + difference 2 1) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA2641 + difference 1 2) (sourceB2641 + difference 2 1) sourceC2641) = raw37076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37076; decide +kernel
    rw [ha]
    exact (canonical37076 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2641 + difference 1 3) (sourceB2641 + difference 3 1) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA2641 + difference 1 3) (sourceB2641 + difference 3 1) sourceC2641) = raw37077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37077; decide +kernel
    rw [ha]
    exact (canonical37077 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2641 + difference 1 4) (sourceB2641 + difference 4 1) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA2641 + difference 1 4) (sourceB2641 + difference 4 1) sourceC2641) = raw37078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37078; decide +kernel
    rw [ha]
    exact (canonical37078 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2641 + difference 1 5) (sourceB2641 + difference 5 1) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA2641 + difference 1 5) (sourceB2641 + difference 5 1) sourceC2641) = raw37079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37079; decide +kernel
    rw [ha]
    exact (canonical37079 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2641 + difference 2 0) (sourceB2641 + difference 0 2) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2142) := by
    have ha : (tripleCharges (sourceA2641 + difference 2 0) (sourceB2641 + difference 0 2) sourceC2641) = raw37080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37080; decide +kernel
    rw [ha]
    exact (canonical37080 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2641 + difference 2 1) (sourceB2641 + difference 1 2) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2641 + difference 2 1) (sourceB2641 + difference 1 2) sourceC2641) = raw37081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37081; decide +kernel
    rw [ha]
    exact (canonical37081 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2641 + difference 2 3) (sourceB2641 + difference 3 2) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2641 + difference 2 3) (sourceB2641 + difference 3 2) sourceC2641) = raw37082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37082; decide +kernel
    rw [ha]
    exact (canonical37082 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2641 + difference 2 4) (sourceB2641 + difference 4 2) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2641 + difference 2 4) (sourceB2641 + difference 4 2) sourceC2641) = raw37083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37083; decide +kernel
    rw [ha]
    exact (canonical37083 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2641 + difference 2 5) (sourceB2641 + difference 5 2) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA2641 + difference 2 5) (sourceB2641 + difference 5 2) sourceC2641) = raw37084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37084; decide +kernel
    rw [ha]
    exact (canonical37084 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2641 + difference 3 0) (sourceB2641 + difference 0 3) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2142) := by
    have ha : (tripleCharges (sourceA2641 + difference 3 0) (sourceB2641 + difference 0 3) sourceC2641) = raw37085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37085; decide +kernel
    rw [ha]
    exact (canonical37085 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2641 + difference 3 1) (sourceB2641 + difference 1 3) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2641 + difference 3 1) (sourceB2641 + difference 1 3) sourceC2641) = raw37086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37086; decide +kernel
    rw [ha]
    exact (canonical37086 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2641 + difference 3 2) (sourceB2641 + difference 2 3) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2641 + difference 3 2) (sourceB2641 + difference 2 3) sourceC2641) = raw37087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37087; decide +kernel
    rw [ha]
    exact (canonical37087 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2641 + difference 3 4) (sourceB2641 + difference 4 3) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2641 + difference 3 4) (sourceB2641 + difference 4 3) sourceC2641) = raw37088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37088; decide +kernel
    rw [ha]
    exact (canonical37088 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2641 + difference 3 5) (sourceB2641 + difference 5 3) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA2641 + difference 3 5) (sourceB2641 + difference 5 3) sourceC2641) = raw37089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37089; decide +kernel
    rw [ha]
    exact (canonical37089 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2641 + difference 4 0) (sourceB2641 + difference 0 4) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2142) := by
    have ha : (tripleCharges (sourceA2641 + difference 4 0) (sourceB2641 + difference 0 4) sourceC2641) = raw37090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37090; decide +kernel
    rw [ha]
    exact (canonical37090 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2641 + difference 4 1) (sourceB2641 + difference 1 4) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2641 + difference 4 1) (sourceB2641 + difference 1 4) sourceC2641) = raw37091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37091; decide +kernel
    rw [ha]
    exact (canonical37091 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2641 + difference 4 2) (sourceB2641 + difference 2 4) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2641 + difference 4 2) (sourceB2641 + difference 2 4) sourceC2641) = raw37092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37092; decide +kernel
    rw [ha]
    exact (canonical37092 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2641 + difference 4 3) (sourceB2641 + difference 3 4) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2641 + difference 4 3) (sourceB2641 + difference 3 4) sourceC2641) = raw37093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37093; decide +kernel
    rw [ha]
    exact (canonical37093 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2641 + difference 4 5) (sourceB2641 + difference 5 4) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA2641 + difference 4 5) (sourceB2641 + difference 5 4) sourceC2641) = raw37094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37094; decide +kernel
    rw [ha]
    exact (canonical37094 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2641 + difference 5 0) (sourceB2641 + difference 0 5) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2139) := by
    have ha : (tripleCharges (sourceA2641 + difference 5 0) (sourceB2641 + difference 0 5) sourceC2641) = raw37095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37095; decide +kernel
    rw [ha]
    exact (canonical37095 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2641 + difference 5 1) (sourceB2641 + difference 1 5) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2690) := by
    have ha : (tripleCharges (sourceA2641 + difference 5 1) (sourceB2641 + difference 1 5) sourceC2641) = raw37096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37096; decide +kernel
    rw [ha]
    exact (canonical37096 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2641 + difference 5 2) (sourceB2641 + difference 2 5) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA2641 + difference 5 2) (sourceB2641 + difference 2 5) sourceC2641) = raw37097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37097; decide +kernel
    rw [ha]
    exact (canonical37097 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2641 + difference 5 3) (sourceB2641 + difference 3 5) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA2641 + difference 5 3) (sourceB2641 + difference 3 5) sourceC2641) = raw37098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37098; decide +kernel
    rw [ha]
    exact (canonical37098 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2641 + difference 5 4) (sourceB2641 + difference 4 5) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA2641 + difference 5 4) (sourceB2641 + difference 4 5) sourceC2641) = raw37099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37099; decide +kernel
    rw [ha]
    exact (canonical37099 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2641 sourceB2641 sourceC2641
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2641, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2645 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2645 + difference 0 1) (sourceB2645 + difference 1 0) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA2645 + difference 0 1) (sourceB2645 + difference 1 0) sourceC2645) = raw37156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37156; decide +kernel
    rw [ha]
    exact (canonical37156 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2645 + difference 0 2) (sourceB2645 + difference 2 0) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA2645 + difference 0 2) (sourceB2645 + difference 2 0) sourceC2645) = raw37157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37157; decide +kernel
    rw [ha]
    exact (canonical37157 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2645 + difference 0 3) (sourceB2645 + difference 3 0) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA2645 + difference 0 3) (sourceB2645 + difference 3 0) sourceC2645) = raw37158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37158; decide +kernel
    rw [ha]
    exact (canonical37158 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2645 + difference 0 4) (sourceB2645 + difference 4 0) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA2645 + difference 0 4) (sourceB2645 + difference 4 0) sourceC2645) = raw37159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37159; decide +kernel
    rw [ha]
    exact (canonical37159 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2645 + difference 0 5) (sourceB2645 + difference 5 0) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA2645 + difference 0 5) (sourceB2645 + difference 5 0) sourceC2645) = raw37160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37160; decide +kernel
    rw [ha]
    exact (canonical37160 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2645 + difference 1 0) (sourceB2645 + difference 0 1) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA2645 + difference 1 0) (sourceB2645 + difference 0 1) sourceC2645) = raw37161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37161; decide +kernel
    rw [ha]
    exact (canonical37161 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2645 + difference 1 2) (sourceB2645 + difference 2 1) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA2645 + difference 1 2) (sourceB2645 + difference 2 1) sourceC2645) = raw37162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37162; decide +kernel
    rw [ha]
    exact (canonical37162 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2645 + difference 1 3) (sourceB2645 + difference 3 1) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA2645 + difference 1 3) (sourceB2645 + difference 3 1) sourceC2645) = raw37163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37163; decide +kernel
    rw [ha]
    exact (canonical37163 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2645 + difference 1 4) (sourceB2645 + difference 4 1) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA2645 + difference 1 4) (sourceB2645 + difference 4 1) sourceC2645) = raw37164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37164; decide +kernel
    rw [ha]
    exact (canonical37164 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2645 + difference 1 5) (sourceB2645 + difference 5 1) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA2645 + difference 1 5) (sourceB2645 + difference 5 1) sourceC2645) = raw37165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37165; decide +kernel
    rw [ha]
    exact (canonical37165 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2645 + difference 2 0) (sourceB2645 + difference 0 2) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2238) := by
    have ha : (tripleCharges (sourceA2645 + difference 2 0) (sourceB2645 + difference 0 2) sourceC2645) = raw37166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37166; decide +kernel
    rw [ha]
    exact (canonical37166 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2645 + difference 2 1) (sourceB2645 + difference 1 2) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2150) := by
    have ha : (tripleCharges (sourceA2645 + difference 2 1) (sourceB2645 + difference 1 2) sourceC2645) = raw37167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37167; decide +kernel
    rw [ha]
    exact (canonical37167 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2645 + difference 2 3) (sourceB2645 + difference 3 2) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2645 + difference 2 3) (sourceB2645 + difference 3 2) sourceC2645) = raw37168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37168; decide +kernel
    rw [ha]
    exact (canonical37168 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2645 + difference 2 4) (sourceB2645 + difference 4 2) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2645 + difference 2 4) (sourceB2645 + difference 4 2) sourceC2645) = raw37169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37169; decide +kernel
    rw [ha]
    exact (canonical37169 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2645 + difference 2 5) (sourceB2645 + difference 5 2) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA2645 + difference 2 5) (sourceB2645 + difference 5 2) sourceC2645) = raw37170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37170; decide +kernel
    rw [ha]
    exact (canonical37170 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2645 + difference 3 0) (sourceB2645 + difference 0 3) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2238) := by
    have ha : (tripleCharges (sourceA2645 + difference 3 0) (sourceB2645 + difference 0 3) sourceC2645) = raw37171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37171; decide +kernel
    rw [ha]
    exact (canonical37171 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2645 + difference 3 1) (sourceB2645 + difference 1 3) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2150) := by
    have ha : (tripleCharges (sourceA2645 + difference 3 1) (sourceB2645 + difference 1 3) sourceC2645) = raw37172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37172; decide +kernel
    rw [ha]
    exact (canonical37172 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2645 + difference 3 2) (sourceB2645 + difference 2 3) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2645 + difference 3 2) (sourceB2645 + difference 2 3) sourceC2645) = raw37173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37173; decide +kernel
    rw [ha]
    exact (canonical37173 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2645 + difference 3 4) (sourceB2645 + difference 4 3) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2645 + difference 3 4) (sourceB2645 + difference 4 3) sourceC2645) = raw37174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37174; decide +kernel
    rw [ha]
    exact (canonical37174 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2645 + difference 3 5) (sourceB2645 + difference 5 3) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA2645 + difference 3 5) (sourceB2645 + difference 5 3) sourceC2645) = raw37175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37175; decide +kernel
    rw [ha]
    exact (canonical37175 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2645 + difference 4 0) (sourceB2645 + difference 0 4) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2238) := by
    have ha : (tripleCharges (sourceA2645 + difference 4 0) (sourceB2645 + difference 0 4) sourceC2645) = raw37176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37176; decide +kernel
    rw [ha]
    exact (canonical37176 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2645 + difference 4 1) (sourceB2645 + difference 1 4) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2150) := by
    have ha : (tripleCharges (sourceA2645 + difference 4 1) (sourceB2645 + difference 1 4) sourceC2645) = raw37177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37177; decide +kernel
    rw [ha]
    exact (canonical37177 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2645 + difference 4 2) (sourceB2645 + difference 2 4) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2645 + difference 4 2) (sourceB2645 + difference 2 4) sourceC2645) = raw37178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37178; decide +kernel
    rw [ha]
    exact (canonical37178 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2645 + difference 4 3) (sourceB2645 + difference 3 4) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2645 + difference 4 3) (sourceB2645 + difference 3 4) sourceC2645) = raw37179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37179; decide +kernel
    rw [ha]
    exact (canonical37179 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2645 + difference 4 5) (sourceB2645 + difference 5 4) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA2645 + difference 4 5) (sourceB2645 + difference 5 4) sourceC2645) = raw37180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37180; decide +kernel
    rw [ha]
    exact (canonical37180 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2645 + difference 5 0) (sourceB2645 + difference 0 5) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2231) := by
    have ha : (tripleCharges (sourceA2645 + difference 5 0) (sourceB2645 + difference 0 5) sourceC2645) = raw37181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37181; decide +kernel
    rw [ha]
    exact (canonical37181 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2645 + difference 5 1) (sourceB2645 + difference 1 5) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2156) := by
    have ha : (tripleCharges (sourceA2645 + difference 5 1) (sourceB2645 + difference 1 5) sourceC2645) = raw37182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37182; decide +kernel
    rw [ha]
    exact (canonical37182 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2645 + difference 5 2) (sourceB2645 + difference 2 5) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA2645 + difference 5 2) (sourceB2645 + difference 2 5) sourceC2645) = raw37183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37183; decide +kernel
    rw [ha]
    exact (canonical37183 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2645 + difference 5 3) (sourceB2645 + difference 3 5) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA2645 + difference 5 3) (sourceB2645 + difference 3 5) sourceC2645) = raw37184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37184; decide +kernel
    rw [ha]
    exact (canonical37184 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2645 + difference 5 4) (sourceB2645 + difference 4 5) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA2645 + difference 5 4) (sourceB2645 + difference 4 5) sourceC2645) = raw37185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37185; decide +kernel
    rw [ha]
    exact (canonical37185 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2645 sourceB2645 sourceC2645
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2645, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2649 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2649 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2649 + difference 0 1) (sourceB2649 + difference 1 0) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (tripleCharges (sourceA2649 + difference 0 1) (sourceB2649 + difference 1 0) sourceC2649) = raw37232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37232; decide +kernel
    rw [ha]
    exact (canonical37232 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2649 + difference 0 2) (sourceB2649 + difference 2 0) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 0 2) (sourceB2649 + difference 2 0) sourceC2649) = raw3440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw3440; decide +kernel
    rw [ha]
    exact (canonical3440 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2649 + difference 0 3) (sourceB2649 + difference 3 0) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 0 3) (sourceB2649 + difference 3 0) sourceC2649) = raw3436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw3436; decide +kernel
    rw [ha]
    exact (canonical3436 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2649 + difference 0 4) (sourceB2649 + difference 4 0) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 0 4) (sourceB2649 + difference 4 0) sourceC2649) = raw37233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37233; decide +kernel
    rw [ha]
    exact (canonical37233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2649 + difference 0 5) (sourceB2649 + difference 5 0) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 0 5) (sourceB2649 + difference 5 0) sourceC2649) = raw37234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37234; decide +kernel
    rw [ha]
    exact (canonical37234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2649 + difference 1 0) (sourceB2649 + difference 0 1) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (tripleCharges (sourceA2649 + difference 1 0) (sourceB2649 + difference 0 1) sourceC2649) = raw14365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw14365; decide +kernel
    rw [ha]
    exact (canonical14365 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2649 + difference 1 2) (sourceB2649 + difference 2 1) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 1 2) (sourceB2649 + difference 2 1) sourceC2649) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2649 + difference 1 3) (sourceB2649 + difference 3 1) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 1 3) (sourceB2649 + difference 3 1) sourceC2649) = raw3328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw3328; decide +kernel
    rw [ha]
    exact (canonical3328 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2649 + difference 1 4) (sourceB2649 + difference 4 1) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 1 4) (sourceB2649 + difference 4 1) sourceC2649) = raw19361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw19361; decide +kernel
    rw [ha]
    exact (canonical19361 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2649 + difference 1 5) (sourceB2649 + difference 5 1) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 1 5) (sourceB2649 + difference 5 1) sourceC2649) = raw19362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw19362; decide +kernel
    rw [ha]
    exact (canonical19362 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2649 + difference 2 0) (sourceB2649 + difference 0 2) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 2 0) (sourceB2649 + difference 0 2) sourceC2649) = raw34724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw34724; decide +kernel
    rw [ha]
    exact (canonical34724 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2649 + difference 2 1) (sourceB2649 + difference 1 2) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 2 1) (sourceB2649 + difference 1 2) sourceC2649) = raw37235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37235; decide +kernel
    rw [ha]
    exact (canonical37235 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2649 + difference 2 3) (sourceB2649 + difference 3 2) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 2 3) (sourceB2649 + difference 3 2) sourceC2649) = raw37236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37236; decide +kernel
    rw [ha]
    exact (canonical37236 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2649 + difference 2 4) (sourceB2649 + difference 4 2) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 2 4) (sourceB2649 + difference 4 2) sourceC2649) = raw37237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37237; decide +kernel
    rw [ha]
    exact (canonical37237 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2649 + difference 2 5) (sourceB2649 + difference 5 2) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 2 5) (sourceB2649 + difference 5 2) sourceC2649) = raw37238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37238; decide +kernel
    rw [ha]
    exact (canonical37238 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2649 + difference 3 0) (sourceB2649 + difference 0 3) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 3 0) (sourceB2649 + difference 0 3) sourceC2649) = raw34728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw34728; decide +kernel
    rw [ha]
    exact (canonical34728 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2649 + difference 3 1) (sourceB2649 + difference 1 3) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 3 1) (sourceB2649 + difference 1 3) sourceC2649) = raw37239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37239; decide +kernel
    rw [ha]
    exact (canonical37239 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2649 + difference 3 2) (sourceB2649 + difference 2 3) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 3 2) (sourceB2649 + difference 2 3) sourceC2649) = raw19363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw19363; decide +kernel
    rw [ha]
    exact (canonical19363 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2649 + difference 3 4) (sourceB2649 + difference 4 3) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 3 4) (sourceB2649 + difference 4 3) sourceC2649) = raw37240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37240; decide +kernel
    rw [ha]
    exact (canonical37240 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2649 + difference 3 5) (sourceB2649 + difference 5 3) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 3 5) (sourceB2649 + difference 5 3) sourceC2649) = raw37241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37241; decide +kernel
    rw [ha]
    exact (canonical37241 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2649 + difference 4 0) (sourceB2649 + difference 0 4) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 4 0) (sourceB2649 + difference 0 4) sourceC2649) = raw34731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw34731; decide +kernel
    rw [ha]
    exact (canonical34731 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2649 + difference 4 1) (sourceB2649 + difference 1 4) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 4 1) (sourceB2649 + difference 1 4) sourceC2649) = raw37242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37242; decide +kernel
    rw [ha]
    exact (canonical37242 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2649 + difference 4 2) (sourceB2649 + difference 2 4) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 4 2) (sourceB2649 + difference 2 4) sourceC2649) = raw19367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw19367; decide +kernel
    rw [ha]
    exact (canonical19367 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2649 + difference 4 3) (sourceB2649 + difference 3 4) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 4 3) (sourceB2649 + difference 3 4) sourceC2649) = raw35539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw35539; decide +kernel
    rw [ha]
    exact (canonical35539 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2649 + difference 4 5) (sourceB2649 + difference 5 4) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 4 5) (sourceB2649 + difference 5 4) sourceC2649) = raw37243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37243; decide +kernel
    rw [ha]
    exact (canonical37243 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2649 + difference 5 0) (sourceB2649 + difference 0 5) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 5 0) (sourceB2649 + difference 0 5) sourceC2649) = raw34405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw34405; decide +kernel
    rw [ha]
    exact (canonical34405 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2649 + difference 5 1) (sourceB2649 + difference 1 5) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 5 1) (sourceB2649 + difference 1 5) sourceC2649) = raw37019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37019; decide +kernel
    rw [ha]
    exact (canonical37019 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2649 + difference 5 2) (sourceB2649 + difference 2 5) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 5 2) (sourceB2649 + difference 2 5) sourceC2649) = raw18337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw18337; decide +kernel
    rw [ha]
    exact (canonical18337 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2649 + difference 5 3) (sourceB2649 + difference 3 5) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 5 3) (sourceB2649 + difference 3 5) sourceC2649) = raw18335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw18335; decide +kernel
    rw [ha]
    exact (canonical18335 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2649 + difference 5 4) (sourceB2649 + difference 4 5) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 5 4) (sourceB2649 + difference 4 5) sourceC2649) = raw37020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37020; decide +kernel
    rw [ha]
    exact (canonical37020 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2649 sourceB2649 sourceC2649
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2649, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2653 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2653 + difference 0 1) (sourceB2653 + difference 1 0) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2653 + difference 0 1) (sourceB2653 + difference 1 0) sourceC2653) = raw37294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37294; decide +kernel
    rw [ha]
    exact (canonical37294 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2653 + difference 0 2) (sourceB2653 + difference 2 0) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2653 + difference 0 2) (sourceB2653 + difference 2 0) sourceC2653) = raw37295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37295; decide +kernel
    rw [ha]
    exact (canonical37295 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2653 + difference 0 3) (sourceB2653 + difference 3 0) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA2653 + difference 0 3) (sourceB2653 + difference 3 0) sourceC2653) = raw37296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37296; decide +kernel
    rw [ha]
    exact (canonical37296 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2653 + difference 0 4) (sourceB2653 + difference 4 0) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA2653 + difference 0 4) (sourceB2653 + difference 4 0) sourceC2653) = raw37297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37297; decide +kernel
    rw [ha]
    exact (canonical37297 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2653 + difference 0 5) (sourceB2653 + difference 5 0) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA2653 + difference 0 5) (sourceB2653 + difference 5 0) sourceC2653) = raw37298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37298; decide +kernel
    rw [ha]
    exact (canonical37298 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2653 + difference 1 0) (sourceB2653 + difference 0 1) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2653 + difference 1 0) (sourceB2653 + difference 0 1) sourceC2653) = raw37299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37299; decide +kernel
    rw [ha]
    exact (canonical37299 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2653 + difference 1 2) (sourceB2653 + difference 2 1) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2653 + difference 1 2) (sourceB2653 + difference 2 1) sourceC2653) = raw37300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37300; decide +kernel
    rw [ha]
    exact (canonical37300 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2653 + difference 1 3) (sourceB2653 + difference 3 1) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA2653 + difference 1 3) (sourceB2653 + difference 3 1) sourceC2653) = raw37301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37301; decide +kernel
    rw [ha]
    exact (canonical37301 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2653 + difference 1 4) (sourceB2653 + difference 4 1) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA2653 + difference 1 4) (sourceB2653 + difference 4 1) sourceC2653) = raw37302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37302; decide +kernel
    rw [ha]
    exact (canonical37302 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2653 + difference 1 5) (sourceB2653 + difference 5 1) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA2653 + difference 1 5) (sourceB2653 + difference 5 1) sourceC2653) = raw37303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37303; decide +kernel
    rw [ha]
    exact (canonical37303 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2653 + difference 2 0) (sourceB2653 + difference 0 2) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2653 + difference 2 0) (sourceB2653 + difference 0 2) sourceC2653) = raw37304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37304; decide +kernel
    rw [ha]
    exact (canonical37304 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2653 + difference 2 1) (sourceB2653 + difference 1 2) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2653 + difference 2 1) (sourceB2653 + difference 1 2) sourceC2653) = raw37305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37305; decide +kernel
    rw [ha]
    exact (canonical37305 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2653 + difference 2 3) (sourceB2653 + difference 3 2) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA2653 + difference 2 3) (sourceB2653 + difference 3 2) sourceC2653) = raw37306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37306; decide +kernel
    rw [ha]
    exact (canonical37306 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2653 + difference 2 4) (sourceB2653 + difference 4 2) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA2653 + difference 2 4) (sourceB2653 + difference 4 2) sourceC2653) = raw37307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37307; decide +kernel
    rw [ha]
    exact (canonical37307 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2653 + difference 2 5) (sourceB2653 + difference 5 2) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA2653 + difference 2 5) (sourceB2653 + difference 5 2) sourceC2653) = raw37308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37308; decide +kernel
    rw [ha]
    exact (canonical37308 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2653 + difference 3 0) (sourceB2653 + difference 0 3) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2178) := by
    have ha : (tripleCharges (sourceA2653 + difference 3 0) (sourceB2653 + difference 0 3) sourceC2653) = raw37309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37309; decide +kernel
    rw [ha]
    exact (canonical37309 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2653 + difference 3 1) (sourceB2653 + difference 1 3) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2653 + difference 3 1) (sourceB2653 + difference 1 3) sourceC2653) = raw37310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37310; decide +kernel
    rw [ha]
    exact (canonical37310 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2653 + difference 3 2) (sourceB2653 + difference 2 3) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2653 + difference 3 2) (sourceB2653 + difference 2 3) sourceC2653) = raw37311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37311; decide +kernel
    rw [ha]
    exact (canonical37311 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2653 + difference 3 4) (sourceB2653 + difference 4 3) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA2653 + difference 3 4) (sourceB2653 + difference 4 3) sourceC2653) = raw37312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37312; decide +kernel
    rw [ha]
    exact (canonical37312 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2653 + difference 3 5) (sourceB2653 + difference 5 3) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA2653 + difference 3 5) (sourceB2653 + difference 5 3) sourceC2653) = raw37313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37313; decide +kernel
    rw [ha]
    exact (canonical37313 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2653 + difference 4 0) (sourceB2653 + difference 0 4) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2171) := by
    have ha : (tripleCharges (sourceA2653 + difference 4 0) (sourceB2653 + difference 0 4) sourceC2653) = raw37314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37314; decide +kernel
    rw [ha]
    exact (canonical37314 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2653 + difference 4 1) (sourceB2653 + difference 1 4) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2653 + difference 4 1) (sourceB2653 + difference 1 4) sourceC2653) = raw37315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37315; decide +kernel
    rw [ha]
    exact (canonical37315 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2653 + difference 4 2) (sourceB2653 + difference 2 4) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2653 + difference 4 2) (sourceB2653 + difference 2 4) sourceC2653) = raw37316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37316; decide +kernel
    rw [ha]
    exact (canonical37316 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2653 + difference 4 3) (sourceB2653 + difference 3 4) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA2653 + difference 4 3) (sourceB2653 + difference 3 4) sourceC2653) = raw37317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37317; decide +kernel
    rw [ha]
    exact (canonical37317 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2653 + difference 4 5) (sourceB2653 + difference 5 4) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA2653 + difference 4 5) (sourceB2653 + difference 5 4) sourceC2653) = raw37318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37318; decide +kernel
    rw [ha]
    exact (canonical37318 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2653 + difference 5 0) (sourceB2653 + difference 0 5) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2175) := by
    have ha : (tripleCharges (sourceA2653 + difference 5 0) (sourceB2653 + difference 0 5) sourceC2653) = raw37319 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37319; decide +kernel
    rw [ha]
    exact (canonical37319 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2653 + difference 5 1) (sourceB2653 + difference 1 5) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2653 + difference 5 1) (sourceB2653 + difference 1 5) sourceC2653) = raw37320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37320; decide +kernel
    rw [ha]
    exact (canonical37320 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2653 + difference 5 2) (sourceB2653 + difference 2 5) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2653 + difference 5 2) (sourceB2653 + difference 2 5) sourceC2653) = raw37321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37321; decide +kernel
    rw [ha]
    exact (canonical37321 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2653 + difference 5 3) (sourceB2653 + difference 3 5) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA2653 + difference 5 3) (sourceB2653 + difference 3 5) sourceC2653) = raw37322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37322; decide +kernel
    rw [ha]
    exact (canonical37322 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2653 + difference 5 4) (sourceB2653 + difference 4 5) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3477) := by
    have ha : (tripleCharges (sourceA2653 + difference 5 4) (sourceB2653 + difference 4 5) sourceC2653) = raw37323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37323; decide +kernel
    rw [ha]
    exact (canonical37323 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2653 sourceB2653 sourceC2653
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2653, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2654 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2654 + difference 0 1) (sourceB2654 + difference 1 0) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2654 + difference 0 1) (sourceB2654 + difference 1 0) sourceC2654) = raw19404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw19404; decide +kernel
    rw [ha]
    exact (canonical19404 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2654 + difference 0 2) (sourceB2654 + difference 2 0) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2654 + difference 0 2) (sourceB2654 + difference 2 0) sourceC2654) = raw19405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw19405; decide +kernel
    rw [ha]
    exact (canonical19405 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2654 + difference 0 3) (sourceB2654 + difference 3 0) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2654 + difference 0 3) (sourceB2654 + difference 3 0) sourceC2654) = raw3449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw3449; decide +kernel
    rw [ha]
    exact (canonical3449 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2654 + difference 0 4) (sourceB2654 + difference 4 0) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2654 + difference 0 4) (sourceB2654 + difference 4 0) sourceC2654) = raw19406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw19406; decide +kernel
    rw [ha]
    exact (canonical19406 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2654 + difference 0 5) (sourceB2654 + difference 5 0) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4095) := by
    have ha : (tripleCharges (sourceA2654 + difference 0 5) (sourceB2654 + difference 5 0) sourceC2654) = raw3441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw3441; decide +kernel
    rw [ha]
    exact (canonical3441 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2654 + difference 1 0) (sourceB2654 + difference 0 1) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2654 + difference 1 0) (sourceB2654 + difference 0 1) sourceC2654) = raw11539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw11539; decide +kernel
    rw [ha]
    exact (canonical11539 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2654 + difference 1 2) (sourceB2654 + difference 2 1) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2654 + difference 1 2) (sourceB2654 + difference 2 1) sourceC2654) = raw37324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37324; decide +kernel
    rw [ha]
    exact (canonical37324 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2654 + difference 1 3) (sourceB2654 + difference 3 1) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2654 + difference 1 3) (sourceB2654 + difference 3 1) sourceC2654) = raw2931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw2931; decide +kernel
    rw [ha]
    exact (canonical2931 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2654 + difference 1 4) (sourceB2654 + difference 4 1) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2654 + difference 1 4) (sourceB2654 + difference 4 1) sourceC2654) = raw2926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw2926; decide +kernel
    rw [ha]
    exact (canonical2926 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2654 + difference 1 5) (sourceB2654 + difference 5 1) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2654 + difference 1 5) (sourceB2654 + difference 5 1) sourceC2654) = raw3333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw3333; decide +kernel
    rw [ha]
    exact (canonical3333 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2654 + difference 2 0) (sourceB2654 + difference 0 2) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2654 + difference 2 0) (sourceB2654 + difference 0 2) sourceC2654) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2654 + difference 2 1) (sourceB2654 + difference 1 2) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2654 + difference 2 1) (sourceB2654 + difference 1 2) sourceC2654) = raw18337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw18337; decide +kernel
    rw [ha]
    exact (canonical18337 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2654 + difference 2 3) (sourceB2654 + difference 3 2) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2654 + difference 2 3) (sourceB2654 + difference 3 2) sourceC2654) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2654 + difference 2 4) (sourceB2654 + difference 4 2) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2654 + difference 2 4) (sourceB2654 + difference 4 2) sourceC2654) = raw2925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw2925; decide +kernel
    rw [ha]
    exact (canonical2925 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2654 + difference 2 5) (sourceB2654 + difference 5 2) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2654 + difference 2 5) (sourceB2654 + difference 5 2) sourceC2654) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2654 + difference 3 0) (sourceB2654 + difference 0 3) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2654 + difference 3 0) (sourceB2654 + difference 0 3) sourceC2654) = raw34408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw34408; decide +kernel
    rw [ha]
    exact (canonical34408 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2654 + difference 3 1) (sourceB2654 + difference 1 3) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2654 + difference 3 1) (sourceB2654 + difference 1 3) sourceC2654) = raw37022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37022; decide +kernel
    rw [ha]
    exact (canonical37022 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2654 + difference 3 2) (sourceB2654 + difference 2 3) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2654 + difference 3 2) (sourceB2654 + difference 2 3) sourceC2654) = raw37325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37325; decide +kernel
    rw [ha]
    exact (canonical37325 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2654 + difference 3 4) (sourceB2654 + difference 4 3) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2654 + difference 3 4) (sourceB2654 + difference 4 3) sourceC2654) = raw37326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37326; decide +kernel
    rw [ha]
    exact (canonical37326 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2654 + difference 3 5) (sourceB2654 + difference 5 3) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2654 + difference 3 5) (sourceB2654 + difference 5 3) sourceC2654) = raw19364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw19364; decide +kernel
    rw [ha]
    exact (canonical19364 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2654 + difference 4 0) (sourceB2654 + difference 0 4) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2654 + difference 4 0) (sourceB2654 + difference 0 4) sourceC2654) = raw31881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw31881; decide +kernel
    rw [ha]
    exact (canonical31881 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2654 + difference 4 1) (sourceB2654 + difference 1 4) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2654 + difference 4 1) (sourceB2654 + difference 1 4) sourceC2654) = raw35541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw35541; decide +kernel
    rw [ha]
    exact (canonical35541 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2654 + difference 4 2) (sourceB2654 + difference 2 4) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2654 + difference 4 2) (sourceB2654 + difference 2 4) sourceC2654) = raw37327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37327; decide +kernel
    rw [ha]
    exact (canonical37327 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2654 + difference 4 3) (sourceB2654 + difference 3 4) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2654 + difference 4 3) (sourceB2654 + difference 3 4) sourceC2654) = raw18340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw18340; decide +kernel
    rw [ha]
    exact (canonical18340 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2654 + difference 4 5) (sourceB2654 + difference 5 4) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2654 + difference 4 5) (sourceB2654 + difference 5 4) sourceC2654) = raw19368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw19368; decide +kernel
    rw [ha]
    exact (canonical19368 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2654 + difference 5 0) (sourceB2654 + difference 0 5) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4077) := by
    have ha : (tripleCharges (sourceA2654 + difference 5 0) (sourceB2654 + difference 0 5) sourceC2654) = raw29298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw29298; decide +kernel
    rw [ha]
    exact (canonical29298 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2654 + difference 5 1) (sourceB2654 + difference 1 5) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2654 + difference 5 1) (sourceB2654 + difference 1 5) sourceC2654) = raw37025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37025; decide +kernel
    rw [ha]
    exact (canonical37025 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2654 + difference 5 2) (sourceB2654 + difference 2 5) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2654 + difference 5 2) (sourceB2654 + difference 2 5) sourceC2654) = raw37328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37328; decide +kernel
    rw [ha]
    exact (canonical37328 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2654 + difference 5 3) (sourceB2654 + difference 3 5) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2654 + difference 5 3) (sourceB2654 + difference 3 5) sourceC2654) = raw18343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw18343; decide +kernel
    rw [ha]
    exact (canonical18343 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2654 + difference 5 4) (sourceB2654 + difference 4 5) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2654 + difference 5 4) (sourceB2654 + difference 4 5) sourceC2654) = raw37329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37329; decide +kernel
    rw [ha]
    exact (canonical37329 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2654 sourceB2654 sourceC2654
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2654, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2098 : Integer.Sparse.reindex keyMap MixedData.row2098 = numericRow2098 := by decide +kernel

theorem numericCheck2098 (x : Master → ℝ) : Integer.Sparse.eval numericRow2098 x =
    (1 : ℝ) * reducedSource2098 x := by
  norm_num [numericRow2098, reducedSource2098, Integer.Sparse.eval, Sparse.eval, nodeValue4073, nodeValue4074, nodeValue4075, nodeValue4078, nodeValue4080, nodeValue4082, nodeValue4086, nodeValue4087, nodeValue4088, nodeValue4089, nodeValue4090, nodeValue4091, nodeValue4092]

theorem reindexCheck2101 : Integer.Sparse.reindex keyMap MixedData.row2101 = numericRow2101 := by decide +kernel

theorem numericCheck2101 (x : Master → ℝ) : Integer.Sparse.eval numericRow2101 x =
    (1 : ℝ) * reducedSource2101 x := by
  norm_num [numericRow2101, reducedSource2101, Integer.Sparse.eval, Sparse.eval, nodeValue2139, nodeValue2142, nodeValue2232, nodeValue2690, nodeValue2697, nodeValue3554, nodeValue3563, nodeValue3832, nodeValue3836, nodeValue3844, nodeValue3846, nodeValue3875, nodeValue3909]

theorem reindexCheck2104 : Integer.Sparse.reindex keyMap MixedData.row2104 = numericRow2104 := by decide +kernel

theorem numericCheck2104 (x : Master → ℝ) : Integer.Sparse.eval numericRow2104 x =
    (1 : ℝ) * reducedSource2104 x := by
  norm_num [numericRow2104, reducedSource2104, Integer.Sparse.eval, Sparse.eval, nodeValue2150, nodeValue2156, nodeValue2204, nodeValue2231, nodeValue2234, nodeValue2238, nodeValue2669, nodeValue2676, nodeValue2684, nodeValue2721, nodeValue2741, nodeValue3037, nodeValue3053]

theorem reindexCheck2106 : Integer.Sparse.reindex keyMap MixedData.row2106 = numericRow2106 := by decide +kernel

theorem numericCheck2106 (x : Master → ℝ) : Integer.Sparse.eval numericRow2106 x =
    (1 : ℝ) * reducedSource2106 x := by
  norm_num [numericRow2106, reducedSource2106, Integer.Sparse.eval, Sparse.eval, nodeValue4073, nodeValue4079, nodeValue4088, nodeValue4091]

theorem reindexCheck2110 : Integer.Sparse.reindex keyMap MixedData.row2110 = numericRow2110 := by decide +kernel

theorem numericCheck2110 (x : Master → ℝ) : Integer.Sparse.eval numericRow2110 x =
    (1 : ℝ) * reducedSource2110 x := by
  norm_num [numericRow2110, reducedSource2110, Integer.Sparse.eval, Sparse.eval, nodeValue2171, nodeValue2175, nodeValue2178, nodeValue2195, nodeValue2653, nodeValue2661, nodeValue2708, nodeValue3474, nodeValue3477, nodeValue3537, nodeValue3755, nodeValue3761, nodeValue3769, nodeValue3804, nodeValue3806, nodeValue3812, nodeValue3840, nodeValue3849, nodeValue3869, nodeValue3871, nodeValue3979]

theorem reindexCheck2111 : Integer.Sparse.reindex keyMap MixedData.row2111 = numericRow2111 := by decide +kernel

theorem numericCheck2111 (x : Master → ℝ) : Integer.Sparse.eval numericRow2111 x =
    (1 : ℝ) * reducedSource2111 x := by
  norm_num [numericRow2111, reducedSource2111, Integer.Sparse.eval, Sparse.eval, nodeValue4077, nodeValue4078, nodeValue4080, nodeValue4086, nodeValue4088, nodeValue4090, nodeValue4091, nodeValue4092, nodeValue4095]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2098 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2098 (mixedVector B) = 0 := by
  have h4073 : mixedVector B (Sum.inr 4073) = Sparse.eval nodeValue4073 (mixedVector B) := by
    change mixedMoment B node4073 node4073Labels = _
    exact sound4073 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  have h4078 : mixedVector B (Sum.inr 4078) = Sparse.eval nodeValue4078 (mixedVector B) := by
    change mixedMoment B node4078 node4078Labels = _
    exact sound4078 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4086 : mixedVector B (Sum.inr 4086) = Sparse.eval nodeValue4086 (mixedVector B) := by
    change mixedMoment B node4086 node4086Labels = _
    exact sound4086 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2638, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4073, h4074, h4075, h4078, h4080, h4082, h4086, h4087, h4088, h4089, h4090, h4091, h4092, reducedSource2098] using sourceEq2638 B hB

theorem rowSound2098 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2098 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2098, numericCheck2098, reducedZero2098 B hB hF, mul_zero]

theorem reducedZero2101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2101 (mixedVector B) = 0 := by
  have h2139 : mixedVector B (Sum.inr 2139) = Sparse.eval nodeValue2139 (mixedVector B) := by
    change mixedMoment B node2139 node2139Labels = _
    exact sound2139 B hB hF
  have h2142 : mixedVector B (Sum.inr 2142) = Sparse.eval nodeValue2142 (mixedVector B) := by
    change mixedMoment B node2142 node2142Labels = _
    exact sound2142 B hB hF
  have h2232 : mixedVector B (Sum.inr 2232) = Sparse.eval nodeValue2232 (mixedVector B) := by
    change mixedMoment B node2232 node2232Labels = _
    exact sound2232 B hB hF
  have h2690 : mixedVector B (Sum.inr 2690) = Sparse.eval nodeValue2690 (mixedVector B) := by
    change mixedMoment B node2690 node2690Labels = _
    exact sound2690 B hB hF
  have h2697 : mixedVector B (Sum.inr 2697) = Sparse.eval nodeValue2697 (mixedVector B) := by
    change mixedMoment B node2697 node2697Labels = _
    exact sound2697 B hB hF
  have h3554 : mixedVector B (Sum.inr 3554) = Sparse.eval nodeValue3554 (mixedVector B) := by
    change mixedMoment B node3554 node3554Labels = _
    exact sound3554 B hB hF
  have h3563 : mixedVector B (Sum.inr 3563) = Sparse.eval nodeValue3563 (mixedVector B) := by
    change mixedMoment B node3563 node3563Labels = _
    exact sound3563 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h3836 : mixedVector B (Sum.inr 3836) = Sparse.eval nodeValue3836 (mixedVector B) := by
    change mixedMoment B node3836 node3836Labels = _
    exact sound3836 B hB hF
  have h3844 : mixedVector B (Sum.inr 3844) = Sparse.eval nodeValue3844 (mixedVector B) := by
    change mixedMoment B node3844 node3844Labels = _
    exact sound3844 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  simpa only [sourceForm2641, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2139, h2142, h2232, h2690, h2697, h3554, h3563, h3832, h3836, h3844, h3846, h3875, h3909, reducedSource2101] using sourceEq2641 B hB

theorem rowSound2101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2101 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2101, numericCheck2101, reducedZero2101 B hB hF, mul_zero]

theorem reducedZero2104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2104 (mixedVector B) = 0 := by
  have h2150 : mixedVector B (Sum.inr 2150) = Sparse.eval nodeValue2150 (mixedVector B) := by
    change mixedMoment B node2150 node2150Labels = _
    exact sound2150 B hB hF
  have h2156 : mixedVector B (Sum.inr 2156) = Sparse.eval nodeValue2156 (mixedVector B) := by
    change mixedMoment B node2156 node2156Labels = _
    exact sound2156 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h2231 : mixedVector B (Sum.inr 2231) = Sparse.eval nodeValue2231 (mixedVector B) := by
    change mixedMoment B node2231 node2231Labels = _
    exact sound2231 B hB hF
  have h2234 : mixedVector B (Sum.inr 2234) = Sparse.eval nodeValue2234 (mixedVector B) := by
    change mixedMoment B node2234 node2234Labels = _
    exact sound2234 B hB hF
  have h2238 : mixedVector B (Sum.inr 2238) = Sparse.eval nodeValue2238 (mixedVector B) := by
    change mixedMoment B node2238 node2238Labels = _
    exact sound2238 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h2684 : mixedVector B (Sum.inr 2684) = Sparse.eval nodeValue2684 (mixedVector B) := by
    change mixedMoment B node2684 node2684Labels = _
    exact sound2684 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2741 : mixedVector B (Sum.inr 2741) = Sparse.eval nodeValue2741 (mixedVector B) := by
    change mixedMoment B node2741 node2741Labels = _
    exact sound2741 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  simpa only [sourceForm2645, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2150, h2156, h2204, h2231, h2234, h2238, h2669, h2676, h2684, h2721, h2741, h3037, h3053, reducedSource2104] using sourceEq2645 B hB

theorem rowSound2104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2104 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2104, numericCheck2104, reducedZero2104 B hB hF, mul_zero]

theorem reducedZero2106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2106 (mixedVector B) = 0 := by
  have h4073 : mixedVector B (Sum.inr 4073) = Sparse.eval nodeValue4073 (mixedVector B) := by
    change mixedMoment B node4073 node4073Labels = _
    exact sound4073 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2649, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4073, h4079, h4088, h4091, reducedSource2106] using sourceEq2649 B hB

theorem rowSound2106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2106 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2106, numericCheck2106, reducedZero2106 B hB hF, mul_zero]

theorem reducedZero2110 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2110 (mixedVector B) = 0 := by
  have h2171 : mixedVector B (Sum.inr 2171) = Sparse.eval nodeValue2171 (mixedVector B) := by
    change mixedMoment B node2171 node2171Labels = _
    exact sound2171 B hB hF
  have h2175 : mixedVector B (Sum.inr 2175) = Sparse.eval nodeValue2175 (mixedVector B) := by
    change mixedMoment B node2175 node2175Labels = _
    exact sound2175 B hB hF
  have h2178 : mixedVector B (Sum.inr 2178) = Sparse.eval nodeValue2178 (mixedVector B) := by
    change mixedMoment B node2178 node2178Labels = _
    exact sound2178 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2653 : mixedVector B (Sum.inr 2653) = Sparse.eval nodeValue2653 (mixedVector B) := by
    change mixedMoment B node2653 node2653Labels = _
    exact sound2653 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h3474 : mixedVector B (Sum.inr 3474) = Sparse.eval nodeValue3474 (mixedVector B) := by
    change mixedMoment B node3474 node3474Labels = _
    exact sound3474 B hB hF
  have h3477 : mixedVector B (Sum.inr 3477) = Sparse.eval nodeValue3477 (mixedVector B) := by
    change mixedMoment B node3477 node3477Labels = _
    exact sound3477 B hB hF
  have h3537 : mixedVector B (Sum.inr 3537) = Sparse.eval nodeValue3537 (mixedVector B) := by
    change mixedMoment B node3537 node3537Labels = _
    exact sound3537 B hB hF
  have h3755 : mixedVector B (Sum.inr 3755) = Sparse.eval nodeValue3755 (mixedVector B) := by
    change mixedMoment B node3755 node3755Labels = _
    exact sound3755 B hB hF
  have h3761 : mixedVector B (Sum.inr 3761) = Sparse.eval nodeValue3761 (mixedVector B) := by
    change mixedMoment B node3761 node3761Labels = _
    exact sound3761 B hB hF
  have h3769 : mixedVector B (Sum.inr 3769) = Sparse.eval nodeValue3769 (mixedVector B) := by
    change mixedMoment B node3769 node3769Labels = _
    exact sound3769 B hB hF
  have h3804 : mixedVector B (Sum.inr 3804) = Sparse.eval nodeValue3804 (mixedVector B) := by
    change mixedMoment B node3804 node3804Labels = _
    exact sound3804 B hB hF
  have h3806 : mixedVector B (Sum.inr 3806) = Sparse.eval nodeValue3806 (mixedVector B) := by
    change mixedMoment B node3806 node3806Labels = _
    exact sound3806 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3869 : mixedVector B (Sum.inr 3869) = Sparse.eval nodeValue3869 (mixedVector B) := by
    change mixedMoment B node3869 node3869Labels = _
    exact sound3869 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3979 : mixedVector B (Sum.inr 3979) = Sparse.eval nodeValue3979 (mixedVector B) := by
    change mixedMoment B node3979 node3979Labels = _
    exact sound3979 B hB hF
  simpa only [sourceForm2653, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2171, h2175, h2178, h2195, h2653, h2661, h2708, h3474, h3477, h3537, h3755, h3761, h3769, h3804, h3806, h3812, h3840, h3849, h3869, h3871, h3979, reducedSource2110] using sourceEq2653 B hB

theorem rowSound2110 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2110 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2110, numericCheck2110, reducedZero2110 B hB hF, mul_zero]

theorem reducedZero2111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2111 (mixedVector B) = 0 := by
  have h4077 : mixedVector B (Sum.inr 4077) = Sparse.eval nodeValue4077 (mixedVector B) := by
    change mixedMoment B node4077 node4077Labels = _
    exact sound4077 B hB hF
  have h4078 : mixedVector B (Sum.inr 4078) = Sparse.eval nodeValue4078 (mixedVector B) := by
    change mixedMoment B node4078 node4078Labels = _
    exact sound4078 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4086 : mixedVector B (Sum.inr 4086) = Sparse.eval nodeValue4086 (mixedVector B) := by
    change mixedMoment B node4086 node4086Labels = _
    exact sound4086 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4095 : mixedVector B (Sum.inr 4095) = Sparse.eval nodeValue4095 (mixedVector B) := by
    change mixedMoment B node4095 node4095Labels = _
    exact sound4095 B hB hF
  simpa only [sourceForm2654, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4077, h4078, h4080, h4086, h4088, h4090, h4091, h4092, h4095, reducedSource2111] using sourceEq2654 B hB

theorem rowSound2111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2111 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2111, numericCheck2111, reducedZero2111 B hB hF, mul_zero]

theorem sourceRowsAt2096 : MixedData.sourceRows (2096 : Fin 2425) =
    MixedData.row2096 := by decide +kernel

theorem sourceRowsAt2097 : MixedData.sourceRows (2097 : Fin 2425) =
    MixedData.row2097 := by decide +kernel

theorem sourceRowsAt2098 : MixedData.sourceRows (2098 : Fin 2425) =
    MixedData.row2098 := by decide +kernel

theorem sourceRowsAt2099 : MixedData.sourceRows (2099 : Fin 2425) =
    MixedData.row2099 := by decide +kernel

theorem sourceRowsAt2100 : MixedData.sourceRows (2100 : Fin 2425) =
    MixedData.row2100 := by decide +kernel

theorem sourceRowsAt2101 : MixedData.sourceRows (2101 : Fin 2425) =
    MixedData.row2101 := by decide +kernel

theorem sourceRowsAt2102 : MixedData.sourceRows (2102 : Fin 2425) =
    MixedData.row2102 := by decide +kernel

theorem sourceRowsAt2103 : MixedData.sourceRows (2103 : Fin 2425) =
    MixedData.row2103 := by decide +kernel

theorem sourceRowsAt2104 : MixedData.sourceRows (2104 : Fin 2425) =
    MixedData.row2104 := by decide +kernel

theorem sourceRowsAt2105 : MixedData.sourceRows (2105 : Fin 2425) =
    MixedData.row2105 := by decide +kernel

theorem sourceRowsAt2106 : MixedData.sourceRows (2106 : Fin 2425) =
    MixedData.row2106 := by decide +kernel

theorem sourceRowsAt2107 : MixedData.sourceRows (2107 : Fin 2425) =
    MixedData.row2107 := by decide +kernel

theorem sourceRowsAt2108 : MixedData.sourceRows (2108 : Fin 2425) =
    MixedData.row2108 := by decide +kernel

theorem sourceRowsAt2109 : MixedData.sourceRows (2109 : Fin 2425) =
    MixedData.row2109 := by decide +kernel

theorem sourceRowsAt2110 : MixedData.sourceRows (2110 : Fin 2425) =
    MixedData.row2110 := by decide +kernel

theorem sourceRowsAt2111 : MixedData.sourceRows (2111 : Fin 2425) =
    MixedData.row2111 := by decide +kernel

theorem chunkSound131_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 131) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2096 ∨ k.val = 2097 ∨ k.val = 2098 ∨ k.val = 2099 ∨ k.val = 2100 ∨ k.val = 2101 ∨ k.val = 2102 ∨ k.val = 2103 ∨ k.val = 2104 ∨ k.val = 2105 ∨ k.val = 2106 ∨ k.val = 2107 ∨ k.val = 2108 ∨ k.val = 2109 ∨ k.val = 2110 ∨ k.val = 2111 := by omega
  rcases heq with h2096 | h2097 | h2098 | h2099 | h2100 | h2101 | h2102 | h2103 | h2104 | h2105 | h2106 | h2107 | h2108 | h2109 | h2110 | h2111
  · have he : k = (2096 : Fin 2425) := Fin.ext h2096
    subst k
    rw [sourceRowsAt2096]
    exact rowSound2096_e B hB hF
  · have he : k = (2097 : Fin 2425) := Fin.ext h2097
    subst k
    rw [sourceRowsAt2097]
    exact rowSound2097_e B hB hF
  · have he : k = (2098 : Fin 2425) := Fin.ext h2098
    subst k
    rw [sourceRowsAt2098]
    exact rowSound2098 B hB hF
  · have he : k = (2099 : Fin 2425) := Fin.ext h2099
    subst k
    rw [sourceRowsAt2099]
    exact rowSound2099_e B hB hF
  · have he : k = (2100 : Fin 2425) := Fin.ext h2100
    subst k
    rw [sourceRowsAt2100]
    exact rowSound2100_e B hB hF
  · have he : k = (2101 : Fin 2425) := Fin.ext h2101
    subst k
    rw [sourceRowsAt2101]
    exact rowSound2101 B hB hF
  · have he : k = (2102 : Fin 2425) := Fin.ext h2102
    subst k
    rw [sourceRowsAt2102]
    exact rowSound2102_e B hB hF
  · have he : k = (2103 : Fin 2425) := Fin.ext h2103
    subst k
    rw [sourceRowsAt2103]
    exact rowSound2103_e B hB hF
  · have he : k = (2104 : Fin 2425) := Fin.ext h2104
    subst k
    rw [sourceRowsAt2104]
    exact rowSound2104 B hB hF
  · have he : k = (2105 : Fin 2425) := Fin.ext h2105
    subst k
    rw [sourceRowsAt2105]
    exact rowSound2105_e B hB hF
  · have he : k = (2106 : Fin 2425) := Fin.ext h2106
    subst k
    rw [sourceRowsAt2106]
    exact rowSound2106 B hB hF
  · have he : k = (2107 : Fin 2425) := Fin.ext h2107
    subst k
    rw [sourceRowsAt2107]
    exact rowSound2107_e B hB hF
  · have he : k = (2108 : Fin 2425) := Fin.ext h2108
    subst k
    rw [sourceRowsAt2108]
    exact rowSound2108_e B hB hF
  · have he : k = (2109 : Fin 2425) := Fin.ext h2109
    subst k
    rw [sourceRowsAt2109]
    exact rowSound2109_e B hB hF
  · have he : k = (2110 : Fin 2425) := Fin.ext h2110
    subst k
    rw [sourceRowsAt2110]
    exact rowSound2110 B hB hF
  · have he : k = (2111 : Fin 2425) := Fin.ext h2111
    subst k
    rw [sourceRowsAt2111]
    exact rowSound2111 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e_oai
