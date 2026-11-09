-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:45:01.001994+00:00
-- url     : https://prove2.me/submissions/fc593422-b858-46ef-83f3-0e85471e8b22

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2002_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2003_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2004_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2005_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2006_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2010_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2011_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2014_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2015_e

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

theorem canonical14369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14369 raw14369Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw14369 raw14369Labels = mixedMoment B raw14369step0 raw14369step0Labels := by
      have hz : ∀ j, raw14369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14369step0 = (fun i j => raw14369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14369step0 raw14369; decide +kernel
      have hl : raw14369step0Labels = raw14369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14369 raw14369Labels permutation346 hz
    mixedMoment B raw14369step0 raw14369step0Labels = mixedMoment B raw14369step1 raw14369step1Labels := by
      have hz : ∀ i, raw14369step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14369step1 = (fun i j => raw14369step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14369step1 raw14369step0; decide +kernel
      have hl : raw14369step1Labels = (fun j => raw14369step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14369step0 raw14369step0Labels permutation6 hz
    mixedMoment B raw14369step1 raw14369step1Labels = mixedMoment B raw14369step2 raw14369step2Labels := by
      have ha : raw14369step2 = (fun i j => raw14369step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14369step2 raw14369step1; decide +kernel
      have hl : raw14369step2Labels = raw14369step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14369step1 raw14369step1Labels permutation35 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical14374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14374 raw14374Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw14374 raw14374Labels = mixedMoment B raw14374step0 raw14374step0Labels := by
      have hz : ∀ j, raw14374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14374step0 = (fun i j => raw14374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14374step0 raw14374; decide +kernel
      have hl : raw14374step0Labels = raw14374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14374 raw14374Labels permutation346 hz
    mixedMoment B raw14374step0 raw14374step0Labels = mixedMoment B raw14374step1 raw14374step1Labels := by
      have hz : ∀ i, raw14374step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14374step1 = (fun i j => raw14374step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14374step1 raw14374step0; decide +kernel
      have hl : raw14374step1Labels = (fun j => raw14374step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14374step0 raw14374step0Labels permutation6 hz
    mixedMoment B raw14374step1 raw14374step1Labels = mixedMoment B raw14374step2 raw14374step2Labels := by
      have ha : raw14374step2 = (fun i j => raw14374step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14374step2 raw14374step1; decide +kernel
      have hl : raw14374step2Labels = raw14374step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14374step1 raw14374step1Labels permutation33 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20142 raw20142Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw20142 raw20142Labels = mixedMoment B raw20142step0 raw20142step0Labels := by
      have hz : ∀ j, raw20142 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20142step0 = (fun i j => raw20142 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20142step0 raw20142; decide +kernel
      have hl : raw20142step0Labels = raw20142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20142 raw20142Labels permutation520 hz
    mixedMoment B raw20142step0 raw20142step0Labels = mixedMoment B raw20142step1 raw20142step1Labels := by
      have hz : ∀ j, raw20142step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20142step1 = (fun i j => raw20142step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20142step1 raw20142step0; decide +kernel
      have hl : raw20142step1Labels = raw20142step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20142step0 raw20142step0Labels permutation80 hz
    mixedMoment B raw20142step1 raw20142step1Labels = mixedMoment B raw20142step2 raw20142step2Labels := by
      have hz : ∀ j, raw20142step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20142step2 = (fun i j => raw20142step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20142step2 raw20142step1; decide +kernel
      have hl : raw20142step2Labels = raw20142step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20142step1 raw20142step1Labels permutation14 hz
    mixedMoment B raw20142step2 raw20142step2Labels = mixedMoment B raw20142step3 raw20142step3Labels := by
      have ha : raw20142step3 = (fun i j => raw20142step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20142step3 raw20142step2; decide +kernel
      have hl : raw20142step3Labels = raw20142step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20142step2 raw20142step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

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

theorem canonical21853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21853 raw21853Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw21853 raw21853Labels = mixedMoment B raw21853step0 raw21853step0Labels := by
      have hz : ∀ j, raw21853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21853step0 = (fun i j => raw21853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21853step0 raw21853; decide +kernel
      have hl : raw21853step0Labels = raw21853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21853 raw21853Labels permutation434 hz
    mixedMoment B raw21853step0 raw21853step0Labels = mixedMoment B raw21853step1 raw21853step1Labels := by
      have hz : ∀ j, raw21853step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21853step1 = (fun i j => raw21853step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21853step1 raw21853step0; decide +kernel
      have hl : raw21853step1Labels = raw21853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21853step0 raw21853step0Labels permutation80 hz
    mixedMoment B raw21853step1 raw21853step1Labels = mixedMoment B raw21853step2 raw21853step2Labels := by
      have ha : raw21853step2 = (fun i j => raw21853step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21853step2 raw21853step1; decide +kernel
      have hl : raw21853step2Labels = raw21853step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21853step1 raw21853step1Labels permutation31 permutation7
    mixedMoment B raw21853step2 raw21853step2Labels = mixedMoment B raw21853step3 raw21853step3Labels := by
      have ha : raw21853step3 = raw21853step2 := by apply Matrix.ext; unfold raw21853step3 raw21853step2; decide +kernel
      have hl : raw21853step2Labels = labelEmbedding1 ∘ raw21853step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21853step2 raw21853step2Labels raw21853step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

theorem canonical21856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21856 raw21856Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw21856 raw21856Labels = mixedMoment B raw21856step0 raw21856step0Labels := by
      have hz : ∀ j, raw21856 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21856step0 = (fun i j => raw21856 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21856step0 raw21856; decide +kernel
      have hl : raw21856step0Labels = raw21856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21856 raw21856Labels permutation434 hz
    mixedMoment B raw21856step0 raw21856step0Labels = mixedMoment B raw21856step1 raw21856step1Labels := by
      have hz : ∀ j, raw21856step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21856step1 = (fun i j => raw21856step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21856step1 raw21856step0; decide +kernel
      have hl : raw21856step1Labels = raw21856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21856step0 raw21856step0Labels permutation80 hz
    mixedMoment B raw21856step1 raw21856step1Labels = mixedMoment B raw21856step2 raw21856step2Labels := by
      have hz : ∀ j, raw21856step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21856step2 = (fun i j => raw21856step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21856step2 raw21856step1; decide +kernel
      have hl : raw21856step2Labels = raw21856step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21856step1 raw21856step1Labels permutation14 hz
    mixedMoment B raw21856step2 raw21856step2Labels = mixedMoment B raw21856step3 raw21856step3Labels := by
      have ha : raw21856step3 = (fun i j => raw21856step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21856step3 raw21856step2; decide +kernel
      have hl : raw21856step3Labels = raw21856step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21856step2 raw21856step2Labels permutation2 permutation7
    mixedMoment B raw21856step3 raw21856step3Labels = mixedMoment B raw21856step4 raw21856step4Labels := by
      have ha : raw21856step4 = -raw21856step3 := by apply Matrix.ext; change ∀ i j, raw21856step4 i j = -(raw21856step3 i j); unfold raw21856step4 raw21856step3; decide +kernel
      have hl : raw21856step4Labels = raw21856step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21856step4 raw21856step4Labels = mixedMoment B raw21856step5 raw21856step5Labels := by
      have ha : raw21856step5 = raw21856step4 := by apply Matrix.ext; unfold raw21856step5 raw21856step4; decide +kernel
      have hl : raw21856step4Labels = labelEmbedding1 ∘ raw21856step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21856step4 raw21856step4Labels raw21856step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2268 node2268Labels := by rfl

theorem canonical21866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21866 raw21866Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21866 raw21866Labels = mixedMoment B raw21866step0 raw21866step0Labels := by
      have hz : ∀ j, raw21866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21866step0 = (fun i j => raw21866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21866step0 raw21866; decide +kernel
      have hl : raw21866step0Labels = raw21866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21866 raw21866Labels permutation346 hz
    mixedMoment B raw21866step0 raw21866step0Labels = mixedMoment B raw21866step1 raw21866step1Labels := by
      have ha : raw21866step1 = (fun i j => raw21866step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21866step1 raw21866step0; decide +kernel
      have hl : raw21866step1Labels = raw21866step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21866step0 raw21866step0Labels permutation32 permutation7
    mixedMoment B raw21866step1 raw21866step1Labels = mixedMoment B raw21866step2 raw21866step2Labels := by
      have ha : raw21866step2 = -raw21866step1 := by apply Matrix.ext; change ∀ i j, raw21866step2 i j = -(raw21866step1 i j); unfold raw21866step2 raw21866step1; decide +kernel
      have hl : raw21866step2Labels = raw21866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21866step2 raw21866step2Labels = mixedMoment B raw21866step3 raw21866step3Labels := by
      have ha : raw21866step3 = raw21866step2 := by apply Matrix.ext; unfold raw21866step3 raw21866step2; decide +kernel
      have hl : raw21866step2Labels = labelEmbedding1 ∘ raw21866step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21866step2 raw21866step2Labels raw21866step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

theorem canonical21868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21868 raw21868Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw21868 raw21868Labels = mixedMoment B raw21868step0 raw21868step0Labels := by
      have hz : ∀ j, raw21868 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21868step0 = (fun i j => raw21868 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21868step0 raw21868; decide +kernel
      have hl : raw21868step0Labels = raw21868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21868 raw21868Labels permutation346 hz
    mixedMoment B raw21868step0 raw21868step0Labels = mixedMoment B raw21868step1 raw21868step1Labels := by
      have hz : ∀ j, raw21868step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21868step1 = (fun i j => raw21868step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21868step1 raw21868step0; decide +kernel
      have hl : raw21868step1Labels = raw21868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21868step0 raw21868step0Labels permutation56 hz
    mixedMoment B raw21868step1 raw21868step1Labels = mixedMoment B raw21868step2 raw21868step2Labels := by
      have ha : raw21868step2 = (fun i j => raw21868step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21868step2 raw21868step1; decide +kernel
      have hl : raw21868step2Labels = raw21868step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21868step1 raw21868step1Labels permutation8 permutation7
    mixedMoment B raw21868step2 raw21868step2Labels = mixedMoment B raw21868step3 raw21868step3Labels := by
      have ha : raw21868step3 = -raw21868step2 := by apply Matrix.ext; change ∀ i j, raw21868step3 i j = -(raw21868step2 i j); unfold raw21868step3 raw21868step2; decide +kernel
      have hl : raw21868step3Labels = raw21868step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21868step3 raw21868step3Labels = mixedMoment B raw21868step4 raw21868step4Labels := by
      have ha : raw21868step4 = raw21868step3 := by apply Matrix.ext; unfold raw21868step4 raw21868step3; decide +kernel
      have hl : raw21868step3Labels = labelEmbedding1 ∘ raw21868step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21868step3 raw21868step3Labels raw21868step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22308 raw22308Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22308 raw22308Labels = mixedMoment B raw22308step0 raw22308step0Labels := by
      have hz : ∀ j, raw22308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22308step0 = (fun i j => raw22308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22308step0 raw22308; decide +kernel
      have hl : raw22308step0Labels = raw22308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22308 raw22308Labels permutation346 hz
    mixedMoment B raw22308step0 raw22308step0Labels = mixedMoment B raw22308step1 raw22308step1Labels := by
      have hz : ∀ i, raw22308step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22308step1 = (fun i j => raw22308step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22308step1 raw22308step0; decide +kernel
      have hl : raw22308step1Labels = (fun j => raw22308step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22308step0 raw22308step0Labels permutation6 hz
    _ = mixedMoment B node4064 node4064Labels := by rfl

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

theorem canonical23786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23786 raw23786Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23786 raw23786Labels = mixedMoment B raw23786step0 raw23786step0Labels := by
      have hz : ∀ j, raw23786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23786step0 = (fun i j => raw23786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23786step0 raw23786; decide +kernel
      have hl : raw23786step0Labels = raw23786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23786 raw23786Labels permutation346 hz
    mixedMoment B raw23786step0 raw23786step0Labels = mixedMoment B raw23786step1 raw23786step1Labels := by
      have hz : ∀ i, raw23786step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23786step1 = (fun i j => raw23786step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23786step1 raw23786step0; decide +kernel
      have hl : raw23786step1Labels = (fun j => raw23786step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23786step0 raw23786step0Labels permutation6 hz
    _ = mixedMoment B node4065 node4065Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical201
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25764 raw25764Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw25764 raw25764Labels = mixedMoment B raw25764step0 raw25764step0Labels := by
      have hz : ∀ j, raw25764 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25764step0 = (fun i j => raw25764 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25764step0 raw25764; decide +kernel
      have hl : raw25764step0Labels = raw25764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25764 raw25764Labels permutation265 hz
    mixedMoment B raw25764step0 raw25764step0Labels = mixedMoment B raw25764step1 raw25764step1Labels := by
      have ha : raw25764step1 = (fun i j => raw25764step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25764step1 raw25764step0; decide +kernel
      have hl : raw25764step1Labels = raw25764step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25764step0 raw25764step0Labels permutation35 permutation7
    mixedMoment B raw25764step1 raw25764step1Labels = mixedMoment B raw25764step2 raw25764step2Labels := by
      have ha : raw25764step2 = -raw25764step1 := by apply Matrix.ext; change ∀ i j, raw25764step2 i j = -(raw25764step1 i j); unfold raw25764step2 raw25764step1; decide +kernel
      have hl : raw25764step2Labels = raw25764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25764step2 raw25764step2Labels = mixedMoment B raw25764step3 raw25764step3Labels := by
      have ha : raw25764step3 = raw25764step2 := by apply Matrix.ext; unfold raw25764step3 raw25764step2; decide +kernel
      have hl : raw25764step2Labels = labelEmbedding1 ∘ raw25764step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25764step2 raw25764step2Labels raw25764step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical25765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25765 raw25765Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw25765 raw25765Labels = mixedMoment B raw25765step0 raw25765step0Labels := by
      have hz : ∀ j, raw25765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25765step0 = (fun i j => raw25765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25765step0 raw25765; decide +kernel
      have hl : raw25765step0Labels = raw25765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25765 raw25765Labels permutation346 hz
    mixedMoment B raw25765step0 raw25765step0Labels = mixedMoment B raw25765step1 raw25765step1Labels := by
      have hz : ∀ j, raw25765step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25765step1 = (fun i j => raw25765step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25765step1 raw25765step0; decide +kernel
      have hl : raw25765step1Labels = raw25765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25765step0 raw25765step0Labels permutation56 hz
    mixedMoment B raw25765step1 raw25765step1Labels = mixedMoment B raw25765step2 raw25765step2Labels := by
      have ha : raw25765step2 = (fun i j => raw25765step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25765step2 raw25765step1; decide +kernel
      have hl : raw25765step2Labels = raw25765step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25765step1 raw25765step1Labels permutation11 permutation7
    mixedMoment B raw25765step2 raw25765step2Labels = mixedMoment B raw25765step3 raw25765step3Labels := by
      have ha : raw25765step3 = -raw25765step2 := by apply Matrix.ext; change ∀ i j, raw25765step3 i j = -(raw25765step2 i j); unfold raw25765step3 raw25765step2; decide +kernel
      have hl : raw25765step3Labels = raw25765step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25765step3 raw25765step3Labels = mixedMoment B raw25765step4 raw25765step4Labels := by
      have ha : raw25765step4 = raw25765step3 := by apply Matrix.ext; unfold raw25765step4 raw25765step3; decide +kernel
      have hl : raw25765step3Labels = labelEmbedding1 ∘ raw25765step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25765step3 raw25765step3Labels raw25765step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical25766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25766 raw25766Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw25766 raw25766Labels = mixedMoment B raw25766step0 raw25766step0Labels := by
      have hz : ∀ j, raw25766 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25766step0 = (fun i j => raw25766 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25766step0 raw25766; decide +kernel
      have hl : raw25766step0Labels = raw25766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25766 raw25766Labels permutation520 hz
    mixedMoment B raw25766step0 raw25766step0Labels = mixedMoment B raw25766step1 raw25766step1Labels := by
      have hz : ∀ j, raw25766step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25766step1 = (fun i j => raw25766step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25766step1 raw25766step0; decide +kernel
      have hl : raw25766step1Labels = raw25766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25766step0 raw25766step0Labels permutation80 hz
    mixedMoment B raw25766step1 raw25766step1Labels = mixedMoment B raw25766step2 raw25766step2Labels := by
      have hz : ∀ j, raw25766step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25766step2 = (fun i j => raw25766step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25766step2 raw25766step1; decide +kernel
      have hl : raw25766step2Labels = raw25766step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25766step1 raw25766step1Labels permutation14 hz
    mixedMoment B raw25766step2 raw25766step2Labels = mixedMoment B raw25766step3 raw25766step3Labels := by
      have ha : raw25766step3 = (fun i j => raw25766step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25766step3 raw25766step2; decide +kernel
      have hl : raw25766step3Labels = raw25766step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25766step2 raw25766step2Labels permutation3 permutation7
    mixedMoment B raw25766step3 raw25766step3Labels = mixedMoment B raw25766step4 raw25766step4Labels := by
      have ha : raw25766step4 = -raw25766step3 := by apply Matrix.ext; change ∀ i j, raw25766step4 i j = -(raw25766step3 i j); unfold raw25766step4 raw25766step3; decide +kernel
      have hl : raw25766step4Labels = raw25766step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25766step4 raw25766step4Labels = mixedMoment B raw25766step5 raw25766step5Labels := by
      have ha : raw25766step5 = raw25766step4 := by apply Matrix.ext; unfold raw25766step5 raw25766step4; decide +kernel
      have hl : raw25766step4Labels = labelEmbedding1 ∘ raw25766step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25766step4 raw25766step4Labels raw25766step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2293 node2293Labels := by rfl

theorem canonical25767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25767 raw25767Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw25767 raw25767Labels = mixedMoment B raw25767step0 raw25767step0Labels := by
      have hz : ∀ j, raw25767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25767step0 = (fun i j => raw25767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25767step0 raw25767; decide +kernel
      have hl : raw25767step0Labels = raw25767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25767 raw25767Labels permutation346 hz
    mixedMoment B raw25767step0 raw25767step0Labels = mixedMoment B raw25767step1 raw25767step1Labels := by
      have hz : ∀ j, raw25767step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25767step1 = (fun i j => raw25767step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25767step1 raw25767step0; decide +kernel
      have hl : raw25767step1Labels = raw25767step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25767step0 raw25767step0Labels permutation56 hz
    mixedMoment B raw25767step1 raw25767step1Labels = mixedMoment B raw25767step2 raw25767step2Labels := by
      have ha : raw25767step2 = (fun i j => raw25767step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25767step2 raw25767step1; decide +kernel
      have hl : raw25767step2Labels = raw25767step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25767step1 raw25767step1Labels permutation11 permutation7
    mixedMoment B raw25767step2 raw25767step2Labels = mixedMoment B raw25767step3 raw25767step3Labels := by
      have ha : raw25767step3 = -raw25767step2 := by apply Matrix.ext; change ∀ i j, raw25767step3 i j = -(raw25767step2 i j); unfold raw25767step3 raw25767step2; decide +kernel
      have hl : raw25767step3Labels = raw25767step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25767step3 raw25767step3Labels = mixedMoment B raw25767step4 raw25767step4Labels := by
      have ha : raw25767step4 = raw25767step3 := by apply Matrix.ext; unfold raw25767step4 raw25767step3; decide +kernel
      have hl : raw25767step3Labels = labelEmbedding1 ∘ raw25767step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25767step3 raw25767step3Labels raw25767step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2265 node2265Labels := by rfl

theorem canonical25774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25774 raw25774Labels = mixedMoment B node1665 node1665Labels := by
  calc
    mixedMoment B raw25774 raw25774Labels = mixedMoment B raw25774step0 raw25774step0Labels := by
      have ha : raw25774step0 = (fun i j => raw25774 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25774step0 raw25774; decide +kernel
      have hl : raw25774step0Labels = raw25774Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25774 raw25774Labels permutation155 permutation7
    mixedMoment B raw25774step0 raw25774step0Labels = mixedMoment B raw25774step1 raw25774step1Labels := by
      have ha : raw25774step1 = -raw25774step0 := by apply Matrix.ext; change ∀ i j, raw25774step1 i j = -(raw25774step0 i j); unfold raw25774step1 raw25774step0; decide +kernel
      have hl : raw25774step1Labels = raw25774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25774step1 raw25774step1Labels = mixedMoment B raw25774step2 raw25774step2Labels := by
      have ha : raw25774step2 = raw25774step1 := by apply Matrix.ext; unfold raw25774step2 raw25774step1; decide +kernel
      have hl : raw25774step1Labels = labelEmbedding1 ∘ raw25774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25774step1 raw25774step1Labels raw25774step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1665 node1665Labels := by rfl

theorem canonical25779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25779 raw25779Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw25779 raw25779Labels = mixedMoment B raw25779step0 raw25779step0Labels := by
      have hz : ∀ j, raw25779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25779step0 = (fun i j => raw25779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25779step0 raw25779; decide +kernel
      have hl : raw25779step0Labels = raw25779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25779 raw25779Labels permutation346 hz
    mixedMoment B raw25779step0 raw25779step0Labels = mixedMoment B raw25779step1 raw25779step1Labels := by
      have ha : raw25779step1 = (fun i j => raw25779step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25779step1 raw25779step0; decide +kernel
      have hl : raw25779step1Labels = raw25779step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25779step0 raw25779step0Labels permutation35 permutation7
    mixedMoment B raw25779step1 raw25779step1Labels = mixedMoment B raw25779step2 raw25779step2Labels := by
      have ha : raw25779step2 = -raw25779step1 := by apply Matrix.ext; change ∀ i j, raw25779step2 i j = -(raw25779step1 i j); unfold raw25779step2 raw25779step1; decide +kernel
      have hl : raw25779step2Labels = raw25779step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25779step2 raw25779step2Labels = mixedMoment B raw25779step3 raw25779step3Labels := by
      have ha : raw25779step3 = raw25779step2 := by apply Matrix.ext; unfold raw25779step3 raw25779step2; decide +kernel
      have hl : raw25779step2Labels = labelEmbedding1 ∘ raw25779step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25779step2 raw25779step2Labels raw25779step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

theorem canonical25784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25784 raw25784Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw25784 raw25784Labels = mixedMoment B raw25784step0 raw25784step0Labels := by
      have hz : ∀ j, raw25784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25784step0 = (fun i j => raw25784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25784step0 raw25784; decide +kernel
      have hl : raw25784step0Labels = raw25784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25784 raw25784Labels permutation346 hz
    mixedMoment B raw25784step0 raw25784step0Labels = mixedMoment B raw25784step1 raw25784step1Labels := by
      have ha : raw25784step1 = (fun i j => raw25784step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25784step1 raw25784step0; decide +kernel
      have hl : raw25784step1Labels = raw25784step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25784step0 raw25784step0Labels permutation35 permutation7
    mixedMoment B raw25784step1 raw25784step1Labels = mixedMoment B raw25784step2 raw25784step2Labels := by
      have ha : raw25784step2 = -raw25784step1 := by apply Matrix.ext; change ∀ i j, raw25784step2 i j = -(raw25784step1 i j); unfold raw25784step2 raw25784step1; decide +kernel
      have hl : raw25784step2Labels = raw25784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25784step2 raw25784step2Labels = mixedMoment B raw25784step3 raw25784step3Labels := by
      have ha : raw25784step3 = raw25784step2 := by apply Matrix.ext; unfold raw25784step3 raw25784step2; decide +kernel
      have hl : raw25784step2Labels = labelEmbedding1 ∘ raw25784step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25784step2 raw25784step2Labels raw25784step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

theorem canonical25789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25789 raw25789Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw25789 raw25789Labels = mixedMoment B raw25789step0 raw25789step0Labels := by
      have hz : ∀ j, raw25789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25789step0 = (fun i j => raw25789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25789step0 raw25789; decide +kernel
      have hl : raw25789step0Labels = raw25789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25789 raw25789Labels permutation346 hz
    mixedMoment B raw25789step0 raw25789step0Labels = mixedMoment B raw25789step1 raw25789step1Labels := by
      have ha : raw25789step1 = (fun i j => raw25789step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25789step1 raw25789step0; decide +kernel
      have hl : raw25789step1Labels = raw25789step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25789step0 raw25789step0Labels permutation35 permutation7
    mixedMoment B raw25789step1 raw25789step1Labels = mixedMoment B raw25789step2 raw25789step2Labels := by
      have ha : raw25789step2 = -raw25789step1 := by apply Matrix.ext; change ∀ i j, raw25789step2 i j = -(raw25789step1 i j); unfold raw25789step2 raw25789step1; decide +kernel
      have hl : raw25789step2Labels = raw25789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25789step2 raw25789step2Labels = mixedMoment B raw25789step3 raw25789step3Labels := by
      have ha : raw25789step3 = raw25789step2 := by apply Matrix.ext; unfold raw25789step3 raw25789step2; decide +kernel
      have hl : raw25789step2Labels = labelEmbedding1 ∘ raw25789step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25789step2 raw25789step2Labels raw25789step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical202
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25974 raw25974Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw25974 raw25974Labels = mixedMoment B raw25974step0 raw25974step0Labels := by
      have hz : ∀ j, raw25974 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25974step0 = (fun i j => raw25974 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25974step0 raw25974; decide +kernel
      have hl : raw25974step0Labels = raw25974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25974 raw25974Labels permutation265 hz
    mixedMoment B raw25974step0 raw25974step0Labels = mixedMoment B raw25974step1 raw25974step1Labels := by
      have ha : raw25974step1 = (fun i j => raw25974step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25974step1 raw25974step0; decide +kernel
      have hl : raw25974step1Labels = raw25974step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25974step0 raw25974step0Labels permutation32 permutation7
    mixedMoment B raw25974step1 raw25974step1Labels = mixedMoment B raw25974step2 raw25974step2Labels := by
      have ha : raw25974step2 = -raw25974step1 := by apply Matrix.ext; change ∀ i j, raw25974step2 i j = -(raw25974step1 i j); unfold raw25974step2 raw25974step1; decide +kernel
      have hl : raw25974step2Labels = raw25974step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25974step2 raw25974step2Labels = mixedMoment B raw25974step3 raw25974step3Labels := by
      have ha : raw25974step3 = raw25974step2 := by apply Matrix.ext; unfold raw25974step3 raw25974step2; decide +kernel
      have hl : raw25974step2Labels = labelEmbedding1 ∘ raw25974step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25974step2 raw25974step2Labels raw25974step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical25975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25975 raw25975Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw25975 raw25975Labels = mixedMoment B raw25975step0 raw25975step0Labels := by
      have hz : ∀ j, raw25975 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25975step0 = (fun i j => raw25975 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25975step0 raw25975; decide +kernel
      have hl : raw25975step0Labels = raw25975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25975 raw25975Labels permutation520 hz
    mixedMoment B raw25975step0 raw25975step0Labels = mixedMoment B raw25975step1 raw25975step1Labels := by
      have hz : ∀ j, raw25975step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25975step1 = (fun i j => raw25975step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25975step1 raw25975step0; decide +kernel
      have hl : raw25975step1Labels = raw25975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25975step0 raw25975step0Labels permutation80 hz
    mixedMoment B raw25975step1 raw25975step1Labels = mixedMoment B raw25975step2 raw25975step2Labels := by
      have hz : ∀ j, raw25975step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25975step2 = (fun i j => raw25975step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25975step2 raw25975step1; decide +kernel
      have hl : raw25975step2Labels = raw25975step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25975step1 raw25975step1Labels permutation14 hz
    mixedMoment B raw25975step2 raw25975step2Labels = mixedMoment B raw25975step3 raw25975step3Labels := by
      have ha : raw25975step3 = (fun i j => raw25975step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25975step3 raw25975step2; decide +kernel
      have hl : raw25975step3Labels = raw25975step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25975step2 raw25975step2Labels permutation2 permutation7
    mixedMoment B raw25975step3 raw25975step3Labels = mixedMoment B raw25975step4 raw25975step4Labels := by
      have ha : raw25975step4 = -raw25975step3 := by apply Matrix.ext; change ∀ i j, raw25975step4 i j = -(raw25975step3 i j); unfold raw25975step4 raw25975step3; decide +kernel
      have hl : raw25975step4Labels = raw25975step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25975step4 raw25975step4Labels = mixedMoment B raw25975step5 raw25975step5Labels := by
      have ha : raw25975step5 = raw25975step4 := by apply Matrix.ext; unfold raw25975step5 raw25975step4; decide +kernel
      have hl : raw25975step4Labels = labelEmbedding1 ∘ raw25975step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25975step4 raw25975step4Labels raw25975step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2268 node2268Labels := by rfl

theorem canonical25976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25976 raw25976Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw25976 raw25976Labels = mixedMoment B raw25976step0 raw25976step0Labels := by
      have hz : ∀ j, raw25976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25976step0 = (fun i j => raw25976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25976step0 raw25976; decide +kernel
      have hl : raw25976step0Labels = raw25976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25976 raw25976Labels permutation346 hz
    mixedMoment B raw25976step0 raw25976step0Labels = mixedMoment B raw25976step1 raw25976step1Labels := by
      have hz : ∀ j, raw25976step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25976step1 = (fun i j => raw25976step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25976step1 raw25976step0; decide +kernel
      have hl : raw25976step1Labels = raw25976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25976step0 raw25976step0Labels permutation56 hz
    mixedMoment B raw25976step1 raw25976step1Labels = mixedMoment B raw25976step2 raw25976step2Labels := by
      have ha : raw25976step2 = (fun i j => raw25976step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25976step2 raw25976step1; decide +kernel
      have hl : raw25976step2Labels = raw25976step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25976step1 raw25976step1Labels permutation8 permutation7
    mixedMoment B raw25976step2 raw25976step2Labels = mixedMoment B raw25976step3 raw25976step3Labels := by
      have ha : raw25976step3 = -raw25976step2 := by apply Matrix.ext; change ∀ i j, raw25976step3 i j = -(raw25976step2 i j); unfold raw25976step3 raw25976step2; decide +kernel
      have hl : raw25976step3Labels = raw25976step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25976step3 raw25976step3Labels = mixedMoment B raw25976step4 raw25976step4Labels := by
      have ha : raw25976step4 = raw25976step3 := by apply Matrix.ext; unfold raw25976step4 raw25976step3; decide +kernel
      have hl : raw25976step3Labels = labelEmbedding1 ∘ raw25976step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25976step3 raw25976step3Labels raw25976step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical25982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25982 raw25982Labels = mixedMoment B node1662 node1662Labels := by
  calc
    mixedMoment B raw25982 raw25982Labels = mixedMoment B raw25982step0 raw25982step0Labels := by
      have ha : raw25982step0 = (fun i j => raw25982 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25982step0 raw25982; decide +kernel
      have hl : raw25982step0Labels = raw25982Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25982 raw25982Labels permutation152 permutation7
    mixedMoment B raw25982step0 raw25982step0Labels = mixedMoment B raw25982step1 raw25982step1Labels := by
      have ha : raw25982step1 = -raw25982step0 := by apply Matrix.ext; change ∀ i j, raw25982step1 i j = -(raw25982step0 i j); unfold raw25982step1 raw25982step0; decide +kernel
      have hl : raw25982step1Labels = raw25982step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25982step1 raw25982step1Labels = mixedMoment B raw25982step2 raw25982step2Labels := by
      have ha : raw25982step2 = raw25982step1 := by apply Matrix.ext; unfold raw25982step2 raw25982step1; decide +kernel
      have hl : raw25982step1Labels = labelEmbedding1 ∘ raw25982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25982step1 raw25982step1Labels raw25982step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1662 node1662Labels := by rfl

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

theorem canonical25986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25986 raw25986Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw25986 raw25986Labels = mixedMoment B raw25986step0 raw25986step0Labels := by
      have hz : ∀ j, raw25986 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25986step0 = (fun i j => raw25986 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25986step0 raw25986; decide +kernel
      have hl : raw25986step0Labels = raw25986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25986 raw25986Labels permutation346 hz
    mixedMoment B raw25986step0 raw25986step0Labels = mixedMoment B raw25986step1 raw25986step1Labels := by
      have ha : raw25986step1 = (fun i j => raw25986step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25986step1 raw25986step0; decide +kernel
      have hl : raw25986step1Labels = raw25986step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25986step0 raw25986step0Labels permutation34 permutation7
    mixedMoment B raw25986step1 raw25986step1Labels = mixedMoment B raw25986step2 raw25986step2Labels := by
      have ha : raw25986step2 = -raw25986step1 := by apply Matrix.ext; change ∀ i j, raw25986step2 i j = -(raw25986step1 i j); unfold raw25986step2 raw25986step1; decide +kernel
      have hl : raw25986step2Labels = raw25986step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25986step2 raw25986step2Labels = mixedMoment B raw25986step3 raw25986step3Labels := by
      have ha : raw25986step3 = raw25986step2 := by apply Matrix.ext; unfold raw25986step3 raw25986step2; decide +kernel
      have hl : raw25986step2Labels = labelEmbedding1 ∘ raw25986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25986step2 raw25986step2Labels raw25986step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

theorem canonical25991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25991 raw25991Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw25991 raw25991Labels = mixedMoment B raw25991step0 raw25991step0Labels := by
      have hz : ∀ j, raw25991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25991step0 = (fun i j => raw25991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25991step0 raw25991; decide +kernel
      have hl : raw25991step0Labels = raw25991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25991 raw25991Labels permutation346 hz
    mixedMoment B raw25991step0 raw25991step0Labels = mixedMoment B raw25991step1 raw25991step1Labels := by
      have ha : raw25991step1 = (fun i j => raw25991step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25991step1 raw25991step0; decide +kernel
      have hl : raw25991step1Labels = raw25991step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25991step0 raw25991step0Labels permutation32 permutation7
    mixedMoment B raw25991step1 raw25991step1Labels = mixedMoment B raw25991step2 raw25991step2Labels := by
      have ha : raw25991step2 = -raw25991step1 := by apply Matrix.ext; change ∀ i j, raw25991step2 i j = -(raw25991step1 i j); unfold raw25991step2 raw25991step1; decide +kernel
      have hl : raw25991step2Labels = raw25991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25991step2 raw25991step2Labels = mixedMoment B raw25991step3 raw25991step3Labels := by
      have ha : raw25991step3 = raw25991step2 := by apply Matrix.ext; unfold raw25991step3 raw25991step2; decide +kernel
      have hl : raw25991step2Labels = labelEmbedding1 ∘ raw25991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25991step2 raw25991step2Labels raw25991step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26358 raw26358Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw26358 raw26358Labels = mixedMoment B raw26358step0 raw26358step0Labels := by
      have hz : ∀ i, raw26358 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26358step0 = (fun i j => raw26358 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26358step0 raw26358; decide +kernel
      have hl : raw26358step0Labels = (fun j => raw26358Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26358 raw26358Labels permutation6 hz
    _ = mixedMoment B node4063 node4063Labels := by rfl

theorem canonical26361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26361 raw26361Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw26361 raw26361Labels = mixedMoment B raw26361step0 raw26361step0Labels := by
      have hz : ∀ j, raw26361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26361step0 = (fun i j => raw26361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26361step0 raw26361; decide +kernel
      have hl : raw26361step0Labels = raw26361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26361 raw26361Labels permutation346 hz
    mixedMoment B raw26361step0 raw26361step0Labels = mixedMoment B raw26361step1 raw26361step1Labels := by
      have hz : ∀ i, raw26361step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26361step1 = (fun i j => raw26361step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26361step1 raw26361step0; decide +kernel
      have hl : raw26361step1Labels = (fun j => raw26361step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26361step0 raw26361step0Labels permutation6 hz
    mixedMoment B raw26361step1 raw26361step1Labels = mixedMoment B raw26361step2 raw26361step2Labels := by
      have ha : raw26361step2 = (fun i j => raw26361step1 (permutation34 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26361step2 raw26361step1; decide +kernel
      have hl : raw26361step2Labels = raw26361step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26361step1 raw26361step1Labels permutation34 permutation0
    _ = mixedMoment B node4065 node4065Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical213
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27344 raw27344Labels = mixedMoment B node1808 node1808Labels := by
  calc
    mixedMoment B raw27344 raw27344Labels = mixedMoment B raw27344step0 raw27344step0Labels := by
      have hz : ∀ j, raw27344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27344step0 = (fun i j => raw27344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27344step0 raw27344; decide +kernel
      have hl : raw27344step0Labels = raw27344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27344 raw27344Labels permutation346 hz
    mixedMoment B raw27344step0 raw27344step0Labels = mixedMoment B raw27344step1 raw27344step1Labels := by
      have ha : raw27344step1 = (fun i j => raw27344step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27344step1 raw27344step0; decide +kernel
      have hl : raw27344step1Labels = raw27344step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27344step0 raw27344step0Labels permutation34 permutation2
    _ = mixedMoment B node1808 node1808Labels := by rfl

theorem canonical27348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27348 raw27348Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw27348 raw27348Labels = mixedMoment B raw27348step0 raw27348step0Labels := by
      have hz : ∀ j, raw27348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27348step0 = (fun i j => raw27348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27348step0 raw27348; decide +kernel
      have hl : raw27348step0Labels = raw27348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27348 raw27348Labels permutation346 hz
    mixedMoment B raw27348step0 raw27348step0Labels = mixedMoment B raw27348step1 raw27348step1Labels := by
      have ha : raw27348step1 = (fun i j => raw27348step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27348step1 raw27348step0; decide +kernel
      have hl : raw27348step1Labels = raw27348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27348step0 raw27348step0Labels permutation34 permutation2
    _ = mixedMoment B node2054 node2054Labels := by rfl

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

theorem canonical2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2924 raw2924Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2924 raw2924Labels = mixedMoment B raw2924step0 raw2924step0Labels := by
      have hz : ∀ j, raw2924 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2924step0 = (fun i j => raw2924 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2924step0 raw2924; decide +kernel
      have hl : raw2924step0Labels = raw2924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924 raw2924Labels permutation520 hz
    mixedMoment B raw2924step0 raw2924step0Labels = mixedMoment B raw2924step1 raw2924step1Labels := by
      have hz : ∀ j, raw2924step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2924step1 = (fun i j => raw2924step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2924step1 raw2924step0; decide +kernel
      have hl : raw2924step1Labels = raw2924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924step0 raw2924step0Labels permutation80 hz
    mixedMoment B raw2924step1 raw2924step1Labels = mixedMoment B raw2924step2 raw2924step2Labels := by
      have hz : ∀ j, raw2924step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2924step2 = (fun i j => raw2924step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2924step2 raw2924step1; decide +kernel
      have hl : raw2924step2Labels = raw2924step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924step1 raw2924step1Labels permutation14 hz
    mixedMoment B raw2924step2 raw2924step2Labels = mixedMoment B raw2924step3 raw2924step3Labels := by
      have hz : ∀ i, raw2924step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2924step3 = (fun i j => raw2924step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2924step3 raw2924step2; decide +kernel
      have hl : raw2924step3Labels = (fun j => raw2924step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2924step2 raw2924step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

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

theorem canonical2929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2929 raw2929Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2929 raw2929Labels = mixedMoment B raw2929step0 raw2929step0Labels := by
      have hz : ∀ j, raw2929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2929step0 = (fun i j => raw2929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2929step0 raw2929; decide +kernel
      have hl : raw2929step0Labels = raw2929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929 raw2929Labels permutation434 hz
    mixedMoment B raw2929step0 raw2929step0Labels = mixedMoment B raw2929step1 raw2929step1Labels := by
      have hz : ∀ j, raw2929step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2929step1 = (fun i j => raw2929step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2929step1 raw2929step0; decide +kernel
      have hl : raw2929step1Labels = raw2929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step0 raw2929step0Labels permutation80 hz
    mixedMoment B raw2929step1 raw2929step1Labels = mixedMoment B raw2929step2 raw2929step2Labels := by
      have hz : ∀ j, raw2929step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2929step2 = (fun i j => raw2929step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2929step2 raw2929step1; decide +kernel
      have hl : raw2929step2Labels = raw2929step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step1 raw2929step1Labels permutation14 hz
    mixedMoment B raw2929step2 raw2929step2Labels = mixedMoment B raw2929step3 raw2929step3Labels := by
      have hz : ∀ i, raw2929step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2929step3 = (fun i j => raw2929step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2929step3 raw2929step2; decide +kernel
      have hl : raw2929step3Labels = (fun j => raw2929step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2929step2 raw2929step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

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

theorem canonical29252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29252 raw29252Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw29252 raw29252Labels = mixedMoment B raw29252step0 raw29252step0Labels := by
      have hz : ∀ j, raw29252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29252step0 = (fun i j => raw29252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29252step0 raw29252; decide +kernel
      have hl : raw29252step0Labels = raw29252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29252 raw29252Labels permutation434 hz
    mixedMoment B raw29252step0 raw29252step0Labels = mixedMoment B raw29252step1 raw29252step1Labels := by
      have hz : ∀ j, raw29252step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29252step1 = (fun i j => raw29252step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29252step1 raw29252step0; decide +kernel
      have hl : raw29252step1Labels = raw29252step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29252step0 raw29252step0Labels permutation80 hz
    mixedMoment B raw29252step1 raw29252step1Labels = mixedMoment B raw29252step2 raw29252step2Labels := by
      have ha : raw29252step2 = (fun i j => raw29252step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29252step2 raw29252step1; decide +kernel
      have hl : raw29252step2Labels = raw29252step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29252step1 raw29252step1Labels permutation31 permutation7
    mixedMoment B raw29252step2 raw29252step2Labels = mixedMoment B raw29252step3 raw29252step3Labels := by
      have ha : raw29252step3 = raw29252step2 := by apply Matrix.ext; unfold raw29252step3 raw29252step2; decide +kernel
      have hl : raw29252step2Labels = labelEmbedding1 ∘ raw29252step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29252step2 raw29252step2Labels raw29252step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2726 node2726Labels := by rfl

theorem canonical29256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29256 raw29256Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw29256 raw29256Labels = mixedMoment B raw29256step0 raw29256step0Labels := by
      have hz : ∀ j, raw29256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29256step0 = (fun i j => raw29256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29256step0 raw29256; decide +kernel
      have hl : raw29256step0Labels = raw29256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29256 raw29256Labels permutation434 hz
    mixedMoment B raw29256step0 raw29256step0Labels = mixedMoment B raw29256step1 raw29256step1Labels := by
      have ha : raw29256step1 = (fun i j => raw29256step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29256step1 raw29256step0; decide +kernel
      have hl : raw29256step1Labels = raw29256step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29256step0 raw29256step0Labels permutation32 permutation7
    mixedMoment B raw29256step1 raw29256step1Labels = mixedMoment B raw29256step2 raw29256step2Labels := by
      have ha : raw29256step2 = -raw29256step1 := by apply Matrix.ext; change ∀ i j, raw29256step2 i j = -(raw29256step1 i j); unfold raw29256step2 raw29256step1; decide +kernel
      have hl : raw29256step2Labels = raw29256step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29256step2 raw29256step2Labels = mixedMoment B raw29256step3 raw29256step3Labels := by
      have ha : raw29256step3 = raw29256step2 := by apply Matrix.ext; unfold raw29256step3 raw29256step2; decide +kernel
      have hl : raw29256step2Labels = labelEmbedding1 ∘ raw29256step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29256step2 raw29256step2Labels raw29256step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical29257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29257 raw29257Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw29257 raw29257Labels = mixedMoment B raw29257step0 raw29257step0Labels := by
      have hz : ∀ j, raw29257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29257step0 = (fun i j => raw29257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29257step0 raw29257; decide +kernel
      have hl : raw29257step0Labels = raw29257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29257 raw29257Labels permutation346 hz
    mixedMoment B raw29257step0 raw29257step0Labels = mixedMoment B raw29257step1 raw29257step1Labels := by
      have ha : raw29257step1 = (fun i j => raw29257step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29257step1 raw29257step0; decide +kernel
      have hl : raw29257step1Labels = raw29257step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29257step0 raw29257step0Labels permutation32 permutation7
    mixedMoment B raw29257step1 raw29257step1Labels = mixedMoment B raw29257step2 raw29257step2Labels := by
      have ha : raw29257step2 = -raw29257step1 := by apply Matrix.ext; change ∀ i j, raw29257step2 i j = -(raw29257step1 i j); unfold raw29257step2 raw29257step1; decide +kernel
      have hl : raw29257step2Labels = raw29257step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29257step2 raw29257step2Labels = mixedMoment B raw29257step3 raw29257step3Labels := by
      have ha : raw29257step3 = raw29257step2 := by apply Matrix.ext; unfold raw29257step3 raw29257step2; decide +kernel
      have hl : raw29257step2Labels = labelEmbedding1 ∘ raw29257step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29257step2 raw29257step2Labels raw29257step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

theorem canonical29258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29258 raw29258Labels = mixedMoment B node2170 node2170Labels := by
  calc
    mixedMoment B raw29258 raw29258Labels = mixedMoment B raw29258step0 raw29258step0Labels := by
      have ha : raw29258step0 = (fun i j => raw29258 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29258step0 raw29258; decide +kernel
      have hl : raw29258step0Labels = raw29258Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29258 raw29258Labels permutation662 permutation7
    mixedMoment B raw29258step0 raw29258step0Labels = mixedMoment B raw29258step1 raw29258step1Labels := by
      have ha : raw29258step1 = raw29258step0 := by apply Matrix.ext; unfold raw29258step1 raw29258step0; decide +kernel
      have hl : raw29258step0Labels = labelEmbedding1 ∘ raw29258step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29258step0 raw29258step0Labels raw29258step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2170 node2170Labels := by rfl

theorem canonical29259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29259 raw29259Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw29259 raw29259Labels = mixedMoment B raw29259step0 raw29259step0Labels := by
      have hz : ∀ j, raw29259 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29259step0 = (fun i j => raw29259 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29259step0 raw29259; decide +kernel
      have hl : raw29259step0Labels = raw29259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29259 raw29259Labels permutation520 hz
    mixedMoment B raw29259step0 raw29259step0Labels = mixedMoment B raw29259step1 raw29259step1Labels := by
      have hz : ∀ j, raw29259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29259step1 = (fun i j => raw29259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29259step1 raw29259step0; decide +kernel
      have hl : raw29259step1Labels = raw29259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29259step0 raw29259step0Labels permutation80 hz
    mixedMoment B raw29259step1 raw29259step1Labels = mixedMoment B raw29259step2 raw29259step2Labels := by
      have ha : raw29259step2 = (fun i j => raw29259step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29259step2 raw29259step1; decide +kernel
      have hl : raw29259step2Labels = raw29259step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29259step1 raw29259step1Labels permutation31 permutation7
    mixedMoment B raw29259step2 raw29259step2Labels = mixedMoment B raw29259step3 raw29259step3Labels := by
      have ha : raw29259step3 = raw29259step2 := by apply Matrix.ext; unfold raw29259step3 raw29259step2; decide +kernel
      have hl : raw29259step2Labels = labelEmbedding1 ∘ raw29259step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29259step2 raw29259step2Labels raw29259step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

theorem canonical29263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29263 raw29263Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw29263 raw29263Labels = mixedMoment B raw29263step0 raw29263step0Labels := by
      have hz : ∀ j, raw29263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29263step0 = (fun i j => raw29263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29263step0 raw29263; decide +kernel
      have hl : raw29263step0Labels = raw29263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29263 raw29263Labels permutation434 hz
    mixedMoment B raw29263step0 raw29263step0Labels = mixedMoment B raw29263step1 raw29263step1Labels := by
      have hz : ∀ j, raw29263step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29263step1 = (fun i j => raw29263step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29263step1 raw29263step0; decide +kernel
      have hl : raw29263step1Labels = raw29263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29263step0 raw29263step0Labels permutation80 hz
    mixedMoment B raw29263step1 raw29263step1Labels = mixedMoment B raw29263step2 raw29263step2Labels := by
      have ha : raw29263step2 = (fun i j => raw29263step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29263step2 raw29263step1; decide +kernel
      have hl : raw29263step2Labels = raw29263step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29263step1 raw29263step1Labels permutation8 permutation7
    mixedMoment B raw29263step2 raw29263step2Labels = mixedMoment B raw29263step3 raw29263step3Labels := by
      have ha : raw29263step3 = -raw29263step2 := by apply Matrix.ext; change ∀ i j, raw29263step3 i j = -(raw29263step2 i j); unfold raw29263step3 raw29263step2; decide +kernel
      have hl : raw29263step3Labels = raw29263step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29263step3 raw29263step3Labels = mixedMoment B raw29263step4 raw29263step4Labels := by
      have ha : raw29263step4 = raw29263step3 := by apply Matrix.ext; unfold raw29263step4 raw29263step3; decide +kernel
      have hl : raw29263step3Labels = labelEmbedding1 ∘ raw29263step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29263step3 raw29263step3Labels raw29263step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical29270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29270 raw29270Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw29270 raw29270Labels = mixedMoment B raw29270step0 raw29270step0Labels := by
      have hz : ∀ j, raw29270 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29270step0 = (fun i j => raw29270 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29270step0 raw29270; decide +kernel
      have hl : raw29270step0Labels = raw29270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29270 raw29270Labels permutation346 hz
    _ = mixedMoment B node1804 node1804Labels := by rfl

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

theorem canonical29305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29305 raw29305Labels = mixedMoment B node1816 node1816Labels := by
  calc
    mixedMoment B raw29305 raw29305Labels = mixedMoment B raw29305step0 raw29305step0Labels := by
      have hz : ∀ j, raw29305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29305step0 = (fun i j => raw29305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29305step0 raw29305; decide +kernel
      have hl : raw29305step0Labels = raw29305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29305 raw29305Labels permutation346 hz
    _ = mixedMoment B node1816 node1816Labels := by rfl

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

theorem canonical3331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3331 raw3331Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3331 raw3331Labels = mixedMoment B raw3331step0 raw3331step0Labels := by
      have hz : ∀ j, raw3331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3331step0 = (fun i j => raw3331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3331step0 raw3331; decide +kernel
      have hl : raw3331step0Labels = raw3331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331 raw3331Labels permutation346 hz
    mixedMoment B raw3331step0 raw3331step0Labels = mixedMoment B raw3331step1 raw3331step1Labels := by
      have hz : ∀ j, raw3331step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3331step1 = (fun i j => raw3331step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3331step1 raw3331step0; decide +kernel
      have hl : raw3331step1Labels = raw3331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331step0 raw3331step0Labels permutation56 hz
    mixedMoment B raw3331step1 raw3331step1Labels = mixedMoment B raw3331step2 raw3331step2Labels := by
      have hz : ∀ i, raw3331step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3331step2 = (fun i j => raw3331step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3331step2 raw3331step1; decide +kernel
      have hl : raw3331step2Labels = (fun j => raw3331step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3331step1 raw3331step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34218 raw34218Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw34218 raw34218Labels = mixedMoment B raw34218step0 raw34218step0Labels := by
      have hz : ∀ j, raw34218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34218step0 = (fun i j => raw34218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34218step0 raw34218; decide +kernel
      have hl : raw34218step0Labels = raw34218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34218 raw34218Labels permutation346 hz
    mixedMoment B raw34218step0 raw34218step0Labels = mixedMoment B raw34218step1 raw34218step1Labels := by
      have ha : raw34218step1 = (fun i j => raw34218step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34218step1 raw34218step0; decide +kernel
      have hl : raw34218step1Labels = raw34218step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34218step0 raw34218step0Labels permutation35 permutation7
    mixedMoment B raw34218step1 raw34218step1Labels = mixedMoment B raw34218step2 raw34218step2Labels := by
      have ha : raw34218step2 = -raw34218step1 := by apply Matrix.ext; change ∀ i j, raw34218step2 i j = -(raw34218step1 i j); unfold raw34218step2 raw34218step1; decide +kernel
      have hl : raw34218step2Labels = raw34218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34218step2 raw34218step2Labels = mixedMoment B raw34218step3 raw34218step3Labels := by
      have ha : raw34218step3 = raw34218step2 := by apply Matrix.ext; unfold raw34218step3 raw34218step2; decide +kernel
      have hl : raw34218step2Labels = labelEmbedding1 ∘ raw34218step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34218step2 raw34218step2Labels raw34218step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

theorem canonical34219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34219 raw34219Labels = mixedMoment B node2695 node2695Labels := by
  calc
    mixedMoment B raw34219 raw34219Labels = mixedMoment B raw34219step0 raw34219step0Labels := by
      have ha : raw34219step0 = (fun i j => raw34219 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34219step0 raw34219; decide +kernel
      have hl : raw34219step0Labels = raw34219Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34219 raw34219Labels permutation155 permutation7
    mixedMoment B raw34219step0 raw34219step0Labels = mixedMoment B raw34219step1 raw34219step1Labels := by
      have ha : raw34219step1 = -raw34219step0 := by apply Matrix.ext; change ∀ i j, raw34219step1 i j = -(raw34219step0 i j); unfold raw34219step1 raw34219step0; decide +kernel
      have hl : raw34219step1Labels = raw34219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34219step1 raw34219step1Labels = mixedMoment B raw34219step2 raw34219step2Labels := by
      have ha : raw34219step2 = raw34219step1 := by apply Matrix.ext; unfold raw34219step2 raw34219step1; decide +kernel
      have hl : raw34219step1Labels = labelEmbedding1 ∘ raw34219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34219step1 raw34219step1Labels raw34219step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2695 node2695Labels := by rfl

theorem canonical34220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34220 raw34220Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw34220 raw34220Labels = mixedMoment B raw34220step0 raw34220step0Labels := by
      have hz : ∀ j, raw34220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34220step0 = (fun i j => raw34220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34220step0 raw34220; decide +kernel
      have hl : raw34220step0Labels = raw34220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34220 raw34220Labels permutation346 hz
    mixedMoment B raw34220step0 raw34220step0Labels = mixedMoment B raw34220step1 raw34220step1Labels := by
      have ha : raw34220step1 = (fun i j => raw34220step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34220step1 raw34220step0; decide +kernel
      have hl : raw34220step1Labels = raw34220step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34220step0 raw34220step0Labels permutation35 permutation7
    mixedMoment B raw34220step1 raw34220step1Labels = mixedMoment B raw34220step2 raw34220step2Labels := by
      have ha : raw34220step2 = -raw34220step1 := by apply Matrix.ext; change ∀ i j, raw34220step2 i j = -(raw34220step1 i j); unfold raw34220step2 raw34220step1; decide +kernel
      have hl : raw34220step2Labels = raw34220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34220step2 raw34220step2Labels = mixedMoment B raw34220step3 raw34220step3Labels := by
      have ha : raw34220step3 = raw34220step2 := by apply Matrix.ext; unfold raw34220step3 raw34220step2; decide +kernel
      have hl : raw34220step2Labels = labelEmbedding1 ∘ raw34220step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34220step2 raw34220step2Labels raw34220step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

theorem canonical34221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34221 raw34221Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw34221 raw34221Labels = mixedMoment B raw34221step0 raw34221step0Labels := by
      have hz : ∀ j, raw34221 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34221step0 = (fun i j => raw34221 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34221step0 raw34221; decide +kernel
      have hl : raw34221step0Labels = raw34221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34221 raw34221Labels permutation520 hz
    mixedMoment B raw34221step0 raw34221step0Labels = mixedMoment B raw34221step1 raw34221step1Labels := by
      have hz : ∀ j, raw34221step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34221step1 = (fun i j => raw34221step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34221step1 raw34221step0; decide +kernel
      have hl : raw34221step1Labels = raw34221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34221step0 raw34221step0Labels permutation80 hz
    mixedMoment B raw34221step1 raw34221step1Labels = mixedMoment B raw34221step2 raw34221step2Labels := by
      have ha : raw34221step2 = (fun i j => raw34221step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34221step2 raw34221step1; decide +kernel
      have hl : raw34221step2Labels = raw34221step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34221step1 raw34221step1Labels permutation9 permutation7
    mixedMoment B raw34221step2 raw34221step2Labels = mixedMoment B raw34221step3 raw34221step3Labels := by
      have ha : raw34221step3 = -raw34221step2 := by apply Matrix.ext; change ∀ i j, raw34221step3 i j = -(raw34221step2 i j); unfold raw34221step3 raw34221step2; decide +kernel
      have hl : raw34221step3Labels = raw34221step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34221step3 raw34221step3Labels = mixedMoment B raw34221step4 raw34221step4Labels := by
      have ha : raw34221step4 = raw34221step3 := by apply Matrix.ext; unfold raw34221step4 raw34221step3; decide +kernel
      have hl : raw34221step3Labels = labelEmbedding1 ∘ raw34221step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34221step3 raw34221step3Labels raw34221step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical34222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34222 raw34222Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw34222 raw34222Labels = mixedMoment B raw34222step0 raw34222step0Labels := by
      have hz : ∀ j, raw34222 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34222step0 = (fun i j => raw34222 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34222step0 raw34222; decide +kernel
      have hl : raw34222step0Labels = raw34222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34222 raw34222Labels permutation346 hz
    mixedMoment B raw34222step0 raw34222step0Labels = mixedMoment B raw34222step1 raw34222step1Labels := by
      have ha : raw34222step1 = (fun i j => raw34222step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34222step1 raw34222step0; decide +kernel
      have hl : raw34222step1Labels = raw34222step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34222step0 raw34222step0Labels permutation35 permutation7
    mixedMoment B raw34222step1 raw34222step1Labels = mixedMoment B raw34222step2 raw34222step2Labels := by
      have ha : raw34222step2 = -raw34222step1 := by apply Matrix.ext; change ∀ i j, raw34222step2 i j = -(raw34222step1 i j); unfold raw34222step2 raw34222step1; decide +kernel
      have hl : raw34222step2Labels = raw34222step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34222step2 raw34222step2Labels = mixedMoment B raw34222step3 raw34222step3Labels := by
      have ha : raw34222step3 = raw34222step2 := by apply Matrix.ext; unfold raw34222step3 raw34222step2; decide +kernel
      have hl : raw34222step2Labels = labelEmbedding1 ∘ raw34222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34222step2 raw34222step2Labels raw34222step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical34223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34223 raw34223Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw34223 raw34223Labels = mixedMoment B raw34223step0 raw34223step0Labels := by
      have hz : ∀ j, raw34223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34223step0 = (fun i j => raw34223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34223step0 raw34223; decide +kernel
      have hl : raw34223step0Labels = raw34223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34223 raw34223Labels permutation346 hz
    mixedMoment B raw34223step0 raw34223step0Labels = mixedMoment B raw34223step1 raw34223step1Labels := by
      have hz : ∀ j, raw34223step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34223step1 = (fun i j => raw34223step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34223step1 raw34223step0; decide +kernel
      have hl : raw34223step1Labels = raw34223step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34223step0 raw34223step0Labels permutation56 hz
    mixedMoment B raw34223step1 raw34223step1Labels = mixedMoment B raw34223step2 raw34223step2Labels := by
      have ha : raw34223step2 = (fun i j => raw34223step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34223step2 raw34223step1; decide +kernel
      have hl : raw34223step2Labels = raw34223step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34223step1 raw34223step1Labels permutation11 permutation7
    mixedMoment B raw34223step2 raw34223step2Labels = mixedMoment B raw34223step3 raw34223step3Labels := by
      have ha : raw34223step3 = -raw34223step2 := by apply Matrix.ext; change ∀ i j, raw34223step3 i j = -(raw34223step2 i j); unfold raw34223step3 raw34223step2; decide +kernel
      have hl : raw34223step3Labels = raw34223step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34223step3 raw34223step3Labels = mixedMoment B raw34223step4 raw34223step4Labels := by
      have ha : raw34223step4 = raw34223step3 := by apply Matrix.ext; unfold raw34223step4 raw34223step3; decide +kernel
      have hl : raw34223step3Labels = labelEmbedding1 ∘ raw34223step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34223step3 raw34223step3Labels raw34223step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical34224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34224 raw34224Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw34224 raw34224Labels = mixedMoment B raw34224step0 raw34224step0Labels := by
      have ha : raw34224step0 = (fun i j => raw34224 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34224step0 raw34224; decide +kernel
      have hl : raw34224step0Labels = raw34224Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34224 raw34224Labels permutation155 permutation7
    mixedMoment B raw34224step0 raw34224step0Labels = mixedMoment B raw34224step1 raw34224step1Labels := by
      have ha : raw34224step1 = -raw34224step0 := by apply Matrix.ext; change ∀ i j, raw34224step1 i j = -(raw34224step0 i j); unfold raw34224step1 raw34224step0; decide +kernel
      have hl : raw34224step1Labels = raw34224step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34224step1 raw34224step1Labels = mixedMoment B raw34224step2 raw34224step2Labels := by
      have ha : raw34224step2 = raw34224step1 := by apply Matrix.ext; unfold raw34224step2 raw34224step1; decide +kernel
      have hl : raw34224step1Labels = labelEmbedding1 ∘ raw34224step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34224step1 raw34224step1Labels raw34224step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

theorem canonical34225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34225 raw34225Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw34225 raw34225Labels = mixedMoment B raw34225step0 raw34225step0Labels := by
      have ha : raw34225step0 = (fun i j => raw34225 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34225step0 raw34225; decide +kernel
      have hl : raw34225step0Labels = raw34225Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34225 raw34225Labels permutation155 permutation7
    mixedMoment B raw34225step0 raw34225step0Labels = mixedMoment B raw34225step1 raw34225step1Labels := by
      have ha : raw34225step1 = -raw34225step0 := by apply Matrix.ext; change ∀ i j, raw34225step1 i j = -(raw34225step0 i j); unfold raw34225step1 raw34225step0; decide +kernel
      have hl : raw34225step1Labels = raw34225step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34225step1 raw34225step1Labels = mixedMoment B raw34225step2 raw34225step2Labels := by
      have ha : raw34225step2 = raw34225step1 := by apply Matrix.ext; unfold raw34225step2 raw34225step1; decide +kernel
      have hl : raw34225step1Labels = labelEmbedding1 ∘ raw34225step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34225step1 raw34225step1Labels raw34225step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2192 node2192Labels := by rfl

theorem canonical34226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34226 raw34226Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw34226 raw34226Labels = mixedMoment B raw34226step0 raw34226step0Labels := by
      have hz : ∀ j, raw34226 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34226step0 = (fun i j => raw34226 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34226step0 raw34226; decide +kernel
      have hl : raw34226step0Labels = raw34226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34226 raw34226Labels permutation520 hz
    mixedMoment B raw34226step0 raw34226step0Labels = mixedMoment B raw34226step1 raw34226step1Labels := by
      have ha : raw34226step1 = (fun i j => raw34226step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34226step1 raw34226step0; decide +kernel
      have hl : raw34226step1Labels = raw34226step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34226step0 raw34226step0Labels permutation33 permutation7
    mixedMoment B raw34226step1 raw34226step1Labels = mixedMoment B raw34226step2 raw34226step2Labels := by
      have ha : raw34226step2 = -raw34226step1 := by apply Matrix.ext; change ∀ i j, raw34226step2 i j = -(raw34226step1 i j); unfold raw34226step2 raw34226step1; decide +kernel
      have hl : raw34226step2Labels = raw34226step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34226step2 raw34226step2Labels = mixedMoment B raw34226step3 raw34226step3Labels := by
      have ha : raw34226step3 = raw34226step2 := by apply Matrix.ext; unfold raw34226step3 raw34226step2; decide +kernel
      have hl : raw34226step2Labels = labelEmbedding1 ∘ raw34226step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34226step2 raw34226step2Labels raw34226step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical34227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34227 raw34227Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw34227 raw34227Labels = mixedMoment B raw34227step0 raw34227step0Labels := by
      have ha : raw34227step0 = (fun i j => raw34227 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34227step0 raw34227; decide +kernel
      have hl : raw34227step0Labels = raw34227Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34227 raw34227Labels permutation155 permutation7
    mixedMoment B raw34227step0 raw34227step0Labels = mixedMoment B raw34227step1 raw34227step1Labels := by
      have ha : raw34227step1 = -raw34227step0 := by apply Matrix.ext; change ∀ i j, raw34227step1 i j = -(raw34227step0 i j); unfold raw34227step1 raw34227step0; decide +kernel
      have hl : raw34227step1Labels = raw34227step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34227step1 raw34227step1Labels = mixedMoment B raw34227step2 raw34227step2Labels := by
      have ha : raw34227step2 = raw34227step1 := by apply Matrix.ext; unfold raw34227step2 raw34227step1; decide +kernel
      have hl : raw34227step1Labels = labelEmbedding1 ∘ raw34227step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34227step1 raw34227step1Labels raw34227step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical34228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34228 raw34228Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw34228 raw34228Labels = mixedMoment B raw34228step0 raw34228step0Labels := by
      have hz : ∀ j, raw34228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34228step0 = (fun i j => raw34228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34228step0 raw34228; decide +kernel
      have hl : raw34228step0Labels = raw34228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34228 raw34228Labels permutation346 hz
    mixedMoment B raw34228step0 raw34228step0Labels = mixedMoment B raw34228step1 raw34228step1Labels := by
      have ha : raw34228step1 = (fun i j => raw34228step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34228step1 raw34228step0; decide +kernel
      have hl : raw34228step1Labels = raw34228step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34228step0 raw34228step0Labels permutation35 permutation7
    mixedMoment B raw34228step1 raw34228step1Labels = mixedMoment B raw34228step2 raw34228step2Labels := by
      have ha : raw34228step2 = -raw34228step1 := by apply Matrix.ext; change ∀ i j, raw34228step2 i j = -(raw34228step1 i j); unfold raw34228step2 raw34228step1; decide +kernel
      have hl : raw34228step2Labels = raw34228step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34228step2 raw34228step2Labels = mixedMoment B raw34228step3 raw34228step3Labels := by
      have ha : raw34228step3 = raw34228step2 := by apply Matrix.ext; unfold raw34228step3 raw34228step2; decide +kernel
      have hl : raw34228step2Labels = labelEmbedding1 ∘ raw34228step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34228step2 raw34228step2Labels raw34228step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

theorem canonical34229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34229 raw34229Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw34229 raw34229Labels = mixedMoment B raw34229step0 raw34229step0Labels := by
      have ha : raw34229step0 = (fun i j => raw34229 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34229step0 raw34229; decide +kernel
      have hl : raw34229step0Labels = raw34229Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34229 raw34229Labels permutation155 permutation7
    mixedMoment B raw34229step0 raw34229step0Labels = mixedMoment B raw34229step1 raw34229step1Labels := by
      have ha : raw34229step1 = -raw34229step0 := by apply Matrix.ext; change ∀ i j, raw34229step1 i j = -(raw34229step0 i j); unfold raw34229step1 raw34229step0; decide +kernel
      have hl : raw34229step1Labels = raw34229step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34229step1 raw34229step1Labels = mixedMoment B raw34229step2 raw34229step2Labels := by
      have ha : raw34229step2 = raw34229step1 := by apply Matrix.ext; unfold raw34229step2 raw34229step1; decide +kernel
      have hl : raw34229step1Labels = labelEmbedding1 ∘ raw34229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34229step1 raw34229step1Labels raw34229step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

theorem canonical34230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34230 raw34230Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw34230 raw34230Labels = mixedMoment B raw34230step0 raw34230step0Labels := by
      have hz : ∀ j, raw34230 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34230step0 = (fun i j => raw34230 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34230step0 raw34230; decide +kernel
      have hl : raw34230step0Labels = raw34230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34230 raw34230Labels permutation520 hz
    mixedMoment B raw34230step0 raw34230step0Labels = mixedMoment B raw34230step1 raw34230step1Labels := by
      have hz : ∀ j, raw34230step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34230step1 = (fun i j => raw34230step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34230step1 raw34230step0; decide +kernel
      have hl : raw34230step1Labels = raw34230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34230step0 raw34230step0Labels permutation80 hz
    mixedMoment B raw34230step1 raw34230step1Labels = mixedMoment B raw34230step2 raw34230step2Labels := by
      have ha : raw34230step2 = (fun i j => raw34230step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34230step2 raw34230step1; decide +kernel
      have hl : raw34230step2Labels = raw34230step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34230step1 raw34230step1Labels permutation9 permutation7
    mixedMoment B raw34230step2 raw34230step2Labels = mixedMoment B raw34230step3 raw34230step3Labels := by
      have ha : raw34230step3 = -raw34230step2 := by apply Matrix.ext; change ∀ i j, raw34230step3 i j = -(raw34230step2 i j); unfold raw34230step3 raw34230step2; decide +kernel
      have hl : raw34230step3Labels = raw34230step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34230step3 raw34230step3Labels = mixedMoment B raw34230step4 raw34230step4Labels := by
      have ha : raw34230step4 = raw34230step3 := by apply Matrix.ext; unfold raw34230step4 raw34230step3; decide +kernel
      have hl : raw34230step3Labels = labelEmbedding1 ∘ raw34230step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34230step3 raw34230step3Labels raw34230step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical34231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34231 raw34231Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw34231 raw34231Labels = mixedMoment B raw34231step0 raw34231step0Labels := by
      have hz : ∀ j, raw34231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34231step0 = (fun i j => raw34231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34231step0 raw34231; decide +kernel
      have hl : raw34231step0Labels = raw34231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34231 raw34231Labels permutation346 hz
    mixedMoment B raw34231step0 raw34231step0Labels = mixedMoment B raw34231step1 raw34231step1Labels := by
      have ha : raw34231step1 = (fun i j => raw34231step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34231step1 raw34231step0; decide +kernel
      have hl : raw34231step1Labels = raw34231step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34231step0 raw34231step0Labels permutation35 permutation7
    mixedMoment B raw34231step1 raw34231step1Labels = mixedMoment B raw34231step2 raw34231step2Labels := by
      have ha : raw34231step2 = -raw34231step1 := by apply Matrix.ext; change ∀ i j, raw34231step2 i j = -(raw34231step1 i j); unfold raw34231step2 raw34231step1; decide +kernel
      have hl : raw34231step2Labels = raw34231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34231step2 raw34231step2Labels = mixedMoment B raw34231step3 raw34231step3Labels := by
      have ha : raw34231step3 = raw34231step2 := by apply Matrix.ext; unfold raw34231step3 raw34231step2; decide +kernel
      have hl : raw34231step2Labels = labelEmbedding1 ∘ raw34231step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34231step2 raw34231step2Labels raw34231step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical34232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34232 raw34232Labels = mixedMoment B node2158 node2158Labels := by
  calc
    mixedMoment B raw34232 raw34232Labels = mixedMoment B raw34232step0 raw34232step0Labels := by
      have hz : ∀ j, raw34232 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34232step0 = (fun i j => raw34232 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34232step0 raw34232; decide +kernel
      have hl : raw34232step0Labels = raw34232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34232 raw34232Labels permutation346 hz
    mixedMoment B raw34232step0 raw34232step0Labels = mixedMoment B raw34232step1 raw34232step1Labels := by
      have ha : raw34232step1 = (fun i j => raw34232step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34232step1 raw34232step0; decide +kernel
      have hl : raw34232step1Labels = raw34232step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34232step0 raw34232step0Labels permutation35 permutation7
    mixedMoment B raw34232step1 raw34232step1Labels = mixedMoment B raw34232step2 raw34232step2Labels := by
      have ha : raw34232step2 = -raw34232step1 := by apply Matrix.ext; change ∀ i j, raw34232step2 i j = -(raw34232step1 i j); unfold raw34232step2 raw34232step1; decide +kernel
      have hl : raw34232step2Labels = raw34232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34232step2 raw34232step2Labels = mixedMoment B raw34232step3 raw34232step3Labels := by
      have ha : raw34232step3 = raw34232step2 := by apply Matrix.ext; unfold raw34232step3 raw34232step2; decide +kernel
      have hl : raw34232step2Labels = labelEmbedding1 ∘ raw34232step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34232step2 raw34232step2Labels raw34232step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2158 node2158Labels := by rfl

theorem canonical34233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34233 raw34233Labels = mixedMoment B node2178 node2178Labels := by
  calc
    mixedMoment B raw34233 raw34233Labels = mixedMoment B raw34233step0 raw34233step0Labels := by
      have ha : raw34233step0 = (fun i j => raw34233 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34233step0 raw34233; decide +kernel
      have hl : raw34233step0Labels = raw34233Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34233 raw34233Labels permutation155 permutation7
    mixedMoment B raw34233step0 raw34233step0Labels = mixedMoment B raw34233step1 raw34233step1Labels := by
      have ha : raw34233step1 = -raw34233step0 := by apply Matrix.ext; change ∀ i j, raw34233step1 i j = -(raw34233step0 i j); unfold raw34233step1 raw34233step0; decide +kernel
      have hl : raw34233step1Labels = raw34233step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34233step1 raw34233step1Labels = mixedMoment B raw34233step2 raw34233step2Labels := by
      have ha : raw34233step2 = raw34233step1 := by apply Matrix.ext; unfold raw34233step2 raw34233step1; decide +kernel
      have hl : raw34233step1Labels = labelEmbedding1 ∘ raw34233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34233step1 raw34233step1Labels raw34233step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2178 node2178Labels := by rfl

theorem canonical34234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34234 raw34234Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw34234 raw34234Labels = mixedMoment B raw34234step0 raw34234step0Labels := by
      have hz : ∀ j, raw34234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34234step0 = (fun i j => raw34234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34234step0 raw34234; decide +kernel
      have hl : raw34234step0Labels = raw34234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34234 raw34234Labels permutation346 hz
    mixedMoment B raw34234step0 raw34234step0Labels = mixedMoment B raw34234step1 raw34234step1Labels := by
      have ha : raw34234step1 = (fun i j => raw34234step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34234step1 raw34234step0; decide +kernel
      have hl : raw34234step1Labels = raw34234step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34234step0 raw34234step0Labels permutation35 permutation7
    mixedMoment B raw34234step1 raw34234step1Labels = mixedMoment B raw34234step2 raw34234step2Labels := by
      have ha : raw34234step2 = -raw34234step1 := by apply Matrix.ext; change ∀ i j, raw34234step2 i j = -(raw34234step1 i j); unfold raw34234step2 raw34234step1; decide +kernel
      have hl : raw34234step2Labels = raw34234step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34234step2 raw34234step2Labels = mixedMoment B raw34234step3 raw34234step3Labels := by
      have ha : raw34234step3 = raw34234step2 := by apply Matrix.ext; unfold raw34234step3 raw34234step2; decide +kernel
      have hl : raw34234step2Labels = labelEmbedding1 ∘ raw34234step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34234step2 raw34234step2Labels raw34234step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

theorem canonical34235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34235 raw34235Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw34235 raw34235Labels = mixedMoment B raw34235step0 raw34235step0Labels := by
      have hz : ∀ j, raw34235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34235step0 = (fun i j => raw34235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34235step0 raw34235; decide +kernel
      have hl : raw34235step0Labels = raw34235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34235 raw34235Labels permutation346 hz
    mixedMoment B raw34235step0 raw34235step0Labels = mixedMoment B raw34235step1 raw34235step1Labels := by
      have ha : raw34235step1 = (fun i j => raw34235step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34235step1 raw34235step0; decide +kernel
      have hl : raw34235step1Labels = raw34235step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34235step0 raw34235step0Labels permutation35 permutation7
    mixedMoment B raw34235step1 raw34235step1Labels = mixedMoment B raw34235step2 raw34235step2Labels := by
      have ha : raw34235step2 = -raw34235step1 := by apply Matrix.ext; change ∀ i j, raw34235step2 i j = -(raw34235step1 i j); unfold raw34235step2 raw34235step1; decide +kernel
      have hl : raw34235step2Labels = raw34235step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34235step2 raw34235step2Labels = mixedMoment B raw34235step3 raw34235step3Labels := by
      have ha : raw34235step3 = raw34235step2 := by apply Matrix.ext; unfold raw34235step3 raw34235step2; decide +kernel
      have hl : raw34235step2Labels = labelEmbedding1 ∘ raw34235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34235step2 raw34235step2Labels raw34235step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical34236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34236 raw34236Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw34236 raw34236Labels = mixedMoment B raw34236step0 raw34236step0Labels := by
      have hz : ∀ j, raw34236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34236step0 = (fun i j => raw34236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34236step0 raw34236; decide +kernel
      have hl : raw34236step0Labels = raw34236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34236 raw34236Labels permutation346 hz
    mixedMoment B raw34236step0 raw34236step0Labels = mixedMoment B raw34236step1 raw34236step1Labels := by
      have ha : raw34236step1 = (fun i j => raw34236step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34236step1 raw34236step0; decide +kernel
      have hl : raw34236step1Labels = raw34236step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34236step0 raw34236step0Labels permutation35 permutation7
    mixedMoment B raw34236step1 raw34236step1Labels = mixedMoment B raw34236step2 raw34236step2Labels := by
      have ha : raw34236step2 = -raw34236step1 := by apply Matrix.ext; change ∀ i j, raw34236step2 i j = -(raw34236step1 i j); unfold raw34236step2 raw34236step1; decide +kernel
      have hl : raw34236step2Labels = raw34236step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34236step2 raw34236step2Labels = mixedMoment B raw34236step3 raw34236step3Labels := by
      have ha : raw34236step3 = raw34236step2 := by apply Matrix.ext; unfold raw34236step3 raw34236step2; decide +kernel
      have hl : raw34236step2Labels = labelEmbedding1 ∘ raw34236step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34236step2 raw34236step2Labels raw34236step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2153 node2153Labels := by rfl

theorem canonical34237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34237 raw34237Labels = mixedMoment B node2175 node2175Labels := by
  calc
    mixedMoment B raw34237 raw34237Labels = mixedMoment B raw34237step0 raw34237step0Labels := by
      have ha : raw34237step0 = (fun i j => raw34237 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34237step0 raw34237; decide +kernel
      have hl : raw34237step0Labels = raw34237Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34237 raw34237Labels permutation155 permutation7
    mixedMoment B raw34237step0 raw34237step0Labels = mixedMoment B raw34237step1 raw34237step1Labels := by
      have ha : raw34237step1 = -raw34237step0 := by apply Matrix.ext; change ∀ i j, raw34237step1 i j = -(raw34237step0 i j); unfold raw34237step1 raw34237step0; decide +kernel
      have hl : raw34237step1Labels = raw34237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34237step1 raw34237step1Labels = mixedMoment B raw34237step2 raw34237step2Labels := by
      have ha : raw34237step2 = raw34237step1 := by apply Matrix.ext; unfold raw34237step2 raw34237step1; decide +kernel
      have hl : raw34237step1Labels = labelEmbedding1 ∘ raw34237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34237step1 raw34237step1Labels raw34237step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2175 node2175Labels := by rfl

theorem canonical34238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34238 raw34238Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw34238 raw34238Labels = mixedMoment B raw34238step0 raw34238step0Labels := by
      have hz : ∀ j, raw34238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34238step0 = (fun i j => raw34238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34238step0 raw34238; decide +kernel
      have hl : raw34238step0Labels = raw34238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34238 raw34238Labels permutation346 hz
    mixedMoment B raw34238step0 raw34238step0Labels = mixedMoment B raw34238step1 raw34238step1Labels := by
      have ha : raw34238step1 = (fun i j => raw34238step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34238step1 raw34238step0; decide +kernel
      have hl : raw34238step1Labels = raw34238step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34238step0 raw34238step0Labels permutation35 permutation7
    mixedMoment B raw34238step1 raw34238step1Labels = mixedMoment B raw34238step2 raw34238step2Labels := by
      have ha : raw34238step2 = -raw34238step1 := by apply Matrix.ext; change ∀ i j, raw34238step2 i j = -(raw34238step1 i j); unfold raw34238step2 raw34238step1; decide +kernel
      have hl : raw34238step2Labels = raw34238step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34238step2 raw34238step2Labels = mixedMoment B raw34238step3 raw34238step3Labels := by
      have ha : raw34238step3 = raw34238step2 := by apply Matrix.ext; unfold raw34238step3 raw34238step2; decide +kernel
      have hl : raw34238step2Labels = labelEmbedding1 ∘ raw34238step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34238step2 raw34238step2Labels raw34238step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical34239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34239 raw34239Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw34239 raw34239Labels = mixedMoment B raw34239step0 raw34239step0Labels := by
      have hz : ∀ j, raw34239 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34239step0 = (fun i j => raw34239 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34239step0 raw34239; decide +kernel
      have hl : raw34239step0Labels = raw34239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34239 raw34239Labels permutation520 hz
    mixedMoment B raw34239step0 raw34239step0Labels = mixedMoment B raw34239step1 raw34239step1Labels := by
      have hz : ∀ j, raw34239step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34239step1 = (fun i j => raw34239step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34239step1 raw34239step0; decide +kernel
      have hl : raw34239step1Labels = raw34239step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34239step0 raw34239step0Labels permutation80 hz
    mixedMoment B raw34239step1 raw34239step1Labels = mixedMoment B raw34239step2 raw34239step2Labels := by
      have ha : raw34239step2 = (fun i j => raw34239step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34239step2 raw34239step1; decide +kernel
      have hl : raw34239step2Labels = raw34239step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34239step1 raw34239step1Labels permutation9 permutation7
    mixedMoment B raw34239step2 raw34239step2Labels = mixedMoment B raw34239step3 raw34239step3Labels := by
      have ha : raw34239step3 = -raw34239step2 := by apply Matrix.ext; change ∀ i j, raw34239step3 i j = -(raw34239step2 i j); unfold raw34239step3 raw34239step2; decide +kernel
      have hl : raw34239step3Labels = raw34239step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34239step3 raw34239step3Labels = mixedMoment B raw34239step4 raw34239step4Labels := by
      have ha : raw34239step4 = raw34239step3 := by apply Matrix.ext; unfold raw34239step4 raw34239step3; decide +kernel
      have hl : raw34239step3Labels = labelEmbedding1 ∘ raw34239step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34239step3 raw34239step3Labels raw34239step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical34240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34240 raw34240Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw34240 raw34240Labels = mixedMoment B raw34240step0 raw34240step0Labels := by
      have hz : ∀ j, raw34240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34240step0 = (fun i j => raw34240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34240step0 raw34240; decide +kernel
      have hl : raw34240step0Labels = raw34240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34240 raw34240Labels permutation346 hz
    mixedMoment B raw34240step0 raw34240step0Labels = mixedMoment B raw34240step1 raw34240step1Labels := by
      have ha : raw34240step1 = (fun i j => raw34240step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34240step1 raw34240step0; decide +kernel
      have hl : raw34240step1Labels = raw34240step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34240step0 raw34240step0Labels permutation34 permutation2
    _ = mixedMoment B node3392 node3392Labels := by rfl

theorem canonical34241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34241 raw34241Labels = mixedMoment B node1803 node1803Labels := by
  calc
    mixedMoment B raw34241 raw34241Labels = mixedMoment B raw34241step0 raw34241step0Labels := by
      have ha : raw34241step0 = (fun i j => raw34241 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34241step0 raw34241; decide +kernel
      have hl : raw34241step0Labels = raw34241Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34241 raw34241Labels permutation154 permutation2
    _ = mixedMoment B node1803 node1803Labels := by rfl

theorem canonical34242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34242 raw34242Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw34242 raw34242Labels = mixedMoment B raw34242step0 raw34242step0Labels := by
      have hz : ∀ j, raw34242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34242step0 = (fun i j => raw34242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34242step0 raw34242; decide +kernel
      have hl : raw34242step0Labels = raw34242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34242 raw34242Labels permutation346 hz
    mixedMoment B raw34242step0 raw34242step0Labels = mixedMoment B raw34242step1 raw34242step1Labels := by
      have ha : raw34242step1 = (fun i j => raw34242step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34242step1 raw34242step0; decide +kernel
      have hl : raw34242step1Labels = raw34242step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34242step0 raw34242step0Labels permutation35 permutation2
    _ = mixedMoment B node1810 node1810Labels := by rfl

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

theorem canonical34350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34350 raw34350Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw34350 raw34350Labels = mixedMoment B raw34350step0 raw34350step0Labels := by
      have hz : ∀ j, raw34350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34350step0 = (fun i j => raw34350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34350step0 raw34350; decide +kernel
      have hl : raw34350step0Labels = raw34350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34350 raw34350Labels permutation346 hz
    mixedMoment B raw34350step0 raw34350step0Labels = mixedMoment B raw34350step1 raw34350step1Labels := by
      have ha : raw34350step1 = (fun i j => raw34350step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34350step1 raw34350step0; decide +kernel
      have hl : raw34350step1Labels = raw34350step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34350step0 raw34350step0Labels permutation32 permutation7
    mixedMoment B raw34350step1 raw34350step1Labels = mixedMoment B raw34350step2 raw34350step2Labels := by
      have ha : raw34350step2 = -raw34350step1 := by apply Matrix.ext; change ∀ i j, raw34350step2 i j = -(raw34350step1 i j); unfold raw34350step2 raw34350step1; decide +kernel
      have hl : raw34350step2Labels = raw34350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34350step2 raw34350step2Labels = mixedMoment B raw34350step3 raw34350step3Labels := by
      have ha : raw34350step3 = raw34350step2 := by apply Matrix.ext; unfold raw34350step3 raw34350step2; decide +kernel
      have hl : raw34350step2Labels = labelEmbedding1 ∘ raw34350step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34350step2 raw34350step2Labels raw34350step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2664 node2664Labels := by rfl

theorem canonical34351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34351 raw34351Labels = mixedMoment B node2691 node2691Labels := by
  calc
    mixedMoment B raw34351 raw34351Labels = mixedMoment B raw34351step0 raw34351step0Labels := by
      have ha : raw34351step0 = (fun i j => raw34351 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34351step0 raw34351; decide +kernel
      have hl : raw34351step0Labels = raw34351Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34351 raw34351Labels permutation662 permutation7
    mixedMoment B raw34351step0 raw34351step0Labels = mixedMoment B raw34351step1 raw34351step1Labels := by
      have ha : raw34351step1 = raw34351step0 := by apply Matrix.ext; unfold raw34351step1 raw34351step0; decide +kernel
      have hl : raw34351step0Labels = labelEmbedding1 ∘ raw34351step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34351step0 raw34351step0Labels raw34351step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2691 node2691Labels := by rfl

theorem canonical34352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34352 raw34352Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw34352 raw34352Labels = mixedMoment B raw34352step0 raw34352step0Labels := by
      have hz : ∀ j, raw34352 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34352step0 = (fun i j => raw34352 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34352step0 raw34352; decide +kernel
      have hl : raw34352step0Labels = raw34352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34352 raw34352Labels permutation520 hz
    mixedMoment B raw34352step0 raw34352step0Labels = mixedMoment B raw34352step1 raw34352step1Labels := by
      have hz : ∀ j, raw34352step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34352step1 = (fun i j => raw34352step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34352step1 raw34352step0; decide +kernel
      have hl : raw34352step1Labels = raw34352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34352step0 raw34352step0Labels permutation80 hz
    mixedMoment B raw34352step1 raw34352step1Labels = mixedMoment B raw34352step2 raw34352step2Labels := by
      have ha : raw34352step2 = (fun i j => raw34352step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34352step2 raw34352step1; decide +kernel
      have hl : raw34352step2Labels = raw34352step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34352step1 raw34352step1Labels permutation31 permutation7
    mixedMoment B raw34352step2 raw34352step2Labels = mixedMoment B raw34352step3 raw34352step3Labels := by
      have ha : raw34352step3 = raw34352step2 := by apply Matrix.ext; unfold raw34352step3 raw34352step2; decide +kernel
      have hl : raw34352step2Labels = labelEmbedding1 ∘ raw34352step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34352step2 raw34352step2Labels raw34352step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2726 node2726Labels := by rfl

theorem canonical34353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34353 raw34353Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw34353 raw34353Labels = mixedMoment B raw34353step0 raw34353step0Labels := by
      have hz : ∀ j, raw34353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34353step0 = (fun i j => raw34353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34353step0 raw34353; decide +kernel
      have hl : raw34353step0Labels = raw34353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34353 raw34353Labels permutation346 hz
    mixedMoment B raw34353step0 raw34353step0Labels = mixedMoment B raw34353step1 raw34353step1Labels := by
      have ha : raw34353step1 = (fun i j => raw34353step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34353step1 raw34353step0; decide +kernel
      have hl : raw34353step1Labels = raw34353step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34353step0 raw34353step0Labels permutation32 permutation7
    mixedMoment B raw34353step1 raw34353step1Labels = mixedMoment B raw34353step2 raw34353step2Labels := by
      have ha : raw34353step2 = -raw34353step1 := by apply Matrix.ext; change ∀ i j, raw34353step2 i j = -(raw34353step1 i j); unfold raw34353step2 raw34353step1; decide +kernel
      have hl : raw34353step2Labels = raw34353step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34353step2 raw34353step2Labels = mixedMoment B raw34353step3 raw34353step3Labels := by
      have ha : raw34353step3 = raw34353step2 := by apply Matrix.ext; unfold raw34353step3 raw34353step2; decide +kernel
      have hl : raw34353step2Labels = labelEmbedding1 ∘ raw34353step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34353step2 raw34353step2Labels raw34353step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2712 node2712Labels := by rfl

theorem canonical34354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34354 raw34354Labels = mixedMoment B node2139 node2139Labels := by
  calc
    mixedMoment B raw34354 raw34354Labels = mixedMoment B raw34354step0 raw34354step0Labels := by
      have ha : raw34354step0 = (fun i j => raw34354 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34354step0 raw34354; decide +kernel
      have hl : raw34354step0Labels = raw34354Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34354 raw34354Labels permutation152 permutation7
    mixedMoment B raw34354step0 raw34354step0Labels = mixedMoment B raw34354step1 raw34354step1Labels := by
      have ha : raw34354step1 = -raw34354step0 := by apply Matrix.ext; change ∀ i j, raw34354step1 i j = -(raw34354step0 i j); unfold raw34354step1 raw34354step0; decide +kernel
      have hl : raw34354step1Labels = raw34354step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34354step1 raw34354step1Labels = mixedMoment B raw34354step2 raw34354step2Labels := by
      have ha : raw34354step2 = raw34354step1 := by apply Matrix.ext; unfold raw34354step2 raw34354step1; decide +kernel
      have hl : raw34354step1Labels = labelEmbedding1 ∘ raw34354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34354step1 raw34354step1Labels raw34354step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2139 node2139Labels := by rfl

theorem canonical34355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34355 raw34355Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw34355 raw34355Labels = mixedMoment B raw34355step0 raw34355step0Labels := by
      have hz : ∀ j, raw34355 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34355step0 = (fun i j => raw34355 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34355step0 raw34355; decide +kernel
      have hl : raw34355step0Labels = raw34355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34355 raw34355Labels permutation520 hz
    mixedMoment B raw34355step0 raw34355step0Labels = mixedMoment B raw34355step1 raw34355step1Labels := by
      have ha : raw34355step1 = (fun i j => raw34355step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34355step1 raw34355step0; decide +kernel
      have hl : raw34355step1Labels = raw34355step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34355step0 raw34355step0Labels permutation32 permutation7
    mixedMoment B raw34355step1 raw34355step1Labels = mixedMoment B raw34355step2 raw34355step2Labels := by
      have ha : raw34355step2 = -raw34355step1 := by apply Matrix.ext; change ∀ i j, raw34355step2 i j = -(raw34355step1 i j); unfold raw34355step2 raw34355step1; decide +kernel
      have hl : raw34355step2Labels = raw34355step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34355step2 raw34355step2Labels = mixedMoment B raw34355step3 raw34355step3Labels := by
      have ha : raw34355step3 = raw34355step2 := by apply Matrix.ext; unfold raw34355step3 raw34355step2; decide +kernel
      have hl : raw34355step2Labels = labelEmbedding1 ∘ raw34355step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34355step2 raw34355step2Labels raw34355step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical34356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34356 raw34356Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw34356 raw34356Labels = mixedMoment B raw34356step0 raw34356step0Labels := by
      have ha : raw34356step0 = (fun i j => raw34356 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34356step0 raw34356; decide +kernel
      have hl : raw34356step0Labels = raw34356Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34356 raw34356Labels permutation152 permutation7
    mixedMoment B raw34356step0 raw34356step0Labels = mixedMoment B raw34356step1 raw34356step1Labels := by
      have ha : raw34356step1 = -raw34356step0 := by apply Matrix.ext; change ∀ i j, raw34356step1 i j = -(raw34356step0 i j); unfold raw34356step1 raw34356step0; decide +kernel
      have hl : raw34356step1Labels = raw34356step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34356step1 raw34356step1Labels = mixedMoment B raw34356step2 raw34356step2Labels := by
      have ha : raw34356step2 = raw34356step1 := by apply Matrix.ext; unfold raw34356step2 raw34356step1; decide +kernel
      have hl : raw34356step1Labels = labelEmbedding1 ∘ raw34356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34356step1 raw34356step1Labels raw34356step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2187 node2187Labels := by rfl

theorem canonical34357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34357 raw34357Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw34357 raw34357Labels = mixedMoment B raw34357step0 raw34357step0Labels := by
      have hz : ∀ j, raw34357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34357step0 = (fun i j => raw34357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34357step0 raw34357; decide +kernel
      have hl : raw34357step0Labels = raw34357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34357 raw34357Labels permutation346 hz
    mixedMoment B raw34357step0 raw34357step0Labels = mixedMoment B raw34357step1 raw34357step1Labels := by
      have ha : raw34357step1 = (fun i j => raw34357step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34357step1 raw34357step0; decide +kernel
      have hl : raw34357step1Labels = raw34357step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34357step0 raw34357step0Labels permutation34 permutation7
    mixedMoment B raw34357step1 raw34357step1Labels = mixedMoment B raw34357step2 raw34357step2Labels := by
      have ha : raw34357step2 = -raw34357step1 := by apply Matrix.ext; change ∀ i j, raw34357step2 i j = -(raw34357step1 i j); unfold raw34357step2 raw34357step1; decide +kernel
      have hl : raw34357step2Labels = raw34357step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34357step2 raw34357step2Labels = mixedMoment B raw34357step3 raw34357step3Labels := by
      have ha : raw34357step3 = raw34357step2 := by apply Matrix.ext; unfold raw34357step3 raw34357step2; decide +kernel
      have hl : raw34357step2Labels = labelEmbedding1 ∘ raw34357step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34357step2 raw34357step2Labels raw34357step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2146 node2146Labels := by rfl

theorem canonical34358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34358 raw34358Labels = mixedMoment B node2171 node2171Labels := by
  calc
    mixedMoment B raw34358 raw34358Labels = mixedMoment B raw34358step0 raw34358step0Labels := by
      have ha : raw34358step0 = (fun i j => raw34358 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34358step0 raw34358; decide +kernel
      have hl : raw34358step0Labels = raw34358Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34358 raw34358Labels permutation154 permutation7
    mixedMoment B raw34358step0 raw34358step0Labels = mixedMoment B raw34358step1 raw34358step1Labels := by
      have ha : raw34358step1 = -raw34358step0 := by apply Matrix.ext; change ∀ i j, raw34358step1 i j = -(raw34358step0 i j); unfold raw34358step1 raw34358step0; decide +kernel
      have hl : raw34358step1Labels = raw34358step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34358step1 raw34358step1Labels = mixedMoment B raw34358step2 raw34358step2Labels := by
      have ha : raw34358step2 = raw34358step1 := by apply Matrix.ext; unfold raw34358step2 raw34358step1; decide +kernel
      have hl : raw34358step1Labels = labelEmbedding1 ∘ raw34358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34358step1 raw34358step1Labels raw34358step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2171 node2171Labels := by rfl

theorem canonical34359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34359 raw34359Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw34359 raw34359Labels = mixedMoment B raw34359step0 raw34359step0Labels := by
      have hz : ∀ j, raw34359 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34359step0 = (fun i j => raw34359 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34359step0 raw34359; decide +kernel
      have hl : raw34359step0Labels = raw34359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34359 raw34359Labels permutation520 hz
    mixedMoment B raw34359step0 raw34359step0Labels = mixedMoment B raw34359step1 raw34359step1Labels := by
      have hz : ∀ j, raw34359step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34359step1 = (fun i j => raw34359step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34359step1 raw34359step0; decide +kernel
      have hl : raw34359step1Labels = raw34359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34359step0 raw34359step0Labels permutation80 hz
    mixedMoment B raw34359step1 raw34359step1Labels = mixedMoment B raw34359step2 raw34359step2Labels := by
      have ha : raw34359step2 = (fun i j => raw34359step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34359step2 raw34359step1; decide +kernel
      have hl : raw34359step2Labels = raw34359step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34359step1 raw34359step1Labels permutation8 permutation7
    mixedMoment B raw34359step2 raw34359step2Labels = mixedMoment B raw34359step3 raw34359step3Labels := by
      have ha : raw34359step3 = -raw34359step2 := by apply Matrix.ext; change ∀ i j, raw34359step3 i j = -(raw34359step2 i j); unfold raw34359step3 raw34359step2; decide +kernel
      have hl : raw34359step3Labels = raw34359step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34359step3 raw34359step3Labels = mixedMoment B raw34359step4 raw34359step4Labels := by
      have ha : raw34359step4 = raw34359step3 := by apply Matrix.ext; unfold raw34359step4 raw34359step3; decide +kernel
      have hl : raw34359step3Labels = labelEmbedding1 ∘ raw34359step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34359step3 raw34359step3Labels raw34359step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical34360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34360 raw34360Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw34360 raw34360Labels = mixedMoment B raw34360step0 raw34360step0Labels := by
      have hz : ∀ j, raw34360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34360step0 = (fun i j => raw34360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34360step0 raw34360; decide +kernel
      have hl : raw34360step0Labels = raw34360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34360 raw34360Labels permutation346 hz
    mixedMoment B raw34360step0 raw34360step0Labels = mixedMoment B raw34360step1 raw34360step1Labels := by
      have ha : raw34360step1 = (fun i j => raw34360step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34360step1 raw34360step0; decide +kernel
      have hl : raw34360step1Labels = raw34360step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34360step0 raw34360step0Labels permutation34 permutation7
    mixedMoment B raw34360step1 raw34360step1Labels = mixedMoment B raw34360step2 raw34360step2Labels := by
      have ha : raw34360step2 = -raw34360step1 := by apply Matrix.ext; change ∀ i j, raw34360step2 i j = -(raw34360step1 i j); unfold raw34360step2 raw34360step1; decide +kernel
      have hl : raw34360step2Labels = raw34360step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34360step2 raw34360step2Labels = mixedMoment B raw34360step3 raw34360step3Labels := by
      have ha : raw34360step3 = raw34360step2 := by apply Matrix.ext; unfold raw34360step3 raw34360step2; decide +kernel
      have hl : raw34360step2Labels = labelEmbedding1 ∘ raw34360step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34360step2 raw34360step2Labels raw34360step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

theorem canonical34361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34361 raw34361Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw34361 raw34361Labels = mixedMoment B raw34361step0 raw34361step0Labels := by
      have hz : ∀ j, raw34361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34361step0 = (fun i j => raw34361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34361step0 raw34361; decide +kernel
      have hl : raw34361step0Labels = raw34361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34361 raw34361Labels permutation346 hz
    mixedMoment B raw34361step0 raw34361step0Labels = mixedMoment B raw34361step1 raw34361step1Labels := by
      have ha : raw34361step1 = (fun i j => raw34361step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34361step1 raw34361step0; decide +kernel
      have hl : raw34361step1Labels = raw34361step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34361step0 raw34361step0Labels permutation32 permutation7
    mixedMoment B raw34361step1 raw34361step1Labels = mixedMoment B raw34361step2 raw34361step2Labels := by
      have ha : raw34361step2 = -raw34361step1 := by apply Matrix.ext; change ∀ i j, raw34361step2 i j = -(raw34361step1 i j); unfold raw34361step2 raw34361step1; decide +kernel
      have hl : raw34361step2Labels = raw34361step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34361step2 raw34361step2Labels = mixedMoment B raw34361step3 raw34361step3Labels := by
      have ha : raw34361step3 = raw34361step2 := by apply Matrix.ext; unfold raw34361step3 raw34361step2; decide +kernel
      have hl : raw34361step2Labels = labelEmbedding1 ∘ raw34361step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34361step2 raw34361step2Labels raw34361step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2146 node2146Labels := by rfl

theorem canonical34362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34362 raw34362Labels = mixedMoment B node2171 node2171Labels := by
  calc
    mixedMoment B raw34362 raw34362Labels = mixedMoment B raw34362step0 raw34362step0Labels := by
      have ha : raw34362step0 = (fun i j => raw34362 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34362step0 raw34362; decide +kernel
      have hl : raw34362step0Labels = raw34362Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34362 raw34362Labels permutation152 permutation7
    mixedMoment B raw34362step0 raw34362step0Labels = mixedMoment B raw34362step1 raw34362step1Labels := by
      have ha : raw34362step1 = -raw34362step0 := by apply Matrix.ext; change ∀ i j, raw34362step1 i j = -(raw34362step0 i j); unfold raw34362step1 raw34362step0; decide +kernel
      have hl : raw34362step1Labels = raw34362step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34362step1 raw34362step1Labels = mixedMoment B raw34362step2 raw34362step2Labels := by
      have ha : raw34362step2 = raw34362step1 := by apply Matrix.ext; unfold raw34362step2 raw34362step1; decide +kernel
      have hl : raw34362step1Labels = labelEmbedding1 ∘ raw34362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34362step1 raw34362step1Labels raw34362step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2171 node2171Labels := by rfl

theorem canonical34363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34363 raw34363Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw34363 raw34363Labels = mixedMoment B raw34363step0 raw34363step0Labels := by
      have hz : ∀ j, raw34363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34363step0 = (fun i j => raw34363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34363step0 raw34363; decide +kernel
      have hl : raw34363step0Labels = raw34363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34363 raw34363Labels permutation346 hz
    mixedMoment B raw34363step0 raw34363step0Labels = mixedMoment B raw34363step1 raw34363step1Labels := by
      have ha : raw34363step1 = (fun i j => raw34363step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34363step1 raw34363step0; decide +kernel
      have hl : raw34363step1Labels = raw34363step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34363step0 raw34363step0Labels permutation32 permutation7
    mixedMoment B raw34363step1 raw34363step1Labels = mixedMoment B raw34363step2 raw34363step2Labels := by
      have ha : raw34363step2 = -raw34363step1 := by apply Matrix.ext; change ∀ i j, raw34363step2 i j = -(raw34363step1 i j); unfold raw34363step2 raw34363step1; decide +kernel
      have hl : raw34363step2Labels = raw34363step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34363step2 raw34363step2Labels = mixedMoment B raw34363step3 raw34363step3Labels := by
      have ha : raw34363step3 = raw34363step2 := by apply Matrix.ext; unfold raw34363step3 raw34363step2; decide +kernel
      have hl : raw34363step2Labels = labelEmbedding1 ∘ raw34363step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34363step2 raw34363step2Labels raw34363step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

theorem canonical34364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34364 raw34364Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw34364 raw34364Labels = mixedMoment B raw34364step0 raw34364step0Labels := by
      have hz : ∀ j, raw34364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34364step0 = (fun i j => raw34364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34364step0 raw34364; decide +kernel
      have hl : raw34364step0Labels = raw34364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34364 raw34364Labels permutation346 hz
    _ = mixedMoment B node3389 node3389Labels := by rfl

theorem canonical34365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34365 raw34365Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw34365 raw34365Labels = mixedMoment B raw34365step0 raw34365step0Labels := by
      have hz : ∀ j, raw34365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34365step0 = (fun i j => raw34365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34365step0 raw34365; decide +kernel
      have hl : raw34365step0Labels = raw34365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34365 raw34365Labels permutation346 hz
    _ = mixedMoment B node2052 node2052Labels := by rfl

theorem canonical34366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34366 raw34366Labels = mixedMoment B node1801 node1801Labels := by
  calc
    _ = mixedMoment B node1801 node1801Labels := by rfl

theorem canonical34367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34367 raw34367Labels = mixedMoment B node1809 node1809Labels := by
  calc
    mixedMoment B raw34367 raw34367Labels = mixedMoment B raw34367step0 raw34367step0Labels := by
      have hz : ∀ j, raw34367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34367step0 = (fun i j => raw34367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34367step0 raw34367; decide +kernel
      have hl : raw34367step0Labels = raw34367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34367 raw34367Labels permutation346 hz
    mixedMoment B raw34367step0 raw34367step0Labels = mixedMoment B raw34367step1 raw34367step1Labels := by
      have ha : raw34367step1 = (fun i j => raw34367step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34367step1 raw34367step0; decide +kernel
      have hl : raw34367step1Labels = raw34367step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34367step0 raw34367step0Labels permutation34 permutation2
    _ = mixedMoment B node1809 node1809Labels := by rfl

theorem canonical34368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34368 raw34368Labels = mixedMoment B node1809 node1809Labels := by
  calc
    mixedMoment B raw34368 raw34368Labels = mixedMoment B raw34368step0 raw34368step0Labels := by
      have hz : ∀ j, raw34368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34368step0 = (fun i j => raw34368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34368step0 raw34368; decide +kernel
      have hl : raw34368step0Labels = raw34368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34368 raw34368Labels permutation346 hz
    _ = mixedMoment B node1809 node1809Labels := by rfl

theorem canonical34369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34369 raw34369Labels = mixedMoment B node918 node918Labels := by
  calc
    _ = mixedMoment B node918 node918Labels := by rfl

theorem canonical34370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34370 raw34370Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw34370 raw34370Labels = mixedMoment B raw34370step0 raw34370step0Labels := by
      have hz : ∀ j, raw34370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34370step0 = (fun i j => raw34370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34370step0 raw34370; decide +kernel
      have hl : raw34370step0Labels = raw34370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34370 raw34370Labels permutation434 hz
    _ = mixedMoment B node2052 node2052Labels := by rfl

theorem canonical34371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34371 raw34371Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw34371 raw34371Labels = mixedMoment B raw34371step0 raw34371step0Labels := by
      have hz : ∀ j, raw34371 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34371step0 = (fun i j => raw34371 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34371step0 raw34371; decide +kernel
      have hl : raw34371step0Labels = raw34371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34371 raw34371Labels permutation520 hz
    _ = mixedMoment B node2052 node2052Labels := by rfl

theorem canonical34372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34372 raw34372Labels = mixedMoment B node2050 node2050Labels := by
  calc
    _ = mixedMoment B node2050 node2050Labels := by rfl

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

theorem canonical34406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34406 raw34406Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34406 raw34406Labels = mixedMoment B raw34406step0 raw34406step0Labels := by
      have hz : ∀ j, raw34406 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34406step0 = (fun i j => raw34406 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34406step0 raw34406; decide +kernel
      have hl : raw34406step0Labels = raw34406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34406 raw34406Labels permutation520 hz
    mixedMoment B raw34406step0 raw34406step0Labels = mixedMoment B raw34406step1 raw34406step1Labels := by
      have hz : ∀ i, raw34406step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34406step1 = (fun i j => raw34406step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34406step1 raw34406step0; decide +kernel
      have hl : raw34406step1Labels = (fun j => raw34406step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34406step0 raw34406step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

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

theorem canonical34409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34409 raw34409Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw34409 raw34409Labels = mixedMoment B raw34409step0 raw34409step0Labels := by
      have hz : ∀ j, raw34409 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34409step0 = (fun i j => raw34409 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34409step0 raw34409; decide +kernel
      have hl : raw34409step0Labels = raw34409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34409 raw34409Labels permutation520 hz
    mixedMoment B raw34409step0 raw34409step0Labels = mixedMoment B raw34409step1 raw34409step1Labels := by
      have hz : ∀ j, raw34409step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34409step1 = (fun i j => raw34409step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34409step1 raw34409step0; decide +kernel
      have hl : raw34409step1Labels = raw34409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34409step0 raw34409step0Labels permutation80 hz
    mixedMoment B raw34409step1 raw34409step1Labels = mixedMoment B raw34409step2 raw34409step2Labels := by
      have hz : ∀ i, raw34409step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34409step2 = (fun i j => raw34409step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34409step2 raw34409step1; decide +kernel
      have hl : raw34409step2Labels = (fun j => raw34409step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34409step1 raw34409step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical34410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34410 raw34410Labels = mixedMoment B node3390 node3390Labels := by
  calc
    mixedMoment B raw34410 raw34410Labels = mixedMoment B raw34410step0 raw34410step0Labels := by
      have ha : raw34410step0 = (fun i j => raw34410 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34410step0 raw34410; decide +kernel
      have hl : raw34410step0Labels = raw34410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34410 raw34410Labels permutation283 permutation2
    _ = mixedMoment B node3390 node3390Labels := by rfl

theorem canonical34411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34411 raw34411Labels = mixedMoment B node3155 node3155Labels := by
  calc
    mixedMoment B raw34411 raw34411Labels = mixedMoment B raw34411step0 raw34411step0Labels := by
      have ha : raw34411step0 = (fun i j => raw34411 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34411step0 raw34411; decide +kernel
      have hl : raw34411step0Labels = raw34411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34411 raw34411Labels permutation170 permutation2
    _ = mixedMoment B node3155 node3155Labels := by rfl

theorem canonical34412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34412 raw34412Labels = mixedMoment B node3128 node3128Labels := by
  calc
    mixedMoment B raw34412 raw34412Labels = mixedMoment B raw34412step0 raw34412step0Labels := by
      have ha : raw34412step0 = (fun i j => raw34412 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34412step0 raw34412; decide +kernel
      have hl : raw34412step0Labels = raw34412Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34412 raw34412Labels permutation173 permutation2
    _ = mixedMoment B node3128 node3128Labels := by rfl

theorem canonical34413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34413 raw34413Labels = mixedMoment B node3128 node3128Labels := by
  calc
    mixedMoment B raw34413 raw34413Labels = mixedMoment B raw34413step0 raw34413step0Labels := by
      have ha : raw34413step0 = (fun i j => raw34413 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34413step0 raw34413; decide +kernel
      have hl : raw34413step0Labels = raw34413Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34413 raw34413Labels permutation171 permutation2
    _ = mixedMoment B node3128 node3128Labels := by rfl

theorem canonical34414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34414 raw34414Labels = mixedMoment B node3128 node3128Labels := by
  calc
    mixedMoment B raw34414 raw34414Labels = mixedMoment B raw34414step0 raw34414step0Labels := by
      have ha : raw34414step0 = (fun i j => raw34414 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34414step0 raw34414; decide +kernel
      have hl : raw34414step0Labels = raw34414Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34414 raw34414Labels permutation170 permutation2
    _ = mixedMoment B node3128 node3128Labels := by rfl

theorem canonical34415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34415 raw34415Labels = mixedMoment B node3130 node3130Labels := by
  calc
    _ = mixedMoment B node3130 node3130Labels := by rfl

theorem canonical34416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34416 raw34416Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw34416 raw34416Labels = mixedMoment B raw34416step0 raw34416step0Labels := by
      have hz : ∀ j, raw34416 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34416step0 = (fun i j => raw34416 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34416step0 raw34416; decide +kernel
      have hl : raw34416step0Labels = raw34416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34416 raw34416Labels permutation590 hz
    mixedMoment B raw34416step0 raw34416step0Labels = mixedMoment B raw34416step1 raw34416step1Labels := by
      have hz : ∀ j, raw34416step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw34416step1 = (fun i j => raw34416step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw34416step1 raw34416step0; decide +kernel
      have hl : raw34416step1Labels = raw34416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34416step0 raw34416step0Labels permutation32 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

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

theorem canonical5206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5206 raw5206Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5206 raw5206Labels = mixedMoment B raw5206step0 raw5206step0Labels := by
      have hz : ∀ j, raw5206 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5206step0 = (fun i j => raw5206 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5206step0 raw5206; decide +kernel
      have hl : raw5206step0Labels = raw5206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5206 raw5206Labels permutation520 hz
    mixedMoment B raw5206step0 raw5206step0Labels = mixedMoment B raw5206step1 raw5206step1Labels := by
      have hz : ∀ j, raw5206step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5206step1 = (fun i j => raw5206step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5206step1 raw5206step0; decide +kernel
      have hl : raw5206step1Labels = raw5206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5206step0 raw5206step0Labels permutation80 hz
    mixedMoment B raw5206step1 raw5206step1Labels = mixedMoment B raw5206step2 raw5206step2Labels := by
      have hz : ∀ i, raw5206step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5206step2 = (fun i j => raw5206step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5206step2 raw5206step1; decide +kernel
      have hl : raw5206step2Labels = (fun j => raw5206step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5206step1 raw5206step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5210 raw5210Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5210 raw5210Labels = mixedMoment B raw5210step0 raw5210step0Labels := by
      have hz : ∀ j, raw5210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5210step0 = (fun i j => raw5210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5210step0 raw5210; decide +kernel
      have hl : raw5210step0Labels = raw5210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5210 raw5210Labels permutation434 hz
    mixedMoment B raw5210step0 raw5210step0Labels = mixedMoment B raw5210step1 raw5210step1Labels := by
      have hz : ∀ j, raw5210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5210step1 = (fun i j => raw5210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5210step1 raw5210step0; decide +kernel
      have hl : raw5210step1Labels = raw5210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5210step0 raw5210step0Labels permutation80 hz
    mixedMoment B raw5210step1 raw5210step1Labels = mixedMoment B raw5210step2 raw5210step2Labels := by
      have hz : ∀ i, raw5210step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5210step2 = (fun i j => raw5210step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5210step2 raw5210step1; decide +kernel
      have hl : raw5210step2Labels = (fun j => raw5210step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5210step1 raw5210step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

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

theorem canonical11535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11535 raw11535Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11535 raw11535Labels = mixedMoment B raw11535step0 raw11535step0Labels := by
      have hz : ∀ j, raw11535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11535step0 = (fun i j => raw11535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11535step0 raw11535; decide +kernel
      have hl : raw11535step0Labels = raw11535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11535 raw11535Labels permutation434 hz
    mixedMoment B raw11535step0 raw11535step0Labels = mixedMoment B raw11535step1 raw11535step1Labels := by
      have hz : ∀ i, raw11535step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11535step1 = (fun i j => raw11535step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11535step1 raw11535step0; decide +kernel
      have hl : raw11535step1Labels = (fun j => raw11535step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11535step0 raw11535step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical11537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11537 raw11537Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11537 raw11537Labels = mixedMoment B raw11537step0 raw11537step0Labels := by
      have hz : ∀ j, raw11537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11537step0 = (fun i j => raw11537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11537step0 raw11537; decide +kernel
      have hl : raw11537step0Labels = raw11537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11537 raw11537Labels permutation346 hz
    mixedMoment B raw11537step0 raw11537step0Labels = mixedMoment B raw11537step1 raw11537step1Labels := by
      have hz : ∀ j, raw11537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11537step1 = (fun i j => raw11537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11537step1 raw11537step0; decide +kernel
      have hl : raw11537step1Labels = raw11537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11537step0 raw11537step0Labels permutation56 hz
    mixedMoment B raw11537step1 raw11537step1Labels = mixedMoment B raw11537step2 raw11537step2Labels := by
      have hz : ∀ i, raw11537step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11537step2 = (fun i j => raw11537step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11537step2 raw11537step1; decide +kernel
      have hl : raw11537step2Labels = (fun j => raw11537step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11537step1 raw11537step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

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

theorem canonical11541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11541 raw11541Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw11541 raw11541Labels = mixedMoment B raw11541step0 raw11541step0Labels := by
      have hz : ∀ j, raw11541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11541step0 = (fun i j => raw11541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11541step0 raw11541; decide +kernel
      have hl : raw11541step0Labels = raw11541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11541 raw11541Labels permutation434 hz
    mixedMoment B raw11541step0 raw11541step0Labels = mixedMoment B raw11541step1 raw11541step1Labels := by
      have hz : ∀ j, raw11541step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11541step1 = (fun i j => raw11541step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11541step1 raw11541step0; decide +kernel
      have hl : raw11541step1Labels = raw11541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11541step0 raw11541step0Labels permutation80 hz
    mixedMoment B raw11541step1 raw11541step1Labels = mixedMoment B raw11541step2 raw11541step2Labels := by
      have hz : ∀ i, raw11541step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11541step2 = (fun i j => raw11541step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11541step2 raw11541step1; decide +kernel
      have hl : raw11541step2Labels = (fun j => raw11541step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11541step1 raw11541step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1662 node1662Labels = 0 := by
  exact mixedMoment_alpha B hF node1662 node1662Labels 1 permutation484
    (by decide +kernel)

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

theorem sound1662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1662 node1662Labels = Sparse.eval nodeValue1662 (mixedVector B) := by
  simpa only [nodeValue1662, Sparse.eval_nil] using zero1662 B _hB _hF

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

theorem zero1665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1665 node1665Labels = 0 := by
  exact mixedMoment_alpha B hF node1665 node1665Labels 1 permutation484
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

theorem sound1665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1665 node1665Labels = Sparse.eval nodeValue1665 (mixedVector B) := by
  simpa only [nodeValue1665, Sparse.eval_nil] using zero1665 B _hB _hF

theorem sound1666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1666 node1666Labels = Sparse.eval nodeValue1666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1666) = mixedMoment B node1666 node1666Labels := rfl
  simpa [nodeValue1666, Sparse.eval] using hc.symm

theorem sound1669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1669 node1669Labels = Sparse.eval nodeValue1669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1669) = mixedMoment B node1669 node1669Labels := rfl
  simpa [nodeValue1669, Sparse.eval] using hc.symm

theorem sound1675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1675 node1675Labels = Sparse.eval nodeValue1675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1675) = mixedMoment B node1675 node1675Labels := rfl
  simpa [nodeValue1675, Sparse.eval] using hc.symm

theorem sound1676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1676 node1676Labels = Sparse.eval nodeValue1676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1676) = mixedMoment B node1676 node1676Labels := rfl
  simpa [nodeValue1676, Sparse.eval] using hc.symm

theorem sound1682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1682 node1682Labels = Sparse.eval nodeValue1682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1682) = mixedMoment B node1682 node1682Labels := rfl
  simpa [nodeValue1682, Sparse.eval] using hc.symm

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

theorem sound1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1728 node1728Labels = Sparse.eval nodeValue1728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1728) = mixedMoment B node1728 node1728Labels := rfl
  simpa [nodeValue1728, Sparse.eval] using hc.symm

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

theorem sound1801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1801 node1801Labels = Sparse.eval nodeValue1801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1801) = mixedMoment B node1801 node1801Labels := rfl
  simpa [nodeValue1801, Sparse.eval] using hc.symm

theorem sound1803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1803 node1803Labels = Sparse.eval nodeValue1803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1803) = mixedMoment B node1803 node1803Labels := rfl
  simpa [nodeValue1803, Sparse.eval] using hc.symm

theorem sound1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1804 node1804Labels = Sparse.eval nodeValue1804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1804) = mixedMoment B node1804 node1804Labels := rfl
  simpa [nodeValue1804, Sparse.eval] using hc.symm

theorem sound1808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1808 node1808Labels = Sparse.eval nodeValue1808 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1808) = mixedMoment B node1808 node1808Labels := rfl
  simpa [nodeValue1808, Sparse.eval] using hc.symm

theorem sound1809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1809 node1809Labels = Sparse.eval nodeValue1809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1809) = mixedMoment B node1809 node1809Labels := rfl
  simpa [nodeValue1809, Sparse.eval] using hc.symm

theorem sound1810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1810 node1810Labels = Sparse.eval nodeValue1810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1810) = mixedMoment B node1810 node1810Labels := rfl
  simpa [nodeValue1810, Sparse.eval] using hc.symm

theorem sound1816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1816 node1816Labels = Sparse.eval nodeValue1816 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1816) = mixedMoment B node1816 node1816Labels := rfl
  simpa [nodeValue1816, Sparse.eval] using hc.symm

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

theorem sound2050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2050 node2050Labels = Sparse.eval nodeValue2050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2050) = mixedMoment B node2050 node2050Labels := rfl
  simpa [nodeValue2050, Sparse.eval] using hc.symm

theorem sound2052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2052 node2052Labels = Sparse.eval nodeValue2052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2052) = mixedMoment B node2052 node2052Labels := rfl
  simpa [nodeValue2052, Sparse.eval] using hc.symm

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

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

theorem sound2143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2143 node2143Labels = Sparse.eval nodeValue2143 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2143) = mixedMoment B node2143 node2143Labels := rfl
  simpa [nodeValue2143, Sparse.eval] using hc.symm

theorem sound2146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2146 node2146Labels = Sparse.eval nodeValue2146 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2146) = mixedMoment B node2146 node2146Labels := rfl
  simpa [nodeValue2146, Sparse.eval] using hc.symm

theorem sound2152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2152 node2152Labels = Sparse.eval nodeValue2152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2152) = mixedMoment B node2152 node2152Labels := rfl
  simpa [nodeValue2152, Sparse.eval] using hc.symm

theorem sound2153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2153 node2153Labels = Sparse.eval nodeValue2153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2153) = mixedMoment B node2153 node2153Labels := rfl
  simpa [nodeValue2153, Sparse.eval] using hc.symm

theorem sound2158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2158 node2158Labels = Sparse.eval nodeValue2158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2158) = mixedMoment B node2158 node2158Labels := rfl
  simpa [nodeValue2158, Sparse.eval] using hc.symm

theorem sound2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2170 node2170Labels = Sparse.eval nodeValue2170 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2170) = mixedMoment B node2170 node2170Labels := rfl
  simpa [nodeValue2170, Sparse.eval] using hc.symm

theorem sound2171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2171 node2171Labels = Sparse.eval nodeValue2171 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2171) = mixedMoment B node2171 node2171Labels := rfl
  simpa [nodeValue2171, Sparse.eval] using hc.symm

theorem sound2174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2174 node2174Labels = Sparse.eval nodeValue2174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2174) = mixedMoment B node2174 node2174Labels := rfl
  simpa [nodeValue2174, Sparse.eval] using hc.symm

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

theorem zero2205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = 0 := by
  exact mixedMoment_order_one B hB node2205 node2205Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2208 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2208 node2208Labels = 0 := by
  exact mixedMoment_order_one B hB node2208 node2208Labels 1
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

theorem sound2178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2178 node2178Labels = Sparse.eval nodeValue2178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2178) = mixedMoment B node2178 node2178Labels := rfl
  simpa [nodeValue2178, Sparse.eval] using hc.symm

theorem sound2187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2187 node2187Labels = Sparse.eval nodeValue2187 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2187) = mixedMoment B node2187 node2187Labels := rfl
  simpa [nodeValue2187, Sparse.eval] using hc.symm

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

theorem sound2192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2192 node2192Labels = Sparse.eval nodeValue2192 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2192) = mixedMoment B node2192 node2192Labels := rfl
  simpa [nodeValue2192, Sparse.eval] using hc.symm

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

theorem sound2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = Sparse.eval nodeValue2205 (mixedVector B) := by
  simpa only [nodeValue2205, Sparse.eval_nil] using zero2205 B _hB _hF

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

theorem sound2208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2208 node2208Labels = Sparse.eval nodeValue2208 (mixedVector B) := by
  simpa only [nodeValue2208, Sparse.eval_nil] using zero2208 B _hB _hF

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

theorem sound2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2218 node2218Labels = Sparse.eval nodeValue2218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2218) = mixedMoment B node2218 node2218Labels := rfl
  simpa [nodeValue2218, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = 0 := by
  exact mixedMoment_order_one B hB node2265 node2265Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2268 node2268Labels = 0 := by
  exact mixedMoment_order_one B hB node2268 node2268Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = 0 := by
  exact mixedMoment_order_one B hB node2293 node2293Labels 1
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

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = Sparse.eval nodeValue2265 (mixedVector B) := by
  simpa only [nodeValue2265, Sparse.eval_nil] using zero2265 B _hB _hF

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2268 node2268Labels = Sparse.eval nodeValue2268 (mixedVector B) := by
  simpa only [nodeValue2268, Sparse.eval_nil] using zero2268 B _hB _hF

theorem sound2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = Sparse.eval nodeValue2293 (mixedVector B) := by
  simpa only [nodeValue2293, Sparse.eval_nil] using zero2293 B _hB _hF

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

theorem sound2673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2673 node2673Labels = Sparse.eval nodeValue2673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2673) = mixedMoment B node2673 node2673Labels := rfl
  simpa [nodeValue2673, Sparse.eval] using hc.symm

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

theorem zero2691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2691 node2691Labels = 0 := by
  exact mixedMoment_alpha B hF node2691 node2691Labels 1 permutation212
    (by decide +kernel)

theorem zero2695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2695 node2695Labels = 0 := by
  exact mixedMoment_alpha B hF node2695 node2695Labels 1 permutation212
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

theorem sound2691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2691 node2691Labels = Sparse.eval nodeValue2691 (mixedVector B) := by
  simpa only [nodeValue2691, Sparse.eval_nil] using zero2691 B _hB _hF

theorem sound2695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2695 node2695Labels = Sparse.eval nodeValue2695 (mixedVector B) := by
  simpa only [nodeValue2695, Sparse.eval_nil] using zero2695 B _hB _hF

theorem sound2712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2712 node2712Labels = Sparse.eval nodeValue2712 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2712) = mixedMoment B node2712 node2712Labels := rfl
  simpa [nodeValue2712, Sparse.eval] using hc.symm

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

theorem sound2724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2724 node2724Labels = Sparse.eval nodeValue2724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2724) = mixedMoment B node2724 node2724Labels := rfl
  simpa [nodeValue2724, Sparse.eval] using hc.symm

theorem sound2726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2726 node2726Labels = Sparse.eval nodeValue2726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2726) = mixedMoment B node2726 node2726Labels := rfl
  simpa [nodeValue2726, Sparse.eval] using hc.symm

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3128 node3128Labels = Sparse.eval nodeValue3128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3128) = mixedMoment B node3128 node3128Labels := rfl
  simpa [nodeValue3128, Sparse.eval] using hc.symm

theorem sound3130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3130 node3130Labels = Sparse.eval nodeValue3130 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3130) = mixedMoment B node3130 node3130Labels := rfl
  simpa [nodeValue3130, Sparse.eval] using hc.symm

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

theorem sound3155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3155 node3155Labels = Sparse.eval nodeValue3155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3155) = mixedMoment B node3155 node3155Labels := rfl
  simpa [nodeValue3155, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3389 node3389Labels = Sparse.eval nodeValue3389 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3389) = mixedMoment B node3389 node3389Labels := rfl
  simpa [nodeValue3389, Sparse.eval] using hc.symm

theorem sound3390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3390 node3390Labels = Sparse.eval nodeValue3390 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3390) = mixedMoment B node3390 node3390Labels := rfl
  simpa [nodeValue3390, Sparse.eval] using hc.symm

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

theorem sound4063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4063 node4063Labels = Sparse.eval nodeValue4063 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4063) = mixedMoment B node4063 node4063Labels := rfl
  simpa [nodeValue4063, Sparse.eval] using hc.symm

theorem sound4064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4064 node4064Labels = Sparse.eval nodeValue4064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4064) = mixedMoment B node4064 node4064Labels := rfl
  simpa [nodeValue4064, Sparse.eval] using hc.symm

theorem sound4065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4065 node4065Labels = Sparse.eval nodeValue4065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4065) = mixedMoment B node4065 node4065Labels := rfl
  simpa [nodeValue4065, Sparse.eval] using hc.symm

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

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

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources77
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2483 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2483 + difference 0 1) (sourceB2483 + difference 1 0) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA2483 + difference 0 1) (sourceB2483 + difference 1 0) sourceC2483) = raw34218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34218; decide +kernel
    rw [ha]
    exact (canonical34218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2483 + difference 0 2) (sourceB2483 + difference 2 0) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA2483 + difference 0 2) (sourceB2483 + difference 2 0) sourceC2483) = raw34219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34219; decide +kernel
    rw [ha]
    exact (canonical34219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2483 + difference 0 3) (sourceB2483 + difference 3 0) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA2483 + difference 0 3) (sourceB2483 + difference 3 0) sourceC2483) = raw34220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34220; decide +kernel
    rw [ha]
    exact (canonical34220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2483 + difference 0 4) (sourceB2483 + difference 4 0) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2483 + difference 0 4) (sourceB2483 + difference 4 0) sourceC2483) = raw34221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34221; decide +kernel
    rw [ha]
    exact (canonical34221 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2483 + difference 0 5) (sourceB2483 + difference 5 0) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA2483 + difference 0 5) (sourceB2483 + difference 5 0) sourceC2483) = raw34222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34222; decide +kernel
    rw [ha]
    exact (canonical34222 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2483 + difference 1 0) (sourceB2483 + difference 0 1) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA2483 + difference 1 0) (sourceB2483 + difference 0 1) sourceC2483) = raw34223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34223; decide +kernel
    rw [ha]
    exact (canonical34223 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2483 + difference 1 2) (sourceB2483 + difference 2 1) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2483 + difference 1 2) (sourceB2483 + difference 2 1) sourceC2483) = raw25764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25764; decide +kernel
    rw [ha]
    exact (canonical25764 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2483 + difference 1 3) (sourceB2483 + difference 3 1) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA2483 + difference 1 3) (sourceB2483 + difference 3 1) sourceC2483) = raw25765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25765; decide +kernel
    rw [ha]
    exact (canonical25765 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2483 + difference 1 4) (sourceB2483 + difference 4 1) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA2483 + difference 1 4) (sourceB2483 + difference 4 1) sourceC2483) = raw25766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25766; decide +kernel
    rw [ha]
    exact (canonical25766 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2483 + difference 1 5) (sourceB2483 + difference 5 1) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA2483 + difference 1 5) (sourceB2483 + difference 5 1) sourceC2483) = raw25767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25767; decide +kernel
    rw [ha]
    exact (canonical25767 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2483 + difference 2 0) (sourceB2483 + difference 0 2) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1665) := by
    have ha : (tripleCharges (sourceA2483 + difference 2 0) (sourceB2483 + difference 0 2) sourceC2483) = raw25774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25774; decide +kernel
    rw [ha]
    exact (canonical25774 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2483 + difference 2 1) (sourceB2483 + difference 1 2) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2142) := by
    have ha : (tripleCharges (sourceA2483 + difference 2 1) (sourceB2483 + difference 1 2) sourceC2483) = raw34224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34224; decide +kernel
    rw [ha]
    exact (canonical34224 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2483 + difference 2 3) (sourceB2483 + difference 3 2) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA2483 + difference 2 3) (sourceB2483 + difference 3 2) sourceC2483) = raw34225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34225; decide +kernel
    rw [ha]
    exact (canonical34225 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2483 + difference 2 4) (sourceB2483 + difference 4 2) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2483 + difference 2 4) (sourceB2483 + difference 4 2) sourceC2483) = raw34226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34226; decide +kernel
    rw [ha]
    exact (canonical34226 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2483 + difference 2 5) (sourceB2483 + difference 5 2) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA2483 + difference 2 5) (sourceB2483 + difference 5 2) sourceC2483) = raw34227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34227; decide +kernel
    rw [ha]
    exact (canonical34227 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2483 + difference 3 0) (sourceB2483 + difference 0 3) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA2483 + difference 3 0) (sourceB2483 + difference 0 3) sourceC2483) = raw25779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25779; decide +kernel
    rw [ha]
    exact (canonical25779 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2483 + difference 3 1) (sourceB2483 + difference 1 3) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2483 + difference 3 1) (sourceB2483 + difference 1 3) sourceC2483) = raw34228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34228; decide +kernel
    rw [ha]
    exact (canonical34228 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2483 + difference 3 2) (sourceB2483 + difference 2 3) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2174) := by
    have ha : (tripleCharges (sourceA2483 + difference 3 2) (sourceB2483 + difference 2 3) sourceC2483) = raw34229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34229; decide +kernel
    rw [ha]
    exact (canonical34229 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2483 + difference 3 4) (sourceB2483 + difference 4 3) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2483 + difference 3 4) (sourceB2483 + difference 4 3) sourceC2483) = raw34230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34230; decide +kernel
    rw [ha]
    exact (canonical34230 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2483 + difference 3 5) (sourceB2483 + difference 5 3) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2483 + difference 3 5) (sourceB2483 + difference 5 3) sourceC2483) = raw34231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34231; decide +kernel
    rw [ha]
    exact (canonical34231 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2483 + difference 4 0) (sourceB2483 + difference 0 4) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA2483 + difference 4 0) (sourceB2483 + difference 0 4) sourceC2483) = raw25784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25784; decide +kernel
    rw [ha]
    exact (canonical25784 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2483 + difference 4 1) (sourceB2483 + difference 1 4) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2158) := by
    have ha : (tripleCharges (sourceA2483 + difference 4 1) (sourceB2483 + difference 1 4) sourceC2483) = raw34232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34232; decide +kernel
    rw [ha]
    exact (canonical34232 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2483 + difference 4 2) (sourceB2483 + difference 2 4) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2178) := by
    have ha : (tripleCharges (sourceA2483 + difference 4 2) (sourceB2483 + difference 2 4) sourceC2483) = raw34233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34233; decide +kernel
    rw [ha]
    exact (canonical34233 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2483 + difference 4 3) (sourceB2483 + difference 3 4) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA2483 + difference 4 3) (sourceB2483 + difference 3 4) sourceC2483) = raw34234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34234; decide +kernel
    rw [ha]
    exact (canonical34234 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2483 + difference 4 5) (sourceB2483 + difference 5 4) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA2483 + difference 4 5) (sourceB2483 + difference 5 4) sourceC2483) = raw34235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34235; decide +kernel
    rw [ha]
    exact (canonical34235 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2483 + difference 5 0) (sourceB2483 + difference 0 5) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA2483 + difference 5 0) (sourceB2483 + difference 0 5) sourceC2483) = raw25789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25789; decide +kernel
    rw [ha]
    exact (canonical25789 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2483 + difference 5 1) (sourceB2483 + difference 1 5) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2153) := by
    have ha : (tripleCharges (sourceA2483 + difference 5 1) (sourceB2483 + difference 1 5) sourceC2483) = raw34236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34236; decide +kernel
    rw [ha]
    exact (canonical34236 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2483 + difference 5 2) (sourceB2483 + difference 2 5) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2175) := by
    have ha : (tripleCharges (sourceA2483 + difference 5 2) (sourceB2483 + difference 2 5) sourceC2483) = raw34237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34237; decide +kernel
    rw [ha]
    exact (canonical34237 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2483 + difference 5 3) (sourceB2483 + difference 3 5) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA2483 + difference 5 3) (sourceB2483 + difference 3 5) sourceC2483) = raw34238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34238; decide +kernel
    rw [ha]
    exact (canonical34238 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2483 + difference 5 4) (sourceB2483 + difference 4 5) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA2483 + difference 5 4) (sourceB2483 + difference 4 5) sourceC2483) = raw34239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34239; decide +kernel
    rw [ha]
    exact (canonical34239 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2483 sourceB2483 sourceC2483
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2483, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2484 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2484 + difference 0 1) (sourceB2484 + difference 1 0) sourceC2484) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA2484 + difference 0 1) (sourceB2484 + difference 1 0) sourceC2484) = raw34240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2484 sourceB2484 sourceC2484 difference raw34240; decide +kernel
    rw [ha]
    exact (canonical34240 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2484 + difference 1 1) (sourceB2484 + difference 1 1) sourceC2484) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA2484 + difference 1 1) (sourceB2484 + difference 1 1) sourceC2484) = raw27348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2484 sourceB2484 sourceC2484 difference raw27348; decide +kernel
    rw [ha]
    exact (canonical27348 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2484 + difference 2 1) (sourceB2484 + difference 1 2) sourceC2484) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1803) := by
    have ha : (tripleCharges (sourceA2484 + difference 2 1) (sourceB2484 + difference 1 2) sourceC2484) = raw34241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2484 sourceB2484 sourceC2484 difference raw34241; decide +kernel
    rw [ha]
    exact (canonical34241 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2484 + difference 3 1) (sourceB2484 + difference 1 3) sourceC2484) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1810) := by
    have ha : (tripleCharges (sourceA2484 + difference 3 1) (sourceB2484 + difference 1 3) sourceC2484) = raw34242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2484 sourceB2484 sourceC2484 difference raw34242; decide +kernel
    rw [ha]
    exact (canonical34242 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2484 + difference 4 1) (sourceB2484 + difference 1 4) sourceC2484) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1816) := by
    have ha : (tripleCharges (sourceA2484 + difference 4 1) (sourceB2484 + difference 1 4) sourceC2484) = raw29305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2484 sourceB2484 sourceC2484 difference raw29305; decide +kernel
    rw [ha]
    exact (canonical29305 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2484 + difference 5 1) (sourceB2484 + difference 1 5) sourceC2484) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1808) := by
    have ha : (tripleCharges (sourceA2484 + difference 5 1) (sourceB2484 + difference 1 5) sourceC2484) = raw27344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2484 sourceB2484 sourceC2484 difference raw27344; decide +kernel
    rw [ha]
    exact (canonical27344 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2484 + sourceB2484) sourceC2484) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2484 + sourceB2484) sourceC2484) = raw20142 := by
      apply Matrix.ext; unfold doubleCharges sourceA2484 sourceB2484 sourceC2484 raw20142; decide +kernel
    rw [ha]
    exact (canonical20142 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2484 sourceB2484 sourceC2484
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2484, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2491 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2491 + difference 0 1) (sourceB2491 + difference 1 0) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA2491 + difference 0 1) (sourceB2491 + difference 1 0) sourceC2491) = raw34350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34350; decide +kernel
    rw [ha]
    exact (canonical34350 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2491 + difference 0 2) (sourceB2491 + difference 2 0) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2691) := by
    have ha : (tripleCharges (sourceA2491 + difference 0 2) (sourceB2491 + difference 2 0) sourceC2491) = raw34351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34351; decide +kernel
    rw [ha]
    exact (canonical34351 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2491 + difference 0 3) (sourceB2491 + difference 3 0) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA2491 + difference 0 3) (sourceB2491 + difference 3 0) sourceC2491) = raw29252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw29252; decide +kernel
    rw [ha]
    exact (canonical29252 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2491 + difference 0 4) (sourceB2491 + difference 4 0) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA2491 + difference 0 4) (sourceB2491 + difference 4 0) sourceC2491) = raw34352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34352; decide +kernel
    rw [ha]
    exact (canonical34352 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2491 + difference 0 5) (sourceB2491 + difference 5 0) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA2491 + difference 0 5) (sourceB2491 + difference 5 0) sourceC2491) = raw34353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34353; decide +kernel
    rw [ha]
    exact (canonical34353 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2491 + difference 1 0) (sourceB2491 + difference 0 1) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA2491 + difference 1 0) (sourceB2491 + difference 0 1) sourceC2491) = raw21868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw21868; decide +kernel
    rw [ha]
    exact (canonical21868 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2491 + difference 1 2) (sourceB2491 + difference 2 1) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2491 + difference 1 2) (sourceB2491 + difference 2 1) sourceC2491) = raw25974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw25974; decide +kernel
    rw [ha]
    exact (canonical25974 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2491 + difference 1 3) (sourceB2491 + difference 3 1) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA2491 + difference 1 3) (sourceB2491 + difference 3 1) sourceC2491) = raw21856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw21856; decide +kernel
    rw [ha]
    exact (canonical21856 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2491 + difference 1 4) (sourceB2491 + difference 4 1) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA2491 + difference 1 4) (sourceB2491 + difference 4 1) sourceC2491) = raw25975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw25975; decide +kernel
    rw [ha]
    exact (canonical25975 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2491 + difference 1 5) (sourceB2491 + difference 5 1) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA2491 + difference 1 5) (sourceB2491 + difference 5 1) sourceC2491) = raw25976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw25976; decide +kernel
    rw [ha]
    exact (canonical25976 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2491 + difference 2 0) (sourceB2491 + difference 0 2) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1662) := by
    have ha : (tripleCharges (sourceA2491 + difference 2 0) (sourceB2491 + difference 0 2) sourceC2491) = raw25982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw25982; decide +kernel
    rw [ha]
    exact (canonical25982 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2491 + difference 2 1) (sourceB2491 + difference 1 2) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2139) := by
    have ha : (tripleCharges (sourceA2491 + difference 2 1) (sourceB2491 + difference 1 2) sourceC2491) = raw34354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34354; decide +kernel
    rw [ha]
    exact (canonical34354 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2491 + difference 2 3) (sourceB2491 + difference 3 2) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2491 + difference 2 3) (sourceB2491 + difference 3 2) sourceC2491) = raw29256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw29256; decide +kernel
    rw [ha]
    exact (canonical29256 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2491 + difference 2 4) (sourceB2491 + difference 4 2) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2491 + difference 2 4) (sourceB2491 + difference 4 2) sourceC2491) = raw34355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34355; decide +kernel
    rw [ha]
    exact (canonical34355 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2491 + difference 2 5) (sourceB2491 + difference 5 2) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2187) := by
    have ha : (tripleCharges (sourceA2491 + difference 2 5) (sourceB2491 + difference 5 2) sourceC2491) = raw34356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34356; decide +kernel
    rw [ha]
    exact (canonical34356 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2491 + difference 3 0) (sourceB2491 + difference 0 3) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA2491 + difference 3 0) (sourceB2491 + difference 0 3) sourceC2491) = raw25986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw25986; decide +kernel
    rw [ha]
    exact (canonical25986 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2491 + difference 3 1) (sourceB2491 + difference 1 3) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2146) := by
    have ha : (tripleCharges (sourceA2491 + difference 3 1) (sourceB2491 + difference 1 3) sourceC2491) = raw34357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34357; decide +kernel
    rw [ha]
    exact (canonical34357 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2491 + difference 3 2) (sourceB2491 + difference 2 3) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2171) := by
    have ha : (tripleCharges (sourceA2491 + difference 3 2) (sourceB2491 + difference 2 3) sourceC2491) = raw34358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34358; decide +kernel
    rw [ha]
    exact (canonical34358 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2491 + difference 3 4) (sourceB2491 + difference 4 3) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2491 + difference 3 4) (sourceB2491 + difference 4 3) sourceC2491) = raw34359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34359; decide +kernel
    rw [ha]
    exact (canonical34359 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2491 + difference 3 5) (sourceB2491 + difference 5 3) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA2491 + difference 3 5) (sourceB2491 + difference 5 3) sourceC2491) = raw34360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34360; decide +kernel
    rw [ha]
    exact (canonical34360 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2491 + difference 4 0) (sourceB2491 + difference 0 4) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA2491 + difference 4 0) (sourceB2491 + difference 0 4) sourceC2491) = raw25991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw25991; decide +kernel
    rw [ha]
    exact (canonical25991 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2491 + difference 4 1) (sourceB2491 + difference 1 4) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2146) := by
    have ha : (tripleCharges (sourceA2491 + difference 4 1) (sourceB2491 + difference 1 4) sourceC2491) = raw34361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34361; decide +kernel
    rw [ha]
    exact (canonical34361 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2491 + difference 4 2) (sourceB2491 + difference 2 4) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2171) := by
    have ha : (tripleCharges (sourceA2491 + difference 4 2) (sourceB2491 + difference 2 4) sourceC2491) = raw34362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34362; decide +kernel
    rw [ha]
    exact (canonical34362 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2491 + difference 4 3) (sourceB2491 + difference 3 4) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2491 + difference 4 3) (sourceB2491 + difference 3 4) sourceC2491) = raw29263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw29263; decide +kernel
    rw [ha]
    exact (canonical29263 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2491 + difference 4 5) (sourceB2491 + difference 5 4) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA2491 + difference 4 5) (sourceB2491 + difference 5 4) sourceC2491) = raw34363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34363; decide +kernel
    rw [ha]
    exact (canonical34363 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2491 + difference 5 0) (sourceB2491 + difference 0 5) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA2491 + difference 5 0) (sourceB2491 + difference 0 5) sourceC2491) = raw21866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw21866; decide +kernel
    rw [ha]
    exact (canonical21866 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2491 + difference 5 1) (sourceB2491 + difference 1 5) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2491 + difference 5 1) (sourceB2491 + difference 1 5) sourceC2491) = raw29257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw29257; decide +kernel
    rw [ha]
    exact (canonical29257 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2491 + difference 5 2) (sourceB2491 + difference 2 5) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2170) := by
    have ha : (tripleCharges (sourceA2491 + difference 5 2) (sourceB2491 + difference 2 5) sourceC2491) = raw29258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw29258; decide +kernel
    rw [ha]
    exact (canonical29258 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2491 + difference 5 3) (sourceB2491 + difference 3 5) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2491 + difference 5 3) (sourceB2491 + difference 3 5) sourceC2491) = raw21853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw21853; decide +kernel
    rw [ha]
    exact (canonical21853 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2491 + difference 5 4) (sourceB2491 + difference 4 5) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2491 + difference 5 4) (sourceB2491 + difference 4 5) sourceC2491) = raw29259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw29259; decide +kernel
    rw [ha]
    exact (canonical29259 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2491 sourceB2491 sourceC2491
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2491, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2492 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2492 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2492 + difference 0 1) (sourceB2492 + difference 1 0) sourceC2492) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA2492 + difference 0 1) (sourceB2492 + difference 1 0) sourceC2492) = raw34364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2492 sourceB2492 sourceC2492 difference raw34364; decide +kernel
    rw [ha]
    exact (canonical34364 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2492 + difference 1 1) (sourceB2492 + difference 1 1) sourceC2492) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA2492 + difference 1 1) (sourceB2492 + difference 1 1) sourceC2492) = raw34365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2492 sourceB2492 sourceC2492 difference raw34365; decide +kernel
    rw [ha]
    exact (canonical34365 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2492 + difference 2 1) (sourceB2492 + difference 1 2) sourceC2492) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1801) := by
    have ha : (tripleCharges (sourceA2492 + difference 2 1) (sourceB2492 + difference 1 2) sourceC2492) = raw34366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2492 sourceB2492 sourceC2492 difference raw34366; decide +kernel
    rw [ha]
    exact (canonical34366 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2492 + difference 3 1) (sourceB2492 + difference 1 3) sourceC2492) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1809) := by
    have ha : (tripleCharges (sourceA2492 + difference 3 1) (sourceB2492 + difference 1 3) sourceC2492) = raw34367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2492 sourceB2492 sourceC2492 difference raw34367; decide +kernel
    rw [ha]
    exact (canonical34367 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2492 + difference 4 1) (sourceB2492 + difference 1 4) sourceC2492) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1809) := by
    have ha : (tripleCharges (sourceA2492 + difference 4 1) (sourceB2492 + difference 1 4) sourceC2492) = raw34368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2492 sourceB2492 sourceC2492 difference raw34368; decide +kernel
    rw [ha]
    exact (canonical34368 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2492 + difference 5 1) (sourceB2492 + difference 1 5) sourceC2492) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1804) := by
    have ha : (tripleCharges (sourceA2492 + difference 5 1) (sourceB2492 + difference 1 5) sourceC2492) = raw29270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2492 sourceB2492 sourceC2492 difference raw29270; decide +kernel
    rw [ha]
    exact (canonical29270 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2492 + sourceB2492) sourceC2492) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA2492 + sourceB2492) sourceC2492) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA2492 sourceB2492 sourceC2492 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2492 sourceB2492 sourceC2492
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2492, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2493 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2493 + difference 2 0) (sourceB2493 + difference 0 2) sourceC2493) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 918) := by
    have ha : (tripleCharges (sourceA2493 + difference 2 0) (sourceB2493 + difference 0 2) sourceC2493) = raw34369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2493 sourceB2493 sourceC2493 difference raw34369; decide +kernel
    rw [ha]
    exact (canonical34369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2493 + difference 2 1) (sourceB2493 + difference 1 2) sourceC2493) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1801) := by
    have ha : (tripleCharges (sourceA2493 + difference 2 1) (sourceB2493 + difference 1 2) sourceC2493) = raw34366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2493 sourceB2493 sourceC2493 difference raw34366; decide +kernel
    rw [ha]
    exact (canonical34366 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2493 + difference 2 2) (sourceB2493 + difference 2 2) sourceC2493) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA2493 + difference 2 2) (sourceB2493 + difference 2 2) sourceC2493) = raw34365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2493 sourceB2493 sourceC2493 difference raw34365; decide +kernel
    rw [ha]
    exact (canonical34365 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2493 + difference 2 3) (sourceB2493 + difference 3 2) sourceC2493) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA2493 + difference 2 3) (sourceB2493 + difference 3 2) sourceC2493) = raw34370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2493 sourceB2493 sourceC2493 difference raw34370; decide +kernel
    rw [ha]
    exact (canonical34370 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2493 + difference 2 4) (sourceB2493 + difference 4 2) sourceC2493) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA2493 + difference 2 4) (sourceB2493 + difference 4 2) sourceC2493) = raw34371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2493 sourceB2493 sourceC2493 difference raw34371; decide +kernel
    rw [ha]
    exact (canonical34371 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2493 + difference 2 5) (sourceB2493 + difference 5 2) sourceC2493) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2050) := by
    have ha : (tripleCharges (sourceA2493 + difference 2 5) (sourceB2493 + difference 5 2) sourceC2493) = raw34372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2493 sourceB2493 sourceC2493 difference raw34372; decide +kernel
    rw [ha]
    exact (canonical34372 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2493 + sourceB2493) sourceC2493) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA2493 + sourceB2493) sourceC2493) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA2493 sourceB2493 sourceC2493 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2493 sourceB2493 sourceC2493
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2493, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources78
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2496 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2496 + difference 0 1) (sourceB2496 + difference 1 0) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2496 + difference 0 1) (sourceB2496 + difference 1 0) sourceC2496) = raw18337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw18337; decide +kernel
    rw [ha]
    exact (canonical18337 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2496 + difference 0 2) (sourceB2496 + difference 2 0) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2496 + difference 0 2) (sourceB2496 + difference 2 0) sourceC2496) = raw18338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw18338; decide +kernel
    rw [ha]
    exact (canonical18338 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2496 + difference 0 3) (sourceB2496 + difference 3 0) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2496 + difference 0 3) (sourceB2496 + difference 3 0) sourceC2496) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2496 + difference 0 4) (sourceB2496 + difference 4 0) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2496 + difference 0 4) (sourceB2496 + difference 4 0) sourceC2496) = raw2925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw2925; decide +kernel
    rw [ha]
    exact (canonical2925 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2496 + difference 0 5) (sourceB2496 + difference 5 0) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2496 + difference 0 5) (sourceB2496 + difference 5 0) sourceC2496) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2496 + difference 1 0) (sourceB2496 + difference 0 1) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA2496 + difference 1 0) (sourceB2496 + difference 0 1) sourceC2496) = raw11537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw11537; decide +kernel
    rw [ha]
    exact (canonical11537 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2496 + difference 1 2) (sourceB2496 + difference 2 1) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2496 + difference 1 2) (sourceB2496 + difference 2 1) sourceC2496) = raw11539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw11539; decide +kernel
    rw [ha]
    exact (canonical11539 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2496 + difference 1 3) (sourceB2496 + difference 3 1) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2496 + difference 1 3) (sourceB2496 + difference 3 1) sourceC2496) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2496 + difference 1 4) (sourceB2496 + difference 4 1) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2496 + difference 1 4) (sourceB2496 + difference 4 1) sourceC2496) = raw2924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw2924; decide +kernel
    rw [ha]
    exact (canonical2924 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2496 + difference 1 5) (sourceB2496 + difference 5 1) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA2496 + difference 1 5) (sourceB2496 + difference 5 1) sourceC2496) = raw3331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw3331; decide +kernel
    rw [ha]
    exact (canonical3331 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2496 + difference 2 0) (sourceB2496 + difference 0 2) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA2496 + difference 2 0) (sourceB2496 + difference 0 2) sourceC2496) = raw26358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw26358; decide +kernel
    rw [ha]
    exact (canonical26358 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2496 + difference 2 1) (sourceB2496 + difference 1 2) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2496 + difference 2 1) (sourceB2496 + difference 1 2) sourceC2496) = raw34405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw34405; decide +kernel
    rw [ha]
    exact (canonical34405 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2496 + difference 2 3) (sourceB2496 + difference 3 2) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2496 + difference 2 3) (sourceB2496 + difference 3 2) sourceC2496) = raw11535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw11535; decide +kernel
    rw [ha]
    exact (canonical11535 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2496 + difference 2 4) (sourceB2496 + difference 4 2) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2496 + difference 2 4) (sourceB2496 + difference 4 2) sourceC2496) = raw34406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw34406; decide +kernel
    rw [ha]
    exact (canonical34406 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2496 + difference 2 5) (sourceB2496 + difference 5 2) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (tripleCharges (sourceA2496 + difference 2 5) (sourceB2496 + difference 5 2) sourceC2496) = raw14365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw14365; decide +kernel
    rw [ha]
    exact (canonical14365 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2496 + difference 3 0) (sourceB2496 + difference 0 3) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA2496 + difference 3 0) (sourceB2496 + difference 0 3) sourceC2496) = raw26361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw26361; decide +kernel
    rw [ha]
    exact (canonical26361 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2496 + difference 3 1) (sourceB2496 + difference 1 3) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2496 + difference 3 1) (sourceB2496 + difference 1 3) sourceC2496) = raw34407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw34407; decide +kernel
    rw [ha]
    exact (canonical34407 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2496 + difference 3 2) (sourceB2496 + difference 2 3) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2496 + difference 3 2) (sourceB2496 + difference 2 3) sourceC2496) = raw34408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw34408; decide +kernel
    rw [ha]
    exact (canonical34408 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2496 + difference 3 4) (sourceB2496 + difference 4 3) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2496 + difference 3 4) (sourceB2496 + difference 4 3) sourceC2496) = raw34409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw34409; decide +kernel
    rw [ha]
    exact (canonical34409 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2496 + difference 3 5) (sourceB2496 + difference 5 3) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2496 + difference 3 5) (sourceB2496 + difference 5 3) sourceC2496) = raw14369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw14369; decide +kernel
    rw [ha]
    exact (canonical14369 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2496 + difference 4 0) (sourceB2496 + difference 0 4) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA2496 + difference 4 0) (sourceB2496 + difference 0 4) sourceC2496) = raw23786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw23786; decide +kernel
    rw [ha]
    exact (canonical23786 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2496 + difference 4 1) (sourceB2496 + difference 1 4) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2496 + difference 4 1) (sourceB2496 + difference 1 4) sourceC2496) = raw31880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw31880; decide +kernel
    rw [ha]
    exact (canonical31880 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2496 + difference 4 2) (sourceB2496 + difference 2 4) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2496 + difference 4 2) (sourceB2496 + difference 2 4) sourceC2496) = raw31881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw31881; decide +kernel
    rw [ha]
    exact (canonical31881 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2496 + difference 4 3) (sourceB2496 + difference 3 4) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2496 + difference 4 3) (sourceB2496 + difference 3 4) sourceC2496) = raw11541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw11541; decide +kernel
    rw [ha]
    exact (canonical11541 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2496 + difference 4 5) (sourceB2496 + difference 5 4) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2496 + difference 4 5) (sourceB2496 + difference 5 4) sourceC2496) = raw14374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw14374; decide +kernel
    rw [ha]
    exact (canonical14374 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2496 + difference 5 0) (sourceB2496 + difference 0 5) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA2496 + difference 5 0) (sourceB2496 + difference 0 5) sourceC2496) = raw22308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw22308; decide +kernel
    rw [ha]
    exact (canonical22308 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2496 + difference 5 1) (sourceB2496 + difference 1 5) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2496 + difference 5 1) (sourceB2496 + difference 1 5) sourceC2496) = raw29297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw29297; decide +kernel
    rw [ha]
    exact (canonical29297 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2496 + difference 5 2) (sourceB2496 + difference 2 5) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4077) := by
    have ha : (tripleCharges (sourceA2496 + difference 5 2) (sourceB2496 + difference 2 5) sourceC2496) = raw29298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw29298; decide +kernel
    rw [ha]
    exact (canonical29298 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2496 + difference 5 3) (sourceB2496 + difference 3 5) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2496 + difference 5 3) (sourceB2496 + difference 3 5) sourceC2496) = raw5210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw5210; decide +kernel
    rw [ha]
    exact (canonical5210 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2496 + difference 5 4) (sourceB2496 + difference 4 5) sourceC2496) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2496 + difference 5 4) (sourceB2496 + difference 4 5) sourceC2496) = raw5206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2496 sourceB2496 sourceC2496 difference raw5206; decide +kernel
    rw [ha]
    exact (canonical5206 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2496 sourceB2496 sourceC2496
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2496, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2497 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2497 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2497 + difference 0 1) (sourceB2497 + difference 1 0) sourceC2497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3390) := by
    have ha : (tripleCharges (sourceA2497 + difference 0 1) (sourceB2497 + difference 1 0) sourceC2497) = raw34410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2497 sourceB2497 sourceC2497 difference raw34410; decide +kernel
    rw [ha]
    exact (canonical34410 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2497 + difference 1 1) (sourceB2497 + difference 1 1) sourceC2497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3155) := by
    have ha : (tripleCharges (sourceA2497 + difference 1 1) (sourceB2497 + difference 1 1) sourceC2497) = raw34411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2497 sourceB2497 sourceC2497 difference raw34411; decide +kernel
    rw [ha]
    exact (canonical34411 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2497 + difference 2 1) (sourceB2497 + difference 1 2) sourceC2497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3128) := by
    have ha : (tripleCharges (sourceA2497 + difference 2 1) (sourceB2497 + difference 1 2) sourceC2497) = raw34412 := by
      apply Matrix.ext; unfold tripleCharges sourceA2497 sourceB2497 sourceC2497 difference raw34412; decide +kernel
    rw [ha]
    exact (canonical34412 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2497 + difference 3 1) (sourceB2497 + difference 1 3) sourceC2497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3128) := by
    have ha : (tripleCharges (sourceA2497 + difference 3 1) (sourceB2497 + difference 1 3) sourceC2497) = raw34413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2497 sourceB2497 sourceC2497 difference raw34413; decide +kernel
    rw [ha]
    exact (canonical34413 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2497 + difference 4 1) (sourceB2497 + difference 1 4) sourceC2497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3128) := by
    have ha : (tripleCharges (sourceA2497 + difference 4 1) (sourceB2497 + difference 1 4) sourceC2497) = raw34414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2497 sourceB2497 sourceC2497 difference raw34414; decide +kernel
    rw [ha]
    exact (canonical34414 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2497 + difference 5 1) (sourceB2497 + difference 1 5) sourceC2497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3130) := by
    have ha : (tripleCharges (sourceA2497 + difference 5 1) (sourceB2497 + difference 1 5) sourceC2497) = raw34415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2497 sourceB2497 sourceC2497 difference raw34415; decide +kernel
    rw [ha]
    exact (canonical34415 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2497 + sourceB2497) sourceC2497) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2497 + sourceB2497) sourceC2497) = raw34416 := by
      apply Matrix.ext; unfold doubleCharges sourceA2497 sourceB2497 sourceC2497 raw34416; decide +kernel
    rw [ha]
    exact (canonical34416 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2497 sourceB2497 sourceC2497
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2497, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2000 : Integer.Sparse.reindex keyMap MixedData.row2000 = numericRow2000 := by decide +kernel

theorem numericCheck2000 (x : Master → ℝ) : Integer.Sparse.eval numericRow2000 x =
    (1 : ℝ) * reducedSource2000 x := by
  norm_num [numericRow2000, reducedSource2000, Integer.Sparse.eval, Sparse.eval, nodeValue1665, nodeValue1675, nodeValue1676, nodeValue1682, nodeValue1728, nodeValue2142, nodeValue2152, nodeValue2153, nodeValue2158, nodeValue2174, nodeValue2175, nodeValue2178, nodeValue2191, nodeValue2192, nodeValue2205, nodeValue2206, nodeValue2207, nodeValue2216, nodeValue2217, nodeValue2229, nodeValue2230, nodeValue2265, nodeValue2266, nodeValue2293, nodeValue2673, nodeValue2695, nodeValue2723, nodeValue2724, nodeValue2743]

theorem reindexCheck2001 : Integer.Sparse.reindex keyMap MixedData.row2001 = numericRow2001 := by decide +kernel

theorem numericCheck2001 (x : Master → ℝ) : Integer.Sparse.eval numericRow2001 x =
    (1 : ℝ) * reducedSource2001 x := by
  norm_num [numericRow2001, reducedSource2001, Integer.Sparse.eval, Sparse.eval, nodeValue1803, nodeValue1808, nodeValue1810, nodeValue1816, nodeValue2054, nodeValue3392, nodeValue4084]

theorem reindexCheck2007 : Integer.Sparse.reindex keyMap MixedData.row2007 = numericRow2007 := by decide +kernel

theorem numericCheck2007 (x : Master → ℝ) : Integer.Sparse.eval numericRow2007 x =
    (1 : ℝ) * reducedSource2007 x := by
  norm_num [numericRow2007, reducedSource2007, Integer.Sparse.eval, Sparse.eval, nodeValue1662, nodeValue1666, nodeValue1669, nodeValue1710, nodeValue2139, nodeValue2143, nodeValue2146, nodeValue2170, nodeValue2171, nodeValue2187, nodeValue2193, nodeValue2197, nodeValue2208, nodeValue2218, nodeValue2247, nodeValue2268, nodeValue2664, nodeValue2691, nodeValue2712, nodeValue2726]

theorem reindexCheck2008 : Integer.Sparse.reindex keyMap MixedData.row2008 = numericRow2008 := by decide +kernel

theorem numericCheck2008 (x : Master → ℝ) : Integer.Sparse.eval numericRow2008 x =
    (1 : ℝ) * reducedSource2008 x := by
  norm_num [numericRow2008, reducedSource2008, Integer.Sparse.eval, Sparse.eval, nodeValue1801, nodeValue1804, nodeValue1809, nodeValue2052, nodeValue3389, nodeValue4085]

theorem reindexCheck2009 : Integer.Sparse.reindex keyMap MixedData.row2009 = numericRow2009 := by decide +kernel

theorem numericCheck2009 (x : Master → ℝ) : Integer.Sparse.eval numericRow2009 x =
    (1 : ℝ) * reducedSource2009 x := by
  norm_num [numericRow2009, reducedSource2009, Integer.Sparse.eval, Sparse.eval, nodeValue918, nodeValue1801, nodeValue2050, nodeValue2052, nodeValue4085]

theorem reindexCheck2012 : Integer.Sparse.reindex keyMap MixedData.row2012 = numericRow2012 := by decide +kernel

theorem numericCheck2012 (x : Master → ℝ) : Integer.Sparse.eval numericRow2012 x =
    (1 : ℝ) * reducedSource2012 x := by
  norm_num [numericRow2012, reducedSource2012, Integer.Sparse.eval, Sparse.eval, nodeValue4063, nodeValue4064, nodeValue4065, nodeValue4069, nodeValue4073, nodeValue4074, nodeValue4075, nodeValue4077, nodeValue4078, nodeValue4079, nodeValue4080, nodeValue4081, nodeValue4082, nodeValue4083, nodeValue4084, nodeValue4088, nodeValue4090, nodeValue4091, nodeValue4092]

theorem reindexCheck2013 : Integer.Sparse.reindex keyMap MixedData.row2013 = numericRow2013 := by decide +kernel

theorem numericCheck2013 (x : Master → ℝ) : Integer.Sparse.eval numericRow2013 x =
    (1 : ℝ) * reducedSource2013 x := by
  norm_num [numericRow2013, reducedSource2013, Integer.Sparse.eval, Sparse.eval, nodeValue3128, nodeValue3130, nodeValue3155, nodeValue3390, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2000 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2000 (mixedVector B) = 0 := by
  have h1665 : mixedVector B (Sum.inr 1665) = Sparse.eval nodeValue1665 (mixedVector B) := by
    change mixedMoment B node1665 node1665Labels = _
    exact sound1665 B hB hF
  have h1675 : mixedVector B (Sum.inr 1675) = Sparse.eval nodeValue1675 (mixedVector B) := by
    change mixedMoment B node1675 node1675Labels = _
    exact sound1675 B hB hF
  have h1676 : mixedVector B (Sum.inr 1676) = Sparse.eval nodeValue1676 (mixedVector B) := by
    change mixedMoment B node1676 node1676Labels = _
    exact sound1676 B hB hF
  have h1682 : mixedVector B (Sum.inr 1682) = Sparse.eval nodeValue1682 (mixedVector B) := by
    change mixedMoment B node1682 node1682Labels = _
    exact sound1682 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h2142 : mixedVector B (Sum.inr 2142) = Sparse.eval nodeValue2142 (mixedVector B) := by
    change mixedMoment B node2142 node2142Labels = _
    exact sound2142 B hB hF
  have h2152 : mixedVector B (Sum.inr 2152) = Sparse.eval nodeValue2152 (mixedVector B) := by
    change mixedMoment B node2152 node2152Labels = _
    exact sound2152 B hB hF
  have h2153 : mixedVector B (Sum.inr 2153) = Sparse.eval nodeValue2153 (mixedVector B) := by
    change mixedMoment B node2153 node2153Labels = _
    exact sound2153 B hB hF
  have h2158 : mixedVector B (Sum.inr 2158) = Sparse.eval nodeValue2158 (mixedVector B) := by
    change mixedMoment B node2158 node2158Labels = _
    exact sound2158 B hB hF
  have h2174 : mixedVector B (Sum.inr 2174) = Sparse.eval nodeValue2174 (mixedVector B) := by
    change mixedMoment B node2174 node2174Labels = _
    exact sound2174 B hB hF
  have h2175 : mixedVector B (Sum.inr 2175) = Sparse.eval nodeValue2175 (mixedVector B) := by
    change mixedMoment B node2175 node2175Labels = _
    exact sound2175 B hB hF
  have h2178 : mixedVector B (Sum.inr 2178) = Sparse.eval nodeValue2178 (mixedVector B) := by
    change mixedMoment B node2178 node2178Labels = _
    exact sound2178 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h2192 : mixedVector B (Sum.inr 2192) = Sparse.eval nodeValue2192 (mixedVector B) := by
    change mixedMoment B node2192 node2192Labels = _
    exact sound2192 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h2673 : mixedVector B (Sum.inr 2673) = Sparse.eval nodeValue2673 (mixedVector B) := by
    change mixedMoment B node2673 node2673Labels = _
    exact sound2673 B hB hF
  have h2695 : mixedVector B (Sum.inr 2695) = Sparse.eval nodeValue2695 (mixedVector B) := by
    change mixedMoment B node2695 node2695Labels = _
    exact sound2695 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  simpa only [sourceForm2483, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1665, h1675, h1676, h1682, h1728, h2142, h2152, h2153, h2158, h2174, h2175, h2178, h2191, h2192, h2205, h2206, h2207, h2216, h2217, h2229, h2230, h2265, h2266, h2293, h2673, h2695, h2723, h2724, h2743, reducedSource2000] using sourceEq2483 B hB

theorem rowSound2000 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2000 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2000, numericCheck2000, reducedZero2000 B hB hF, mul_zero]

theorem reducedZero2001 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2001 (mixedVector B) = 0 := by
  have h1803 : mixedVector B (Sum.inr 1803) = Sparse.eval nodeValue1803 (mixedVector B) := by
    change mixedMoment B node1803 node1803Labels = _
    exact sound1803 B hB hF
  have h1808 : mixedVector B (Sum.inr 1808) = Sparse.eval nodeValue1808 (mixedVector B) := by
    change mixedMoment B node1808 node1808Labels = _
    exact sound1808 B hB hF
  have h1810 : mixedVector B (Sum.inr 1810) = Sparse.eval nodeValue1810 (mixedVector B) := by
    change mixedMoment B node1810 node1810Labels = _
    exact sound1810 B hB hF
  have h1816 : mixedVector B (Sum.inr 1816) = Sparse.eval nodeValue1816 (mixedVector B) := by
    change mixedMoment B node1816 node1816Labels = _
    exact sound1816 B hB hF
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h3392 : mixedVector B (Sum.inr 3392) = Sparse.eval nodeValue3392 (mixedVector B) := by
    change mixedMoment B node3392 node3392Labels = _
    exact sound3392 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2484, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1803, h1808, h1810, h1816, h2054, h3392, h4084, reducedSource2001] using sourceEq2484 B hB

theorem rowSound2001 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2001 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2001, numericCheck2001, reducedZero2001 B hB hF, mul_zero]

theorem reducedZero2007 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2007 (mixedVector B) = 0 := by
  have h1662 : mixedVector B (Sum.inr 1662) = Sparse.eval nodeValue1662 (mixedVector B) := by
    change mixedMoment B node1662 node1662Labels = _
    exact sound1662 B hB hF
  have h1666 : mixedVector B (Sum.inr 1666) = Sparse.eval nodeValue1666 (mixedVector B) := by
    change mixedMoment B node1666 node1666Labels = _
    exact sound1666 B hB hF
  have h1669 : mixedVector B (Sum.inr 1669) = Sparse.eval nodeValue1669 (mixedVector B) := by
    change mixedMoment B node1669 node1669Labels = _
    exact sound1669 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h2139 : mixedVector B (Sum.inr 2139) = Sparse.eval nodeValue2139 (mixedVector B) := by
    change mixedMoment B node2139 node2139Labels = _
    exact sound2139 B hB hF
  have h2143 : mixedVector B (Sum.inr 2143) = Sparse.eval nodeValue2143 (mixedVector B) := by
    change mixedMoment B node2143 node2143Labels = _
    exact sound2143 B hB hF
  have h2146 : mixedVector B (Sum.inr 2146) = Sparse.eval nodeValue2146 (mixedVector B) := by
    change mixedMoment B node2146 node2146Labels = _
    exact sound2146 B hB hF
  have h2170 : mixedVector B (Sum.inr 2170) = Sparse.eval nodeValue2170 (mixedVector B) := by
    change mixedMoment B node2170 node2170Labels = _
    exact sound2170 B hB hF
  have h2171 : mixedVector B (Sum.inr 2171) = Sparse.eval nodeValue2171 (mixedVector B) := by
    change mixedMoment B node2171 node2171Labels = _
    exact sound2171 B hB hF
  have h2187 : mixedVector B (Sum.inr 2187) = Sparse.eval nodeValue2187 (mixedVector B) := by
    change mixedMoment B node2187 node2187Labels = _
    exact sound2187 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2197 : mixedVector B (Sum.inr 2197) = Sparse.eval nodeValue2197 (mixedVector B) := by
    change mixedMoment B node2197 node2197Labels = _
    exact sound2197 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2664 : mixedVector B (Sum.inr 2664) = Sparse.eval nodeValue2664 (mixedVector B) := by
    change mixedMoment B node2664 node2664Labels = _
    exact sound2664 B hB hF
  have h2691 : mixedVector B (Sum.inr 2691) = Sparse.eval nodeValue2691 (mixedVector B) := by
    change mixedMoment B node2691 node2691Labels = _
    exact sound2691 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  simpa only [sourceForm2491, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1662, h1666, h1669, h1710, h2139, h2143, h2146, h2170, h2171, h2187, h2193, h2197, h2208, h2218, h2247, h2268, h2664, h2691, h2712, h2726, reducedSource2007] using sourceEq2491 B hB

theorem rowSound2007 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2007 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2007, numericCheck2007, reducedZero2007 B hB hF, mul_zero]

theorem reducedZero2008 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2008 (mixedVector B) = 0 := by
  have h1801 : mixedVector B (Sum.inr 1801) = Sparse.eval nodeValue1801 (mixedVector B) := by
    change mixedMoment B node1801 node1801Labels = _
    exact sound1801 B hB hF
  have h1804 : mixedVector B (Sum.inr 1804) = Sparse.eval nodeValue1804 (mixedVector B) := by
    change mixedMoment B node1804 node1804Labels = _
    exact sound1804 B hB hF
  have h1809 : mixedVector B (Sum.inr 1809) = Sparse.eval nodeValue1809 (mixedVector B) := by
    change mixedMoment B node1809 node1809Labels = _
    exact sound1809 B hB hF
  have h2052 : mixedVector B (Sum.inr 2052) = Sparse.eval nodeValue2052 (mixedVector B) := by
    change mixedMoment B node2052 node2052Labels = _
    exact sound2052 B hB hF
  have h3389 : mixedVector B (Sum.inr 3389) = Sparse.eval nodeValue3389 (mixedVector B) := by
    change mixedMoment B node3389 node3389Labels = _
    exact sound3389 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm2492, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1801, h1804, h1809, h2052, h3389, h4085, reducedSource2008] using sourceEq2492 B hB

theorem rowSound2008 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2008 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2008, numericCheck2008, reducedZero2008 B hB hF, mul_zero]

theorem reducedZero2009 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2009 (mixedVector B) = 0 := by
  have h918 : mixedVector B (Sum.inr 918) = Sparse.eval nodeValue918 (mixedVector B) := by
    change mixedMoment B node918 node918Labels = _
    exact sound918 B hB hF
  have h1801 : mixedVector B (Sum.inr 1801) = Sparse.eval nodeValue1801 (mixedVector B) := by
    change mixedMoment B node1801 node1801Labels = _
    exact sound1801 B hB hF
  have h2050 : mixedVector B (Sum.inr 2050) = Sparse.eval nodeValue2050 (mixedVector B) := by
    change mixedMoment B node2050 node2050Labels = _
    exact sound2050 B hB hF
  have h2052 : mixedVector B (Sum.inr 2052) = Sparse.eval nodeValue2052 (mixedVector B) := by
    change mixedMoment B node2052 node2052Labels = _
    exact sound2052 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm2493, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h918, h1801, h2050, h2052, h4085, reducedSource2009] using sourceEq2493 B hB

theorem rowSound2009 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2009 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2009, numericCheck2009, reducedZero2009 B hB hF, mul_zero]

theorem reducedZero2012 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2012 (mixedVector B) = 0 := by
  have h4063 : mixedVector B (Sum.inr 4063) = Sparse.eval nodeValue4063 (mixedVector B) := by
    change mixedMoment B node4063 node4063Labels = _
    exact sound4063 B hB hF
  have h4064 : mixedVector B (Sum.inr 4064) = Sparse.eval nodeValue4064 (mixedVector B) := by
    change mixedMoment B node4064 node4064Labels = _
    exact sound4064 B hB hF
  have h4065 : mixedVector B (Sum.inr 4065) = Sparse.eval nodeValue4065 (mixedVector B) := by
    change mixedMoment B node4065 node4065Labels = _
    exact sound4065 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4073 : mixedVector B (Sum.inr 4073) = Sparse.eval nodeValue4073 (mixedVector B) := by
    change mixedMoment B node4073 node4073Labels = _
    exact sound4073 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  have h4077 : mixedVector B (Sum.inr 4077) = Sparse.eval nodeValue4077 (mixedVector B) := by
    change mixedMoment B node4077 node4077Labels = _
    exact sound4077 B hB hF
  have h4078 : mixedVector B (Sum.inr 4078) = Sparse.eval nodeValue4078 (mixedVector B) := by
    change mixedMoment B node4078 node4078Labels = _
    exact sound4078 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
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
  simpa only [sourceForm2496, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4063, h4064, h4065, h4069, h4073, h4074, h4075, h4077, h4078, h4079, h4080, h4081, h4082, h4083, h4084, h4088, h4090, h4091, h4092, reducedSource2012] using sourceEq2496 B hB

theorem rowSound2012 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2012 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2012, numericCheck2012, reducedZero2012 B hB hF, mul_zero]

theorem reducedZero2013 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2013 (mixedVector B) = 0 := by
  have h3128 : mixedVector B (Sum.inr 3128) = Sparse.eval nodeValue3128 (mixedVector B) := by
    change mixedMoment B node3128 node3128Labels = _
    exact sound3128 B hB hF
  have h3130 : mixedVector B (Sum.inr 3130) = Sparse.eval nodeValue3130 (mixedVector B) := by
    change mixedMoment B node3130 node3130Labels = _
    exact sound3130 B hB hF
  have h3155 : mixedVector B (Sum.inr 3155) = Sparse.eval nodeValue3155 (mixedVector B) := by
    change mixedMoment B node3155 node3155Labels = _
    exact sound3155 B hB hF
  have h3390 : mixedVector B (Sum.inr 3390) = Sparse.eval nodeValue3390 (mixedVector B) := by
    change mixedMoment B node3390 node3390Labels = _
    exact sound3390 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2497, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3128, h3130, h3155, h3390, h4083, reducedSource2013] using sourceEq2497 B hB

theorem rowSound2013 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2013 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2013, numericCheck2013, reducedZero2013 B hB hF, mul_zero]

theorem sourceRowsAt2000 : MixedData.sourceRows (2000 : Fin 2425) =
    MixedData.row2000 := by decide +kernel

theorem sourceRowsAt2001 : MixedData.sourceRows (2001 : Fin 2425) =
    MixedData.row2001 := by decide +kernel

theorem sourceRowsAt2002 : MixedData.sourceRows (2002 : Fin 2425) =
    MixedData.row2002 := by decide +kernel

theorem sourceRowsAt2003 : MixedData.sourceRows (2003 : Fin 2425) =
    MixedData.row2003 := by decide +kernel

theorem sourceRowsAt2004 : MixedData.sourceRows (2004 : Fin 2425) =
    MixedData.row2004 := by decide +kernel

theorem sourceRowsAt2005 : MixedData.sourceRows (2005 : Fin 2425) =
    MixedData.row2005 := by decide +kernel

theorem sourceRowsAt2006 : MixedData.sourceRows (2006 : Fin 2425) =
    MixedData.row2006 := by decide +kernel

theorem sourceRowsAt2007 : MixedData.sourceRows (2007 : Fin 2425) =
    MixedData.row2007 := by decide +kernel

theorem sourceRowsAt2008 : MixedData.sourceRows (2008 : Fin 2425) =
    MixedData.row2008 := by decide +kernel

theorem sourceRowsAt2009 : MixedData.sourceRows (2009 : Fin 2425) =
    MixedData.row2009 := by decide +kernel

theorem sourceRowsAt2010 : MixedData.sourceRows (2010 : Fin 2425) =
    MixedData.row2010 := by decide +kernel

theorem sourceRowsAt2011 : MixedData.sourceRows (2011 : Fin 2425) =
    MixedData.row2011 := by decide +kernel

theorem sourceRowsAt2012 : MixedData.sourceRows (2012 : Fin 2425) =
    MixedData.row2012 := by decide +kernel

theorem sourceRowsAt2013 : MixedData.sourceRows (2013 : Fin 2425) =
    MixedData.row2013 := by decide +kernel

theorem sourceRowsAt2014 : MixedData.sourceRows (2014 : Fin 2425) =
    MixedData.row2014 := by decide +kernel

theorem sourceRowsAt2015 : MixedData.sourceRows (2015 : Fin 2425) =
    MixedData.row2015 := by decide +kernel

theorem chunkSound125_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 125) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2000 ∨ k.val = 2001 ∨ k.val = 2002 ∨ k.val = 2003 ∨ k.val = 2004 ∨ k.val = 2005 ∨ k.val = 2006 ∨ k.val = 2007 ∨ k.val = 2008 ∨ k.val = 2009 ∨ k.val = 2010 ∨ k.val = 2011 ∨ k.val = 2012 ∨ k.val = 2013 ∨ k.val = 2014 ∨ k.val = 2015 := by omega
  rcases heq with h2000 | h2001 | h2002 | h2003 | h2004 | h2005 | h2006 | h2007 | h2008 | h2009 | h2010 | h2011 | h2012 | h2013 | h2014 | h2015
  · have he : k = (2000 : Fin 2425) := Fin.ext h2000
    subst k
    rw [sourceRowsAt2000]
    exact rowSound2000 B hB hF
  · have he : k = (2001 : Fin 2425) := Fin.ext h2001
    subst k
    rw [sourceRowsAt2001]
    exact rowSound2001 B hB hF
  · have he : k = (2002 : Fin 2425) := Fin.ext h2002
    subst k
    rw [sourceRowsAt2002]
    exact rowSound2002_e B hB hF
  · have he : k = (2003 : Fin 2425) := Fin.ext h2003
    subst k
    rw [sourceRowsAt2003]
    exact rowSound2003_e B hB hF
  · have he : k = (2004 : Fin 2425) := Fin.ext h2004
    subst k
    rw [sourceRowsAt2004]
    exact rowSound2004_e B hB hF
  · have he : k = (2005 : Fin 2425) := Fin.ext h2005
    subst k
    rw [sourceRowsAt2005]
    exact rowSound2005_e B hB hF
  · have he : k = (2006 : Fin 2425) := Fin.ext h2006
    subst k
    rw [sourceRowsAt2006]
    exact rowSound2006_e B hB hF
  · have he : k = (2007 : Fin 2425) := Fin.ext h2007
    subst k
    rw [sourceRowsAt2007]
    exact rowSound2007 B hB hF
  · have he : k = (2008 : Fin 2425) := Fin.ext h2008
    subst k
    rw [sourceRowsAt2008]
    exact rowSound2008 B hB hF
  · have he : k = (2009 : Fin 2425) := Fin.ext h2009
    subst k
    rw [sourceRowsAt2009]
    exact rowSound2009 B hB hF
  · have he : k = (2010 : Fin 2425) := Fin.ext h2010
    subst k
    rw [sourceRowsAt2010]
    exact rowSound2010_e B hB hF
  · have he : k = (2011 : Fin 2425) := Fin.ext h2011
    subst k
    rw [sourceRowsAt2011]
    exact rowSound2011_e B hB hF
  · have he : k = (2012 : Fin 2425) := Fin.ext h2012
    subst k
    rw [sourceRowsAt2012]
    exact rowSound2012 B hB hF
  · have he : k = (2013 : Fin 2425) := Fin.ext h2013
    subst k
    rw [sourceRowsAt2013]
    exact rowSound2013 B hB hF
  · have he : k = (2014 : Fin 2425) := Fin.ext h2014
    subst k
    rw [sourceRowsAt2014]
    exact rowSound2014_e B hB hF
  · have he : k = (2015 : Fin 2425) := Fin.ext h2015
    subst k
    rw [sourceRowsAt2015]
    exact rowSound2015_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e_oai
