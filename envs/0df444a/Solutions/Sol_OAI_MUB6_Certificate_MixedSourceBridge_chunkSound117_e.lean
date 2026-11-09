-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:14:13.733047+00:00
-- url     : https://prove2.me/submissions/d82a9c05-5951-4365-aa15-80eae417af23

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1872_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1873_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1874_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1877_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1880_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1881_e

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

theorem canonical18341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18341 raw18341Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw18341 raw18341Labels = mixedMoment B raw18341step0 raw18341step0Labels := by
      have hz : ∀ j, raw18341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18341step0 = (fun i j => raw18341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18341step0 raw18341; decide +kernel
      have hl : raw18341step0Labels = raw18341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18341 raw18341Labels permutation346 hz
    mixedMoment B raw18341step0 raw18341step0Labels = mixedMoment B raw18341step1 raw18341step1Labels := by
      have hz : ∀ i, raw18341step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18341step1 = (fun i j => raw18341step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18341step1 raw18341step0; decide +kernel
      have hl : raw18341step1Labels = (fun j => raw18341step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18341step0 raw18341step0Labels permutation6 hz
    mixedMoment B raw18341step1 raw18341step1Labels = mixedMoment B raw18341step2 raw18341step2Labels := by
      have ha : raw18341step2 = (fun i j => raw18341step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18341step2 raw18341step1; decide +kernel
      have hl : raw18341step2Labels = raw18341step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18341step1 raw18341step1Labels permutation125 permutation0
    mixedMoment B raw18341step2 raw18341step2Labels = mixedMoment B raw18341step3 raw18341step3Labels := by
      have ha : raw18341step3 = -raw18341step2 := by apply Matrix.ext; change ∀ i j, raw18341step3 i j = -(raw18341step2 i j); unfold raw18341step3 raw18341step2; decide +kernel
      have hl : raw18341step3Labels = raw18341step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

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

theorem canonical19413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19413 raw19413Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw19413 raw19413Labels = mixedMoment B raw19413step0 raw19413step0Labels := by
      have hz : ∀ j, raw19413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19413step0 = (fun i j => raw19413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19413step0 raw19413; decide +kernel
      have hl : raw19413step0Labels = raw19413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413 raw19413Labels permutation434 hz
    mixedMoment B raw19413step0 raw19413step0Labels = mixedMoment B raw19413step1 raw19413step1Labels := by
      have hz : ∀ j, raw19413step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19413step1 = (fun i j => raw19413step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19413step1 raw19413step0; decide +kernel
      have hl : raw19413step1Labels = raw19413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413step0 raw19413step0Labels permutation80 hz
    mixedMoment B raw19413step1 raw19413step1Labels = mixedMoment B raw19413step2 raw19413step2Labels := by
      have hz : ∀ j, raw19413step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19413step2 = (fun i j => raw19413step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19413step2 raw19413step1; decide +kernel
      have hl : raw19413step2Labels = raw19413step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413step1 raw19413step1Labels permutation14 hz
    mixedMoment B raw19413step2 raw19413step2Labels = mixedMoment B raw19413step3 raw19413step3Labels := by
      have ha : raw19413step3 = (fun i j => raw19413step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19413step3 raw19413step2; decide +kernel
      have hl : raw19413step3Labels = raw19413step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19413step2 raw19413step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21656 raw21656Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw21656 raw21656Labels = mixedMoment B raw21656step0 raw21656step0Labels := by
      have hz : ∀ j, raw21656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21656step0 = (fun i j => raw21656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21656step0 raw21656; decide +kernel
      have hl : raw21656step0Labels = raw21656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21656 raw21656Labels permutation434 hz
    mixedMoment B raw21656step0 raw21656step0Labels = mixedMoment B raw21656step1 raw21656step1Labels := by
      have hz : ∀ j, raw21656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21656step1 = (fun i j => raw21656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21656step1 raw21656step0; decide +kernel
      have hl : raw21656step1Labels = raw21656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21656step0 raw21656step0Labels permutation80 hz
    mixedMoment B raw21656step1 raw21656step1Labels = mixedMoment B raw21656step2 raw21656step2Labels := by
      have ha : raw21656step2 = (fun i j => raw21656step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21656step2 raw21656step1; decide +kernel
      have hl : raw21656step2Labels = raw21656step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21656step1 raw21656step1Labels permutation9 permutation7
    mixedMoment B raw21656step2 raw21656step2Labels = mixedMoment B raw21656step3 raw21656step3Labels := by
      have ha : raw21656step3 = -raw21656step2 := by apply Matrix.ext; change ∀ i j, raw21656step3 i j = -(raw21656step2 i j); unfold raw21656step3 raw21656step2; decide +kernel
      have hl : raw21656step3Labels = raw21656step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21656step3 raw21656step3Labels = mixedMoment B raw21656step4 raw21656step4Labels := by
      have ha : raw21656step4 = raw21656step3 := by apply Matrix.ext; unfold raw21656step4 raw21656step3; decide +kernel
      have hl : raw21656step3Labels = labelEmbedding1 ∘ raw21656step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21656step3 raw21656step3Labels raw21656step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical21660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21660 raw21660Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw21660 raw21660Labels = mixedMoment B raw21660step0 raw21660step0Labels := by
      have hz : ∀ j, raw21660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21660step0 = (fun i j => raw21660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21660step0 raw21660; decide +kernel
      have hl : raw21660step0Labels = raw21660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21660 raw21660Labels permutation434 hz
    mixedMoment B raw21660step0 raw21660step0Labels = mixedMoment B raw21660step1 raw21660step1Labels := by
      have hz : ∀ j, raw21660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21660step1 = (fun i j => raw21660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21660step1 raw21660step0; decide +kernel
      have hl : raw21660step1Labels = raw21660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21660step0 raw21660step0Labels permutation80 hz
    mixedMoment B raw21660step1 raw21660step1Labels = mixedMoment B raw21660step2 raw21660step2Labels := by
      have hz : ∀ j, raw21660step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21660step2 = (fun i j => raw21660step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21660step2 raw21660step1; decide +kernel
      have hl : raw21660step2Labels = raw21660step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21660step1 raw21660step1Labels permutation14 hz
    mixedMoment B raw21660step2 raw21660step2Labels = mixedMoment B raw21660step3 raw21660step3Labels := by
      have ha : raw21660step3 = (fun i j => raw21660step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21660step3 raw21660step2; decide +kernel
      have hl : raw21660step3Labels = raw21660step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21660step2 raw21660step2Labels permutation3 permutation7
    mixedMoment B raw21660step3 raw21660step3Labels = mixedMoment B raw21660step4 raw21660step4Labels := by
      have ha : raw21660step4 = -raw21660step3 := by apply Matrix.ext; change ∀ i j, raw21660step4 i j = -(raw21660step3 i j); unfold raw21660step4 raw21660step3; decide +kernel
      have hl : raw21660step4Labels = raw21660step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21660step4 raw21660step4Labels = mixedMoment B raw21660step5 raw21660step5Labels := by
      have ha : raw21660step5 = raw21660step4 := by apply Matrix.ext; unfold raw21660step5 raw21660step4; decide +kernel
      have hl : raw21660step4Labels = labelEmbedding1 ∘ raw21660step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21660step4 raw21660step4Labels raw21660step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2293 node2293Labels := by rfl

theorem canonical21677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21677 raw21677Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw21677 raw21677Labels = mixedMoment B raw21677step0 raw21677step0Labels := by
      have hz : ∀ j, raw21677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21677step0 = (fun i j => raw21677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21677step0 raw21677; decide +kernel
      have hl : raw21677step0Labels = raw21677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21677 raw21677Labels permutation434 hz
    mixedMoment B raw21677step0 raw21677step0Labels = mixedMoment B raw21677step1 raw21677step1Labels := by
      have hz : ∀ j, raw21677step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21677step1 = (fun i j => raw21677step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21677step1 raw21677step0; decide +kernel
      have hl : raw21677step1Labels = raw21677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21677step0 raw21677step0Labels permutation80 hz
    mixedMoment B raw21677step1 raw21677step1Labels = mixedMoment B raw21677step2 raw21677step2Labels := by
      have ha : raw21677step2 = (fun i j => raw21677step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21677step2 raw21677step1; decide +kernel
      have hl : raw21677step2Labels = raw21677step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21677step1 raw21677step1Labels permutation9 permutation7
    mixedMoment B raw21677step2 raw21677step2Labels = mixedMoment B raw21677step3 raw21677step3Labels := by
      have ha : raw21677step3 = -raw21677step2 := by apply Matrix.ext; change ∀ i j, raw21677step3 i j = -(raw21677step2 i j); unfold raw21677step3 raw21677step2; decide +kernel
      have hl : raw21677step3Labels = raw21677step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21677step3 raw21677step3Labels = mixedMoment B raw21677step4 raw21677step4Labels := by
      have ha : raw21677step4 = raw21677step3 := by apply Matrix.ext; unfold raw21677step4 raw21677step3; decide +kernel
      have hl : raw21677step3Labels = labelEmbedding1 ∘ raw21677step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21677step3 raw21677step3Labels raw21677step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

theorem canonical21680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21680 raw21680Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw21680 raw21680Labels = mixedMoment B raw21680step0 raw21680step0Labels := by
      have hz : ∀ j, raw21680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21680step0 = (fun i j => raw21680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21680step0 raw21680; decide +kernel
      have hl : raw21680step0Labels = raw21680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21680 raw21680Labels permutation434 hz
    mixedMoment B raw21680step0 raw21680step0Labels = mixedMoment B raw21680step1 raw21680step1Labels := by
      have hz : ∀ j, raw21680step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21680step1 = (fun i j => raw21680step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21680step1 raw21680step0; decide +kernel
      have hl : raw21680step1Labels = raw21680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21680step0 raw21680step0Labels permutation80 hz
    mixedMoment B raw21680step1 raw21680step1Labels = mixedMoment B raw21680step2 raw21680step2Labels := by
      have hz : ∀ j, raw21680step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21680step2 = (fun i j => raw21680step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21680step2 raw21680step1; decide +kernel
      have hl : raw21680step2Labels = raw21680step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21680step1 raw21680step1Labels permutation14 hz
    mixedMoment B raw21680step2 raw21680step2Labels = mixedMoment B raw21680step3 raw21680step3Labels := by
      have ha : raw21680step3 = (fun i j => raw21680step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21680step3 raw21680step2; decide +kernel
      have hl : raw21680step3Labels = raw21680step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21680step2 raw21680step2Labels permutation3 permutation7
    mixedMoment B raw21680step3 raw21680step3Labels = mixedMoment B raw21680step4 raw21680step4Labels := by
      have ha : raw21680step4 = -raw21680step3 := by apply Matrix.ext; change ∀ i j, raw21680step4 i j = -(raw21680step3 i j); unfold raw21680step4 raw21680step3; decide +kernel
      have hl : raw21680step4Labels = raw21680step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21680step4 raw21680step4Labels = mixedMoment B raw21680step5 raw21680step5Labels := by
      have ha : raw21680step5 = raw21680step4 := by apply Matrix.ext; unfold raw21680step5 raw21680step4; decide +kernel
      have hl : raw21680step4Labels = labelEmbedding1 ∘ raw21680step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21680step4 raw21680step4Labels raw21680step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1755 node1755Labels := by rfl

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

theorem canonical22311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22311 raw22311Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw22311 raw22311Labels = mixedMoment B raw22311step0 raw22311step0Labels := by
      have hz : ∀ j, raw22311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22311step0 = (fun i j => raw22311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22311step0 raw22311; decide +kernel
      have hl : raw22311step0Labels = raw22311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22311 raw22311Labels permutation434 hz
    mixedMoment B raw22311step0 raw22311step0Labels = mixedMoment B raw22311step1 raw22311step1Labels := by
      have hz : ∀ j, raw22311step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22311step1 = (fun i j => raw22311step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22311step1 raw22311step0; decide +kernel
      have hl : raw22311step1Labels = raw22311step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22311step0 raw22311step0Labels permutation80 hz
    mixedMoment B raw22311step1 raw22311step1Labels = mixedMoment B raw22311step2 raw22311step2Labels := by
      have hz : ∀ i, raw22311step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22311step2 = (fun i j => raw22311step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22311step2 raw22311step1; decide +kernel
      have hl : raw22311step2Labels = (fun j => raw22311step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22311step1 raw22311step1Labels permutation6 hz
    _ = mixedMoment B node4067 node4067Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23390 raw23390Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw23390 raw23390Labels = mixedMoment B raw23390step0 raw23390step0Labels := by
      have hz : ∀ j, raw23390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23390step0 = (fun i j => raw23390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23390step0 raw23390; decide +kernel
      have hl : raw23390step0Labels = raw23390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23390 raw23390Labels permutation434 hz
    mixedMoment B raw23390step0 raw23390step0Labels = mixedMoment B raw23390step1 raw23390step1Labels := by
      have hz : ∀ j, raw23390step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23390step1 = (fun i j => raw23390step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23390step1 raw23390step0; decide +kernel
      have hl : raw23390step1Labels = raw23390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23390step0 raw23390step0Labels permutation56 hz
    mixedMoment B raw23390step1 raw23390step1Labels = mixedMoment B raw23390step2 raw23390step2Labels := by
      have ha : raw23390step2 = (fun i j => raw23390step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23390step2 raw23390step1; decide +kernel
      have hl : raw23390step2Labels = raw23390step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23390step1 raw23390step1Labels permutation9 permutation7
    mixedMoment B raw23390step2 raw23390step2Labels = mixedMoment B raw23390step3 raw23390step3Labels := by
      have ha : raw23390step3 = -raw23390step2 := by apply Matrix.ext; change ∀ i j, raw23390step3 i j = -(raw23390step2 i j); unfold raw23390step3 raw23390step2; decide +kernel
      have hl : raw23390step3Labels = raw23390step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23390step3 raw23390step3Labels = mixedMoment B raw23390step4 raw23390step4Labels := by
      have ha : raw23390step4 = raw23390step3 := by apply Matrix.ext; unfold raw23390step4 raw23390step3; decide +kernel
      have hl : raw23390step3Labels = labelEmbedding1 ∘ raw23390step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23390step3 raw23390step3Labels raw23390step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical23391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23391 raw23391Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw23391 raw23391Labels = mixedMoment B raw23391step0 raw23391step0Labels := by
      have hz : ∀ j, raw23391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23391step0 = (fun i j => raw23391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23391step0 raw23391; decide +kernel
      have hl : raw23391step0Labels = raw23391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23391 raw23391Labels permutation346 hz
    mixedMoment B raw23391step0 raw23391step0Labels = mixedMoment B raw23391step1 raw23391step1Labels := by
      have hz : ∀ j, raw23391step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23391step1 = (fun i j => raw23391step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23391step1 raw23391step0; decide +kernel
      have hl : raw23391step1Labels = raw23391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23391step0 raw23391step0Labels permutation56 hz
    mixedMoment B raw23391step1 raw23391step1Labels = mixedMoment B raw23391step2 raw23391step2Labels := by
      have ha : raw23391step2 = (fun i j => raw23391step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23391step2 raw23391step1; decide +kernel
      have hl : raw23391step2Labels = raw23391step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23391step1 raw23391step1Labels permutation9 permutation7
    mixedMoment B raw23391step2 raw23391step2Labels = mixedMoment B raw23391step3 raw23391step3Labels := by
      have ha : raw23391step3 = -raw23391step2 := by apply Matrix.ext; change ∀ i j, raw23391step3 i j = -(raw23391step2 i j); unfold raw23391step3 raw23391step2; decide +kernel
      have hl : raw23391step3Labels = raw23391step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23391step3 raw23391step3Labels = mixedMoment B raw23391step4 raw23391step4Labels := by
      have ha : raw23391step4 = raw23391step3 := by apply Matrix.ext; unfold raw23391step4 raw23391step3; decide +kernel
      have hl : raw23391step3Labels = labelEmbedding1 ∘ raw23391step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23391step3 raw23391step3Labels raw23391step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical23392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23392 raw23392Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw23392 raw23392Labels = mixedMoment B raw23392step0 raw23392step0Labels := by
      have hz : ∀ j, raw23392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23392step0 = (fun i j => raw23392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23392step0 raw23392; decide +kernel
      have hl : raw23392step0Labels = raw23392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23392 raw23392Labels permutation434 hz
    mixedMoment B raw23392step0 raw23392step0Labels = mixedMoment B raw23392step1 raw23392step1Labels := by
      have hz : ∀ j, raw23392step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23392step1 = (fun i j => raw23392step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23392step1 raw23392step0; decide +kernel
      have hl : raw23392step1Labels = raw23392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23392step0 raw23392step0Labels permutation80 hz
    mixedMoment B raw23392step1 raw23392step1Labels = mixedMoment B raw23392step2 raw23392step2Labels := by
      have hz : ∀ j, raw23392step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23392step2 = (fun i j => raw23392step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23392step2 raw23392step1; decide +kernel
      have hl : raw23392step2Labels = raw23392step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23392step1 raw23392step1Labels permutation14 hz
    mixedMoment B raw23392step2 raw23392step2Labels = mixedMoment B raw23392step3 raw23392step3Labels := by
      have ha : raw23392step3 = (fun i j => raw23392step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23392step3 raw23392step2; decide +kernel
      have hl : raw23392step3Labels = raw23392step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23392step2 raw23392step2Labels permutation3 permutation7
    mixedMoment B raw23392step3 raw23392step3Labels = mixedMoment B raw23392step4 raw23392step4Labels := by
      have ha : raw23392step4 = -raw23392step3 := by apply Matrix.ext; change ∀ i j, raw23392step4 i j = -(raw23392step3 i j); unfold raw23392step4 raw23392step3; decide +kernel
      have hl : raw23392step4Labels = raw23392step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23392step4 raw23392step4Labels = mixedMoment B raw23392step5 raw23392step5Labels := by
      have ha : raw23392step5 = raw23392step4 := by apply Matrix.ext; unfold raw23392step5 raw23392step4; decide +kernel
      have hl : raw23392step4Labels = labelEmbedding1 ∘ raw23392step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23392step4 raw23392step4Labels raw23392step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2281 node2281Labels := by rfl

theorem canonical23393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23393 raw23393Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw23393 raw23393Labels = mixedMoment B raw23393step0 raw23393step0Labels := by
      have hz : ∀ j, raw23393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23393step0 = (fun i j => raw23393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23393step0 raw23393; decide +kernel
      have hl : raw23393step0Labels = raw23393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23393 raw23393Labels permutation434 hz
    mixedMoment B raw23393step0 raw23393step0Labels = mixedMoment B raw23393step1 raw23393step1Labels := by
      have hz : ∀ j, raw23393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23393step1 = (fun i j => raw23393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23393step1 raw23393step0; decide +kernel
      have hl : raw23393step1Labels = raw23393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23393step0 raw23393step0Labels permutation80 hz
    mixedMoment B raw23393step1 raw23393step1Labels = mixedMoment B raw23393step2 raw23393step2Labels := by
      have hz : ∀ j, raw23393step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23393step2 = (fun i j => raw23393step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23393step2 raw23393step1; decide +kernel
      have hl : raw23393step2Labels = raw23393step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23393step1 raw23393step1Labels permutation14 hz
    mixedMoment B raw23393step2 raw23393step2Labels = mixedMoment B raw23393step3 raw23393step3Labels := by
      have ha : raw23393step3 = (fun i j => raw23393step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23393step3 raw23393step2; decide +kernel
      have hl : raw23393step3Labels = raw23393step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23393step2 raw23393step2Labels permutation3 permutation7
    mixedMoment B raw23393step3 raw23393step3Labels = mixedMoment B raw23393step4 raw23393step4Labels := by
      have ha : raw23393step4 = -raw23393step3 := by apply Matrix.ext; change ∀ i j, raw23393step4 i j = -(raw23393step3 i j); unfold raw23393step4 raw23393step3; decide +kernel
      have hl : raw23393step4Labels = raw23393step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23393step4 raw23393step4Labels = mixedMoment B raw23393step5 raw23393step5Labels := by
      have ha : raw23393step5 = raw23393step4 := by apply Matrix.ext; unfold raw23393step5 raw23393step4; decide +kernel
      have hl : raw23393step4Labels = labelEmbedding1 ∘ raw23393step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23393step4 raw23393step4Labels raw23393step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2268 node2268Labels := by rfl

theorem canonical23400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23400 raw23400Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23400 raw23400Labels = mixedMoment B raw23400step0 raw23400step0Labels := by
      have hz : ∀ j, raw23400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23400step0 = (fun i j => raw23400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23400step0 raw23400; decide +kernel
      have hl : raw23400step0Labels = raw23400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23400 raw23400Labels permutation434 hz
    mixedMoment B raw23400step0 raw23400step0Labels = mixedMoment B raw23400step1 raw23400step1Labels := by
      have ha : raw23400step1 = (fun i j => raw23400step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23400step1 raw23400step0; decide +kernel
      have hl : raw23400step1Labels = raw23400step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23400step0 raw23400step0Labels permutation33 permutation7
    mixedMoment B raw23400step1 raw23400step1Labels = mixedMoment B raw23400step2 raw23400step2Labels := by
      have ha : raw23400step2 = -raw23400step1 := by apply Matrix.ext; change ∀ i j, raw23400step2 i j = -(raw23400step1 i j); unfold raw23400step2 raw23400step1; decide +kernel
      have hl : raw23400step2Labels = raw23400step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23400step2 raw23400step2Labels = mixedMoment B raw23400step3 raw23400step3Labels := by
      have ha : raw23400step3 = raw23400step2 := by apply Matrix.ext; unfold raw23400step3 raw23400step2; decide +kernel
      have hl : raw23400step2Labels = labelEmbedding1 ∘ raw23400step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23400step2 raw23400step2Labels raw23400step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

theorem canonical23405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23405 raw23405Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23405 raw23405Labels = mixedMoment B raw23405step0 raw23405step0Labels := by
      have hz : ∀ j, raw23405 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23405step0 = (fun i j => raw23405 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23405step0 raw23405; decide +kernel
      have hl : raw23405step0Labels = raw23405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23405 raw23405Labels permutation346 hz
    mixedMoment B raw23405step0 raw23405step0Labels = mixedMoment B raw23405step1 raw23405step1Labels := by
      have ha : raw23405step1 = (fun i j => raw23405step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23405step1 raw23405step0; decide +kernel
      have hl : raw23405step1Labels = raw23405step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23405step0 raw23405step0Labels permutation33 permutation7
    mixedMoment B raw23405step1 raw23405step1Labels = mixedMoment B raw23405step2 raw23405step2Labels := by
      have ha : raw23405step2 = -raw23405step1 := by apply Matrix.ext; change ∀ i j, raw23405step2 i j = -(raw23405step1 i j); unfold raw23405step2 raw23405step1; decide +kernel
      have hl : raw23405step2Labels = raw23405step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23405step2 raw23405step2Labels = mixedMoment B raw23405step3 raw23405step3Labels := by
      have ha : raw23405step3 = raw23405step2 := by apply Matrix.ext; unfold raw23405step3 raw23405step2; decide +kernel
      have hl : raw23405step2Labels = labelEmbedding1 ∘ raw23405step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23405step2 raw23405step2Labels raw23405step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

theorem canonical23410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23410 raw23410Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw23410 raw23410Labels = mixedMoment B raw23410step0 raw23410step0Labels := by
      have hz : ∀ j, raw23410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23410step0 = (fun i j => raw23410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23410step0 raw23410; decide +kernel
      have hl : raw23410step0Labels = raw23410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23410 raw23410Labels permutation434 hz
    mixedMoment B raw23410step0 raw23410step0Labels = mixedMoment B raw23410step1 raw23410step1Labels := by
      have hz : ∀ j, raw23410step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23410step1 = (fun i j => raw23410step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23410step1 raw23410step0; decide +kernel
      have hl : raw23410step1Labels = raw23410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23410step0 raw23410step0Labels permutation80 hz
    mixedMoment B raw23410step1 raw23410step1Labels = mixedMoment B raw23410step2 raw23410step2Labels := by
      have ha : raw23410step2 = (fun i j => raw23410step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23410step2 raw23410step1; decide +kernel
      have hl : raw23410step2Labels = raw23410step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23410step1 raw23410step1Labels permutation9 permutation7
    mixedMoment B raw23410step2 raw23410step2Labels = mixedMoment B raw23410step3 raw23410step3Labels := by
      have ha : raw23410step3 = -raw23410step2 := by apply Matrix.ext; change ∀ i j, raw23410step3 i j = -(raw23410step2 i j); unfold raw23410step3 raw23410step2; decide +kernel
      have hl : raw23410step3Labels = raw23410step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23410step3 raw23410step3Labels = mixedMoment B raw23410step4 raw23410step4Labels := by
      have ha : raw23410step4 = raw23410step3 := by apply Matrix.ext; unfold raw23410step4 raw23410step3; decide +kernel
      have hl : raw23410step3Labels = labelEmbedding1 ∘ raw23410step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23410step3 raw23410step3Labels raw23410step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

theorem canonical23415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23415 raw23415Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw23415 raw23415Labels = mixedMoment B raw23415step0 raw23415step0Labels := by
      have hz : ∀ j, raw23415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23415step0 = (fun i j => raw23415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23415step0 raw23415; decide +kernel
      have hl : raw23415step0Labels = raw23415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23415 raw23415Labels permutation434 hz
    mixedMoment B raw23415step0 raw23415step0Labels = mixedMoment B raw23415step1 raw23415step1Labels := by
      have hz : ∀ j, raw23415step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23415step1 = (fun i j => raw23415step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23415step1 raw23415step0; decide +kernel
      have hl : raw23415step1Labels = raw23415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23415step0 raw23415step0Labels permutation80 hz
    mixedMoment B raw23415step1 raw23415step1Labels = mixedMoment B raw23415step2 raw23415step2Labels := by
      have ha : raw23415step2 = (fun i j => raw23415step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23415step2 raw23415step1; decide +kernel
      have hl : raw23415step2Labels = raw23415step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23415step1 raw23415step1Labels permutation9 permutation7
    mixedMoment B raw23415step2 raw23415step2Labels = mixedMoment B raw23415step3 raw23415step3Labels := by
      have ha : raw23415step3 = -raw23415step2 := by apply Matrix.ext; change ∀ i j, raw23415step3 i j = -(raw23415step2 i j); unfold raw23415step3 raw23415step2; decide +kernel
      have hl : raw23415step3Labels = raw23415step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23415step3 raw23415step3Labels = mixedMoment B raw23415step4 raw23415step4Labels := by
      have ha : raw23415step4 = raw23415step3 := by apply Matrix.ext; unfold raw23415step4 raw23415step3; decide +kernel
      have hl : raw23415step3Labels = labelEmbedding1 ∘ raw23415step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23415step3 raw23415step3Labels raw23415step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1687 node1687Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical183
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23536 raw23536Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw23536 raw23536Labels = mixedMoment B raw23536step0 raw23536step0Labels := by
      have hz : ∀ j, raw23536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23536step0 = (fun i j => raw23536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23536step0 raw23536; decide +kernel
      have hl : raw23536step0Labels = raw23536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23536 raw23536Labels permutation434 hz
    mixedMoment B raw23536step0 raw23536step0Labels = mixedMoment B raw23536step1 raw23536step1Labels := by
      have hz : ∀ j, raw23536step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23536step1 = (fun i j => raw23536step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23536step1 raw23536step0; decide +kernel
      have hl : raw23536step1Labels = raw23536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23536step0 raw23536step0Labels permutation56 hz
    mixedMoment B raw23536step1 raw23536step1Labels = mixedMoment B raw23536step2 raw23536step2Labels := by
      have ha : raw23536step2 = (fun i j => raw23536step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23536step2 raw23536step1; decide +kernel
      have hl : raw23536step2Labels = raw23536step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23536step1 raw23536step1Labels permutation9 permutation7
    mixedMoment B raw23536step2 raw23536step2Labels = mixedMoment B raw23536step3 raw23536step3Labels := by
      have ha : raw23536step3 = -raw23536step2 := by apply Matrix.ext; change ∀ i j, raw23536step3 i j = -(raw23536step2 i j); unfold raw23536step3 raw23536step2; decide +kernel
      have hl : raw23536step3Labels = raw23536step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23536step3 raw23536step3Labels = mixedMoment B raw23536step4 raw23536step4Labels := by
      have ha : raw23536step4 = raw23536step3 := by apply Matrix.ext; unfold raw23536step4 raw23536step3; decide +kernel
      have hl : raw23536step3Labels = labelEmbedding1 ∘ raw23536step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23536step3 raw23536step3Labels raw23536step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical23537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23537 raw23537Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw23537 raw23537Labels = mixedMoment B raw23537step0 raw23537step0Labels := by
      have hz : ∀ j, raw23537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23537step0 = (fun i j => raw23537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23537step0 raw23537; decide +kernel
      have hl : raw23537step0Labels = raw23537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23537 raw23537Labels permutation346 hz
    mixedMoment B raw23537step0 raw23537step0Labels = mixedMoment B raw23537step1 raw23537step1Labels := by
      have hz : ∀ j, raw23537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23537step1 = (fun i j => raw23537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23537step1 raw23537step0; decide +kernel
      have hl : raw23537step1Labels = raw23537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23537step0 raw23537step0Labels permutation56 hz
    mixedMoment B raw23537step1 raw23537step1Labels = mixedMoment B raw23537step2 raw23537step2Labels := by
      have ha : raw23537step2 = (fun i j => raw23537step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23537step2 raw23537step1; decide +kernel
      have hl : raw23537step2Labels = raw23537step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23537step1 raw23537step1Labels permutation9 permutation7
    mixedMoment B raw23537step2 raw23537step2Labels = mixedMoment B raw23537step3 raw23537step3Labels := by
      have ha : raw23537step3 = -raw23537step2 := by apply Matrix.ext; change ∀ i j, raw23537step3 i j = -(raw23537step2 i j); unfold raw23537step3 raw23537step2; decide +kernel
      have hl : raw23537step3Labels = raw23537step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23537step3 raw23537step3Labels = mixedMoment B raw23537step4 raw23537step4Labels := by
      have ha : raw23537step4 = raw23537step3 := by apply Matrix.ext; unfold raw23537step4 raw23537step3; decide +kernel
      have hl : raw23537step3Labels = labelEmbedding1 ∘ raw23537step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23537step3 raw23537step3Labels raw23537step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical23538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23538 raw23538Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23538 raw23538Labels = mixedMoment B raw23538step0 raw23538step0Labels := by
      have hz : ∀ j, raw23538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23538step0 = (fun i j => raw23538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23538step0 raw23538; decide +kernel
      have hl : raw23538step0Labels = raw23538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23538 raw23538Labels permutation434 hz
    mixedMoment B raw23538step0 raw23538step0Labels = mixedMoment B raw23538step1 raw23538step1Labels := by
      have hz : ∀ j, raw23538step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23538step1 = (fun i j => raw23538step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23538step1 raw23538step0; decide +kernel
      have hl : raw23538step1Labels = raw23538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23538step0 raw23538step0Labels permutation80 hz
    mixedMoment B raw23538step1 raw23538step1Labels = mixedMoment B raw23538step2 raw23538step2Labels := by
      have hz : ∀ j, raw23538step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23538step2 = (fun i j => raw23538step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23538step2 raw23538step1; decide +kernel
      have hl : raw23538step2Labels = raw23538step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23538step1 raw23538step1Labels permutation14 hz
    mixedMoment B raw23538step2 raw23538step2Labels = mixedMoment B raw23538step3 raw23538step3Labels := by
      have hz : ∀ i, raw23538step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw23538step3 = (fun i j => raw23538step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw23538step3 raw23538step2; decide +kernel
      have hl : raw23538step3Labels = (fun j => raw23538step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23538step2 raw23538step2Labels permutation4 hz
    mixedMoment B raw23538step3 raw23538step3Labels = mixedMoment B raw23538step4 raw23538step4Labels := by
      have ha : raw23538step4 = (fun i j => raw23538step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23538step4 raw23538step3; decide +kernel
      have hl : raw23538step4Labels = raw23538step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23538step3 raw23538step3Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical23544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23544 raw23544Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23544 raw23544Labels = mixedMoment B raw23544step0 raw23544step0Labels := by
      have hz : ∀ j, raw23544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23544step0 = (fun i j => raw23544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23544step0 raw23544; decide +kernel
      have hl : raw23544step0Labels = raw23544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23544 raw23544Labels permutation434 hz
    mixedMoment B raw23544step0 raw23544step0Labels = mixedMoment B raw23544step1 raw23544step1Labels := by
      have ha : raw23544step1 = (fun i j => raw23544step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23544step1 raw23544step0; decide +kernel
      have hl : raw23544step1Labels = raw23544step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23544step0 raw23544step0Labels permutation33 permutation7
    mixedMoment B raw23544step1 raw23544step1Labels = mixedMoment B raw23544step2 raw23544step2Labels := by
      have ha : raw23544step2 = -raw23544step1 := by apply Matrix.ext; change ∀ i j, raw23544step2 i j = -(raw23544step1 i j); unfold raw23544step2 raw23544step1; decide +kernel
      have hl : raw23544step2Labels = raw23544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23544step2 raw23544step2Labels = mixedMoment B raw23544step3 raw23544step3Labels := by
      have ha : raw23544step3 = raw23544step2 := by apply Matrix.ext; unfold raw23544step3 raw23544step2; decide +kernel
      have hl : raw23544step2Labels = labelEmbedding1 ∘ raw23544step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23544step2 raw23544step2Labels raw23544step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

theorem canonical23548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23548 raw23548Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23548 raw23548Labels = mixedMoment B raw23548step0 raw23548step0Labels := by
      have hz : ∀ j, raw23548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23548step0 = (fun i j => raw23548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23548step0 raw23548; decide +kernel
      have hl : raw23548step0Labels = raw23548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23548 raw23548Labels permutation346 hz
    mixedMoment B raw23548step0 raw23548step0Labels = mixedMoment B raw23548step1 raw23548step1Labels := by
      have ha : raw23548step1 = (fun i j => raw23548step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23548step1 raw23548step0; decide +kernel
      have hl : raw23548step1Labels = raw23548step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23548step0 raw23548step0Labels permutation33 permutation7
    mixedMoment B raw23548step1 raw23548step1Labels = mixedMoment B raw23548step2 raw23548step2Labels := by
      have ha : raw23548step2 = -raw23548step1 := by apply Matrix.ext; change ∀ i j, raw23548step2 i j = -(raw23548step1 i j); unfold raw23548step2 raw23548step1; decide +kernel
      have hl : raw23548step2Labels = raw23548step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23548step2 raw23548step2Labels = mixedMoment B raw23548step3 raw23548step3Labels := by
      have ha : raw23548step3 = raw23548step2 := by apply Matrix.ext; unfold raw23548step3 raw23548step2; decide +kernel
      have hl : raw23548step2Labels = labelEmbedding1 ∘ raw23548step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23548step2 raw23548step2Labels raw23548step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23552 raw23552Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw23552 raw23552Labels = mixedMoment B raw23552step0 raw23552step0Labels := by
      have hz : ∀ j, raw23552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23552step0 = (fun i j => raw23552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23552step0 raw23552; decide +kernel
      have hl : raw23552step0Labels = raw23552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23552 raw23552Labels permutation434 hz
    mixedMoment B raw23552step0 raw23552step0Labels = mixedMoment B raw23552step1 raw23552step1Labels := by
      have hz : ∀ j, raw23552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23552step1 = (fun i j => raw23552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23552step1 raw23552step0; decide +kernel
      have hl : raw23552step1Labels = raw23552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23552step0 raw23552step0Labels permutation80 hz
    mixedMoment B raw23552step1 raw23552step1Labels = mixedMoment B raw23552step2 raw23552step2Labels := by
      have ha : raw23552step2 = (fun i j => raw23552step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23552step2 raw23552step1; decide +kernel
      have hl : raw23552step2Labels = raw23552step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23552step1 raw23552step1Labels permutation9 permutation7
    mixedMoment B raw23552step2 raw23552step2Labels = mixedMoment B raw23552step3 raw23552step3Labels := by
      have ha : raw23552step3 = -raw23552step2 := by apply Matrix.ext; change ∀ i j, raw23552step3 i j = -(raw23552step2 i j); unfold raw23552step3 raw23552step2; decide +kernel
      have hl : raw23552step3Labels = raw23552step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23552step3 raw23552step3Labels = mixedMoment B raw23552step4 raw23552step4Labels := by
      have ha : raw23552step4 = raw23552step3 := by apply Matrix.ext; unfold raw23552step4 raw23552step3; decide +kernel
      have hl : raw23552step3Labels = labelEmbedding1 ∘ raw23552step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23552step3 raw23552step3Labels raw23552step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

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

theorem canonical23782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23782 raw23782Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23782 raw23782Labels = mixedMoment B raw23782step0 raw23782step0Labels := by
      have hz : ∀ j, raw23782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23782step0 = (fun i j => raw23782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23782step0 raw23782; decide +kernel
      have hl : raw23782step0Labels = raw23782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23782 raw23782Labels permutation434 hz
    mixedMoment B raw23782step0 raw23782step0Labels = mixedMoment B raw23782step1 raw23782step1Labels := by
      have hz : ∀ i, raw23782step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23782step1 = (fun i j => raw23782step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23782step1 raw23782step0; decide +kernel
      have hl : raw23782step1Labels = (fun j => raw23782step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23782step0 raw23782step0Labels permutation6 hz
    _ = mixedMoment B node4065 node4065Labels := by rfl

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

theorem canonical23789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23789 raw23789Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw23789 raw23789Labels = mixedMoment B raw23789step0 raw23789step0Labels := by
      have hz : ∀ j, raw23789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23789step0 = (fun i j => raw23789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23789step0 raw23789; decide +kernel
      have hl : raw23789step0Labels = raw23789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23789 raw23789Labels permutation434 hz
    mixedMoment B raw23789step0 raw23789step0Labels = mixedMoment B raw23789step1 raw23789step1Labels := by
      have hz : ∀ j, raw23789step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23789step1 = (fun i j => raw23789step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23789step1 raw23789step0; decide +kernel
      have hl : raw23789step1Labels = raw23789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23789step0 raw23789step0Labels permutation80 hz
    mixedMoment B raw23789step1 raw23789step1Labels = mixedMoment B raw23789step2 raw23789step2Labels := by
      have hz : ∀ i, raw23789step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23789step2 = (fun i j => raw23789step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23789step2 raw23789step1; decide +kernel
      have hl : raw23789step2Labels = (fun j => raw23789step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23789step1 raw23789step1Labels permutation6 hz
    mixedMoment B raw23789step2 raw23789step2Labels = mixedMoment B raw23789step3 raw23789step3Labels := by
      have ha : raw23789step3 = (fun i j => raw23789step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23789step3 raw23789step2; decide +kernel
      have hl : raw23789step3Labels = raw23789step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23789step2 raw23789step2Labels permutation9 permutation0
    _ = mixedMoment B node4067 node4067Labels := by rfl

theorem canonical23805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23805 raw23805Labels = mixedMoment B node923 node923Labels := by
  calc
    mixedMoment B raw23805 raw23805Labels = mixedMoment B raw23805step0 raw23805step0Labels := by
      have ha : raw23805step0 = (fun i j => raw23805 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23805step0 raw23805; decide +kernel
      have hl : raw23805step0Labels = raw23805Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23805 raw23805Labels permutation158 permutation2
    _ = mixedMoment B node923 node923Labels := by rfl

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

theorem canonical23810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23810 raw23810Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23810 raw23810Labels = mixedMoment B raw23810step0 raw23810step0Labels := by
      have hz : ∀ j, raw23810 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw23810step0 = (fun i j => raw23810 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw23810step0 raw23810; decide +kernel
      have hl : raw23810step0Labels = raw23810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23810 raw23810Labels permutation590 hz
    mixedMoment B raw23810step0 raw23810step0Labels = mixedMoment B raw23810step1 raw23810step1Labels := by
      have hz : ∀ j, raw23810step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw23810step1 = (fun i j => raw23810step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw23810step1 raw23810step0; decide +kernel
      have hl : raw23810step1Labels = raw23810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23810step0 raw23810step0Labels permutation104 hz
    mixedMoment B raw23810step1 raw23810step1Labels = mixedMoment B raw23810step2 raw23810step2Labels := by
      have hz : ∀ j, raw23810step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23810step2 = (fun i j => raw23810step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23810step2 raw23810step1; decide +kernel
      have hl : raw23810step2Labels = raw23810step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23810step1 raw23810step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical23833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23833 raw23833Labels = mixedMoment B node920 node920Labels := by
  calc
    mixedMoment B raw23833 raw23833Labels = mixedMoment B raw23833step0 raw23833step0Labels := by
      have ha : raw23833step0 = (fun i j => raw23833 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23833step0 raw23833; decide +kernel
      have hl : raw23833step0Labels = raw23833Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23833 raw23833Labels permutation160 permutation2
    _ = mixedMoment B node920 node920Labels := by rfl

theorem canonical23838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23838 raw23838Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23838 raw23838Labels = mixedMoment B raw23838step0 raw23838step0Labels := by
      have hz : ∀ j, raw23838 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23838step0 = (fun i j => raw23838 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23838step0 raw23838; decide +kernel
      have hl : raw23838step0Labels = raw23838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23838 raw23838Labels permutation520 hz
    mixedMoment B raw23838step0 raw23838step0Labels = mixedMoment B raw23838step1 raw23838step1Labels := by
      have hz : ∀ j, raw23838step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw23838step1 = (fun i j => raw23838step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw23838step1 raw23838step0; decide +kernel
      have hl : raw23838step1Labels = raw23838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23838step0 raw23838step0Labels permutation104 hz
    mixedMoment B raw23838step1 raw23838step1Labels = mixedMoment B raw23838step2 raw23838step2Labels := by
      have hz : ∀ j, raw23838step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23838step2 = (fun i j => raw23838step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23838step2 raw23838step1; decide +kernel
      have hl : raw23838step2Labels = raw23838step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23838step1 raw23838step1Labels permutation14 hz
    mixedMoment B raw23838step2 raw23838step2Labels = mixedMoment B raw23838step3 raw23838step3Labels := by
      have ha : raw23838step3 = (fun i j => raw23838step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23838step3 raw23838step2; decide +kernel
      have hl : raw23838step3Labels = raw23838step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23838step2 raw23838step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

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

theorem canonical27309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27309 raw27309Labels = mixedMoment B node1820 node1820Labels := by
  calc
    mixedMoment B raw27309 raw27309Labels = mixedMoment B raw27309step0 raw27309step0Labels := by
      have hz : ∀ j, raw27309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27309step0 = (fun i j => raw27309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27309step0 raw27309; decide +kernel
      have hl : raw27309step0Labels = raw27309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27309 raw27309Labels permutation434 hz
    mixedMoment B raw27309step0 raw27309step0Labels = mixedMoment B raw27309step1 raw27309step1Labels := by
      have hz : ∀ j, raw27309step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27309step1 = (fun i j => raw27309step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27309step1 raw27309step0; decide +kernel
      have hl : raw27309step1Labels = raw27309step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27309step0 raw27309step0Labels permutation80 hz
    _ = mixedMoment B node1820 node1820Labels := by rfl

theorem canonical27312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27312 raw27312Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw27312 raw27312Labels = mixedMoment B raw27312step0 raw27312step0Labels := by
      have hz : ∀ j, raw27312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27312step0 = (fun i j => raw27312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27312step0 raw27312; decide +kernel
      have hl : raw27312step0Labels = raw27312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27312 raw27312Labels permutation434 hz
    mixedMoment B raw27312step0 raw27312step0Labels = mixedMoment B raw27312step1 raw27312step1Labels := by
      have hz : ∀ j, raw27312step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27312step1 = (fun i j => raw27312step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27312step1 raw27312step0; decide +kernel
      have hl : raw27312step1Labels = raw27312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27312step0 raw27312step0Labels permutation80 hz
    mixedMoment B raw27312step1 raw27312step1Labels = mixedMoment B raw27312step2 raw27312step2Labels := by
      have ha : raw27312step2 = (fun i j => raw27312step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27312step2 raw27312step1; decide +kernel
      have hl : raw27312step2Labels = raw27312step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27312step1 raw27312step1Labels permutation9 permutation2
    _ = mixedMoment B node2065 node2065Labels := by rfl

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

theorem canonical29299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29299 raw29299Labels = mixedMoment B node4076 node4076Labels := by
  calc
    mixedMoment B raw29299 raw29299Labels = mixedMoment B raw29299step0 raw29299step0Labels := by
      have hz : ∀ j, raw29299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29299step0 = (fun i j => raw29299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29299step0 raw29299; decide +kernel
      have hl : raw29299step0Labels = raw29299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29299 raw29299Labels permutation434 hz
    mixedMoment B raw29299step0 raw29299step0Labels = mixedMoment B raw29299step1 raw29299step1Labels := by
      have hz : ∀ j, raw29299step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29299step1 = (fun i j => raw29299step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29299step1 raw29299step0; decide +kernel
      have hl : raw29299step1Labels = raw29299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29299step0 raw29299step0Labels permutation80 hz
    mixedMoment B raw29299step1 raw29299step1Labels = mixedMoment B raw29299step2 raw29299step2Labels := by
      have hz : ∀ i, raw29299step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29299step2 = (fun i j => raw29299step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29299step2 raw29299step1; decide +kernel
      have hl : raw29299step2Labels = (fun j => raw29299step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29299step1 raw29299step1Labels permutation6 hz
    _ = mixedMoment B node4076 node4076Labels := by rfl

theorem canonical29300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29300 raw29300Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw29300 raw29300Labels = mixedMoment B raw29300step0 raw29300step0Labels := by
      have hz : ∀ j, raw29300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29300step0 = (fun i j => raw29300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29300step0 raw29300; decide +kernel
      have hl : raw29300step0Labels = raw29300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29300 raw29300Labels permutation434 hz
    mixedMoment B raw29300step0 raw29300step0Labels = mixedMoment B raw29300step1 raw29300step1Labels := by
      have hz : ∀ i, raw29300step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29300step1 = (fun i j => raw29300step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29300step1 raw29300step0; decide +kernel
      have hl : raw29300step1Labels = (fun j => raw29300step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29300step0 raw29300step0Labels permutation6 hz
    mixedMoment B raw29300step1 raw29300step1Labels = mixedMoment B raw29300step2 raw29300step2Labels := by
      have ha : raw29300step2 = (fun i j => raw29300step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29300step2 raw29300step1; decide +kernel
      have hl : raw29300step2Labels = raw29300step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29300step1 raw29300step1Labels permutation149 permutation0
    mixedMoment B raw29300step2 raw29300step2Labels = mixedMoment B raw29300step3 raw29300step3Labels := by
      have ha : raw29300step3 = -raw29300step2 := by apply Matrix.ext; change ∀ i j, raw29300step3 i j = -(raw29300step2 i j); unfold raw29300step3 raw29300step2; decide +kernel
      have hl : raw29300step3Labels = raw29300step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

theorem canonical29301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29301 raw29301Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw29301 raw29301Labels = mixedMoment B raw29301step0 raw29301step0Labels := by
      have hz : ∀ j, raw29301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29301step0 = (fun i j => raw29301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29301step0 raw29301; decide +kernel
      have hl : raw29301step0Labels = raw29301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29301 raw29301Labels permutation346 hz
    mixedMoment B raw29301step0 raw29301step0Labels = mixedMoment B raw29301step1 raw29301step1Labels := by
      have hz : ∀ i, raw29301step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29301step1 = (fun i j => raw29301step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29301step1 raw29301step0; decide +kernel
      have hl : raw29301step1Labels = (fun j => raw29301step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29301step0 raw29301step0Labels permutation6 hz
    mixedMoment B raw29301step1 raw29301step1Labels = mixedMoment B raw29301step2 raw29301step2Labels := by
      have ha : raw29301step2 = (fun i j => raw29301step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29301step2 raw29301step1; decide +kernel
      have hl : raw29301step2Labels = raw29301step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29301step1 raw29301step1Labels permutation149 permutation0
    mixedMoment B raw29301step2 raw29301step2Labels = mixedMoment B raw29301step3 raw29301step3Labels := by
      have ha : raw29301step3 = -raw29301step2 := by apply Matrix.ext; change ∀ i j, raw29301step3 i j = -(raw29301step2 i j); unfold raw29301step3 raw29301step2; decide +kernel
      have hl : raw29301step3Labels = raw29301step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical245
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31374 raw31374Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw31374 raw31374Labels = mixedMoment B raw31374step0 raw31374step0Labels := by
      have hz : ∀ j, raw31374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31374step0 = (fun i j => raw31374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31374step0 raw31374; decide +kernel
      have hl : raw31374step0Labels = raw31374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31374 raw31374Labels permutation434 hz
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical31378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31378 raw31378Labels = mixedMoment B node2021 node2021Labels := by
  calc
    _ = mixedMoment B node2021 node2021Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical247
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31667 raw31667Labels = mixedMoment B node2680 node2680Labels := by
  calc
    mixedMoment B raw31667 raw31667Labels = mixedMoment B raw31667step0 raw31667step0Labels := by
      have hz : ∀ j, raw31667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31667step0 = (fun i j => raw31667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31667step0 raw31667; decide +kernel
      have hl : raw31667step0Labels = raw31667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31667 raw31667Labels permutation434 hz
    mixedMoment B raw31667step0 raw31667step0Labels = mixedMoment B raw31667step1 raw31667step1Labels := by
      have hz : ∀ j, raw31667step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31667step1 = (fun i j => raw31667step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31667step1 raw31667step0; decide +kernel
      have hl : raw31667step1Labels = raw31667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31667step0 raw31667step0Labels permutation80 hz
    mixedMoment B raw31667step1 raw31667step1Labels = mixedMoment B raw31667step2 raw31667step2Labels := by
      have ha : raw31667step2 = (fun i j => raw31667step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31667step2 raw31667step1; decide +kernel
      have hl : raw31667step2Labels = raw31667step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31667step1 raw31667step1Labels permutation25 permutation7
    mixedMoment B raw31667step2 raw31667step2Labels = mixedMoment B raw31667step3 raw31667step3Labels := by
      have ha : raw31667step3 = raw31667step2 := by apply Matrix.ext; unfold raw31667step3 raw31667step2; decide +kernel
      have hl : raw31667step2Labels = labelEmbedding1 ∘ raw31667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31667step2 raw31667step2Labels raw31667step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2680 node2680Labels := by rfl

theorem canonical31668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31668 raw31668Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw31668 raw31668Labels = mixedMoment B raw31668step0 raw31668step0Labels := by
      have hz : ∀ j, raw31668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31668step0 = (fun i j => raw31668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31668step0 raw31668; decide +kernel
      have hl : raw31668step0Labels = raw31668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31668 raw31668Labels permutation434 hz
    mixedMoment B raw31668step0 raw31668step0Labels = mixedMoment B raw31668step1 raw31668step1Labels := by
      have ha : raw31668step1 = (fun i j => raw31668step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31668step1 raw31668step0; decide +kernel
      have hl : raw31668step1Labels = raw31668step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31668step0 raw31668step0Labels permutation125 permutation7
    mixedMoment B raw31668step1 raw31668step1Labels = mixedMoment B raw31668step2 raw31668step2Labels := by
      have ha : raw31668step2 = raw31668step1 := by apply Matrix.ext; unfold raw31668step2 raw31668step1; decide +kernel
      have hl : raw31668step1Labels = labelEmbedding1 ∘ raw31668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31668step1 raw31668step1Labels raw31668step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2664 node2664Labels := by rfl

theorem canonical31669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31669 raw31669Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw31669 raw31669Labels = mixedMoment B raw31669step0 raw31669step0Labels := by
      have hz : ∀ j, raw31669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31669step0 = (fun i j => raw31669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31669step0 raw31669; decide +kernel
      have hl : raw31669step0Labels = raw31669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31669 raw31669Labels permutation346 hz
    mixedMoment B raw31669step0 raw31669step0Labels = mixedMoment B raw31669step1 raw31669step1Labels := by
      have ha : raw31669step1 = (fun i j => raw31669step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31669step1 raw31669step0; decide +kernel
      have hl : raw31669step1Labels = raw31669step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31669step0 raw31669step0Labels permutation125 permutation7
    mixedMoment B raw31669step1 raw31669step1Labels = mixedMoment B raw31669step2 raw31669step2Labels := by
      have ha : raw31669step2 = raw31669step1 := by apply Matrix.ext; unfold raw31669step2 raw31669step1; decide +kernel
      have hl : raw31669step1Labels = labelEmbedding1 ∘ raw31669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31669step1 raw31669step1Labels raw31669step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2664 node2664Labels := by rfl

theorem canonical31670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31670 raw31670Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw31670 raw31670Labels = mixedMoment B raw31670step0 raw31670step0Labels := by
      have hz : ∀ j, raw31670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31670step0 = (fun i j => raw31670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31670step0 raw31670; decide +kernel
      have hl : raw31670step0Labels = raw31670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31670 raw31670Labels permutation434 hz
    mixedMoment B raw31670step0 raw31670step0Labels = mixedMoment B raw31670step1 raw31670step1Labels := by
      have hz : ∀ j, raw31670step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31670step1 = (fun i j => raw31670step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31670step1 raw31670step0; decide +kernel
      have hl : raw31670step1Labels = raw31670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31670step0 raw31670step0Labels permutation80 hz
    mixedMoment B raw31670step1 raw31670step1Labels = mixedMoment B raw31670step2 raw31670step2Labels := by
      have ha : raw31670step2 = (fun i j => raw31670step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31670step2 raw31670step1; decide +kernel
      have hl : raw31670step2Labels = raw31670step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31670step1 raw31670step1Labels permutation9 permutation7
    mixedMoment B raw31670step2 raw31670step2Labels = mixedMoment B raw31670step3 raw31670step3Labels := by
      have ha : raw31670step3 = -raw31670step2 := by apply Matrix.ext; change ∀ i j, raw31670step3 i j = -(raw31670step2 i j); unfold raw31670step3 raw31670step2; decide +kernel
      have hl : raw31670step3Labels = raw31670step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31670step3 raw31670step3Labels = mixedMoment B raw31670step4 raw31670step4Labels := by
      have ha : raw31670step4 = raw31670step3 := by apply Matrix.ext; unfold raw31670step4 raw31670step3; decide +kernel
      have hl : raw31670step3Labels = labelEmbedding1 ∘ raw31670step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31670step3 raw31670step3Labels raw31670step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

theorem canonical31671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31671 raw31671Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw31671 raw31671Labels = mixedMoment B raw31671step0 raw31671step0Labels := by
      have hz : ∀ j, raw31671 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31671step0 = (fun i j => raw31671 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31671step0 raw31671; decide +kernel
      have hl : raw31671step0Labels = raw31671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31671 raw31671Labels permutation434 hz
    mixedMoment B raw31671step0 raw31671step0Labels = mixedMoment B raw31671step1 raw31671step1Labels := by
      have hz : ∀ j, raw31671step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31671step1 = (fun i j => raw31671step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31671step1 raw31671step0; decide +kernel
      have hl : raw31671step1Labels = raw31671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31671step0 raw31671step0Labels permutation80 hz
    mixedMoment B raw31671step1 raw31671step1Labels = mixedMoment B raw31671step2 raw31671step2Labels := by
      have ha : raw31671step2 = (fun i j => raw31671step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31671step2 raw31671step1; decide +kernel
      have hl : raw31671step2Labels = raw31671step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31671step1 raw31671step1Labels permutation25 permutation7
    mixedMoment B raw31671step2 raw31671step2Labels = mixedMoment B raw31671step3 raw31671step3Labels := by
      have ha : raw31671step3 = raw31671step2 := by apply Matrix.ext; unfold raw31671step3 raw31671step2; decide +kernel
      have hl : raw31671step2Labels = labelEmbedding1 ∘ raw31671step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31671step2 raw31671step2Labels raw31671step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2726 node2726Labels := by rfl

theorem canonical31672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31672 raw31672Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw31672 raw31672Labels = mixedMoment B raw31672step0 raw31672step0Labels := by
      have hz : ∀ j, raw31672 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31672step0 = (fun i j => raw31672 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31672step0 raw31672; decide +kernel
      have hl : raw31672step0Labels = raw31672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31672 raw31672Labels permutation434 hz
    mixedMoment B raw31672step0 raw31672step0Labels = mixedMoment B raw31672step1 raw31672step1Labels := by
      have hz : ∀ j, raw31672step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31672step1 = (fun i j => raw31672step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31672step1 raw31672step0; decide +kernel
      have hl : raw31672step1Labels = raw31672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31672step0 raw31672step0Labels permutation80 hz
    mixedMoment B raw31672step1 raw31672step1Labels = mixedMoment B raw31672step2 raw31672step2Labels := by
      have hz : ∀ j, raw31672step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw31672step2 = (fun i j => raw31672step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw31672step2 raw31672step1; decide +kernel
      have hl : raw31672step2Labels = raw31672step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31672step1 raw31672step1Labels permutation14 hz
    mixedMoment B raw31672step2 raw31672step2Labels = mixedMoment B raw31672step3 raw31672step3Labels := by
      have ha : raw31672step3 = (fun i j => raw31672step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31672step3 raw31672step2; decide +kernel
      have hl : raw31672step3Labels = raw31672step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31672step2 raw31672step2Labels permutation3 permutation7
    mixedMoment B raw31672step3 raw31672step3Labels = mixedMoment B raw31672step4 raw31672step4Labels := by
      have ha : raw31672step4 = -raw31672step3 := by apply Matrix.ext; change ∀ i j, raw31672step4 i j = -(raw31672step3 i j); unfold raw31672step4 raw31672step3; decide +kernel
      have hl : raw31672step4Labels = raw31672step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31672step4 raw31672step4Labels = mixedMoment B raw31672step5 raw31672step5Labels := by
      have ha : raw31672step5 = raw31672step4 := by apply Matrix.ext; unfold raw31672step5 raw31672step4; decide +kernel
      have hl : raw31672step4Labels = labelEmbedding1 ∘ raw31672step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31672step4 raw31672step4Labels raw31672step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1741 node1741Labels := by rfl

theorem canonical31673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31673 raw31673Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw31673 raw31673Labels = mixedMoment B raw31673step0 raw31673step0Labels := by
      have hz : ∀ j, raw31673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31673step0 = (fun i j => raw31673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31673step0 raw31673; decide +kernel
      have hl : raw31673step0Labels = raw31673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31673 raw31673Labels permutation434 hz
    mixedMoment B raw31673step0 raw31673step0Labels = mixedMoment B raw31673step1 raw31673step1Labels := by
      have ha : raw31673step1 = (fun i j => raw31673step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31673step1 raw31673step0; decide +kernel
      have hl : raw31673step1Labels = raw31673step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31673step0 raw31673step0Labels permutation33 permutation7
    mixedMoment B raw31673step1 raw31673step1Labels = mixedMoment B raw31673step2 raw31673step2Labels := by
      have ha : raw31673step2 = -raw31673step1 := by apply Matrix.ext; change ∀ i j, raw31673step2 i j = -(raw31673step1 i j); unfold raw31673step2 raw31673step1; decide +kernel
      have hl : raw31673step2Labels = raw31673step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31673step2 raw31673step2Labels = mixedMoment B raw31673step3 raw31673step3Labels := by
      have ha : raw31673step3 = raw31673step2 := by apply Matrix.ext; unfold raw31673step3 raw31673step2; decide +kernel
      have hl : raw31673step2Labels = labelEmbedding1 ∘ raw31673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31673step2 raw31673step2Labels raw31673step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2146 node2146Labels := by rfl

theorem canonical31674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31674 raw31674Labels = mixedMoment B node2171 node2171Labels := by
  calc
    mixedMoment B raw31674 raw31674Labels = mixedMoment B raw31674step0 raw31674step0Labels := by
      have ha : raw31674step0 = (fun i j => raw31674 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31674step0 raw31674; decide +kernel
      have hl : raw31674step0Labels = raw31674Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31674 raw31674Labels permutation159 permutation7
    mixedMoment B raw31674step0 raw31674step0Labels = mixedMoment B raw31674step1 raw31674step1Labels := by
      have ha : raw31674step1 = -raw31674step0 := by apply Matrix.ext; change ∀ i j, raw31674step1 i j = -(raw31674step0 i j); unfold raw31674step1 raw31674step0; decide +kernel
      have hl : raw31674step1Labels = raw31674step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31674step1 raw31674step1Labels = mixedMoment B raw31674step2 raw31674step2Labels := by
      have ha : raw31674step2 = raw31674step1 := by apply Matrix.ext; unfold raw31674step2 raw31674step1; decide +kernel
      have hl : raw31674step1Labels = labelEmbedding1 ∘ raw31674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31674step1 raw31674step1Labels raw31674step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2171 node2171Labels := by rfl

theorem canonical31675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31675 raw31675Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw31675 raw31675Labels = mixedMoment B raw31675step0 raw31675step0Labels := by
      have hz : ∀ j, raw31675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31675step0 = (fun i j => raw31675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31675step0 raw31675; decide +kernel
      have hl : raw31675step0Labels = raw31675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31675 raw31675Labels permutation434 hz
    mixedMoment B raw31675step0 raw31675step0Labels = mixedMoment B raw31675step1 raw31675step1Labels := by
      have ha : raw31675step1 = (fun i j => raw31675step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31675step1 raw31675step0; decide +kernel
      have hl : raw31675step1Labels = raw31675step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31675step0 raw31675step0Labels permutation33 permutation7
    mixedMoment B raw31675step1 raw31675step1Labels = mixedMoment B raw31675step2 raw31675step2Labels := by
      have ha : raw31675step2 = -raw31675step1 := by apply Matrix.ext; change ∀ i j, raw31675step2 i j = -(raw31675step1 i j); unfold raw31675step2 raw31675step1; decide +kernel
      have hl : raw31675step2Labels = raw31675step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31675step2 raw31675step2Labels = mixedMoment B raw31675step3 raw31675step3Labels := by
      have ha : raw31675step3 = raw31675step2 := by apply Matrix.ext; unfold raw31675step3 raw31675step2; decide +kernel
      have hl : raw31675step2Labels = labelEmbedding1 ∘ raw31675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31675step2 raw31675step2Labels raw31675step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

theorem canonical31676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31676 raw31676Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw31676 raw31676Labels = mixedMoment B raw31676step0 raw31676step0Labels := by
      have hz : ∀ j, raw31676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31676step0 = (fun i j => raw31676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31676step0 raw31676; decide +kernel
      have hl : raw31676step0Labels = raw31676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31676 raw31676Labels permutation434 hz
    mixedMoment B raw31676step0 raw31676step0Labels = mixedMoment B raw31676step1 raw31676step1Labels := by
      have ha : raw31676step1 = (fun i j => raw31676step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31676step1 raw31676step0; decide +kernel
      have hl : raw31676step1Labels = raw31676step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31676step0 raw31676step0Labels permutation33 permutation7
    mixedMoment B raw31676step1 raw31676step1Labels = mixedMoment B raw31676step2 raw31676step2Labels := by
      have ha : raw31676step2 = -raw31676step1 := by apply Matrix.ext; change ∀ i j, raw31676step2 i j = -(raw31676step1 i j); unfold raw31676step2 raw31676step1; decide +kernel
      have hl : raw31676step2Labels = raw31676step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31676step2 raw31676step2Labels = mixedMoment B raw31676step3 raw31676step3Labels := by
      have ha : raw31676step3 = raw31676step2 := by apply Matrix.ext; unfold raw31676step3 raw31676step2; decide +kernel
      have hl : raw31676step2Labels = labelEmbedding1 ∘ raw31676step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31676step2 raw31676step2Labels raw31676step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical31677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31677 raw31677Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw31677 raw31677Labels = mixedMoment B raw31677step0 raw31677step0Labels := by
      have hz : ∀ j, raw31677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31677step0 = (fun i j => raw31677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31677step0 raw31677; decide +kernel
      have hl : raw31677step0Labels = raw31677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31677 raw31677Labels permutation346 hz
    mixedMoment B raw31677step0 raw31677step0Labels = mixedMoment B raw31677step1 raw31677step1Labels := by
      have ha : raw31677step1 = (fun i j => raw31677step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31677step1 raw31677step0; decide +kernel
      have hl : raw31677step1Labels = raw31677step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31677step0 raw31677step0Labels permutation33 permutation7
    mixedMoment B raw31677step1 raw31677step1Labels = mixedMoment B raw31677step2 raw31677step2Labels := by
      have ha : raw31677step2 = -raw31677step1 := by apply Matrix.ext; change ∀ i j, raw31677step2 i j = -(raw31677step1 i j); unfold raw31677step2 raw31677step1; decide +kernel
      have hl : raw31677step2Labels = raw31677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31677step2 raw31677step2Labels = mixedMoment B raw31677step3 raw31677step3Labels := by
      have ha : raw31677step3 = raw31677step2 := by apply Matrix.ext; unfold raw31677step3 raw31677step2; decide +kernel
      have hl : raw31677step2Labels = labelEmbedding1 ∘ raw31677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31677step2 raw31677step2Labels raw31677step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2146 node2146Labels := by rfl

theorem canonical31678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31678 raw31678Labels = mixedMoment B node2171 node2171Labels := by
  calc
    mixedMoment B raw31678 raw31678Labels = mixedMoment B raw31678step0 raw31678step0Labels := by
      have ha : raw31678step0 = (fun i j => raw31678 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31678step0 raw31678; decide +kernel
      have hl : raw31678step0Labels = raw31678Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31678 raw31678Labels permutation153 permutation7
    mixedMoment B raw31678step0 raw31678step0Labels = mixedMoment B raw31678step1 raw31678step1Labels := by
      have ha : raw31678step1 = -raw31678step0 := by apply Matrix.ext; change ∀ i j, raw31678step1 i j = -(raw31678step0 i j); unfold raw31678step1 raw31678step0; decide +kernel
      have hl : raw31678step1Labels = raw31678step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31678step1 raw31678step1Labels = mixedMoment B raw31678step2 raw31678step2Labels := by
      have ha : raw31678step2 = raw31678step1 := by apply Matrix.ext; unfold raw31678step2 raw31678step1; decide +kernel
      have hl : raw31678step1Labels = labelEmbedding1 ∘ raw31678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31678step1 raw31678step1Labels raw31678step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2171 node2171Labels := by rfl

theorem canonical31679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31679 raw31679Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw31679 raw31679Labels = mixedMoment B raw31679step0 raw31679step0Labels := by
      have hz : ∀ j, raw31679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31679step0 = (fun i j => raw31679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31679step0 raw31679; decide +kernel
      have hl : raw31679step0Labels = raw31679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31679 raw31679Labels permutation346 hz
    mixedMoment B raw31679step0 raw31679step0Labels = mixedMoment B raw31679step1 raw31679step1Labels := by
      have ha : raw31679step1 = (fun i j => raw31679step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31679step1 raw31679step0; decide +kernel
      have hl : raw31679step1Labels = raw31679step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31679step0 raw31679step0Labels permutation33 permutation7
    mixedMoment B raw31679step1 raw31679step1Labels = mixedMoment B raw31679step2 raw31679step2Labels := by
      have ha : raw31679step2 = -raw31679step1 := by apply Matrix.ext; change ∀ i j, raw31679step2 i j = -(raw31679step1 i j); unfold raw31679step2 raw31679step1; decide +kernel
      have hl : raw31679step2Labels = raw31679step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31679step2 raw31679step2Labels = mixedMoment B raw31679step3 raw31679step3Labels := by
      have ha : raw31679step3 = raw31679step2 := by apply Matrix.ext; unfold raw31679step3 raw31679step2; decide +kernel
      have hl : raw31679step2Labels = labelEmbedding1 ∘ raw31679step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31679step2 raw31679step2Labels raw31679step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

theorem canonical31680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31680 raw31680Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw31680 raw31680Labels = mixedMoment B raw31680step0 raw31680step0Labels := by
      have hz : ∀ j, raw31680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31680step0 = (fun i j => raw31680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31680step0 raw31680; decide +kernel
      have hl : raw31680step0Labels = raw31680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31680 raw31680Labels permutation346 hz
    mixedMoment B raw31680step0 raw31680step0Labels = mixedMoment B raw31680step1 raw31680step1Labels := by
      have ha : raw31680step1 = (fun i j => raw31680step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31680step1 raw31680step0; decide +kernel
      have hl : raw31680step1Labels = raw31680step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31680step0 raw31680step0Labels permutation33 permutation7
    mixedMoment B raw31680step1 raw31680step1Labels = mixedMoment B raw31680step2 raw31680step2Labels := by
      have ha : raw31680step2 = -raw31680step1 := by apply Matrix.ext; change ∀ i j, raw31680step2 i j = -(raw31680step1 i j); unfold raw31680step2 raw31680step1; decide +kernel
      have hl : raw31680step2Labels = raw31680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31680step2 raw31680step2Labels = mixedMoment B raw31680step3 raw31680step3Labels := by
      have ha : raw31680step3 = raw31680step2 := by apply Matrix.ext; unfold raw31680step3 raw31680step2; decide +kernel
      have hl : raw31680step2Labels = labelEmbedding1 ∘ raw31680step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31680step2 raw31680step2Labels raw31680step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical31681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31681 raw31681Labels = mixedMoment B node2159 node2159Labels := by
  calc
    mixedMoment B raw31681 raw31681Labels = mixedMoment B raw31681step0 raw31681step0Labels := by
      have hz : ∀ j, raw31681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31681step0 = (fun i j => raw31681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31681step0 raw31681; decide +kernel
      have hl : raw31681step0Labels = raw31681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31681 raw31681Labels permutation434 hz
    mixedMoment B raw31681step0 raw31681step0Labels = mixedMoment B raw31681step1 raw31681step1Labels := by
      have hz : ∀ j, raw31681step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31681step1 = (fun i j => raw31681step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31681step1 raw31681step0; decide +kernel
      have hl : raw31681step1Labels = raw31681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31681step0 raw31681step0Labels permutation80 hz
    mixedMoment B raw31681step1 raw31681step1Labels = mixedMoment B raw31681step2 raw31681step2Labels := by
      have ha : raw31681step2 = (fun i j => raw31681step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31681step2 raw31681step1; decide +kernel
      have hl : raw31681step2Labels = raw31681step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31681step1 raw31681step1Labels permutation25 permutation7
    mixedMoment B raw31681step2 raw31681step2Labels = mixedMoment B raw31681step3 raw31681step3Labels := by
      have ha : raw31681step3 = raw31681step2 := by apply Matrix.ext; unfold raw31681step3 raw31681step2; decide +kernel
      have hl : raw31681step2Labels = labelEmbedding1 ∘ raw31681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31681step2 raw31681step2Labels raw31681step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2159 node2159Labels := by rfl

theorem canonical31682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31682 raw31682Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw31682 raw31682Labels = mixedMoment B raw31682step0 raw31682step0Labels := by
      have hz : ∀ j, raw31682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31682step0 = (fun i j => raw31682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31682step0 raw31682; decide +kernel
      have hl : raw31682step0Labels = raw31682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31682 raw31682Labels permutation434 hz
    mixedMoment B raw31682step0 raw31682step0Labels = mixedMoment B raw31682step1 raw31682step1Labels := by
      have ha : raw31682step1 = (fun i j => raw31682step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31682step1 raw31682step0; decide +kernel
      have hl : raw31682step1Labels = raw31682step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31682step0 raw31682step0Labels permutation125 permutation7
    mixedMoment B raw31682step1 raw31682step1Labels = mixedMoment B raw31682step2 raw31682step2Labels := by
      have ha : raw31682step2 = raw31682step1 := by apply Matrix.ext; unfold raw31682step2 raw31682step1; decide +kernel
      have hl : raw31682step1Labels = labelEmbedding1 ∘ raw31682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31682step1 raw31682step1Labels raw31682step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

theorem canonical31683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31683 raw31683Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw31683 raw31683Labels = mixedMoment B raw31683step0 raw31683step0Labels := by
      have hz : ∀ j, raw31683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31683step0 = (fun i j => raw31683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31683step0 raw31683; decide +kernel
      have hl : raw31683step0Labels = raw31683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31683 raw31683Labels permutation346 hz
    mixedMoment B raw31683step0 raw31683step0Labels = mixedMoment B raw31683step1 raw31683step1Labels := by
      have ha : raw31683step1 = (fun i j => raw31683step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31683step1 raw31683step0; decide +kernel
      have hl : raw31683step1Labels = raw31683step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31683step0 raw31683step0Labels permutation125 permutation7
    mixedMoment B raw31683step1 raw31683step1Labels = mixedMoment B raw31683step2 raw31683step2Labels := by
      have ha : raw31683step2 = raw31683step1 := by apply Matrix.ext; unfold raw31683step2 raw31683step1; decide +kernel
      have hl : raw31683step1Labels = labelEmbedding1 ∘ raw31683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31683step1 raw31683step1Labels raw31683step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

theorem canonical31684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31684 raw31684Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw31684 raw31684Labels = mixedMoment B raw31684step0 raw31684step0Labels := by
      have hz : ∀ j, raw31684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31684step0 = (fun i j => raw31684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31684step0 raw31684; decide +kernel
      have hl : raw31684step0Labels = raw31684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31684 raw31684Labels permutation434 hz
    mixedMoment B raw31684step0 raw31684step0Labels = mixedMoment B raw31684step1 raw31684step1Labels := by
      have hz : ∀ j, raw31684step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31684step1 = (fun i j => raw31684step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31684step1 raw31684step0; decide +kernel
      have hl : raw31684step1Labels = raw31684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31684step0 raw31684step0Labels permutation80 hz
    mixedMoment B raw31684step1 raw31684step1Labels = mixedMoment B raw31684step2 raw31684step2Labels := by
      have ha : raw31684step2 = (fun i j => raw31684step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31684step2 raw31684step1; decide +kernel
      have hl : raw31684step2Labels = raw31684step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31684step1 raw31684step1Labels permutation25 permutation7
    mixedMoment B raw31684step2 raw31684step2Labels = mixedMoment B raw31684step3 raw31684step3Labels := by
      have ha : raw31684step3 = raw31684step2 := by apply Matrix.ext; unfold raw31684step3 raw31684step2; decide +kernel
      have hl : raw31684step2Labels = labelEmbedding1 ∘ raw31684step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31684step2 raw31684step2Labels raw31684step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

theorem canonical31685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31685 raw31685Labels = mixedMoment B node2163 node2163Labels := by
  calc
    mixedMoment B raw31685 raw31685Labels = mixedMoment B raw31685step0 raw31685step0Labels := by
      have hz : ∀ j, raw31685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31685step0 = (fun i j => raw31685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31685step0 raw31685; decide +kernel
      have hl : raw31685step0Labels = raw31685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31685 raw31685Labels permutation434 hz
    mixedMoment B raw31685step0 raw31685step0Labels = mixedMoment B raw31685step1 raw31685step1Labels := by
      have hz : ∀ j, raw31685step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31685step1 = (fun i j => raw31685step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31685step1 raw31685step0; decide +kernel
      have hl : raw31685step1Labels = raw31685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31685step0 raw31685step0Labels permutation80 hz
    mixedMoment B raw31685step1 raw31685step1Labels = mixedMoment B raw31685step2 raw31685step2Labels := by
      have ha : raw31685step2 = (fun i j => raw31685step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31685step2 raw31685step1; decide +kernel
      have hl : raw31685step2Labels = raw31685step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31685step1 raw31685step1Labels permutation9 permutation7
    mixedMoment B raw31685step2 raw31685step2Labels = mixedMoment B raw31685step3 raw31685step3Labels := by
      have ha : raw31685step3 = -raw31685step2 := by apply Matrix.ext; change ∀ i j, raw31685step3 i j = -(raw31685step2 i j); unfold raw31685step3 raw31685step2; decide +kernel
      have hl : raw31685step3Labels = raw31685step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31685step3 raw31685step3Labels = mixedMoment B raw31685step4 raw31685step4Labels := by
      have ha : raw31685step4 = raw31685step3 := by apply Matrix.ext; unfold raw31685step4 raw31685step3; decide +kernel
      have hl : raw31685step3Labels = labelEmbedding1 ∘ raw31685step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31685step3 raw31685step3Labels raw31685step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2163 node2163Labels := by rfl

theorem canonical31686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31686 raw31686Labels = mixedMoment B node2180 node2180Labels := by
  calc
    mixedMoment B raw31686 raw31686Labels = mixedMoment B raw31686step0 raw31686step0Labels := by
      have hz : ∀ j, raw31686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31686step0 = (fun i j => raw31686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31686step0 raw31686; decide +kernel
      have hl : raw31686step0Labels = raw31686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31686 raw31686Labels permutation434 hz
    mixedMoment B raw31686step0 raw31686step0Labels = mixedMoment B raw31686step1 raw31686step1Labels := by
      have ha : raw31686step1 = (fun i j => raw31686step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31686step1 raw31686step0; decide +kernel
      have hl : raw31686step1Labels = raw31686step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31686step0 raw31686step0Labels permutation33 permutation7
    mixedMoment B raw31686step1 raw31686step1Labels = mixedMoment B raw31686step2 raw31686step2Labels := by
      have ha : raw31686step2 = -raw31686step1 := by apply Matrix.ext; change ∀ i j, raw31686step2 i j = -(raw31686step1 i j); unfold raw31686step2 raw31686step1; decide +kernel
      have hl : raw31686step2Labels = raw31686step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31686step2 raw31686step2Labels = mixedMoment B raw31686step3 raw31686step3Labels := by
      have ha : raw31686step3 = raw31686step2 := by apply Matrix.ext; unfold raw31686step3 raw31686step2; decide +kernel
      have hl : raw31686step2Labels = labelEmbedding1 ∘ raw31686step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31686step2 raw31686step2Labels raw31686step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2180 node2180Labels := by rfl

theorem canonical31687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31687 raw31687Labels = mixedMoment B node2180 node2180Labels := by
  calc
    mixedMoment B raw31687 raw31687Labels = mixedMoment B raw31687step0 raw31687step0Labels := by
      have hz : ∀ j, raw31687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31687step0 = (fun i j => raw31687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31687step0 raw31687; decide +kernel
      have hl : raw31687step0Labels = raw31687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31687 raw31687Labels permutation346 hz
    mixedMoment B raw31687step0 raw31687step0Labels = mixedMoment B raw31687step1 raw31687step1Labels := by
      have ha : raw31687step1 = (fun i j => raw31687step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31687step1 raw31687step0; decide +kernel
      have hl : raw31687step1Labels = raw31687step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31687step0 raw31687step0Labels permutation33 permutation7
    mixedMoment B raw31687step1 raw31687step1Labels = mixedMoment B raw31687step2 raw31687step2Labels := by
      have ha : raw31687step2 = -raw31687step1 := by apply Matrix.ext; change ∀ i j, raw31687step2 i j = -(raw31687step1 i j); unfold raw31687step2 raw31687step1; decide +kernel
      have hl : raw31687step2Labels = raw31687step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31687step2 raw31687step2Labels = mixedMoment B raw31687step3 raw31687step3Labels := by
      have ha : raw31687step3 = raw31687step2 := by apply Matrix.ext; unfold raw31687step3 raw31687step2; decide +kernel
      have hl : raw31687step2Labels = labelEmbedding1 ∘ raw31687step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31687step2 raw31687step2Labels raw31687step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2180 node2180Labels := by rfl

theorem canonical31688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31688 raw31688Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw31688 raw31688Labels = mixedMoment B raw31688step0 raw31688step0Labels := by
      have hz : ∀ j, raw31688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31688step0 = (fun i j => raw31688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31688step0 raw31688; decide +kernel
      have hl : raw31688step0Labels = raw31688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31688 raw31688Labels permutation434 hz
    mixedMoment B raw31688step0 raw31688step0Labels = mixedMoment B raw31688step1 raw31688step1Labels := by
      have hz : ∀ j, raw31688step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31688step1 = (fun i j => raw31688step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31688step1 raw31688step0; decide +kernel
      have hl : raw31688step1Labels = raw31688step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31688step0 raw31688step0Labels permutation80 hz
    mixedMoment B raw31688step1 raw31688step1Labels = mixedMoment B raw31688step2 raw31688step2Labels := by
      have ha : raw31688step2 = (fun i j => raw31688step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31688step2 raw31688step1; decide +kernel
      have hl : raw31688step2Labels = raw31688step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31688step1 raw31688step1Labels permutation9 permutation7
    mixedMoment B raw31688step2 raw31688step2Labels = mixedMoment B raw31688step3 raw31688step3Labels := by
      have ha : raw31688step3 = -raw31688step2 := by apply Matrix.ext; change ∀ i j, raw31688step3 i j = -(raw31688step2 i j); unfold raw31688step3 raw31688step2; decide +kernel
      have hl : raw31688step3Labels = raw31688step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31688step3 raw31688step3Labels = mixedMoment B raw31688step4 raw31688step4Labels := by
      have ha : raw31688step4 = raw31688step3 := by apply Matrix.ext; unfold raw31688step4 raw31688step3; decide +kernel
      have hl : raw31688step3Labels = labelEmbedding1 ∘ raw31688step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31688step3 raw31688step3Labels raw31688step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2222 node2222Labels := by rfl

theorem canonical31689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31689 raw31689Labels = mixedMoment B node3396 node3396Labels := by
  calc
    mixedMoment B raw31689 raw31689Labels = mixedMoment B raw31689step0 raw31689step0Labels := by
      have hz : ∀ j, raw31689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31689step0 = (fun i j => raw31689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31689step0 raw31689; decide +kernel
      have hl : raw31689step0Labels = raw31689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31689 raw31689Labels permutation434 hz
    mixedMoment B raw31689step0 raw31689step0Labels = mixedMoment B raw31689step1 raw31689step1Labels := by
      have hz : ∀ j, raw31689step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31689step1 = (fun i j => raw31689step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31689step1 raw31689step0; decide +kernel
      have hl : raw31689step1Labels = raw31689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31689step0 raw31689step0Labels permutation80 hz
    mixedMoment B raw31689step1 raw31689step1Labels = mixedMoment B raw31689step2 raw31689step2Labels := by
      have ha : raw31689step2 = (fun i j => raw31689step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31689step2 raw31689step1; decide +kernel
      have hl : raw31689step2Labels = raw31689step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31689step1 raw31689step1Labels permutation9 permutation2
    _ = mixedMoment B node3396 node3396Labels := by rfl

theorem canonical31690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31690 raw31690Labels = mixedMoment B node1809 node1809Labels := by
  calc
    mixedMoment B raw31690 raw31690Labels = mixedMoment B raw31690step0 raw31690step0Labels := by
      have hz : ∀ j, raw31690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31690step0 = (fun i j => raw31690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31690step0 raw31690; decide +kernel
      have hl : raw31690step0Labels = raw31690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31690 raw31690Labels permutation434 hz
    mixedMoment B raw31690step0 raw31690step0Labels = mixedMoment B raw31690step1 raw31690step1Labels := by
      have ha : raw31690step1 = (fun i j => raw31690step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31690step1 raw31690step0; decide +kernel
      have hl : raw31690step1Labels = raw31690step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31690step0 raw31690step0Labels permutation33 permutation2
    _ = mixedMoment B node1809 node1809Labels := by rfl

theorem canonical31691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31691 raw31691Labels = mixedMoment B node1809 node1809Labels := by
  calc
    mixedMoment B raw31691 raw31691Labels = mixedMoment B raw31691step0 raw31691step0Labels := by
      have hz : ∀ j, raw31691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31691step0 = (fun i j => raw31691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31691step0 raw31691; decide +kernel
      have hl : raw31691step0Labels = raw31691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31691 raw31691Labels permutation346 hz
    mixedMoment B raw31691step0 raw31691step0Labels = mixedMoment B raw31691step1 raw31691step1Labels := by
      have ha : raw31691step1 = (fun i j => raw31691step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31691step1 raw31691step0; decide +kernel
      have hl : raw31691step1Labels = raw31691step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31691step0 raw31691step0Labels permutation33 permutation2
    _ = mixedMoment B node1809 node1809Labels := by rfl

theorem canonical31692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31692 raw31692Labels = mixedMoment B node1817 node1817Labels := by
  calc
    mixedMoment B raw31692 raw31692Labels = mixedMoment B raw31692step0 raw31692step0Labels := by
      have hz : ∀ j, raw31692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31692step0 = (fun i j => raw31692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31692step0 raw31692; decide +kernel
      have hl : raw31692step0Labels = raw31692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31692 raw31692Labels permutation434 hz
    mixedMoment B raw31692step0 raw31692step0Labels = mixedMoment B raw31692step1 raw31692step1Labels := by
      have hz : ∀ j, raw31692step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31692step1 = (fun i j => raw31692step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31692step1 raw31692step0; decide +kernel
      have hl : raw31692step1Labels = raw31692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31692step0 raw31692step0Labels permutation80 hz
    mixedMoment B raw31692step1 raw31692step1Labels = mixedMoment B raw31692step2 raw31692step2Labels := by
      have ha : raw31692step2 = (fun i j => raw31692step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31692step2 raw31692step1; decide +kernel
      have hl : raw31692step2Labels = raw31692step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31692step1 raw31692step1Labels permutation9 permutation2
    _ = mixedMoment B node1817 node1817Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical248
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31745 raw31745Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw31745 raw31745Labels = mixedMoment B raw31745step0 raw31745step0Labels := by
      have hz : ∀ j, raw31745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31745step0 = (fun i j => raw31745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31745step0 raw31745; decide +kernel
      have hl : raw31745step0Labels = raw31745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31745 raw31745Labels permutation434 hz
    mixedMoment B raw31745step0 raw31745step0Labels = mixedMoment B raw31745step1 raw31745step1Labels := by
      have hz : ∀ j, raw31745step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31745step1 = (fun i j => raw31745step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31745step1 raw31745step0; decide +kernel
      have hl : raw31745step1Labels = raw31745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31745step0 raw31745step0Labels permutation80 hz
    mixedMoment B raw31745step1 raw31745step1Labels = mixedMoment B raw31745step2 raw31745step2Labels := by
      have ha : raw31745step2 = (fun i j => raw31745step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31745step2 raw31745step1; decide +kernel
      have hl : raw31745step2Labels = raw31745step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31745step1 raw31745step1Labels permutation9 permutation7
    mixedMoment B raw31745step2 raw31745step2Labels = mixedMoment B raw31745step3 raw31745step3Labels := by
      have ha : raw31745step3 = -raw31745step2 := by apply Matrix.ext; change ∀ i j, raw31745step3 i j = -(raw31745step2 i j); unfold raw31745step3 raw31745step2; decide +kernel
      have hl : raw31745step3Labels = raw31745step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31745step3 raw31745step3Labels = mixedMoment B raw31745step4 raw31745step4Labels := by
      have ha : raw31745step4 = raw31745step3 := by apply Matrix.ext; unfold raw31745step4 raw31745step3; decide +kernel
      have hl : raw31745step3Labels = labelEmbedding1 ∘ raw31745step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31745step3 raw31745step3Labels raw31745step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical31746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31746 raw31746Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw31746 raw31746Labels = mixedMoment B raw31746step0 raw31746step0Labels := by
      have hz : ∀ j, raw31746 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31746step0 = (fun i j => raw31746 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31746step0 raw31746; decide +kernel
      have hl : raw31746step0Labels = raw31746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31746 raw31746Labels permutation434 hz
    mixedMoment B raw31746step0 raw31746step0Labels = mixedMoment B raw31746step1 raw31746step1Labels := by
      have ha : raw31746step1 = (fun i j => raw31746step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31746step1 raw31746step0; decide +kernel
      have hl : raw31746step1Labels = raw31746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31746step0 raw31746step0Labels permutation33 permutation7
    mixedMoment B raw31746step1 raw31746step1Labels = mixedMoment B raw31746step2 raw31746step2Labels := by
      have ha : raw31746step2 = -raw31746step1 := by apply Matrix.ext; change ∀ i j, raw31746step2 i j = -(raw31746step1 i j); unfold raw31746step2 raw31746step1; decide +kernel
      have hl : raw31746step2Labels = raw31746step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31746step2 raw31746step2Labels = mixedMoment B raw31746step3 raw31746step3Labels := by
      have ha : raw31746step3 = raw31746step2 := by apply Matrix.ext; unfold raw31746step3 raw31746step2; decide +kernel
      have hl : raw31746step2Labels = labelEmbedding1 ∘ raw31746step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31746step2 raw31746step2Labels raw31746step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical31747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31747 raw31747Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw31747 raw31747Labels = mixedMoment B raw31747step0 raw31747step0Labels := by
      have hz : ∀ j, raw31747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31747step0 = (fun i j => raw31747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31747step0 raw31747; decide +kernel
      have hl : raw31747step0Labels = raw31747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31747 raw31747Labels permutation346 hz
    mixedMoment B raw31747step0 raw31747step0Labels = mixedMoment B raw31747step1 raw31747step1Labels := by
      have ha : raw31747step1 = (fun i j => raw31747step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31747step1 raw31747step0; decide +kernel
      have hl : raw31747step1Labels = raw31747step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31747step0 raw31747step0Labels permutation33 permutation7
    mixedMoment B raw31747step1 raw31747step1Labels = mixedMoment B raw31747step2 raw31747step2Labels := by
      have ha : raw31747step2 = -raw31747step1 := by apply Matrix.ext; change ∀ i j, raw31747step2 i j = -(raw31747step1 i j); unfold raw31747step2 raw31747step1; decide +kernel
      have hl : raw31747step2Labels = raw31747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31747step2 raw31747step2Labels = mixedMoment B raw31747step3 raw31747step3Labels := by
      have ha : raw31747step3 = raw31747step2 := by apply Matrix.ext; unfold raw31747step3 raw31747step2; decide +kernel
      have hl : raw31747step2Labels = labelEmbedding1 ∘ raw31747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31747step2 raw31747step2Labels raw31747step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical31748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31748 raw31748Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw31748 raw31748Labels = mixedMoment B raw31748step0 raw31748step0Labels := by
      have hz : ∀ j, raw31748 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31748step0 = (fun i j => raw31748 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31748step0 raw31748; decide +kernel
      have hl : raw31748step0Labels = raw31748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31748 raw31748Labels permutation434 hz
    mixedMoment B raw31748step0 raw31748step0Labels = mixedMoment B raw31748step1 raw31748step1Labels := by
      have hz : ∀ j, raw31748step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31748step1 = (fun i j => raw31748step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31748step1 raw31748step0; decide +kernel
      have hl : raw31748step1Labels = raw31748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31748step0 raw31748step0Labels permutation80 hz
    mixedMoment B raw31748step1 raw31748step1Labels = mixedMoment B raw31748step2 raw31748step2Labels := by
      have ha : raw31748step2 = (fun i j => raw31748step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31748step2 raw31748step1; decide +kernel
      have hl : raw31748step2Labels = raw31748step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31748step1 raw31748step1Labels permutation9 permutation7
    mixedMoment B raw31748step2 raw31748step2Labels = mixedMoment B raw31748step3 raw31748step3Labels := by
      have ha : raw31748step3 = -raw31748step2 := by apply Matrix.ext; change ∀ i j, raw31748step3 i j = -(raw31748step2 i j); unfold raw31748step3 raw31748step2; decide +kernel
      have hl : raw31748step3Labels = raw31748step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31748step3 raw31748step3Labels = mixedMoment B raw31748step4 raw31748step4Labels := by
      have ha : raw31748step4 = raw31748step3 := by apply Matrix.ext; unfold raw31748step4 raw31748step3; decide +kernel
      have hl : raw31748step3Labels = labelEmbedding1 ∘ raw31748step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31748step3 raw31748step3Labels raw31748step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical31749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31749 raw31749Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw31749 raw31749Labels = mixedMoment B raw31749step0 raw31749step0Labels := by
      have hz : ∀ j, raw31749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31749step0 = (fun i j => raw31749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31749step0 raw31749; decide +kernel
      have hl : raw31749step0Labels = raw31749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31749 raw31749Labels permutation434 hz
    mixedMoment B raw31749step0 raw31749step0Labels = mixedMoment B raw31749step1 raw31749step1Labels := by
      have hz : ∀ j, raw31749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31749step1 = (fun i j => raw31749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31749step1 raw31749step0; decide +kernel
      have hl : raw31749step1Labels = raw31749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31749step0 raw31749step0Labels permutation80 hz
    mixedMoment B raw31749step1 raw31749step1Labels = mixedMoment B raw31749step2 raw31749step2Labels := by
      have ha : raw31749step2 = (fun i j => raw31749step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31749step2 raw31749step1; decide +kernel
      have hl : raw31749step2Labels = raw31749step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31749step1 raw31749step1Labels permutation9 permutation7
    mixedMoment B raw31749step2 raw31749step2Labels = mixedMoment B raw31749step3 raw31749step3Labels := by
      have ha : raw31749step3 = -raw31749step2 := by apply Matrix.ext; change ∀ i j, raw31749step3 i j = -(raw31749step2 i j); unfold raw31749step3 raw31749step2; decide +kernel
      have hl : raw31749step3Labels = raw31749step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31749step3 raw31749step3Labels = mixedMoment B raw31749step4 raw31749step4Labels := by
      have ha : raw31749step4 = raw31749step3 := by apply Matrix.ext; unfold raw31749step4 raw31749step3; decide +kernel
      have hl : raw31749step3Labels = labelEmbedding1 ∘ raw31749step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31749step3 raw31749step3Labels raw31749step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical31750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31750 raw31750Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw31750 raw31750Labels = mixedMoment B raw31750step0 raw31750step0Labels := by
      have hz : ∀ j, raw31750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31750step0 = (fun i j => raw31750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31750step0 raw31750; decide +kernel
      have hl : raw31750step0Labels = raw31750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31750 raw31750Labels permutation434 hz
    mixedMoment B raw31750step0 raw31750step0Labels = mixedMoment B raw31750step1 raw31750step1Labels := by
      have ha : raw31750step1 = (fun i j => raw31750step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31750step1 raw31750step0; decide +kernel
      have hl : raw31750step1Labels = raw31750step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31750step0 raw31750step0Labels permutation33 permutation7
    mixedMoment B raw31750step1 raw31750step1Labels = mixedMoment B raw31750step2 raw31750step2Labels := by
      have ha : raw31750step2 = -raw31750step1 := by apply Matrix.ext; change ∀ i j, raw31750step2 i j = -(raw31750step1 i j); unfold raw31750step2 raw31750step1; decide +kernel
      have hl : raw31750step2Labels = raw31750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31750step2 raw31750step2Labels = mixedMoment B raw31750step3 raw31750step3Labels := by
      have ha : raw31750step3 = raw31750step2 := by apply Matrix.ext; unfold raw31750step3 raw31750step2; decide +kernel
      have hl : raw31750step2Labels = labelEmbedding1 ∘ raw31750step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31750step2 raw31750step2Labels raw31750step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

theorem canonical31751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31751 raw31751Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw31751 raw31751Labels = mixedMoment B raw31751step0 raw31751step0Labels := by
      have ha : raw31751step0 = (fun i j => raw31751 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31751step0 raw31751; decide +kernel
      have hl : raw31751step0Labels = raw31751Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31751 raw31751Labels permutation159 permutation7
    mixedMoment B raw31751step0 raw31751step0Labels = mixedMoment B raw31751step1 raw31751step1Labels := by
      have ha : raw31751step1 = -raw31751step0 := by apply Matrix.ext; change ∀ i j, raw31751step1 i j = -(raw31751step0 i j); unfold raw31751step1 raw31751step0; decide +kernel
      have hl : raw31751step1Labels = raw31751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31751step1 raw31751step1Labels = mixedMoment B raw31751step2 raw31751step2Labels := by
      have ha : raw31751step2 = raw31751step1 := by apply Matrix.ext; unfold raw31751step2 raw31751step1; decide +kernel
      have hl : raw31751step1Labels = labelEmbedding1 ∘ raw31751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31751step1 raw31751step1Labels raw31751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

theorem canonical31752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31752 raw31752Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw31752 raw31752Labels = mixedMoment B raw31752step0 raw31752step0Labels := by
      have hz : ∀ j, raw31752 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31752step0 = (fun i j => raw31752 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31752step0 raw31752; decide +kernel
      have hl : raw31752step0Labels = raw31752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31752 raw31752Labels permutation434 hz
    mixedMoment B raw31752step0 raw31752step0Labels = mixedMoment B raw31752step1 raw31752step1Labels := by
      have ha : raw31752step1 = (fun i j => raw31752step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31752step1 raw31752step0; decide +kernel
      have hl : raw31752step1Labels = raw31752step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31752step0 raw31752step0Labels permutation33 permutation7
    mixedMoment B raw31752step1 raw31752step1Labels = mixedMoment B raw31752step2 raw31752step2Labels := by
      have ha : raw31752step2 = -raw31752step1 := by apply Matrix.ext; change ∀ i j, raw31752step2 i j = -(raw31752step1 i j); unfold raw31752step2 raw31752step1; decide +kernel
      have hl : raw31752step2Labels = raw31752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31752step2 raw31752step2Labels = mixedMoment B raw31752step3 raw31752step3Labels := by
      have ha : raw31752step3 = raw31752step2 := by apply Matrix.ext; unfold raw31752step3 raw31752step2; decide +kernel
      have hl : raw31752step2Labels = labelEmbedding1 ∘ raw31752step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31752step2 raw31752step2Labels raw31752step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical31753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31753 raw31753Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw31753 raw31753Labels = mixedMoment B raw31753step0 raw31753step0Labels := by
      have hz : ∀ j, raw31753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31753step0 = (fun i j => raw31753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31753step0 raw31753; decide +kernel
      have hl : raw31753step0Labels = raw31753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31753 raw31753Labels permutation434 hz
    mixedMoment B raw31753step0 raw31753step0Labels = mixedMoment B raw31753step1 raw31753step1Labels := by
      have ha : raw31753step1 = (fun i j => raw31753step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31753step1 raw31753step0; decide +kernel
      have hl : raw31753step1Labels = raw31753step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31753step0 raw31753step0Labels permutation33 permutation7
    mixedMoment B raw31753step1 raw31753step1Labels = mixedMoment B raw31753step2 raw31753step2Labels := by
      have ha : raw31753step2 = -raw31753step1 := by apply Matrix.ext; change ∀ i j, raw31753step2 i j = -(raw31753step1 i j); unfold raw31753step2 raw31753step1; decide +kernel
      have hl : raw31753step2Labels = raw31753step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31753step2 raw31753step2Labels = mixedMoment B raw31753step3 raw31753step3Labels := by
      have ha : raw31753step3 = raw31753step2 := by apply Matrix.ext; unfold raw31753step3 raw31753step2; decide +kernel
      have hl : raw31753step2Labels = labelEmbedding1 ∘ raw31753step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31753step2 raw31753step2Labels raw31753step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical31754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31754 raw31754Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw31754 raw31754Labels = mixedMoment B raw31754step0 raw31754step0Labels := by
      have hz : ∀ j, raw31754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31754step0 = (fun i j => raw31754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31754step0 raw31754; decide +kernel
      have hl : raw31754step0Labels = raw31754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31754 raw31754Labels permutation346 hz
    mixedMoment B raw31754step0 raw31754step0Labels = mixedMoment B raw31754step1 raw31754step1Labels := by
      have ha : raw31754step1 = (fun i j => raw31754step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31754step1 raw31754step0; decide +kernel
      have hl : raw31754step1Labels = raw31754step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31754step0 raw31754step0Labels permutation33 permutation7
    mixedMoment B raw31754step1 raw31754step1Labels = mixedMoment B raw31754step2 raw31754step2Labels := by
      have ha : raw31754step2 = -raw31754step1 := by apply Matrix.ext; change ∀ i j, raw31754step2 i j = -(raw31754step1 i j); unfold raw31754step2 raw31754step1; decide +kernel
      have hl : raw31754step2Labels = raw31754step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31754step2 raw31754step2Labels = mixedMoment B raw31754step3 raw31754step3Labels := by
      have ha : raw31754step3 = raw31754step2 := by apply Matrix.ext; unfold raw31754step3 raw31754step2; decide +kernel
      have hl : raw31754step2Labels = labelEmbedding1 ∘ raw31754step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31754step2 raw31754step2Labels raw31754step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

theorem canonical31755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31755 raw31755Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw31755 raw31755Labels = mixedMoment B raw31755step0 raw31755step0Labels := by
      have ha : raw31755step0 = (fun i j => raw31755 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31755step0 raw31755; decide +kernel
      have hl : raw31755step0Labels = raw31755Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31755 raw31755Labels permutation153 permutation7
    mixedMoment B raw31755step0 raw31755step0Labels = mixedMoment B raw31755step1 raw31755step1Labels := by
      have ha : raw31755step1 = -raw31755step0 := by apply Matrix.ext; change ∀ i j, raw31755step1 i j = -(raw31755step0 i j); unfold raw31755step1 raw31755step0; decide +kernel
      have hl : raw31755step1Labels = raw31755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31755step1 raw31755step1Labels = mixedMoment B raw31755step2 raw31755step2Labels := by
      have ha : raw31755step2 = raw31755step1 := by apply Matrix.ext; unfold raw31755step2 raw31755step1; decide +kernel
      have hl : raw31755step1Labels = labelEmbedding1 ∘ raw31755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31755step1 raw31755step1Labels raw31755step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

theorem canonical31756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31756 raw31756Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw31756 raw31756Labels = mixedMoment B raw31756step0 raw31756step0Labels := by
      have hz : ∀ j, raw31756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31756step0 = (fun i j => raw31756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31756step0 raw31756; decide +kernel
      have hl : raw31756step0Labels = raw31756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31756 raw31756Labels permutation346 hz
    mixedMoment B raw31756step0 raw31756step0Labels = mixedMoment B raw31756step1 raw31756step1Labels := by
      have ha : raw31756step1 = (fun i j => raw31756step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31756step1 raw31756step0; decide +kernel
      have hl : raw31756step1Labels = raw31756step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31756step0 raw31756step0Labels permutation33 permutation7
    mixedMoment B raw31756step1 raw31756step1Labels = mixedMoment B raw31756step2 raw31756step2Labels := by
      have ha : raw31756step2 = -raw31756step1 := by apply Matrix.ext; change ∀ i j, raw31756step2 i j = -(raw31756step1 i j); unfold raw31756step2 raw31756step1; decide +kernel
      have hl : raw31756step2Labels = raw31756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31756step2 raw31756step2Labels = mixedMoment B raw31756step3 raw31756step3Labels := by
      have ha : raw31756step3 = raw31756step2 := by apply Matrix.ext; unfold raw31756step3 raw31756step2; decide +kernel
      have hl : raw31756step2Labels = labelEmbedding1 ∘ raw31756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31756step2 raw31756step2Labels raw31756step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical31757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31757 raw31757Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw31757 raw31757Labels = mixedMoment B raw31757step0 raw31757step0Labels := by
      have hz : ∀ j, raw31757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31757step0 = (fun i j => raw31757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31757step0 raw31757; decide +kernel
      have hl : raw31757step0Labels = raw31757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31757 raw31757Labels permutation346 hz
    mixedMoment B raw31757step0 raw31757step0Labels = mixedMoment B raw31757step1 raw31757step1Labels := by
      have ha : raw31757step1 = (fun i j => raw31757step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31757step1 raw31757step0; decide +kernel
      have hl : raw31757step1Labels = raw31757step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31757step0 raw31757step0Labels permutation33 permutation7
    mixedMoment B raw31757step1 raw31757step1Labels = mixedMoment B raw31757step2 raw31757step2Labels := by
      have ha : raw31757step2 = -raw31757step1 := by apply Matrix.ext; change ∀ i j, raw31757step2 i j = -(raw31757step1 i j); unfold raw31757step2 raw31757step1; decide +kernel
      have hl : raw31757step2Labels = raw31757step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31757step2 raw31757step2Labels = mixedMoment B raw31757step3 raw31757step3Labels := by
      have ha : raw31757step3 = raw31757step2 := by apply Matrix.ext; unfold raw31757step3 raw31757step2; decide +kernel
      have hl : raw31757step2Labels = labelEmbedding1 ∘ raw31757step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31757step2 raw31757step2Labels raw31757step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical31758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31758 raw31758Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw31758 raw31758Labels = mixedMoment B raw31758step0 raw31758step0Labels := by
      have hz : ∀ j, raw31758 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31758step0 = (fun i j => raw31758 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31758step0 raw31758; decide +kernel
      have hl : raw31758step0Labels = raw31758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31758 raw31758Labels permutation434 hz
    mixedMoment B raw31758step0 raw31758step0Labels = mixedMoment B raw31758step1 raw31758step1Labels := by
      have hz : ∀ j, raw31758step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31758step1 = (fun i j => raw31758step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31758step1 raw31758step0; decide +kernel
      have hl : raw31758step1Labels = raw31758step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31758step0 raw31758step0Labels permutation80 hz
    mixedMoment B raw31758step1 raw31758step1Labels = mixedMoment B raw31758step2 raw31758step2Labels := by
      have ha : raw31758step2 = (fun i j => raw31758step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31758step2 raw31758step1; decide +kernel
      have hl : raw31758step2Labels = raw31758step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31758step1 raw31758step1Labels permutation9 permutation7
    mixedMoment B raw31758step2 raw31758step2Labels = mixedMoment B raw31758step3 raw31758step3Labels := by
      have ha : raw31758step3 = -raw31758step2 := by apply Matrix.ext; change ∀ i j, raw31758step3 i j = -(raw31758step2 i j); unfold raw31758step3 raw31758step2; decide +kernel
      have hl : raw31758step3Labels = raw31758step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31758step3 raw31758step3Labels = mixedMoment B raw31758step4 raw31758step4Labels := by
      have ha : raw31758step4 = raw31758step3 := by apply Matrix.ext; unfold raw31758step4 raw31758step3; decide +kernel
      have hl : raw31758step3Labels = labelEmbedding1 ∘ raw31758step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31758step3 raw31758step3Labels raw31758step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

theorem canonical31759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31759 raw31759Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw31759 raw31759Labels = mixedMoment B raw31759step0 raw31759step0Labels := by
      have hz : ∀ j, raw31759 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31759step0 = (fun i j => raw31759 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31759step0 raw31759; decide +kernel
      have hl : raw31759step0Labels = raw31759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31759 raw31759Labels permutation434 hz
    mixedMoment B raw31759step0 raw31759step0Labels = mixedMoment B raw31759step1 raw31759step1Labels := by
      have ha : raw31759step1 = (fun i j => raw31759step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31759step1 raw31759step0; decide +kernel
      have hl : raw31759step1Labels = raw31759step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31759step0 raw31759step0Labels permutation33 permutation7
    mixedMoment B raw31759step1 raw31759step1Labels = mixedMoment B raw31759step2 raw31759step2Labels := by
      have ha : raw31759step2 = -raw31759step1 := by apply Matrix.ext; change ∀ i j, raw31759step2 i j = -(raw31759step1 i j); unfold raw31759step2 raw31759step1; decide +kernel
      have hl : raw31759step2Labels = raw31759step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31759step2 raw31759step2Labels = mixedMoment B raw31759step3 raw31759step3Labels := by
      have ha : raw31759step3 = raw31759step2 := by apply Matrix.ext; unfold raw31759step3 raw31759step2; decide +kernel
      have hl : raw31759step2Labels = labelEmbedding1 ∘ raw31759step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31759step2 raw31759step2Labels raw31759step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical31760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31760 raw31760Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw31760 raw31760Labels = mixedMoment B raw31760step0 raw31760step0Labels := by
      have hz : ∀ j, raw31760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31760step0 = (fun i j => raw31760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31760step0 raw31760; decide +kernel
      have hl : raw31760step0Labels = raw31760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31760 raw31760Labels permutation346 hz
    mixedMoment B raw31760step0 raw31760step0Labels = mixedMoment B raw31760step1 raw31760step1Labels := by
      have ha : raw31760step1 = (fun i j => raw31760step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31760step1 raw31760step0; decide +kernel
      have hl : raw31760step1Labels = raw31760step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31760step0 raw31760step0Labels permutation33 permutation7
    mixedMoment B raw31760step1 raw31760step1Labels = mixedMoment B raw31760step2 raw31760step2Labels := by
      have ha : raw31760step2 = -raw31760step1 := by apply Matrix.ext; change ∀ i j, raw31760step2 i j = -(raw31760step1 i j); unfold raw31760step2 raw31760step1; decide +kernel
      have hl : raw31760step2Labels = raw31760step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31760step2 raw31760step2Labels = mixedMoment B raw31760step3 raw31760step3Labels := by
      have ha : raw31760step3 = raw31760step2 := by apply Matrix.ext; unfold raw31760step3 raw31760step2; decide +kernel
      have hl : raw31760step2Labels = labelEmbedding1 ∘ raw31760step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31760step2 raw31760step2Labels raw31760step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical31761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31761 raw31761Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw31761 raw31761Labels = mixedMoment B raw31761step0 raw31761step0Labels := by
      have hz : ∀ j, raw31761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31761step0 = (fun i j => raw31761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31761step0 raw31761; decide +kernel
      have hl : raw31761step0Labels = raw31761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31761 raw31761Labels permutation434 hz
    mixedMoment B raw31761step0 raw31761step0Labels = mixedMoment B raw31761step1 raw31761step1Labels := by
      have hz : ∀ j, raw31761step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31761step1 = (fun i j => raw31761step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31761step1 raw31761step0; decide +kernel
      have hl : raw31761step1Labels = raw31761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31761step0 raw31761step0Labels permutation80 hz
    mixedMoment B raw31761step1 raw31761step1Labels = mixedMoment B raw31761step2 raw31761step2Labels := by
      have ha : raw31761step2 = (fun i j => raw31761step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31761step2 raw31761step1; decide +kernel
      have hl : raw31761step2Labels = raw31761step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31761step1 raw31761step1Labels permutation9 permutation7
    mixedMoment B raw31761step2 raw31761step2Labels = mixedMoment B raw31761step3 raw31761step3Labels := by
      have ha : raw31761step3 = -raw31761step2 := by apply Matrix.ext; change ∀ i j, raw31761step3 i j = -(raw31761step2 i j); unfold raw31761step3 raw31761step2; decide +kernel
      have hl : raw31761step3Labels = raw31761step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31761step3 raw31761step3Labels = mixedMoment B raw31761step4 raw31761step4Labels := by
      have ha : raw31761step4 = raw31761step3 := by apply Matrix.ext; unfold raw31761step4 raw31761step3; decide +kernel
      have hl : raw31761step3Labels = labelEmbedding1 ∘ raw31761step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31761step3 raw31761step3Labels raw31761step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical31762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31762 raw31762Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw31762 raw31762Labels = mixedMoment B raw31762step0 raw31762step0Labels := by
      have hz : ∀ j, raw31762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31762step0 = (fun i j => raw31762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31762step0 raw31762; decide +kernel
      have hl : raw31762step0Labels = raw31762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31762 raw31762Labels permutation434 hz
    mixedMoment B raw31762step0 raw31762step0Labels = mixedMoment B raw31762step1 raw31762step1Labels := by
      have hz : ∀ j, raw31762step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31762step1 = (fun i j => raw31762step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31762step1 raw31762step0; decide +kernel
      have hl : raw31762step1Labels = raw31762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31762step0 raw31762step0Labels permutation80 hz
    mixedMoment B raw31762step1 raw31762step1Labels = mixedMoment B raw31762step2 raw31762step2Labels := by
      have ha : raw31762step2 = (fun i j => raw31762step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31762step2 raw31762step1; decide +kernel
      have hl : raw31762step2Labels = raw31762step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31762step1 raw31762step1Labels permutation9 permutation7
    mixedMoment B raw31762step2 raw31762step2Labels = mixedMoment B raw31762step3 raw31762step3Labels := by
      have ha : raw31762step3 = -raw31762step2 := by apply Matrix.ext; change ∀ i j, raw31762step3 i j = -(raw31762step2 i j); unfold raw31762step3 raw31762step2; decide +kernel
      have hl : raw31762step3Labels = raw31762step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31762step3 raw31762step3Labels = mixedMoment B raw31762step4 raw31762step4Labels := by
      have ha : raw31762step4 = raw31762step3 := by apply Matrix.ext; unfold raw31762step4 raw31762step3; decide +kernel
      have hl : raw31762step3Labels = labelEmbedding1 ∘ raw31762step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31762step3 raw31762step3Labels raw31762step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2169 node2169Labels := by rfl

theorem canonical31763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31763 raw31763Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw31763 raw31763Labels = mixedMoment B raw31763step0 raw31763step0Labels := by
      have hz : ∀ j, raw31763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31763step0 = (fun i j => raw31763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31763step0 raw31763; decide +kernel
      have hl : raw31763step0Labels = raw31763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31763 raw31763Labels permutation434 hz
    mixedMoment B raw31763step0 raw31763step0Labels = mixedMoment B raw31763step1 raw31763step1Labels := by
      have ha : raw31763step1 = (fun i j => raw31763step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31763step1 raw31763step0; decide +kernel
      have hl : raw31763step1Labels = raw31763step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31763step0 raw31763step0Labels permutation33 permutation7
    mixedMoment B raw31763step1 raw31763step1Labels = mixedMoment B raw31763step2 raw31763step2Labels := by
      have ha : raw31763step2 = -raw31763step1 := by apply Matrix.ext; change ∀ i j, raw31763step2 i j = -(raw31763step1 i j); unfold raw31763step2 raw31763step1; decide +kernel
      have hl : raw31763step2Labels = raw31763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31763step2 raw31763step2Labels = mixedMoment B raw31763step3 raw31763step3Labels := by
      have ha : raw31763step3 = raw31763step2 := by apply Matrix.ext; unfold raw31763step3 raw31763step2; decide +kernel
      have hl : raw31763step2Labels = labelEmbedding1 ∘ raw31763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31763step2 raw31763step2Labels raw31763step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

theorem canonical31764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31764 raw31764Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw31764 raw31764Labels = mixedMoment B raw31764step0 raw31764step0Labels := by
      have hz : ∀ j, raw31764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31764step0 = (fun i j => raw31764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31764step0 raw31764; decide +kernel
      have hl : raw31764step0Labels = raw31764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31764 raw31764Labels permutation346 hz
    mixedMoment B raw31764step0 raw31764step0Labels = mixedMoment B raw31764step1 raw31764step1Labels := by
      have ha : raw31764step1 = (fun i j => raw31764step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31764step1 raw31764step0; decide +kernel
      have hl : raw31764step1Labels = raw31764step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31764step0 raw31764step0Labels permutation33 permutation7
    mixedMoment B raw31764step1 raw31764step1Labels = mixedMoment B raw31764step2 raw31764step2Labels := by
      have ha : raw31764step2 = -raw31764step1 := by apply Matrix.ext; change ∀ i j, raw31764step2 i j = -(raw31764step1 i j); unfold raw31764step2 raw31764step1; decide +kernel
      have hl : raw31764step2Labels = raw31764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31764step2 raw31764step2Labels = mixedMoment B raw31764step3 raw31764step3Labels := by
      have ha : raw31764step3 = raw31764step2 := by apply Matrix.ext; unfold raw31764step3 raw31764step2; decide +kernel
      have hl : raw31764step2Labels = labelEmbedding1 ∘ raw31764step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31764step2 raw31764step2Labels raw31764step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

theorem canonical31765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31765 raw31765Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw31765 raw31765Labels = mixedMoment B raw31765step0 raw31765step0Labels := by
      have hz : ∀ j, raw31765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31765step0 = (fun i j => raw31765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31765step0 raw31765; decide +kernel
      have hl : raw31765step0Labels = raw31765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31765 raw31765Labels permutation434 hz
    mixedMoment B raw31765step0 raw31765step0Labels = mixedMoment B raw31765step1 raw31765step1Labels := by
      have hz : ∀ j, raw31765step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31765step1 = (fun i j => raw31765step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31765step1 raw31765step0; decide +kernel
      have hl : raw31765step1Labels = raw31765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31765step0 raw31765step0Labels permutation80 hz
    mixedMoment B raw31765step1 raw31765step1Labels = mixedMoment B raw31765step2 raw31765step2Labels := by
      have ha : raw31765step2 = (fun i j => raw31765step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31765step2 raw31765step1; decide +kernel
      have hl : raw31765step2Labels = raw31765step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31765step1 raw31765step1Labels permutation9 permutation2
    _ = mixedMoment B node3397 node3397Labels := by rfl

theorem canonical31766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31766 raw31766Labels = mixedMoment B node2066 node2066Labels := by
  calc
    mixedMoment B raw31766 raw31766Labels = mixedMoment B raw31766step0 raw31766step0Labels := by
      have hz : ∀ j, raw31766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31766step0 = (fun i j => raw31766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31766step0 raw31766; decide +kernel
      have hl : raw31766step0Labels = raw31766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31766 raw31766Labels permutation434 hz
    mixedMoment B raw31766step0 raw31766step0Labels = mixedMoment B raw31766step1 raw31766step1Labels := by
      have hz : ∀ j, raw31766step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31766step1 = (fun i j => raw31766step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31766step1 raw31766step0; decide +kernel
      have hl : raw31766step1Labels = raw31766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31766step0 raw31766step0Labels permutation80 hz
    mixedMoment B raw31766step1 raw31766step1Labels = mixedMoment B raw31766step2 raw31766step2Labels := by
      have ha : raw31766step2 = (fun i j => raw31766step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31766step2 raw31766step1; decide +kernel
      have hl : raw31766step2Labels = raw31766step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31766step1 raw31766step1Labels permutation9 permutation2
    _ = mixedMoment B node2066 node2066Labels := by rfl

theorem canonical31767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31767 raw31767Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw31767 raw31767Labels = mixedMoment B raw31767step0 raw31767step0Labels := by
      have hz : ∀ j, raw31767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31767step0 = (fun i j => raw31767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31767step0 raw31767; decide +kernel
      have hl : raw31767step0Labels = raw31767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31767 raw31767Labels permutation434 hz
    mixedMoment B raw31767step0 raw31767step0Labels = mixedMoment B raw31767step1 raw31767step1Labels := by
      have ha : raw31767step1 = (fun i j => raw31767step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31767step1 raw31767step0; decide +kernel
      have hl : raw31767step1Labels = raw31767step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31767step0 raw31767step0Labels permutation33 permutation2
    _ = mixedMoment B node1810 node1810Labels := by rfl

theorem canonical31768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31768 raw31768Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw31768 raw31768Labels = mixedMoment B raw31768step0 raw31768step0Labels := by
      have hz : ∀ j, raw31768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31768step0 = (fun i j => raw31768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31768step0 raw31768; decide +kernel
      have hl : raw31768step0Labels = raw31768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31768 raw31768Labels permutation346 hz
    mixedMoment B raw31768step0 raw31768step0Labels = mixedMoment B raw31768step1 raw31768step1Labels := by
      have ha : raw31768step1 = (fun i j => raw31768step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31768step1 raw31768step0; decide +kernel
      have hl : raw31768step1Labels = raw31768step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31768step0 raw31768step0Labels permutation33 permutation2
    _ = mixedMoment B node1810 node1810Labels := by rfl

theorem canonical31769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31769 raw31769Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw31769 raw31769Labels = mixedMoment B raw31769step0 raw31769step0Labels := by
      have hz : ∀ j, raw31769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31769step0 = (fun i j => raw31769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31769step0 raw31769; decide +kernel
      have hl : raw31769step0Labels = raw31769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31769 raw31769Labels permutation434 hz
    mixedMoment B raw31769step0 raw31769step0Labels = mixedMoment B raw31769step1 raw31769step1Labels := by
      have hz : ∀ j, raw31769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31769step1 = (fun i j => raw31769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31769step1 raw31769step0; decide +kernel
      have hl : raw31769step1Labels = raw31769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31769step0 raw31769step0Labels permutation80 hz
    mixedMoment B raw31769step1 raw31769step1Labels = mixedMoment B raw31769step2 raw31769step2Labels := by
      have ha : raw31769step2 = (fun i j => raw31769step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31769step2 raw31769step1; decide +kernel
      have hl : raw31769step2Labels = raw31769step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31769step1 raw31769step1Labels permutation9 permutation2
    _ = mixedMoment B node1818 node1818Labels := by rfl

theorem canonical31770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31770 raw31770Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw31770 raw31770Labels = mixedMoment B raw31770step0 raw31770step0Labels := by
      have hz : ∀ j, raw31770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31770step0 = (fun i j => raw31770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31770step0 raw31770; decide +kernel
      have hl : raw31770step0Labels = raw31770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31770 raw31770Labels permutation434 hz
    mixedMoment B raw31770step0 raw31770step0Labels = mixedMoment B raw31770step1 raw31770step1Labels := by
      have hz : ∀ j, raw31770step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31770step1 = (fun i j => raw31770step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31770step1 raw31770step0; decide +kernel
      have hl : raw31770step1Labels = raw31770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31770step0 raw31770step0Labels permutation80 hz
    _ = mixedMoment B node1819 node1819Labels := by rfl

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

theorem canonical31877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31877 raw31877Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw31877 raw31877Labels = mixedMoment B raw31877step0 raw31877step0Labels := by
      have hz : ∀ j, raw31877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31877step0 = (fun i j => raw31877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31877step0 raw31877; decide +kernel
      have hl : raw31877step0Labels = raw31877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31877 raw31877Labels permutation434 hz
    mixedMoment B raw31877step0 raw31877step0Labels = mixedMoment B raw31877step1 raw31877step1Labels := by
      have hz : ∀ i, raw31877step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31877step1 = (fun i j => raw31877step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31877step1 raw31877step0; decide +kernel
      have hl : raw31877step1Labels = (fun j => raw31877step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31877step0 raw31877step0Labels permutation6 hz
    _ = mixedMoment B node4075 node4075Labels := by rfl

theorem canonical31878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31878 raw31878Labels = mixedMoment B node4078 node4078Labels := by
  calc
    mixedMoment B raw31878 raw31878Labels = mixedMoment B raw31878step0 raw31878step0Labels := by
      have hz : ∀ i, raw31878 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31878step0 = (fun i j => raw31878 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31878step0 raw31878; decide +kernel
      have hl : raw31878step0Labels = (fun j => raw31878Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31878 raw31878Labels permutation6 hz
    mixedMoment B raw31878step0 raw31878step0Labels = mixedMoment B raw31878step1 raw31878step1Labels := by
      have ha : raw31878step1 = (fun i j => raw31878step0 (permutation158 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31878step1 raw31878step0; decide +kernel
      have hl : raw31878step1Labels = raw31878step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31878step0 raw31878step0Labels permutation158 permutation0
    _ = mixedMoment B node4078 node4078Labels := by rfl

theorem canonical31879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31879 raw31879Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw31879 raw31879Labels = mixedMoment B raw31879step0 raw31879step0Labels := by
      have hz : ∀ j, raw31879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31879step0 = (fun i j => raw31879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31879step0 raw31879; decide +kernel
      have hl : raw31879step0Labels = raw31879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31879 raw31879Labels permutation434 hz
    mixedMoment B raw31879step0 raw31879step0Labels = mixedMoment B raw31879step1 raw31879step1Labels := by
      have hz : ∀ i, raw31879step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31879step1 = (fun i j => raw31879step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31879step1 raw31879step0; decide +kernel
      have hl : raw31879step1Labels = (fun j => raw31879step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31879step0 raw31879step0Labels permutation6 hz
    mixedMoment B raw31879step1 raw31879step1Labels = mixedMoment B raw31879step2 raw31879step2Labels := by
      have ha : raw31879step2 = (fun i j => raw31879step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31879step2 raw31879step1; decide +kernel
      have hl : raw31879step2Labels = raw31879step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31879step1 raw31879step1Labels permutation33 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

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

theorem canonical31882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31882 raw31882Labels = mixedMoment B node4076 node4076Labels := by
  calc
    mixedMoment B raw31882 raw31882Labels = mixedMoment B raw31882step0 raw31882step0Labels := by
      have hz : ∀ j, raw31882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31882step0 = (fun i j => raw31882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31882step0 raw31882; decide +kernel
      have hl : raw31882step0Labels = raw31882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31882 raw31882Labels permutation434 hz
    mixedMoment B raw31882step0 raw31882step0Labels = mixedMoment B raw31882step1 raw31882step1Labels := by
      have hz : ∀ j, raw31882step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31882step1 = (fun i j => raw31882step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31882step1 raw31882step0; decide +kernel
      have hl : raw31882step1Labels = raw31882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31882step0 raw31882step0Labels permutation80 hz
    mixedMoment B raw31882step1 raw31882step1Labels = mixedMoment B raw31882step2 raw31882step2Labels := by
      have hz : ∀ i, raw31882step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31882step2 = (fun i j => raw31882step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31882step2 raw31882step1; decide +kernel
      have hl : raw31882step2Labels = (fun j => raw31882step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31882step1 raw31882step1Labels permutation6 hz
    mixedMoment B raw31882step2 raw31882step2Labels = mixedMoment B raw31882step3 raw31882step3Labels := by
      have ha : raw31882step3 = (fun i j => raw31882step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31882step3 raw31882step2; decide +kernel
      have hl : raw31882step3Labels = raw31882step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31882step2 raw31882step2Labels permutation9 permutation0
    _ = mixedMoment B node4076 node4076Labels := by rfl

theorem canonical31883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31883 raw31883Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw31883 raw31883Labels = mixedMoment B raw31883step0 raw31883step0Labels := by
      have hz : ∀ j, raw31883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31883step0 = (fun i j => raw31883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31883step0 raw31883; decide +kernel
      have hl : raw31883step0Labels = raw31883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31883 raw31883Labels permutation434 hz
    mixedMoment B raw31883step0 raw31883step0Labels = mixedMoment B raw31883step1 raw31883step1Labels := by
      have hz : ∀ i, raw31883step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31883step1 = (fun i j => raw31883step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31883step1 raw31883step0; decide +kernel
      have hl : raw31883step1Labels = (fun j => raw31883step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31883step0 raw31883step0Labels permutation6 hz
    mixedMoment B raw31883step1 raw31883step1Labels = mixedMoment B raw31883step2 raw31883step2Labels := by
      have ha : raw31883step2 = (fun i j => raw31883step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31883step2 raw31883step1; decide +kernel
      have hl : raw31883step2Labels = raw31883step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31883step1 raw31883step1Labels permutation125 permutation0
    mixedMoment B raw31883step2 raw31883step2Labels = mixedMoment B raw31883step3 raw31883step3Labels := by
      have ha : raw31883step3 = -raw31883step2 := by apply Matrix.ext; change ∀ i j, raw31883step3 i j = -(raw31883step2 i j); unfold raw31883step3 raw31883step2; decide +kernel
      have hl : raw31883step3Labels = raw31883step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

theorem canonical31884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31884 raw31884Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw31884 raw31884Labels = mixedMoment B raw31884step0 raw31884step0Labels := by
      have hz : ∀ j, raw31884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31884step0 = (fun i j => raw31884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31884step0 raw31884; decide +kernel
      have hl : raw31884step0Labels = raw31884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31884 raw31884Labels permutation346 hz
    mixedMoment B raw31884step0 raw31884step0Labels = mixedMoment B raw31884step1 raw31884step1Labels := by
      have hz : ∀ i, raw31884step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31884step1 = (fun i j => raw31884step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31884step1 raw31884step0; decide +kernel
      have hl : raw31884step1Labels = (fun j => raw31884step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31884step0 raw31884step0Labels permutation6 hz
    mixedMoment B raw31884step1 raw31884step1Labels = mixedMoment B raw31884step2 raw31884step2Labels := by
      have ha : raw31884step2 = (fun i j => raw31884step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31884step2 raw31884step1; decide +kernel
      have hl : raw31884step2Labels = raw31884step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31884step1 raw31884step1Labels permutation125 permutation0
    mixedMoment B raw31884step2 raw31884step2Labels = mixedMoment B raw31884step3 raw31884step3Labels := by
      have ha : raw31884step3 = -raw31884step2 := by apply Matrix.ext; change ∀ i j, raw31884step3 i j = -(raw31884step2 i j); unfold raw31884step3 raw31884step2; decide +kernel
      have hl : raw31884step3Labels = raw31884step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

theorem canonical31885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31885 raw31885Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw31885 raw31885Labels = mixedMoment B raw31885step0 raw31885step0Labels := by
      have hz : ∀ j, raw31885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31885step0 = (fun i j => raw31885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31885step0 raw31885; decide +kernel
      have hl : raw31885step0Labels = raw31885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31885 raw31885Labels permutation434 hz
    mixedMoment B raw31885step0 raw31885step0Labels = mixedMoment B raw31885step1 raw31885step1Labels := by
      have hz : ∀ j, raw31885step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31885step1 = (fun i j => raw31885step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31885step1 raw31885step0; decide +kernel
      have hl : raw31885step1Labels = raw31885step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31885step0 raw31885step0Labels permutation80 hz
    mixedMoment B raw31885step1 raw31885step1Labels = mixedMoment B raw31885step2 raw31885step2Labels := by
      have hz : ∀ i, raw31885step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31885step2 = (fun i j => raw31885step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31885step2 raw31885step1; decide +kernel
      have hl : raw31885step2Labels = (fun j => raw31885step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31885step1 raw31885step1Labels permutation6 hz
    mixedMoment B raw31885step2 raw31885step2Labels = mixedMoment B raw31885step3 raw31885step3Labels := by
      have ha : raw31885step3 = (fun i j => raw31885step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31885step3 raw31885step2; decide +kernel
      have hl : raw31885step3Labels = raw31885step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31885step2 raw31885step2Labels permutation9 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical31886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31886 raw31886Labels = mixedMoment B node1806 node1806Labels := by
  calc
    mixedMoment B raw31886 raw31886Labels = mixedMoment B raw31886step0 raw31886step0Labels := by
      have ha : raw31886step0 = (fun i j => raw31886 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31886step0 raw31886; decide +kernel
      have hl : raw31886step0Labels = raw31886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31886 raw31886Labels permutation158 permutation2
    _ = mixedMoment B node1806 node1806Labels := by rfl

theorem canonical31887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31887 raw31887Labels = mixedMoment B node2034 node2034Labels := by
  calc
    mixedMoment B raw31887 raw31887Labels = mixedMoment B raw31887step0 raw31887step0Labels := by
      have ha : raw31887step0 = (fun i j => raw31887 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31887step0 raw31887; decide +kernel
      have hl : raw31887step0Labels = raw31887Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31887 raw31887Labels permutation166 permutation2
    _ = mixedMoment B node2034 node2034Labels := by rfl

theorem canonical31888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31888 raw31888Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw31888 raw31888Labels = mixedMoment B raw31888step0 raw31888step0Labels := by
      have ha : raw31888step0 = (fun i j => raw31888 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31888step0 raw31888; decide +kernel
      have hl : raw31888step0Labels = raw31888Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31888 raw31888Labels permutation162 permutation2
    _ = mixedMoment B node2051 node2051Labels := by rfl

theorem canonical31889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31889 raw31889Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw31889 raw31889Labels = mixedMoment B raw31889step0 raw31889step0Labels := by
      have ha : raw31889step0 = (fun i j => raw31889 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31889step0 raw31889; decide +kernel
      have hl : raw31889step0Labels = raw31889Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31889 raw31889Labels permutation662 permutation2
    mixedMoment B raw31889step0 raw31889step0Labels = mixedMoment B raw31889step1 raw31889step1Labels := by
      have ha : raw31889step1 = -raw31889step0 := by apply Matrix.ext; change ∀ i j, raw31889step1 i j = -(raw31889step0 i j); unfold raw31889step1 raw31889step0; decide +kernel
      have hl : raw31889step1Labels = raw31889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3789 node3789Labels := by rfl

theorem canonical31890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31890 raw31890Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw31890 raw31890Labels = mixedMoment B raw31890step0 raw31890step0Labels := by
      have ha : raw31890step0 = (fun i j => raw31890 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31890step0 raw31890; decide +kernel
      have hl : raw31890step0Labels = raw31890Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31890 raw31890Labels permutation178 permutation2
    _ = mixedMoment B node3202 node3202Labels := by rfl

theorem canonical31891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31891 raw31891Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw31891 raw31891Labels = mixedMoment B raw31891step0 raw31891step0Labels := by
      have ha : raw31891step0 = (fun i j => raw31891 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31891step0 raw31891; decide +kernel
      have hl : raw31891step0Labels = raw31891Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31891 raw31891Labels permutation154 permutation2
    _ = mixedMoment B node3202 node3202Labels := by rfl

theorem canonical31892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31892 raw31892Labels = mixedMoment B node3189 node3189Labels := by
  calc
    mixedMoment B raw31892 raw31892Labels = mixedMoment B raw31892step0 raw31892step0Labels := by
      have ha : raw31892step0 = (fun i j => raw31892 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31892step0 raw31892; decide +kernel
      have hl : raw31892step0Labels = raw31892Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31892 raw31892Labels permutation154 permutation2
    _ = mixedMoment B node3189 node3189Labels := by rfl

theorem canonical31893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31893 raw31893Labels = mixedMoment B node3062 node3062Labels := by
  calc
    mixedMoment B raw31893 raw31893Labels = mixedMoment B raw31893step0 raw31893step0Labels := by
      have ha : raw31893step0 = (fun i j => raw31893 (permutation533 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31893step0 raw31893; decide +kernel
      have hl : raw31893step0Labels = raw31893Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31893 raw31893Labels permutation533 permutation4
    _ = mixedMoment B node3062 node3062Labels := by rfl

theorem canonical31894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31894 raw31894Labels = mixedMoment B node2440 node2440Labels := by
  calc
    mixedMoment B raw31894 raw31894Labels = mixedMoment B raw31894step0 raw31894step0Labels := by
      have ha : raw31894step0 = (fun i j => raw31894 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31894step0 raw31894; decide +kernel
      have hl : raw31894step0Labels = raw31894Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31894 raw31894Labels permutation662 permutation2
    mixedMoment B raw31894step0 raw31894step0Labels = mixedMoment B raw31894step1 raw31894step1Labels := by
      have ha : raw31894step1 = -raw31894step0 := by apply Matrix.ext; change ∀ i j, raw31894step1 i j = -(raw31894step0 i j); unfold raw31894step1 raw31894step0; decide +kernel
      have hl : raw31894step1Labels = raw31894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2440 node2440Labels := by rfl

theorem canonical31895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31895 raw31895Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw31895 raw31895Labels = mixedMoment B raw31895step0 raw31895step0Labels := by
      have hz : ∀ j, raw31895 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw31895step0 = (fun i j => raw31895 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw31895step0 raw31895; decide +kernel
      have hl : raw31895step0Labels = raw31895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31895 raw31895Labels permutation152 hz
    mixedMoment B raw31895step0 raw31895step0Labels = mixedMoment B raw31895step1 raw31895step1Labels := by
      have ha : raw31895step1 = (fun i j => raw31895step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31895step1 raw31895step0; decide +kernel
      have hl : raw31895step1Labels = raw31895step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31895step0 raw31895step0Labels permutation140 permutation0
    mixedMoment B raw31895step1 raw31895step1Labels = mixedMoment B raw31895step2 raw31895step2Labels := by
      have ha : raw31895step2 = -raw31895step1 := by apply Matrix.ext; change ∀ i j, raw31895step2 i j = -(raw31895step1 i j); unfold raw31895step2 raw31895step1; decide +kernel
      have hl : raw31895step2Labels = raw31895step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical31903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31903 raw31903Labels = mixedMoment B node1803 node1803Labels := by
  calc
    mixedMoment B raw31903 raw31903Labels = mixedMoment B raw31903step0 raw31903step0Labels := by
      have ha : raw31903step0 = (fun i j => raw31903 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31903step0 raw31903; decide +kernel
      have hl : raw31903step0Labels = raw31903Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31903 raw31903Labels permutation160 permutation2
    _ = mixedMoment B node1803 node1803Labels := by rfl

theorem canonical31904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31904 raw31904Labels = mixedMoment B node2033 node2033Labels := by
  calc
    _ = mixedMoment B node2033 node2033Labels := by rfl

theorem canonical31905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31905 raw31905Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw31905 raw31905Labels = mixedMoment B raw31905step0 raw31905step0Labels := by
      have hz : ∀ j, raw31905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31905step0 = (fun i j => raw31905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31905step0 raw31905; decide +kernel
      have hl : raw31905step0Labels = raw31905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31905 raw31905Labels permutation434 hz
    mixedMoment B raw31905step0 raw31905step0Labels = mixedMoment B raw31905step1 raw31905step1Labels := by
      have ha : raw31905step1 = (fun i j => raw31905step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31905step1 raw31905step0; decide +kernel
      have hl : raw31905step1Labels = raw31905step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31905step0 raw31905step0Labels permutation34 permutation2
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical31906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31906 raw31906Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw31906 raw31906Labels = mixedMoment B raw31906step0 raw31906step0Labels := by
      have hz : ∀ j, raw31906 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw31906step0 = (fun i j => raw31906 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw31906step0 raw31906; decide +kernel
      have hl : raw31906step0Labels = raw31906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31906 raw31906Labels permutation520 hz
    mixedMoment B raw31906step0 raw31906step0Labels = mixedMoment B raw31906step1 raw31906step1Labels := by
      have ha : raw31906step1 = (fun i j => raw31906step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31906step1 raw31906step0; decide +kernel
      have hl : raw31906step1Labels = raw31906step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31906step0 raw31906step0Labels permutation34 permutation2
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical31907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31907 raw31907Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw31907 raw31907Labels = mixedMoment B raw31907step0 raw31907step0Labels := by
      have ha : raw31907step0 = (fun i j => raw31907 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31907step0 raw31907; decide +kernel
      have hl : raw31907step0Labels = raw31907Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31907 raw31907Labels permutation161 permutation2
    _ = mixedMoment B node2051 node2051Labels := by rfl

theorem canonical31908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31908 raw31908Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw31908 raw31908Labels = mixedMoment B raw31908step0 raw31908step0Labels := by
      have ha : raw31908step0 = (fun i j => raw31908 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31908step0 raw31908; decide +kernel
      have hl : raw31908step0Labels = raw31908Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31908 raw31908Labels permutation662 permutation2
    mixedMoment B raw31908step0 raw31908step0Labels = mixedMoment B raw31908step1 raw31908step1Labels := by
      have ha : raw31908step1 = -raw31908step0 := by apply Matrix.ext; change ∀ i j, raw31908step1 i j = -(raw31908step0 i j); unfold raw31908step1 raw31908step0; decide +kernel
      have hl : raw31908step1Labels = raw31908step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

theorem canonical31909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31909 raw31909Labels = mixedMoment B node3172 node3172Labels := by
  calc
    mixedMoment B raw31909 raw31909Labels = mixedMoment B raw31909step0 raw31909step0Labels := by
      have ha : raw31909step0 = (fun i j => raw31909 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31909step0 raw31909; decide +kernel
      have hl : raw31909step0Labels = raw31909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31909 raw31909Labels permutation176 permutation2
    _ = mixedMoment B node3172 node3172Labels := by rfl

theorem canonical31910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31910 raw31910Labels = mixedMoment B node3197 node3197Labels := by
  calc
    _ = mixedMoment B node3197 node3197Labels := by rfl

theorem canonical31911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31911 raw31911Labels = mixedMoment B node3164 node3164Labels := by
  calc
    mixedMoment B raw31911 raw31911Labels = mixedMoment B raw31911step0 raw31911step0Labels := by
      have ha : raw31911step0 = (fun i j => raw31911 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31911step0 raw31911; decide +kernel
      have hl : raw31911step0Labels = raw31911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31911 raw31911Labels permutation178 permutation2
    _ = mixedMoment B node3164 node3164Labels := by rfl

theorem canonical31912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31912 raw31912Labels = mixedMoment B node3164 node3164Labels := by
  calc
    mixedMoment B raw31912 raw31912Labels = mixedMoment B raw31912step0 raw31912step0Labels := by
      have ha : raw31912step0 = (fun i j => raw31912 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31912step0 raw31912; decide +kernel
      have hl : raw31912step0Labels = raw31912Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31912 raw31912Labels permutation176 permutation2
    _ = mixedMoment B node3164 node3164Labels := by rfl

theorem canonical31913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31913 raw31913Labels = mixedMoment B node2895 node2895Labels := by
  calc
    mixedMoment B raw31913 raw31913Labels = mixedMoment B raw31913step0 raw31913step0Labels := by
      have ha : raw31913step0 = (fun i j => raw31913 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31913step0 raw31913; decide +kernel
      have hl : raw31913step0Labels = raw31913Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31913 raw31913Labels permutation662 permutation2
    mixedMoment B raw31913step0 raw31913step0Labels = mixedMoment B raw31913step1 raw31913step1Labels := by
      have ha : raw31913step1 = -raw31913step0 := by apply Matrix.ext; change ∀ i j, raw31913step1 i j = -(raw31913step0 i j); unfold raw31913step1 raw31913step0; decide +kernel
      have hl : raw31913step1Labels = raw31913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2895 node2895Labels := by rfl

theorem canonical31914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31914 raw31914Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw31914 raw31914Labels = mixedMoment B raw31914step0 raw31914step0Labels := by
      have hz : ∀ j, raw31914 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw31914step0 = (fun i j => raw31914 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw31914step0 raw31914; decide +kernel
      have hl : raw31914step0Labels = raw31914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31914 raw31914Labels permutation152 hz
    mixedMoment B raw31914step0 raw31914step0Labels = mixedMoment B raw31914step1 raw31914step1Labels := by
      have ha : raw31914step1 = (fun i j => raw31914step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31914step1 raw31914step0; decide +kernel
      have hl : raw31914step1Labels = raw31914step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31914step0 raw31914step0Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical31921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31921 raw31921Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw31921 raw31921Labels = mixedMoment B raw31921step0 raw31921step0Labels := by
      have ha : raw31921step0 = (fun i j => raw31921 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31921step0 raw31921; decide +kernel
      have hl : raw31921step0Labels = raw31921Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31921 raw31921Labels permutation662 permutation2
    mixedMoment B raw31921step0 raw31921step0Labels = mixedMoment B raw31921step1 raw31921step1Labels := by
      have ha : raw31921step1 = -raw31921step0 := by apply Matrix.ext; change ∀ i j, raw31921step1 i j = -(raw31921step0 i j); unfold raw31921step1 raw31921step0; decide +kernel
      have hl : raw31921step1Labels = raw31921step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

theorem canonical31922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31922 raw31922Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw31922 raw31922Labels = mixedMoment B raw31922step0 raw31922step0Labels := by
      have ha : raw31922step0 = (fun i j => raw31922 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31922step0 raw31922; decide +kernel
      have hl : raw31922step0Labels = raw31922Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31922 raw31922Labels permutation178 permutation2
    _ = mixedMoment B node3170 node3170Labels := by rfl

theorem canonical31923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31923 raw31923Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw31923 raw31923Labels = mixedMoment B raw31923step0 raw31923step0Labels := by
      have ha : raw31923step0 = (fun i j => raw31923 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31923step0 raw31923; decide +kernel
      have hl : raw31923step0Labels = raw31923Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31923 raw31923Labels permutation154 permutation2
    _ = mixedMoment B node3196 node3196Labels := by rfl

theorem canonical31924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31924 raw31924Labels = mixedMoment B node3162 node3162Labels := by
  calc
    mixedMoment B raw31924 raw31924Labels = mixedMoment B raw31924step0 raw31924step0Labels := by
      have ha : raw31924step0 = (fun i j => raw31924 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31924step0 raw31924; decide +kernel
      have hl : raw31924step0Labels = raw31924Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31924 raw31924Labels permutation178 permutation2
    _ = mixedMoment B node3162 node3162Labels := by rfl

theorem canonical31925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31925 raw31925Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw31925 raw31925Labels = mixedMoment B raw31925step0 raw31925step0Labels := by
      have ha : raw31925step0 = (fun i j => raw31925 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31925step0 raw31925; decide +kernel
      have hl : raw31925step0Labels = raw31925Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31925 raw31925Labels permutation176 permutation2
    _ = mixedMoment B node3163 node3163Labels := by rfl

theorem canonical31926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31926 raw31926Labels = mixedMoment B node2430 node2430Labels := by
  calc
    mixedMoment B raw31926 raw31926Labels = mixedMoment B raw31926step0 raw31926step0Labels := by
      have ha : raw31926step0 = (fun i j => raw31926 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31926step0 raw31926; decide +kernel
      have hl : raw31926step0Labels = raw31926Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31926 raw31926Labels permutation662 permutation2
    mixedMoment B raw31926step0 raw31926step0Labels = mixedMoment B raw31926step1 raw31926step1Labels := by
      have ha : raw31926step1 = -raw31926step0 := by apply Matrix.ext; change ∀ i j, raw31926step1 i j = -(raw31926step0 i j); unfold raw31926step1 raw31926step0; decide +kernel
      have hl : raw31926step1Labels = raw31926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2430 node2430Labels := by rfl

theorem canonical31927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31927 raw31927Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw31927 raw31927Labels = mixedMoment B raw31927step0 raw31927step0Labels := by
      have hz : ∀ j, raw31927 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw31927step0 = (fun i j => raw31927 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw31927step0 raw31927; decide +kernel
      have hl : raw31927step0Labels = raw31927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31927 raw31927Labels permutation520 hz
    mixedMoment B raw31927step0 raw31927step0Labels = mixedMoment B raw31927step1 raw31927step1Labels := by
      have hz : ∀ j, raw31927step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw31927step1 = (fun i j => raw31927step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw31927step1 raw31927step0; decide +kernel
      have hl : raw31927step1Labels = raw31927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31927step0 raw31927step0Labels permutation32 hz
    mixedMoment B raw31927step1 raw31927step1Labels = mixedMoment B raw31927step2 raw31927step2Labels := by
      have ha : raw31927step2 = (fun i j => raw31927step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31927step2 raw31927step1; decide +kernel
      have hl : raw31927step2Labels = raw31927step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31927step1 raw31927step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

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

theorem canonical3335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3335 raw3335Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw3335 raw3335Labels = mixedMoment B raw3335step0 raw3335step0Labels := by
      have hz : ∀ j, raw3335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3335step0 = (fun i j => raw3335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3335step0 raw3335; decide +kernel
      have hl : raw3335step0Labels = raw3335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335 raw3335Labels permutation434 hz
    mixedMoment B raw3335step0 raw3335step0Labels = mixedMoment B raw3335step1 raw3335step1Labels := by
      have hz : ∀ j, raw3335step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3335step1 = (fun i j => raw3335step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3335step1 raw3335step0; decide +kernel
      have hl : raw3335step1Labels = raw3335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335step0 raw3335step0Labels permutation80 hz
    mixedMoment B raw3335step1 raw3335step1Labels = mixedMoment B raw3335step2 raw3335step2Labels := by
      have hz : ∀ j, raw3335step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3335step2 = (fun i j => raw3335step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3335step2 raw3335step1; decide +kernel
      have hl : raw3335step2Labels = raw3335step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335step1 raw3335step1Labels permutation14 hz
    mixedMoment B raw3335step2 raw3335step2Labels = mixedMoment B raw3335step3 raw3335step3Labels := by
      have hz : ∀ i, raw3335step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3335step3 = (fun i j => raw3335step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3335step3 raw3335step2; decide +kernel
      have hl : raw3335step3Labels = (fun j => raw3335step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3335step2 raw3335step2Labels permutation6 hz
    mixedMoment B raw3335step3 raw3335step3Labels = mixedMoment B raw3335step4 raw3335step4Labels := by
      have ha : raw3335step4 = (fun i j => raw3335step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3335step4 raw3335step3; decide +kernel
      have hl : raw3335step4Labels = raw3335step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3335step3 raw3335step3Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical3336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3336 raw3336Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3336 raw3336Labels = mixedMoment B raw3336step0 raw3336step0Labels := by
      have hz : ∀ j, raw3336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3336step0 = (fun i j => raw3336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3336step0 raw3336; decide +kernel
      have hl : raw3336step0Labels = raw3336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3336 raw3336Labels permutation434 hz
    mixedMoment B raw3336step0 raw3336step0Labels = mixedMoment B raw3336step1 raw3336step1Labels := by
      have hz : ∀ j, raw3336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3336step1 = (fun i j => raw3336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3336step1 raw3336step0; decide +kernel
      have hl : raw3336step1Labels = raw3336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3336step0 raw3336step0Labels permutation80 hz
    mixedMoment B raw3336step1 raw3336step1Labels = mixedMoment B raw3336step2 raw3336step2Labels := by
      have hz : ∀ i, raw3336step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3336step2 = (fun i j => raw3336step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3336step2 raw3336step1; decide +kernel
      have hl : raw3336step2Labels = (fun j => raw3336step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3336step1 raw3336step1Labels permutation6 hz
    mixedMoment B raw3336step2 raw3336step2Labels = mixedMoment B raw3336step3 raw3336step3Labels := by
      have ha : raw3336step3 = (fun i j => raw3336step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3336step3 raw3336step2; decide +kernel
      have hl : raw3336step3Labels = raw3336step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3336step2 raw3336step2Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3517 raw3517Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw3517 raw3517Labels = mixedMoment B raw3517step0 raw3517step0Labels := by
      have hz : ∀ j, raw3517 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3517step0 = (fun i j => raw3517 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3517step0 raw3517; decide +kernel
      have hl : raw3517step0Labels = raw3517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517 raw3517Labels permutation590 hz
    mixedMoment B raw3517step0 raw3517step0Labels = mixedMoment B raw3517step1 raw3517step1Labels := by
      have hz : ∀ j, raw3517step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3517step1 = (fun i j => raw3517step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3517step1 raw3517step0; decide +kernel
      have hl : raw3517step1Labels = raw3517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step0 raw3517step0Labels permutation104 hz
    mixedMoment B raw3517step1 raw3517step1Labels = mixedMoment B raw3517step2 raw3517step2Labels := by
      have hz : ∀ j, raw3517step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3517step2 = (fun i j => raw3517step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3517step2 raw3517step1; decide +kernel
      have hl : raw3517step2Labels = raw3517step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step1 raw3517step1Labels permutation20 hz
    mixedMoment B raw3517step2 raw3517step2Labels = mixedMoment B raw3517step3 raw3517step3Labels := by
      have hz : ∀ j, raw3517step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3517step3 = (fun i j => raw3517step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3517step3 raw3517step2; decide +kernel
      have hl : raw3517step3Labels = raw3517step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step2 raw3517step2Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

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

theorem canonical11540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11540 raw11540Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw11540 raw11540Labels = mixedMoment B raw11540step0 raw11540step0Labels := by
      have hz : ∀ j, raw11540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11540step0 = (fun i j => raw11540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11540step0 raw11540; decide +kernel
      have hl : raw11540step0Labels = raw11540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540 raw11540Labels permutation434 hz
    mixedMoment B raw11540step0 raw11540step0Labels = mixedMoment B raw11540step1 raw11540step1Labels := by
      have hz : ∀ j, raw11540step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11540step1 = (fun i j => raw11540step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11540step1 raw11540step0; decide +kernel
      have hl : raw11540step1Labels = raw11540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540step0 raw11540step0Labels permutation80 hz
    mixedMoment B raw11540step1 raw11540step1Labels = mixedMoment B raw11540step2 raw11540step2Labels := by
      have hz : ∀ j, raw11540step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11540step2 = (fun i j => raw11540step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11540step2 raw11540step1; decide +kernel
      have hl : raw11540step2Labels = raw11540step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540step1 raw11540step1Labels permutation14 hz
    mixedMoment B raw11540step2 raw11540step2Labels = mixedMoment B raw11540step3 raw11540step3Labels := by
      have hz : ∀ i, raw11540step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11540step3 = (fun i j => raw11540step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11540step3 raw11540step2; decide +kernel
      have hl : raw11540step3Labels = (fun j => raw11540step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11540step2 raw11540step2Labels permutation6 hz
    _ = mixedMoment B node4071 node4071Labels := by rfl

theorem canonical11542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11542 raw11542Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw11542 raw11542Labels = mixedMoment B raw11542step0 raw11542step0Labels := by
      have hz : ∀ j, raw11542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11542step0 = (fun i j => raw11542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11542step0 raw11542; decide +kernel
      have hl : raw11542step0Labels = raw11542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11542 raw11542Labels permutation434 hz
    mixedMoment B raw11542step0 raw11542step0Labels = mixedMoment B raw11542step1 raw11542step1Labels := by
      have hz : ∀ j, raw11542step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11542step1 = (fun i j => raw11542step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11542step1 raw11542step0; decide +kernel
      have hl : raw11542step1Labels = raw11542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11542step0 raw11542step0Labels permutation56 hz
    mixedMoment B raw11542step1 raw11542step1Labels = mixedMoment B raw11542step2 raw11542step2Labels := by
      have hz : ∀ i, raw11542step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11542step2 = (fun i j => raw11542step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11542step2 raw11542step1; decide +kernel
      have hl : raw11542step2Labels = (fun j => raw11542step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11542step1 raw11542step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical11543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11543 raw11543Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw11543 raw11543Labels = mixedMoment B raw11543step0 raw11543step0Labels := by
      have hz : ∀ j, raw11543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11543step0 = (fun i j => raw11543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11543step0 raw11543; decide +kernel
      have hl : raw11543step0Labels = raw11543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11543 raw11543Labels permutation346 hz
    mixedMoment B raw11543step0 raw11543step0Labels = mixedMoment B raw11543step1 raw11543step1Labels := by
      have hz : ∀ j, raw11543step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11543step1 = (fun i j => raw11543step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11543step1 raw11543step0; decide +kernel
      have hl : raw11543step1Labels = raw11543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11543step0 raw11543step0Labels permutation56 hz
    mixedMoment B raw11543step1 raw11543step1Labels = mixedMoment B raw11543step2 raw11543step2Labels := by
      have hz : ∀ i, raw11543step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11543step2 = (fun i j => raw11543step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11543step2 raw11543step1; decide +kernel
      have hl : raw11543step2Labels = (fun j => raw11543step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11543step1 raw11543step1Labels permutation6 hz
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2281 node2281Labels = Sparse.eval nodeValue2281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2281) = mixedMoment B node2281 node2281Labels := rfl
  simpa [nodeValue2281, Sparse.eval] using hc.symm

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

theorem zero920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node920 node920Labels = 0 := by
  exact mixedMoment_alpha B hF node920 node920Labels 1 permutation160
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

theorem sound920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node920 node920Labels = Sparse.eval nodeValue920 (mixedVector B) := by
  simpa only [nodeValue920, Sparse.eval_nil] using zero920 B _hB _hF

theorem sound923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node923 node923Labels = Sparse.eval nodeValue923 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 923) = mixedMoment B node923 node923Labels := rfl
  simpa [nodeValue923, Sparse.eval] using hc.symm

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

theorem sound1683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1683 node1683Labels = Sparse.eval nodeValue1683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1683) = mixedMoment B node1683 node1683Labels := rfl
  simpa [nodeValue1683, Sparse.eval] using hc.symm

theorem sound1687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1687 node1687Labels = Sparse.eval nodeValue1687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1687) = mixedMoment B node1687 node1687Labels := rfl
  simpa [nodeValue1687, Sparse.eval] using hc.symm

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1755 node1755Labels = 0 := by
  exact mixedMoment_order_one B hB node1755 node1755Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1755 node1755Labels = Sparse.eval nodeValue1755 (mixedVector B) := by
  simpa only [nodeValue1755, Sparse.eval_nil] using zero1755 B _hB _hF

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

theorem sound1803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1803 node1803Labels = Sparse.eval nodeValue1803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1803) = mixedMoment B node1803 node1803Labels := rfl
  simpa [nodeValue1803, Sparse.eval] using hc.symm

theorem sound1806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1806 node1806Labels = Sparse.eval nodeValue1806 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1806) = mixedMoment B node1806 node1806Labels := rfl
  simpa [nodeValue1806, Sparse.eval] using hc.symm

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

theorem sound1817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1817 node1817Labels = Sparse.eval nodeValue1817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1817) = mixedMoment B node1817 node1817Labels := rfl
  simpa [nodeValue1817, Sparse.eval] using hc.symm

theorem sound1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1818 node1818Labels = Sparse.eval nodeValue1818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1818) = mixedMoment B node1818 node1818Labels := rfl
  simpa [nodeValue1818, Sparse.eval] using hc.symm

theorem sound1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1819 node1819Labels = Sparse.eval nodeValue1819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1819) = mixedMoment B node1819 node1819Labels := rfl
  simpa [nodeValue1819, Sparse.eval] using hc.symm

theorem sound1820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1820 node1820Labels = Sparse.eval nodeValue1820 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1820) = mixedMoment B node1820 node1820Labels := rfl
  simpa [nodeValue1820, Sparse.eval] using hc.symm

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

theorem sound2021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2021 node2021Labels = Sparse.eval nodeValue2021 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2021) = mixedMoment B node2021 node2021Labels := rfl
  simpa [nodeValue2021, Sparse.eval] using hc.symm

theorem sound2033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2033 node2033Labels = Sparse.eval nodeValue2033 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2033) = mixedMoment B node2033 node2033Labels := rfl
  simpa [nodeValue2033, Sparse.eval] using hc.symm

theorem sound2034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2034 node2034Labels = Sparse.eval nodeValue2034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2034) = mixedMoment B node2034 node2034Labels := rfl
  simpa [nodeValue2034, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2066 node2066Labels = 0 := by
  exact mixedMoment_order_one B hB node2066 node2066Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2051 node2051Labels = Sparse.eval nodeValue2051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2051) = mixedMoment B node2051 node2051Labels := rfl
  simpa [nodeValue2051, Sparse.eval] using hc.symm

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

theorem sound2065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2065 node2065Labels = Sparse.eval nodeValue2065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2065) = mixedMoment B node2065 node2065Labels := rfl
  simpa [nodeValue2065, Sparse.eval] using hc.symm

theorem sound2066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2066 node2066Labels = Sparse.eval nodeValue2066 (mixedVector B) := by
  simpa only [nodeValue2066, Sparse.eval_nil] using zero2066 B _hB _hF

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

theorem sound2159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2159 node2159Labels = Sparse.eval nodeValue2159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2159) = mixedMoment B node2159 node2159Labels := rfl
  simpa [nodeValue2159, Sparse.eval] using hc.symm

theorem sound2163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2163 node2163Labels = Sparse.eval nodeValue2163 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2163) = mixedMoment B node2163 node2163Labels := rfl
  simpa [nodeValue2163, Sparse.eval] using hc.symm

theorem sound2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2168 node2168Labels = Sparse.eval nodeValue2168 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2168) = mixedMoment B node2168 node2168Labels := rfl
  simpa [nodeValue2168, Sparse.eval] using hc.symm

theorem sound2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2169 node2169Labels = Sparse.eval nodeValue2169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2169) = mixedMoment B node2169 node2169Labels := rfl
  simpa [nodeValue2169, Sparse.eval] using hc.symm

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

theorem sound2180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2180 node2180Labels = Sparse.eval nodeValue2180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2180) = mixedMoment B node2180 node2180Labels := rfl
  simpa [nodeValue2180, Sparse.eval] using hc.symm

theorem sound2185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2185 node2185Labels = Sparse.eval nodeValue2185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2185) = mixedMoment B node2185 node2185Labels := rfl
  simpa [nodeValue2185, Sparse.eval] using hc.symm

theorem sound2186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2186 node2186Labels = Sparse.eval nodeValue2186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2186) = mixedMoment B node2186 node2186Labels := rfl
  simpa [nodeValue2186, Sparse.eval] using hc.symm

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

theorem sound2208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2208 node2208Labels = Sparse.eval nodeValue2208 (mixedVector B) := by
  simpa only [nodeValue2208, Sparse.eval_nil] using zero2208 B _hB _hF

theorem sound2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2218 node2218Labels = Sparse.eval nodeValue2218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2218) = mixedMoment B node2218 node2218Labels := rfl
  simpa [nodeValue2218, Sparse.eval] using hc.symm

theorem sound2222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2222 node2222Labels = Sparse.eval nodeValue2222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2222) = mixedMoment B node2222 node2222Labels := rfl
  simpa [nodeValue2222, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2430 node2430Labels = Sparse.eval nodeValue2430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2430) = mixedMoment B node2430 node2430Labels := rfl
  simpa [nodeValue2430, Sparse.eval] using hc.symm

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

theorem sound2440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2440 node2440Labels = Sparse.eval nodeValue2440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2440) = mixedMoment B node2440 node2440Labels := rfl
  simpa [nodeValue2440, Sparse.eval] using hc.symm

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

theorem sound2680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2680 node2680Labels = Sparse.eval nodeValue2680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2680) = mixedMoment B node2680 node2680Labels := rfl
  simpa [nodeValue2680, Sparse.eval] using hc.symm

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

theorem zero2742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = 0 := by
  exact mixedMoment_order_one B hB node2742 node2742Labels 1
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

theorem sound2705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2705 node2705Labels = Sparse.eval nodeValue2705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2705) = mixedMoment B node2705 node2705Labels := rfl
  simpa [nodeValue2705, Sparse.eval] using hc.symm

theorem sound2726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2726 node2726Labels = Sparse.eval nodeValue2726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2726) = mixedMoment B node2726 node2726Labels := rfl
  simpa [nodeValue2726, Sparse.eval] using hc.symm

theorem sound2734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2734 node2734Labels = Sparse.eval nodeValue2734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2734) = mixedMoment B node2734 node2734Labels := rfl
  simpa [nodeValue2734, Sparse.eval] using hc.symm

theorem sound2742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = Sparse.eval nodeValue2742 (mixedVector B) := by
  simpa only [nodeValue2742, Sparse.eval_nil] using zero2742 B _hB _hF

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

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

theorem sound2895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2895 node2895Labels = Sparse.eval nodeValue2895 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2895) = mixedMoment B node2895 node2895Labels := rfl
  simpa [nodeValue2895, Sparse.eval] using hc.symm

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

theorem sound3062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3062 node3062Labels = Sparse.eval nodeValue3062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3062) = mixedMoment B node3062 node3062Labels := rfl
  simpa [nodeValue3062, Sparse.eval] using hc.symm

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

theorem sound3162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3162 node3162Labels = Sparse.eval nodeValue3162 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3162) = mixedMoment B node3162 node3162Labels := rfl
  simpa [nodeValue3162, Sparse.eval] using hc.symm

theorem sound3163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3163 node3163Labels = Sparse.eval nodeValue3163 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3163) = mixedMoment B node3163 node3163Labels := rfl
  simpa [nodeValue3163, Sparse.eval] using hc.symm

theorem sound3164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3164 node3164Labels = Sparse.eval nodeValue3164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3164) = mixedMoment B node3164 node3164Labels := rfl
  simpa [nodeValue3164, Sparse.eval] using hc.symm

theorem sound3170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3170 node3170Labels = Sparse.eval nodeValue3170 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3170) = mixedMoment B node3170 node3170Labels := rfl
  simpa [nodeValue3170, Sparse.eval] using hc.symm

theorem sound3172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3172 node3172Labels = Sparse.eval nodeValue3172 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3172) = mixedMoment B node3172 node3172Labels := rfl
  simpa [nodeValue3172, Sparse.eval] using hc.symm

theorem sound3189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3189 node3189Labels = Sparse.eval nodeValue3189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3189) = mixedMoment B node3189 node3189Labels := rfl
  simpa [nodeValue3189, Sparse.eval] using hc.symm

theorem sound3196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3196 node3196Labels = Sparse.eval nodeValue3196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3196) = mixedMoment B node3196 node3196Labels := rfl
  simpa [nodeValue3196, Sparse.eval] using hc.symm

theorem sound3197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3197 node3197Labels = Sparse.eval nodeValue3197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3197) = mixedMoment B node3197 node3197Labels := rfl
  simpa [nodeValue3197, Sparse.eval] using hc.symm

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

theorem sound3202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3202 node3202Labels = Sparse.eval nodeValue3202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3202) = mixedMoment B node3202 node3202Labels := rfl
  simpa [nodeValue3202, Sparse.eval] using hc.symm

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

theorem sound3396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3396 node3396Labels = Sparse.eval nodeValue3396 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3396) = mixedMoment B node3396 node3396Labels := rfl
  simpa [nodeValue3396, Sparse.eval] using hc.symm

theorem sound3397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3397 node3397Labels = Sparse.eval nodeValue3397 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3397) = mixedMoment B node3397 node3397Labels := rfl
  simpa [nodeValue3397, Sparse.eval] using hc.symm

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

theorem sound3782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3782 node3782Labels = Sparse.eval nodeValue3782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3782) = mixedMoment B node3782 node3782Labels := rfl
  simpa [nodeValue3782, Sparse.eval] using hc.symm

theorem sound3789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3789 node3789Labels = Sparse.eval nodeValue3789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3789) = mixedMoment B node3789 node3789Labels := rfl
  simpa [nodeValue3789, Sparse.eval] using hc.symm

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

theorem sound3964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3964 node3964Labels = Sparse.eval nodeValue3964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3964) = mixedMoment B node3964 node3964Labels := rfl
  simpa [nodeValue3964, Sparse.eval] using hc.symm

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

theorem sound4065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4065 node4065Labels = Sparse.eval nodeValue4065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4065) = mixedMoment B node4065 node4065Labels := rfl
  simpa [nodeValue4065, Sparse.eval] using hc.symm

theorem sound4067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4067 node4067Labels = Sparse.eval nodeValue4067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4067) = mixedMoment B node4067 node4067Labels := rfl
  simpa [nodeValue4067, Sparse.eval] using hc.symm

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

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

theorem sound4076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4076 node4076Labels = Sparse.eval nodeValue4076 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4076) = mixedMoment B node4076 node4076Labels := rfl
  simpa [nodeValue4076, Sparse.eval] using hc.symm

theorem sound4078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4078 node4078Labels = Sparse.eval nodeValue4078 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4078) = mixedMoment B node4078 node4078Labels := rfl
  simpa [nodeValue4078, Sparse.eval] using hc.symm

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

theorem sound4089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4089 node4089Labels = Sparse.eval nodeValue4089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4089) = mixedMoment B node4089 node4089Labels := rfl
  simpa [nodeValue4089, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources71
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2297 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2297 + difference 0 1) (sourceB2297 + difference 1 0) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2680) := by
    have ha : (tripleCharges (sourceA2297 + difference 0 1) (sourceB2297 + difference 1 0) sourceC2297) = raw31667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31667; decide +kernel
    rw [ha]
    exact (canonical31667 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2297 + difference 0 2) (sourceB2297 + difference 2 0) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA2297 + difference 0 2) (sourceB2297 + difference 2 0) sourceC2297) = raw31668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31668; decide +kernel
    rw [ha]
    exact (canonical31668 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2297 + difference 0 3) (sourceB2297 + difference 3 0) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA2297 + difference 0 3) (sourceB2297 + difference 3 0) sourceC2297) = raw31669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31669; decide +kernel
    rw [ha]
    exact (canonical31669 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2297 + difference 0 4) (sourceB2297 + difference 4 0) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA2297 + difference 0 4) (sourceB2297 + difference 4 0) sourceC2297) = raw31670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31670; decide +kernel
    rw [ha]
    exact (canonical31670 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2297 + difference 0 5) (sourceB2297 + difference 5 0) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA2297 + difference 0 5) (sourceB2297 + difference 5 0) sourceC2297) = raw31671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31671; decide +kernel
    rw [ha]
    exact (canonical31671 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2297 + difference 1 0) (sourceB2297 + difference 0 1) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA2297 + difference 1 0) (sourceB2297 + difference 0 1) sourceC2297) = raw31672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31672; decide +kernel
    rw [ha]
    exact (canonical31672 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2297 + difference 1 2) (sourceB2297 + difference 2 1) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2297 + difference 1 2) (sourceB2297 + difference 2 1) sourceC2297) = raw23390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23390; decide +kernel
    rw [ha]
    exact (canonical23390 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2297 + difference 1 3) (sourceB2297 + difference 3 1) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2297 + difference 1 3) (sourceB2297 + difference 3 1) sourceC2297) = raw23391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23391; decide +kernel
    rw [ha]
    exact (canonical23391 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2297 + difference 1 4) (sourceB2297 + difference 4 1) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA2297 + difference 1 4) (sourceB2297 + difference 4 1) sourceC2297) = raw23392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23392; decide +kernel
    rw [ha]
    exact (canonical23392 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2297 + difference 1 5) (sourceB2297 + difference 5 1) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA2297 + difference 1 5) (sourceB2297 + difference 5 1) sourceC2297) = raw23393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23393; decide +kernel
    rw [ha]
    exact (canonical23393 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2297 + difference 2 0) (sourceB2297 + difference 0 2) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA2297 + difference 2 0) (sourceB2297 + difference 0 2) sourceC2297) = raw23400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23400; decide +kernel
    rw [ha]
    exact (canonical23400 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2297 + difference 2 1) (sourceB2297 + difference 1 2) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2146) := by
    have ha : (tripleCharges (sourceA2297 + difference 2 1) (sourceB2297 + difference 1 2) sourceC2297) = raw31673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31673; decide +kernel
    rw [ha]
    exact (canonical31673 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2297 + difference 2 3) (sourceB2297 + difference 3 2) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2171) := by
    have ha : (tripleCharges (sourceA2297 + difference 2 3) (sourceB2297 + difference 3 2) sourceC2297) = raw31674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31674; decide +kernel
    rw [ha]
    exact (canonical31674 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2297 + difference 2 4) (sourceB2297 + difference 4 2) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA2297 + difference 2 4) (sourceB2297 + difference 4 2) sourceC2297) = raw31675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31675; decide +kernel
    rw [ha]
    exact (canonical31675 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2297 + difference 2 5) (sourceB2297 + difference 5 2) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2297 + difference 2 5) (sourceB2297 + difference 5 2) sourceC2297) = raw31676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31676; decide +kernel
    rw [ha]
    exact (canonical31676 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2297 + difference 3 0) (sourceB2297 + difference 0 3) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA2297 + difference 3 0) (sourceB2297 + difference 0 3) sourceC2297) = raw23405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23405; decide +kernel
    rw [ha]
    exact (canonical23405 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2297 + difference 3 1) (sourceB2297 + difference 1 3) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2146) := by
    have ha : (tripleCharges (sourceA2297 + difference 3 1) (sourceB2297 + difference 1 3) sourceC2297) = raw31677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31677; decide +kernel
    rw [ha]
    exact (canonical31677 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2297 + difference 3 2) (sourceB2297 + difference 2 3) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2171) := by
    have ha : (tripleCharges (sourceA2297 + difference 3 2) (sourceB2297 + difference 2 3) sourceC2297) = raw31678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31678; decide +kernel
    rw [ha]
    exact (canonical31678 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2297 + difference 3 4) (sourceB2297 + difference 4 3) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA2297 + difference 3 4) (sourceB2297 + difference 4 3) sourceC2297) = raw31679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31679; decide +kernel
    rw [ha]
    exact (canonical31679 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2297 + difference 3 5) (sourceB2297 + difference 5 3) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2297 + difference 3 5) (sourceB2297 + difference 5 3) sourceC2297) = raw31680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31680; decide +kernel
    rw [ha]
    exact (canonical31680 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2297 + difference 4 0) (sourceB2297 + difference 0 4) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2297 + difference 4 0) (sourceB2297 + difference 0 4) sourceC2297) = raw23410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23410; decide +kernel
    rw [ha]
    exact (canonical23410 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2297 + difference 4 1) (sourceB2297 + difference 1 4) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2159) := by
    have ha : (tripleCharges (sourceA2297 + difference 4 1) (sourceB2297 + difference 1 4) sourceC2297) = raw31681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31681; decide +kernel
    rw [ha]
    exact (canonical31681 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2297 + difference 4 2) (sourceB2297 + difference 2 4) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2297 + difference 4 2) (sourceB2297 + difference 2 4) sourceC2297) = raw31682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31682; decide +kernel
    rw [ha]
    exact (canonical31682 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2297 + difference 4 3) (sourceB2297 + difference 3 4) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2297 + difference 4 3) (sourceB2297 + difference 3 4) sourceC2297) = raw31683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31683; decide +kernel
    rw [ha]
    exact (canonical31683 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2297 + difference 4 5) (sourceB2297 + difference 5 4) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2297 + difference 4 5) (sourceB2297 + difference 5 4) sourceC2297) = raw31684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31684; decide +kernel
    rw [ha]
    exact (canonical31684 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2297 + difference 5 0) (sourceB2297 + difference 0 5) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1687) := by
    have ha : (tripleCharges (sourceA2297 + difference 5 0) (sourceB2297 + difference 0 5) sourceC2297) = raw23415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23415; decide +kernel
    rw [ha]
    exact (canonical23415 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2297 + difference 5 1) (sourceB2297 + difference 1 5) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2163) := by
    have ha : (tripleCharges (sourceA2297 + difference 5 1) (sourceB2297 + difference 1 5) sourceC2297) = raw31685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31685; decide +kernel
    rw [ha]
    exact (canonical31685 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2297 + difference 5 2) (sourceB2297 + difference 2 5) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2180) := by
    have ha : (tripleCharges (sourceA2297 + difference 5 2) (sourceB2297 + difference 2 5) sourceC2297) = raw31686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31686; decide +kernel
    rw [ha]
    exact (canonical31686 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2297 + difference 5 3) (sourceB2297 + difference 3 5) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2180) := by
    have ha : (tripleCharges (sourceA2297 + difference 5 3) (sourceB2297 + difference 3 5) sourceC2297) = raw31687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31687; decide +kernel
    rw [ha]
    exact (canonical31687 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2297 + difference 5 4) (sourceB2297 + difference 4 5) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA2297 + difference 5 4) (sourceB2297 + difference 4 5) sourceC2297) = raw31688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31688; decide +kernel
    rw [ha]
    exact (canonical31688 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2297 sourceB2297 sourceC2297
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2297, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2298 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2298 + difference 0 1) (sourceB2298 + difference 1 0) sourceC2298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3396) := by
    have ha : (tripleCharges (sourceA2298 + difference 0 1) (sourceB2298 + difference 1 0) sourceC2298) = raw31689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2298 sourceB2298 sourceC2298 difference raw31689; decide +kernel
    rw [ha]
    exact (canonical31689 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2298 + difference 1 1) (sourceB2298 + difference 1 1) sourceC2298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA2298 + difference 1 1) (sourceB2298 + difference 1 1) sourceC2298) = raw27312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2298 sourceB2298 sourceC2298 difference raw27312; decide +kernel
    rw [ha]
    exact (canonical27312 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2298 + difference 2 1) (sourceB2298 + difference 1 2) sourceC2298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1809) := by
    have ha : (tripleCharges (sourceA2298 + difference 2 1) (sourceB2298 + difference 1 2) sourceC2298) = raw31690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2298 sourceB2298 sourceC2298 difference raw31690; decide +kernel
    rw [ha]
    exact (canonical31690 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2298 + difference 3 1) (sourceB2298 + difference 1 3) sourceC2298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1809) := by
    have ha : (tripleCharges (sourceA2298 + difference 3 1) (sourceB2298 + difference 1 3) sourceC2298) = raw31691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2298 sourceB2298 sourceC2298 difference raw31691; decide +kernel
    rw [ha]
    exact (canonical31691 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2298 + difference 4 1) (sourceB2298 + difference 1 4) sourceC2298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1817) := by
    have ha : (tripleCharges (sourceA2298 + difference 4 1) (sourceB2298 + difference 1 4) sourceC2298) = raw31692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2298 sourceB2298 sourceC2298 difference raw31692; decide +kernel
    rw [ha]
    exact (canonical31692 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2298 + difference 5 1) (sourceB2298 + difference 1 5) sourceC2298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1820) := by
    have ha : (tripleCharges (sourceA2298 + difference 5 1) (sourceB2298 + difference 1 5) sourceC2298) = raw27309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2298 sourceB2298 sourceC2298 difference raw27309; decide +kernel
    rw [ha]
    exact (canonical27309 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2298 + sourceB2298) sourceC2298) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA2298 + sourceB2298) sourceC2298) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA2298 sourceB2298 sourceC2298 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2298 sourceB2298 sourceC2298
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2298, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2303 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2303 + difference 0 1) (sourceB2303 + difference 1 0) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA2303 + difference 0 1) (sourceB2303 + difference 1 0) sourceC2303) = raw31745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31745; decide +kernel
    rw [ha]
    exact (canonical31745 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2303 + difference 0 2) (sourceB2303 + difference 2 0) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2303 + difference 0 2) (sourceB2303 + difference 2 0) sourceC2303) = raw31746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31746; decide +kernel
    rw [ha]
    exact (canonical31746 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2303 + difference 0 3) (sourceB2303 + difference 3 0) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2303 + difference 0 3) (sourceB2303 + difference 3 0) sourceC2303) = raw31747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31747; decide +kernel
    rw [ha]
    exact (canonical31747 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2303 + difference 0 4) (sourceB2303 + difference 4 0) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2303 + difference 0 4) (sourceB2303 + difference 4 0) sourceC2303) = raw31748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31748; decide +kernel
    rw [ha]
    exact (canonical31748 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2303 + difference 0 5) (sourceB2303 + difference 5 0) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2303 + difference 0 5) (sourceB2303 + difference 5 0) sourceC2303) = raw31749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31749; decide +kernel
    rw [ha]
    exact (canonical31749 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2303 + difference 1 0) (sourceB2303 + difference 0 1) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA2303 + difference 1 0) (sourceB2303 + difference 0 1) sourceC2303) = raw21680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw21680; decide +kernel
    rw [ha]
    exact (canonical21680 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2303 + difference 1 2) (sourceB2303 + difference 2 1) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2303 + difference 1 2) (sourceB2303 + difference 2 1) sourceC2303) = raw23536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw23536; decide +kernel
    rw [ha]
    exact (canonical23536 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2303 + difference 1 3) (sourceB2303 + difference 3 1) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2303 + difference 1 3) (sourceB2303 + difference 3 1) sourceC2303) = raw23537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw23537; decide +kernel
    rw [ha]
    exact (canonical23537 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2303 + difference 1 4) (sourceB2303 + difference 4 1) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA2303 + difference 1 4) (sourceB2303 + difference 4 1) sourceC2303) = raw21660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw21660; decide +kernel
    rw [ha]
    exact (canonical21660 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2303 + difference 1 5) (sourceB2303 + difference 5 1) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2303 + difference 1 5) (sourceB2303 + difference 5 1) sourceC2303) = raw23538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw23538; decide +kernel
    rw [ha]
    exact (canonical23538 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2303 + difference 2 0) (sourceB2303 + difference 0 2) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA2303 + difference 2 0) (sourceB2303 + difference 0 2) sourceC2303) = raw23544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw23544; decide +kernel
    rw [ha]
    exact (canonical23544 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2303 + difference 2 1) (sourceB2303 + difference 1 2) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2303 + difference 2 1) (sourceB2303 + difference 1 2) sourceC2303) = raw31750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31750; decide +kernel
    rw [ha]
    exact (canonical31750 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2303 + difference 2 3) (sourceB2303 + difference 3 2) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2174) := by
    have ha : (tripleCharges (sourceA2303 + difference 2 3) (sourceB2303 + difference 3 2) sourceC2303) = raw31751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31751; decide +kernel
    rw [ha]
    exact (canonical31751 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2303 + difference 2 4) (sourceB2303 + difference 4 2) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2303 + difference 2 4) (sourceB2303 + difference 4 2) sourceC2303) = raw31752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31752; decide +kernel
    rw [ha]
    exact (canonical31752 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2303 + difference 2 5) (sourceB2303 + difference 5 2) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2303 + difference 2 5) (sourceB2303 + difference 5 2) sourceC2303) = raw31753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31753; decide +kernel
    rw [ha]
    exact (canonical31753 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2303 + difference 3 0) (sourceB2303 + difference 0 3) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA2303 + difference 3 0) (sourceB2303 + difference 0 3) sourceC2303) = raw23548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw23548; decide +kernel
    rw [ha]
    exact (canonical23548 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2303 + difference 3 1) (sourceB2303 + difference 1 3) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2303 + difference 3 1) (sourceB2303 + difference 1 3) sourceC2303) = raw31754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31754; decide +kernel
    rw [ha]
    exact (canonical31754 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2303 + difference 3 2) (sourceB2303 + difference 2 3) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2174) := by
    have ha : (tripleCharges (sourceA2303 + difference 3 2) (sourceB2303 + difference 2 3) sourceC2303) = raw31755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31755; decide +kernel
    rw [ha]
    exact (canonical31755 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2303 + difference 3 4) (sourceB2303 + difference 4 3) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2303 + difference 3 4) (sourceB2303 + difference 4 3) sourceC2303) = raw31756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31756; decide +kernel
    rw [ha]
    exact (canonical31756 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2303 + difference 3 5) (sourceB2303 + difference 5 3) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2303 + difference 3 5) (sourceB2303 + difference 5 3) sourceC2303) = raw31757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31757; decide +kernel
    rw [ha]
    exact (canonical31757 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2303 + difference 4 0) (sourceB2303 + difference 0 4) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2303 + difference 4 0) (sourceB2303 + difference 0 4) sourceC2303) = raw23552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw23552; decide +kernel
    rw [ha]
    exact (canonical23552 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2303 + difference 4 1) (sourceB2303 + difference 1 4) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2303 + difference 4 1) (sourceB2303 + difference 1 4) sourceC2303) = raw31758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31758; decide +kernel
    rw [ha]
    exact (canonical31758 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2303 + difference 4 2) (sourceB2303 + difference 2 4) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2303 + difference 4 2) (sourceB2303 + difference 2 4) sourceC2303) = raw31759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31759; decide +kernel
    rw [ha]
    exact (canonical31759 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2303 + difference 4 3) (sourceB2303 + difference 3 4) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2303 + difference 4 3) (sourceB2303 + difference 3 4) sourceC2303) = raw31760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31760; decide +kernel
    rw [ha]
    exact (canonical31760 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2303 + difference 4 5) (sourceB2303 + difference 5 4) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2303 + difference 4 5) (sourceB2303 + difference 5 4) sourceC2303) = raw31761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31761; decide +kernel
    rw [ha]
    exact (canonical31761 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2303 + difference 5 0) (sourceB2303 + difference 0 5) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2303 + difference 5 0) (sourceB2303 + difference 0 5) sourceC2303) = raw21677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw21677; decide +kernel
    rw [ha]
    exact (canonical21677 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2303 + difference 5 1) (sourceB2303 + difference 1 5) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2303 + difference 5 1) (sourceB2303 + difference 1 5) sourceC2303) = raw31762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31762; decide +kernel
    rw [ha]
    exact (canonical31762 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2303 + difference 5 2) (sourceB2303 + difference 2 5) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2303 + difference 5 2) (sourceB2303 + difference 2 5) sourceC2303) = raw31763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31763; decide +kernel
    rw [ha]
    exact (canonical31763 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2303 + difference 5 3) (sourceB2303 + difference 3 5) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2303 + difference 5 3) (sourceB2303 + difference 3 5) sourceC2303) = raw31764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31764; decide +kernel
    rw [ha]
    exact (canonical31764 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2303 + difference 5 4) (sourceB2303 + difference 4 5) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA2303 + difference 5 4) (sourceB2303 + difference 4 5) sourceC2303) = raw21656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw21656; decide +kernel
    rw [ha]
    exact (canonical21656 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2303 sourceB2303 sourceC2303
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2303, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources72
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2304 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2304 + difference 0 1) (sourceB2304 + difference 1 0) sourceC2304) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA2304 + difference 0 1) (sourceB2304 + difference 1 0) sourceC2304) = raw31765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2304 sourceB2304 sourceC2304 difference raw31765; decide +kernel
    rw [ha]
    exact (canonical31765 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2304 + difference 1 1) (sourceB2304 + difference 1 1) sourceC2304) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2066) := by
    have ha : (tripleCharges (sourceA2304 + difference 1 1) (sourceB2304 + difference 1 1) sourceC2304) = raw31766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2304 sourceB2304 sourceC2304 difference raw31766; decide +kernel
    rw [ha]
    exact (canonical31766 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2304 + difference 2 1) (sourceB2304 + difference 1 2) sourceC2304) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1810) := by
    have ha : (tripleCharges (sourceA2304 + difference 2 1) (sourceB2304 + difference 1 2) sourceC2304) = raw31767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2304 sourceB2304 sourceC2304 difference raw31767; decide +kernel
    rw [ha]
    exact (canonical31767 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2304 + difference 3 1) (sourceB2304 + difference 1 3) sourceC2304) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1810) := by
    have ha : (tripleCharges (sourceA2304 + difference 3 1) (sourceB2304 + difference 1 3) sourceC2304) = raw31768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2304 sourceB2304 sourceC2304 difference raw31768; decide +kernel
    rw [ha]
    exact (canonical31768 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2304 + difference 4 1) (sourceB2304 + difference 1 4) sourceC2304) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1818) := by
    have ha : (tripleCharges (sourceA2304 + difference 4 1) (sourceB2304 + difference 1 4) sourceC2304) = raw31769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2304 sourceB2304 sourceC2304 difference raw31769; decide +kernel
    rw [ha]
    exact (canonical31769 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2304 + difference 5 1) (sourceB2304 + difference 1 5) sourceC2304) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1819) := by
    have ha : (tripleCharges (sourceA2304 + difference 5 1) (sourceB2304 + difference 1 5) sourceC2304) = raw31770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2304 sourceB2304 sourceC2304 difference raw31770; decide +kernel
    rw [ha]
    exact (canonical31770 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2304 + sourceB2304) sourceC2304) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2304 + sourceB2304) sourceC2304) = raw19413 := by
      apply Matrix.ext; unfold doubleCharges sourceA2304 sourceB2304 sourceC2304 raw19413; decide +kernel
    rw [ha]
    exact (canonical19413 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2304 sourceB2304 sourceC2304
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2304, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2311 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2311 + difference 0 1) (sourceB2311 + difference 1 0) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (tripleCharges (sourceA2311 + difference 0 1) (sourceB2311 + difference 1 0) sourceC2311) = raw18339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw18339; decide +kernel
    rw [ha]
    exact (canonical18339 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2311 + difference 0 2) (sourceB2311 + difference 2 0) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2311 + difference 0 2) (sourceB2311 + difference 2 0) sourceC2311) = raw18340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw18340; decide +kernel
    rw [ha]
    exact (canonical18340 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2311 + difference 0 3) (sourceB2311 + difference 3 0) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2311 + difference 0 3) (sourceB2311 + difference 3 0) sourceC2311) = raw18341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw18341; decide +kernel
    rw [ha]
    exact (canonical18341 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2311 + difference 0 4) (sourceB2311 + difference 4 0) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2311 + difference 0 4) (sourceB2311 + difference 4 0) sourceC2311) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2311 + difference 0 5) (sourceB2311 + difference 5 0) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2311 + difference 0 5) (sourceB2311 + difference 5 0) sourceC2311) = raw3336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw3336; decide +kernel
    rw [ha]
    exact (canonical3336 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2311 + difference 1 0) (sourceB2311 + difference 0 1) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA2311 + difference 1 0) (sourceB2311 + difference 0 1) sourceC2311) = raw11540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw11540; decide +kernel
    rw [ha]
    exact (canonical11540 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2311 + difference 1 2) (sourceB2311 + difference 2 1) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2311 + difference 1 2) (sourceB2311 + difference 2 1) sourceC2311) = raw11542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw11542; decide +kernel
    rw [ha]
    exact (canonical11542 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2311 + difference 1 3) (sourceB2311 + difference 3 1) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2311 + difference 1 3) (sourceB2311 + difference 3 1) sourceC2311) = raw11543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw11543; decide +kernel
    rw [ha]
    exact (canonical11543 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2311 + difference 1 4) (sourceB2311 + difference 4 1) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2311 + difference 1 4) (sourceB2311 + difference 4 1) sourceC2311) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2311 + difference 1 5) (sourceB2311 + difference 5 1) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2311 + difference 1 5) (sourceB2311 + difference 5 1) sourceC2311) = raw3335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw3335; decide +kernel
    rw [ha]
    exact (canonical3335 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2311 + difference 2 0) (sourceB2311 + difference 0 2) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA2311 + difference 2 0) (sourceB2311 + difference 0 2) sourceC2311) = raw23782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw23782; decide +kernel
    rw [ha]
    exact (canonical23782 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2311 + difference 2 1) (sourceB2311 + difference 1 2) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2311 + difference 2 1) (sourceB2311 + difference 1 2) sourceC2311) = raw31877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31877; decide +kernel
    rw [ha]
    exact (canonical31877 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2311 + difference 2 3) (sourceB2311 + difference 3 2) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2311 + difference 2 3) (sourceB2311 + difference 3 2) sourceC2311) = raw31878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31878; decide +kernel
    rw [ha]
    exact (canonical31878 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2311 + difference 2 4) (sourceB2311 + difference 4 2) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2311 + difference 2 4) (sourceB2311 + difference 4 2) sourceC2311) = raw11535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw11535; decide +kernel
    rw [ha]
    exact (canonical11535 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2311 + difference 2 5) (sourceB2311 + difference 5 2) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2311 + difference 2 5) (sourceB2311 + difference 5 2) sourceC2311) = raw31879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31879; decide +kernel
    rw [ha]
    exact (canonical31879 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2311 + difference 3 0) (sourceB2311 + difference 0 3) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA2311 + difference 3 0) (sourceB2311 + difference 0 3) sourceC2311) = raw23786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw23786; decide +kernel
    rw [ha]
    exact (canonical23786 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2311 + difference 3 1) (sourceB2311 + difference 1 3) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2311 + difference 3 1) (sourceB2311 + difference 1 3) sourceC2311) = raw31880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31880; decide +kernel
    rw [ha]
    exact (canonical31880 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2311 + difference 3 2) (sourceB2311 + difference 2 3) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2311 + difference 3 2) (sourceB2311 + difference 2 3) sourceC2311) = raw31881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31881; decide +kernel
    rw [ha]
    exact (canonical31881 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2311 + difference 3 4) (sourceB2311 + difference 4 3) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2311 + difference 3 4) (sourceB2311 + difference 4 3) sourceC2311) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2311 + difference 3 5) (sourceB2311 + difference 5 3) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2311 + difference 3 5) (sourceB2311 + difference 5 3) sourceC2311) = raw14374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw14374; decide +kernel
    rw [ha]
    exact (canonical14374 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2311 + difference 4 0) (sourceB2311 + difference 0 4) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA2311 + difference 4 0) (sourceB2311 + difference 0 4) sourceC2311) = raw23789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw23789; decide +kernel
    rw [ha]
    exact (canonical23789 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2311 + difference 4 1) (sourceB2311 + difference 1 4) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2311 + difference 4 1) (sourceB2311 + difference 1 4) sourceC2311) = raw31882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31882; decide +kernel
    rw [ha]
    exact (canonical31882 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2311 + difference 4 2) (sourceB2311 + difference 2 4) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2311 + difference 4 2) (sourceB2311 + difference 2 4) sourceC2311) = raw31883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31883; decide +kernel
    rw [ha]
    exact (canonical31883 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2311 + difference 4 3) (sourceB2311 + difference 3 4) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2311 + difference 4 3) (sourceB2311 + difference 3 4) sourceC2311) = raw31884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31884; decide +kernel
    rw [ha]
    exact (canonical31884 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2311 + difference 4 5) (sourceB2311 + difference 5 4) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2311 + difference 4 5) (sourceB2311 + difference 5 4) sourceC2311) = raw31885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31885; decide +kernel
    rw [ha]
    exact (canonical31885 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2311 + difference 5 0) (sourceB2311 + difference 0 5) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA2311 + difference 5 0) (sourceB2311 + difference 0 5) sourceC2311) = raw22311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw22311; decide +kernel
    rw [ha]
    exact (canonical22311 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2311 + difference 5 1) (sourceB2311 + difference 1 5) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2311 + difference 5 1) (sourceB2311 + difference 1 5) sourceC2311) = raw29299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw29299; decide +kernel
    rw [ha]
    exact (canonical29299 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2311 + difference 5 2) (sourceB2311 + difference 2 5) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2311 + difference 5 2) (sourceB2311 + difference 2 5) sourceC2311) = raw29300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw29300; decide +kernel
    rw [ha]
    exact (canonical29300 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2311 + difference 5 3) (sourceB2311 + difference 3 5) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2311 + difference 5 3) (sourceB2311 + difference 3 5) sourceC2311) = raw29301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw29301; decide +kernel
    rw [ha]
    exact (canonical29301 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2311 + difference 5 4) (sourceB2311 + difference 4 5) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2311 + difference 5 4) (sourceB2311 + difference 4 5) sourceC2311) = raw5210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw5210; decide +kernel
    rw [ha]
    exact (canonical5210 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2311 sourceB2311 sourceC2311
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2311, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2312 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2312 + difference 2 0) (sourceB2312 + difference 0 2) sourceC2312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 923) := by
    have ha : (tripleCharges (sourceA2312 + difference 2 0) (sourceB2312 + difference 0 2) sourceC2312) = raw23805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2312 sourceB2312 sourceC2312 difference raw23805; decide +kernel
    rw [ha]
    exact (canonical23805 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2312 + difference 2 1) (sourceB2312 + difference 1 2) sourceC2312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1806) := by
    have ha : (tripleCharges (sourceA2312 + difference 2 1) (sourceB2312 + difference 1 2) sourceC2312) = raw31886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2312 sourceB2312 sourceC2312 difference raw31886; decide +kernel
    rw [ha]
    exact (canonical31886 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2312 + difference 2 2) (sourceB2312 + difference 2 2) sourceC2312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA2312 + difference 2 2) (sourceB2312 + difference 2 2) sourceC2312) = raw31378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2312 sourceB2312 sourceC2312 difference raw31378; decide +kernel
    rw [ha]
    exact (canonical31378 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2312 + difference 2 3) (sourceB2312 + difference 3 2) sourceC2312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA2312 + difference 2 3) (sourceB2312 + difference 3 2) sourceC2312) = raw31374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2312 sourceB2312 sourceC2312 difference raw31374; decide +kernel
    rw [ha]
    exact (canonical31374 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2312 + difference 2 4) (sourceB2312 + difference 4 2) sourceC2312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA2312 + difference 2 4) (sourceB2312 + difference 4 2) sourceC2312) = raw31887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2312 sourceB2312 sourceC2312 difference raw31887; decide +kernel
    rw [ha]
    exact (canonical31887 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2312 + difference 2 5) (sourceB2312 + difference 5 2) sourceC2312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2051) := by
    have ha : (tripleCharges (sourceA2312 + difference 2 5) (sourceB2312 + difference 5 2) sourceC2312) = raw31888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2312 sourceB2312 sourceC2312 difference raw31888; decide +kernel
    rw [ha]
    exact (canonical31888 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2312 + sourceB2312) sourceC2312) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2312 + sourceB2312) sourceC2312) = raw23810 := by
      apply Matrix.ext; unfold doubleCharges sourceA2312 sourceB2312 sourceC2312 raw23810; decide +kernel
    rw [ha]
    exact (canonical23810 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2312 sourceB2312 sourceC2312
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2312, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2313 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2313 + difference 0 2) (sourceB2313 + difference 2 0) sourceC2313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA2313 + difference 0 2) (sourceB2313 + difference 2 0) sourceC2313) = raw31889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2313 sourceB2313 sourceC2313 difference raw31889; decide +kernel
    rw [ha]
    exact (canonical31889 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2313 + difference 1 2) (sourceB2313 + difference 2 1) sourceC2313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA2313 + difference 1 2) (sourceB2313 + difference 2 1) sourceC2313) = raw31890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2313 sourceB2313 sourceC2313 difference raw31890; decide +kernel
    rw [ha]
    exact (canonical31890 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2313 + difference 2 2) (sourceB2313 + difference 2 2) sourceC2313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA2313 + difference 2 2) (sourceB2313 + difference 2 2) sourceC2313) = raw31891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2313 sourceB2313 sourceC2313 difference raw31891; decide +kernel
    rw [ha]
    exact (canonical31891 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2313 + difference 3 2) (sourceB2313 + difference 2 3) sourceC2313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3189) := by
    have ha : (tripleCharges (sourceA2313 + difference 3 2) (sourceB2313 + difference 2 3) sourceC2313) = raw31892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2313 sourceB2313 sourceC2313 difference raw31892; decide +kernel
    rw [ha]
    exact (canonical31892 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2313 + difference 4 2) (sourceB2313 + difference 2 4) sourceC2313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3062) := by
    have ha : (tripleCharges (sourceA2313 + difference 4 2) (sourceB2313 + difference 2 4) sourceC2313) = raw31893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2313 sourceB2313 sourceC2313 difference raw31893; decide +kernel
    rw [ha]
    exact (canonical31893 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2313 + difference 5 2) (sourceB2313 + difference 2 5) sourceC2313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2440) := by
    have ha : (tripleCharges (sourceA2313 + difference 5 2) (sourceB2313 + difference 2 5) sourceC2313) = raw31894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2313 sourceB2313 sourceC2313 difference raw31894; decide +kernel
    rw [ha]
    exact (canonical31894 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2313 + sourceB2313) sourceC2313) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2313 + sourceB2313) sourceC2313) = raw31895 := by
      apply Matrix.ext; unfold doubleCharges sourceA2313 sourceB2313 sourceC2313 raw31895; decide +kernel
    rw [ha]
    exact (canonical31895 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2313 sourceB2313 sourceC2313
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2313, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2315 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2315 + difference 2 0) (sourceB2315 + difference 0 2) sourceC2315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 920) := by
    have ha : (tripleCharges (sourceA2315 + difference 2 0) (sourceB2315 + difference 0 2) sourceC2315) = raw23833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2315 sourceB2315 sourceC2315 difference raw23833; decide +kernel
    rw [ha]
    exact (canonical23833 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2315 + difference 2 1) (sourceB2315 + difference 1 2) sourceC2315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1803) := by
    have ha : (tripleCharges (sourceA2315 + difference 2 1) (sourceB2315 + difference 1 2) sourceC2315) = raw31903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2315 sourceB2315 sourceC2315 difference raw31903; decide +kernel
    rw [ha]
    exact (canonical31903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2315 + difference 2 2) (sourceB2315 + difference 2 2) sourceC2315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2033) := by
    have ha : (tripleCharges (sourceA2315 + difference 2 2) (sourceB2315 + difference 2 2) sourceC2315) = raw31904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2315 sourceB2315 sourceC2315 difference raw31904; decide +kernel
    rw [ha]
    exact (canonical31904 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2315 + difference 2 3) (sourceB2315 + difference 3 2) sourceC2315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA2315 + difference 2 3) (sourceB2315 + difference 3 2) sourceC2315) = raw31905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2315 sourceB2315 sourceC2315 difference raw31905; decide +kernel
    rw [ha]
    exact (canonical31905 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2315 + difference 2 4) (sourceB2315 + difference 4 2) sourceC2315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA2315 + difference 2 4) (sourceB2315 + difference 4 2) sourceC2315) = raw31906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2315 sourceB2315 sourceC2315 difference raw31906; decide +kernel
    rw [ha]
    exact (canonical31906 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2315 + difference 2 5) (sourceB2315 + difference 5 2) sourceC2315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2051) := by
    have ha : (tripleCharges (sourceA2315 + difference 2 5) (sourceB2315 + difference 5 2) sourceC2315) = raw31907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2315 sourceB2315 sourceC2315 difference raw31907; decide +kernel
    rw [ha]
    exact (canonical31907 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2315 + sourceB2315) sourceC2315) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2315 + sourceB2315) sourceC2315) = raw23838 := by
      apply Matrix.ext; unfold doubleCharges sourceA2315 sourceB2315 sourceC2315 raw23838; decide +kernel
    rw [ha]
    exact (canonical23838 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2315 sourceB2315 sourceC2315
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2315, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2316 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2316 + difference 0 2) (sourceB2316 + difference 2 0) sourceC2316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA2316 + difference 0 2) (sourceB2316 + difference 2 0) sourceC2316) = raw31908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2316 sourceB2316 sourceC2316 difference raw31908; decide +kernel
    rw [ha]
    exact (canonical31908 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2316 + difference 1 2) (sourceB2316 + difference 2 1) sourceC2316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA2316 + difference 1 2) (sourceB2316 + difference 2 1) sourceC2316) = raw31909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2316 sourceB2316 sourceC2316 difference raw31909; decide +kernel
    rw [ha]
    exact (canonical31909 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2316 + difference 2 2) (sourceB2316 + difference 2 2) sourceC2316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA2316 + difference 2 2) (sourceB2316 + difference 2 2) sourceC2316) = raw31910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2316 sourceB2316 sourceC2316 difference raw31910; decide +kernel
    rw [ha]
    exact (canonical31910 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2316 + difference 3 2) (sourceB2316 + difference 2 3) sourceC2316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3164) := by
    have ha : (tripleCharges (sourceA2316 + difference 3 2) (sourceB2316 + difference 2 3) sourceC2316) = raw31911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2316 sourceB2316 sourceC2316 difference raw31911; decide +kernel
    rw [ha]
    exact (canonical31911 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2316 + difference 4 2) (sourceB2316 + difference 2 4) sourceC2316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3164) := by
    have ha : (tripleCharges (sourceA2316 + difference 4 2) (sourceB2316 + difference 2 4) sourceC2316) = raw31912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2316 sourceB2316 sourceC2316 difference raw31912; decide +kernel
    rw [ha]
    exact (canonical31912 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2316 + difference 5 2) (sourceB2316 + difference 2 5) sourceC2316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2895) := by
    have ha : (tripleCharges (sourceA2316 + difference 5 2) (sourceB2316 + difference 2 5) sourceC2316) = raw31913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2316 sourceB2316 sourceC2316 difference raw31913; decide +kernel
    rw [ha]
    exact (canonical31913 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2316 + sourceB2316) sourceC2316) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2316 + sourceB2316) sourceC2316) = raw31914 := by
      apply Matrix.ext; unfold doubleCharges sourceA2316 sourceB2316 sourceC2316 raw31914; decide +kernel
    rw [ha]
    exact (canonical31914 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2316 sourceB2316 sourceC2316
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2316, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2318 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2318 + difference 0 2) (sourceB2318 + difference 2 0) sourceC2318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA2318 + difference 0 2) (sourceB2318 + difference 2 0) sourceC2318) = raw31921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2318 sourceB2318 sourceC2318 difference raw31921; decide +kernel
    rw [ha]
    exact (canonical31921 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2318 + difference 1 2) (sourceB2318 + difference 2 1) sourceC2318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA2318 + difference 1 2) (sourceB2318 + difference 2 1) sourceC2318) = raw31922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2318 sourceB2318 sourceC2318 difference raw31922; decide +kernel
    rw [ha]
    exact (canonical31922 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2318 + difference 2 2) (sourceB2318 + difference 2 2) sourceC2318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA2318 + difference 2 2) (sourceB2318 + difference 2 2) sourceC2318) = raw31923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2318 sourceB2318 sourceC2318 difference raw31923; decide +kernel
    rw [ha]
    exact (canonical31923 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2318 + difference 3 2) (sourceB2318 + difference 2 3) sourceC2318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3162) := by
    have ha : (tripleCharges (sourceA2318 + difference 3 2) (sourceB2318 + difference 2 3) sourceC2318) = raw31924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2318 sourceB2318 sourceC2318 difference raw31924; decide +kernel
    rw [ha]
    exact (canonical31924 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2318 + difference 4 2) (sourceB2318 + difference 2 4) sourceC2318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3163) := by
    have ha : (tripleCharges (sourceA2318 + difference 4 2) (sourceB2318 + difference 2 4) sourceC2318) = raw31925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2318 sourceB2318 sourceC2318 difference raw31925; decide +kernel
    rw [ha]
    exact (canonical31925 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2318 + difference 5 2) (sourceB2318 + difference 2 5) sourceC2318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2430) := by
    have ha : (tripleCharges (sourceA2318 + difference 5 2) (sourceB2318 + difference 2 5) sourceC2318) = raw31926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2318 sourceB2318 sourceC2318 difference raw31926; decide +kernel
    rw [ha]
    exact (canonical31926 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2318 + sourceB2318) sourceC2318) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2318 + sourceB2318) sourceC2318) = raw31927 := by
      apply Matrix.ext; unfold doubleCharges sourceA2318 sourceB2318 sourceC2318 raw31927; decide +kernel
    rw [ha]
    exact (canonical31927 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2318 sourceB2318 sourceC2318
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2318, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1875 : Integer.Sparse.reindex keyMap MixedData.row1875 = numericRow1875 := by decide +kernel

theorem numericCheck1875 (x : Master → ℝ) : Integer.Sparse.eval numericRow1875 x =
    (1 : ℝ) * reducedSource1875 x := by
  norm_num [numericRow1875, reducedSource1875, Integer.Sparse.eval, Sparse.eval, nodeValue1669, nodeValue1683, nodeValue1687, nodeValue1741, nodeValue2143, nodeValue2146, nodeValue2159, nodeValue2163, nodeValue2171, nodeValue2180, nodeValue2193, nodeValue2197, nodeValue2208, nodeValue2218, nodeValue2222, nodeValue2268, nodeValue2281, nodeValue2664, nodeValue2680, nodeValue2726, nodeValue2734]

theorem reindexCheck1876 : Integer.Sparse.reindex keyMap MixedData.row1876 = numericRow1876 := by decide +kernel

theorem numericCheck1876 (x : Master → ℝ) : Integer.Sparse.eval numericRow1876 x =
    (1 : ℝ) * reducedSource1876 x := by
  norm_num [numericRow1876, reducedSource1876, Integer.Sparse.eval, Sparse.eval, nodeValue1809, nodeValue1817, nodeValue1820, nodeValue2065, nodeValue3396, nodeValue4085]

theorem reindexCheck1878 : Integer.Sparse.reindex keyMap MixedData.row1878 = numericRow1878 := by decide +kernel

theorem numericCheck1878 (x : Master → ℝ) : Integer.Sparse.eval numericRow1878 x =
    (1 : ℝ) * reducedSource1878 x := by
  norm_num [numericRow1878, reducedSource1878, Integer.Sparse.eval, Sparse.eval, nodeValue1675, nodeValue1693, nodeValue1694, nodeValue1755, nodeValue2152, nodeValue2168, nodeValue2169, nodeValue2174, nodeValue2185, nodeValue2186, nodeValue2205, nodeValue2206, nodeValue2228, nodeValue2229, nodeValue2230, nodeValue2293, nodeValue2686, nodeValue2705, nodeValue2742, nodeValue2743, nodeValue4084]

theorem reindexCheck1879 : Integer.Sparse.reindex keyMap MixedData.row1879 = numericRow1879 := by decide +kernel

theorem numericCheck1879 (x : Master → ℝ) : Integer.Sparse.eval numericRow1879 x =
    (1 : ℝ) * reducedSource1879 x := by
  norm_num [numericRow1879, reducedSource1879, Integer.Sparse.eval, Sparse.eval, nodeValue1810, nodeValue1818, nodeValue1819, nodeValue2066, nodeValue3397, nodeValue4084]

theorem reindexCheck1882 : Integer.Sparse.reindex keyMap MixedData.row1882 = numericRow1882 := by decide +kernel

theorem numericCheck1882 (x : Master → ℝ) : Integer.Sparse.eval numericRow1882 x =
    (1 : ℝ) * reducedSource1882 x := by
  norm_num [numericRow1882, reducedSource1882, Integer.Sparse.eval, Sparse.eval, nodeValue4065, nodeValue4067, nodeValue4071, nodeValue4074, nodeValue4075, nodeValue4076, nodeValue4078, nodeValue4080, nodeValue4081, nodeValue4082, nodeValue4084, nodeValue4088, nodeValue4089, nodeValue4092]

theorem reindexCheck1883 : Integer.Sparse.reindex keyMap MixedData.row1883 = numericRow1883 := by decide +kernel

theorem numericCheck1883 (x : Master → ℝ) : Integer.Sparse.eval numericRow1883 x =
    (1 : ℝ) * reducedSource1883 x := by
  norm_num [numericRow1883, reducedSource1883, Integer.Sparse.eval, Sparse.eval, nodeValue923, nodeValue1806, nodeValue2021, nodeValue2034, nodeValue2051, nodeValue2058, nodeValue4084]

theorem reindexCheck1884 : Integer.Sparse.reindex keyMap MixedData.row1884 = numericRow1884 := by decide +kernel

theorem numericCheck1884 (x : Master → ℝ) : Integer.Sparse.eval numericRow1884 x =
    (1 : ℝ) * reducedSource1884 x := by
  norm_num [numericRow1884, reducedSource1884, Integer.Sparse.eval, Sparse.eval, nodeValue2440, nodeValue3062, nodeValue3189, nodeValue3202, nodeValue3789, nodeValue4091]

theorem reindexCheck1885 : Integer.Sparse.reindex keyMap MixedData.row1885 = numericRow1885 := by decide +kernel

theorem numericCheck1885 (x : Master → ℝ) : Integer.Sparse.eval numericRow1885 x =
    (1 : ℝ) * reducedSource1885 x := by
  norm_num [numericRow1885, reducedSource1885, Integer.Sparse.eval, Sparse.eval, nodeValue920, nodeValue1803, nodeValue2033, nodeValue2051, nodeValue2054, nodeValue4084]

theorem reindexCheck1886 : Integer.Sparse.reindex keyMap MixedData.row1886 = numericRow1886 := by decide +kernel

theorem numericCheck1886 (x : Master → ℝ) : Integer.Sparse.eval numericRow1886 x =
    (1 : ℝ) * reducedSource1886 x := by
  norm_num [numericRow1886, reducedSource1886, Integer.Sparse.eval, Sparse.eval, nodeValue2895, nodeValue3164, nodeValue3172, nodeValue3197, nodeValue3964, nodeValue4091]

theorem reindexCheck1887 : Integer.Sparse.reindex keyMap MixedData.row1887 = numericRow1887 := by decide +kernel

theorem numericCheck1887 (x : Master → ℝ) : Integer.Sparse.eval numericRow1887 x =
    (1 : ℝ) * reducedSource1887 x := by
  norm_num [numericRow1887, reducedSource1887, Integer.Sparse.eval, Sparse.eval, nodeValue2430, nodeValue3162, nodeValue3163, nodeValue3170, nodeValue3196, nodeValue3782, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1875 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1875 (mixedVector B) = 0 := by
  have h1669 : mixedVector B (Sum.inr 1669) = Sparse.eval nodeValue1669 (mixedVector B) := by
    change mixedMoment B node1669 node1669Labels = _
    exact sound1669 B hB hF
  have h1683 : mixedVector B (Sum.inr 1683) = Sparse.eval nodeValue1683 (mixedVector B) := by
    change mixedMoment B node1683 node1683Labels = _
    exact sound1683 B hB hF
  have h1687 : mixedVector B (Sum.inr 1687) = Sparse.eval nodeValue1687 (mixedVector B) := by
    change mixedMoment B node1687 node1687Labels = _
    exact sound1687 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h2143 : mixedVector B (Sum.inr 2143) = Sparse.eval nodeValue2143 (mixedVector B) := by
    change mixedMoment B node2143 node2143Labels = _
    exact sound2143 B hB hF
  have h2146 : mixedVector B (Sum.inr 2146) = Sparse.eval nodeValue2146 (mixedVector B) := by
    change mixedMoment B node2146 node2146Labels = _
    exact sound2146 B hB hF
  have h2159 : mixedVector B (Sum.inr 2159) = Sparse.eval nodeValue2159 (mixedVector B) := by
    change mixedMoment B node2159 node2159Labels = _
    exact sound2159 B hB hF
  have h2163 : mixedVector B (Sum.inr 2163) = Sparse.eval nodeValue2163 (mixedVector B) := by
    change mixedMoment B node2163 node2163Labels = _
    exact sound2163 B hB hF
  have h2171 : mixedVector B (Sum.inr 2171) = Sparse.eval nodeValue2171 (mixedVector B) := by
    change mixedMoment B node2171 node2171Labels = _
    exact sound2171 B hB hF
  have h2180 : mixedVector B (Sum.inr 2180) = Sparse.eval nodeValue2180 (mixedVector B) := by
    change mixedMoment B node2180 node2180Labels = _
    exact sound2180 B hB hF
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
  have h2222 : mixedVector B (Sum.inr 2222) = Sparse.eval nodeValue2222 (mixedVector B) := by
    change mixedMoment B node2222 node2222Labels = _
    exact sound2222 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h2664 : mixedVector B (Sum.inr 2664) = Sparse.eval nodeValue2664 (mixedVector B) := by
    change mixedMoment B node2664 node2664Labels = _
    exact sound2664 B hB hF
  have h2680 : mixedVector B (Sum.inr 2680) = Sparse.eval nodeValue2680 (mixedVector B) := by
    change mixedMoment B node2680 node2680Labels = _
    exact sound2680 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  simpa only [sourceForm2297, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1669, h1683, h1687, h1741, h2143, h2146, h2159, h2163, h2171, h2180, h2193, h2197, h2208, h2218, h2222, h2268, h2281, h2664, h2680, h2726, h2734, reducedSource1875] using sourceEq2297 B hB

theorem rowSound1875 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1875 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1875, numericCheck1875, reducedZero1875 B hB hF, mul_zero]

theorem reducedZero1876 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1876 (mixedVector B) = 0 := by
  have h1809 : mixedVector B (Sum.inr 1809) = Sparse.eval nodeValue1809 (mixedVector B) := by
    change mixedMoment B node1809 node1809Labels = _
    exact sound1809 B hB hF
  have h1817 : mixedVector B (Sum.inr 1817) = Sparse.eval nodeValue1817 (mixedVector B) := by
    change mixedMoment B node1817 node1817Labels = _
    exact sound1817 B hB hF
  have h1820 : mixedVector B (Sum.inr 1820) = Sparse.eval nodeValue1820 (mixedVector B) := by
    change mixedMoment B node1820 node1820Labels = _
    exact sound1820 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h3396 : mixedVector B (Sum.inr 3396) = Sparse.eval nodeValue3396 (mixedVector B) := by
    change mixedMoment B node3396 node3396Labels = _
    exact sound3396 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm2298, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1809, h1817, h1820, h2065, h3396, h4085, reducedSource1876] using sourceEq2298 B hB

theorem rowSound1876 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1876 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1876, numericCheck1876, reducedZero1876 B hB hF, mul_zero]

theorem reducedZero1878 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1878 (mixedVector B) = 0 := by
  have h1675 : mixedVector B (Sum.inr 1675) = Sparse.eval nodeValue1675 (mixedVector B) := by
    change mixedMoment B node1675 node1675Labels = _
    exact sound1675 B hB hF
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h1755 : mixedVector B (Sum.inr 1755) = Sparse.eval nodeValue1755 (mixedVector B) := by
    change mixedMoment B node1755 node1755Labels = _
    exact sound1755 B hB hF
  have h2152 : mixedVector B (Sum.inr 2152) = Sparse.eval nodeValue2152 (mixedVector B) := by
    change mixedMoment B node2152 node2152Labels = _
    exact sound2152 B hB hF
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h2169 : mixedVector B (Sum.inr 2169) = Sparse.eval nodeValue2169 (mixedVector B) := by
    change mixedMoment B node2169 node2169Labels = _
    exact sound2169 B hB hF
  have h2174 : mixedVector B (Sum.inr 2174) = Sparse.eval nodeValue2174 (mixedVector B) := by
    change mixedMoment B node2174 node2174Labels = _
    exact sound2174 B hB hF
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h2186 : mixedVector B (Sum.inr 2186) = Sparse.eval nodeValue2186 (mixedVector B) := by
    change mixedMoment B node2186 node2186Labels = _
    exact sound2186 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2303, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1675, h1693, h1694, h1755, h2152, h2168, h2169, h2174, h2185, h2186, h2205, h2206, h2228, h2229, h2230, h2293, h2686, h2705, h2742, h2743, h4084, reducedSource1878] using sourceEq2303 B hB

theorem rowSound1878 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1878 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1878, numericCheck1878, reducedZero1878 B hB hF, mul_zero]

theorem reducedZero1879 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1879 (mixedVector B) = 0 := by
  have h1810 : mixedVector B (Sum.inr 1810) = Sparse.eval nodeValue1810 (mixedVector B) := by
    change mixedMoment B node1810 node1810Labels = _
    exact sound1810 B hB hF
  have h1818 : mixedVector B (Sum.inr 1818) = Sparse.eval nodeValue1818 (mixedVector B) := by
    change mixedMoment B node1818 node1818Labels = _
    exact sound1818 B hB hF
  have h1819 : mixedVector B (Sum.inr 1819) = Sparse.eval nodeValue1819 (mixedVector B) := by
    change mixedMoment B node1819 node1819Labels = _
    exact sound1819 B hB hF
  have h2066 : mixedVector B (Sum.inr 2066) = Sparse.eval nodeValue2066 (mixedVector B) := by
    change mixedMoment B node2066 node2066Labels = _
    exact sound2066 B hB hF
  have h3397 : mixedVector B (Sum.inr 3397) = Sparse.eval nodeValue3397 (mixedVector B) := by
    change mixedMoment B node3397 node3397Labels = _
    exact sound3397 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2304, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1810, h1818, h1819, h2066, h3397, h4084, reducedSource1879] using sourceEq2304 B hB

theorem rowSound1879 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1879 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1879, numericCheck1879, reducedZero1879 B hB hF, mul_zero]

theorem reducedZero1882 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1882 (mixedVector B) = 0 := by
  have h4065 : mixedVector B (Sum.inr 4065) = Sparse.eval nodeValue4065 (mixedVector B) := by
    change mixedMoment B node4065 node4065Labels = _
    exact sound4065 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  have h4078 : mixedVector B (Sum.inr 4078) = Sparse.eval nodeValue4078 (mixedVector B) := by
    change mixedMoment B node4078 node4078Labels = _
    exact sound4078 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2311, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4065, h4067, h4071, h4074, h4075, h4076, h4078, h4080, h4081, h4082, h4084, h4088, h4089, h4092, reducedSource1882] using sourceEq2311 B hB

theorem rowSound1882 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1882 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1882, numericCheck1882, reducedZero1882 B hB hF, mul_zero]

theorem reducedZero1883 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1883 (mixedVector B) = 0 := by
  have h923 : mixedVector B (Sum.inr 923) = Sparse.eval nodeValue923 (mixedVector B) := by
    change mixedMoment B node923 node923Labels = _
    exact sound923 B hB hF
  have h1806 : mixedVector B (Sum.inr 1806) = Sparse.eval nodeValue1806 (mixedVector B) := by
    change mixedMoment B node1806 node1806Labels = _
    exact sound1806 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2051 : mixedVector B (Sum.inr 2051) = Sparse.eval nodeValue2051 (mixedVector B) := by
    change mixedMoment B node2051 node2051Labels = _
    exact sound2051 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2312, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h923, h1806, h2021, h2034, h2051, h2058, h4084, reducedSource1883] using sourceEq2312 B hB

theorem rowSound1883 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1883 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1883, numericCheck1883, reducedZero1883 B hB hF, mul_zero]

theorem reducedZero1884 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1884 (mixedVector B) = 0 := by
  have h2440 : mixedVector B (Sum.inr 2440) = Sparse.eval nodeValue2440 (mixedVector B) := by
    change mixedMoment B node2440 node2440Labels = _
    exact sound2440 B hB hF
  have h3062 : mixedVector B (Sum.inr 3062) = Sparse.eval nodeValue3062 (mixedVector B) := by
    change mixedMoment B node3062 node3062Labels = _
    exact sound3062 B hB hF
  have h3189 : mixedVector B (Sum.inr 3189) = Sparse.eval nodeValue3189 (mixedVector B) := by
    change mixedMoment B node3189 node3189Labels = _
    exact sound3189 B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3789 : mixedVector B (Sum.inr 3789) = Sparse.eval nodeValue3789 (mixedVector B) := by
    change mixedMoment B node3789 node3789Labels = _
    exact sound3789 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2313, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2440, h3062, h3189, h3202, h3789, h4091, reducedSource1884] using sourceEq2313 B hB

theorem rowSound1884 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1884 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1884, numericCheck1884, reducedZero1884 B hB hF, mul_zero]

theorem reducedZero1885 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1885 (mixedVector B) = 0 := by
  have h920 : mixedVector B (Sum.inr 920) = Sparse.eval nodeValue920 (mixedVector B) := by
    change mixedMoment B node920 node920Labels = _
    exact sound920 B hB hF
  have h1803 : mixedVector B (Sum.inr 1803) = Sparse.eval nodeValue1803 (mixedVector B) := by
    change mixedMoment B node1803 node1803Labels = _
    exact sound1803 B hB hF
  have h2033 : mixedVector B (Sum.inr 2033) = Sparse.eval nodeValue2033 (mixedVector B) := by
    change mixedMoment B node2033 node2033Labels = _
    exact sound2033 B hB hF
  have h2051 : mixedVector B (Sum.inr 2051) = Sparse.eval nodeValue2051 (mixedVector B) := by
    change mixedMoment B node2051 node2051Labels = _
    exact sound2051 B hB hF
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2315, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h920, h1803, h2033, h2051, h2054, h4084, reducedSource1885] using sourceEq2315 B hB

theorem rowSound1885 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1885 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1885, numericCheck1885, reducedZero1885 B hB hF, mul_zero]

theorem reducedZero1886 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1886 (mixedVector B) = 0 := by
  have h2895 : mixedVector B (Sum.inr 2895) = Sparse.eval nodeValue2895 (mixedVector B) := by
    change mixedMoment B node2895 node2895Labels = _
    exact sound2895 B hB hF
  have h3164 : mixedVector B (Sum.inr 3164) = Sparse.eval nodeValue3164 (mixedVector B) := by
    change mixedMoment B node3164 node3164Labels = _
    exact sound3164 B hB hF
  have h3172 : mixedVector B (Sum.inr 3172) = Sparse.eval nodeValue3172 (mixedVector B) := by
    change mixedMoment B node3172 node3172Labels = _
    exact sound3172 B hB hF
  have h3197 : mixedVector B (Sum.inr 3197) = Sparse.eval nodeValue3197 (mixedVector B) := by
    change mixedMoment B node3197 node3197Labels = _
    exact sound3197 B hB hF
  have h3964 : mixedVector B (Sum.inr 3964) = Sparse.eval nodeValue3964 (mixedVector B) := by
    change mixedMoment B node3964 node3964Labels = _
    exact sound3964 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2316, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2895, h3164, h3172, h3197, h3964, h4091, reducedSource1886] using sourceEq2316 B hB

theorem rowSound1886 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1886 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1886, numericCheck1886, reducedZero1886 B hB hF, mul_zero]

theorem reducedZero1887 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1887 (mixedVector B) = 0 := by
  have h2430 : mixedVector B (Sum.inr 2430) = Sparse.eval nodeValue2430 (mixedVector B) := by
    change mixedMoment B node2430 node2430Labels = _
    exact sound2430 B hB hF
  have h3162 : mixedVector B (Sum.inr 3162) = Sparse.eval nodeValue3162 (mixedVector B) := by
    change mixedMoment B node3162 node3162Labels = _
    exact sound3162 B hB hF
  have h3163 : mixedVector B (Sum.inr 3163) = Sparse.eval nodeValue3163 (mixedVector B) := by
    change mixedMoment B node3163 node3163Labels = _
    exact sound3163 B hB hF
  have h3170 : mixedVector B (Sum.inr 3170) = Sparse.eval nodeValue3170 (mixedVector B) := by
    change mixedMoment B node3170 node3170Labels = _
    exact sound3170 B hB hF
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2318, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2430, h3162, h3163, h3170, h3196, h3782, h4092, reducedSource1887] using sourceEq2318 B hB

theorem rowSound1887 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1887 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1887, numericCheck1887, reducedZero1887 B hB hF, mul_zero]

theorem sourceRowsAt1872 : MixedData.sourceRows (1872 : Fin 2425) =
    MixedData.row1872 := by decide +kernel

theorem sourceRowsAt1873 : MixedData.sourceRows (1873 : Fin 2425) =
    MixedData.row1873 := by decide +kernel

theorem sourceRowsAt1874 : MixedData.sourceRows (1874 : Fin 2425) =
    MixedData.row1874 := by decide +kernel

theorem sourceRowsAt1875 : MixedData.sourceRows (1875 : Fin 2425) =
    MixedData.row1875 := by decide +kernel

theorem sourceRowsAt1876 : MixedData.sourceRows (1876 : Fin 2425) =
    MixedData.row1876 := by decide +kernel

theorem sourceRowsAt1877 : MixedData.sourceRows (1877 : Fin 2425) =
    MixedData.row1877 := by decide +kernel

theorem sourceRowsAt1878 : MixedData.sourceRows (1878 : Fin 2425) =
    MixedData.row1878 := by decide +kernel

theorem sourceRowsAt1879 : MixedData.sourceRows (1879 : Fin 2425) =
    MixedData.row1879 := by decide +kernel

theorem sourceRowsAt1880 : MixedData.sourceRows (1880 : Fin 2425) =
    MixedData.row1880 := by decide +kernel

theorem sourceRowsAt1881 : MixedData.sourceRows (1881 : Fin 2425) =
    MixedData.row1881 := by decide +kernel

theorem sourceRowsAt1882 : MixedData.sourceRows (1882 : Fin 2425) =
    MixedData.row1882 := by decide +kernel

theorem sourceRowsAt1883 : MixedData.sourceRows (1883 : Fin 2425) =
    MixedData.row1883 := by decide +kernel

theorem sourceRowsAt1884 : MixedData.sourceRows (1884 : Fin 2425) =
    MixedData.row1884 := by decide +kernel

theorem sourceRowsAt1885 : MixedData.sourceRows (1885 : Fin 2425) =
    MixedData.row1885 := by decide +kernel

theorem sourceRowsAt1886 : MixedData.sourceRows (1886 : Fin 2425) =
    MixedData.row1886 := by decide +kernel

theorem sourceRowsAt1887 : MixedData.sourceRows (1887 : Fin 2425) =
    MixedData.row1887 := by decide +kernel

theorem chunkSound117_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 117) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1872 ∨ k.val = 1873 ∨ k.val = 1874 ∨ k.val = 1875 ∨ k.val = 1876 ∨ k.val = 1877 ∨ k.val = 1878 ∨ k.val = 1879 ∨ k.val = 1880 ∨ k.val = 1881 ∨ k.val = 1882 ∨ k.val = 1883 ∨ k.val = 1884 ∨ k.val = 1885 ∨ k.val = 1886 ∨ k.val = 1887 := by omega
  rcases heq with h1872 | h1873 | h1874 | h1875 | h1876 | h1877 | h1878 | h1879 | h1880 | h1881 | h1882 | h1883 | h1884 | h1885 | h1886 | h1887
  · have he : k = (1872 : Fin 2425) := Fin.ext h1872
    subst k
    rw [sourceRowsAt1872]
    exact rowSound1872_e B hB hF
  · have he : k = (1873 : Fin 2425) := Fin.ext h1873
    subst k
    rw [sourceRowsAt1873]
    exact rowSound1873_e B hB hF
  · have he : k = (1874 : Fin 2425) := Fin.ext h1874
    subst k
    rw [sourceRowsAt1874]
    exact rowSound1874_e B hB hF
  · have he : k = (1875 : Fin 2425) := Fin.ext h1875
    subst k
    rw [sourceRowsAt1875]
    exact rowSound1875 B hB hF
  · have he : k = (1876 : Fin 2425) := Fin.ext h1876
    subst k
    rw [sourceRowsAt1876]
    exact rowSound1876 B hB hF
  · have he : k = (1877 : Fin 2425) := Fin.ext h1877
    subst k
    rw [sourceRowsAt1877]
    exact rowSound1877_e B hB hF
  · have he : k = (1878 : Fin 2425) := Fin.ext h1878
    subst k
    rw [sourceRowsAt1878]
    exact rowSound1878 B hB hF
  · have he : k = (1879 : Fin 2425) := Fin.ext h1879
    subst k
    rw [sourceRowsAt1879]
    exact rowSound1879 B hB hF
  · have he : k = (1880 : Fin 2425) := Fin.ext h1880
    subst k
    rw [sourceRowsAt1880]
    exact rowSound1880_e B hB hF
  · have he : k = (1881 : Fin 2425) := Fin.ext h1881
    subst k
    rw [sourceRowsAt1881]
    exact rowSound1881_e B hB hF
  · have he : k = (1882 : Fin 2425) := Fin.ext h1882
    subst k
    rw [sourceRowsAt1882]
    exact rowSound1882 B hB hF
  · have he : k = (1883 : Fin 2425) := Fin.ext h1883
    subst k
    rw [sourceRowsAt1883]
    exact rowSound1883 B hB hF
  · have he : k = (1884 : Fin 2425) := Fin.ext h1884
    subst k
    rw [sourceRowsAt1884]
    exact rowSound1884 B hB hF
  · have he : k = (1885 : Fin 2425) := Fin.ext h1885
    subst k
    rw [sourceRowsAt1885]
    exact rowSound1885 B hB hF
  · have he : k = (1886 : Fin 2425) := Fin.ext h1886
    subst k
    rw [sourceRowsAt1886]
    exact rowSound1886 B hB hF
  · have he : k = (1887 : Fin 2425) := Fin.ext h1887
    subst k
    rw [sourceRowsAt1887]
    exact rowSound1887 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e_oai
