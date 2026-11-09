-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:41:07.157172+00:00
-- url     : https://prove2.me/submissions/43c3c280-9673-40fc-b01c-833a21a29eb8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2080_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2082_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2084_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2085_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2086_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2088_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2089_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2090_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2091_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2092_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2093_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2094_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17918 raw17918Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw17918 raw17918Labels = mixedMoment B raw17918step0 raw17918step0Labels := by
      have hz : ∀ j, raw17918 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17918step0 = (fun i j => raw17918 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17918step0 raw17918; decide +kernel
      have hl : raw17918step0Labels = raw17918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17918 raw17918Labels permutation434 hz
    mixedMoment B raw17918step0 raw17918step0Labels = mixedMoment B raw17918step1 raw17918step1Labels := by
      have ha : raw17918step1 = (fun i j => raw17918step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17918step1 raw17918step0; decide +kernel
      have hl : raw17918step1Labels = raw17918step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17918step0 raw17918step0Labels permutation58 permutation7
    mixedMoment B raw17918step1 raw17918step1Labels = mixedMoment B raw17918step2 raw17918step2Labels := by
      have ha : raw17918step2 = -raw17918step1 := by apply Matrix.ext; change ∀ i j, raw17918step2 i j = -(raw17918step1 i j); unfold raw17918step2 raw17918step1; decide +kernel
      have hl : raw17918step2Labels = raw17918step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17918step2 raw17918step2Labels = mixedMoment B raw17918step3 raw17918step3Labels := by
      have ha : raw17918step3 = raw17918step2 := by apply Matrix.ext; unfold raw17918step3 raw17918step2; decide +kernel
      have hl : raw17918step2Labels = labelEmbedding1 ∘ raw17918step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17918step2 raw17918step2Labels raw17918step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17929 raw17929Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw17929 raw17929Labels = mixedMoment B raw17929step0 raw17929step0Labels := by
      have hz : ∀ j, raw17929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17929step0 = (fun i j => raw17929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17929step0 raw17929; decide +kernel
      have hl : raw17929step0Labels = raw17929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17929 raw17929Labels permutation434 hz
    mixedMoment B raw17929step0 raw17929step0Labels = mixedMoment B raw17929step1 raw17929step1Labels := by
      have ha : raw17929step1 = (fun i j => raw17929step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17929step1 raw17929step0; decide +kernel
      have hl : raw17929step1Labels = raw17929step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17929step0 raw17929step0Labels permutation58 permutation7
    mixedMoment B raw17929step1 raw17929step1Labels = mixedMoment B raw17929step2 raw17929step2Labels := by
      have ha : raw17929step2 = -raw17929step1 := by apply Matrix.ext; change ∀ i j, raw17929step2 i j = -(raw17929step1 i j); unfold raw17929step2 raw17929step1; decide +kernel
      have hl : raw17929step2Labels = raw17929step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17929step2 raw17929step2Labels = mixedMoment B raw17929step3 raw17929step3Labels := by
      have ha : raw17929step3 = raw17929step2 := by apply Matrix.ext; unfold raw17929step3 raw17929step2; decide +kernel
      have hl : raw17929step2Labels = labelEmbedding1 ∘ raw17929step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17929step2 raw17929step2Labels raw17929step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical17933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17933 raw17933Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw17933 raw17933Labels = mixedMoment B raw17933step0 raw17933step0Labels := by
      have ha : raw17933step0 = (fun i j => raw17933 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17933step0 raw17933; decide +kernel
      have hl : raw17933step0Labels = raw17933Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17933 raw17933Labels permutation194 permutation5
    mixedMoment B raw17933step0 raw17933step0Labels = mixedMoment B raw17933step1 raw17933step1Labels := by
      have ha : raw17933step1 = -raw17933step0 := by apply Matrix.ext; change ∀ i j, raw17933step1 i j = -(raw17933step0 i j); unfold raw17933step1 raw17933step0; decide +kernel
      have hl : raw17933step1Labels = raw17933step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17933step1 raw17933step1Labels = mixedMoment B raw17933step2 raw17933step2Labels := by
      have ha : raw17933step2 = raw17933step1 := by apply Matrix.ext; unfold raw17933step2 raw17933step1; decide +kernel
      have hl : raw17933step1Labels = labelEmbedding1 ∘ raw17933step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17933step1 raw17933step1Labels raw17933step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

theorem canonical17935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17935 raw17935Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw17935 raw17935Labels = mixedMoment B raw17935step0 raw17935step0Labels := by
      have ha : raw17935step0 = (fun i j => raw17935 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17935step0 raw17935; decide +kernel
      have hl : raw17935step0Labels = raw17935Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17935 raw17935Labels permutation639 permutation7
    mixedMoment B raw17935step0 raw17935step0Labels = mixedMoment B raw17935step1 raw17935step1Labels := by
      have ha : raw17935step1 = raw17935step0 := by apply Matrix.ext; unfold raw17935step1 raw17935step0; decide +kernel
      have hl : raw17935step0Labels = labelEmbedding1 ∘ raw17935step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17935step0 raw17935step0Labels raw17935step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

theorem canonical17936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17936 raw17936Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw17936 raw17936Labels = mixedMoment B raw17936step0 raw17936step0Labels := by
      have hz : ∀ j, raw17936 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17936step0 = (fun i j => raw17936 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17936step0 raw17936; decide +kernel
      have hl : raw17936step0Labels = raw17936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17936 raw17936Labels permutation520 hz
    mixedMoment B raw17936step0 raw17936step0Labels = mixedMoment B raw17936step1 raw17936step1Labels := by
      have ha : raw17936step1 = (fun i j => raw17936step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17936step1 raw17936step0; decide +kernel
      have hl : raw17936step1Labels = raw17936step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17936step0 raw17936step0Labels permutation144 permutation7
    mixedMoment B raw17936step1 raw17936step1Labels = mixedMoment B raw17936step2 raw17936step2Labels := by
      have ha : raw17936step2 = raw17936step1 := by apply Matrix.ext; unfold raw17936step2 raw17936step1; decide +kernel
      have hl : raw17936step1Labels = labelEmbedding1 ∘ raw17936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17936step1 raw17936step1Labels raw17936step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical17937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17937 raw17937Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw17937 raw17937Labels = mixedMoment B raw17937step0 raw17937step0Labels := by
      have ha : raw17937step0 = (fun i j => raw17937 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17937step0 raw17937; decide +kernel
      have hl : raw17937step0Labels = raw17937Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17937 raw17937Labels permutation273 permutation7
    mixedMoment B raw17937step0 raw17937step0Labels = mixedMoment B raw17937step1 raw17937step1Labels := by
      have ha : raw17937step1 = -raw17937step0 := by apply Matrix.ext; change ∀ i j, raw17937step1 i j = -(raw17937step0 i j); unfold raw17937step1 raw17937step0; decide +kernel
      have hl : raw17937step1Labels = raw17937step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17937step1 raw17937step1Labels = mixedMoment B raw17937step2 raw17937step2Labels := by
      have ha : raw17937step2 = raw17937step1 := by apply Matrix.ext; unfold raw17937step2 raw17937step1; decide +kernel
      have hl : raw17937step1Labels = labelEmbedding1 ∘ raw17937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17937step1 raw17937step1Labels raw17937step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3953 node3953Labels := by rfl

theorem canonical17939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17939 raw17939Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw17939 raw17939Labels = mixedMoment B raw17939step0 raw17939step0Labels := by
      have hz : ∀ j, raw17939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17939step0 = (fun i j => raw17939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17939step0 raw17939; decide +kernel
      have hl : raw17939step0Labels = raw17939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17939 raw17939Labels permutation434 hz
    mixedMoment B raw17939step0 raw17939step0Labels = mixedMoment B raw17939step1 raw17939step1Labels := by
      have ha : raw17939step1 = (fun i j => raw17939step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17939step1 raw17939step0; decide +kernel
      have hl : raw17939step1Labels = raw17939step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17939step0 raw17939step0Labels permutation58 permutation7
    mixedMoment B raw17939step1 raw17939step1Labels = mixedMoment B raw17939step2 raw17939step2Labels := by
      have ha : raw17939step2 = -raw17939step1 := by apply Matrix.ext; change ∀ i j, raw17939step2 i j = -(raw17939step1 i j); unfold raw17939step2 raw17939step1; decide +kernel
      have hl : raw17939step2Labels = raw17939step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17939step2 raw17939step2Labels = mixedMoment B raw17939step3 raw17939step3Labels := by
      have ha : raw17939step3 = raw17939step2 := by apply Matrix.ext; unfold raw17939step3 raw17939step2; decide +kernel
      have hl : raw17939step2Labels = labelEmbedding1 ∘ raw17939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17939step2 raw17939step2Labels raw17939step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

theorem canonical17944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17944 raw17944Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw17944 raw17944Labels = mixedMoment B raw17944step0 raw17944step0Labels := by
      have hz : ∀ j, raw17944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17944step0 = (fun i j => raw17944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17944step0 raw17944; decide +kernel
      have hl : raw17944step0Labels = raw17944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17944 raw17944Labels permutation434 hz
    mixedMoment B raw17944step0 raw17944step0Labels = mixedMoment B raw17944step1 raw17944step1Labels := by
      have ha : raw17944step1 = (fun i j => raw17944step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17944step1 raw17944step0; decide +kernel
      have hl : raw17944step1Labels = raw17944step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17944step0 raw17944step0Labels permutation144 permutation7
    mixedMoment B raw17944step1 raw17944step1Labels = mixedMoment B raw17944step2 raw17944step2Labels := by
      have ha : raw17944step2 = raw17944step1 := by apply Matrix.ext; unfold raw17944step2 raw17944step1; decide +kernel
      have hl : raw17944step1Labels = labelEmbedding1 ∘ raw17944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17944step1 raw17944step1Labels raw17944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19110 raw19110Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw19110 raw19110Labels = mixedMoment B raw19110step0 raw19110step0Labels := by
      have ha : raw19110step0 = (fun i j => raw19110 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19110step0 raw19110; decide +kernel
      have hl : raw19110step0Labels = raw19110Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19110 raw19110Labels permutation283 permutation7
    mixedMoment B raw19110step0 raw19110step0Labels = mixedMoment B raw19110step1 raw19110step1Labels := by
      have ha : raw19110step1 = -raw19110step0 := by apply Matrix.ext; change ∀ i j, raw19110step1 i j = -(raw19110step0 i j); unfold raw19110step1 raw19110step0; decide +kernel
      have hl : raw19110step1Labels = raw19110step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19110step1 raw19110step1Labels = mixedMoment B raw19110step2 raw19110step2Labels := by
      have ha : raw19110step2 = raw19110step1 := by apply Matrix.ext; unfold raw19110step2 raw19110step1; decide +kernel
      have hl : raw19110step1Labels = labelEmbedding1 ∘ raw19110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19110step1 raw19110step1Labels raw19110step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

theorem canonical19121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19121 raw19121Labels = mixedMoment B node3765 node3765Labels := by
  calc
    mixedMoment B raw19121 raw19121Labels = mixedMoment B raw19121step0 raw19121step0Labels := by
      have ha : raw19121step0 = (fun i j => raw19121 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19121step0 raw19121; decide +kernel
      have hl : raw19121step0Labels = raw19121Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19121 raw19121Labels permutation283 permutation7
    mixedMoment B raw19121step0 raw19121step0Labels = mixedMoment B raw19121step1 raw19121step1Labels := by
      have ha : raw19121step1 = -raw19121step0 := by apply Matrix.ext; change ∀ i j, raw19121step1 i j = -(raw19121step0 i j); unfold raw19121step1 raw19121step0; decide +kernel
      have hl : raw19121step1Labels = raw19121step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19121step1 raw19121step1Labels = mixedMoment B raw19121step2 raw19121step2Labels := by
      have ha : raw19121step2 = raw19121step1 := by apply Matrix.ext; unfold raw19121step2 raw19121step1; decide +kernel
      have hl : raw19121step1Labels = labelEmbedding1 ∘ raw19121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19121step1 raw19121step1Labels raw19121step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3765 node3765Labels := by rfl

theorem canonical19126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19126 raw19126Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw19126 raw19126Labels = mixedMoment B raw19126step0 raw19126step0Labels := by
      have ha : raw19126step0 = (fun i j => raw19126 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19126step0 raw19126; decide +kernel
      have hl : raw19126step0Labels = raw19126Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19126 raw19126Labels permutation284 permutation7
    mixedMoment B raw19126step0 raw19126step0Labels = mixedMoment B raw19126step1 raw19126step1Labels := by
      have ha : raw19126step1 = -raw19126step0 := by apply Matrix.ext; change ∀ i j, raw19126step1 i j = -(raw19126step0 i j); unfold raw19126step1 raw19126step0; decide +kernel
      have hl : raw19126step1Labels = raw19126step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19126step1 raw19126step1Labels = mixedMoment B raw19126step2 raw19126step2Labels := by
      have ha : raw19126step2 = raw19126step1 := by apply Matrix.ext; unfold raw19126step2 raw19126step1; decide +kernel
      have hl : raw19126step1Labels = labelEmbedding1 ∘ raw19126step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19126step1 raw19126step1Labels raw19126step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

theorem canonical19131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19131 raw19131Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw19131 raw19131Labels = mixedMoment B raw19131step0 raw19131step0Labels := by
      have ha : raw19131step0 = (fun i j => raw19131 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19131step0 raw19131; decide +kernel
      have hl : raw19131step0Labels = raw19131Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19131 raw19131Labels permutation283 permutation7
    mixedMoment B raw19131step0 raw19131step0Labels = mixedMoment B raw19131step1 raw19131step1Labels := by
      have ha : raw19131step1 = -raw19131step0 := by apply Matrix.ext; change ∀ i j, raw19131step1 i j = -(raw19131step0 i j); unfold raw19131step1 raw19131step0; decide +kernel
      have hl : raw19131step1Labels = raw19131step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19131step1 raw19131step1Labels = mixedMoment B raw19131step2 raw19131step2Labels := by
      have ha : raw19131step2 = raw19131step1 := by apply Matrix.ext; unfold raw19131step2 raw19131step1; decide +kernel
      have hl : raw19131step1Labels = labelEmbedding1 ∘ raw19131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19131step1 raw19131step1Labels raw19131step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

theorem canonical19135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19135 raw19135Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw19135 raw19135Labels = mixedMoment B raw19135step0 raw19135step0Labels := by
      have ha : raw19135step0 = (fun i j => raw19135 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19135step0 raw19135; decide +kernel
      have hl : raw19135step0Labels = raw19135Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19135 raw19135Labels permutation184 permutation5
    mixedMoment B raw19135step0 raw19135step0Labels = mixedMoment B raw19135step1 raw19135step1Labels := by
      have ha : raw19135step1 = -raw19135step0 := by apply Matrix.ext; change ∀ i j, raw19135step1 i j = -(raw19135step0 i j); unfold raw19135step1 raw19135step0; decide +kernel
      have hl : raw19135step1Labels = raw19135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19135step1 raw19135step1Labels = mixedMoment B raw19135step2 raw19135step2Labels := by
      have ha : raw19135step2 = raw19135step1 := by apply Matrix.ext; unfold raw19135step2 raw19135step1; decide +kernel
      have hl : raw19135step1Labels = labelEmbedding1 ∘ raw19135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19135step1 raw19135step1Labels raw19135step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

theorem canonical19137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19137 raw19137Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw19137 raw19137Labels = mixedMoment B raw19137step0 raw19137step0Labels := by
      have ha : raw19137step0 = (fun i j => raw19137 (permutation615 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19137step0 raw19137; decide +kernel
      have hl : raw19137step0Labels = raw19137Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19137 raw19137Labels permutation615 permutation5
    mixedMoment B raw19137step0 raw19137step0Labels = mixedMoment B raw19137step1 raw19137step1Labels := by
      have ha : raw19137step1 = raw19137step0 := by apply Matrix.ext; unfold raw19137step1 raw19137step0; decide +kernel
      have hl : raw19137step0Labels = labelEmbedding1 ∘ raw19137step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19137step0 raw19137step0Labels raw19137step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

theorem canonical19138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19138 raw19138Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw19138 raw19138Labels = mixedMoment B raw19138step0 raw19138step0Labels := by
      have ha : raw19138step0 = (fun i j => raw19138 (permutation620 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19138step0 raw19138; decide +kernel
      have hl : raw19138step0Labels = raw19138Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19138 raw19138Labels permutation620 permutation5
    mixedMoment B raw19138step0 raw19138step0Labels = mixedMoment B raw19138step1 raw19138step1Labels := by
      have ha : raw19138step1 = raw19138step0 := by apply Matrix.ext; unfold raw19138step1 raw19138step0; decide +kernel
      have hl : raw19138step0Labels = labelEmbedding1 ∘ raw19138step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19138step0 raw19138step0Labels raw19138step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

theorem canonical19139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19139 raw19139Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw19139 raw19139Labels = mixedMoment B raw19139step0 raw19139step0Labels := by
      have ha : raw19139step0 = (fun i j => raw19139 (permutation614 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19139step0 raw19139; decide +kernel
      have hl : raw19139step0Labels = raw19139Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19139 raw19139Labels permutation614 permutation5
    mixedMoment B raw19139step0 raw19139step0Labels = mixedMoment B raw19139step1 raw19139step1Labels := by
      have ha : raw19139step1 = raw19139step0 := by apply Matrix.ext; unfold raw19139step1 raw19139step0; decide +kernel
      have hl : raw19139step0Labels = labelEmbedding1 ∘ raw19139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19139step0 raw19139step0Labels raw19139step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

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

theorem canonical28425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28425 raw28425Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw28425 raw28425Labels = mixedMoment B raw28425step0 raw28425step0Labels := by
      have hz : ∀ j, raw28425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28425step0 = (fun i j => raw28425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28425step0 raw28425; decide +kernel
      have hl : raw28425step0Labels = raw28425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28425 raw28425Labels permutation434 hz
    mixedMoment B raw28425step0 raw28425step0Labels = mixedMoment B raw28425step1 raw28425step1Labels := by
      have hz : ∀ j, raw28425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28425step1 = (fun i j => raw28425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28425step1 raw28425step0; decide +kernel
      have hl : raw28425step1Labels = raw28425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28425step0 raw28425step0Labels permutation80 hz
    mixedMoment B raw28425step1 raw28425step1Labels = mixedMoment B raw28425step2 raw28425step2Labels := by
      have ha : raw28425step2 = (fun i j => raw28425step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28425step2 raw28425step1; decide +kernel
      have hl : raw28425step2Labels = raw28425step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28425step1 raw28425step1Labels permutation30 permutation7
    mixedMoment B raw28425step2 raw28425step2Labels = mixedMoment B raw28425step3 raw28425step3Labels := by
      have ha : raw28425step3 = raw28425step2 := by apply Matrix.ext; unfold raw28425step3 raw28425step2; decide +kernel
      have hl : raw28425step2Labels = labelEmbedding1 ∘ raw28425step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28425step2 raw28425step2Labels raw28425step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical28429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28429 raw28429Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw28429 raw28429Labels = mixedMoment B raw28429step0 raw28429step0Labels := by
      have hz : ∀ j, raw28429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28429step0 = (fun i j => raw28429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28429step0 raw28429; decide +kernel
      have hl : raw28429step0Labels = raw28429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28429 raw28429Labels permutation434 hz
    mixedMoment B raw28429step0 raw28429step0Labels = mixedMoment B raw28429step1 raw28429step1Labels := by
      have hz : ∀ j, raw28429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28429step1 = (fun i j => raw28429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28429step1 raw28429step0; decide +kernel
      have hl : raw28429step1Labels = raw28429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28429step0 raw28429step0Labels permutation80 hz
    mixedMoment B raw28429step1 raw28429step1Labels = mixedMoment B raw28429step2 raw28429step2Labels := by
      have ha : raw28429step2 = (fun i j => raw28429step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28429step2 raw28429step1; decide +kernel
      have hl : raw28429step2Labels = raw28429step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28429step1 raw28429step1Labels permutation30 permutation7
    mixedMoment B raw28429step2 raw28429step2Labels = mixedMoment B raw28429step3 raw28429step3Labels := by
      have ha : raw28429step3 = raw28429step2 := by apply Matrix.ext; unfold raw28429step3 raw28429step2; decide +kernel
      have hl : raw28429step2Labels = labelEmbedding1 ∘ raw28429step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28429step2 raw28429step2Labels raw28429step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical28441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28441 raw28441Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw28441 raw28441Labels = mixedMoment B raw28441step0 raw28441step0Labels := by
      have hz : ∀ j, raw28441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28441step0 = (fun i j => raw28441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28441step0 raw28441; decide +kernel
      have hl : raw28441step0Labels = raw28441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28441 raw28441Labels permutation346 hz
    mixedMoment B raw28441step0 raw28441step0Labels = mixedMoment B raw28441step1 raw28441step1Labels := by
      have ha : raw28441step1 = (fun i j => raw28441step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28441step1 raw28441step0; decide +kernel
      have hl : raw28441step1Labels = raw28441step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28441step0 raw28441step0Labels permutation144 permutation7
    mixedMoment B raw28441step1 raw28441step1Labels = mixedMoment B raw28441step2 raw28441step2Labels := by
      have ha : raw28441step2 = raw28441step1 := by apply Matrix.ext; unfold raw28441step2 raw28441step1; decide +kernel
      have hl : raw28441step1Labels = labelEmbedding1 ∘ raw28441step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28441step1 raw28441step1Labels raw28441step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

theorem canonical28444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28444 raw28444Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw28444 raw28444Labels = mixedMoment B raw28444step0 raw28444step0Labels := by
      have hz : ∀ j, raw28444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28444step0 = (fun i j => raw28444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28444step0 raw28444; decide +kernel
      have hl : raw28444step0Labels = raw28444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28444 raw28444Labels permutation346 hz
    mixedMoment B raw28444step0 raw28444step0Labels = mixedMoment B raw28444step1 raw28444step1Labels := by
      have ha : raw28444step1 = (fun i j => raw28444step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28444step1 raw28444step0; decide +kernel
      have hl : raw28444step1Labels = raw28444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28444step0 raw28444step0Labels permutation144 permutation7
    mixedMoment B raw28444step1 raw28444step1Labels = mixedMoment B raw28444step2 raw28444step2Labels := by
      have ha : raw28444step2 = raw28444step1 := by apply Matrix.ext; unfold raw28444step2 raw28444step1; decide +kernel
      have hl : raw28444step1Labels = labelEmbedding1 ∘ raw28444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28444step1 raw28444step1Labels raw28444step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical253
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32443 raw32443Labels = mixedMoment B node3798 node3798Labels := by
  calc
    mixedMoment B raw32443 raw32443Labels = mixedMoment B raw32443step0 raw32443step0Labels := by
      have ha : raw32443step0 = (fun i j => raw32443 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32443step0 raw32443; decide +kernel
      have hl : raw32443step0Labels = raw32443Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32443 raw32443Labels permutation662 permutation7
    mixedMoment B raw32443step0 raw32443step0Labels = mixedMoment B raw32443step1 raw32443step1Labels := by
      have ha : raw32443step1 = raw32443step0 := by apply Matrix.ext; unfold raw32443step1 raw32443step0; decide +kernel
      have hl : raw32443step0Labels = labelEmbedding1 ∘ raw32443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32443step0 raw32443step0Labels raw32443step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3798 node3798Labels := by rfl

theorem canonical32444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32444 raw32444Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw32444 raw32444Labels = mixedMoment B raw32444step0 raw32444step0Labels := by
      have ha : raw32444step0 = (fun i j => raw32444 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32444step0 raw32444; decide +kernel
      have hl : raw32444step0Labels = raw32444Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32444 raw32444Labels permutation664 permutation7
    mixedMoment B raw32444step0 raw32444step0Labels = mixedMoment B raw32444step1 raw32444step1Labels := by
      have ha : raw32444step1 = raw32444step0 := by apply Matrix.ext; unfold raw32444step1 raw32444step0; decide +kernel
      have hl : raw32444step0Labels = labelEmbedding1 ∘ raw32444step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32444step0 raw32444step0Labels raw32444step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical32445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32445 raw32445Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw32445 raw32445Labels = mixedMoment B raw32445step0 raw32445step0Labels := by
      have hz : ∀ j, raw32445 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32445step0 = (fun i j => raw32445 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32445step0 raw32445; decide +kernel
      have hl : raw32445step0Labels = raw32445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32445 raw32445Labels permutation520 hz
    mixedMoment B raw32445step0 raw32445step0Labels = mixedMoment B raw32445step1 raw32445step1Labels := by
      have ha : raw32445step1 = (fun i j => raw32445step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32445step1 raw32445step0; decide +kernel
      have hl : raw32445step1Labels = raw32445step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32445step0 raw32445step0Labels permutation151 permutation7
    mixedMoment B raw32445step1 raw32445step1Labels = mixedMoment B raw32445step2 raw32445step2Labels := by
      have ha : raw32445step2 = raw32445step1 := by apply Matrix.ext; unfold raw32445step2 raw32445step1; decide +kernel
      have hl : raw32445step1Labels = labelEmbedding1 ∘ raw32445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32445step1 raw32445step1Labels raw32445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical32446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32446 raw32446Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw32446 raw32446Labels = mixedMoment B raw32446step0 raw32446step0Labels := by
      have ha : raw32446step0 = (fun i j => raw32446 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32446step0 raw32446; decide +kernel
      have hl : raw32446step0Labels = raw32446Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32446 raw32446Labels permutation664 permutation7
    mixedMoment B raw32446step0 raw32446step0Labels = mixedMoment B raw32446step1 raw32446step1Labels := by
      have ha : raw32446step1 = raw32446step0 := by apply Matrix.ext; unfold raw32446step1 raw32446step0; decide +kernel
      have hl : raw32446step0Labels = labelEmbedding1 ∘ raw32446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32446step0 raw32446step0Labels raw32446step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical32453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32453 raw32453Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw32453 raw32453Labels = mixedMoment B raw32453step0 raw32453step0Labels := by
      have ha : raw32453step0 = (fun i j => raw32453 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32453step0 raw32453; decide +kernel
      have hl : raw32453step0Labels = raw32453Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32453 raw32453Labels permutation163 permutation5
    mixedMoment B raw32453step0 raw32453step0Labels = mixedMoment B raw32453step1 raw32453step1Labels := by
      have ha : raw32453step1 = -raw32453step0 := by apply Matrix.ext; change ∀ i j, raw32453step1 i j = -(raw32453step0 i j); unfold raw32453step1 raw32453step0; decide +kernel
      have hl : raw32453step1Labels = raw32453step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32453step1 raw32453step1Labels = mixedMoment B raw32453step2 raw32453step2Labels := by
      have ha : raw32453step2 = raw32453step1 := by apply Matrix.ext; unfold raw32453step2 raw32453step1; decide +kernel
      have hl : raw32453step1Labels = labelEmbedding1 ∘ raw32453step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32453step1 raw32453step1Labels raw32453step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

theorem canonical32458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32458 raw32458Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw32458 raw32458Labels = mixedMoment B raw32458step0 raw32458step0Labels := by
      have ha : raw32458step0 = (fun i j => raw32458 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32458step0 raw32458; decide +kernel
      have hl : raw32458step0Labels = raw32458Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32458 raw32458Labels permutation171 permutation5
    mixedMoment B raw32458step0 raw32458step0Labels = mixedMoment B raw32458step1 raw32458step1Labels := by
      have ha : raw32458step1 = -raw32458step0 := by apply Matrix.ext; change ∀ i j, raw32458step1 i j = -(raw32458step0 i j); unfold raw32458step1 raw32458step0; decide +kernel
      have hl : raw32458step1Labels = raw32458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32458step1 raw32458step1Labels = mixedMoment B raw32458step2 raw32458step2Labels := by
      have ha : raw32458step2 = raw32458step1 := by apply Matrix.ext; unfold raw32458step2 raw32458step1; decide +kernel
      have hl : raw32458step1Labels = labelEmbedding1 ∘ raw32458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32458step1 raw32458step1Labels raw32458step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

theorem canonical32463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32463 raw32463Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw32463 raw32463Labels = mixedMoment B raw32463step0 raw32463step0Labels := by
      have ha : raw32463step0 = (fun i j => raw32463 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32463step0 raw32463; decide +kernel
      have hl : raw32463step0Labels = raw32463Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32463 raw32463Labels permutation162 permutation5
    mixedMoment B raw32463step0 raw32463step0Labels = mixedMoment B raw32463step1 raw32463step1Labels := by
      have ha : raw32463step1 = -raw32463step0 := by apply Matrix.ext; change ∀ i j, raw32463step1 i j = -(raw32463step0 i j); unfold raw32463step1 raw32463step0; decide +kernel
      have hl : raw32463step1Labels = raw32463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32463step1 raw32463step1Labels = mixedMoment B raw32463step2 raw32463step2Labels := by
      have ha : raw32463step2 = raw32463step1 := by apply Matrix.ext; unfold raw32463step2 raw32463step1; decide +kernel
      have hl : raw32463step1Labels = labelEmbedding1 ∘ raw32463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32463step1 raw32463step1Labels raw32463step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

theorem canonical32468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32468 raw32468Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw32468 raw32468Labels = mixedMoment B raw32468step0 raw32468step0Labels := by
      have ha : raw32468step0 = (fun i j => raw32468 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32468step0 raw32468; decide +kernel
      have hl : raw32468step0Labels = raw32468Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32468 raw32468Labels permutation158 permutation5
    mixedMoment B raw32468step0 raw32468step0Labels = mixedMoment B raw32468step1 raw32468step1Labels := by
      have ha : raw32468step1 = -raw32468step0 := by apply Matrix.ext; change ∀ i j, raw32468step1 i j = -(raw32468step0 i j); unfold raw32468step1 raw32468step0; decide +kernel
      have hl : raw32468step1Labels = raw32468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32468step1 raw32468step1Labels = mixedMoment B raw32468step2 raw32468step2Labels := by
      have ha : raw32468step2 = raw32468step1 := by apply Matrix.ext; unfold raw32468step2 raw32468step1; decide +kernel
      have hl : raw32468step1Labels = labelEmbedding1 ∘ raw32468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32468step1 raw32468step1Labels raw32468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical283
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36311 raw36311Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw36311 raw36311Labels = mixedMoment B raw36311step0 raw36311step0Labels := by
      have ha : raw36311step0 = (fun i j => raw36311 (permutation275 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36311step0 raw36311; decide +kernel
      have hl : raw36311step0Labels = raw36311Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36311 raw36311Labels permutation275 permutation5
    mixedMoment B raw36311step0 raw36311step0Labels = mixedMoment B raw36311step1 raw36311step1Labels := by
      have ha : raw36311step1 = -raw36311step0 := by apply Matrix.ext; change ∀ i j, raw36311step1 i j = -(raw36311step0 i j); unfold raw36311step1 raw36311step0; decide +kernel
      have hl : raw36311step1Labels = raw36311step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36311step1 raw36311step1Labels = mixedMoment B raw36311step2 raw36311step2Labels := by
      have ha : raw36311step2 = raw36311step1 := by apply Matrix.ext; unfold raw36311step2 raw36311step1; decide +kernel
      have hl : raw36311step1Labels = labelEmbedding1 ∘ raw36311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36311step1 raw36311step1Labels raw36311step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical36312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36312 raw36312Labels = mixedMoment B node3798 node3798Labels := by
  calc
    mixedMoment B raw36312 raw36312Labels = mixedMoment B raw36312step0 raw36312step0Labels := by
      have ha : raw36312step0 = (fun i j => raw36312 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36312step0 raw36312; decide +kernel
      have hl : raw36312step0Labels = raw36312Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36312 raw36312Labels permutation660 permutation7
    mixedMoment B raw36312step0 raw36312step0Labels = mixedMoment B raw36312step1 raw36312step1Labels := by
      have ha : raw36312step1 = raw36312step0 := by apply Matrix.ext; unfold raw36312step1 raw36312step0; decide +kernel
      have hl : raw36312step0Labels = labelEmbedding1 ∘ raw36312step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36312step0 raw36312step0Labels raw36312step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3798 node3798Labels := by rfl

theorem canonical36313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36313 raw36313Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw36313 raw36313Labels = mixedMoment B raw36313step0 raw36313step0Labels := by
      have ha : raw36313step0 = (fun i j => raw36313 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36313step0 raw36313; decide +kernel
      have hl : raw36313step0Labels = raw36313Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36313 raw36313Labels permutation663 permutation7
    mixedMoment B raw36313step0 raw36313step0Labels = mixedMoment B raw36313step1 raw36313step1Labels := by
      have ha : raw36313step1 = raw36313step0 := by apply Matrix.ext; unfold raw36313step1 raw36313step0; decide +kernel
      have hl : raw36313step0Labels = labelEmbedding1 ∘ raw36313step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36313step0 raw36313step0Labels raw36313step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical36314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36314 raw36314Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw36314 raw36314Labels = mixedMoment B raw36314step0 raw36314step0Labels := by
      have hz : ∀ j, raw36314 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36314step0 = (fun i j => raw36314 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36314step0 raw36314; decide +kernel
      have hl : raw36314step0Labels = raw36314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36314 raw36314Labels permutation520 hz
    mixedMoment B raw36314step0 raw36314step0Labels = mixedMoment B raw36314step1 raw36314step1Labels := by
      have ha : raw36314step1 = (fun i j => raw36314step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36314step1 raw36314step0; decide +kernel
      have hl : raw36314step1Labels = raw36314step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36314step0 raw36314step0Labels permutation150 permutation7
    mixedMoment B raw36314step1 raw36314step1Labels = mixedMoment B raw36314step2 raw36314step2Labels := by
      have ha : raw36314step2 = raw36314step1 := by apply Matrix.ext; unfold raw36314step2 raw36314step1; decide +kernel
      have hl : raw36314step1Labels = labelEmbedding1 ∘ raw36314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36314step1 raw36314step1Labels raw36314step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical36315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36315 raw36315Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw36315 raw36315Labels = mixedMoment B raw36315step0 raw36315step0Labels := by
      have ha : raw36315step0 = (fun i j => raw36315 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36315step0 raw36315; decide +kernel
      have hl : raw36315step0Labels = raw36315Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36315 raw36315Labels permutation663 permutation7
    mixedMoment B raw36315step0 raw36315step0Labels = mixedMoment B raw36315step1 raw36315step1Labels := by
      have ha : raw36315step1 = raw36315step0 := by apply Matrix.ext; unfold raw36315step1 raw36315step0; decide +kernel
      have hl : raw36315step0Labels = labelEmbedding1 ∘ raw36315step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36315step0 raw36315step0Labels raw36315step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical36316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36316 raw36316Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw36316 raw36316Labels = mixedMoment B raw36316step0 raw36316step0Labels := by
      have ha : raw36316step0 = (fun i j => raw36316 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36316step0 raw36316; decide +kernel
      have hl : raw36316step0Labels = raw36316Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36316 raw36316Labels permutation162 permutation5
    mixedMoment B raw36316step0 raw36316step0Labels = mixedMoment B raw36316step1 raw36316step1Labels := by
      have ha : raw36316step1 = -raw36316step0 := by apply Matrix.ext; change ∀ i j, raw36316step1 i j = -(raw36316step0 i j); unfold raw36316step1 raw36316step0; decide +kernel
      have hl : raw36316step1Labels = raw36316step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36316step1 raw36316step1Labels = mixedMoment B raw36316step2 raw36316step2Labels := by
      have ha : raw36316step2 = raw36316step1 := by apply Matrix.ext; unfold raw36316step2 raw36316step1; decide +kernel
      have hl : raw36316step1Labels = labelEmbedding1 ∘ raw36316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36316step1 raw36316step1Labels raw36316step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical36317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36317 raw36317Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw36317 raw36317Labels = mixedMoment B raw36317step0 raw36317step0Labels := by
      have ha : raw36317step0 = (fun i j => raw36317 (permutation276 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36317step0 raw36317; decide +kernel
      have hl : raw36317step0Labels = raw36317Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36317 raw36317Labels permutation276 permutation5
    mixedMoment B raw36317step0 raw36317step0Labels = mixedMoment B raw36317step1 raw36317step1Labels := by
      have ha : raw36317step1 = -raw36317step0 := by apply Matrix.ext; change ∀ i j, raw36317step1 i j = -(raw36317step0 i j); unfold raw36317step1 raw36317step0; decide +kernel
      have hl : raw36317step1Labels = raw36317step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36317step1 raw36317step1Labels = mixedMoment B raw36317step2 raw36317step2Labels := by
      have ha : raw36317step2 = raw36317step1 := by apply Matrix.ext; unfold raw36317step2 raw36317step1; decide +kernel
      have hl : raw36317step1Labels = labelEmbedding1 ∘ raw36317step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36317step1 raw36317step1Labels raw36317step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

theorem canonical36318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36318 raw36318Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw36318 raw36318Labels = mixedMoment B raw36318step0 raw36318step0Labels := by
      have ha : raw36318step0 = (fun i j => raw36318 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36318step0 raw36318; decide +kernel
      have hl : raw36318step0Labels = raw36318Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36318 raw36318Labels permutation663 permutation7
    mixedMoment B raw36318step0 raw36318step0Labels = mixedMoment B raw36318step1 raw36318step1Labels := by
      have ha : raw36318step1 = raw36318step0 := by apply Matrix.ext; unfold raw36318step1 raw36318step0; decide +kernel
      have hl : raw36318step0Labels = labelEmbedding1 ∘ raw36318step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36318step0 raw36318step0Labels raw36318step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

theorem canonical36319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36319 raw36319Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw36319 raw36319Labels = mixedMoment B raw36319step0 raw36319step0Labels := by
      have hz : ∀ j, raw36319 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36319step0 = (fun i j => raw36319 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36319step0 raw36319; decide +kernel
      have hl : raw36319step0Labels = raw36319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36319 raw36319Labels permutation520 hz
    mixedMoment B raw36319step0 raw36319step0Labels = mixedMoment B raw36319step1 raw36319step1Labels := by
      have ha : raw36319step1 = (fun i j => raw36319step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36319step1 raw36319step0; decide +kernel
      have hl : raw36319step1Labels = raw36319step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36319step0 raw36319step0Labels permutation150 permutation7
    mixedMoment B raw36319step1 raw36319step1Labels = mixedMoment B raw36319step2 raw36319step2Labels := by
      have ha : raw36319step2 = raw36319step1 := by apply Matrix.ext; unfold raw36319step2 raw36319step1; decide +kernel
      have hl : raw36319step1Labels = labelEmbedding1 ∘ raw36319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36319step1 raw36319step1Labels raw36319step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

theorem canonical36320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36320 raw36320Labels = mixedMoment B node3973 node3973Labels := by
  calc
    mixedMoment B raw36320 raw36320Labels = mixedMoment B raw36320step0 raw36320step0Labels := by
      have ha : raw36320step0 = (fun i j => raw36320 (permutation408 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36320step0 raw36320; decide +kernel
      have hl : raw36320step0Labels = raw36320Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36320 raw36320Labels permutation408 permutation5
    mixedMoment B raw36320step0 raw36320step0Labels = mixedMoment B raw36320step1 raw36320step1Labels := by
      have ha : raw36320step1 = raw36320step0 := by apply Matrix.ext; unfold raw36320step1 raw36320step0; decide +kernel
      have hl : raw36320step0Labels = labelEmbedding1 ∘ raw36320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36320step0 raw36320step0Labels raw36320step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3973 node3973Labels := by rfl

theorem canonical36321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36321 raw36321Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw36321 raw36321Labels = mixedMoment B raw36321step0 raw36321step0Labels := by
      have ha : raw36321step0 = (fun i j => raw36321 (permutation284 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36321step0 raw36321; decide +kernel
      have hl : raw36321step0Labels = raw36321Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36321 raw36321Labels permutation284 permutation5
    mixedMoment B raw36321step0 raw36321step0Labels = mixedMoment B raw36321step1 raw36321step1Labels := by
      have ha : raw36321step1 = -raw36321step0 := by apply Matrix.ext; change ∀ i j, raw36321step1 i j = -(raw36321step0 i j); unfold raw36321step1 raw36321step0; decide +kernel
      have hl : raw36321step1Labels = raw36321step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36321step1 raw36321step1Labels = mixedMoment B raw36321step2 raw36321step2Labels := by
      have ha : raw36321step2 = raw36321step1 := by apply Matrix.ext; unfold raw36321step2 raw36321step1; decide +kernel
      have hl : raw36321step1Labels = labelEmbedding1 ∘ raw36321step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36321step1 raw36321step1Labels raw36321step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

theorem canonical36322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36322 raw36322Labels = mixedMoment B node3756 node3756Labels := by
  calc
    mixedMoment B raw36322 raw36322Labels = mixedMoment B raw36322step0 raw36322step0Labels := by
      have ha : raw36322step0 = (fun i j => raw36322 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36322step0 raw36322; decide +kernel
      have hl : raw36322step0Labels = raw36322Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36322 raw36322Labels permutation663 permutation7
    mixedMoment B raw36322step0 raw36322step0Labels = mixedMoment B raw36322step1 raw36322step1Labels := by
      have ha : raw36322step1 = raw36322step0 := by apply Matrix.ext; unfold raw36322step1 raw36322step0; decide +kernel
      have hl : raw36322step0Labels = labelEmbedding1 ∘ raw36322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36322step0 raw36322step0Labels raw36322step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3756 node3756Labels := by rfl

theorem canonical36323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36323 raw36323Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw36323 raw36323Labels = mixedMoment B raw36323step0 raw36323step0Labels := by
      have hz : ∀ j, raw36323 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36323step0 = (fun i j => raw36323 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36323step0 raw36323; decide +kernel
      have hl : raw36323step0Labels = raw36323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36323 raw36323Labels permutation520 hz
    mixedMoment B raw36323step0 raw36323step0Labels = mixedMoment B raw36323step1 raw36323step1Labels := by
      have ha : raw36323step1 = (fun i j => raw36323step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36323step1 raw36323step0; decide +kernel
      have hl : raw36323step1Labels = raw36323step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36323step0 raw36323step0Labels permutation150 permutation7
    mixedMoment B raw36323step1 raw36323step1Labels = mixedMoment B raw36323step2 raw36323step2Labels := by
      have ha : raw36323step2 = raw36323step1 := by apply Matrix.ext; unfold raw36323step2 raw36323step1; decide +kernel
      have hl : raw36323step1Labels = labelEmbedding1 ∘ raw36323step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36323step1 raw36323step1Labels raw36323step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

theorem canonical36324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36324 raw36324Labels = mixedMoment B node3951 node3951Labels := by
  calc
    mixedMoment B raw36324 raw36324Labels = mixedMoment B raw36324step0 raw36324step0Labels := by
      have ha : raw36324step0 = (fun i j => raw36324 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36324step0 raw36324; decide +kernel
      have hl : raw36324step0Labels = raw36324Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36324 raw36324Labels permutation663 permutation7
    mixedMoment B raw36324step0 raw36324step0Labels = mixedMoment B raw36324step1 raw36324step1Labels := by
      have ha : raw36324step1 = raw36324step0 := by apply Matrix.ext; unfold raw36324step1 raw36324step0; decide +kernel
      have hl : raw36324step0Labels = labelEmbedding1 ∘ raw36324step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36324step0 raw36324step0Labels raw36324step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3951 node3951Labels := by rfl

theorem canonical36325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36325 raw36325Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw36325 raw36325Labels = mixedMoment B raw36325step0 raw36325step0Labels := by
      have ha : raw36325step0 = (fun i j => raw36325 (permutation275 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36325step0 raw36325; decide +kernel
      have hl : raw36325step0Labels = raw36325Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36325 raw36325Labels permutation275 permutation5
    mixedMoment B raw36325step0 raw36325step0Labels = mixedMoment B raw36325step1 raw36325step1Labels := by
      have ha : raw36325step1 = -raw36325step0 := by apply Matrix.ext; change ∀ i j, raw36325step1 i j = -(raw36325step0 i j); unfold raw36325step1 raw36325step0; decide +kernel
      have hl : raw36325step1Labels = raw36325step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36325step1 raw36325step1Labels = mixedMoment B raw36325step2 raw36325step2Labels := by
      have ha : raw36325step2 = raw36325step1 := by apply Matrix.ext; unfold raw36325step2 raw36325step1; decide +kernel
      have hl : raw36325step1Labels = labelEmbedding1 ∘ raw36325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36325step1 raw36325step1Labels raw36325step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

theorem canonical36326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36326 raw36326Labels = mixedMoment B node3792 node3792Labels := by
  calc
    mixedMoment B raw36326 raw36326Labels = mixedMoment B raw36326step0 raw36326step0Labels := by
      have ha : raw36326step0 = (fun i j => raw36326 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36326step0 raw36326; decide +kernel
      have hl : raw36326step0Labels = raw36326Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36326 raw36326Labels permutation663 permutation7
    mixedMoment B raw36326step0 raw36326step0Labels = mixedMoment B raw36326step1 raw36326step1Labels := by
      have ha : raw36326step1 = raw36326step0 := by apply Matrix.ext; unfold raw36326step1 raw36326step0; decide +kernel
      have hl : raw36326step0Labels = labelEmbedding1 ∘ raw36326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36326step0 raw36326step0Labels raw36326step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3792 node3792Labels := by rfl

theorem canonical36327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36327 raw36327Labels = mixedMoment B node3835 node3835Labels := by
  calc
    mixedMoment B raw36327 raw36327Labels = mixedMoment B raw36327step0 raw36327step0Labels := by
      have ha : raw36327step0 = (fun i j => raw36327 (permutation551 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36327step0 raw36327; decide +kernel
      have hl : raw36327step0Labels = raw36327Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36327 raw36327Labels permutation551 permutation5
    mixedMoment B raw36327step0 raw36327step0Labels = mixedMoment B raw36327step1 raw36327step1Labels := by
      have ha : raw36327step1 = raw36327step0 := by apply Matrix.ext; unfold raw36327step1 raw36327step0; decide +kernel
      have hl : raw36327step0Labels = labelEmbedding1 ∘ raw36327step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36327step0 raw36327step0Labels raw36327step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3835 node3835Labels := by rfl

theorem canonical36328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36328 raw36328Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw36328 raw36328Labels = mixedMoment B raw36328step0 raw36328step0Labels := by
      have ha : raw36328step0 = (fun i j => raw36328 (permutation545 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36328step0 raw36328; decide +kernel
      have hl : raw36328step0Labels = raw36328Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36328 raw36328Labels permutation545 permutation5
    mixedMoment B raw36328step0 raw36328step0Labels = mixedMoment B raw36328step1 raw36328step1Labels := by
      have ha : raw36328step1 = raw36328step0 := by apply Matrix.ext; unfold raw36328step1 raw36328step0; decide +kernel
      have hl : raw36328step0Labels = labelEmbedding1 ∘ raw36328step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36328step0 raw36328step0Labels raw36328step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

theorem canonical36329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36329 raw36329Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw36329 raw36329Labels = mixedMoment B raw36329step0 raw36329step0Labels := by
      have ha : raw36329step0 = (fun i j => raw36329 (permutation271 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36329step0 raw36329; decide +kernel
      have hl : raw36329step0Labels = raw36329Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36329 raw36329Labels permutation271 permutation5
    mixedMoment B raw36329step0 raw36329step0Labels = mixedMoment B raw36329step1 raw36329step1Labels := by
      have ha : raw36329step1 = -raw36329step0 := by apply Matrix.ext; change ∀ i j, raw36329step1 i j = -(raw36329step0 i j); unfold raw36329step1 raw36329step0; decide +kernel
      have hl : raw36329step1Labels = raw36329step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36329step1 raw36329step1Labels = mixedMoment B raw36329step2 raw36329step2Labels := by
      have ha : raw36329step2 = raw36329step1 := by apply Matrix.ext; unfold raw36329step2 raw36329step1; decide +kernel
      have hl : raw36329step1Labels = labelEmbedding1 ∘ raw36329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36329step1 raw36329step1Labels raw36329step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

theorem canonical36330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36330 raw36330Labels = mixedMoment B node3456 node3456Labels := by
  calc
    mixedMoment B raw36330 raw36330Labels = mixedMoment B raw36330step0 raw36330step0Labels := by
      have ha : raw36330step0 = (fun i j => raw36330 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36330step0 raw36330; decide +kernel
      have hl : raw36330step0Labels = raw36330Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36330 raw36330Labels permutation663 permutation7
    mixedMoment B raw36330step0 raw36330step0Labels = mixedMoment B raw36330step1 raw36330step1Labels := by
      have ha : raw36330step1 = raw36330step0 := by apply Matrix.ext; unfold raw36330step1 raw36330step0; decide +kernel
      have hl : raw36330step0Labels = labelEmbedding1 ∘ raw36330step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36330step0 raw36330step0Labels raw36330step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3456 node3456Labels := by rfl

theorem canonical36331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36331 raw36331Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw36331 raw36331Labels = mixedMoment B raw36331step0 raw36331step0Labels := by
      have ha : raw36331step0 = (fun i j => raw36331 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36331step0 raw36331; decide +kernel
      have hl : raw36331step0Labels = raw36331Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36331 raw36331Labels permutation663 permutation7
    mixedMoment B raw36331step0 raw36331step0Labels = mixedMoment B raw36331step1 raw36331step1Labels := by
      have ha : raw36331step1 = raw36331step0 := by apply Matrix.ext; unfold raw36331step1 raw36331step0; decide +kernel
      have hl : raw36331step0Labels = labelEmbedding1 ∘ raw36331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36331step0 raw36331step0Labels raw36331step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3520 node3520Labels := by rfl

theorem canonical36332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36332 raw36332Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw36332 raw36332Labels = mixedMoment B raw36332step0 raw36332step0Labels := by
      have hz : ∀ j, raw36332 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36332step0 = (fun i j => raw36332 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36332step0 raw36332; decide +kernel
      have hl : raw36332step0Labels = raw36332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36332 raw36332Labels permutation520 hz
    mixedMoment B raw36332step0 raw36332step0Labels = mixedMoment B raw36332step1 raw36332step1Labels := by
      have ha : raw36332step1 = (fun i j => raw36332step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36332step1 raw36332step0; decide +kernel
      have hl : raw36332step1Labels = raw36332step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36332step0 raw36332step0Labels permutation150 permutation7
    mixedMoment B raw36332step1 raw36332step1Labels = mixedMoment B raw36332step2 raw36332step2Labels := by
      have ha : raw36332step2 = raw36332step1 := by apply Matrix.ext; unfold raw36332step2 raw36332step1; decide +kernel
      have hl : raw36332step1Labels = labelEmbedding1 ∘ raw36332step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36332step1 raw36332step1Labels raw36332step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical284
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36403 raw36403Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw36403 raw36403Labels = mixedMoment B raw36403step0 raw36403step0Labels := by
      have ha : raw36403step0 = (fun i j => raw36403 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36403step0 raw36403; decide +kernel
      have hl : raw36403step0Labels = raw36403Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36403 raw36403Labels permutation283 permutation7
    mixedMoment B raw36403step0 raw36403step0Labels = mixedMoment B raw36403step1 raw36403step1Labels := by
      have ha : raw36403step1 = -raw36403step0 := by apply Matrix.ext; change ∀ i j, raw36403step1 i j = -(raw36403step0 i j); unfold raw36403step1 raw36403step0; decide +kernel
      have hl : raw36403step1Labels = raw36403step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36403step1 raw36403step1Labels = mixedMoment B raw36403step2 raw36403step2Labels := by
      have ha : raw36403step2 = raw36403step1 := by apply Matrix.ext; unfold raw36403step2 raw36403step1; decide +kernel
      have hl : raw36403step1Labels = labelEmbedding1 ∘ raw36403step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36403step1 raw36403step1Labels raw36403step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

theorem canonical36404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36404 raw36404Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw36404 raw36404Labels = mixedMoment B raw36404step0 raw36404step0Labels := by
      have ha : raw36404step0 = (fun i j => raw36404 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36404step0 raw36404; decide +kernel
      have hl : raw36404step0Labels = raw36404Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36404 raw36404Labels permutation283 permutation7
    mixedMoment B raw36404step0 raw36404step0Labels = mixedMoment B raw36404step1 raw36404step1Labels := by
      have ha : raw36404step1 = -raw36404step0 := by apply Matrix.ext; change ∀ i j, raw36404step1 i j = -(raw36404step0 i j); unfold raw36404step1 raw36404step0; decide +kernel
      have hl : raw36404step1Labels = raw36404step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36404step1 raw36404step1Labels = mixedMoment B raw36404step2 raw36404step2Labels := by
      have ha : raw36404step2 = raw36404step1 := by apply Matrix.ext; unfold raw36404step2 raw36404step1; decide +kernel
      have hl : raw36404step1Labels = labelEmbedding1 ∘ raw36404step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36404step1 raw36404step1Labels raw36404step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

theorem canonical36405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36405 raw36405Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw36405 raw36405Labels = mixedMoment B raw36405step0 raw36405step0Labels := by
      have ha : raw36405step0 = (fun i j => raw36405 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36405step0 raw36405; decide +kernel
      have hl : raw36405step0Labels = raw36405Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36405 raw36405Labels permutation283 permutation7
    mixedMoment B raw36405step0 raw36405step0Labels = mixedMoment B raw36405step1 raw36405step1Labels := by
      have ha : raw36405step1 = -raw36405step0 := by apply Matrix.ext; change ∀ i j, raw36405step1 i j = -(raw36405step0 i j); unfold raw36405step1 raw36405step0; decide +kernel
      have hl : raw36405step1Labels = raw36405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36405step1 raw36405step1Labels = mixedMoment B raw36405step2 raw36405step2Labels := by
      have ha : raw36405step2 = raw36405step1 := by apply Matrix.ext; unfold raw36405step2 raw36405step1; decide +kernel
      have hl : raw36405step1Labels = labelEmbedding1 ∘ raw36405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36405step1 raw36405step1Labels raw36405step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical36406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36406 raw36406Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw36406 raw36406Labels = mixedMoment B raw36406step0 raw36406step0Labels := by
      have ha : raw36406step0 = (fun i j => raw36406 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36406step0 raw36406; decide +kernel
      have hl : raw36406step0Labels = raw36406Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36406 raw36406Labels permutation284 permutation7
    mixedMoment B raw36406step0 raw36406step0Labels = mixedMoment B raw36406step1 raw36406step1Labels := by
      have ha : raw36406step1 = -raw36406step0 := by apply Matrix.ext; change ∀ i j, raw36406step1 i j = -(raw36406step0 i j); unfold raw36406step1 raw36406step0; decide +kernel
      have hl : raw36406step1Labels = raw36406step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36406step1 raw36406step1Labels = mixedMoment B raw36406step2 raw36406step2Labels := by
      have ha : raw36406step2 = raw36406step1 := by apply Matrix.ext; unfold raw36406step2 raw36406step1; decide +kernel
      have hl : raw36406step1Labels = labelEmbedding1 ∘ raw36406step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36406step1 raw36406step1Labels raw36406step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical36407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36407 raw36407Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw36407 raw36407Labels = mixedMoment B raw36407step0 raw36407step0Labels := by
      have ha : raw36407step0 = (fun i j => raw36407 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36407step0 raw36407; decide +kernel
      have hl : raw36407step0Labels = raw36407Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36407 raw36407Labels permutation283 permutation7
    mixedMoment B raw36407step0 raw36407step0Labels = mixedMoment B raw36407step1 raw36407step1Labels := by
      have ha : raw36407step1 = -raw36407step0 := by apply Matrix.ext; change ∀ i j, raw36407step1 i j = -(raw36407step0 i j); unfold raw36407step1 raw36407step0; decide +kernel
      have hl : raw36407step1Labels = raw36407step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36407step1 raw36407step1Labels = mixedMoment B raw36407step2 raw36407step2Labels := by
      have ha : raw36407step2 = raw36407step1 := by apply Matrix.ext; unfold raw36407step2 raw36407step1; decide +kernel
      have hl : raw36407step1Labels = labelEmbedding1 ∘ raw36407step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36407step1 raw36407step1Labels raw36407step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical36408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36408 raw36408Labels = mixedMoment B node3585 node3585Labels := by
  calc
    mixedMoment B raw36408 raw36408Labels = mixedMoment B raw36408step0 raw36408step0Labels := by
      have ha : raw36408step0 = (fun i j => raw36408 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36408step0 raw36408; decide +kernel
      have hl : raw36408step0Labels = raw36408Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36408 raw36408Labels permutation152 permutation5
    mixedMoment B raw36408step0 raw36408step0Labels = mixedMoment B raw36408step1 raw36408step1Labels := by
      have ha : raw36408step1 = -raw36408step0 := by apply Matrix.ext; change ∀ i j, raw36408step1 i j = -(raw36408step0 i j); unfold raw36408step1 raw36408step0; decide +kernel
      have hl : raw36408step1Labels = raw36408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36408step1 raw36408step1Labels = mixedMoment B raw36408step2 raw36408step2Labels := by
      have ha : raw36408step2 = raw36408step1 := by apply Matrix.ext; unfold raw36408step2 raw36408step1; decide +kernel
      have hl : raw36408step1Labels = labelEmbedding1 ∘ raw36408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36408step1 raw36408step1Labels raw36408step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3585 node3585Labels := by rfl

theorem canonical36409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36409 raw36409Labels = mixedMoment B node3416 node3416Labels := by
  calc
    mixedMoment B raw36409 raw36409Labels = mixedMoment B raw36409step0 raw36409step0Labels := by
      have ha : raw36409step0 = (fun i j => raw36409 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36409step0 raw36409; decide +kernel
      have hl : raw36409step0Labels = raw36409Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36409 raw36409Labels permutation283 permutation7
    mixedMoment B raw36409step0 raw36409step0Labels = mixedMoment B raw36409step1 raw36409step1Labels := by
      have ha : raw36409step1 = -raw36409step0 := by apply Matrix.ext; change ∀ i j, raw36409step1 i j = -(raw36409step0 i j); unfold raw36409step1 raw36409step0; decide +kernel
      have hl : raw36409step1Labels = raw36409step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36409step1 raw36409step1Labels = mixedMoment B raw36409step2 raw36409step2Labels := by
      have ha : raw36409step2 = raw36409step1 := by apply Matrix.ext; unfold raw36409step2 raw36409step1; decide +kernel
      have hl : raw36409step1Labels = labelEmbedding1 ∘ raw36409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36409step1 raw36409step1Labels raw36409step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3416 node3416Labels := by rfl

theorem canonical36410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36410 raw36410Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw36410 raw36410Labels = mixedMoment B raw36410step0 raw36410step0Labels := by
      have ha : raw36410step0 = (fun i j => raw36410 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36410step0 raw36410; decide +kernel
      have hl : raw36410step0Labels = raw36410Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36410 raw36410Labels permutation285 permutation7
    mixedMoment B raw36410step0 raw36410step0Labels = mixedMoment B raw36410step1 raw36410step1Labels := by
      have ha : raw36410step1 = -raw36410step0 := by apply Matrix.ext; change ∀ i j, raw36410step1 i j = -(raw36410step0 i j); unfold raw36410step1 raw36410step0; decide +kernel
      have hl : raw36410step1Labels = raw36410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36410step1 raw36410step1Labels = mixedMoment B raw36410step2 raw36410step2Labels := by
      have ha : raw36410step2 = raw36410step1 := by apply Matrix.ext; unfold raw36410step2 raw36410step1; decide +kernel
      have hl : raw36410step1Labels = labelEmbedding1 ∘ raw36410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36410step1 raw36410step1Labels raw36410step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

theorem canonical36411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36411 raw36411Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw36411 raw36411Labels = mixedMoment B raw36411step0 raw36411step0Labels := by
      have ha : raw36411step0 = (fun i j => raw36411 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36411step0 raw36411; decide +kernel
      have hl : raw36411step0Labels = raw36411Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36411 raw36411Labels permutation287 permutation7
    mixedMoment B raw36411step0 raw36411step0Labels = mixedMoment B raw36411step1 raw36411step1Labels := by
      have ha : raw36411step1 = -raw36411step0 := by apply Matrix.ext; change ∀ i j, raw36411step1 i j = -(raw36411step0 i j); unfold raw36411step1 raw36411step0; decide +kernel
      have hl : raw36411step1Labels = raw36411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36411step1 raw36411step1Labels = mixedMoment B raw36411step2 raw36411step2Labels := by
      have ha : raw36411step2 = raw36411step1 := by apply Matrix.ext; unfold raw36411step2 raw36411step1; decide +kernel
      have hl : raw36411step1Labels = labelEmbedding1 ∘ raw36411step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36411step1 raw36411step1Labels raw36411step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

theorem canonical36412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36412 raw36412Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw36412 raw36412Labels = mixedMoment B raw36412step0 raw36412step0Labels := by
      have ha : raw36412step0 = (fun i j => raw36412 (permutation178 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36412step0 raw36412; decide +kernel
      have hl : raw36412step0Labels = raw36412Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36412 raw36412Labels permutation178 permutation5
    mixedMoment B raw36412step0 raw36412step0Labels = mixedMoment B raw36412step1 raw36412step1Labels := by
      have ha : raw36412step1 = -raw36412step0 := by apply Matrix.ext; change ∀ i j, raw36412step1 i j = -(raw36412step0 i j); unfold raw36412step1 raw36412step0; decide +kernel
      have hl : raw36412step1Labels = raw36412step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36412step1 raw36412step1Labels = mixedMoment B raw36412step2 raw36412step2Labels := by
      have ha : raw36412step2 = raw36412step1 := by apply Matrix.ext; unfold raw36412step2 raw36412step1; decide +kernel
      have hl : raw36412step1Labels = labelEmbedding1 ∘ raw36412step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36412step1 raw36412step1Labels raw36412step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

theorem canonical36413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36413 raw36413Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw36413 raw36413Labels = mixedMoment B raw36413step0 raw36413step0Labels := by
      have ha : raw36413step0 = (fun i j => raw36413 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36413step0 raw36413; decide +kernel
      have hl : raw36413step0Labels = raw36413Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36413 raw36413Labels permutation284 permutation7
    mixedMoment B raw36413step0 raw36413step0Labels = mixedMoment B raw36413step1 raw36413step1Labels := by
      have ha : raw36413step1 = -raw36413step0 := by apply Matrix.ext; change ∀ i j, raw36413step1 i j = -(raw36413step0 i j); unfold raw36413step1 raw36413step0; decide +kernel
      have hl : raw36413step1Labels = raw36413step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36413step1 raw36413step1Labels = mixedMoment B raw36413step2 raw36413step2Labels := by
      have ha : raw36413step2 = raw36413step1 := by apply Matrix.ext; unfold raw36413step2 raw36413step1; decide +kernel
      have hl : raw36413step1Labels = labelEmbedding1 ∘ raw36413step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36413step1 raw36413step1Labels raw36413step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

theorem canonical36414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36414 raw36414Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw36414 raw36414Labels = mixedMoment B raw36414step0 raw36414step0Labels := by
      have ha : raw36414step0 = (fun i j => raw36414 (permutation661 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36414step0 raw36414; decide +kernel
      have hl : raw36414step0Labels = raw36414Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36414 raw36414Labels permutation661 permutation5
    mixedMoment B raw36414step0 raw36414step0Labels = mixedMoment B raw36414step1 raw36414step1Labels := by
      have ha : raw36414step1 = raw36414step0 := by apply Matrix.ext; unfold raw36414step1 raw36414step0; decide +kernel
      have hl : raw36414step0Labels = labelEmbedding1 ∘ raw36414step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36414step0 raw36414step0Labels raw36414step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

theorem canonical36415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36415 raw36415Labels = mixedMoment B node3768 node3768Labels := by
  calc
    mixedMoment B raw36415 raw36415Labels = mixedMoment B raw36415step0 raw36415step0Labels := by
      have ha : raw36415step0 = (fun i j => raw36415 (permutation653 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36415step0 raw36415; decide +kernel
      have hl : raw36415step0Labels = raw36415Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36415 raw36415Labels permutation653 permutation5
    mixedMoment B raw36415step0 raw36415step0Labels = mixedMoment B raw36415step1 raw36415step1Labels := by
      have ha : raw36415step1 = raw36415step0 := by apply Matrix.ext; unfold raw36415step1 raw36415step0; decide +kernel
      have hl : raw36415step0Labels = labelEmbedding1 ∘ raw36415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36415step0 raw36415step0Labels raw36415step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3768 node3768Labels := by rfl

theorem canonical36416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36416 raw36416Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw36416 raw36416Labels = mixedMoment B raw36416step0 raw36416step0Labels := by
      have ha : raw36416step0 = (fun i j => raw36416 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36416step0 raw36416; decide +kernel
      have hl : raw36416step0Labels = raw36416Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36416 raw36416Labels permutation176 permutation5
    mixedMoment B raw36416step0 raw36416step0Labels = mixedMoment B raw36416step1 raw36416step1Labels := by
      have ha : raw36416step1 = -raw36416step0 := by apply Matrix.ext; change ∀ i j, raw36416step1 i j = -(raw36416step0 i j); unfold raw36416step1 raw36416step0; decide +kernel
      have hl : raw36416step1Labels = raw36416step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36416step1 raw36416step1Labels = mixedMoment B raw36416step2 raw36416step2Labels := by
      have ha : raw36416step2 = raw36416step1 := by apply Matrix.ext; unfold raw36416step2 raw36416step1; decide +kernel
      have hl : raw36416step1Labels = labelEmbedding1 ∘ raw36416step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36416step1 raw36416step1Labels raw36416step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

theorem canonical36417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36417 raw36417Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw36417 raw36417Labels = mixedMoment B raw36417step0 raw36417step0Labels := by
      have ha : raw36417step0 = (fun i j => raw36417 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36417step0 raw36417; decide +kernel
      have hl : raw36417step0Labels = raw36417Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36417 raw36417Labels permutation283 permutation7
    mixedMoment B raw36417step0 raw36417step0Labels = mixedMoment B raw36417step1 raw36417step1Labels := by
      have ha : raw36417step1 = -raw36417step0 := by apply Matrix.ext; change ∀ i j, raw36417step1 i j = -(raw36417step0 i j); unfold raw36417step1 raw36417step0; decide +kernel
      have hl : raw36417step1Labels = raw36417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36417step1 raw36417step1Labels = mixedMoment B raw36417step2 raw36417step2Labels := by
      have ha : raw36417step2 = raw36417step1 := by apply Matrix.ext; unfold raw36417step2 raw36417step1; decide +kernel
      have hl : raw36417step1Labels = labelEmbedding1 ∘ raw36417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36417step1 raw36417step1Labels raw36417step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

theorem canonical36418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36418 raw36418Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw36418 raw36418Labels = mixedMoment B raw36418step0 raw36418step0Labels := by
      have ha : raw36418step0 = (fun i j => raw36418 (permutation685 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36418step0 raw36418; decide +kernel
      have hl : raw36418step0Labels = raw36418Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36418 raw36418Labels permutation685 permutation5
    mixedMoment B raw36418step0 raw36418step0Labels = mixedMoment B raw36418step1 raw36418step1Labels := by
      have ha : raw36418step1 = raw36418step0 := by apply Matrix.ext; unfold raw36418step1 raw36418step0; decide +kernel
      have hl : raw36418step0Labels = labelEmbedding1 ∘ raw36418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36418step0 raw36418step0Labels raw36418step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

theorem canonical36419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36419 raw36419Labels = mixedMoment B node3768 node3768Labels := by
  calc
    mixedMoment B raw36419 raw36419Labels = mixedMoment B raw36419step0 raw36419step0Labels := by
      have ha : raw36419step0 = (fun i j => raw36419 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36419step0 raw36419; decide +kernel
      have hl : raw36419step0Labels = raw36419Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36419 raw36419Labels permutation674 permutation5
    mixedMoment B raw36419step0 raw36419step0Labels = mixedMoment B raw36419step1 raw36419step1Labels := by
      have ha : raw36419step1 = raw36419step0 := by apply Matrix.ext; unfold raw36419step1 raw36419step0; decide +kernel
      have hl : raw36419step0Labels = labelEmbedding1 ∘ raw36419step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36419step0 raw36419step0Labels raw36419step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3768 node3768Labels := by rfl

theorem canonical36420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36420 raw36420Labels = mixedMoment B node2176 node2176Labels := by
  calc
    mixedMoment B raw36420 raw36420Labels = mixedMoment B raw36420step0 raw36420step0Labels := by
      have ha : raw36420step0 = (fun i j => raw36420 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36420step0 raw36420; decide +kernel
      have hl : raw36420step0Labels = raw36420Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36420 raw36420Labels permutation662 permutation5
    mixedMoment B raw36420step0 raw36420step0Labels = mixedMoment B raw36420step1 raw36420step1Labels := by
      have ha : raw36420step1 = raw36420step0 := by apply Matrix.ext; unfold raw36420step1 raw36420step0; decide +kernel
      have hl : raw36420step0Labels = labelEmbedding1 ∘ raw36420step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36420step0 raw36420step0Labels raw36420step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2176 node2176Labels := by rfl

theorem canonical36421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36421 raw36421Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw36421 raw36421Labels = mixedMoment B raw36421step0 raw36421step0Labels := by
      have ha : raw36421step0 = (fun i j => raw36421 (permutation663 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36421step0 raw36421; decide +kernel
      have hl : raw36421step0Labels = raw36421Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36421 raw36421Labels permutation663 permutation5
    mixedMoment B raw36421step0 raw36421step0Labels = mixedMoment B raw36421step1 raw36421step1Labels := by
      have ha : raw36421step1 = raw36421step0 := by apply Matrix.ext; unfold raw36421step1 raw36421step0; decide +kernel
      have hl : raw36421step0Labels = labelEmbedding1 ∘ raw36421step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36421step0 raw36421step0Labels raw36421step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2181 node2181Labels := by rfl

theorem canonical36422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36422 raw36422Labels = mixedMoment B node2178 node2178Labels := by
  calc
    mixedMoment B raw36422 raw36422Labels = mixedMoment B raw36422step0 raw36422step0Labels := by
      have ha : raw36422step0 = (fun i j => raw36422 (permutation661 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36422step0 raw36422; decide +kernel
      have hl : raw36422step0Labels = raw36422Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36422 raw36422Labels permutation661 permutation5
    mixedMoment B raw36422step0 raw36422step0Labels = mixedMoment B raw36422step1 raw36422step1Labels := by
      have ha : raw36422step1 = raw36422step0 := by apply Matrix.ext; unfold raw36422step1 raw36422step0; decide +kernel
      have hl : raw36422step0Labels = labelEmbedding1 ∘ raw36422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36422step0 raw36422step0Labels raw36422step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2178 node2178Labels := by rfl

theorem canonical36423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36423 raw36423Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw36423 raw36423Labels = mixedMoment B raw36423step0 raw36423step0Labels := by
      have ha : raw36423step0 = (fun i j => raw36423 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36423step0 raw36423; decide +kernel
      have hl : raw36423step0Labels = raw36423Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36423 raw36423Labels permutation674 permutation5
    mixedMoment B raw36423step0 raw36423step0Labels = mixedMoment B raw36423step1 raw36423step1Labels := by
      have ha : raw36423step1 = raw36423step0 := by apply Matrix.ext; unfold raw36423step1 raw36423step0; decide +kernel
      have hl : raw36423step0Labels = labelEmbedding1 ∘ raw36423step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36423step0 raw36423step0Labels raw36423step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

theorem canonical36424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36424 raw36424Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw36424 raw36424Labels = mixedMoment B raw36424step0 raw36424step0Labels := by
      have ha : raw36424step0 = (fun i j => raw36424 (permutation653 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36424step0 raw36424; decide +kernel
      have hl : raw36424step0Labels = raw36424Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36424 raw36424Labels permutation653 permutation5
    mixedMoment B raw36424step0 raw36424step0Labels = mixedMoment B raw36424step1 raw36424step1Labels := by
      have ha : raw36424step1 = raw36424step0 := by apply Matrix.ext; unfold raw36424step1 raw36424step0; decide +kernel
      have hl : raw36424step0Labels = labelEmbedding1 ∘ raw36424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36424step0 raw36424step0Labels raw36424step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical285
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36552 raw36552Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw36552 raw36552Labels = mixedMoment B raw36552step0 raw36552step0Labels := by
      have ha : raw36552step0 = (fun i j => raw36552 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36552step0 raw36552; decide +kernel
      have hl : raw36552step0Labels = raw36552Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36552 raw36552Labels permutation273 permutation7
    mixedMoment B raw36552step0 raw36552step0Labels = mixedMoment B raw36552step1 raw36552step1Labels := by
      have ha : raw36552step1 = -raw36552step0 := by apply Matrix.ext; change ∀ i j, raw36552step1 i j = -(raw36552step0 i j); unfold raw36552step1 raw36552step0; decide +kernel
      have hl : raw36552step1Labels = raw36552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36552step1 raw36552step1Labels = mixedMoment B raw36552step2 raw36552step2Labels := by
      have ha : raw36552step2 = raw36552step1 := by apply Matrix.ext; unfold raw36552step2 raw36552step1; decide +kernel
      have hl : raw36552step1Labels = labelEmbedding1 ∘ raw36552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36552step1 raw36552step1Labels raw36552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

theorem canonical36553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36553 raw36553Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw36553 raw36553Labels = mixedMoment B raw36553step0 raw36553step0Labels := by
      have ha : raw36553step0 = (fun i j => raw36553 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36553step0 raw36553; decide +kernel
      have hl : raw36553step0Labels = raw36553Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36553 raw36553Labels permutation273 permutation7
    mixedMoment B raw36553step0 raw36553step0Labels = mixedMoment B raw36553step1 raw36553step1Labels := by
      have ha : raw36553step1 = -raw36553step0 := by apply Matrix.ext; change ∀ i j, raw36553step1 i j = -(raw36553step0 i j); unfold raw36553step1 raw36553step0; decide +kernel
      have hl : raw36553step1Labels = raw36553step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36553step1 raw36553step1Labels = mixedMoment B raw36553step2 raw36553step2Labels := by
      have ha : raw36553step2 = raw36553step1 := by apply Matrix.ext; unfold raw36553step2 raw36553step1; decide +kernel
      have hl : raw36553step1Labels = labelEmbedding1 ∘ raw36553step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36553step1 raw36553step1Labels raw36553step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

theorem canonical36554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36554 raw36554Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw36554 raw36554Labels = mixedMoment B raw36554step0 raw36554step0Labels := by
      have hz : ∀ j, raw36554 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36554step0 = (fun i j => raw36554 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36554step0 raw36554; decide +kernel
      have hl : raw36554step0Labels = raw36554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36554 raw36554Labels permutation520 hz
    mixedMoment B raw36554step0 raw36554step0Labels = mixedMoment B raw36554step1 raw36554step1Labels := by
      have ha : raw36554step1 = (fun i j => raw36554step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36554step1 raw36554step0; decide +kernel
      have hl : raw36554step1Labels = raw36554step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36554step0 raw36554step0Labels permutation58 permutation7
    mixedMoment B raw36554step1 raw36554step1Labels = mixedMoment B raw36554step2 raw36554step2Labels := by
      have ha : raw36554step2 = -raw36554step1 := by apply Matrix.ext; change ∀ i j, raw36554step2 i j = -(raw36554step1 i j); unfold raw36554step2 raw36554step1; decide +kernel
      have hl : raw36554step2Labels = raw36554step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36554step2 raw36554step2Labels = mixedMoment B raw36554step3 raw36554step3Labels := by
      have ha : raw36554step3 = raw36554step2 := by apply Matrix.ext; unfold raw36554step3 raw36554step2; decide +kernel
      have hl : raw36554step2Labels = labelEmbedding1 ∘ raw36554step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36554step2 raw36554step2Labels raw36554step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical36555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36555 raw36555Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw36555 raw36555Labels = mixedMoment B raw36555step0 raw36555step0Labels := by
      have ha : raw36555step0 = (fun i j => raw36555 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36555step0 raw36555; decide +kernel
      have hl : raw36555step0Labels = raw36555Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36555 raw36555Labels permutation273 permutation7
    mixedMoment B raw36555step0 raw36555step0Labels = mixedMoment B raw36555step1 raw36555step1Labels := by
      have ha : raw36555step1 = -raw36555step0 := by apply Matrix.ext; change ∀ i j, raw36555step1 i j = -(raw36555step0 i j); unfold raw36555step1 raw36555step0; decide +kernel
      have hl : raw36555step1Labels = raw36555step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36555step1 raw36555step1Labels = mixedMoment B raw36555step2 raw36555step2Labels := by
      have ha : raw36555step2 = raw36555step1 := by apply Matrix.ext; unfold raw36555step2 raw36555step1; decide +kernel
      have hl : raw36555step1Labels = labelEmbedding1 ∘ raw36555step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36555step1 raw36555step1Labels raw36555step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical36556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36556 raw36556Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw36556 raw36556Labels = mixedMoment B raw36556step0 raw36556step0Labels := by
      have hz : ∀ j, raw36556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36556step0 = (fun i j => raw36556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36556step0 raw36556; decide +kernel
      have hl : raw36556step0Labels = raw36556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36556 raw36556Labels permutation434 hz
    mixedMoment B raw36556step0 raw36556step0Labels = mixedMoment B raw36556step1 raw36556step1Labels := by
      have ha : raw36556step1 = (fun i j => raw36556step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36556step1 raw36556step0; decide +kernel
      have hl : raw36556step1Labels = raw36556step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36556step0 raw36556step0Labels permutation144 permutation7
    mixedMoment B raw36556step1 raw36556step1Labels = mixedMoment B raw36556step2 raw36556step2Labels := by
      have ha : raw36556step2 = raw36556step1 := by apply Matrix.ext; unfold raw36556step2 raw36556step1; decide +kernel
      have hl : raw36556step1Labels = labelEmbedding1 ∘ raw36556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36556step1 raw36556step1Labels raw36556step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical36557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36557 raw36557Labels = mixedMoment B node3590 node3590Labels := by
  calc
    mixedMoment B raw36557 raw36557Labels = mixedMoment B raw36557step0 raw36557step0Labels := by
      have ha : raw36557step0 = (fun i j => raw36557 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36557step0 raw36557; decide +kernel
      have hl : raw36557step0Labels = raw36557Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36557 raw36557Labels permutation156 permutation5
    mixedMoment B raw36557step0 raw36557step0Labels = mixedMoment B raw36557step1 raw36557step1Labels := by
      have ha : raw36557step1 = -raw36557step0 := by apply Matrix.ext; change ∀ i j, raw36557step1 i j = -(raw36557step0 i j); unfold raw36557step1 raw36557step0; decide +kernel
      have hl : raw36557step1Labels = raw36557step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36557step1 raw36557step1Labels = mixedMoment B raw36557step2 raw36557step2Labels := by
      have ha : raw36557step2 = raw36557step1 := by apply Matrix.ext; unfold raw36557step2 raw36557step1; decide +kernel
      have hl : raw36557step1Labels = labelEmbedding1 ∘ raw36557step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36557step1 raw36557step1Labels raw36557step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3590 node3590Labels := by rfl

theorem canonical36558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36558 raw36558Labels = mixedMoment B node3404 node3404Labels := by
  calc
    mixedMoment B raw36558 raw36558Labels = mixedMoment B raw36558step0 raw36558step0Labels := by
      have ha : raw36558step0 = (fun i j => raw36558 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36558step0 raw36558; decide +kernel
      have hl : raw36558step0Labels = raw36558Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36558 raw36558Labels permutation273 permutation7
    mixedMoment B raw36558step0 raw36558step0Labels = mixedMoment B raw36558step1 raw36558step1Labels := by
      have ha : raw36558step1 = -raw36558step0 := by apply Matrix.ext; change ∀ i j, raw36558step1 i j = -(raw36558step0 i j); unfold raw36558step1 raw36558step0; decide +kernel
      have hl : raw36558step1Labels = raw36558step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36558step1 raw36558step1Labels = mixedMoment B raw36558step2 raw36558step2Labels := by
      have ha : raw36558step2 = raw36558step1 := by apply Matrix.ext; unfold raw36558step2 raw36558step1; decide +kernel
      have hl : raw36558step1Labels = labelEmbedding1 ∘ raw36558step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36558step1 raw36558step1Labels raw36558step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3404 node3404Labels := by rfl

theorem canonical36559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36559 raw36559Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw36559 raw36559Labels = mixedMoment B raw36559step0 raw36559step0Labels := by
      have hz : ∀ j, raw36559 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36559step0 = (fun i j => raw36559 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36559step0 raw36559; decide +kernel
      have hl : raw36559step0Labels = raw36559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36559 raw36559Labels permutation520 hz
    mixedMoment B raw36559step0 raw36559step0Labels = mixedMoment B raw36559step1 raw36559step1Labels := by
      have ha : raw36559step1 = (fun i j => raw36559step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36559step1 raw36559step0; decide +kernel
      have hl : raw36559step1Labels = raw36559step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36559step0 raw36559step0Labels permutation58 permutation7
    mixedMoment B raw36559step1 raw36559step1Labels = mixedMoment B raw36559step2 raw36559step2Labels := by
      have ha : raw36559step2 = -raw36559step1 := by apply Matrix.ext; change ∀ i j, raw36559step2 i j = -(raw36559step1 i j); unfold raw36559step2 raw36559step1; decide +kernel
      have hl : raw36559step2Labels = raw36559step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36559step2 raw36559step2Labels = mixedMoment B raw36559step3 raw36559step3Labels := by
      have ha : raw36559step3 = raw36559step2 := by apply Matrix.ext; unfold raw36559step3 raw36559step2; decide +kernel
      have hl : raw36559step2Labels = labelEmbedding1 ∘ raw36559step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36559step2 raw36559step2Labels raw36559step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical36560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36560 raw36560Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw36560 raw36560Labels = mixedMoment B raw36560step0 raw36560step0Labels := by
      have ha : raw36560step0 = (fun i j => raw36560 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36560step0 raw36560; decide +kernel
      have hl : raw36560step0Labels = raw36560Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36560 raw36560Labels permutation273 permutation7
    mixedMoment B raw36560step0 raw36560step0Labels = mixedMoment B raw36560step1 raw36560step1Labels := by
      have ha : raw36560step1 = -raw36560step0 := by apply Matrix.ext; change ∀ i j, raw36560step1 i j = -(raw36560step0 i j); unfold raw36560step1 raw36560step0; decide +kernel
      have hl : raw36560step1Labels = raw36560step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36560step1 raw36560step1Labels = mixedMoment B raw36560step2 raw36560step2Labels := by
      have ha : raw36560step2 = raw36560step1 := by apply Matrix.ext; unfold raw36560step2 raw36560step1; decide +kernel
      have hl : raw36560step1Labels = labelEmbedding1 ∘ raw36560step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36560step1 raw36560step1Labels raw36560step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

theorem canonical36561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36561 raw36561Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw36561 raw36561Labels = mixedMoment B raw36561step0 raw36561step0Labels := by
      have ha : raw36561step0 = (fun i j => raw36561 (permutation181 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36561step0 raw36561; decide +kernel
      have hl : raw36561step0Labels = raw36561Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36561 raw36561Labels permutation181 permutation5
    mixedMoment B raw36561step0 raw36561step0Labels = mixedMoment B raw36561step1 raw36561step1Labels := by
      have ha : raw36561step1 = -raw36561step0 := by apply Matrix.ext; change ∀ i j, raw36561step1 i j = -(raw36561step0 i j); unfold raw36561step1 raw36561step0; decide +kernel
      have hl : raw36561step1Labels = raw36561step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36561step1 raw36561step1Labels = mixedMoment B raw36561step2 raw36561step2Labels := by
      have ha : raw36561step2 = raw36561step1 := by apply Matrix.ext; unfold raw36561step2 raw36561step1; decide +kernel
      have hl : raw36561step1Labels = labelEmbedding1 ∘ raw36561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36561step1 raw36561step1Labels raw36561step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

theorem canonical36562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36562 raw36562Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw36562 raw36562Labels = mixedMoment B raw36562step0 raw36562step0Labels := by
      have ha : raw36562step0 = (fun i j => raw36562 (permutation279 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36562step0 raw36562; decide +kernel
      have hl : raw36562step0Labels = raw36562Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36562 raw36562Labels permutation279 permutation7
    mixedMoment B raw36562step0 raw36562step0Labels = mixedMoment B raw36562step1 raw36562step1Labels := by
      have ha : raw36562step1 = -raw36562step0 := by apply Matrix.ext; change ∀ i j, raw36562step1 i j = -(raw36562step0 i j); unfold raw36562step1 raw36562step0; decide +kernel
      have hl : raw36562step1Labels = raw36562step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36562step1 raw36562step1Labels = mixedMoment B raw36562step2 raw36562step2Labels := by
      have ha : raw36562step2 = raw36562step1 := by apply Matrix.ext; unfold raw36562step2 raw36562step1; decide +kernel
      have hl : raw36562step1Labels = labelEmbedding1 ∘ raw36562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36562step1 raw36562step1Labels raw36562step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

theorem canonical36563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36563 raw36563Labels = mixedMoment B node3760 node3760Labels := by
  calc
    mixedMoment B raw36563 raw36563Labels = mixedMoment B raw36563step0 raw36563step0Labels := by
      have ha : raw36563step0 = (fun i j => raw36563 (permutation279 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36563step0 raw36563; decide +kernel
      have hl : raw36563step0Labels = raw36563Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36563 raw36563Labels permutation279 permutation7
    mixedMoment B raw36563step0 raw36563step0Labels = mixedMoment B raw36563step1 raw36563step1Labels := by
      have ha : raw36563step1 = -raw36563step0 := by apply Matrix.ext; change ∀ i j, raw36563step1 i j = -(raw36563step0 i j); unfold raw36563step1 raw36563step0; decide +kernel
      have hl : raw36563step1Labels = raw36563step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36563step1 raw36563step1Labels = mixedMoment B raw36563step2 raw36563step2Labels := by
      have ha : raw36563step2 = raw36563step1 := by apply Matrix.ext; unfold raw36563step2 raw36563step1; decide +kernel
      have hl : raw36563step1Labels = labelEmbedding1 ∘ raw36563step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36563step1 raw36563step1Labels raw36563step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3760 node3760Labels := by rfl

theorem canonical36564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36564 raw36564Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw36564 raw36564Labels = mixedMoment B raw36564step0 raw36564step0Labels := by
      have hz : ∀ j, raw36564 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36564step0 = (fun i j => raw36564 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36564step0 raw36564; decide +kernel
      have hl : raw36564step0Labels = raw36564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36564 raw36564Labels permutation520 hz
    mixedMoment B raw36564step0 raw36564step0Labels = mixedMoment B raw36564step1 raw36564step1Labels := by
      have ha : raw36564step1 = (fun i j => raw36564step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36564step1 raw36564step0; decide +kernel
      have hl : raw36564step1Labels = raw36564step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36564step0 raw36564step0Labels permutation58 permutation7
    mixedMoment B raw36564step1 raw36564step1Labels = mixedMoment B raw36564step2 raw36564step2Labels := by
      have ha : raw36564step2 = -raw36564step1 := by apply Matrix.ext; change ∀ i j, raw36564step2 i j = -(raw36564step1 i j); unfold raw36564step2 raw36564step1; decide +kernel
      have hl : raw36564step2Labels = raw36564step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36564step2 raw36564step2Labels = mixedMoment B raw36564step3 raw36564step3Labels := by
      have ha : raw36564step3 = raw36564step2 := by apply Matrix.ext; unfold raw36564step3 raw36564step2; decide +kernel
      have hl : raw36564step2Labels = labelEmbedding1 ∘ raw36564step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36564step2 raw36564step2Labels raw36564step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

theorem canonical36565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36565 raw36565Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw36565 raw36565Labels = mixedMoment B raw36565step0 raw36565step0Labels := by
      have ha : raw36565step0 = (fun i j => raw36565 (permutation279 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36565step0 raw36565; decide +kernel
      have hl : raw36565step0Labels = raw36565Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36565 raw36565Labels permutation279 permutation7
    mixedMoment B raw36565step0 raw36565step0Labels = mixedMoment B raw36565step1 raw36565step1Labels := by
      have ha : raw36565step1 = -raw36565step0 := by apply Matrix.ext; change ∀ i j, raw36565step1 i j = -(raw36565step0 i j); unfold raw36565step1 raw36565step0; decide +kernel
      have hl : raw36565step1Labels = raw36565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36565step1 raw36565step1Labels = mixedMoment B raw36565step2 raw36565step2Labels := by
      have ha : raw36565step2 = raw36565step1 := by apply Matrix.ext; unfold raw36565step2 raw36565step1; decide +kernel
      have hl : raw36565step1Labels = labelEmbedding1 ∘ raw36565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36565step1 raw36565step1Labels raw36565step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

theorem canonical36566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36566 raw36566Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw36566 raw36566Labels = mixedMoment B raw36566step0 raw36566step0Labels := by
      have ha : raw36566step0 = (fun i j => raw36566 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36566step0 raw36566; decide +kernel
      have hl : raw36566step0Labels = raw36566Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36566 raw36566Labels permutation180 permutation5
    mixedMoment B raw36566step0 raw36566step0Labels = mixedMoment B raw36566step1 raw36566step1Labels := by
      have ha : raw36566step1 = -raw36566step0 := by apply Matrix.ext; change ∀ i j, raw36566step1 i j = -(raw36566step0 i j); unfold raw36566step1 raw36566step0; decide +kernel
      have hl : raw36566step1Labels = raw36566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36566step1 raw36566step1Labels = mixedMoment B raw36566step2 raw36566step2Labels := by
      have ha : raw36566step2 = raw36566step1 := by apply Matrix.ext; unfold raw36566step2 raw36566step1; decide +kernel
      have hl : raw36566step1Labels = labelEmbedding1 ∘ raw36566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36566step1 raw36566step1Labels raw36566step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

theorem canonical36567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36567 raw36567Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw36567 raw36567Labels = mixedMoment B raw36567step0 raw36567step0Labels := by
      have ha : raw36567step0 = (fun i j => raw36567 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36567step0 raw36567; decide +kernel
      have hl : raw36567step0Labels = raw36567Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36567 raw36567Labels permutation273 permutation7
    mixedMoment B raw36567step0 raw36567step0Labels = mixedMoment B raw36567step1 raw36567step1Labels := by
      have ha : raw36567step1 = -raw36567step0 := by apply Matrix.ext; change ∀ i j, raw36567step1 i j = -(raw36567step0 i j); unfold raw36567step1 raw36567step0; decide +kernel
      have hl : raw36567step1Labels = raw36567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36567step1 raw36567step1Labels = mixedMoment B raw36567step2 raw36567step2Labels := by
      have ha : raw36567step2 = raw36567step1 := by apply Matrix.ext; unfold raw36567step2 raw36567step1; decide +kernel
      have hl : raw36567step1Labels = labelEmbedding1 ∘ raw36567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36567step1 raw36567step1Labels raw36567step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

theorem canonical36568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36568 raw36568Labels = mixedMoment B node3760 node3760Labels := by
  calc
    mixedMoment B raw36568 raw36568Labels = mixedMoment B raw36568step0 raw36568step0Labels := by
      have ha : raw36568step0 = (fun i j => raw36568 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36568step0 raw36568; decide +kernel
      have hl : raw36568step0Labels = raw36568Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36568 raw36568Labels permutation273 permutation7
    mixedMoment B raw36568step0 raw36568step0Labels = mixedMoment B raw36568step1 raw36568step1Labels := by
      have ha : raw36568step1 = -raw36568step0 := by apply Matrix.ext; change ∀ i j, raw36568step1 i j = -(raw36568step0 i j); unfold raw36568step1 raw36568step0; decide +kernel
      have hl : raw36568step1Labels = raw36568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36568step1 raw36568step1Labels = mixedMoment B raw36568step2 raw36568step2Labels := by
      have ha : raw36568step2 = raw36568step1 := by apply Matrix.ext; unfold raw36568step2 raw36568step1; decide +kernel
      have hl : raw36568step1Labels = labelEmbedding1 ∘ raw36568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36568step1 raw36568step1Labels raw36568step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3760 node3760Labels := by rfl

theorem canonical36569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36569 raw36569Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw36569 raw36569Labels = mixedMoment B raw36569step0 raw36569step0Labels := by
      have ha : raw36569step0 = (fun i j => raw36569 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36569step0 raw36569; decide +kernel
      have hl : raw36569step0Labels = raw36569Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36569 raw36569Labels permutation273 permutation7
    mixedMoment B raw36569step0 raw36569step0Labels = mixedMoment B raw36569step1 raw36569step1Labels := by
      have ha : raw36569step1 = -raw36569step0 := by apply Matrix.ext; change ∀ i j, raw36569step1 i j = -(raw36569step0 i j); unfold raw36569step1 raw36569step0; decide +kernel
      have hl : raw36569step1Labels = raw36569step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36569step1 raw36569step1Labels = mixedMoment B raw36569step2 raw36569step2Labels := by
      have ha : raw36569step2 = raw36569step1 := by apply Matrix.ext; unfold raw36569step2 raw36569step1; decide +kernel
      have hl : raw36569step1Labels = labelEmbedding1 ∘ raw36569step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36569step1 raw36569step1Labels raw36569step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

theorem canonical36570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36570 raw36570Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw36570 raw36570Labels = mixedMoment B raw36570step0 raw36570step0Labels := by
      have ha : raw36570step0 = (fun i j => raw36570 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36570step0 raw36570; decide +kernel
      have hl : raw36570step0Labels = raw36570Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36570 raw36570Labels permutation176 permutation5
    mixedMoment B raw36570step0 raw36570step0Labels = mixedMoment B raw36570step1 raw36570step1Labels := by
      have ha : raw36570step1 = -raw36570step0 := by apply Matrix.ext; change ∀ i j, raw36570step1 i j = -(raw36570step0 i j); unfold raw36570step1 raw36570step0; decide +kernel
      have hl : raw36570step1Labels = raw36570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36570step1 raw36570step1Labels = mixedMoment B raw36570step2 raw36570step2Labels := by
      have ha : raw36570step2 = raw36570step1 := by apply Matrix.ext; unfold raw36570step2 raw36570step1; decide +kernel
      have hl : raw36570step1Labels = labelEmbedding1 ∘ raw36570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36570step1 raw36570step1Labels raw36570step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3510 node3510Labels := by rfl

theorem canonical36571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36571 raw36571Labels = mixedMoment B node3403 node3403Labels := by
  calc
    mixedMoment B raw36571 raw36571Labels = mixedMoment B raw36571step0 raw36571step0Labels := by
      have ha : raw36571step0 = (fun i j => raw36571 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36571step0 raw36571; decide +kernel
      have hl : raw36571step0Labels = raw36571Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36571 raw36571Labels permutation273 permutation7
    mixedMoment B raw36571step0 raw36571step0Labels = mixedMoment B raw36571step1 raw36571step1Labels := by
      have ha : raw36571step1 = -raw36571step0 := by apply Matrix.ext; change ∀ i j, raw36571step1 i j = -(raw36571step0 i j); unfold raw36571step1 raw36571step0; decide +kernel
      have hl : raw36571step1Labels = raw36571step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36571step1 raw36571step1Labels = mixedMoment B raw36571step2 raw36571step2Labels := by
      have ha : raw36571step2 = raw36571step1 := by apply Matrix.ext; unfold raw36571step2 raw36571step1; decide +kernel
      have hl : raw36571step1Labels = labelEmbedding1 ∘ raw36571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36571step1 raw36571step1Labels raw36571step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3403 node3403Labels := by rfl

theorem canonical36572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36572 raw36572Labels = mixedMoment B node3556 node3556Labels := by
  calc
    mixedMoment B raw36572 raw36572Labels = mixedMoment B raw36572step0 raw36572step0Labels := by
      have ha : raw36572step0 = (fun i j => raw36572 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36572step0 raw36572; decide +kernel
      have hl : raw36572step0Labels = raw36572Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36572 raw36572Labels permutation639 permutation7
    mixedMoment B raw36572step0 raw36572step0Labels = mixedMoment B raw36572step1 raw36572step1Labels := by
      have ha : raw36572step1 = raw36572step0 := by apply Matrix.ext; unfold raw36572step1 raw36572step0; decide +kernel
      have hl : raw36572step0Labels = labelEmbedding1 ∘ raw36572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36572step0 raw36572step0Labels raw36572step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3556 node3556Labels := by rfl

theorem canonical36573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36573 raw36573Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw36573 raw36573Labels = mixedMoment B raw36573step0 raw36573step0Labels := by
      have hz : ∀ j, raw36573 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36573step0 = (fun i j => raw36573 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36573step0 raw36573; decide +kernel
      have hl : raw36573step0Labels = raw36573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36573 raw36573Labels permutation520 hz
    mixedMoment B raw36573step0 raw36573step0Labels = mixedMoment B raw36573step1 raw36573step1Labels := by
      have ha : raw36573step1 = (fun i j => raw36573step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36573step1 raw36573step0; decide +kernel
      have hl : raw36573step1Labels = raw36573step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36573step0 raw36573step0Labels permutation144 permutation7
    mixedMoment B raw36573step1 raw36573step1Labels = mixedMoment B raw36573step2 raw36573step2Labels := by
      have ha : raw36573step2 = raw36573step1 := by apply Matrix.ext; unfold raw36573step2 raw36573step1; decide +kernel
      have hl : raw36573step1Labels = labelEmbedding1 ∘ raw36573step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36573step1 raw36573step1Labels raw36573step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical287
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36815 raw36815Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw36815 raw36815Labels = mixedMoment B raw36815step0 raw36815step0Labels := by
      have hz : ∀ j, raw36815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36815step0 = (fun i j => raw36815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36815step0 raw36815; decide +kernel
      have hl : raw36815step0Labels = raw36815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36815 raw36815Labels permutation346 hz
    mixedMoment B raw36815step0 raw36815step0Labels = mixedMoment B raw36815step1 raw36815step1Labels := by
      have ha : raw36815step1 = (fun i j => raw36815step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36815step1 raw36815step0; decide +kernel
      have hl : raw36815step1Labels = raw36815step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36815step0 raw36815step0Labels permutation144 permutation7
    mixedMoment B raw36815step1 raw36815step1Labels = mixedMoment B raw36815step2 raw36815step2Labels := by
      have ha : raw36815step2 = raw36815step1 := by apply Matrix.ext; unfold raw36815step2 raw36815step1; decide +kernel
      have hl : raw36815step1Labels = labelEmbedding1 ∘ raw36815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36815step1 raw36815step1Labels raw36815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical36816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36816 raw36816Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw36816 raw36816Labels = mixedMoment B raw36816step0 raw36816step0Labels := by
      have ha : raw36816step0 = (fun i j => raw36816 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36816step0 raw36816; decide +kernel
      have hl : raw36816step0Labels = raw36816Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36816 raw36816Labels permutation663 permutation7
    mixedMoment B raw36816step0 raw36816step0Labels = mixedMoment B raw36816step1 raw36816step1Labels := by
      have ha : raw36816step1 = raw36816step0 := by apply Matrix.ext; unfold raw36816step1 raw36816step0; decide +kernel
      have hl : raw36816step0Labels = labelEmbedding1 ∘ raw36816step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36816step0 raw36816step0Labels raw36816step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical36817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36817 raw36817Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw36817 raw36817Labels = mixedMoment B raw36817step0 raw36817step0Labels := by
      have hz : ∀ j, raw36817 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36817step0 = (fun i j => raw36817 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36817step0 raw36817; decide +kernel
      have hl : raw36817step0Labels = raw36817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36817 raw36817Labels permutation434 hz
    mixedMoment B raw36817step0 raw36817step0Labels = mixedMoment B raw36817step1 raw36817step1Labels := by
      have hz : ∀ j, raw36817step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36817step1 = (fun i j => raw36817step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36817step1 raw36817step0; decide +kernel
      have hl : raw36817step1Labels = raw36817step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36817step0 raw36817step0Labels permutation80 hz
    mixedMoment B raw36817step1 raw36817step1Labels = mixedMoment B raw36817step2 raw36817step2Labels := by
      have ha : raw36817step2 = (fun i j => raw36817step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36817step2 raw36817step1; decide +kernel
      have hl : raw36817step2Labels = raw36817step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36817step1 raw36817step1Labels permutation30 permutation7
    mixedMoment B raw36817step2 raw36817step2Labels = mixedMoment B raw36817step3 raw36817step3Labels := by
      have ha : raw36817step3 = raw36817step2 := by apply Matrix.ext; unfold raw36817step3 raw36817step2; decide +kernel
      have hl : raw36817step2Labels = labelEmbedding1 ∘ raw36817step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36817step2 raw36817step2Labels raw36817step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical36818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36818 raw36818Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw36818 raw36818Labels = mixedMoment B raw36818step0 raw36818step0Labels := by
      have hz : ∀ j, raw36818 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36818step0 = (fun i j => raw36818 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36818step0 raw36818; decide +kernel
      have hl : raw36818step0Labels = raw36818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36818 raw36818Labels permutation520 hz
    mixedMoment B raw36818step0 raw36818step0Labels = mixedMoment B raw36818step1 raw36818step1Labels := by
      have hz : ∀ j, raw36818step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36818step1 = (fun i j => raw36818step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36818step1 raw36818step0; decide +kernel
      have hl : raw36818step1Labels = raw36818step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36818step0 raw36818step0Labels permutation80 hz
    mixedMoment B raw36818step1 raw36818step1Labels = mixedMoment B raw36818step2 raw36818step2Labels := by
      have ha : raw36818step2 = (fun i j => raw36818step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36818step2 raw36818step1; decide +kernel
      have hl : raw36818step2Labels = raw36818step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36818step1 raw36818step1Labels permutation30 permutation7
    mixedMoment B raw36818step2 raw36818step2Labels = mixedMoment B raw36818step3 raw36818step3Labels := by
      have ha : raw36818step3 = raw36818step2 := by apply Matrix.ext; unfold raw36818step3 raw36818step2; decide +kernel
      have hl : raw36818step2Labels = labelEmbedding1 ∘ raw36818step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36818step2 raw36818step2Labels raw36818step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical36819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36819 raw36819Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw36819 raw36819Labels = mixedMoment B raw36819step0 raw36819step0Labels := by
      have hz : ∀ j, raw36819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36819step0 = (fun i j => raw36819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36819step0 raw36819; decide +kernel
      have hl : raw36819step0Labels = raw36819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36819 raw36819Labels permutation346 hz
    mixedMoment B raw36819step0 raw36819step0Labels = mixedMoment B raw36819step1 raw36819step1Labels := by
      have ha : raw36819step1 = (fun i j => raw36819step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36819step1 raw36819step0; decide +kernel
      have hl : raw36819step1Labels = raw36819step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36819step0 raw36819step0Labels permutation144 permutation7
    mixedMoment B raw36819step1 raw36819step1Labels = mixedMoment B raw36819step2 raw36819step2Labels := by
      have ha : raw36819step2 = raw36819step1 := by apply Matrix.ext; unfold raw36819step2 raw36819step1; decide +kernel
      have hl : raw36819step1Labels = labelEmbedding1 ∘ raw36819step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36819step1 raw36819step1Labels raw36819step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical36820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36820 raw36820Labels = mixedMoment B node2695 node2695Labels := by
  calc
    mixedMoment B raw36820 raw36820Labels = mixedMoment B raw36820step0 raw36820step0Labels := by
      have ha : raw36820step0 = (fun i j => raw36820 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36820step0 raw36820; decide +kernel
      have hl : raw36820step0Labels = raw36820Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36820 raw36820Labels permutation663 permutation7
    mixedMoment B raw36820step0 raw36820step0Labels = mixedMoment B raw36820step1 raw36820step1Labels := by
      have ha : raw36820step1 = raw36820step0 := by apply Matrix.ext; unfold raw36820step1 raw36820step0; decide +kernel
      have hl : raw36820step0Labels = labelEmbedding1 ∘ raw36820step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36820step0 raw36820step0Labels raw36820step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2695 node2695Labels := by rfl

theorem canonical36821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36821 raw36821Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw36821 raw36821Labels = mixedMoment B raw36821step0 raw36821step0Labels := by
      have hz : ∀ j, raw36821 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36821step0 = (fun i j => raw36821 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36821step0 raw36821; decide +kernel
      have hl : raw36821step0Labels = raw36821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36821 raw36821Labels permutation520 hz
    mixedMoment B raw36821step0 raw36821step0Labels = mixedMoment B raw36821step1 raw36821step1Labels := by
      have hz : ∀ j, raw36821step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36821step1 = (fun i j => raw36821step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36821step1 raw36821step0; decide +kernel
      have hl : raw36821step1Labels = raw36821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36821step0 raw36821step0Labels permutation80 hz
    mixedMoment B raw36821step1 raw36821step1Labels = mixedMoment B raw36821step2 raw36821step2Labels := by
      have ha : raw36821step2 = (fun i j => raw36821step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36821step2 raw36821step1; decide +kernel
      have hl : raw36821step2Labels = raw36821step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36821step1 raw36821step1Labels permutation30 permutation7
    mixedMoment B raw36821step2 raw36821step2Labels = mixedMoment B raw36821step3 raw36821step3Labels := by
      have ha : raw36821step3 = raw36821step2 := by apply Matrix.ext; unfold raw36821step3 raw36821step2; decide +kernel
      have hl : raw36821step2Labels = labelEmbedding1 ∘ raw36821step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36821step2 raw36821step2Labels raw36821step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical36822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36822 raw36822Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw36822 raw36822Labels = mixedMoment B raw36822step0 raw36822step0Labels := by
      have hz : ∀ j, raw36822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36822step0 = (fun i j => raw36822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36822step0 raw36822; decide +kernel
      have hl : raw36822step0Labels = raw36822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36822 raw36822Labels permutation346 hz
    mixedMoment B raw36822step0 raw36822step0Labels = mixedMoment B raw36822step1 raw36822step1Labels := by
      have ha : raw36822step1 = (fun i j => raw36822step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36822step1 raw36822step0; decide +kernel
      have hl : raw36822step1Labels = raw36822step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36822step0 raw36822step0Labels permutation144 permutation7
    mixedMoment B raw36822step1 raw36822step1Labels = mixedMoment B raw36822step2 raw36822step2Labels := by
      have ha : raw36822step2 = raw36822step1 := by apply Matrix.ext; unfold raw36822step2 raw36822step1; decide +kernel
      have hl : raw36822step1Labels = labelEmbedding1 ∘ raw36822step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36822step1 raw36822step1Labels raw36822step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3078 node3078Labels := by rfl

theorem canonical36823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36823 raw36823Labels = mixedMoment B node2690 node2690Labels := by
  calc
    mixedMoment B raw36823 raw36823Labels = mixedMoment B raw36823step0 raw36823step0Labels := by
      have ha : raw36823step0 = (fun i j => raw36823 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36823step0 raw36823; decide +kernel
      have hl : raw36823step0Labels = raw36823Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36823 raw36823Labels permutation639 permutation7
    mixedMoment B raw36823step0 raw36823step0Labels = mixedMoment B raw36823step1 raw36823step1Labels := by
      have ha : raw36823step1 = raw36823step0 := by apply Matrix.ext; unfold raw36823step1 raw36823step0; decide +kernel
      have hl : raw36823step0Labels = labelEmbedding1 ∘ raw36823step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36823step0 raw36823step0Labels raw36823step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2690 node2690Labels := by rfl

theorem canonical36824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36824 raw36824Labels = mixedMoment B node2689 node2689Labels := by
  calc
    mixedMoment B raw36824 raw36824Labels = mixedMoment B raw36824step0 raw36824step0Labels := by
      have ha : raw36824step0 = (fun i j => raw36824 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36824step0 raw36824; decide +kernel
      have hl : raw36824step0Labels = raw36824Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36824 raw36824Labels permutation639 permutation7
    mixedMoment B raw36824step0 raw36824step0Labels = mixedMoment B raw36824step1 raw36824step1Labels := by
      have ha : raw36824step1 = raw36824step0 := by apply Matrix.ext; unfold raw36824step1 raw36824step0; decide +kernel
      have hl : raw36824step0Labels = labelEmbedding1 ∘ raw36824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36824step0 raw36824step0Labels raw36824step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2689 node2689Labels := by rfl

theorem canonical36825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36825 raw36825Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw36825 raw36825Labels = mixedMoment B raw36825step0 raw36825step0Labels := by
      have hz : ∀ j, raw36825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36825step0 = (fun i j => raw36825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36825step0 raw36825; decide +kernel
      have hl : raw36825step0Labels = raw36825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36825 raw36825Labels permutation434 hz
    mixedMoment B raw36825step0 raw36825step0Labels = mixedMoment B raw36825step1 raw36825step1Labels := by
      have ha : raw36825step1 = (fun i j => raw36825step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36825step1 raw36825step0; decide +kernel
      have hl : raw36825step1Labels = raw36825step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36825step0 raw36825step0Labels permutation144 permutation7
    mixedMoment B raw36825step1 raw36825step1Labels = mixedMoment B raw36825step2 raw36825step2Labels := by
      have ha : raw36825step2 = raw36825step1 := by apply Matrix.ext; unfold raw36825step2 raw36825step1; decide +kernel
      have hl : raw36825step1Labels = labelEmbedding1 ∘ raw36825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36825step1 raw36825step1Labels raw36825step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical36826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36826 raw36826Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw36826 raw36826Labels = mixedMoment B raw36826step0 raw36826step0Labels := by
      have hz : ∀ j, raw36826 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36826step0 = (fun i j => raw36826 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36826step0 raw36826; decide +kernel
      have hl : raw36826step0Labels = raw36826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36826 raw36826Labels permutation520 hz
    mixedMoment B raw36826step0 raw36826step0Labels = mixedMoment B raw36826step1 raw36826step1Labels := by
      have ha : raw36826step1 = (fun i j => raw36826step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36826step1 raw36826step0; decide +kernel
      have hl : raw36826step1Labels = raw36826step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36826step0 raw36826step0Labels permutation144 permutation7
    mixedMoment B raw36826step1 raw36826step1Labels = mixedMoment B raw36826step2 raw36826step2Labels := by
      have ha : raw36826step2 = raw36826step1 := by apply Matrix.ext; unfold raw36826step2 raw36826step1; decide +kernel
      have hl : raw36826step1Labels = labelEmbedding1 ∘ raw36826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36826step1 raw36826step1Labels raw36826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical36827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36827 raw36827Labels = mixedMoment B node3059 node3059Labels := by
  calc
    mixedMoment B raw36827 raw36827Labels = mixedMoment B raw36827step0 raw36827step0Labels := by
      have ha : raw36827step0 = (fun i j => raw36827 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36827step0 raw36827; decide +kernel
      have hl : raw36827step0Labels = raw36827Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36827 raw36827Labels permutation639 permutation7
    mixedMoment B raw36827step0 raw36827step0Labels = mixedMoment B raw36827step1 raw36827step1Labels := by
      have ha : raw36827step1 = raw36827step0 := by apply Matrix.ext; unfold raw36827step1 raw36827step0; decide +kernel
      have hl : raw36827step0Labels = labelEmbedding1 ∘ raw36827step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36827step0 raw36827step0Labels raw36827step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3059 node3059Labels := by rfl

theorem canonical36828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36828 raw36828Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw36828 raw36828Labels = mixedMoment B raw36828step0 raw36828step0Labels := by
      have hz : ∀ j, raw36828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36828step0 = (fun i j => raw36828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36828step0 raw36828; decide +kernel
      have hl : raw36828step0Labels = raw36828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36828 raw36828Labels permutation346 hz
    mixedMoment B raw36828step0 raw36828step0Labels = mixedMoment B raw36828step1 raw36828step1Labels := by
      have ha : raw36828step1 = (fun i j => raw36828step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36828step1 raw36828step0; decide +kernel
      have hl : raw36828step1Labels = raw36828step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36828step0 raw36828step0Labels permutation144 permutation7
    mixedMoment B raw36828step1 raw36828step1Labels = mixedMoment B raw36828step2 raw36828step2Labels := by
      have ha : raw36828step2 = raw36828step1 := by apply Matrix.ext; unfold raw36828step2 raw36828step1; decide +kernel
      have hl : raw36828step1Labels = labelEmbedding1 ∘ raw36828step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36828step1 raw36828step1Labels raw36828step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

theorem canonical36829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36829 raw36829Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw36829 raw36829Labels = mixedMoment B raw36829step0 raw36829step0Labels := by
      have hz : ∀ j, raw36829 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36829step0 = (fun i j => raw36829 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36829step0 raw36829; decide +kernel
      have hl : raw36829step0Labels = raw36829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36829 raw36829Labels permutation346 hz
    mixedMoment B raw36829step0 raw36829step0Labels = mixedMoment B raw36829step1 raw36829step1Labels := by
      have ha : raw36829step1 = (fun i j => raw36829step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36829step1 raw36829step0; decide +kernel
      have hl : raw36829step1Labels = raw36829step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36829step0 raw36829step0Labels permutation144 permutation7
    mixedMoment B raw36829step1 raw36829step1Labels = mixedMoment B raw36829step2 raw36829step2Labels := by
      have ha : raw36829step2 = raw36829step1 := by apply Matrix.ext; unfold raw36829step2 raw36829step1; decide +kernel
      have hl : raw36829step1Labels = labelEmbedding1 ∘ raw36829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36829step1 raw36829step1Labels raw36829step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical36830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36830 raw36830Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw36830 raw36830Labels = mixedMoment B raw36830step0 raw36830step0Labels := by
      have ha : raw36830step0 = (fun i j => raw36830 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36830step0 raw36830; decide +kernel
      have hl : raw36830step0Labels = raw36830Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36830 raw36830Labels permutation663 permutation7
    mixedMoment B raw36830step0 raw36830step0Labels = mixedMoment B raw36830step1 raw36830step1Labels := by
      have ha : raw36830step1 = raw36830step0 := by apply Matrix.ext; unfold raw36830step1 raw36830step0; decide +kernel
      have hl : raw36830step0Labels = labelEmbedding1 ∘ raw36830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36830step0 raw36830step0Labels raw36830step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

theorem canonical36831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36831 raw36831Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw36831 raw36831Labels = mixedMoment B raw36831step0 raw36831step0Labels := by
      have hz : ∀ j, raw36831 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36831step0 = (fun i j => raw36831 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36831step0 raw36831; decide +kernel
      have hl : raw36831step0Labels = raw36831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36831 raw36831Labels permutation520 hz
    mixedMoment B raw36831step0 raw36831step0Labels = mixedMoment B raw36831step1 raw36831step1Labels := by
      have hz : ∀ j, raw36831step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36831step1 = (fun i j => raw36831step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36831step1 raw36831step0; decide +kernel
      have hl : raw36831step1Labels = raw36831step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36831step0 raw36831step0Labels permutation80 hz
    mixedMoment B raw36831step1 raw36831step1Labels = mixedMoment B raw36831step2 raw36831step2Labels := by
      have ha : raw36831step2 = (fun i j => raw36831step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36831step2 raw36831step1; decide +kernel
      have hl : raw36831step2Labels = raw36831step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36831step1 raw36831step1Labels permutation30 permutation7
    mixedMoment B raw36831step2 raw36831step2Labels = mixedMoment B raw36831step3 raw36831step3Labels := by
      have ha : raw36831step3 = raw36831step2 := by apply Matrix.ext; unfold raw36831step3 raw36831step2; decide +kernel
      have hl : raw36831step2Labels = labelEmbedding1 ∘ raw36831step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36831step2 raw36831step2Labels raw36831step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical36832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36832 raw36832Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw36832 raw36832Labels = mixedMoment B raw36832step0 raw36832step0Labels := by
      have hz : ∀ j, raw36832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36832step0 = (fun i j => raw36832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36832step0 raw36832; decide +kernel
      have hl : raw36832step0Labels = raw36832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36832 raw36832Labels permutation346 hz
    mixedMoment B raw36832step0 raw36832step0Labels = mixedMoment B raw36832step1 raw36832step1Labels := by
      have ha : raw36832step1 = (fun i j => raw36832step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36832step1 raw36832step0; decide +kernel
      have hl : raw36832step1Labels = raw36832step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36832step0 raw36832step0Labels permutation144 permutation7
    mixedMoment B raw36832step1 raw36832step1Labels = mixedMoment B raw36832step2 raw36832step2Labels := by
      have ha : raw36832step2 = raw36832step1 := by apply Matrix.ext; unfold raw36832step2 raw36832step1; decide +kernel
      have hl : raw36832step1Labels = labelEmbedding1 ∘ raw36832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36832step1 raw36832step1Labels raw36832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

theorem canonical36833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36833 raw36833Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw36833 raw36833Labels = mixedMoment B raw36833step0 raw36833step0Labels := by
      have hz : ∀ j, raw36833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36833step0 = (fun i j => raw36833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36833step0 raw36833; decide +kernel
      have hl : raw36833step0Labels = raw36833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36833 raw36833Labels permutation346 hz
    mixedMoment B raw36833step0 raw36833step0Labels = mixedMoment B raw36833step1 raw36833step1Labels := by
      have ha : raw36833step1 = (fun i j => raw36833step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36833step1 raw36833step0; decide +kernel
      have hl : raw36833step1Labels = raw36833step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36833step0 raw36833step0Labels permutation150 permutation7
    mixedMoment B raw36833step1 raw36833step1Labels = mixedMoment B raw36833step2 raw36833step2Labels := by
      have ha : raw36833step2 = raw36833step1 := by apply Matrix.ext; unfold raw36833step2 raw36833step1; decide +kernel
      have hl : raw36833step1Labels = labelEmbedding1 ∘ raw36833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36833step1 raw36833step1Labels raw36833step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

theorem canonical36834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36834 raw36834Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw36834 raw36834Labels = mixedMoment B raw36834step0 raw36834step0Labels := by
      have hz : ∀ j, raw36834 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36834step0 = (fun i j => raw36834 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36834step0 raw36834; decide +kernel
      have hl : raw36834step0Labels = raw36834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36834 raw36834Labels permutation346 hz
    mixedMoment B raw36834step0 raw36834step0Labels = mixedMoment B raw36834step1 raw36834step1Labels := by
      have ha : raw36834step1 = (fun i j => raw36834step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36834step1 raw36834step0; decide +kernel
      have hl : raw36834step1Labels = raw36834step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36834step0 raw36834step0Labels permutation150 permutation7
    mixedMoment B raw36834step1 raw36834step1Labels = mixedMoment B raw36834step2 raw36834step2Labels := by
      have ha : raw36834step2 = raw36834step1 := by apply Matrix.ext; unfold raw36834step2 raw36834step1; decide +kernel
      have hl : raw36834step1Labels = labelEmbedding1 ∘ raw36834step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36834step1 raw36834step1Labels raw36834step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical36835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36835 raw36835Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw36835 raw36835Labels = mixedMoment B raw36835step0 raw36835step0Labels := by
      have ha : raw36835step0 = (fun i j => raw36835 (permutation687 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36835step0 raw36835; decide +kernel
      have hl : raw36835step0Labels = raw36835Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36835 raw36835Labels permutation687 permutation7
    mixedMoment B raw36835step0 raw36835step0Labels = mixedMoment B raw36835step1 raw36835step1Labels := by
      have ha : raw36835step1 = raw36835step0 := by apply Matrix.ext; unfold raw36835step1 raw36835step0; decide +kernel
      have hl : raw36835step0Labels = labelEmbedding1 ∘ raw36835step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36835step0 raw36835step0Labels raw36835step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

theorem canonical36836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36836 raw36836Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw36836 raw36836Labels = mixedMoment B raw36836step0 raw36836step0Labels := by
      have hz : ∀ j, raw36836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36836step0 = (fun i j => raw36836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36836step0 raw36836; decide +kernel
      have hl : raw36836step0Labels = raw36836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36836 raw36836Labels permutation434 hz
    mixedMoment B raw36836step0 raw36836step0Labels = mixedMoment B raw36836step1 raw36836step1Labels := by
      have hz : ∀ j, raw36836step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36836step1 = (fun i j => raw36836step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36836step1 raw36836step0; decide +kernel
      have hl : raw36836step1Labels = raw36836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36836step0 raw36836step0Labels permutation80 hz
    mixedMoment B raw36836step1 raw36836step1Labels = mixedMoment B raw36836step2 raw36836step2Labels := by
      have ha : raw36836step2 = (fun i j => raw36836step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36836step2 raw36836step1; decide +kernel
      have hl : raw36836step2Labels = raw36836step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36836step1 raw36836step1Labels permutation30 permutation7
    mixedMoment B raw36836step2 raw36836step2Labels = mixedMoment B raw36836step3 raw36836step3Labels := by
      have ha : raw36836step3 = raw36836step2 := by apply Matrix.ext; unfold raw36836step3 raw36836step2; decide +kernel
      have hl : raw36836step2Labels = labelEmbedding1 ∘ raw36836step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36836step2 raw36836step2Labels raw36836step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical36837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36837 raw36837Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw36837 raw36837Labels = mixedMoment B raw36837step0 raw36837step0Labels := by
      have hz : ∀ j, raw36837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36837step0 = (fun i j => raw36837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36837step0 raw36837; decide +kernel
      have hl : raw36837step0Labels = raw36837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36837 raw36837Labels permutation346 hz
    mixedMoment B raw36837step0 raw36837step0Labels = mixedMoment B raw36837step1 raw36837step1Labels := by
      have ha : raw36837step1 = (fun i j => raw36837step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36837step1 raw36837step0; decide +kernel
      have hl : raw36837step1Labels = raw36837step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36837step0 raw36837step0Labels permutation150 permutation7
    mixedMoment B raw36837step1 raw36837step1Labels = mixedMoment B raw36837step2 raw36837step2Labels := by
      have ha : raw36837step2 = raw36837step1 := by apply Matrix.ext; unfold raw36837step2 raw36837step1; decide +kernel
      have hl : raw36837step1Labels = labelEmbedding1 ∘ raw36837step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36837step1 raw36837step1Labels raw36837step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

theorem canonical36838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36838 raw36838Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw36838 raw36838Labels = mixedMoment B raw36838step0 raw36838step0Labels := by
      have hz : ∀ j, raw36838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36838step0 = (fun i j => raw36838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36838step0 raw36838; decide +kernel
      have hl : raw36838step0Labels = raw36838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36838 raw36838Labels permutation346 hz
    mixedMoment B raw36838step0 raw36838step0Labels = mixedMoment B raw36838step1 raw36838step1Labels := by
      have ha : raw36838step1 = (fun i j => raw36838step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36838step1 raw36838step0; decide +kernel
      have hl : raw36838step1Labels = raw36838step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36838step0 raw36838step0Labels permutation144 permutation7
    mixedMoment B raw36838step1 raw36838step1Labels = mixedMoment B raw36838step2 raw36838step2Labels := by
      have ha : raw36838step2 = raw36838step1 := by apply Matrix.ext; unfold raw36838step2 raw36838step1; decide +kernel
      have hl : raw36838step1Labels = labelEmbedding1 ∘ raw36838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36838step1 raw36838step1Labels raw36838step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical36839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36839 raw36839Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw36839 raw36839Labels = mixedMoment B raw36839step0 raw36839step0Labels := by
      have ha : raw36839step0 = (fun i j => raw36839 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36839step0 raw36839; decide +kernel
      have hl : raw36839step0Labels = raw36839Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36839 raw36839Labels permutation663 permutation7
    mixedMoment B raw36839step0 raw36839step0Labels = mixedMoment B raw36839step1 raw36839step1Labels := by
      have ha : raw36839step1 = raw36839step0 := by apply Matrix.ext; unfold raw36839step1 raw36839step0; decide +kernel
      have hl : raw36839step0Labels = labelEmbedding1 ∘ raw36839step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36839step0 raw36839step0Labels raw36839step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

theorem canonical36840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36840 raw36840Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw36840 raw36840Labels = mixedMoment B raw36840step0 raw36840step0Labels := by
      have hz : ∀ j, raw36840 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36840step0 = (fun i j => raw36840 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36840step0 raw36840; decide +kernel
      have hl : raw36840step0Labels = raw36840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36840 raw36840Labels permutation520 hz
    mixedMoment B raw36840step0 raw36840step0Labels = mixedMoment B raw36840step1 raw36840step1Labels := by
      have hz : ∀ j, raw36840step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36840step1 = (fun i j => raw36840step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36840step1 raw36840step0; decide +kernel
      have hl : raw36840step1Labels = raw36840step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36840step0 raw36840step0Labels permutation80 hz
    mixedMoment B raw36840step1 raw36840step1Labels = mixedMoment B raw36840step2 raw36840step2Labels := by
      have ha : raw36840step2 = (fun i j => raw36840step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36840step2 raw36840step1; decide +kernel
      have hl : raw36840step2Labels = raw36840step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36840step1 raw36840step1Labels permutation30 permutation7
    mixedMoment B raw36840step2 raw36840step2Labels = mixedMoment B raw36840step3 raw36840step3Labels := by
      have ha : raw36840step3 = raw36840step2 := by apply Matrix.ext; unfold raw36840step3 raw36840step2; decide +kernel
      have hl : raw36840step2Labels = labelEmbedding1 ∘ raw36840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36840step2 raw36840step2Labels raw36840step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

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

theorem sound2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2176 node2176Labels = Sparse.eval nodeValue2176 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2176) = mixedMoment B node2176 node2176Labels := rfl
  simpa [nodeValue2176, Sparse.eval] using hc.symm

theorem sound2178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2178 node2178Labels = Sparse.eval nodeValue2178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2178) = mixedMoment B node2178 node2178Labels := rfl
  simpa [nodeValue2178, Sparse.eval] using hc.symm

theorem sound2181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2181 node2181Labels = Sparse.eval nodeValue2181 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2181) = mixedMoment B node2181 node2181Labels := rfl
  simpa [nodeValue2181, Sparse.eval] using hc.symm

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

theorem sound2213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2213 node2213Labels = Sparse.eval nodeValue2213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2213) = mixedMoment B node2213 node2213Labels := rfl
  simpa [nodeValue2213, Sparse.eval] using hc.symm

theorem sound2229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2229 node2229Labels = Sparse.eval nodeValue2229 (mixedVector B) := by
  simpa only [nodeValue2229, Sparse.eval_nil] using zero2229 B _hB _hF

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

theorem sound2658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2658 node2658Labels = Sparse.eval nodeValue2658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2658) = mixedMoment B node2658 node2658Labels := rfl
  simpa [nodeValue2658, Sparse.eval] using hc.symm

theorem sound2659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2659 node2659Labels = Sparse.eval nodeValue2659 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2659) = mixedMoment B node2659 node2659Labels := rfl
  simpa [nodeValue2659, Sparse.eval] using hc.symm

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

theorem zero2689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2689 node2689Labels = 0 := by
  exact mixedMoment_alpha B hF node2689 node2689Labels 1 permutation216
    (by decide +kernel)

theorem zero2695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2695 node2695Labels = 0 := by
  exact mixedMoment_alpha B hF node2695 node2695Labels 1 permutation212
    (by decide +kernel)

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

theorem sound2689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2689 node2689Labels = Sparse.eval nodeValue2689 (mixedVector B) := by
  simpa only [nodeValue2689, Sparse.eval_nil] using zero2689 B _hB _hF

theorem sound2690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2690 node2690Labels = Sparse.eval nodeValue2690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2690) = mixedMoment B node2690 node2690Labels := rfl
  simpa [nodeValue2690, Sparse.eval] using hc.symm

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

theorem sound2695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2695 node2695Labels = Sparse.eval nodeValue2695 (mixedVector B) := by
  simpa only [nodeValue2695, Sparse.eval_nil] using zero2695 B _hB _hF

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

theorem sound2706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2706 node2706Labels = Sparse.eval nodeValue2706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2706) = mixedMoment B node2706 node2706Labels := rfl
  simpa [nodeValue2706, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3025 node3025Labels = Sparse.eval nodeValue3025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3025) = mixedMoment B node3025 node3025Labels := rfl
  simpa [nodeValue3025, Sparse.eval] using hc.symm

theorem sound3059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3059 node3059Labels = Sparse.eval nodeValue3059 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3059) = mixedMoment B node3059 node3059Labels := rfl
  simpa [nodeValue3059, Sparse.eval] using hc.symm

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

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

theorem sound3078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3078 node3078Labels = Sparse.eval nodeValue3078 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3078) = mixedMoment B node3078 node3078Labels := rfl
  simpa [nodeValue3078, Sparse.eval] using hc.symm

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

theorem sound3404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3404 node3404Labels = Sparse.eval nodeValue3404 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3404) = mixedMoment B node3404 node3404Labels := rfl
  simpa [nodeValue3404, Sparse.eval] using hc.symm

theorem sound3406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3406 node3406Labels = Sparse.eval nodeValue3406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3406) = mixedMoment B node3406 node3406Labels := rfl
  simpa [nodeValue3406, Sparse.eval] using hc.symm

theorem sound3407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3407 node3407Labels = Sparse.eval nodeValue3407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3407) = mixedMoment B node3407 node3407Labels := rfl
  simpa [nodeValue3407, Sparse.eval] using hc.symm

theorem sound3408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3408 node3408Labels = Sparse.eval nodeValue3408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3408) = mixedMoment B node3408 node3408Labels := rfl
  simpa [nodeValue3408, Sparse.eval] using hc.symm

theorem sound3414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3414 node3414Labels = Sparse.eval nodeValue3414 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3414) = mixedMoment B node3414 node3414Labels := rfl
  simpa [nodeValue3414, Sparse.eval] using hc.symm

theorem sound3416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3416 node3416Labels = Sparse.eval nodeValue3416 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3416) = mixedMoment B node3416 node3416Labels := rfl
  simpa [nodeValue3416, Sparse.eval] using hc.symm

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

theorem sound3456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3456 node3456Labels = Sparse.eval nodeValue3456 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3456) = mixedMoment B node3456 node3456Labels := rfl
  simpa [nodeValue3456, Sparse.eval] using hc.symm

theorem sound3459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3459 node3459Labels = Sparse.eval nodeValue3459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3459) = mixedMoment B node3459 node3459Labels := rfl
  simpa [nodeValue3459, Sparse.eval] using hc.symm

theorem sound3477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3477 node3477Labels = Sparse.eval nodeValue3477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3477) = mixedMoment B node3477 node3477Labels := rfl
  simpa [nodeValue3477, Sparse.eval] using hc.symm

theorem sound3482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3482 node3482Labels = Sparse.eval nodeValue3482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3482) = mixedMoment B node3482 node3482Labels := rfl
  simpa [nodeValue3482, Sparse.eval] using hc.symm

theorem sound3508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3508 node3508Labels = Sparse.eval nodeValue3508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3508) = mixedMoment B node3508 node3508Labels := rfl
  simpa [nodeValue3508, Sparse.eval] using hc.symm

theorem sound3509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3509 node3509Labels = Sparse.eval nodeValue3509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3509) = mixedMoment B node3509 node3509Labels := rfl
  simpa [nodeValue3509, Sparse.eval] using hc.symm

theorem sound3510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3510 node3510Labels = Sparse.eval nodeValue3510 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3510) = mixedMoment B node3510 node3510Labels := rfl
  simpa [nodeValue3510, Sparse.eval] using hc.symm

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

theorem zero3520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3520 node3520Labels = 0 := by
  exact mixedMoment_alpha B hF node3520 node3520Labels 1 permutation446
    (by decide +kernel)

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

theorem sound3520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3520 node3520Labels = Sparse.eval nodeValue3520 (mixedVector B) := by
  simpa only [nodeValue3520, Sparse.eval_nil] using zero3520 B _hB _hF

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

theorem sound3537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3537 node3537Labels = Sparse.eval nodeValue3537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3537) = mixedMoment B node3537 node3537Labels := rfl
  simpa [nodeValue3537, Sparse.eval] using hc.symm

theorem sound3556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3556 node3556Labels = Sparse.eval nodeValue3556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3556) = mixedMoment B node3556 node3556Labels := rfl
  simpa [nodeValue3556, Sparse.eval] using hc.symm

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

theorem sound3585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3585 node3585Labels = Sparse.eval nodeValue3585 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3585) = mixedMoment B node3585 node3585Labels := rfl
  simpa [nodeValue3585, Sparse.eval] using hc.symm

theorem sound3590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3590 node3590Labels = Sparse.eval nodeValue3590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3590) = mixedMoment B node3590 node3590Labels := rfl
  simpa [nodeValue3590, Sparse.eval] using hc.symm

theorem sound3605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3605 node3605Labels = Sparse.eval nodeValue3605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3605) = mixedMoment B node3605 node3605Labels := rfl
  simpa [nodeValue3605, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3765 node3765Labels = 0 := by
  exact mixedMoment_order_one B hB node3765 node3765Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3766 node3766Labels = 0 := by
  exact mixedMoment_order_one B hB node3766 node3766Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3756 node3756Labels = Sparse.eval nodeValue3756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3756) = mixedMoment B node3756 node3756Labels := rfl
  simpa [nodeValue3756, Sparse.eval] using hc.symm

theorem sound3758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3758 node3758Labels = Sparse.eval nodeValue3758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3758) = mixedMoment B node3758 node3758Labels := rfl
  simpa [nodeValue3758, Sparse.eval] using hc.symm

theorem sound3760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3760 node3760Labels = Sparse.eval nodeValue3760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3760) = mixedMoment B node3760 node3760Labels := rfl
  simpa [nodeValue3760, Sparse.eval] using hc.symm

theorem sound3761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3761 node3761Labels = Sparse.eval nodeValue3761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3761) = mixedMoment B node3761 node3761Labels := rfl
  simpa [nodeValue3761, Sparse.eval] using hc.symm

theorem sound3764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3764 node3764Labels = Sparse.eval nodeValue3764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3764) = mixedMoment B node3764 node3764Labels := rfl
  simpa [nodeValue3764, Sparse.eval] using hc.symm

theorem sound3765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3765 node3765Labels = Sparse.eval nodeValue3765 (mixedVector B) := by
  simpa only [nodeValue3765, Sparse.eval_nil] using zero3765 B _hB _hF

theorem sound3766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3766 node3766Labels = Sparse.eval nodeValue3766 (mixedVector B) := by
  simpa only [nodeValue3766, Sparse.eval_nil] using zero3766 B _hB _hF

theorem sound3768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3768 node3768Labels = Sparse.eval nodeValue3768 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3768) = mixedMoment B node3768 node3768Labels := rfl
  simpa [nodeValue3768, Sparse.eval] using hc.symm

theorem sound3769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3769 node3769Labels = Sparse.eval nodeValue3769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3769) = mixedMoment B node3769 node3769Labels := rfl
  simpa [nodeValue3769, Sparse.eval] using hc.symm

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

theorem sound3773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3773 node3773Labels = Sparse.eval nodeValue3773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3773) = mixedMoment B node3773 node3773Labels := rfl
  simpa [nodeValue3773, Sparse.eval] using hc.symm

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

theorem zero3798 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3798 node3798Labels = 0 := by
  exact mixedMoment_order_one B hB node3798 node3798Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = 0 := by
  exact mixedMoment_order_one B hB node3806 node3806Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = 0 := by
  exact mixedMoment_order_one B hB node3807 node3807Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = 0 := by
  exact mixedMoment_order_one B hB node3816 node3816Labels 1
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

theorem sound3792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3792 node3792Labels = Sparse.eval nodeValue3792 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3792) = mixedMoment B node3792 node3792Labels := rfl
  simpa [nodeValue3792, Sparse.eval] using hc.symm

theorem sound3798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3798 node3798Labels = Sparse.eval nodeValue3798 (mixedVector B) := by
  simpa only [nodeValue3798, Sparse.eval_nil] using zero3798 B _hB _hF

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

theorem sound3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3800 node3800Labels = Sparse.eval nodeValue3800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3800) = mixedMoment B node3800 node3800Labels := rfl
  simpa [nodeValue3800, Sparse.eval] using hc.symm

theorem sound3806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = Sparse.eval nodeValue3806 (mixedVector B) := by
  simpa only [nodeValue3806, Sparse.eval_nil] using zero3806 B _hB _hF

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

theorem sound3810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3810 node3810Labels = Sparse.eval nodeValue3810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3810) = mixedMoment B node3810 node3810Labels := rfl
  simpa [nodeValue3810, Sparse.eval] using hc.symm

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

theorem sound3815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3815 node3815Labels = Sparse.eval nodeValue3815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3815) = mixedMoment B node3815 node3815Labels := rfl
  simpa [nodeValue3815, Sparse.eval] using hc.symm

theorem sound3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = Sparse.eval nodeValue3816 (mixedVector B) := by
  simpa only [nodeValue3816, Sparse.eval_nil] using zero3816 B _hB _hF

theorem sound3835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3835 node3835Labels = Sparse.eval nodeValue3835 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3835) = mixedMoment B node3835 node3835Labels := rfl
  simpa [nodeValue3835, Sparse.eval] using hc.symm

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

theorem sound3842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3842 node3842Labels = Sparse.eval nodeValue3842 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3842) = mixedMoment B node3842 node3842Labels := rfl
  simpa [nodeValue3842, Sparse.eval] using hc.symm

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

theorem sound3869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3869 node3869Labels = Sparse.eval nodeValue3869 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3869) = mixedMoment B node3869 node3869Labels := rfl
  simpa [nodeValue3869, Sparse.eval] using hc.symm

theorem sound3874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3874 node3874Labels = Sparse.eval nodeValue3874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3874) = mixedMoment B node3874 node3874Labels := rfl
  simpa [nodeValue3874, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3951 node3951Labels = 0 := by
  exact mixedMoment_alpha B hF node3951 node3951Labels 1 permutation216
    (by decide +kernel)

theorem zero3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = 0 := by
  exact mixedMoment_alpha B hF node3953 node3953Labels 1 permutation200
    (by decide +kernel)

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

theorem sound3951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3951 node3951Labels = Sparse.eval nodeValue3951 (mixedVector B) := by
  simpa only [nodeValue3951, Sparse.eval_nil] using zero3951 B _hB _hF

theorem sound3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = Sparse.eval nodeValue3953 (mixedVector B) := by
  simpa only [nodeValue3953, Sparse.eval_nil] using zero3953 B _hB _hF

theorem sound3957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3957 node3957Labels = Sparse.eval nodeValue3957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3957) = mixedMoment B node3957 node3957Labels := rfl
  simpa [nodeValue3957, Sparse.eval] using hc.symm

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

theorem sound3973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3973 node3973Labels = Sparse.eval nodeValue3973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3973) = mixedMoment B node3973 node3973Labels := rfl
  simpa [nodeValue3973, Sparse.eval] using hc.symm

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources81
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2608 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2608 + difference 0 1) (sourceB2608 + difference 1 0) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA2608 + difference 0 1) (sourceB2608 + difference 1 0) sourceC2608) = raw36311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36311; decide +kernel
    rw [ha]
    exact (canonical36311 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2608 + difference 0 2) (sourceB2608 + difference 2 0) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3798) := by
    have ha : (tripleCharges (sourceA2608 + difference 0 2) (sourceB2608 + difference 2 0) sourceC2608) = raw36312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36312; decide +kernel
    rw [ha]
    exact (canonical36312 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2608 + difference 0 3) (sourceB2608 + difference 3 0) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2608 + difference 0 3) (sourceB2608 + difference 3 0) sourceC2608) = raw36313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36313; decide +kernel
    rw [ha]
    exact (canonical36313 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2608 + difference 0 4) (sourceB2608 + difference 4 0) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2608 + difference 0 4) (sourceB2608 + difference 4 0) sourceC2608) = raw36314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36314; decide +kernel
    rw [ha]
    exact (canonical36314 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2608 + difference 0 5) (sourceB2608 + difference 5 0) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA2608 + difference 0 5) (sourceB2608 + difference 5 0) sourceC2608) = raw36315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36315; decide +kernel
    rw [ha]
    exact (canonical36315 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2608 + difference 1 0) (sourceB2608 + difference 0 1) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA2608 + difference 1 0) (sourceB2608 + difference 0 1) sourceC2608) = raw36316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36316; decide +kernel
    rw [ha]
    exact (canonical36316 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2608 + difference 1 2) (sourceB2608 + difference 2 1) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3798) := by
    have ha : (tripleCharges (sourceA2608 + difference 1 2) (sourceB2608 + difference 2 1) sourceC2608) = raw32443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32443; decide +kernel
    rw [ha]
    exact (canonical32443 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2608 + difference 1 3) (sourceB2608 + difference 3 1) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2608 + difference 1 3) (sourceB2608 + difference 3 1) sourceC2608) = raw32444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32444; decide +kernel
    rw [ha]
    exact (canonical32444 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2608 + difference 1 4) (sourceB2608 + difference 4 1) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2608 + difference 1 4) (sourceB2608 + difference 4 1) sourceC2608) = raw32445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32445; decide +kernel
    rw [ha]
    exact (canonical32445 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2608 + difference 1 5) (sourceB2608 + difference 5 1) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA2608 + difference 1 5) (sourceB2608 + difference 5 1) sourceC2608) = raw32446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32446; decide +kernel
    rw [ha]
    exact (canonical32446 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2608 + difference 2 0) (sourceB2608 + difference 0 2) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2608 + difference 2 0) (sourceB2608 + difference 0 2) sourceC2608) = raw32453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32453; decide +kernel
    rw [ha]
    exact (canonical32453 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2608 + difference 2 1) (sourceB2608 + difference 1 2) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2608 + difference 2 1) (sourceB2608 + difference 1 2) sourceC2608) = raw36317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36317; decide +kernel
    rw [ha]
    exact (canonical36317 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2608 + difference 2 3) (sourceB2608 + difference 3 2) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3842) := by
    have ha : (tripleCharges (sourceA2608 + difference 2 3) (sourceB2608 + difference 3 2) sourceC2608) = raw36318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36318; decide +kernel
    rw [ha]
    exact (canonical36318 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2608 + difference 2 4) (sourceB2608 + difference 4 2) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3815) := by
    have ha : (tripleCharges (sourceA2608 + difference 2 4) (sourceB2608 + difference 4 2) sourceC2608) = raw36319 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36319; decide +kernel
    rw [ha]
    exact (canonical36319 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2608 + difference 2 5) (sourceB2608 + difference 5 2) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3973) := by
    have ha : (tripleCharges (sourceA2608 + difference 2 5) (sourceB2608 + difference 5 2) sourceC2608) = raw36320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36320; decide +kernel
    rw [ha]
    exact (canonical36320 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2608 + difference 3 0) (sourceB2608 + difference 0 3) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2608 + difference 3 0) (sourceB2608 + difference 0 3) sourceC2608) = raw32458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32458; decide +kernel
    rw [ha]
    exact (canonical32458 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2608 + difference 3 1) (sourceB2608 + difference 1 3) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2608 + difference 3 1) (sourceB2608 + difference 1 3) sourceC2608) = raw36321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36321; decide +kernel
    rw [ha]
    exact (canonical36321 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2608 + difference 3 2) (sourceB2608 + difference 2 3) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3756) := by
    have ha : (tripleCharges (sourceA2608 + difference 3 2) (sourceB2608 + difference 2 3) sourceC2608) = raw36322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36322; decide +kernel
    rw [ha]
    exact (canonical36322 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2608 + difference 3 4) (sourceB2608 + difference 4 3) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3773) := by
    have ha : (tripleCharges (sourceA2608 + difference 3 4) (sourceB2608 + difference 4 3) sourceC2608) = raw36323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36323; decide +kernel
    rw [ha]
    exact (canonical36323 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2608 + difference 3 5) (sourceB2608 + difference 5 3) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3951) := by
    have ha : (tripleCharges (sourceA2608 + difference 3 5) (sourceB2608 + difference 5 3) sourceC2608) = raw36324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36324; decide +kernel
    rw [ha]
    exact (canonical36324 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2608 + difference 4 0) (sourceB2608 + difference 0 4) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2608 + difference 4 0) (sourceB2608 + difference 0 4) sourceC2608) = raw32463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32463; decide +kernel
    rw [ha]
    exact (canonical32463 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2608 + difference 4 1) (sourceB2608 + difference 1 4) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2608 + difference 4 1) (sourceB2608 + difference 1 4) sourceC2608) = raw36325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36325; decide +kernel
    rw [ha]
    exact (canonical36325 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2608 + difference 4 2) (sourceB2608 + difference 2 4) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3792) := by
    have ha : (tripleCharges (sourceA2608 + difference 4 2) (sourceB2608 + difference 2 4) sourceC2608) = raw36326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36326; decide +kernel
    rw [ha]
    exact (canonical36326 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2608 + difference 4 3) (sourceB2608 + difference 3 4) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3835) := by
    have ha : (tripleCharges (sourceA2608 + difference 4 3) (sourceB2608 + difference 3 4) sourceC2608) = raw36327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36327; decide +kernel
    rw [ha]
    exact (canonical36327 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2608 + difference 4 5) (sourceB2608 + difference 5 4) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3842) := by
    have ha : (tripleCharges (sourceA2608 + difference 4 5) (sourceB2608 + difference 5 4) sourceC2608) = raw36328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36328; decide +kernel
    rw [ha]
    exact (canonical36328 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2608 + difference 5 0) (sourceB2608 + difference 0 5) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2608 + difference 5 0) (sourceB2608 + difference 0 5) sourceC2608) = raw32468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32468; decide +kernel
    rw [ha]
    exact (canonical32468 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2608 + difference 5 1) (sourceB2608 + difference 1 5) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2608 + difference 5 1) (sourceB2608 + difference 1 5) sourceC2608) = raw36329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36329; decide +kernel
    rw [ha]
    exact (canonical36329 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2608 + difference 5 2) (sourceB2608 + difference 2 5) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3456) := by
    have ha : (tripleCharges (sourceA2608 + difference 5 2) (sourceB2608 + difference 2 5) sourceC2608) = raw36330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36330; decide +kernel
    rw [ha]
    exact (canonical36330 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2608 + difference 5 3) (sourceB2608 + difference 3 5) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2608 + difference 5 3) (sourceB2608 + difference 3 5) sourceC2608) = raw36331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36331; decide +kernel
    rw [ha]
    exact (canonical36331 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2608 + difference 5 4) (sourceB2608 + difference 4 5) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2608 + difference 5 4) (sourceB2608 + difference 4 5) sourceC2608) = raw36332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36332; decide +kernel
    rw [ha]
    exact (canonical36332 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2608 sourceB2608 sourceC2608
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2608, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2612 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2612 + difference 0 1) (sourceB2612 + difference 1 0) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3477) := by
    have ha : (tripleCharges (sourceA2612 + difference 0 1) (sourceB2612 + difference 1 0) sourceC2612) = raw36403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36403; decide +kernel
    rw [ha]
    exact (canonical36403 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2612 + difference 0 2) (sourceB2612 + difference 2 0) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3810) := by
    have ha : (tripleCharges (sourceA2612 + difference 0 2) (sourceB2612 + difference 2 0) sourceC2612) = raw36404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36404; decide +kernel
    rw [ha]
    exact (canonical36404 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2612 + difference 0 3) (sourceB2612 + difference 3 0) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA2612 + difference 0 3) (sourceB2612 + difference 3 0) sourceC2612) = raw36405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36405; decide +kernel
    rw [ha]
    exact (canonical36405 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2612 + difference 0 4) (sourceB2612 + difference 4 0) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA2612 + difference 0 4) (sourceB2612 + difference 4 0) sourceC2612) = raw36406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36406; decide +kernel
    rw [ha]
    exact (canonical36406 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2612 + difference 0 5) (sourceB2612 + difference 5 0) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA2612 + difference 0 5) (sourceB2612 + difference 5 0) sourceC2612) = raw19110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19110; decide +kernel
    rw [ha]
    exact (canonical19110 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2612 + difference 1 0) (sourceB2612 + difference 0 1) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA2612 + difference 1 0) (sourceB2612 + difference 0 1) sourceC2612) = raw19135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19135; decide +kernel
    rw [ha]
    exact (canonical19135 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2612 + difference 1 2) (sourceB2612 + difference 2 1) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA2612 + difference 1 2) (sourceB2612 + difference 2 1) sourceC2612) = raw19137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19137; decide +kernel
    rw [ha]
    exact (canonical19137 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2612 + difference 1 3) (sourceB2612 + difference 3 1) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA2612 + difference 1 3) (sourceB2612 + difference 3 1) sourceC2612) = raw19138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19138; decide +kernel
    rw [ha]
    exact (canonical19138 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2612 + difference 1 4) (sourceB2612 + difference 4 1) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA2612 + difference 1 4) (sourceB2612 + difference 4 1) sourceC2612) = raw19139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19139; decide +kernel
    rw [ha]
    exact (canonical19139 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2612 + difference 1 5) (sourceB2612 + difference 5 1) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA2612 + difference 1 5) (sourceB2612 + difference 5 1) sourceC2612) = raw36407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36407; decide +kernel
    rw [ha]
    exact (canonical36407 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2612 + difference 2 0) (sourceB2612 + difference 0 2) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3585) := by
    have ha : (tripleCharges (sourceA2612 + difference 2 0) (sourceB2612 + difference 0 2) sourceC2612) = raw36408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36408; decide +kernel
    rw [ha]
    exact (canonical36408 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2612 + difference 2 1) (sourceB2612 + difference 1 2) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3416) := by
    have ha : (tripleCharges (sourceA2612 + difference 2 1) (sourceB2612 + difference 1 2) sourceC2612) = raw36409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36409; decide +kernel
    rw [ha]
    exact (canonical36409 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2612 + difference 2 3) (sourceB2612 + difference 3 2) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA2612 + difference 2 3) (sourceB2612 + difference 3 2) sourceC2612) = raw36410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36410; decide +kernel
    rw [ha]
    exact (canonical36410 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2612 + difference 2 4) (sourceB2612 + difference 4 2) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA2612 + difference 2 4) (sourceB2612 + difference 4 2) sourceC2612) = raw36411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36411; decide +kernel
    rw [ha]
    exact (canonical36411 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2612 + difference 2 5) (sourceB2612 + difference 5 2) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3765) := by
    have ha : (tripleCharges (sourceA2612 + difference 2 5) (sourceB2612 + difference 5 2) sourceC2612) = raw19121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19121; decide +kernel
    rw [ha]
    exact (canonical19121 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2612 + difference 3 0) (sourceB2612 + difference 0 3) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2612 + difference 3 0) (sourceB2612 + difference 0 3) sourceC2612) = raw36412 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36412; decide +kernel
    rw [ha]
    exact (canonical36412 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2612 + difference 3 1) (sourceB2612 + difference 1 3) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2612 + difference 3 1) (sourceB2612 + difference 1 3) sourceC2612) = raw36413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36413; decide +kernel
    rw [ha]
    exact (canonical36413 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2612 + difference 3 2) (sourceB2612 + difference 2 3) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2612 + difference 3 2) (sourceB2612 + difference 2 3) sourceC2612) = raw36414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36414; decide +kernel
    rw [ha]
    exact (canonical36414 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2612 + difference 3 4) (sourceB2612 + difference 4 3) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3768) := by
    have ha : (tripleCharges (sourceA2612 + difference 3 4) (sourceB2612 + difference 4 3) sourceC2612) = raw36415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36415; decide +kernel
    rw [ha]
    exact (canonical36415 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2612 + difference 3 5) (sourceB2612 + difference 5 3) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2612 + difference 3 5) (sourceB2612 + difference 5 3) sourceC2612) = raw19126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19126; decide +kernel
    rw [ha]
    exact (canonical19126 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2612 + difference 4 0) (sourceB2612 + difference 0 4) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2612 + difference 4 0) (sourceB2612 + difference 0 4) sourceC2612) = raw36416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36416; decide +kernel
    rw [ha]
    exact (canonical36416 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2612 + difference 4 1) (sourceB2612 + difference 1 4) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2612 + difference 4 1) (sourceB2612 + difference 1 4) sourceC2612) = raw36417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36417; decide +kernel
    rw [ha]
    exact (canonical36417 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2612 + difference 4 2) (sourceB2612 + difference 2 4) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2612 + difference 4 2) (sourceB2612 + difference 2 4) sourceC2612) = raw36418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36418; decide +kernel
    rw [ha]
    exact (canonical36418 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2612 + difference 4 3) (sourceB2612 + difference 3 4) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3768) := by
    have ha : (tripleCharges (sourceA2612 + difference 4 3) (sourceB2612 + difference 3 4) sourceC2612) = raw36419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36419; decide +kernel
    rw [ha]
    exact (canonical36419 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2612 + difference 4 5) (sourceB2612 + difference 5 4) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2612 + difference 4 5) (sourceB2612 + difference 5 4) sourceC2612) = raw19131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19131; decide +kernel
    rw [ha]
    exact (canonical19131 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2612 + difference 5 0) (sourceB2612 + difference 0 5) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2176) := by
    have ha : (tripleCharges (sourceA2612 + difference 5 0) (sourceB2612 + difference 0 5) sourceC2612) = raw36420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36420; decide +kernel
    rw [ha]
    exact (canonical36420 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2612 + difference 5 1) (sourceB2612 + difference 1 5) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2181) := by
    have ha : (tripleCharges (sourceA2612 + difference 5 1) (sourceB2612 + difference 1 5) sourceC2612) = raw36421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36421; decide +kernel
    rw [ha]
    exact (canonical36421 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2612 + difference 5 2) (sourceB2612 + difference 2 5) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2178) := by
    have ha : (tripleCharges (sourceA2612 + difference 5 2) (sourceB2612 + difference 2 5) sourceC2612) = raw36422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36422; decide +kernel
    rw [ha]
    exact (canonical36422 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2612 + difference 5 3) (sourceB2612 + difference 3 5) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2612 + difference 5 3) (sourceB2612 + difference 3 5) sourceC2612) = raw36423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36423; decide +kernel
    rw [ha]
    exact (canonical36423 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2612 + difference 5 4) (sourceB2612 + difference 4 5) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2612 + difference 5 4) (sourceB2612 + difference 4 5) sourceC2612) = raw36424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36424; decide +kernel
    rw [ha]
    exact (canonical36424 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2612 sourceB2612 sourceC2612
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2612, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2619 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2619 + difference 0 1) (sourceB2619 + difference 1 0) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA2619 + difference 0 1) (sourceB2619 + difference 1 0) sourceC2619) = raw36552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36552; decide +kernel
    rw [ha]
    exact (canonical36552 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2619 + difference 0 2) (sourceB2619 + difference 2 0) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2619 + difference 0 2) (sourceB2619 + difference 2 0) sourceC2619) = raw36553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36553; decide +kernel
    rw [ha]
    exact (canonical36553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2619 + difference 0 3) (sourceB2619 + difference 3 0) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2619 + difference 0 3) (sourceB2619 + difference 3 0) sourceC2619) = raw17918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17918; decide +kernel
    rw [ha]
    exact (canonical17918 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2619 + difference 0 4) (sourceB2619 + difference 4 0) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2619 + difference 0 4) (sourceB2619 + difference 4 0) sourceC2619) = raw36554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36554; decide +kernel
    rw [ha]
    exact (canonical36554 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2619 + difference 0 5) (sourceB2619 + difference 5 0) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA2619 + difference 0 5) (sourceB2619 + difference 5 0) sourceC2619) = raw36555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36555; decide +kernel
    rw [ha]
    exact (canonical36555 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2619 + difference 1 0) (sourceB2619 + difference 0 1) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA2619 + difference 1 0) (sourceB2619 + difference 0 1) sourceC2619) = raw17933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17933; decide +kernel
    rw [ha]
    exact (canonical17933 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2619 + difference 1 2) (sourceB2619 + difference 2 1) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA2619 + difference 1 2) (sourceB2619 + difference 2 1) sourceC2619) = raw17935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17935; decide +kernel
    rw [ha]
    exact (canonical17935 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2619 + difference 1 3) (sourceB2619 + difference 3 1) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA2619 + difference 1 3) (sourceB2619 + difference 3 1) sourceC2619) = raw36556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36556; decide +kernel
    rw [ha]
    exact (canonical36556 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2619 + difference 1 4) (sourceB2619 + difference 4 1) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA2619 + difference 1 4) (sourceB2619 + difference 4 1) sourceC2619) = raw17936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17936; decide +kernel
    rw [ha]
    exact (canonical17936 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2619 + difference 1 5) (sourceB2619 + difference 5 1) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA2619 + difference 1 5) (sourceB2619 + difference 5 1) sourceC2619) = raw17937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17937; decide +kernel
    rw [ha]
    exact (canonical17937 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2619 + difference 2 0) (sourceB2619 + difference 0 2) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3590) := by
    have ha : (tripleCharges (sourceA2619 + difference 2 0) (sourceB2619 + difference 0 2) sourceC2619) = raw36557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36557; decide +kernel
    rw [ha]
    exact (canonical36557 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2619 + difference 2 1) (sourceB2619 + difference 1 2) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3404) := by
    have ha : (tripleCharges (sourceA2619 + difference 2 1) (sourceB2619 + difference 1 2) sourceC2619) = raw36558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36558; decide +kernel
    rw [ha]
    exact (canonical36558 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2619 + difference 2 3) (sourceB2619 + difference 3 2) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2619 + difference 2 3) (sourceB2619 + difference 3 2) sourceC2619) = raw17929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17929; decide +kernel
    rw [ha]
    exact (canonical17929 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2619 + difference 2 4) (sourceB2619 + difference 4 2) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2619 + difference 2 4) (sourceB2619 + difference 4 2) sourceC2619) = raw36559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36559; decide +kernel
    rw [ha]
    exact (canonical36559 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2619 + difference 2 5) (sourceB2619 + difference 5 2) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA2619 + difference 2 5) (sourceB2619 + difference 5 2) sourceC2619) = raw36560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36560; decide +kernel
    rw [ha]
    exact (canonical36560 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2619 + difference 3 0) (sourceB2619 + difference 0 3) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3509) := by
    have ha : (tripleCharges (sourceA2619 + difference 3 0) (sourceB2619 + difference 0 3) sourceC2619) = raw36561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36561; decide +kernel
    rw [ha]
    exact (canonical36561 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2619 + difference 3 1) (sourceB2619 + difference 1 3) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2619 + difference 3 1) (sourceB2619 + difference 1 3) sourceC2619) = raw36562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36562; decide +kernel
    rw [ha]
    exact (canonical36562 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2619 + difference 3 2) (sourceB2619 + difference 2 3) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3760) := by
    have ha : (tripleCharges (sourceA2619 + difference 3 2) (sourceB2619 + difference 2 3) sourceC2619) = raw36563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36563; decide +kernel
    rw [ha]
    exact (canonical36563 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2619 + difference 3 4) (sourceB2619 + difference 4 3) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2619 + difference 3 4) (sourceB2619 + difference 4 3) sourceC2619) = raw36564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36564; decide +kernel
    rw [ha]
    exact (canonical36564 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2619 + difference 3 5) (sourceB2619 + difference 5 3) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2619 + difference 3 5) (sourceB2619 + difference 5 3) sourceC2619) = raw36565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36565; decide +kernel
    rw [ha]
    exact (canonical36565 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2619 + difference 4 0) (sourceB2619 + difference 0 4) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3509) := by
    have ha : (tripleCharges (sourceA2619 + difference 4 0) (sourceB2619 + difference 0 4) sourceC2619) = raw36566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36566; decide +kernel
    rw [ha]
    exact (canonical36566 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2619 + difference 4 1) (sourceB2619 + difference 1 4) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2619 + difference 4 1) (sourceB2619 + difference 1 4) sourceC2619) = raw36567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36567; decide +kernel
    rw [ha]
    exact (canonical36567 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2619 + difference 4 2) (sourceB2619 + difference 2 4) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3760) := by
    have ha : (tripleCharges (sourceA2619 + difference 4 2) (sourceB2619 + difference 2 4) sourceC2619) = raw36568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36568; decide +kernel
    rw [ha]
    exact (canonical36568 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2619 + difference 4 3) (sourceB2619 + difference 3 4) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2619 + difference 4 3) (sourceB2619 + difference 3 4) sourceC2619) = raw17939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17939; decide +kernel
    rw [ha]
    exact (canonical17939 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2619 + difference 4 5) (sourceB2619 + difference 5 4) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2619 + difference 4 5) (sourceB2619 + difference 5 4) sourceC2619) = raw36569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36569; decide +kernel
    rw [ha]
    exact (canonical36569 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2619 + difference 5 0) (sourceB2619 + difference 0 5) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3510) := by
    have ha : (tripleCharges (sourceA2619 + difference 5 0) (sourceB2619 + difference 0 5) sourceC2619) = raw36570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36570; decide +kernel
    rw [ha]
    exact (canonical36570 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2619 + difference 5 1) (sourceB2619 + difference 1 5) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3403) := by
    have ha : (tripleCharges (sourceA2619 + difference 5 1) (sourceB2619 + difference 1 5) sourceC2619) = raw36571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36571; decide +kernel
    rw [ha]
    exact (canonical36571 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2619 + difference 5 2) (sourceB2619 + difference 2 5) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3556) := by
    have ha : (tripleCharges (sourceA2619 + difference 5 2) (sourceB2619 + difference 2 5) sourceC2619) = raw36572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36572; decide +kernel
    rw [ha]
    exact (canonical36572 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2619 + difference 5 3) (sourceB2619 + difference 3 5) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2619 + difference 5 3) (sourceB2619 + difference 3 5) sourceC2619) = raw17944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17944; decide +kernel
    rw [ha]
    exact (canonical17944 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2619 + difference 5 4) (sourceB2619 + difference 4 5) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2619 + difference 5 4) (sourceB2619 + difference 4 5) sourceC2619) = raw36573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36573; decide +kernel
    rw [ha]
    exact (canonical36573 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2619 sourceB2619 sourceC2619
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2619, Integer.Sparse.eval]
  linarith only [hs]

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

theorem sourceEq2630 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2630 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2630 + difference 0 1) (sourceB2630 + difference 1 0) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2630 + difference 0 1) (sourceB2630 + difference 1 0) sourceC2630) = raw36815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36815; decide +kernel
    rw [ha]
    exact (canonical36815 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2630 + difference 0 2) (sourceB2630 + difference 2 0) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA2630 + difference 0 2) (sourceB2630 + difference 2 0) sourceC2630) = raw36816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36816; decide +kernel
    rw [ha]
    exact (canonical36816 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2630 + difference 0 3) (sourceB2630 + difference 3 0) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2630 + difference 0 3) (sourceB2630 + difference 3 0) sourceC2630) = raw36817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36817; decide +kernel
    rw [ha]
    exact (canonical36817 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2630 + difference 0 4) (sourceB2630 + difference 4 0) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2630 + difference 0 4) (sourceB2630 + difference 4 0) sourceC2630) = raw36818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36818; decide +kernel
    rw [ha]
    exact (canonical36818 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2630 + difference 0 5) (sourceB2630 + difference 5 0) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA2630 + difference 0 5) (sourceB2630 + difference 5 0) sourceC2630) = raw36819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36819; decide +kernel
    rw [ha]
    exact (canonical36819 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2630 + difference 1 0) (sourceB2630 + difference 0 1) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA2630 + difference 1 0) (sourceB2630 + difference 0 1) sourceC2630) = raw28444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw28444; decide +kernel
    rw [ha]
    exact (canonical28444 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2630 + difference 1 2) (sourceB2630 + difference 2 1) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA2630 + difference 1 2) (sourceB2630 + difference 2 1) sourceC2630) = raw36820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36820; decide +kernel
    rw [ha]
    exact (canonical36820 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2630 + difference 1 3) (sourceB2630 + difference 3 1) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2630 + difference 1 3) (sourceB2630 + difference 3 1) sourceC2630) = raw28429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw28429; decide +kernel
    rw [ha]
    exact (canonical28429 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2630 + difference 1 4) (sourceB2630 + difference 4 1) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2630 + difference 1 4) (sourceB2630 + difference 4 1) sourceC2630) = raw36821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36821; decide +kernel
    rw [ha]
    exact (canonical36821 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2630 + difference 1 5) (sourceB2630 + difference 5 1) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA2630 + difference 1 5) (sourceB2630 + difference 5 1) sourceC2630) = raw36822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36822; decide +kernel
    rw [ha]
    exact (canonical36822 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2630 + difference 2 0) (sourceB2630 + difference 0 2) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2690) := by
    have ha : (tripleCharges (sourceA2630 + difference 2 0) (sourceB2630 + difference 0 2) sourceC2630) = raw36823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36823; decide +kernel
    rw [ha]
    exact (canonical36823 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2630 + difference 2 1) (sourceB2630 + difference 1 2) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2689) := by
    have ha : (tripleCharges (sourceA2630 + difference 2 1) (sourceB2630 + difference 1 2) sourceC2630) = raw36824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36824; decide +kernel
    rw [ha]
    exact (canonical36824 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2630 + difference 2 3) (sourceB2630 + difference 3 2) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2630 + difference 2 3) (sourceB2630 + difference 3 2) sourceC2630) = raw36825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36825; decide +kernel
    rw [ha]
    exact (canonical36825 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2630 + difference 2 4) (sourceB2630 + difference 4 2) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2630 + difference 2 4) (sourceB2630 + difference 4 2) sourceC2630) = raw36826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36826; decide +kernel
    rw [ha]
    exact (canonical36826 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2630 + difference 2 5) (sourceB2630 + difference 5 2) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3059) := by
    have ha : (tripleCharges (sourceA2630 + difference 2 5) (sourceB2630 + difference 5 2) sourceC2630) = raw36827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36827; decide +kernel
    rw [ha]
    exact (canonical36827 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2630 + difference 3 0) (sourceB2630 + difference 0 3) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2659) := by
    have ha : (tripleCharges (sourceA2630 + difference 3 0) (sourceB2630 + difference 0 3) sourceC2630) = raw36828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36828; decide +kernel
    rw [ha]
    exact (canonical36828 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2630 + difference 3 1) (sourceB2630 + difference 1 3) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2630 + difference 3 1) (sourceB2630 + difference 1 3) sourceC2630) = raw36829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36829; decide +kernel
    rw [ha]
    exact (canonical36829 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2630 + difference 3 2) (sourceB2630 + difference 2 3) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2630 + difference 3 2) (sourceB2630 + difference 2 3) sourceC2630) = raw36830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36830; decide +kernel
    rw [ha]
    exact (canonical36830 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2630 + difference 3 4) (sourceB2630 + difference 4 3) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA2630 + difference 3 4) (sourceB2630 + difference 4 3) sourceC2630) = raw36831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36831; decide +kernel
    rw [ha]
    exact (canonical36831 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2630 + difference 3 5) (sourceB2630 + difference 5 3) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA2630 + difference 3 5) (sourceB2630 + difference 5 3) sourceC2630) = raw36832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36832; decide +kernel
    rw [ha]
    exact (canonical36832 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2630 + difference 4 0) (sourceB2630 + difference 0 4) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2659) := by
    have ha : (tripleCharges (sourceA2630 + difference 4 0) (sourceB2630 + difference 0 4) sourceC2630) = raw36833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36833; decide +kernel
    rw [ha]
    exact (canonical36833 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2630 + difference 4 1) (sourceB2630 + difference 1 4) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2630 + difference 4 1) (sourceB2630 + difference 1 4) sourceC2630) = raw36834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36834; decide +kernel
    rw [ha]
    exact (canonical36834 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2630 + difference 4 2) (sourceB2630 + difference 2 4) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2630 + difference 4 2) (sourceB2630 + difference 2 4) sourceC2630) = raw36835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36835; decide +kernel
    rw [ha]
    exact (canonical36835 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2630 + difference 4 3) (sourceB2630 + difference 3 4) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA2630 + difference 4 3) (sourceB2630 + difference 3 4) sourceC2630) = raw36836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36836; decide +kernel
    rw [ha]
    exact (canonical36836 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2630 + difference 4 5) (sourceB2630 + difference 5 4) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA2630 + difference 4 5) (sourceB2630 + difference 5 4) sourceC2630) = raw36837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36837; decide +kernel
    rw [ha]
    exact (canonical36837 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2630 + difference 5 0) (sourceB2630 + difference 0 5) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2630 + difference 5 0) (sourceB2630 + difference 0 5) sourceC2630) = raw28441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw28441; decide +kernel
    rw [ha]
    exact (canonical28441 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2630 + difference 5 1) (sourceB2630 + difference 1 5) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2630 + difference 5 1) (sourceB2630 + difference 1 5) sourceC2630) = raw36838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36838; decide +kernel
    rw [ha]
    exact (canonical36838 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2630 + difference 5 2) (sourceB2630 + difference 2 5) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2174) := by
    have ha : (tripleCharges (sourceA2630 + difference 5 2) (sourceB2630 + difference 2 5) sourceC2630) = raw36839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36839; decide +kernel
    rw [ha]
    exact (canonical36839 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2630 + difference 5 3) (sourceB2630 + difference 3 5) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2630 + difference 5 3) (sourceB2630 + difference 3 5) sourceC2630) = raw28425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw28425; decide +kernel
    rw [ha]
    exact (canonical28425 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2630 + difference 5 4) (sourceB2630 + difference 4 5) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2630 + difference 5 4) (sourceB2630 + difference 4 5) sourceC2630) = raw36840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36840; decide +kernel
    rw [ha]
    exact (canonical36840 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2630 sourceB2630 sourceC2630
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2630, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2081 : Integer.Sparse.reindex keyMap MixedData.row2081 = numericRow2081 := by decide +kernel

theorem numericCheck2081 (x : Master → ℝ) : Integer.Sparse.eval numericRow2081 x =
    (1 : ℝ) * reducedSource2081 x := by
  norm_num [numericRow2081, reducedSource2081, Integer.Sparse.eval, Sparse.eval, nodeValue3406, nodeValue3407, nodeValue3408, nodeValue3414, nodeValue3456, nodeValue3482, nodeValue3520, nodeValue3605, nodeValue3756, nodeValue3773, nodeValue3792, nodeValue3798, nodeValue3815, nodeValue3816, nodeValue3835, nodeValue3842, nodeValue3843, nodeValue3951, nodeValue3973, nodeValue3974]

theorem reindexCheck2083 : Integer.Sparse.reindex keyMap MixedData.row2083 = numericRow2083 := by decide +kernel

theorem numericCheck2083 (x : Master → ℝ) : Integer.Sparse.eval numericRow2083 x =
    (1 : ℝ) * reducedSource2083 x := by
  norm_num [numericRow2083, reducedSource2083, Integer.Sparse.eval, Sparse.eval, nodeValue2176, nodeValue2178, nodeValue2181, nodeValue2213, nodeValue3414, nodeValue3416, nodeValue3477, nodeValue3508, nodeValue3524, nodeValue3585, nodeValue3755, nodeValue3764, nodeValue3765, nodeValue3768, nodeValue3769, nodeValue3806, nodeValue3810, nodeValue3812, nodeValue3869, nodeValue3874, nodeValue3957]

theorem reindexCheck2087 : Integer.Sparse.reindex keyMap MixedData.row2087 = numericRow2087 := by decide +kernel

theorem numericCheck2087 (x : Master → ℝ) : Integer.Sparse.eval numericRow2087 x =
    (1 : ℝ) * reducedSource2087 x := by
  norm_num [numericRow2087, reducedSource2087, Integer.Sparse.eval, Sparse.eval, nodeValue3403, nodeValue3404, nodeValue3406, nodeValue3459, nodeValue3509, nodeValue3510, nodeValue3522, nodeValue3537, nodeValue3556, nodeValue3590, nodeValue3758, nodeValue3760, nodeValue3761, nodeValue3766, nodeValue3770, nodeValue3799, nodeValue3800, nodeValue3807, nodeValue3845, nodeValue3869, nodeValue3953]

theorem reindexCheck2095 : Integer.Sparse.reindex keyMap MixedData.row2095 = numericRow2095 := by decide +kernel

theorem numericCheck2095 (x : Master → ℝ) : Integer.Sparse.eval numericRow2095 x =
    (1 : ℝ) * reducedSource2095 x := by
  norm_num [numericRow2095, reducedSource2095, Integer.Sparse.eval, Sparse.eval, nodeValue2174, nodeValue2185, nodeValue2186, nodeValue2229, nodeValue2653, nodeValue2658, nodeValue2659, nodeValue2686, nodeValue2689, nodeValue2690, nodeValue2694, nodeValue2695, nodeValue2704, nodeValue2705, nodeValue2706, nodeValue2742, nodeValue2743, nodeValue3025, nodeValue3059, nodeValue3077, nodeValue3078]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2081 (mixedVector B) = 0 := by
  have h3406 : mixedVector B (Sum.inr 3406) = Sparse.eval nodeValue3406 (mixedVector B) := by
    change mixedMoment B node3406 node3406Labels = _
    exact sound3406 B hB hF
  have h3407 : mixedVector B (Sum.inr 3407) = Sparse.eval nodeValue3407 (mixedVector B) := by
    change mixedMoment B node3407 node3407Labels = _
    exact sound3407 B hB hF
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3414 : mixedVector B (Sum.inr 3414) = Sparse.eval nodeValue3414 (mixedVector B) := by
    change mixedMoment B node3414 node3414Labels = _
    exact sound3414 B hB hF
  have h3456 : mixedVector B (Sum.inr 3456) = Sparse.eval nodeValue3456 (mixedVector B) := by
    change mixedMoment B node3456 node3456Labels = _
    exact sound3456 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3520 : mixedVector B (Sum.inr 3520) = Sparse.eval nodeValue3520 (mixedVector B) := by
    change mixedMoment B node3520 node3520Labels = _
    exact sound3520 B hB hF
  have h3605 : mixedVector B (Sum.inr 3605) = Sparse.eval nodeValue3605 (mixedVector B) := by
    change mixedMoment B node3605 node3605Labels = _
    exact sound3605 B hB hF
  have h3756 : mixedVector B (Sum.inr 3756) = Sparse.eval nodeValue3756 (mixedVector B) := by
    change mixedMoment B node3756 node3756Labels = _
    exact sound3756 B hB hF
  have h3773 : mixedVector B (Sum.inr 3773) = Sparse.eval nodeValue3773 (mixedVector B) := by
    change mixedMoment B node3773 node3773Labels = _
    exact sound3773 B hB hF
  have h3792 : mixedVector B (Sum.inr 3792) = Sparse.eval nodeValue3792 (mixedVector B) := by
    change mixedMoment B node3792 node3792Labels = _
    exact sound3792 B hB hF
  have h3798 : mixedVector B (Sum.inr 3798) = Sparse.eval nodeValue3798 (mixedVector B) := by
    change mixedMoment B node3798 node3798Labels = _
    exact sound3798 B hB hF
  have h3815 : mixedVector B (Sum.inr 3815) = Sparse.eval nodeValue3815 (mixedVector B) := by
    change mixedMoment B node3815 node3815Labels = _
    exact sound3815 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3835 : mixedVector B (Sum.inr 3835) = Sparse.eval nodeValue3835 (mixedVector B) := by
    change mixedMoment B node3835 node3835Labels = _
    exact sound3835 B hB hF
  have h3842 : mixedVector B (Sum.inr 3842) = Sparse.eval nodeValue3842 (mixedVector B) := by
    change mixedMoment B node3842 node3842Labels = _
    exact sound3842 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3951 : mixedVector B (Sum.inr 3951) = Sparse.eval nodeValue3951 (mixedVector B) := by
    change mixedMoment B node3951 node3951Labels = _
    exact sound3951 B hB hF
  have h3973 : mixedVector B (Sum.inr 3973) = Sparse.eval nodeValue3973 (mixedVector B) := by
    change mixedMoment B node3973 node3973Labels = _
    exact sound3973 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  simpa only [sourceForm2608, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3406, h3407, h3408, h3414, h3456, h3482, h3520, h3605, h3756, h3773, h3792, h3798, h3815, h3816, h3835, h3842, h3843, h3951, h3973, h3974, reducedSource2081] using sourceEq2608 B hB

theorem rowSound2081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2081 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2081, numericCheck2081, reducedZero2081 B hB hF, mul_zero]

theorem reducedZero2083 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2083 (mixedVector B) = 0 := by
  have h2176 : mixedVector B (Sum.inr 2176) = Sparse.eval nodeValue2176 (mixedVector B) := by
    change mixedMoment B node2176 node2176Labels = _
    exact sound2176 B hB hF
  have h2178 : mixedVector B (Sum.inr 2178) = Sparse.eval nodeValue2178 (mixedVector B) := by
    change mixedMoment B node2178 node2178Labels = _
    exact sound2178 B hB hF
  have h2181 : mixedVector B (Sum.inr 2181) = Sparse.eval nodeValue2181 (mixedVector B) := by
    change mixedMoment B node2181 node2181Labels = _
    exact sound2181 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h3414 : mixedVector B (Sum.inr 3414) = Sparse.eval nodeValue3414 (mixedVector B) := by
    change mixedMoment B node3414 node3414Labels = _
    exact sound3414 B hB hF
  have h3416 : mixedVector B (Sum.inr 3416) = Sparse.eval nodeValue3416 (mixedVector B) := by
    change mixedMoment B node3416 node3416Labels = _
    exact sound3416 B hB hF
  have h3477 : mixedVector B (Sum.inr 3477) = Sparse.eval nodeValue3477 (mixedVector B) := by
    change mixedMoment B node3477 node3477Labels = _
    exact sound3477 B hB hF
  have h3508 : mixedVector B (Sum.inr 3508) = Sparse.eval nodeValue3508 (mixedVector B) := by
    change mixedMoment B node3508 node3508Labels = _
    exact sound3508 B hB hF
  have h3524 : mixedVector B (Sum.inr 3524) = Sparse.eval nodeValue3524 (mixedVector B) := by
    change mixedMoment B node3524 node3524Labels = _
    exact sound3524 B hB hF
  have h3585 : mixedVector B (Sum.inr 3585) = Sparse.eval nodeValue3585 (mixedVector B) := by
    change mixedMoment B node3585 node3585Labels = _
    exact sound3585 B hB hF
  have h3755 : mixedVector B (Sum.inr 3755) = Sparse.eval nodeValue3755 (mixedVector B) := by
    change mixedMoment B node3755 node3755Labels = _
    exact sound3755 B hB hF
  have h3764 : mixedVector B (Sum.inr 3764) = Sparse.eval nodeValue3764 (mixedVector B) := by
    change mixedMoment B node3764 node3764Labels = _
    exact sound3764 B hB hF
  have h3765 : mixedVector B (Sum.inr 3765) = Sparse.eval nodeValue3765 (mixedVector B) := by
    change mixedMoment B node3765 node3765Labels = _
    exact sound3765 B hB hF
  have h3768 : mixedVector B (Sum.inr 3768) = Sparse.eval nodeValue3768 (mixedVector B) := by
    change mixedMoment B node3768 node3768Labels = _
    exact sound3768 B hB hF
  have h3769 : mixedVector B (Sum.inr 3769) = Sparse.eval nodeValue3769 (mixedVector B) := by
    change mixedMoment B node3769 node3769Labels = _
    exact sound3769 B hB hF
  have h3806 : mixedVector B (Sum.inr 3806) = Sparse.eval nodeValue3806 (mixedVector B) := by
    change mixedMoment B node3806 node3806Labels = _
    exact sound3806 B hB hF
  have h3810 : mixedVector B (Sum.inr 3810) = Sparse.eval nodeValue3810 (mixedVector B) := by
    change mixedMoment B node3810 node3810Labels = _
    exact sound3810 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3869 : mixedVector B (Sum.inr 3869) = Sparse.eval nodeValue3869 (mixedVector B) := by
    change mixedMoment B node3869 node3869Labels = _
    exact sound3869 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  simpa only [sourceForm2612, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2176, h2178, h2181, h2213, h3414, h3416, h3477, h3508, h3524, h3585, h3755, h3764, h3765, h3768, h3769, h3806, h3810, h3812, h3869, h3874, h3957, reducedSource2083] using sourceEq2612 B hB

theorem rowSound2083 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2083 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2083, numericCheck2083, reducedZero2083 B hB hF, mul_zero]

theorem reducedZero2087 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2087 (mixedVector B) = 0 := by
  have h3403 : mixedVector B (Sum.inr 3403) = Sparse.eval nodeValue3403 (mixedVector B) := by
    change mixedMoment B node3403 node3403Labels = _
    exact sound3403 B hB hF
  have h3404 : mixedVector B (Sum.inr 3404) = Sparse.eval nodeValue3404 (mixedVector B) := by
    change mixedMoment B node3404 node3404Labels = _
    exact sound3404 B hB hF
  have h3406 : mixedVector B (Sum.inr 3406) = Sparse.eval nodeValue3406 (mixedVector B) := by
    change mixedMoment B node3406 node3406Labels = _
    exact sound3406 B hB hF
  have h3459 : mixedVector B (Sum.inr 3459) = Sparse.eval nodeValue3459 (mixedVector B) := by
    change mixedMoment B node3459 node3459Labels = _
    exact sound3459 B hB hF
  have h3509 : mixedVector B (Sum.inr 3509) = Sparse.eval nodeValue3509 (mixedVector B) := by
    change mixedMoment B node3509 node3509Labels = _
    exact sound3509 B hB hF
  have h3510 : mixedVector B (Sum.inr 3510) = Sparse.eval nodeValue3510 (mixedVector B) := by
    change mixedMoment B node3510 node3510Labels = _
    exact sound3510 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3537 : mixedVector B (Sum.inr 3537) = Sparse.eval nodeValue3537 (mixedVector B) := by
    change mixedMoment B node3537 node3537Labels = _
    exact sound3537 B hB hF
  have h3556 : mixedVector B (Sum.inr 3556) = Sparse.eval nodeValue3556 (mixedVector B) := by
    change mixedMoment B node3556 node3556Labels = _
    exact sound3556 B hB hF
  have h3590 : mixedVector B (Sum.inr 3590) = Sparse.eval nodeValue3590 (mixedVector B) := by
    change mixedMoment B node3590 node3590Labels = _
    exact sound3590 B hB hF
  have h3758 : mixedVector B (Sum.inr 3758) = Sparse.eval nodeValue3758 (mixedVector B) := by
    change mixedMoment B node3758 node3758Labels = _
    exact sound3758 B hB hF
  have h3760 : mixedVector B (Sum.inr 3760) = Sparse.eval nodeValue3760 (mixedVector B) := by
    change mixedMoment B node3760 node3760Labels = _
    exact sound3760 B hB hF
  have h3761 : mixedVector B (Sum.inr 3761) = Sparse.eval nodeValue3761 (mixedVector B) := by
    change mixedMoment B node3761 node3761Labels = _
    exact sound3761 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h3799 : mixedVector B (Sum.inr 3799) = Sparse.eval nodeValue3799 (mixedVector B) := by
    change mixedMoment B node3799 node3799Labels = _
    exact sound3799 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3869 : mixedVector B (Sum.inr 3869) = Sparse.eval nodeValue3869 (mixedVector B) := by
    change mixedMoment B node3869 node3869Labels = _
    exact sound3869 B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  simpa only [sourceForm2619, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3403, h3404, h3406, h3459, h3509, h3510, h3522, h3537, h3556, h3590, h3758, h3760, h3761, h3766, h3770, h3799, h3800, h3807, h3845, h3869, h3953, reducedSource2087] using sourceEq2619 B hB

theorem rowSound2087 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2087 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2087, numericCheck2087, reducedZero2087 B hB hF, mul_zero]

theorem reducedZero2095 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2095 (mixedVector B) = 0 := by
  have h2174 : mixedVector B (Sum.inr 2174) = Sparse.eval nodeValue2174 (mixedVector B) := by
    change mixedMoment B node2174 node2174Labels = _
    exact sound2174 B hB hF
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h2186 : mixedVector B (Sum.inr 2186) = Sparse.eval nodeValue2186 (mixedVector B) := by
    change mixedMoment B node2186 node2186Labels = _
    exact sound2186 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2653 : mixedVector B (Sum.inr 2653) = Sparse.eval nodeValue2653 (mixedVector B) := by
    change mixedMoment B node2653 node2653Labels = _
    exact sound2653 B hB hF
  have h2658 : mixedVector B (Sum.inr 2658) = Sparse.eval nodeValue2658 (mixedVector B) := by
    change mixedMoment B node2658 node2658Labels = _
    exact sound2658 B hB hF
  have h2659 : mixedVector B (Sum.inr 2659) = Sparse.eval nodeValue2659 (mixedVector B) := by
    change mixedMoment B node2659 node2659Labels = _
    exact sound2659 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h2689 : mixedVector B (Sum.inr 2689) = Sparse.eval nodeValue2689 (mixedVector B) := by
    change mixedMoment B node2689 node2689Labels = _
    exact sound2689 B hB hF
  have h2690 : mixedVector B (Sum.inr 2690) = Sparse.eval nodeValue2690 (mixedVector B) := by
    change mixedMoment B node2690 node2690Labels = _
    exact sound2690 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2695 : mixedVector B (Sum.inr 2695) = Sparse.eval nodeValue2695 (mixedVector B) := by
    change mixedMoment B node2695 node2695Labels = _
    exact sound2695 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h2706 : mixedVector B (Sum.inr 2706) = Sparse.eval nodeValue2706 (mixedVector B) := by
    change mixedMoment B node2706 node2706Labels = _
    exact sound2706 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h3025 : mixedVector B (Sum.inr 3025) = Sparse.eval nodeValue3025 (mixedVector B) := by
    change mixedMoment B node3025 node3025Labels = _
    exact sound3025 B hB hF
  have h3059 : mixedVector B (Sum.inr 3059) = Sparse.eval nodeValue3059 (mixedVector B) := by
    change mixedMoment B node3059 node3059Labels = _
    exact sound3059 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  simpa only [sourceForm2630, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2174, h2185, h2186, h2229, h2653, h2658, h2659, h2686, h2689, h2690, h2694, h2695, h2704, h2705, h2706, h2742, h2743, h3025, h3059, h3077, h3078, reducedSource2095] using sourceEq2630 B hB

theorem rowSound2095 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2095 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2095, numericCheck2095, reducedZero2095 B hB hF, mul_zero]

theorem sourceRowsAt2080 : MixedData.sourceRows (2080 : Fin 2425) =
    MixedData.row2080 := by decide +kernel

theorem sourceRowsAt2081 : MixedData.sourceRows (2081 : Fin 2425) =
    MixedData.row2081 := by decide +kernel

theorem sourceRowsAt2082 : MixedData.sourceRows (2082 : Fin 2425) =
    MixedData.row2082 := by decide +kernel

theorem sourceRowsAt2083 : MixedData.sourceRows (2083 : Fin 2425) =
    MixedData.row2083 := by decide +kernel

theorem sourceRowsAt2084 : MixedData.sourceRows (2084 : Fin 2425) =
    MixedData.row2084 := by decide +kernel

theorem sourceRowsAt2085 : MixedData.sourceRows (2085 : Fin 2425) =
    MixedData.row2085 := by decide +kernel

theorem sourceRowsAt2086 : MixedData.sourceRows (2086 : Fin 2425) =
    MixedData.row2086 := by decide +kernel

theorem sourceRowsAt2087 : MixedData.sourceRows (2087 : Fin 2425) =
    MixedData.row2087 := by decide +kernel

theorem sourceRowsAt2088 : MixedData.sourceRows (2088 : Fin 2425) =
    MixedData.row2088 := by decide +kernel

theorem sourceRowsAt2089 : MixedData.sourceRows (2089 : Fin 2425) =
    MixedData.row2089 := by decide +kernel

theorem sourceRowsAt2090 : MixedData.sourceRows (2090 : Fin 2425) =
    MixedData.row2090 := by decide +kernel

theorem sourceRowsAt2091 : MixedData.sourceRows (2091 : Fin 2425) =
    MixedData.row2091 := by decide +kernel

theorem sourceRowsAt2092 : MixedData.sourceRows (2092 : Fin 2425) =
    MixedData.row2092 := by decide +kernel

theorem sourceRowsAt2093 : MixedData.sourceRows (2093 : Fin 2425) =
    MixedData.row2093 := by decide +kernel

theorem sourceRowsAt2094 : MixedData.sourceRows (2094 : Fin 2425) =
    MixedData.row2094 := by decide +kernel

theorem sourceRowsAt2095 : MixedData.sourceRows (2095 : Fin 2425) =
    MixedData.row2095 := by decide +kernel

theorem chunkSound130_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 130) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2080 ∨ k.val = 2081 ∨ k.val = 2082 ∨ k.val = 2083 ∨ k.val = 2084 ∨ k.val = 2085 ∨ k.val = 2086 ∨ k.val = 2087 ∨ k.val = 2088 ∨ k.val = 2089 ∨ k.val = 2090 ∨ k.val = 2091 ∨ k.val = 2092 ∨ k.val = 2093 ∨ k.val = 2094 ∨ k.val = 2095 := by omega
  rcases heq with h2080 | h2081 | h2082 | h2083 | h2084 | h2085 | h2086 | h2087 | h2088 | h2089 | h2090 | h2091 | h2092 | h2093 | h2094 | h2095
  · have he : k = (2080 : Fin 2425) := Fin.ext h2080
    subst k
    rw [sourceRowsAt2080]
    exact rowSound2080_e B hB hF
  · have he : k = (2081 : Fin 2425) := Fin.ext h2081
    subst k
    rw [sourceRowsAt2081]
    exact rowSound2081 B hB hF
  · have he : k = (2082 : Fin 2425) := Fin.ext h2082
    subst k
    rw [sourceRowsAt2082]
    exact rowSound2082_e B hB hF
  · have he : k = (2083 : Fin 2425) := Fin.ext h2083
    subst k
    rw [sourceRowsAt2083]
    exact rowSound2083 B hB hF
  · have he : k = (2084 : Fin 2425) := Fin.ext h2084
    subst k
    rw [sourceRowsAt2084]
    exact rowSound2084_e B hB hF
  · have he : k = (2085 : Fin 2425) := Fin.ext h2085
    subst k
    rw [sourceRowsAt2085]
    exact rowSound2085_e B hB hF
  · have he : k = (2086 : Fin 2425) := Fin.ext h2086
    subst k
    rw [sourceRowsAt2086]
    exact rowSound2086_e B hB hF
  · have he : k = (2087 : Fin 2425) := Fin.ext h2087
    subst k
    rw [sourceRowsAt2087]
    exact rowSound2087 B hB hF
  · have he : k = (2088 : Fin 2425) := Fin.ext h2088
    subst k
    rw [sourceRowsAt2088]
    exact rowSound2088_e B hB hF
  · have he : k = (2089 : Fin 2425) := Fin.ext h2089
    subst k
    rw [sourceRowsAt2089]
    exact rowSound2089_e B hB hF
  · have he : k = (2090 : Fin 2425) := Fin.ext h2090
    subst k
    rw [sourceRowsAt2090]
    exact rowSound2090_e B hB hF
  · have he : k = (2091 : Fin 2425) := Fin.ext h2091
    subst k
    rw [sourceRowsAt2091]
    exact rowSound2091_e B hB hF
  · have he : k = (2092 : Fin 2425) := Fin.ext h2092
    subst k
    rw [sourceRowsAt2092]
    exact rowSound2092_e B hB hF
  · have he : k = (2093 : Fin 2425) := Fin.ext h2093
    subst k
    rw [sourceRowsAt2093]
    exact rowSound2093_e B hB hF
  · have he : k = (2094 : Fin 2425) := Fin.ext h2094
    subst k
    rw [sourceRowsAt2094]
    exact rowSound2094_e B hB hF
  · have he : k = (2095 : Fin 2425) := Fin.ext h2095
    subst k
    rw [sourceRowsAt2095]
    exact rowSound2095 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130_e_oai
