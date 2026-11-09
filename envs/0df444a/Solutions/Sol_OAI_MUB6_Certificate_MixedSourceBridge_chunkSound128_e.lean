-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:46:58.242468+00:00
-- url     : https://prove2.me/submissions/77420d16-623f-44fa-aff4-6ae3facfff35

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2048_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2049_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2050_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2051_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2056_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2059_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2060_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2061_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2062_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2063_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17733 raw17733Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw17733 raw17733Labels = mixedMoment B raw17733step0 raw17733step0Labels := by
      have hz : ∀ j, raw17733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17733step0 = (fun i j => raw17733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17733step0 raw17733; decide +kernel
      have hl : raw17733step0Labels = raw17733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17733 raw17733Labels permutation346 hz
    mixedMoment B raw17733step0 raw17733step0Labels = mixedMoment B raw17733step1 raw17733step1Labels := by
      have ha : raw17733step1 = (fun i j => raw17733step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17733step1 raw17733step0; decide +kernel
      have hl : raw17733step1Labels = raw17733step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17733step0 raw17733step0Labels permutation126 permutation7
    mixedMoment B raw17733step1 raw17733step1Labels = mixedMoment B raw17733step2 raw17733step2Labels := by
      have ha : raw17733step2 = raw17733step1 := by apply Matrix.ext; unfold raw17733step2 raw17733step1; decide +kernel
      have hl : raw17733step1Labels = labelEmbedding1 ∘ raw17733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17733step1 raw17733step1Labels raw17733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical17744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17744 raw17744Labels = mixedMoment B node3951 node3951Labels := by
  calc
    mixedMoment B raw17744 raw17744Labels = mixedMoment B raw17744step0 raw17744step0Labels := by
      have ha : raw17744step0 = (fun i j => raw17744 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17744step0 raw17744; decide +kernel
      have hl : raw17744step0Labels = raw17744Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17744 raw17744Labels permutation583 permutation7
    mixedMoment B raw17744step0 raw17744step0Labels = mixedMoment B raw17744step1 raw17744step1Labels := by
      have ha : raw17744step1 = raw17744step0 := by apply Matrix.ext; unfold raw17744step1 raw17744step0; decide +kernel
      have hl : raw17744step0Labels = labelEmbedding1 ∘ raw17744step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17744step0 raw17744step0Labels raw17744step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3951 node3951Labels := by rfl

theorem canonical17749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17749 raw17749Labels = mixedMoment B node3960 node3960Labels := by
  calc
    mixedMoment B raw17749 raw17749Labels = mixedMoment B raw17749step0 raw17749step0Labels := by
      have hz : ∀ j, raw17749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17749step0 = (fun i j => raw17749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17749step0 raw17749; decide +kernel
      have hl : raw17749step0Labels = raw17749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17749 raw17749Labels permutation346 hz
    mixedMoment B raw17749step0 raw17749step0Labels = mixedMoment B raw17749step1 raw17749step1Labels := by
      have ha : raw17749step1 = (fun i j => raw17749step0 (permutation102 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17749step1 raw17749step0; decide +kernel
      have hl : raw17749step1Labels = raw17749step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17749step0 raw17749step0Labels permutation102 permutation5
    mixedMoment B raw17749step1 raw17749step1Labels = mixedMoment B raw17749step2 raw17749step2Labels := by
      have ha : raw17749step2 = raw17749step1 := by apply Matrix.ext; unfold raw17749step2 raw17749step1; decide +kernel
      have hl : raw17749step1Labels = labelEmbedding1 ∘ raw17749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17749step1 raw17749step1Labels raw17749step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3960 node3960Labels := by rfl

theorem canonical17753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17753 raw17753Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw17753 raw17753Labels = mixedMoment B raw17753step0 raw17753step0Labels := by
      have hz : ∀ j, raw17753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17753step0 = (fun i j => raw17753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17753step0 raw17753; decide +kernel
      have hl : raw17753step0Labels = raw17753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17753 raw17753Labels permutation346 hz
    mixedMoment B raw17753step0 raw17753step0Labels = mixedMoment B raw17753step1 raw17753step1Labels := by
      have ha : raw17753step1 = (fun i j => raw17753step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17753step1 raw17753step0; decide +kernel
      have hl : raw17753step1Labels = raw17753step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17753step0 raw17753step0Labels permutation34 permutation5
    mixedMoment B raw17753step1 raw17753step1Labels = mixedMoment B raw17753step2 raw17753step2Labels := by
      have ha : raw17753step2 = -raw17753step1 := by apply Matrix.ext; change ∀ i j, raw17753step2 i j = -(raw17753step1 i j); unfold raw17753step2 raw17753step1; decide +kernel
      have hl : raw17753step2Labels = raw17753step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17753step2 raw17753step2Labels = mixedMoment B raw17753step3 raw17753step3Labels := by
      have ha : raw17753step3 = raw17753step2 := by apply Matrix.ext; unfold raw17753step3 raw17753step2; decide +kernel
      have hl : raw17753step2Labels = labelEmbedding1 ∘ raw17753step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17753step2 raw17753step2Labels raw17753step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical17755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17755 raw17755Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw17755 raw17755Labels = mixedMoment B raw17755step0 raw17755step0Labels := by
      have ha : raw17755step0 = (fun i j => raw17755 (permutation584 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17755step0 raw17755; decide +kernel
      have hl : raw17755step0Labels = raw17755Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17755 raw17755Labels permutation584 permutation7
    mixedMoment B raw17755step0 raw17755step0Labels = mixedMoment B raw17755step1 raw17755step1Labels := by
      have ha : raw17755step1 = raw17755step0 := by apply Matrix.ext; unfold raw17755step1 raw17755step0; decide +kernel
      have hl : raw17755step0Labels = labelEmbedding1 ∘ raw17755step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17755step0 raw17755step0Labels raw17755step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

theorem canonical17756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17756 raw17756Labels = mixedMoment B node3774 node3774Labels := by
  calc
    mixedMoment B raw17756 raw17756Labels = mixedMoment B raw17756step0 raw17756step0Labels := by
      have hz : ∀ j, raw17756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17756step0 = (fun i j => raw17756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17756step0 raw17756; decide +kernel
      have hl : raw17756step0Labels = raw17756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17756 raw17756Labels permutation346 hz
    mixedMoment B raw17756step0 raw17756step0Labels = mixedMoment B raw17756step1 raw17756step1Labels := by
      have ha : raw17756step1 = (fun i j => raw17756step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17756step1 raw17756step0; decide +kernel
      have hl : raw17756step1Labels = raw17756step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17756step0 raw17756step0Labels permutation125 permutation7
    mixedMoment B raw17756step1 raw17756step1Labels = mixedMoment B raw17756step2 raw17756step2Labels := by
      have ha : raw17756step2 = raw17756step1 := by apply Matrix.ext; unfold raw17756step2 raw17756step1; decide +kernel
      have hl : raw17756step1Labels = labelEmbedding1 ∘ raw17756step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17756step1 raw17756step1Labels raw17756step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3774 node3774Labels := by rfl

theorem canonical17757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17757 raw17757Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw17757 raw17757Labels = mixedMoment B raw17757step0 raw17757step0Labels := by
      have hz : ∀ j, raw17757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17757step0 = (fun i j => raw17757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17757step0 raw17757; decide +kernel
      have hl : raw17757step0Labels = raw17757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17757 raw17757Labels permutation346 hz
    mixedMoment B raw17757step0 raw17757step0Labels = mixedMoment B raw17757step1 raw17757step1Labels := by
      have ha : raw17757step1 = (fun i j => raw17757step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17757step1 raw17757step0; decide +kernel
      have hl : raw17757step1Labels = raw17757step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17757step0 raw17757step0Labels permutation127 permutation7
    mixedMoment B raw17757step1 raw17757step1Labels = mixedMoment B raw17757step2 raw17757step2Labels := by
      have ha : raw17757step2 = raw17757step1 := by apply Matrix.ext; unfold raw17757step2 raw17757step1; decide +kernel
      have hl : raw17757step1Labels = labelEmbedding1 ∘ raw17757step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17757step1 raw17757step1Labels raw17757step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical17759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17759 raw17759Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw17759 raw17759Labels = mixedMoment B raw17759step0 raw17759step0Labels := by
      have hz : ∀ j, raw17759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17759step0 = (fun i j => raw17759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17759step0 raw17759; decide +kernel
      have hl : raw17759step0Labels = raw17759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17759 raw17759Labels permutation346 hz
    mixedMoment B raw17759step0 raw17759step0Labels = mixedMoment B raw17759step1 raw17759step1Labels := by
      have ha : raw17759step1 = (fun i j => raw17759step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17759step1 raw17759step0; decide +kernel
      have hl : raw17759step1Labels = raw17759step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17759step0 raw17759step0Labels permutation144 permutation5
    mixedMoment B raw17759step1 raw17759step1Labels = mixedMoment B raw17759step2 raw17759step2Labels := by
      have ha : raw17759step2 = raw17759step1 := by apply Matrix.ext; unfold raw17759step2 raw17759step1; decide +kernel
      have hl : raw17759step1Labels = labelEmbedding1 ∘ raw17759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17759step1 raw17759step1Labels raw17759step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

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

theorem canonical18008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18008 raw18008Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw18008 raw18008Labels = mixedMoment B raw18008step0 raw18008step0Labels := by
      have hz : ∀ j, raw18008 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18008step0 = (fun i j => raw18008 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18008step0 raw18008; decide +kernel
      have hl : raw18008step0Labels = raw18008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18008 raw18008Labels permutation434 hz
    mixedMoment B raw18008step0 raw18008step0Labels = mixedMoment B raw18008step1 raw18008step1Labels := by
      have hz : ∀ j, raw18008step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18008step1 = (fun i j => raw18008step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18008step1 raw18008step0; decide +kernel
      have hl : raw18008step1Labels = raw18008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18008step0 raw18008step0Labels permutation80 hz
    mixedMoment B raw18008step1 raw18008step1Labels = mixedMoment B raw18008step2 raw18008step2Labels := by
      have ha : raw18008step2 = (fun i j => raw18008step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18008step2 raw18008step1; decide +kernel
      have hl : raw18008step2Labels = raw18008step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18008step1 raw18008step1Labels permutation15 permutation7
    mixedMoment B raw18008step2 raw18008step2Labels = mixedMoment B raw18008step3 raw18008step3Labels := by
      have ha : raw18008step3 = -raw18008step2 := by apply Matrix.ext; change ∀ i j, raw18008step3 i j = -(raw18008step2 i j); unfold raw18008step3 raw18008step2; decide +kernel
      have hl : raw18008step3Labels = raw18008step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18008step3 raw18008step3Labels = mixedMoment B raw18008step4 raw18008step4Labels := by
      have ha : raw18008step4 = raw18008step3 := by apply Matrix.ext; unfold raw18008step4 raw18008step3; decide +kernel
      have hl : raw18008step3Labels = labelEmbedding1 ∘ raw18008step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18008step3 raw18008step3Labels raw18008step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

theorem canonical18019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18019 raw18019Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw18019 raw18019Labels = mixedMoment B raw18019step0 raw18019step0Labels := by
      have hz : ∀ j, raw18019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18019step0 = (fun i j => raw18019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18019step0 raw18019; decide +kernel
      have hl : raw18019step0Labels = raw18019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18019 raw18019Labels permutation434 hz
    mixedMoment B raw18019step0 raw18019step0Labels = mixedMoment B raw18019step1 raw18019step1Labels := by
      have ha : raw18019step1 = (fun i j => raw18019step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18019step1 raw18019step0; decide +kernel
      have hl : raw18019step1Labels = raw18019step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18019step0 raw18019step0Labels permutation57 permutation7
    mixedMoment B raw18019step1 raw18019step1Labels = mixedMoment B raw18019step2 raw18019step2Labels := by
      have ha : raw18019step2 = -raw18019step1 := by apply Matrix.ext; change ∀ i j, raw18019step2 i j = -(raw18019step1 i j); unfold raw18019step2 raw18019step1; decide +kernel
      have hl : raw18019step2Labels = raw18019step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18019step2 raw18019step2Labels = mixedMoment B raw18019step3 raw18019step3Labels := by
      have ha : raw18019step3 = raw18019step2 := by apply Matrix.ext; unfold raw18019step3 raw18019step2; decide +kernel
      have hl : raw18019step2Labels = labelEmbedding1 ∘ raw18019step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18019step2 raw18019step2Labels raw18019step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

theorem canonical18024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18024 raw18024Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw18024 raw18024Labels = mixedMoment B raw18024step0 raw18024step0Labels := by
      have hz : ∀ j, raw18024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18024step0 = (fun i j => raw18024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18024step0 raw18024; decide +kernel
      have hl : raw18024step0Labels = raw18024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18024 raw18024Labels permutation346 hz
    mixedMoment B raw18024step0 raw18024step0Labels = mixedMoment B raw18024step1 raw18024step1Labels := by
      have ha : raw18024step1 = (fun i j => raw18024step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18024step1 raw18024step0; decide +kernel
      have hl : raw18024step1Labels = raw18024step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18024step0 raw18024step0Labels permutation57 permutation7
    mixedMoment B raw18024step1 raw18024step1Labels = mixedMoment B raw18024step2 raw18024step2Labels := by
      have ha : raw18024step2 = -raw18024step1 := by apply Matrix.ext; change ∀ i j, raw18024step2 i j = -(raw18024step1 i j); unfold raw18024step2 raw18024step1; decide +kernel
      have hl : raw18024step2Labels = raw18024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18024step2 raw18024step2Labels = mixedMoment B raw18024step3 raw18024step3Labels := by
      have ha : raw18024step3 = raw18024step2 := by apply Matrix.ext; unfold raw18024step3 raw18024step2; decide +kernel
      have hl : raw18024step2Labels = labelEmbedding1 ∘ raw18024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18024step2 raw18024step2Labels raw18024step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

theorem canonical18028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18028 raw18028Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw18028 raw18028Labels = mixedMoment B raw18028step0 raw18028step0Labels := by
      have hz : ∀ j, raw18028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18028step0 = (fun i j => raw18028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18028step0 raw18028; decide +kernel
      have hl : raw18028step0Labels = raw18028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18028 raw18028Labels permutation434 hz
    mixedMoment B raw18028step0 raw18028step0Labels = mixedMoment B raw18028step1 raw18028step1Labels := by
      have hz : ∀ j, raw18028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18028step1 = (fun i j => raw18028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18028step1 raw18028step0; decide +kernel
      have hl : raw18028step1Labels = raw18028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18028step0 raw18028step0Labels permutation80 hz
    mixedMoment B raw18028step1 raw18028step1Labels = mixedMoment B raw18028step2 raw18028step2Labels := by
      have ha : raw18028step2 = (fun i j => raw18028step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18028step2 raw18028step1; decide +kernel
      have hl : raw18028step2Labels = raw18028step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18028step1 raw18028step1Labels permutation10 permutation5
    mixedMoment B raw18028step2 raw18028step2Labels = mixedMoment B raw18028step3 raw18028step3Labels := by
      have ha : raw18028step3 = -raw18028step2 := by apply Matrix.ext; change ∀ i j, raw18028step3 i j = -(raw18028step2 i j); unfold raw18028step3 raw18028step2; decide +kernel
      have hl : raw18028step3Labels = raw18028step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18028step3 raw18028step3Labels = mixedMoment B raw18028step4 raw18028step4Labels := by
      have ha : raw18028step4 = raw18028step3 := by apply Matrix.ext; unfold raw18028step4 raw18028step3; decide +kernel
      have hl : raw18028step3Labels = labelEmbedding1 ∘ raw18028step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18028step3 raw18028step3Labels raw18028step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

theorem canonical18030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18030 raw18030Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw18030 raw18030Labels = mixedMoment B raw18030step0 raw18030step0Labels := by
      have hz : ∀ j, raw18030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18030step0 = (fun i j => raw18030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18030step0 raw18030; decide +kernel
      have hl : raw18030step0Labels = raw18030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18030 raw18030Labels permutation434 hz
    mixedMoment B raw18030step0 raw18030step0Labels = mixedMoment B raw18030step1 raw18030step1Labels := by
      have ha : raw18030step1 = (fun i j => raw18030step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18030step1 raw18030step0; decide +kernel
      have hl : raw18030step1Labels = raw18030step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18030step0 raw18030step0Labels permutation126 permutation7
    mixedMoment B raw18030step1 raw18030step1Labels = mixedMoment B raw18030step2 raw18030step2Labels := by
      have ha : raw18030step2 = raw18030step1 := by apply Matrix.ext; unfold raw18030step2 raw18030step1; decide +kernel
      have hl : raw18030step1Labels = labelEmbedding1 ∘ raw18030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18030step1 raw18030step1Labels raw18030step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

theorem canonical18031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18031 raw18031Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw18031 raw18031Labels = mixedMoment B raw18031step0 raw18031step0Labels := by
      have hz : ∀ j, raw18031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18031step0 = (fun i j => raw18031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18031step0 raw18031; decide +kernel
      have hl : raw18031step0Labels = raw18031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18031 raw18031Labels permutation346 hz
    mixedMoment B raw18031step0 raw18031step0Labels = mixedMoment B raw18031step1 raw18031step1Labels := by
      have ha : raw18031step1 = (fun i j => raw18031step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18031step1 raw18031step0; decide +kernel
      have hl : raw18031step1Labels = raw18031step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18031step0 raw18031step0Labels permutation126 permutation7
    mixedMoment B raw18031step1 raw18031step1Labels = mixedMoment B raw18031step2 raw18031step2Labels := by
      have ha : raw18031step2 = raw18031step1 := by apply Matrix.ext; unfold raw18031step2 raw18031step1; decide +kernel
      have hl : raw18031step1Labels = labelEmbedding1 ∘ raw18031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18031step1 raw18031step1Labels raw18031step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

theorem canonical18032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18032 raw18032Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw18032 raw18032Labels = mixedMoment B raw18032step0 raw18032step0Labels := by
      have hz : ∀ j, raw18032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18032step0 = (fun i j => raw18032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18032step0 raw18032; decide +kernel
      have hl : raw18032step0Labels = raw18032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18032 raw18032Labels permutation434 hz
    mixedMoment B raw18032step0 raw18032step0Labels = mixedMoment B raw18032step1 raw18032step1Labels := by
      have hz : ∀ j, raw18032step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18032step1 = (fun i j => raw18032step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18032step1 raw18032step0; decide +kernel
      have hl : raw18032step1Labels = raw18032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18032step0 raw18032step0Labels permutation80 hz
    mixedMoment B raw18032step1 raw18032step1Labels = mixedMoment B raw18032step2 raw18032step2Labels := by
      have ha : raw18032step2 = (fun i j => raw18032step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18032step2 raw18032step1; decide +kernel
      have hl : raw18032step2Labels = raw18032step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18032step1 raw18032step1Labels permutation24 permutation7
    mixedMoment B raw18032step2 raw18032step2Labels = mixedMoment B raw18032step3 raw18032step3Labels := by
      have ha : raw18032step3 = raw18032step2 := by apply Matrix.ext; unfold raw18032step3 raw18032step2; decide +kernel
      have hl : raw18032step2Labels = labelEmbedding1 ∘ raw18032step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18032step2 raw18032step2Labels raw18032step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

theorem canonical18034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18034 raw18034Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw18034 raw18034Labels = mixedMoment B raw18034step0 raw18034step0Labels := by
      have hz : ∀ j, raw18034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18034step0 = (fun i j => raw18034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18034step0 raw18034; decide +kernel
      have hl : raw18034step0Labels = raw18034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18034 raw18034Labels permutation434 hz
    mixedMoment B raw18034step0 raw18034step0Labels = mixedMoment B raw18034step1 raw18034step1Labels := by
      have hz : ∀ j, raw18034step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18034step1 = (fun i j => raw18034step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18034step1 raw18034step0; decide +kernel
      have hl : raw18034step1Labels = raw18034step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18034step0 raw18034step0Labels permutation80 hz
    mixedMoment B raw18034step1 raw18034step1Labels = mixedMoment B raw18034step2 raw18034step2Labels := by
      have ha : raw18034step2 = (fun i j => raw18034step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18034step2 raw18034step1; decide +kernel
      have hl : raw18034step2Labels = raw18034step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18034step1 raw18034step1Labels permutation29 permutation5
    mixedMoment B raw18034step2 raw18034step2Labels = mixedMoment B raw18034step3 raw18034step3Labels := by
      have ha : raw18034step3 = raw18034step2 := by apply Matrix.ext; unfold raw18034step3 raw18034step2; decide +kernel
      have hl : raw18034step2Labels = labelEmbedding1 ∘ raw18034step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18034step2 raw18034step2Labels raw18034step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27823 raw27823Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw27823 raw27823Labels = mixedMoment B raw27823step0 raw27823step0Labels := by
      have hz : ∀ j, raw27823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27823step0 = (fun i j => raw27823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27823step0 raw27823; decide +kernel
      have hl : raw27823step0Labels = raw27823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27823 raw27823Labels permutation346 hz
    mixedMoment B raw27823step0 raw27823step0Labels = mixedMoment B raw27823step1 raw27823step1Labels := by
      have ha : raw27823step1 = (fun i j => raw27823step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27823step1 raw27823step0; decide +kernel
      have hl : raw27823step1Labels = raw27823step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27823step0 raw27823step0Labels permutation122 permutation0
    mixedMoment B raw27823step1 raw27823step1Labels = mixedMoment B raw27823step2 raw27823step2Labels := by
      have ha : raw27823step2 = -raw27823step1 := by apply Matrix.ext; change ∀ i j, raw27823step2 i j = -(raw27823step1 i j); unfold raw27823step2 raw27823step1; decide +kernel
      have hl : raw27823step2Labels = raw27823step1Labels := by decide +kernel
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical232
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29787 raw29787Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw29787 raw29787Labels = mixedMoment B raw29787step0 raw29787step0Labels := by
      have hz : ∀ j, raw29787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29787step0 = (fun i j => raw29787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29787step0 raw29787; decide +kernel
      have hl : raw29787step0Labels = raw29787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29787 raw29787Labels permutation346 hz
    mixedMoment B raw29787step0 raw29787step0Labels = mixedMoment B raw29787step1 raw29787step1Labels := by
      have ha : raw29787step1 = (fun i j => raw29787step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29787step1 raw29787step0; decide +kernel
      have hl : raw29787step1Labels = raw29787step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29787step0 raw29787step0Labels permutation127 permutation7
    mixedMoment B raw29787step1 raw29787step1Labels = mixedMoment B raw29787step2 raw29787step2Labels := by
      have ha : raw29787step2 = raw29787step1 := by apply Matrix.ext; unfold raw29787step2 raw29787step1; decide +kernel
      have hl : raw29787step1Labels = labelEmbedding1 ∘ raw29787step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29787step1 raw29787step1Labels raw29787step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical29793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29793 raw29793Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw29793 raw29793Labels = mixedMoment B raw29793step0 raw29793step0Labels := by
      have ha : raw29793step0 = (fun i j => raw29793 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29793step0 raw29793; decide +kernel
      have hl : raw29793step0Labels = raw29793Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29793 raw29793Labels permutation166 permutation5
    mixedMoment B raw29793step0 raw29793step0Labels = mixedMoment B raw29793step1 raw29793step1Labels := by
      have ha : raw29793step1 = -raw29793step0 := by apply Matrix.ext; change ∀ i j, raw29793step1 i j = -(raw29793step0 i j); unfold raw29793step1 raw29793step0; decide +kernel
      have hl : raw29793step1Labels = raw29793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29793step1 raw29793step1Labels = mixedMoment B raw29793step2 raw29793step2Labels := by
      have ha : raw29793step2 = raw29793step1 := by apply Matrix.ext; unfold raw29793step2 raw29793step1; decide +kernel
      have hl : raw29793step1Labels = labelEmbedding1 ∘ raw29793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29793step1 raw29793step1Labels raw29793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

theorem canonical29797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29797 raw29797Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw29797 raw29797Labels = mixedMoment B raw29797step0 raw29797step0Labels := by
      have hz : ∀ j, raw29797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29797step0 = (fun i j => raw29797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29797step0 raw29797; decide +kernel
      have hl : raw29797step0Labels = raw29797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29797 raw29797Labels permutation346 hz
    mixedMoment B raw29797step0 raw29797step0Labels = mixedMoment B raw29797step1 raw29797step1Labels := by
      have ha : raw29797step1 = (fun i j => raw29797step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29797step1 raw29797step0; decide +kernel
      have hl : raw29797step1Labels = raw29797step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29797step0 raw29797step0Labels permutation35 permutation5
    mixedMoment B raw29797step1 raw29797step1Labels = mixedMoment B raw29797step2 raw29797step2Labels := by
      have ha : raw29797step2 = -raw29797step1 := by apply Matrix.ext; change ∀ i j, raw29797step2 i j = -(raw29797step1 i j); unfold raw29797step2 raw29797step1; decide +kernel
      have hl : raw29797step2Labels = raw29797step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29797step2 raw29797step2Labels = mixedMoment B raw29797step3 raw29797step3Labels := by
      have ha : raw29797step3 = raw29797step2 := by apply Matrix.ext; unfold raw29797step3 raw29797step2; decide +kernel
      have hl : raw29797step2Labels = labelEmbedding1 ∘ raw29797step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29797step2 raw29797step2Labels raw29797step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

theorem canonical29801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29801 raw29801Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw29801 raw29801Labels = mixedMoment B raw29801step0 raw29801step0Labels := by
      have hz : ∀ j, raw29801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29801step0 = (fun i j => raw29801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29801step0 raw29801; decide +kernel
      have hl : raw29801step0Labels = raw29801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29801 raw29801Labels permutation346 hz
    mixedMoment B raw29801step0 raw29801step0Labels = mixedMoment B raw29801step1 raw29801step1Labels := by
      have ha : raw29801step1 = (fun i j => raw29801step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29801step1 raw29801step0; decide +kernel
      have hl : raw29801step1Labels = raw29801step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29801step0 raw29801step0Labels permutation33 permutation5
    mixedMoment B raw29801step1 raw29801step1Labels = mixedMoment B raw29801step2 raw29801step2Labels := by
      have ha : raw29801step2 = -raw29801step1 := by apply Matrix.ext; change ∀ i j, raw29801step2 i j = -(raw29801step1 i j); unfold raw29801step2 raw29801step1; decide +kernel
      have hl : raw29801step2Labels = raw29801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29801step2 raw29801step2Labels = mixedMoment B raw29801step3 raw29801step3Labels := by
      have ha : raw29801step3 = raw29801step2 := by apply Matrix.ext; unfold raw29801step3 raw29801step2; decide +kernel
      have hl : raw29801step2Labels = labelEmbedding1 ∘ raw29801step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29801step2 raw29801step2Labels raw29801step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

theorem canonical29806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29806 raw29806Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw29806 raw29806Labels = mixedMoment B raw29806step0 raw29806step0Labels := by
      have hz : ∀ j, raw29806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29806step0 = (fun i j => raw29806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29806step0 raw29806; decide +kernel
      have hl : raw29806step0Labels = raw29806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29806 raw29806Labels permutation346 hz
    mixedMoment B raw29806step0 raw29806step0Labels = mixedMoment B raw29806step1 raw29806step1Labels := by
      have ha : raw29806step1 = (fun i j => raw29806step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29806step1 raw29806step0; decide +kernel
      have hl : raw29806step1Labels = raw29806step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29806step0 raw29806step0Labels permutation34 permutation5
    mixedMoment B raw29806step1 raw29806step1Labels = mixedMoment B raw29806step2 raw29806step2Labels := by
      have ha : raw29806step2 = -raw29806step1 := by apply Matrix.ext; change ∀ i j, raw29806step2 i j = -(raw29806step1 i j); unfold raw29806step2 raw29806step1; decide +kernel
      have hl : raw29806step2Labels = raw29806step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29806step2 raw29806step2Labels = mixedMoment B raw29806step3 raw29806step3Labels := by
      have ha : raw29806step3 = raw29806step2 := by apply Matrix.ext; unfold raw29806step3 raw29806step2; decide +kernel
      have hl : raw29806step2Labels = labelEmbedding1 ∘ raw29806step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29806step2 raw29806step2Labels raw29806step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

theorem canonical29809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29809 raw29809Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw29809 raw29809Labels = mixedMoment B raw29809step0 raw29809step0Labels := by
      have hz : ∀ j, raw29809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29809step0 = (fun i j => raw29809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29809step0 raw29809; decide +kernel
      have hl : raw29809step0Labels = raw29809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29809 raw29809Labels permutation346 hz
    mixedMoment B raw29809step0 raw29809step0Labels = mixedMoment B raw29809step1 raw29809step1Labels := by
      have ha : raw29809step1 = (fun i j => raw29809step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29809step1 raw29809step0; decide +kernel
      have hl : raw29809step1Labels = raw29809step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29809step0 raw29809step0Labels permutation126 permutation2
    mixedMoment B raw29809step1 raw29809step1Labels = mixedMoment B raw29809step2 raw29809step2Labels := by
      have ha : raw29809step2 = -raw29809step1 := by apply Matrix.ext; change ∀ i j, raw29809step2 i j = -(raw29809step1 i j); unfold raw29809step2 raw29809step1; decide +kernel
      have hl : raw29809step2Labels = raw29809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3694 node3694Labels := by rfl

theorem canonical29810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29810 raw29810Labels = mixedMoment B node2822 node2822Labels := by
  calc
    mixedMoment B raw29810 raw29810Labels = mixedMoment B raw29810step0 raw29810step0Labels := by
      have ha : raw29810step0 = (fun i j => raw29810 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29810step0 raw29810; decide +kernel
      have hl : raw29810step0Labels = raw29810Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29810 raw29810Labels permutation159 permutation2
    _ = mixedMoment B node2822 node2822Labels := by rfl

theorem canonical29811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29811 raw29811Labels = mixedMoment B node2827 node2827Labels := by
  calc
    mixedMoment B raw29811 raw29811Labels = mixedMoment B raw29811step0 raw29811step0Labels := by
      have hz : ∀ j, raw29811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29811step0 = (fun i j => raw29811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29811step0 raw29811; decide +kernel
      have hl : raw29811step0Labels = raw29811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29811 raw29811Labels permutation346 hz
    mixedMoment B raw29811step0 raw29811step0Labels = mixedMoment B raw29811step1 raw29811step1Labels := by
      have ha : raw29811step1 = (fun i j => raw29811step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29811step1 raw29811step0; decide +kernel
      have hl : raw29811step1Labels = raw29811step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29811step0 raw29811step0Labels permutation33 permutation2
    _ = mixedMoment B node2827 node2827Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical234
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30001 raw30001Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw30001 raw30001Labels = mixedMoment B raw30001step0 raw30001step0Labels := by
      have hz : ∀ j, raw30001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30001step0 = (fun i j => raw30001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30001step0 raw30001; decide +kernel
      have hl : raw30001step0Labels = raw30001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30001 raw30001Labels permutation434 hz
    mixedMoment B raw30001step0 raw30001step0Labels = mixedMoment B raw30001step1 raw30001step1Labels := by
      have hz : ∀ j, raw30001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30001step1 = (fun i j => raw30001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30001step1 raw30001step0; decide +kernel
      have hl : raw30001step1Labels = raw30001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30001step0 raw30001step0Labels permutation80 hz
    mixedMoment B raw30001step1 raw30001step1Labels = mixedMoment B raw30001step2 raw30001step2Labels := by
      have ha : raw30001step2 = (fun i j => raw30001step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30001step2 raw30001step1; decide +kernel
      have hl : raw30001step2Labels = raw30001step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30001step1 raw30001step1Labels permutation24 permutation7
    mixedMoment B raw30001step2 raw30001step2Labels = mixedMoment B raw30001step3 raw30001step3Labels := by
      have ha : raw30001step3 = raw30001step2 := by apply Matrix.ext; unfold raw30001step3 raw30001step2; decide +kernel
      have hl : raw30001step2Labels = labelEmbedding1 ∘ raw30001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30001step2 raw30001step2Labels raw30001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3963 node3963Labels := by rfl

theorem canonical30007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30007 raw30007Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw30007 raw30007Labels = mixedMoment B raw30007step0 raw30007step0Labels := by
      have hz : ∀ j, raw30007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30007step0 = (fun i j => raw30007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30007step0 raw30007; decide +kernel
      have hl : raw30007step0Labels = raw30007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30007 raw30007Labels permutation434 hz
    mixedMoment B raw30007step0 raw30007step0Labels = mixedMoment B raw30007step1 raw30007step1Labels := by
      have ha : raw30007step1 = (fun i j => raw30007step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30007step1 raw30007step0; decide +kernel
      have hl : raw30007step1Labels = raw30007step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30007step0 raw30007step0Labels permutation34 permutation5
    mixedMoment B raw30007step1 raw30007step1Labels = mixedMoment B raw30007step2 raw30007step2Labels := by
      have ha : raw30007step2 = -raw30007step1 := by apply Matrix.ext; change ∀ i j, raw30007step2 i j = -(raw30007step1 i j); unfold raw30007step2 raw30007step1; decide +kernel
      have hl : raw30007step2Labels = raw30007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30007step2 raw30007step2Labels = mixedMoment B raw30007step3 raw30007step3Labels := by
      have ha : raw30007step3 = raw30007step2 := by apply Matrix.ext; unfold raw30007step3 raw30007step2; decide +kernel
      have hl : raw30007step2Labels = labelEmbedding1 ∘ raw30007step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30007step2 raw30007step2Labels raw30007step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

theorem canonical30011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30011 raw30011Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw30011 raw30011Labels = mixedMoment B raw30011step0 raw30011step0Labels := by
      have hz : ∀ j, raw30011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30011step0 = (fun i j => raw30011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30011step0 raw30011; decide +kernel
      have hl : raw30011step0Labels = raw30011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30011 raw30011Labels permutation346 hz
    mixedMoment B raw30011step0 raw30011step0Labels = mixedMoment B raw30011step1 raw30011step1Labels := by
      have ha : raw30011step1 = (fun i j => raw30011step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30011step1 raw30011step0; decide +kernel
      have hl : raw30011step1Labels = raw30011step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30011step0 raw30011step0Labels permutation34 permutation5
    mixedMoment B raw30011step1 raw30011step1Labels = mixedMoment B raw30011step2 raw30011step2Labels := by
      have ha : raw30011step2 = -raw30011step1 := by apply Matrix.ext; change ∀ i j, raw30011step2 i j = -(raw30011step1 i j); unfold raw30011step2 raw30011step1; decide +kernel
      have hl : raw30011step2Labels = raw30011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30011step2 raw30011step2Labels = mixedMoment B raw30011step3 raw30011step3Labels := by
      have ha : raw30011step3 = raw30011step2 := by apply Matrix.ext; unfold raw30011step3 raw30011step2; decide +kernel
      have hl : raw30011step2Labels = labelEmbedding1 ∘ raw30011step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30011step2 raw30011step2Labels raw30011step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

theorem canonical30015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30015 raw30015Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw30015 raw30015Labels = mixedMoment B raw30015step0 raw30015step0Labels := by
      have hz : ∀ j, raw30015 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30015step0 = (fun i j => raw30015 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30015step0 raw30015; decide +kernel
      have hl : raw30015step0Labels = raw30015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30015 raw30015Labels permutation434 hz
    mixedMoment B raw30015step0 raw30015step0Labels = mixedMoment B raw30015step1 raw30015step1Labels := by
      have hz : ∀ j, raw30015step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30015step1 = (fun i j => raw30015step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30015step1 raw30015step0; decide +kernel
      have hl : raw30015step1Labels = raw30015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30015step0 raw30015step0Labels permutation80 hz
    mixedMoment B raw30015step1 raw30015step1Labels = mixedMoment B raw30015step2 raw30015step2Labels := by
      have ha : raw30015step2 = (fun i j => raw30015step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30015step2 raw30015step1; decide +kernel
      have hl : raw30015step2Labels = raw30015step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30015step1 raw30015step1Labels permutation24 permutation7
    mixedMoment B raw30015step2 raw30015step2Labels = mixedMoment B raw30015step3 raw30015step3Labels := by
      have ha : raw30015step3 = raw30015step2 := by apply Matrix.ext; unfold raw30015step3 raw30015step2; decide +kernel
      have hl : raw30015step2Labels = labelEmbedding1 ∘ raw30015step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30015step2 raw30015step2Labels raw30015step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3423 node3423Labels := by rfl

theorem canonical30020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30020 raw30020Labels = mixedMoment B node3596 node3596Labels := by
  calc
    mixedMoment B raw30020 raw30020Labels = mixedMoment B raw30020step0 raw30020step0Labels := by
      have hz : ∀ j, raw30020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30020step0 = (fun i j => raw30020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30020step0 raw30020; decide +kernel
      have hl : raw30020step0Labels = raw30020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30020 raw30020Labels permutation434 hz
    mixedMoment B raw30020step0 raw30020step0Labels = mixedMoment B raw30020step1 raw30020step1Labels := by
      have hz : ∀ j, raw30020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30020step1 = (fun i j => raw30020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30020step1 raw30020step0; decide +kernel
      have hl : raw30020step1Labels = raw30020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30020step0 raw30020step0Labels permutation80 hz
    mixedMoment B raw30020step1 raw30020step1Labels = mixedMoment B raw30020step2 raw30020step2Labels := by
      have ha : raw30020step2 = (fun i j => raw30020step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30020step2 raw30020step1; decide +kernel
      have hl : raw30020step2Labels = raw30020step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30020step1 raw30020step1Labels permutation31 permutation5
    mixedMoment B raw30020step2 raw30020step2Labels = mixedMoment B raw30020step3 raw30020step3Labels := by
      have ha : raw30020step3 = raw30020step2 := by apply Matrix.ext; unfold raw30020step3 raw30020step2; decide +kernel
      have hl : raw30020step2Labels = labelEmbedding1 ∘ raw30020step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30020step2 raw30020step2Labels raw30020step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3596 node3596Labels := by rfl

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

theorem canonical3444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3444 raw3444Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3444 raw3444Labels = mixedMoment B raw3444step0 raw3444step0Labels := by
      have hz : ∀ j, raw3444 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3444step0 = (fun i j => raw3444 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3444step0 raw3444; decide +kernel
      have hl : raw3444step0Labels = raw3444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3444 raw3444Labels permutation434 hz
    mixedMoment B raw3444step0 raw3444step0Labels = mixedMoment B raw3444step1 raw3444step1Labels := by
      have hz : ∀ j, raw3444step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3444step1 = (fun i j => raw3444step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3444step1 raw3444step0; decide +kernel
      have hl : raw3444step1Labels = raw3444step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3444step0 raw3444step0Labels permutation80 hz
    mixedMoment B raw3444step1 raw3444step1Labels = mixedMoment B raw3444step2 raw3444step2Labels := by
      have hz : ∀ i, raw3444step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3444step2 = (fun i j => raw3444step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3444step2 raw3444step1; decide +kernel
      have hl : raw3444step2Labels = (fun j => raw3444step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3444step1 raw3444step1Labels permutation6 hz
    mixedMoment B raw3444step2 raw3444step2Labels = mixedMoment B raw3444step3 raw3444step3Labels := by
      have ha : raw3444step3 = (fun i j => raw3444step2 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3444step3 raw3444step2; decide +kernel
      have hl : raw3444step3Labels = raw3444step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3444step2 raw3444step2Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical275
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35317 raw35317Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw35317 raw35317Labels = mixedMoment B raw35317step0 raw35317step0Labels := by
      have hz : ∀ j, raw35317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35317step0 = (fun i j => raw35317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35317step0 raw35317; decide +kernel
      have hl : raw35317step0Labels = raw35317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35317 raw35317Labels permutation346 hz
    mixedMoment B raw35317step0 raw35317step0Labels = mixedMoment B raw35317step1 raw35317step1Labels := by
      have ha : raw35317step1 = (fun i j => raw35317step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35317step1 raw35317step0; decide +kernel
      have hl : raw35317step1Labels = raw35317step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35317step0 raw35317step0Labels permutation58 permutation5
    mixedMoment B raw35317step1 raw35317step1Labels = mixedMoment B raw35317step2 raw35317step2Labels := by
      have ha : raw35317step2 = -raw35317step1 := by apply Matrix.ext; change ∀ i j, raw35317step2 i j = -(raw35317step1 i j); unfold raw35317step2 raw35317step1; decide +kernel
      have hl : raw35317step2Labels = raw35317step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35317step2 raw35317step2Labels = mixedMoment B raw35317step3 raw35317step3Labels := by
      have ha : raw35317step3 = raw35317step2 := by apply Matrix.ext; unfold raw35317step3 raw35317step2; decide +kernel
      have hl : raw35317step2Labels = labelEmbedding1 ∘ raw35317step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35317step2 raw35317step2Labels raw35317step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical35318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35318 raw35318Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw35318 raw35318Labels = mixedMoment B raw35318step0 raw35318step0Labels := by
      have ha : raw35318step0 = (fun i j => raw35318 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35318step0 raw35318; decide +kernel
      have hl : raw35318step0Labels = raw35318Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35318 raw35318Labels permutation583 permutation7
    mixedMoment B raw35318step0 raw35318step0Labels = mixedMoment B raw35318step1 raw35318step1Labels := by
      have ha : raw35318step1 = raw35318step0 := by apply Matrix.ext; unfold raw35318step1 raw35318step0; decide +kernel
      have hl : raw35318step0Labels = labelEmbedding1 ∘ raw35318step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35318step0 raw35318step0Labels raw35318step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

theorem canonical35319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35319 raw35319Labels = mixedMoment B node3774 node3774Labels := by
  calc
    mixedMoment B raw35319 raw35319Labels = mixedMoment B raw35319step0 raw35319step0Labels := by
      have hz : ∀ j, raw35319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35319step0 = (fun i j => raw35319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35319step0 raw35319; decide +kernel
      have hl : raw35319step0Labels = raw35319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35319 raw35319Labels permutation346 hz
    mixedMoment B raw35319step0 raw35319step0Labels = mixedMoment B raw35319step1 raw35319step1Labels := by
      have ha : raw35319step1 = (fun i j => raw35319step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35319step1 raw35319step0; decide +kernel
      have hl : raw35319step1Labels = raw35319step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35319step0 raw35319step0Labels permutation123 permutation7
    mixedMoment B raw35319step1 raw35319step1Labels = mixedMoment B raw35319step2 raw35319step2Labels := by
      have ha : raw35319step2 = raw35319step1 := by apply Matrix.ext; unfold raw35319step2 raw35319step1; decide +kernel
      have hl : raw35319step1Labels = labelEmbedding1 ∘ raw35319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35319step1 raw35319step1Labels raw35319step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3774 node3774Labels := by rfl

theorem canonical35320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35320 raw35320Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw35320 raw35320Labels = mixedMoment B raw35320step0 raw35320step0Labels := by
      have hz : ∀ j, raw35320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35320step0 = (fun i j => raw35320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35320step0 raw35320; decide +kernel
      have hl : raw35320step0Labels = raw35320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35320 raw35320Labels permutation346 hz
    mixedMoment B raw35320step0 raw35320step0Labels = mixedMoment B raw35320step1 raw35320step1Labels := by
      have ha : raw35320step1 = (fun i j => raw35320step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35320step1 raw35320step0; decide +kernel
      have hl : raw35320step1Labels = raw35320step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35320step0 raw35320step0Labels permutation126 permutation7
    mixedMoment B raw35320step1 raw35320step1Labels = mixedMoment B raw35320step2 raw35320step2Labels := by
      have ha : raw35320step2 = raw35320step1 := by apply Matrix.ext; unfold raw35320step2 raw35320step1; decide +kernel
      have hl : raw35320step1Labels = labelEmbedding1 ∘ raw35320step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35320step1 raw35320step1Labels raw35320step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical35321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35321 raw35321Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw35321 raw35321Labels = mixedMoment B raw35321step0 raw35321step0Labels := by
      have ha : raw35321step0 = (fun i j => raw35321 (permutation279 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35321step0 raw35321; decide +kernel
      have hl : raw35321step0Labels = raw35321Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35321 raw35321Labels permutation279 permutation5
    mixedMoment B raw35321step0 raw35321step0Labels = mixedMoment B raw35321step1 raw35321step1Labels := by
      have ha : raw35321step1 = -raw35321step0 := by apply Matrix.ext; change ∀ i j, raw35321step1 i j = -(raw35321step0 i j); unfold raw35321step1 raw35321step0; decide +kernel
      have hl : raw35321step1Labels = raw35321step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35321step1 raw35321step1Labels = mixedMoment B raw35321step2 raw35321step2Labels := by
      have ha : raw35321step2 = raw35321step1 := by apply Matrix.ext; unfold raw35321step2 raw35321step1; decide +kernel
      have hl : raw35321step1Labels = labelEmbedding1 ∘ raw35321step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35321step1 raw35321step1Labels raw35321step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

theorem canonical35322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35322 raw35322Labels = mixedMoment B node3756 node3756Labels := by
  calc
    mixedMoment B raw35322 raw35322Labels = mixedMoment B raw35322step0 raw35322step0Labels := by
      have ha : raw35322step0 = (fun i j => raw35322 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35322step0 raw35322; decide +kernel
      have hl : raw35322step0Labels = raw35322Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35322 raw35322Labels permutation583 permutation7
    mixedMoment B raw35322step0 raw35322step0Labels = mixedMoment B raw35322step1 raw35322step1Labels := by
      have ha : raw35322step1 = raw35322step0 := by apply Matrix.ext; unfold raw35322step1 raw35322step0; decide +kernel
      have hl : raw35322step0Labels = labelEmbedding1 ∘ raw35322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35322step0 raw35322step0Labels raw35322step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3756 node3756Labels := by rfl

theorem canonical35323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35323 raw35323Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw35323 raw35323Labels = mixedMoment B raw35323step0 raw35323step0Labels := by
      have ha : raw35323step0 = (fun i j => raw35323 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35323step0 raw35323; decide +kernel
      have hl : raw35323step0Labels = raw35323Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35323 raw35323Labels permutation583 permutation7
    mixedMoment B raw35323step0 raw35323step0Labels = mixedMoment B raw35323step1 raw35323step1Labels := by
      have ha : raw35323step1 = raw35323step0 := by apply Matrix.ext; unfold raw35323step1 raw35323step0; decide +kernel
      have hl : raw35323step0Labels = labelEmbedding1 ∘ raw35323step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35323step0 raw35323step0Labels raw35323step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

theorem canonical35324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35324 raw35324Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw35324 raw35324Labels = mixedMoment B raw35324step0 raw35324step0Labels := by
      have hz : ∀ j, raw35324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35324step0 = (fun i j => raw35324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35324step0 raw35324; decide +kernel
      have hl : raw35324step0Labels = raw35324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35324 raw35324Labels permutation346 hz
    mixedMoment B raw35324step0 raw35324step0Labels = mixedMoment B raw35324step1 raw35324step1Labels := by
      have ha : raw35324step1 = (fun i j => raw35324step0 (permutation59 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35324step1 raw35324step0; decide +kernel
      have hl : raw35324step1Labels = raw35324step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35324step0 raw35324step0Labels permutation59 permutation5
    mixedMoment B raw35324step1 raw35324step1Labels = mixedMoment B raw35324step2 raw35324step2Labels := by
      have ha : raw35324step2 = -raw35324step1 := by apply Matrix.ext; change ∀ i j, raw35324step2 i j = -(raw35324step1 i j); unfold raw35324step2 raw35324step1; decide +kernel
      have hl : raw35324step2Labels = raw35324step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35324step2 raw35324step2Labels = mixedMoment B raw35324step3 raw35324step3Labels := by
      have ha : raw35324step3 = raw35324step2 := by apply Matrix.ext; unfold raw35324step3 raw35324step2; decide +kernel
      have hl : raw35324step2Labels = labelEmbedding1 ∘ raw35324step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35324step2 raw35324step2Labels raw35324step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

theorem canonical35325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35325 raw35325Labels = mixedMoment B node3763 node3763Labels := by
  calc
    mixedMoment B raw35325 raw35325Labels = mixedMoment B raw35325step0 raw35325step0Labels := by
      have ha : raw35325step0 = (fun i j => raw35325 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35325step0 raw35325; decide +kernel
      have hl : raw35325step0Labels = raw35325Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35325 raw35325Labels permutation583 permutation7
    mixedMoment B raw35325step0 raw35325step0Labels = mixedMoment B raw35325step1 raw35325step1Labels := by
      have ha : raw35325step1 = raw35325step0 := by apply Matrix.ext; unfold raw35325step1 raw35325step0; decide +kernel
      have hl : raw35325step0Labels = labelEmbedding1 ∘ raw35325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35325step0 raw35325step0Labels raw35325step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3763 node3763Labels := by rfl

theorem canonical35326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35326 raw35326Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw35326 raw35326Labels = mixedMoment B raw35326step0 raw35326step0Labels := by
      have hz : ∀ j, raw35326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35326step0 = (fun i j => raw35326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35326step0 raw35326; decide +kernel
      have hl : raw35326step0Labels = raw35326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35326 raw35326Labels permutation346 hz
    mixedMoment B raw35326step0 raw35326step0Labels = mixedMoment B raw35326step1 raw35326step1Labels := by
      have ha : raw35326step1 = (fun i j => raw35326step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35326step1 raw35326step0; decide +kernel
      have hl : raw35326step1Labels = raw35326step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35326step0 raw35326step0Labels permutation126 permutation7
    mixedMoment B raw35326step1 raw35326step1Labels = mixedMoment B raw35326step2 raw35326step2Labels := by
      have ha : raw35326step2 = raw35326step1 := by apply Matrix.ext; unfold raw35326step2 raw35326step1; decide +kernel
      have hl : raw35326step1Labels = labelEmbedding1 ∘ raw35326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35326step1 raw35326step1Labels raw35326step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

theorem canonical35327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35327 raw35327Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw35327 raw35327Labels = mixedMoment B raw35327step0 raw35327step0Labels := by
      have hz : ∀ j, raw35327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35327step0 = (fun i j => raw35327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35327step0 raw35327; decide +kernel
      have hl : raw35327step0Labels = raw35327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35327 raw35327Labels permutation346 hz
    mixedMoment B raw35327step0 raw35327step0Labels = mixedMoment B raw35327step1 raw35327step1Labels := by
      have ha : raw35327step1 = (fun i j => raw35327step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35327step1 raw35327step0; decide +kernel
      have hl : raw35327step1Labels = raw35327step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35327step0 raw35327step0Labels permutation57 permutation5
    mixedMoment B raw35327step1 raw35327step1Labels = mixedMoment B raw35327step2 raw35327step2Labels := by
      have ha : raw35327step2 = -raw35327step1 := by apply Matrix.ext; change ∀ i j, raw35327step2 i j = -(raw35327step1 i j); unfold raw35327step2 raw35327step1; decide +kernel
      have hl : raw35327step2Labels = raw35327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35327step2 raw35327step2Labels = mixedMoment B raw35327step3 raw35327step3Labels := by
      have ha : raw35327step3 = raw35327step2 := by apply Matrix.ext; unfold raw35327step3 raw35327step2; decide +kernel
      have hl : raw35327step2Labels = labelEmbedding1 ∘ raw35327step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35327step2 raw35327step2Labels raw35327step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical276
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35328 raw35328Labels = mixedMoment B node3409 node3409Labels := by
  calc
    mixedMoment B raw35328 raw35328Labels = mixedMoment B raw35328step0 raw35328step0Labels := by
      have ha : raw35328step0 = (fun i j => raw35328 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35328step0 raw35328; decide +kernel
      have hl : raw35328step0Labels = raw35328Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35328 raw35328Labels permutation583 permutation7
    mixedMoment B raw35328step0 raw35328step0Labels = mixedMoment B raw35328step1 raw35328step1Labels := by
      have ha : raw35328step1 = raw35328step0 := by apply Matrix.ext; unfold raw35328step1 raw35328step0; decide +kernel
      have hl : raw35328step0Labels = labelEmbedding1 ∘ raw35328step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35328step0 raw35328step0Labels raw35328step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3409 node3409Labels := by rfl

theorem canonical35329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35329 raw35329Labels = mixedMoment B node3421 node3421Labels := by
  calc
    mixedMoment B raw35329 raw35329Labels = mixedMoment B raw35329step0 raw35329step0Labels := by
      have hz : ∀ j, raw35329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35329step0 = (fun i j => raw35329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35329step0 raw35329; decide +kernel
      have hl : raw35329step0Labels = raw35329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35329 raw35329Labels permutation346 hz
    mixedMoment B raw35329step0 raw35329step0Labels = mixedMoment B raw35329step1 raw35329step1Labels := by
      have ha : raw35329step1 = (fun i j => raw35329step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35329step1 raw35329step0; decide +kernel
      have hl : raw35329step1Labels = raw35329step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35329step0 raw35329step0Labels permutation126 permutation7
    mixedMoment B raw35329step1 raw35329step1Labels = mixedMoment B raw35329step2 raw35329step2Labels := by
      have ha : raw35329step2 = raw35329step1 := by apply Matrix.ext; unfold raw35329step2 raw35329step1; decide +kernel
      have hl : raw35329step1Labels = labelEmbedding1 ∘ raw35329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35329step1 raw35329step1Labels raw35329step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3421 node3421Labels := by rfl

theorem canonical35330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35330 raw35330Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw35330 raw35330Labels = mixedMoment B raw35330step0 raw35330step0Labels := by
      have hz : ∀ j, raw35330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35330step0 = (fun i j => raw35330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35330step0 raw35330; decide +kernel
      have hl : raw35330step0Labels = raw35330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35330 raw35330Labels permutation346 hz
    mixedMoment B raw35330step0 raw35330step0Labels = mixedMoment B raw35330step1 raw35330step1Labels := by
      have ha : raw35330step1 = (fun i j => raw35330step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35330step1 raw35330step0; decide +kernel
      have hl : raw35330step1Labels = raw35330step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35330step0 raw35330step0Labels permutation126 permutation7
    mixedMoment B raw35330step1 raw35330step1Labels = mixedMoment B raw35330step2 raw35330step2Labels := by
      have ha : raw35330step2 = raw35330step1 := by apply Matrix.ext; unfold raw35330step2 raw35330step1; decide +kernel
      have hl : raw35330step1Labels = labelEmbedding1 ∘ raw35330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35330step1 raw35330step1Labels raw35330step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

theorem canonical35331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35331 raw35331Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw35331 raw35331Labels = mixedMoment B raw35331step0 raw35331step0Labels := by
      have hz : ∀ j, raw35331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35331step0 = (fun i j => raw35331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35331step0 raw35331; decide +kernel
      have hl : raw35331step0Labels = raw35331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35331 raw35331Labels permutation346 hz
    mixedMoment B raw35331step0 raw35331step0Labels = mixedMoment B raw35331step1 raw35331step1Labels := by
      have ha : raw35331step1 = (fun i j => raw35331step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35331step1 raw35331step0; decide +kernel
      have hl : raw35331step1Labels = raw35331step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35331step0 raw35331step0Labels permutation58 permutation5
    mixedMoment B raw35331step1 raw35331step1Labels = mixedMoment B raw35331step2 raw35331step2Labels := by
      have ha : raw35331step2 = -raw35331step1 := by apply Matrix.ext; change ∀ i j, raw35331step2 i j = -(raw35331step1 i j); unfold raw35331step2 raw35331step1; decide +kernel
      have hl : raw35331step2Labels = raw35331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35331step2 raw35331step2Labels = mixedMoment B raw35331step3 raw35331step3Labels := by
      have ha : raw35331step3 = raw35331step2 := by apply Matrix.ext; unfold raw35331step3 raw35331step2; decide +kernel
      have hl : raw35331step2Labels = labelEmbedding1 ∘ raw35331step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35331step2 raw35331step2Labels raw35331step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

theorem canonical35332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35332 raw35332Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw35332 raw35332Labels = mixedMoment B raw35332step0 raw35332step0Labels := by
      have ha : raw35332step0 = (fun i j => raw35332 (permutation663 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35332step0 raw35332; decide +kernel
      have hl : raw35332step0Labels = raw35332Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35332 raw35332Labels permutation663 permutation5
    mixedMoment B raw35332step0 raw35332step0Labels = mixedMoment B raw35332step1 raw35332step1Labels := by
      have ha : raw35332step1 = raw35332step0 := by apply Matrix.ext; unfold raw35332step1 raw35332step0; decide +kernel
      have hl : raw35332step0Labels = labelEmbedding1 ∘ raw35332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35332step0 raw35332step0Labels raw35332step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

theorem canonical35333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35333 raw35333Labels = mixedMoment B node3592 node3592Labels := by
  calc
    mixedMoment B raw35333 raw35333Labels = mixedMoment B raw35333step0 raw35333step0Labels := by
      have hz : ∀ j, raw35333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35333step0 = (fun i j => raw35333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35333step0 raw35333; decide +kernel
      have hl : raw35333step0Labels = raw35333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35333 raw35333Labels permutation346 hz
    mixedMoment B raw35333step0 raw35333step0Labels = mixedMoment B raw35333step1 raw35333step1Labels := by
      have ha : raw35333step1 = (fun i j => raw35333step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35333step1 raw35333step0; decide +kernel
      have hl : raw35333step1Labels = raw35333step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35333step0 raw35333step0Labels permutation150 permutation5
    mixedMoment B raw35333step1 raw35333step1Labels = mixedMoment B raw35333step2 raw35333step2Labels := by
      have ha : raw35333step2 = raw35333step1 := by apply Matrix.ext; unfold raw35333step2 raw35333step1; decide +kernel
      have hl : raw35333step1Labels = labelEmbedding1 ∘ raw35333step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35333step1 raw35333step1Labels raw35333step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3592 node3592Labels := by rfl

theorem canonical35334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35334 raw35334Labels = mixedMoment B node2822 node2822Labels := by
  calc
    mixedMoment B raw35334 raw35334Labels = mixedMoment B raw35334step0 raw35334step0Labels := by
      have ha : raw35334step0 = (fun i j => raw35334 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35334step0 raw35334; decide +kernel
      have hl : raw35334step0Labels = raw35334Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35334 raw35334Labels permutation272 permutation2
    _ = mixedMoment B node2822 node2822Labels := by rfl

theorem canonical35335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35335 raw35335Labels = mixedMoment B node3672 node3672Labels := by
  calc
    mixedMoment B raw35335 raw35335Labels = mixedMoment B raw35335step0 raw35335step0Labels := by
      have ha : raw35335step0 = (fun i j => raw35335 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35335step0 raw35335; decide +kernel
      have hl : raw35335step0Labels = raw35335Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35335 raw35335Labels permutation583 permutation2
    mixedMoment B raw35335step0 raw35335step0Labels = mixedMoment B raw35335step1 raw35335step1Labels := by
      have ha : raw35335step1 = -raw35335step0 := by apply Matrix.ext; change ∀ i j, raw35335step1 i j = -(raw35335step0 i j); unfold raw35335step1 raw35335step0; decide +kernel
      have hl : raw35335step1Labels = raw35335step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3672 node3672Labels := by rfl

theorem canonical35336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35336 raw35336Labels = mixedMoment B node3920 node3920Labels := by
  calc
    mixedMoment B raw35336 raw35336Labels = mixedMoment B raw35336step0 raw35336step0Labels := by
      have ha : raw35336step0 = (fun i j => raw35336 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35336step0 raw35336; decide +kernel
      have hl : raw35336step0Labels = raw35336Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35336 raw35336Labels permutation158 permutation2
    _ = mixedMoment B node3920 node3920Labels := by rfl

theorem canonical35337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35337 raw35337Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw35337 raw35337Labels = mixedMoment B raw35337step0 raw35337step0Labels := by
      have ha : raw35337step0 = (fun i j => raw35337 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35337step0 raw35337; decide +kernel
      have hl : raw35337step0Labels = raw35337Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35337 raw35337Labels permutation583 permutation2
    mixedMoment B raw35337step0 raw35337step0Labels = mixedMoment B raw35337step1 raw35337step1Labels := by
      have ha : raw35337step1 = -raw35337step0 := by apply Matrix.ext; change ∀ i j, raw35337step1 i j = -(raw35337step0 i j); unfold raw35337step1 raw35337step0; decide +kernel
      have hl : raw35337step1Labels = raw35337step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3779 node3779Labels := by rfl

theorem canonical35338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35338 raw35338Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw35338 raw35338Labels = mixedMoment B raw35338step0 raw35338step0Labels := by
      have ha : raw35338step0 = (fun i j => raw35338 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35338step0 raw35338; decide +kernel
      have hl : raw35338step0Labels = raw35338Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35338 raw35338Labels permutation588 permutation2
    mixedMoment B raw35338step0 raw35338step0Labels = mixedMoment B raw35338step1 raw35338step1Labels := by
      have ha : raw35338step1 = -raw35338step0 := by apply Matrix.ext; change ∀ i j, raw35338step1 i j = -(raw35338step0 i j); unfold raw35338step1 raw35338step0; decide +kernel
      have hl : raw35338step1Labels = raw35338step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3690 node3690Labels := by rfl

theorem canonical35339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35339 raw35339Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw35339 raw35339Labels = mixedMoment B raw35339step0 raw35339step0Labels := by
      have ha : raw35339step0 = (fun i j => raw35339 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35339step0 raw35339; decide +kernel
      have hl : raw35339step0Labels = raw35339Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35339 raw35339Labels permutation589 permutation2
    mixedMoment B raw35339step0 raw35339step0Labels = mixedMoment B raw35339step1 raw35339step1Labels := by
      have ha : raw35339step1 = -raw35339step0 := by apply Matrix.ext; change ∀ i j, raw35339step1 i j = -(raw35339step0 i j); unfold raw35339step1 raw35339step0; decide +kernel
      have hl : raw35339step1Labels = raw35339step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3690 node3690Labels := by rfl

theorem canonical35340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35340 raw35340Labels = mixedMoment B node3675 node3675Labels := by
  calc
    mixedMoment B raw35340 raw35340Labels = mixedMoment B raw35340step0 raw35340step0Labels := by
      have ha : raw35340step0 = (fun i j => raw35340 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35340step0 raw35340; decide +kernel
      have hl : raw35340step0Labels = raw35340Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35340 raw35340Labels permutation588 permutation2
    mixedMoment B raw35340step0 raw35340step0Labels = mixedMoment B raw35340step1 raw35340step1Labels := by
      have ha : raw35340step1 = -raw35340step0 := by apply Matrix.ext; change ∀ i j, raw35340step1 i j = -(raw35340step0 i j); unfold raw35340step1 raw35340step0; decide +kernel
      have hl : raw35340step1Labels = raw35340step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3675 node3675Labels := by rfl

theorem canonical35341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35341 raw35341Labels = mixedMoment B node2322 node2322Labels := by
  calc
    mixedMoment B raw35341 raw35341Labels = mixedMoment B raw35341step0 raw35341step0Labels := by
      have ha : raw35341step0 = (fun i j => raw35341 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35341step0 raw35341; decide +kernel
      have hl : raw35341step0Labels = raw35341Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35341 raw35341Labels permutation588 permutation2
    mixedMoment B raw35341step0 raw35341step0Labels = mixedMoment B raw35341step1 raw35341step1Labels := by
      have ha : raw35341step1 = -raw35341step0 := by apply Matrix.ext; change ∀ i j, raw35341step1 i j = -(raw35341step0 i j); unfold raw35341step1 raw35341step0; decide +kernel
      have hl : raw35341step1Labels = raw35341step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2322 node2322Labels := by rfl

theorem canonical35342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35342 raw35342Labels = mixedMoment B node2799 node2799Labels := by
  calc
    mixedMoment B raw35342 raw35342Labels = mixedMoment B raw35342step0 raw35342step0Labels := by
      have ha : raw35342step0 = (fun i j => raw35342 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35342step0 raw35342; decide +kernel
      have hl : raw35342step0Labels = raw35342Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35342 raw35342Labels permutation687 permutation2
    mixedMoment B raw35342step0 raw35342step0Labels = mixedMoment B raw35342step1 raw35342step1Labels := by
      have ha : raw35342step1 = -raw35342step0 := by apply Matrix.ext; change ∀ i j, raw35342step1 i j = -(raw35342step0 i j); unfold raw35342step1 raw35342step0; decide +kernel
      have hl : raw35342step1Labels = raw35342step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2799 node2799Labels := by rfl

theorem canonical35343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35343 raw35343Labels = mixedMoment B node2827 node2827Labels := by
  calc
    mixedMoment B raw35343 raw35343Labels = mixedMoment B raw35343step0 raw35343step0Labels := by
      have hz : ∀ j, raw35343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35343step0 = (fun i j => raw35343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35343step0 raw35343; decide +kernel
      have hl : raw35343step0Labels = raw35343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35343 raw35343Labels permutation346 hz
    mixedMoment B raw35343step0 raw35343step0Labels = mixedMoment B raw35343step1 raw35343step1Labels := by
      have ha : raw35343step1 = (fun i j => raw35343step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35343step1 raw35343step0; decide +kernel
      have hl : raw35343step1Labels = raw35343step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35343step0 raw35343step0Labels permutation57 permutation2
    _ = mixedMoment B node2827 node2827Labels := by rfl

theorem canonical35344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35344 raw35344Labels = mixedMoment B node3929 node3929Labels := by
  calc
    mixedMoment B raw35344 raw35344Labels = mixedMoment B raw35344step0 raw35344step0Labels := by
      have hz : ∀ j, raw35344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35344step0 = (fun i j => raw35344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35344step0 raw35344; decide +kernel
      have hl : raw35344step0Labels = raw35344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35344 raw35344Labels permutation346 hz
    _ = mixedMoment B node3929 node3929Labels := by rfl

theorem canonical35345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35345 raw35345Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw35345 raw35345Labels = mixedMoment B raw35345step0 raw35345step0Labels := by
      have hz : ∀ j, raw35345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35345step0 = (fun i j => raw35345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35345step0 raw35345; decide +kernel
      have hl : raw35345step0Labels = raw35345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35345 raw35345Labels permutation346 hz
    mixedMoment B raw35345step0 raw35345step0Labels = mixedMoment B raw35345step1 raw35345step1Labels := by
      have ha : raw35345step1 = (fun i j => raw35345step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35345step1 raw35345step0; decide +kernel
      have hl : raw35345step1Labels = raw35345step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35345step0 raw35345step0Labels permutation126 permutation2
    mixedMoment B raw35345step1 raw35345step1Labels = mixedMoment B raw35345step2 raw35345step2Labels := by
      have ha : raw35345step2 = -raw35345step1 := by apply Matrix.ext; change ∀ i j, raw35345step2 i j = -(raw35345step1 i j); unfold raw35345step2 raw35345step1; decide +kernel
      have hl : raw35345step2Labels = raw35345step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3790 node3790Labels := by rfl

theorem canonical35433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35433 raw35433Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw35433 raw35433Labels = mixedMoment B raw35433step0 raw35433step0Labels := by
      have hz : ∀ j, raw35433 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35433step0 = (fun i j => raw35433 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35433step0 raw35433; decide +kernel
      have hl : raw35433step0Labels = raw35433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35433 raw35433Labels permutation434 hz
    mixedMoment B raw35433step0 raw35433step0Labels = mixedMoment B raw35433step1 raw35433step1Labels := by
      have hz : ∀ j, raw35433step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35433step1 = (fun i j => raw35433step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35433step1 raw35433step0; decide +kernel
      have hl : raw35433step1Labels = raw35433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35433step0 raw35433step0Labels permutation80 hz
    mixedMoment B raw35433step1 raw35433step1Labels = mixedMoment B raw35433step2 raw35433step2Labels := by
      have ha : raw35433step2 = (fun i j => raw35433step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35433step2 raw35433step1; decide +kernel
      have hl : raw35433step2Labels = raw35433step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35433step1 raw35433step1Labels permutation15 permutation7
    mixedMoment B raw35433step2 raw35433step2Labels = mixedMoment B raw35433step3 raw35433step3Labels := by
      have ha : raw35433step3 = -raw35433step2 := by apply Matrix.ext; change ∀ i j, raw35433step3 i j = -(raw35433step2 i j); unfold raw35433step3 raw35433step2; decide +kernel
      have hl : raw35433step3Labels = raw35433step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35433step3 raw35433step3Labels = mixedMoment B raw35433step4 raw35433step4Labels := by
      have ha : raw35433step4 = raw35433step3 := by apply Matrix.ext; unfold raw35433step4 raw35433step3; decide +kernel
      have hl : raw35433step3Labels = labelEmbedding1 ∘ raw35433step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35433step3 raw35433step3Labels raw35433step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3485 node3485Labels := by rfl

theorem canonical35434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35434 raw35434Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw35434 raw35434Labels = mixedMoment B raw35434step0 raw35434step0Labels := by
      have hz : ∀ j, raw35434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35434step0 = (fun i j => raw35434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35434step0 raw35434; decide +kernel
      have hl : raw35434step0Labels = raw35434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35434 raw35434Labels permutation434 hz
    mixedMoment B raw35434step0 raw35434step0Labels = mixedMoment B raw35434step1 raw35434step1Labels := by
      have ha : raw35434step1 = (fun i j => raw35434step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35434step1 raw35434step0; decide +kernel
      have hl : raw35434step1Labels = raw35434step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35434step0 raw35434step0Labels permutation126 permutation7
    mixedMoment B raw35434step1 raw35434step1Labels = mixedMoment B raw35434step2 raw35434step2Labels := by
      have ha : raw35434step2 = raw35434step1 := by apply Matrix.ext; unfold raw35434step2 raw35434step1; decide +kernel
      have hl : raw35434step1Labels = labelEmbedding1 ∘ raw35434step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35434step1 raw35434step1Labels raw35434step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical35435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35435 raw35435Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw35435 raw35435Labels = mixedMoment B raw35435step0 raw35435step0Labels := by
      have hz : ∀ j, raw35435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35435step0 = (fun i j => raw35435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35435step0 raw35435; decide +kernel
      have hl : raw35435step0Labels = raw35435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35435 raw35435Labels permutation346 hz
    mixedMoment B raw35435step0 raw35435step0Labels = mixedMoment B raw35435step1 raw35435step1Labels := by
      have ha : raw35435step1 = (fun i j => raw35435step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35435step1 raw35435step0; decide +kernel
      have hl : raw35435step1Labels = raw35435step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35435step0 raw35435step0Labels permutation126 permutation7
    mixedMoment B raw35435step1 raw35435step1Labels = mixedMoment B raw35435step2 raw35435step2Labels := by
      have ha : raw35435step2 = raw35435step1 := by apply Matrix.ext; unfold raw35435step2 raw35435step1; decide +kernel
      have hl : raw35435step1Labels = labelEmbedding1 ∘ raw35435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35435step1 raw35435step1Labels raw35435step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical35436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35436 raw35436Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw35436 raw35436Labels = mixedMoment B raw35436step0 raw35436step0Labels := by
      have hz : ∀ j, raw35436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35436step0 = (fun i j => raw35436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35436step0 raw35436; decide +kernel
      have hl : raw35436step0Labels = raw35436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35436 raw35436Labels permutation434 hz
    mixedMoment B raw35436step0 raw35436step0Labels = mixedMoment B raw35436step1 raw35436step1Labels := by
      have hz : ∀ j, raw35436step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35436step1 = (fun i j => raw35436step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35436step1 raw35436step0; decide +kernel
      have hl : raw35436step1Labels = raw35436step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35436step0 raw35436step0Labels permutation80 hz
    mixedMoment B raw35436step1 raw35436step1Labels = mixedMoment B raw35436step2 raw35436step2Labels := by
      have hz : ∀ i, raw35436step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw35436step2 = (fun i j => raw35436step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw35436step2 raw35436step1; decide +kernel
      have hl : raw35436step2Labels = (fun j => raw35436step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35436step1 raw35436step1Labels permutation4 hz
    mixedMoment B raw35436step2 raw35436step2Labels = mixedMoment B raw35436step3 raw35436step3Labels := by
      have ha : raw35436step3 = (fun i j => raw35436step2 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35436step3 raw35436step2; decide +kernel
      have hl : raw35436step3Labels = raw35436step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35436step2 raw35436step2Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical35437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35437 raw35437Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw35437 raw35437Labels = mixedMoment B raw35437step0 raw35437step0Labels := by
      have hz : ∀ j, raw35437 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35437step0 = (fun i j => raw35437 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35437step0 raw35437; decide +kernel
      have hl : raw35437step0Labels = raw35437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35437 raw35437Labels permutation434 hz
    mixedMoment B raw35437step0 raw35437step0Labels = mixedMoment B raw35437step1 raw35437step1Labels := by
      have ha : raw35437step1 = (fun i j => raw35437step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35437step1 raw35437step0; decide +kernel
      have hl : raw35437step1Labels = raw35437step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35437step0 raw35437step0Labels permutation57 permutation7
    mixedMoment B raw35437step1 raw35437step1Labels = mixedMoment B raw35437step2 raw35437step2Labels := by
      have ha : raw35437step2 = -raw35437step1 := by apply Matrix.ext; change ∀ i j, raw35437step2 i j = -(raw35437step1 i j); unfold raw35437step2 raw35437step1; decide +kernel
      have hl : raw35437step2Labels = raw35437step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35437step2 raw35437step2Labels = mixedMoment B raw35437step3 raw35437step3Labels := by
      have ha : raw35437step3 = raw35437step2 := by apply Matrix.ext; unfold raw35437step3 raw35437step2; decide +kernel
      have hl : raw35437step2Labels = labelEmbedding1 ∘ raw35437step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35437step2 raw35437step2Labels raw35437step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

theorem canonical35438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35438 raw35438Labels = mixedMoment B node3753 node3753Labels := by
  calc
    mixedMoment B raw35438 raw35438Labels = mixedMoment B raw35438step0 raw35438step0Labels := by
      have ha : raw35438step0 = (fun i j => raw35438 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35438step0 raw35438; decide +kernel
      have hl : raw35438step0Labels = raw35438Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35438 raw35438Labels permutation583 permutation7
    mixedMoment B raw35438step0 raw35438step0Labels = mixedMoment B raw35438step1 raw35438step1Labels := by
      have ha : raw35438step1 = raw35438step0 := by apply Matrix.ext; unfold raw35438step1 raw35438step0; decide +kernel
      have hl : raw35438step0Labels = labelEmbedding1 ∘ raw35438step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35438step0 raw35438step0Labels raw35438step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3753 node3753Labels := by rfl

theorem canonical35439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35439 raw35439Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw35439 raw35439Labels = mixedMoment B raw35439step0 raw35439step0Labels := by
      have hz : ∀ j, raw35439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35439step0 = (fun i j => raw35439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35439step0 raw35439; decide +kernel
      have hl : raw35439step0Labels = raw35439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35439 raw35439Labels permutation434 hz
    mixedMoment B raw35439step0 raw35439step0Labels = mixedMoment B raw35439step1 raw35439step1Labels := by
      have ha : raw35439step1 = (fun i j => raw35439step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35439step1 raw35439step0; decide +kernel
      have hl : raw35439step1Labels = raw35439step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35439step0 raw35439step0Labels permutation57 permutation7
    mixedMoment B raw35439step1 raw35439step1Labels = mixedMoment B raw35439step2 raw35439step2Labels := by
      have ha : raw35439step2 = -raw35439step1 := by apply Matrix.ext; change ∀ i j, raw35439step2 i j = -(raw35439step1 i j); unfold raw35439step2 raw35439step1; decide +kernel
      have hl : raw35439step2Labels = raw35439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35439step2 raw35439step2Labels = mixedMoment B raw35439step3 raw35439step3Labels := by
      have ha : raw35439step3 = raw35439step2 := by apply Matrix.ext; unfold raw35439step3 raw35439step2; decide +kernel
      have hl : raw35439step2Labels = labelEmbedding1 ∘ raw35439step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35439step2 raw35439step2Labels raw35439step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical35440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35440 raw35440Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw35440 raw35440Labels = mixedMoment B raw35440step0 raw35440step0Labels := by
      have hz : ∀ j, raw35440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35440step0 = (fun i j => raw35440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35440step0 raw35440; decide +kernel
      have hl : raw35440step0Labels = raw35440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35440 raw35440Labels permutation346 hz
    mixedMoment B raw35440step0 raw35440step0Labels = mixedMoment B raw35440step1 raw35440step1Labels := by
      have ha : raw35440step1 = (fun i j => raw35440step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35440step1 raw35440step0; decide +kernel
      have hl : raw35440step1Labels = raw35440step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35440step0 raw35440step0Labels permutation57 permutation7
    mixedMoment B raw35440step1 raw35440step1Labels = mixedMoment B raw35440step2 raw35440step2Labels := by
      have ha : raw35440step2 = -raw35440step1 := by apply Matrix.ext; change ∀ i j, raw35440step2 i j = -(raw35440step1 i j); unfold raw35440step2 raw35440step1; decide +kernel
      have hl : raw35440step2Labels = raw35440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35440step2 raw35440step2Labels = mixedMoment B raw35440step3 raw35440step3Labels := by
      have ha : raw35440step3 = raw35440step2 := by apply Matrix.ext; unfold raw35440step3 raw35440step2; decide +kernel
      have hl : raw35440step2Labels = labelEmbedding1 ∘ raw35440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35440step2 raw35440step2Labels raw35440step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

theorem canonical35441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35441 raw35441Labels = mixedMoment B node3753 node3753Labels := by
  calc
    mixedMoment B raw35441 raw35441Labels = mixedMoment B raw35441step0 raw35441step0Labels := by
      have ha : raw35441step0 = (fun i j => raw35441 (permutation588 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35441step0 raw35441; decide +kernel
      have hl : raw35441step0Labels = raw35441Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35441 raw35441Labels permutation588 permutation7
    mixedMoment B raw35441step0 raw35441step0Labels = mixedMoment B raw35441step1 raw35441step1Labels := by
      have ha : raw35441step1 = raw35441step0 := by apply Matrix.ext; unfold raw35441step1 raw35441step0; decide +kernel
      have hl : raw35441step0Labels = labelEmbedding1 ∘ raw35441step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35441step0 raw35441step0Labels raw35441step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3753 node3753Labels := by rfl

theorem canonical35442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35442 raw35442Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw35442 raw35442Labels = mixedMoment B raw35442step0 raw35442step0Labels := by
      have hz : ∀ j, raw35442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35442step0 = (fun i j => raw35442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35442step0 raw35442; decide +kernel
      have hl : raw35442step0Labels = raw35442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35442 raw35442Labels permutation346 hz
    mixedMoment B raw35442step0 raw35442step0Labels = mixedMoment B raw35442step1 raw35442step1Labels := by
      have ha : raw35442step1 = (fun i j => raw35442step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35442step1 raw35442step0; decide +kernel
      have hl : raw35442step1Labels = raw35442step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35442step0 raw35442step0Labels permutation57 permutation7
    mixedMoment B raw35442step1 raw35442step1Labels = mixedMoment B raw35442step2 raw35442step2Labels := by
      have ha : raw35442step2 = -raw35442step1 := by apply Matrix.ext; change ∀ i j, raw35442step2 i j = -(raw35442step1 i j); unfold raw35442step2 raw35442step1; decide +kernel
      have hl : raw35442step2Labels = raw35442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35442step2 raw35442step2Labels = mixedMoment B raw35442step3 raw35442step3Labels := by
      have ha : raw35442step3 = raw35442step2 := by apply Matrix.ext; unfold raw35442step3 raw35442step2; decide +kernel
      have hl : raw35442step2Labels = labelEmbedding1 ∘ raw35442step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35442step2 raw35442step2Labels raw35442step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical35443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35443 raw35443Labels = mixedMoment B node3422 node3422Labels := by
  calc
    mixedMoment B raw35443 raw35443Labels = mixedMoment B raw35443step0 raw35443step0Labels := by
      have hz : ∀ j, raw35443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35443step0 = (fun i j => raw35443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35443step0 raw35443; decide +kernel
      have hl : raw35443step0Labels = raw35443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35443 raw35443Labels permutation434 hz
    mixedMoment B raw35443step0 raw35443step0Labels = mixedMoment B raw35443step1 raw35443step1Labels := by
      have hz : ∀ j, raw35443step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35443step1 = (fun i j => raw35443step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35443step1 raw35443step0; decide +kernel
      have hl : raw35443step1Labels = raw35443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35443step0 raw35443step0Labels permutation80 hz
    mixedMoment B raw35443step1 raw35443step1Labels = mixedMoment B raw35443step2 raw35443step2Labels := by
      have ha : raw35443step2 = (fun i j => raw35443step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35443step2 raw35443step1; decide +kernel
      have hl : raw35443step2Labels = raw35443step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35443step1 raw35443step1Labels permutation24 permutation7
    mixedMoment B raw35443step2 raw35443step2Labels = mixedMoment B raw35443step3 raw35443step3Labels := by
      have ha : raw35443step3 = raw35443step2 := by apply Matrix.ext; unfold raw35443step3 raw35443step2; decide +kernel
      have hl : raw35443step2Labels = labelEmbedding1 ∘ raw35443step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35443step2 raw35443step2Labels raw35443step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3422 node3422Labels := by rfl

theorem canonical35444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35444 raw35444Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw35444 raw35444Labels = mixedMoment B raw35444step0 raw35444step0Labels := by
      have hz : ∀ j, raw35444 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35444step0 = (fun i j => raw35444 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35444step0 raw35444; decide +kernel
      have hl : raw35444step0Labels = raw35444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35444 raw35444Labels permutation434 hz
    mixedMoment B raw35444step0 raw35444step0Labels = mixedMoment B raw35444step1 raw35444step1Labels := by
      have ha : raw35444step1 = (fun i j => raw35444step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35444step1 raw35444step0; decide +kernel
      have hl : raw35444step1Labels = raw35444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35444step0 raw35444step0Labels permutation126 permutation7
    mixedMoment B raw35444step1 raw35444step1Labels = mixedMoment B raw35444step2 raw35444step2Labels := by
      have ha : raw35444step2 = raw35444step1 := by apply Matrix.ext; unfold raw35444step2 raw35444step1; decide +kernel
      have hl : raw35444step1Labels = labelEmbedding1 ∘ raw35444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35444step1 raw35444step1Labels raw35444step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

theorem canonical35445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35445 raw35445Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw35445 raw35445Labels = mixedMoment B raw35445step0 raw35445step0Labels := by
      have hz : ∀ j, raw35445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35445step0 = (fun i j => raw35445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35445step0 raw35445; decide +kernel
      have hl : raw35445step0Labels = raw35445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35445 raw35445Labels permutation346 hz
    mixedMoment B raw35445step0 raw35445step0Labels = mixedMoment B raw35445step1 raw35445step1Labels := by
      have ha : raw35445step1 = (fun i j => raw35445step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35445step1 raw35445step0; decide +kernel
      have hl : raw35445step1Labels = raw35445step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35445step0 raw35445step0Labels permutation126 permutation7
    mixedMoment B raw35445step1 raw35445step1Labels = mixedMoment B raw35445step2 raw35445step2Labels := by
      have ha : raw35445step2 = raw35445step1 := by apply Matrix.ext; unfold raw35445step2 raw35445step1; decide +kernel
      have hl : raw35445step1Labels = labelEmbedding1 ∘ raw35445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35445step1 raw35445step1Labels raw35445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

theorem canonical35446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35446 raw35446Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw35446 raw35446Labels = mixedMoment B raw35446step0 raw35446step0Labels := by
      have hz : ∀ j, raw35446 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35446step0 = (fun i j => raw35446 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35446step0 raw35446; decide +kernel
      have hl : raw35446step0Labels = raw35446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35446 raw35446Labels permutation434 hz
    mixedMoment B raw35446step0 raw35446step0Labels = mixedMoment B raw35446step1 raw35446step1Labels := by
      have hz : ∀ j, raw35446step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35446step1 = (fun i j => raw35446step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35446step1 raw35446step0; decide +kernel
      have hl : raw35446step1Labels = raw35446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35446step0 raw35446step0Labels permutation80 hz
    mixedMoment B raw35446step1 raw35446step1Labels = mixedMoment B raw35446step2 raw35446step2Labels := by
      have ha : raw35446step2 = (fun i j => raw35446step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35446step2 raw35446step1; decide +kernel
      have hl : raw35446step2Labels = raw35446step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35446step1 raw35446step1Labels permutation24 permutation7
    mixedMoment B raw35446step2 raw35446step2Labels = mixedMoment B raw35446step3 raw35446step3Labels := by
      have ha : raw35446step3 = raw35446step2 := by apply Matrix.ext; unfold raw35446step3 raw35446step2; decide +kernel
      have hl : raw35446step2Labels = labelEmbedding1 ∘ raw35446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35446step2 raw35446step2Labels raw35446step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3485 node3485Labels := by rfl

theorem canonical35447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35447 raw35447Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw35447 raw35447Labels = mixedMoment B raw35447step0 raw35447step0Labels := by
      have hz : ∀ j, raw35447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35447step0 = (fun i j => raw35447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35447step0 raw35447; decide +kernel
      have hl : raw35447step0Labels = raw35447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35447 raw35447Labels permutation434 hz
    mixedMoment B raw35447step0 raw35447step0Labels = mixedMoment B raw35447step1 raw35447step1Labels := by
      have hz : ∀ j, raw35447step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35447step1 = (fun i j => raw35447step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35447step1 raw35447step0; decide +kernel
      have hl : raw35447step1Labels = raw35447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35447step0 raw35447step0Labels permutation80 hz
    mixedMoment B raw35447step1 raw35447step1Labels = mixedMoment B raw35447step2 raw35447step2Labels := by
      have ha : raw35447step2 = (fun i j => raw35447step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35447step2 raw35447step1; decide +kernel
      have hl : raw35447step2Labels = raw35447step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35447step1 raw35447step1Labels permutation15 permutation7
    mixedMoment B raw35447step2 raw35447step2Labels = mixedMoment B raw35447step3 raw35447step3Labels := by
      have ha : raw35447step3 = -raw35447step2 := by apply Matrix.ext; change ∀ i j, raw35447step3 i j = -(raw35447step2 i j); unfold raw35447step3 raw35447step2; decide +kernel
      have hl : raw35447step3Labels = raw35447step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35447step3 raw35447step3Labels = mixedMoment B raw35447step4 raw35447step4Labels := by
      have ha : raw35447step4 = raw35447step3 := by apply Matrix.ext; unfold raw35447step4 raw35447step3; decide +kernel
      have hl : raw35447step3Labels = labelEmbedding1 ∘ raw35447step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35447step3 raw35447step3Labels raw35447step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3423 node3423Labels := by rfl

theorem canonical35448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35448 raw35448Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw35448 raw35448Labels = mixedMoment B raw35448step0 raw35448step0Labels := by
      have hz : ∀ j, raw35448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35448step0 = (fun i j => raw35448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35448step0 raw35448; decide +kernel
      have hl : raw35448step0Labels = raw35448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35448 raw35448Labels permutation434 hz
    mixedMoment B raw35448step0 raw35448step0Labels = mixedMoment B raw35448step1 raw35448step1Labels := by
      have ha : raw35448step1 = (fun i j => raw35448step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35448step1 raw35448step0; decide +kernel
      have hl : raw35448step1Labels = raw35448step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35448step0 raw35448step0Labels permutation149 permutation5
    mixedMoment B raw35448step1 raw35448step1Labels = mixedMoment B raw35448step2 raw35448step2Labels := by
      have ha : raw35448step2 = raw35448step1 := by apply Matrix.ext; unfold raw35448step2 raw35448step1; decide +kernel
      have hl : raw35448step1Labels = labelEmbedding1 ∘ raw35448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35448step1 raw35448step1Labels raw35448step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

theorem canonical35449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35449 raw35449Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw35449 raw35449Labels = mixedMoment B raw35449step0 raw35449step0Labels := by
      have hz : ∀ j, raw35449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35449step0 = (fun i j => raw35449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35449step0 raw35449; decide +kernel
      have hl : raw35449step0Labels = raw35449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35449 raw35449Labels permutation346 hz
    mixedMoment B raw35449step0 raw35449step0Labels = mixedMoment B raw35449step1 raw35449step1Labels := by
      have ha : raw35449step1 = (fun i j => raw35449step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35449step1 raw35449step0; decide +kernel
      have hl : raw35449step1Labels = raw35449step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35449step0 raw35449step0Labels permutation149 permutation5
    mixedMoment B raw35449step1 raw35449step1Labels = mixedMoment B raw35449step2 raw35449step2Labels := by
      have ha : raw35449step2 = raw35449step1 := by apply Matrix.ext; unfold raw35449step2 raw35449step1; decide +kernel
      have hl : raw35449step1Labels = labelEmbedding1 ∘ raw35449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35449step1 raw35449step1Labels raw35449step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

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

theorem canonical35534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35534 raw35534Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw35534 raw35534Labels = mixedMoment B raw35534step0 raw35534step0Labels := by
      have hz : ∀ j, raw35534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35534step0 = (fun i j => raw35534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35534step0 raw35534; decide +kernel
      have hl : raw35534step0Labels = raw35534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35534 raw35534Labels permutation434 hz
    mixedMoment B raw35534step0 raw35534step0Labels = mixedMoment B raw35534step1 raw35534step1Labels := by
      have hz : ∀ j, raw35534step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35534step1 = (fun i j => raw35534step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35534step1 raw35534step0; decide +kernel
      have hl : raw35534step1Labels = raw35534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35534step0 raw35534step0Labels permutation80 hz
    mixedMoment B raw35534step1 raw35534step1Labels = mixedMoment B raw35534step2 raw35534step2Labels := by
      have hz : ∀ i, raw35534step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35534step2 = (fun i j => raw35534step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35534step2 raw35534step1; decide +kernel
      have hl : raw35534step2Labels = (fun j => raw35534step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35534step1 raw35534step1Labels permutation6 hz
    mixedMoment B raw35534step2 raw35534step2Labels = mixedMoment B raw35534step3 raw35534step3Labels := by
      have ha : raw35534step3 = (fun i j => raw35534step2 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35534step3 raw35534step2; decide +kernel
      have hl : raw35534step3Labels = raw35534step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35534step2 raw35534step2Labels permutation14 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical35535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35535 raw35535Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw35535 raw35535Labels = mixedMoment B raw35535step0 raw35535step0Labels := by
      have hz : ∀ j, raw35535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35535step0 = (fun i j => raw35535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35535step0 raw35535; decide +kernel
      have hl : raw35535step0Labels = raw35535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35535 raw35535Labels permutation434 hz
    mixedMoment B raw35535step0 raw35535step0Labels = mixedMoment B raw35535step1 raw35535step1Labels := by
      have hz : ∀ i, raw35535step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35535step1 = (fun i j => raw35535step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35535step1 raw35535step0; decide +kernel
      have hl : raw35535step1Labels = (fun j => raw35535step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35535step0 raw35535step0Labels permutation6 hz
    mixedMoment B raw35535step1 raw35535step1Labels = mixedMoment B raw35535step2 raw35535step2Labels := by
      have ha : raw35535step2 = (fun i j => raw35535step1 (permutation123 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35535step2 raw35535step1; decide +kernel
      have hl : raw35535step2Labels = raw35535step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35535step1 raw35535step1Labels permutation123 permutation0
    mixedMoment B raw35535step2 raw35535step2Labels = mixedMoment B raw35535step3 raw35535step3Labels := by
      have ha : raw35535step3 = -raw35535step2 := by apply Matrix.ext; change ∀ i j, raw35535step3 i j = -(raw35535step2 i j); unfold raw35535step3 raw35535step2; decide +kernel
      have hl : raw35535step3Labels = raw35535step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical35536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35536 raw35536Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw35536 raw35536Labels = mixedMoment B raw35536step0 raw35536step0Labels := by
      have hz : ∀ j, raw35536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35536step0 = (fun i j => raw35536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35536step0 raw35536; decide +kernel
      have hl : raw35536step0Labels = raw35536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35536 raw35536Labels permutation346 hz
    mixedMoment B raw35536step0 raw35536step0Labels = mixedMoment B raw35536step1 raw35536step1Labels := by
      have hz : ∀ i, raw35536step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35536step1 = (fun i j => raw35536step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35536step1 raw35536step0; decide +kernel
      have hl : raw35536step1Labels = (fun j => raw35536step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35536step0 raw35536step0Labels permutation6 hz
    mixedMoment B raw35536step1 raw35536step1Labels = mixedMoment B raw35536step2 raw35536step2Labels := by
      have ha : raw35536step2 = (fun i j => raw35536step1 (permutation123 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35536step2 raw35536step1; decide +kernel
      have hl : raw35536step2Labels = raw35536step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35536step1 raw35536step1Labels permutation123 permutation0
    mixedMoment B raw35536step2 raw35536step2Labels = mixedMoment B raw35536step3 raw35536step3Labels := by
      have ha : raw35536step3 = -raw35536step2 := by apply Matrix.ext; change ∀ i j, raw35536step3 i j = -(raw35536step2 i j); unfold raw35536step3 raw35536step2; decide +kernel
      have hl : raw35536step3Labels = raw35536step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical35537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35537 raw35537Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw35537 raw35537Labels = mixedMoment B raw35537step0 raw35537step0Labels := by
      have hz : ∀ j, raw35537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35537step0 = (fun i j => raw35537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35537step0 raw35537; decide +kernel
      have hl : raw35537step0Labels = raw35537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35537 raw35537Labels permutation434 hz
    mixedMoment B raw35537step0 raw35537step0Labels = mixedMoment B raw35537step1 raw35537step1Labels := by
      have hz : ∀ i, raw35537step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35537step1 = (fun i j => raw35537step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35537step1 raw35537step0; decide +kernel
      have hl : raw35537step1Labels = (fun j => raw35537step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35537step0 raw35537step0Labels permutation6 hz
    mixedMoment B raw35537step1 raw35537step1Labels = mixedMoment B raw35537step2 raw35537step2Labels := by
      have ha : raw35537step2 = (fun i j => raw35537step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35537step2 raw35537step1; decide +kernel
      have hl : raw35537step2Labels = raw35537step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35537step1 raw35537step1Labels permutation56 permutation0
    _ = mixedMoment B node4075 node4075Labels := by rfl

theorem canonical35538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35538 raw35538Labels = mixedMoment B node4086 node4086Labels := by
  calc
    mixedMoment B raw35538 raw35538Labels = mixedMoment B raw35538step0 raw35538step0Labels := by
      have hz : ∀ i, raw35538 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35538step0 = (fun i j => raw35538 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35538step0 raw35538; decide +kernel
      have hl : raw35538step0Labels = (fun j => raw35538Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35538 raw35538Labels permutation6 hz
    mixedMoment B raw35538step0 raw35538step0Labels = mixedMoment B raw35538step1 raw35538step1Labels := by
      have ha : raw35538step1 = (fun i j => raw35538step0 (permutation158 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35538step1 raw35538step0; decide +kernel
      have hl : raw35538step1Labels = raw35538step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35538step0 raw35538step0Labels permutation158 permutation0
    _ = mixedMoment B node4086 node4086Labels := by rfl

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

theorem canonical35542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35542 raw35542Labels = mixedMoment B node4076 node4076Labels := by
  calc
    mixedMoment B raw35542 raw35542Labels = mixedMoment B raw35542step0 raw35542step0Labels := by
      have hz : ∀ j, raw35542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35542step0 = (fun i j => raw35542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35542step0 raw35542; decide +kernel
      have hl : raw35542step0Labels = raw35542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35542 raw35542Labels permutation434 hz
    mixedMoment B raw35542step0 raw35542step0Labels = mixedMoment B raw35542step1 raw35542step1Labels := by
      have hz : ∀ j, raw35542step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35542step1 = (fun i j => raw35542step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35542step1 raw35542step0; decide +kernel
      have hl : raw35542step1Labels = raw35542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35542step0 raw35542step0Labels permutation80 hz
    mixedMoment B raw35542step1 raw35542step1Labels = mixedMoment B raw35542step2 raw35542step2Labels := by
      have hz : ∀ i, raw35542step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35542step2 = (fun i j => raw35542step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35542step2 raw35542step1; decide +kernel
      have hl : raw35542step2Labels = (fun j => raw35542step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35542step1 raw35542step1Labels permutation6 hz
    mixedMoment B raw35542step2 raw35542step2Labels = mixedMoment B raw35542step3 raw35542step3Labels := by
      have ha : raw35542step3 = (fun i j => raw35542step2 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35542step3 raw35542step2; decide +kernel
      have hl : raw35542step3Labels = raw35542step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35542step2 raw35542step2Labels permutation15 permutation0
    _ = mixedMoment B node4076 node4076Labels := by rfl

theorem canonical35543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35543 raw35543Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw35543 raw35543Labels = mixedMoment B raw35543step0 raw35543step0Labels := by
      have hz : ∀ j, raw35543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35543step0 = (fun i j => raw35543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35543step0 raw35543; decide +kernel
      have hl : raw35543step0Labels = raw35543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35543 raw35543Labels permutation434 hz
    mixedMoment B raw35543step0 raw35543step0Labels = mixedMoment B raw35543step1 raw35543step1Labels := by
      have hz : ∀ i, raw35543step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35543step1 = (fun i j => raw35543step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35543step1 raw35543step0; decide +kernel
      have hl : raw35543step1Labels = (fun j => raw35543step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35543step0 raw35543step0Labels permutation6 hz
    mixedMoment B raw35543step1 raw35543step1Labels = mixedMoment B raw35543step2 raw35543step2Labels := by
      have ha : raw35543step2 = (fun i j => raw35543step1 (permutation126 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35543step2 raw35543step1; decide +kernel
      have hl : raw35543step2Labels = raw35543step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35543step1 raw35543step1Labels permutation126 permutation0
    mixedMoment B raw35543step2 raw35543step2Labels = mixedMoment B raw35543step3 raw35543step3Labels := by
      have ha : raw35543step3 = -raw35543step2 := by apply Matrix.ext; change ∀ i j, raw35543step3 i j = -(raw35543step2 i j); unfold raw35543step3 raw35543step2; decide +kernel
      have hl : raw35543step3Labels = raw35543step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4075 node4075Labels := by rfl

theorem canonical35544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35544 raw35544Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw35544 raw35544Labels = mixedMoment B raw35544step0 raw35544step0Labels := by
      have hz : ∀ j, raw35544 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35544step0 = (fun i j => raw35544 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35544step0 raw35544; decide +kernel
      have hl : raw35544step0Labels = raw35544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35544 raw35544Labels permutation346 hz
    mixedMoment B raw35544step0 raw35544step0Labels = mixedMoment B raw35544step1 raw35544step1Labels := by
      have hz : ∀ i, raw35544step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35544step1 = (fun i j => raw35544step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35544step1 raw35544step0; decide +kernel
      have hl : raw35544step1Labels = (fun j => raw35544step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35544step0 raw35544step0Labels permutation6 hz
    mixedMoment B raw35544step1 raw35544step1Labels = mixedMoment B raw35544step2 raw35544step2Labels := by
      have ha : raw35544step2 = (fun i j => raw35544step1 (permutation126 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35544step2 raw35544step1; decide +kernel
      have hl : raw35544step2Labels = raw35544step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35544step1 raw35544step1Labels permutation126 permutation0
    mixedMoment B raw35544step2 raw35544step2Labels = mixedMoment B raw35544step3 raw35544step3Labels := by
      have ha : raw35544step3 = -raw35544step2 := by apply Matrix.ext; change ∀ i j, raw35544step3 i j = -(raw35544step2 i j); unfold raw35544step3 raw35544step2; decide +kernel
      have hl : raw35544step3Labels = raw35544step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4075 node4075Labels := by rfl

theorem canonical35545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35545 raw35545Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw35545 raw35545Labels = mixedMoment B raw35545step0 raw35545step0Labels := by
      have hz : ∀ j, raw35545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35545step0 = (fun i j => raw35545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35545step0 raw35545; decide +kernel
      have hl : raw35545step0Labels = raw35545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35545 raw35545Labels permutation434 hz
    mixedMoment B raw35545step0 raw35545step0Labels = mixedMoment B raw35545step1 raw35545step1Labels := by
      have hz : ∀ j, raw35545step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35545step1 = (fun i j => raw35545step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35545step1 raw35545step0; decide +kernel
      have hl : raw35545step1Labels = raw35545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35545step0 raw35545step0Labels permutation80 hz
    mixedMoment B raw35545step1 raw35545step1Labels = mixedMoment B raw35545step2 raw35545step2Labels := by
      have hz : ∀ i, raw35545step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35545step2 = (fun i j => raw35545step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35545step2 raw35545step1; decide +kernel
      have hl : raw35545step2Labels = (fun j => raw35545step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35545step1 raw35545step1Labels permutation6 hz
    mixedMoment B raw35545step2 raw35545step2Labels = mixedMoment B raw35545step3 raw35545step3Labels := by
      have ha : raw35545step3 = (fun i j => raw35545step2 (permutation24 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35545step3 raw35545step2; decide +kernel
      have hl : raw35545step3Labels = raw35545step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35545step2 raw35545step2Labels permutation24 permutation0
    mixedMoment B raw35545step3 raw35545step3Labels = mixedMoment B raw35545step4 raw35545step4Labels := by
      have ha : raw35545step4 = -raw35545step3 := by apply Matrix.ext; change ∀ i j, raw35545step4 i j = -(raw35545step3 i j); unfold raw35545step4 raw35545step3; decide +kernel
      have hl : raw35545step4Labels = raw35545step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical35546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35546 raw35546Labels = mixedMoment B node4076 node4076Labels := by
  calc
    mixedMoment B raw35546 raw35546Labels = mixedMoment B raw35546step0 raw35546step0Labels := by
      have hz : ∀ j, raw35546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35546step0 = (fun i j => raw35546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35546step0 raw35546; decide +kernel
      have hl : raw35546step0Labels = raw35546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35546 raw35546Labels permutation434 hz
    mixedMoment B raw35546step0 raw35546step0Labels = mixedMoment B raw35546step1 raw35546step1Labels := by
      have hz : ∀ j, raw35546step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35546step1 = (fun i j => raw35546step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35546step1 raw35546step0; decide +kernel
      have hl : raw35546step1Labels = raw35546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35546step0 raw35546step0Labels permutation80 hz
    mixedMoment B raw35546step1 raw35546step1Labels = mixedMoment B raw35546step2 raw35546step2Labels := by
      have hz : ∀ i, raw35546step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35546step2 = (fun i j => raw35546step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35546step2 raw35546step1; decide +kernel
      have hl : raw35546step2Labels = (fun j => raw35546step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35546step1 raw35546step1Labels permutation6 hz
    mixedMoment B raw35546step2 raw35546step2Labels = mixedMoment B raw35546step3 raw35546step3Labels := by
      have ha : raw35546step3 = (fun i j => raw35546step2 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35546step3 raw35546step2; decide +kernel
      have hl : raw35546step3Labels = raw35546step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35546step2 raw35546step2Labels permutation14 permutation0
    _ = mixedMoment B node4076 node4076Labels := by rfl

theorem canonical35547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35547 raw35547Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw35547 raw35547Labels = mixedMoment B raw35547step0 raw35547step0Labels := by
      have hz : ∀ j, raw35547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35547step0 = (fun i j => raw35547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35547step0 raw35547; decide +kernel
      have hl : raw35547step0Labels = raw35547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35547 raw35547Labels permutation434 hz
    mixedMoment B raw35547step0 raw35547step0Labels = mixedMoment B raw35547step1 raw35547step1Labels := by
      have hz : ∀ i, raw35547step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35547step1 = (fun i j => raw35547step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35547step1 raw35547step0; decide +kernel
      have hl : raw35547step1Labels = (fun j => raw35547step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35547step0 raw35547step0Labels permutation6 hz
    mixedMoment B raw35547step1 raw35547step1Labels = mixedMoment B raw35547step2 raw35547step2Labels := by
      have ha : raw35547step2 = (fun i j => raw35547step1 (permutation150 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35547step2 raw35547step1; decide +kernel
      have hl : raw35547step2Labels = raw35547step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35547step1 raw35547step1Labels permutation150 permutation0
    mixedMoment B raw35547step2 raw35547step2Labels = mixedMoment B raw35547step3 raw35547step3Labels := by
      have ha : raw35547step3 = -raw35547step2 := by apply Matrix.ext; change ∀ i j, raw35547step3 i j = -(raw35547step2 i j); unfold raw35547step3 raw35547step2; decide +kernel
      have hl : raw35547step3Labels = raw35547step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4075 node4075Labels := by rfl

theorem canonical35548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35548 raw35548Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw35548 raw35548Labels = mixedMoment B raw35548step0 raw35548step0Labels := by
      have hz : ∀ j, raw35548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35548step0 = (fun i j => raw35548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35548step0 raw35548; decide +kernel
      have hl : raw35548step0Labels = raw35548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35548 raw35548Labels permutation346 hz
    mixedMoment B raw35548step0 raw35548step0Labels = mixedMoment B raw35548step1 raw35548step1Labels := by
      have hz : ∀ i, raw35548step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35548step1 = (fun i j => raw35548step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35548step1 raw35548step0; decide +kernel
      have hl : raw35548step1Labels = (fun j => raw35548step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35548step0 raw35548step0Labels permutation6 hz
    mixedMoment B raw35548step1 raw35548step1Labels = mixedMoment B raw35548step2 raw35548step2Labels := by
      have ha : raw35548step2 = (fun i j => raw35548step1 (permutation150 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35548step2 raw35548step1; decide +kernel
      have hl : raw35548step2Labels = raw35548step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35548step1 raw35548step1Labels permutation150 permutation0
    mixedMoment B raw35548step2 raw35548step2Labels = mixedMoment B raw35548step3 raw35548step3Labels := by
      have ha : raw35548step3 = -raw35548step2 := by apply Matrix.ext; change ∀ i j, raw35548step3 i j = -(raw35548step2 i j); unfold raw35548step3 raw35548step2; decide +kernel
      have hl : raw35548step3Labels = raw35548step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4075 node4075Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2322 node2322Labels = 0 := by
  exact mixedMoment_alpha B hF node2322 node2322Labels 1 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2322 node2322Labels = Sparse.eval nodeValue2322 (mixedVector B) := by
  simpa only [nodeValue2322, Sparse.eval_nil] using zero2322 B _hB _hF

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

theorem sound2799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2799 node2799Labels = Sparse.eval nodeValue2799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2799) = mixedMoment B node2799 node2799Labels := rfl
  simpa [nodeValue2799, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2822 node2822Labels = Sparse.eval nodeValue2822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2822) = mixedMoment B node2822 node2822Labels := rfl
  simpa [nodeValue2822, Sparse.eval] using hc.symm

theorem sound2827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2827 node2827Labels = Sparse.eval nodeValue2827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2827) = mixedMoment B node2827 node2827Labels := rfl
  simpa [nodeValue2827, Sparse.eval] using hc.symm

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

theorem zero3409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3409 node3409Labels = 0 := by
  exact mixedMoment_alpha B hF node3409 node3409Labels 1 permutation487
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

theorem sound3409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3409 node3409Labels = Sparse.eval nodeValue3409 (mixedVector B) := by
  simpa only [nodeValue3409, Sparse.eval_nil] using zero3409 B _hB _hF

theorem sound3412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3412 node3412Labels = Sparse.eval nodeValue3412 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3412) = mixedMoment B node3412 node3412Labels := rfl
  simpa [nodeValue3412, Sparse.eval] using hc.symm

theorem sound3414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3414 node3414Labels = Sparse.eval nodeValue3414 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3414) = mixedMoment B node3414 node3414Labels := rfl
  simpa [nodeValue3414, Sparse.eval] using hc.symm

theorem sound3415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3415 node3415Labels = Sparse.eval nodeValue3415 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3415) = mixedMoment B node3415 node3415Labels := rfl
  simpa [nodeValue3415, Sparse.eval] using hc.symm

theorem sound3418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3418 node3418Labels = Sparse.eval nodeValue3418 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3418) = mixedMoment B node3418 node3418Labels := rfl
  simpa [nodeValue3418, Sparse.eval] using hc.symm

theorem sound3419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3419 node3419Labels = Sparse.eval nodeValue3419 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3419) = mixedMoment B node3419 node3419Labels := rfl
  simpa [nodeValue3419, Sparse.eval] using hc.symm

theorem sound3421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3421 node3421Labels = Sparse.eval nodeValue3421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3421) = mixedMoment B node3421 node3421Labels := rfl
  simpa [nodeValue3421, Sparse.eval] using hc.symm

theorem sound3422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3422 node3422Labels = Sparse.eval nodeValue3422 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3422) = mixedMoment B node3422 node3422Labels := rfl
  simpa [nodeValue3422, Sparse.eval] using hc.symm

theorem sound3423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3423 node3423Labels = Sparse.eval nodeValue3423 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3423) = mixedMoment B node3423 node3423Labels := rfl
  simpa [nodeValue3423, Sparse.eval] using hc.symm

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

theorem zero3485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3485 node3485Labels = 0 := by
  exact mixedMoment_order_one B hB node3485 node3485Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3482 node3482Labels = Sparse.eval nodeValue3482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3482) = mixedMoment B node3482 node3482Labels := rfl
  simpa [nodeValue3482, Sparse.eval] using hc.symm

theorem sound3485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3485 node3485Labels = Sparse.eval nodeValue3485 (mixedVector B) := by
  simpa only [nodeValue3485, Sparse.eval_nil] using zero3485 B _hB _hF

theorem sound3511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3511 node3511Labels = Sparse.eval nodeValue3511 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3511) = mixedMoment B node3511 node3511Labels := rfl
  simpa [nodeValue3511, Sparse.eval] using hc.symm

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

theorem sound3542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3542 node3542Labels = Sparse.eval nodeValue3542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3542) = mixedMoment B node3542 node3542Labels := rfl
  simpa [nodeValue3542, Sparse.eval] using hc.symm

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

theorem sound3592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3592 node3592Labels = Sparse.eval nodeValue3592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3592) = mixedMoment B node3592 node3592Labels := rfl
  simpa [nodeValue3592, Sparse.eval] using hc.symm

theorem sound3595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3595 node3595Labels = Sparse.eval nodeValue3595 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3595) = mixedMoment B node3595 node3595Labels := rfl
  simpa [nodeValue3595, Sparse.eval] using hc.symm

theorem sound3596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3596 node3596Labels = Sparse.eval nodeValue3596 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3596) = mixedMoment B node3596 node3596Labels := rfl
  simpa [nodeValue3596, Sparse.eval] using hc.symm

theorem sound3612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3612 node3612Labels = Sparse.eval nodeValue3612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3612) = mixedMoment B node3612 node3612Labels := rfl
  simpa [nodeValue3612, Sparse.eval] using hc.symm

theorem sound3631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3631 node3631Labels = Sparse.eval nodeValue3631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3631) = mixedMoment B node3631 node3631Labels := rfl
  simpa [nodeValue3631, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3672 node3672Labels = Sparse.eval nodeValue3672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3672) = mixedMoment B node3672 node3672Labels := rfl
  simpa [nodeValue3672, Sparse.eval] using hc.symm

theorem sound3675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3675 node3675Labels = Sparse.eval nodeValue3675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3675) = mixedMoment B node3675 node3675Labels := rfl
  simpa [nodeValue3675, Sparse.eval] using hc.symm

theorem sound3690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3690 node3690Labels = Sparse.eval nodeValue3690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3690) = mixedMoment B node3690 node3690Labels := rfl
  simpa [nodeValue3690, Sparse.eval] using hc.symm

theorem sound3694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3694 node3694Labels = Sparse.eval nodeValue3694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3694) = mixedMoment B node3694 node3694Labels := rfl
  simpa [nodeValue3694, Sparse.eval] using hc.symm

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

theorem zero3766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3766 node3766Labels = 0 := by
  exact mixedMoment_order_one B hB node3766 node3766Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3774 node3774Labels = 0 := by
  exact mixedMoment_order_one B hB node3774 node3774Labels 1
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

theorem sound3753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3753 node3753Labels = Sparse.eval nodeValue3753 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3753) = mixedMoment B node3753 node3753Labels := rfl
  simpa [nodeValue3753, Sparse.eval] using hc.symm

theorem sound3756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3756 node3756Labels = Sparse.eval nodeValue3756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3756) = mixedMoment B node3756 node3756Labels := rfl
  simpa [nodeValue3756, Sparse.eval] using hc.symm

theorem sound3763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3763 node3763Labels = Sparse.eval nodeValue3763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3763) = mixedMoment B node3763 node3763Labels := rfl
  simpa [nodeValue3763, Sparse.eval] using hc.symm

theorem sound3764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3764 node3764Labels = Sparse.eval nodeValue3764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3764) = mixedMoment B node3764 node3764Labels := rfl
  simpa [nodeValue3764, Sparse.eval] using hc.symm

theorem sound3766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3766 node3766Labels = Sparse.eval nodeValue3766 (mixedVector B) := by
  simpa only [nodeValue3766, Sparse.eval_nil] using zero3766 B _hB _hF

theorem sound3767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3767 node3767Labels = Sparse.eval nodeValue3767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3767) = mixedMoment B node3767 node3767Labels := rfl
  simpa [nodeValue3767, Sparse.eval] using hc.symm

theorem sound3774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3774 node3774Labels = Sparse.eval nodeValue3774 (mixedVector B) := by
  simpa only [nodeValue3774, Sparse.eval_nil] using zero3774 B _hB _hF

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

theorem zero3816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = 0 := by
  exact mixedMoment_order_one B hB node3816 node3816Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3817 node3817Labels = 0 := by
  exact mixedMoment_order_one B hB node3817 node3817Labels 1
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

theorem sound3779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3779 node3779Labels = Sparse.eval nodeValue3779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3779) = mixedMoment B node3779 node3779Labels := rfl
  simpa [nodeValue3779, Sparse.eval] using hc.symm

theorem sound3790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3790 node3790Labels = Sparse.eval nodeValue3790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3790) = mixedMoment B node3790 node3790Labels := rfl
  simpa [nodeValue3790, Sparse.eval] using hc.symm

theorem sound3797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3797 node3797Labels = Sparse.eval nodeValue3797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3797) = mixedMoment B node3797 node3797Labels := rfl
  simpa [nodeValue3797, Sparse.eval] using hc.symm

theorem sound3815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3815 node3815Labels = Sparse.eval nodeValue3815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3815) = mixedMoment B node3815 node3815Labels := rfl
  simpa [nodeValue3815, Sparse.eval] using hc.symm

theorem sound3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = Sparse.eval nodeValue3816 (mixedVector B) := by
  simpa only [nodeValue3816, Sparse.eval_nil] using zero3816 B _hB _hF

theorem sound3817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3817 node3817Labels = Sparse.eval nodeValue3817 (mixedVector B) := by
  simpa only [nodeValue3817, Sparse.eval_nil] using zero3817 B _hB _hF

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

theorem zero3920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3920 node3920Labels = 0 := by
  exact mixedMoment_alpha B hF node3920 node3920Labels 1 permutation160
    (by decide +kernel)

theorem zero3951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3951 node3951Labels = 0 := by
  exact mixedMoment_alpha B hF node3951 node3951Labels 1 permutation216
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

theorem sound3920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3920 node3920Labels = Sparse.eval nodeValue3920 (mixedVector B) := by
  simpa only [nodeValue3920, Sparse.eval_nil] using zero3920 B _hB _hF

theorem sound3929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3929 node3929Labels = Sparse.eval nodeValue3929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3929) = mixedMoment B node3929 node3929Labels := rfl
  simpa [nodeValue3929, Sparse.eval] using hc.symm

theorem sound3951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3951 node3951Labels = Sparse.eval nodeValue3951 (mixedVector B) := by
  simpa only [nodeValue3951, Sparse.eval_nil] using zero3951 B _hB _hF

theorem sound3960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3960 node3960Labels = Sparse.eval nodeValue3960 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3960) = mixedMoment B node3960 node3960Labels := rfl
  simpa [nodeValue3960, Sparse.eval] using hc.symm

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

theorem sound3963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3963 node3963Labels = Sparse.eval nodeValue3963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3963) = mixedMoment B node3963 node3963Labels := rfl
  simpa [nodeValue3963, Sparse.eval] using hc.symm

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

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources79
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2555 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2555 + difference 0 1) (sourceB2555 + difference 1 0) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2555 + difference 0 1) (sourceB2555 + difference 1 0) sourceC2555) = raw35317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35317; decide +kernel
    rw [ha]
    exact (canonical35317 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2555 + difference 0 2) (sourceB2555 + difference 2 0) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2555 + difference 0 2) (sourceB2555 + difference 2 0) sourceC2555) = raw35318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35318; decide +kernel
    rw [ha]
    exact (canonical35318 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2555 + difference 0 3) (sourceB2555 + difference 3 0) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3774) := by
    have ha : (tripleCharges (sourceA2555 + difference 0 3) (sourceB2555 + difference 3 0) sourceC2555) = raw35319 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35319; decide +kernel
    rw [ha]
    exact (canonical35319 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2555 + difference 0 4) (sourceB2555 + difference 4 0) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA2555 + difference 0 4) (sourceB2555 + difference 4 0) sourceC2555) = raw17733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17733; decide +kernel
    rw [ha]
    exact (canonical17733 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2555 + difference 0 5) (sourceB2555 + difference 5 0) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2555 + difference 0 5) (sourceB2555 + difference 5 0) sourceC2555) = raw35320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35320; decide +kernel
    rw [ha]
    exact (canonical35320 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2555 + difference 1 0) (sourceB2555 + difference 0 1) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2555 + difference 1 0) (sourceB2555 + difference 0 1) sourceC2555) = raw17753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17753; decide +kernel
    rw [ha]
    exact (canonical17753 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2555 + difference 1 2) (sourceB2555 + difference 2 1) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2555 + difference 1 2) (sourceB2555 + difference 2 1) sourceC2555) = raw17755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17755; decide +kernel
    rw [ha]
    exact (canonical17755 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2555 + difference 1 3) (sourceB2555 + difference 3 1) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3774) := by
    have ha : (tripleCharges (sourceA2555 + difference 1 3) (sourceB2555 + difference 3 1) sourceC2555) = raw17756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17756; decide +kernel
    rw [ha]
    exact (canonical17756 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2555 + difference 1 4) (sourceB2555 + difference 4 1) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA2555 + difference 1 4) (sourceB2555 + difference 4 1) sourceC2555) = raw29787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw29787; decide +kernel
    rw [ha]
    exact (canonical29787 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2555 + difference 1 5) (sourceB2555 + difference 5 1) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2555 + difference 1 5) (sourceB2555 + difference 5 1) sourceC2555) = raw17757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17757; decide +kernel
    rw [ha]
    exact (canonical17757 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2555 + difference 2 0) (sourceB2555 + difference 0 2) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2555 + difference 2 0) (sourceB2555 + difference 0 2) sourceC2555) = raw29793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw29793; decide +kernel
    rw [ha]
    exact (canonical29793 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2555 + difference 2 1) (sourceB2555 + difference 1 2) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2555 + difference 2 1) (sourceB2555 + difference 1 2) sourceC2555) = raw35321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35321; decide +kernel
    rw [ha]
    exact (canonical35321 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2555 + difference 2 3) (sourceB2555 + difference 3 2) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3756) := by
    have ha : (tripleCharges (sourceA2555 + difference 2 3) (sourceB2555 + difference 3 2) sourceC2555) = raw35322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35322; decide +kernel
    rw [ha]
    exact (canonical35322 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2555 + difference 2 4) (sourceB2555 + difference 4 2) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3951) := by
    have ha : (tripleCharges (sourceA2555 + difference 2 4) (sourceB2555 + difference 4 2) sourceC2555) = raw17744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17744; decide +kernel
    rw [ha]
    exact (canonical17744 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2555 + difference 2 5) (sourceB2555 + difference 5 2) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3797) := by
    have ha : (tripleCharges (sourceA2555 + difference 2 5) (sourceB2555 + difference 5 2) sourceC2555) = raw35323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35323; decide +kernel
    rw [ha]
    exact (canonical35323 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2555 + difference 3 0) (sourceB2555 + difference 0 3) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2555 + difference 3 0) (sourceB2555 + difference 0 3) sourceC2555) = raw29797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw29797; decide +kernel
    rw [ha]
    exact (canonical29797 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2555 + difference 3 1) (sourceB2555 + difference 1 3) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2555 + difference 3 1) (sourceB2555 + difference 1 3) sourceC2555) = raw35324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35324; decide +kernel
    rw [ha]
    exact (canonical35324 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2555 + difference 3 2) (sourceB2555 + difference 2 3) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3763) := by
    have ha : (tripleCharges (sourceA2555 + difference 3 2) (sourceB2555 + difference 2 3) sourceC2555) = raw35325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35325; decide +kernel
    rw [ha]
    exact (canonical35325 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2555 + difference 3 4) (sourceB2555 + difference 4 3) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3960) := by
    have ha : (tripleCharges (sourceA2555 + difference 3 4) (sourceB2555 + difference 4 3) sourceC2555) = raw17749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17749; decide +kernel
    rw [ha]
    exact (canonical17749 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2555 + difference 3 5) (sourceB2555 + difference 5 3) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3815) := by
    have ha : (tripleCharges (sourceA2555 + difference 3 5) (sourceB2555 + difference 5 3) sourceC2555) = raw35326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35326; decide +kernel
    rw [ha]
    exact (canonical35326 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2555 + difference 4 0) (sourceB2555 + difference 0 4) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2555 + difference 4 0) (sourceB2555 + difference 0 4) sourceC2555) = raw29801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw29801; decide +kernel
    rw [ha]
    exact (canonical29801 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2555 + difference 4 1) (sourceB2555 + difference 1 4) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2555 + difference 4 1) (sourceB2555 + difference 1 4) sourceC2555) = raw35327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35327; decide +kernel
    rw [ha]
    exact (canonical35327 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2555 + difference 4 2) (sourceB2555 + difference 2 4) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3409) := by
    have ha : (tripleCharges (sourceA2555 + difference 4 2) (sourceB2555 + difference 2 4) sourceC2555) = raw35328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35328; decide +kernel
    rw [ha]
    exact (canonical35328 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2555 + difference 4 3) (sourceB2555 + difference 3 4) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3421) := by
    have ha : (tripleCharges (sourceA2555 + difference 4 3) (sourceB2555 + difference 3 4) sourceC2555) = raw35329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35329; decide +kernel
    rw [ha]
    exact (canonical35329 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2555 + difference 4 5) (sourceB2555 + difference 5 4) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2555 + difference 4 5) (sourceB2555 + difference 5 4) sourceC2555) = raw35330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35330; decide +kernel
    rw [ha]
    exact (canonical35330 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2555 + difference 5 0) (sourceB2555 + difference 0 5) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2555 + difference 5 0) (sourceB2555 + difference 0 5) sourceC2555) = raw29806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw29806; decide +kernel
    rw [ha]
    exact (canonical29806 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2555 + difference 5 1) (sourceB2555 + difference 1 5) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2555 + difference 5 1) (sourceB2555 + difference 1 5) sourceC2555) = raw35331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35331; decide +kernel
    rw [ha]
    exact (canonical35331 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2555 + difference 5 2) (sourceB2555 + difference 2 5) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3511) := by
    have ha : (tripleCharges (sourceA2555 + difference 5 2) (sourceB2555 + difference 2 5) sourceC2555) = raw35332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35332; decide +kernel
    rw [ha]
    exact (canonical35332 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2555 + difference 5 3) (sourceB2555 + difference 3 5) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3592) := by
    have ha : (tripleCharges (sourceA2555 + difference 5 3) (sourceB2555 + difference 3 5) sourceC2555) = raw35333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35333; decide +kernel
    rw [ha]
    exact (canonical35333 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2555 + difference 5 4) (sourceB2555 + difference 4 5) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2555 + difference 5 4) (sourceB2555 + difference 4 5) sourceC2555) = raw17759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17759; decide +kernel
    rw [ha]
    exact (canonical17759 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2555 sourceB2555 sourceC2555
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2555, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2556 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2556 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2556 + difference 2 0) (sourceB2556 + difference 0 2) sourceC2556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2822) := by
    have ha : (tripleCharges (sourceA2556 + difference 2 0) (sourceB2556 + difference 0 2) sourceC2556) = raw29810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2556 sourceB2556 sourceC2556 difference raw29810; decide +kernel
    rw [ha]
    exact (canonical29810 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2556 + difference 2 1) (sourceB2556 + difference 1 2) sourceC2556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2822) := by
    have ha : (tripleCharges (sourceA2556 + difference 2 1) (sourceB2556 + difference 1 2) sourceC2556) = raw35334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2556 sourceB2556 sourceC2556 difference raw35334; decide +kernel
    rw [ha]
    exact (canonical35334 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2556 + difference 2 2) (sourceB2556 + difference 2 2) sourceC2556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2556 + difference 2 2) (sourceB2556 + difference 2 2) sourceC2556) = raw29809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2556 sourceB2556 sourceC2556 difference raw29809; decide +kernel
    rw [ha]
    exact (canonical29809 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2556 + difference 2 3) (sourceB2556 + difference 3 2) sourceC2556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3672) := by
    have ha : (tripleCharges (sourceA2556 + difference 2 3) (sourceB2556 + difference 3 2) sourceC2556) = raw35335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2556 sourceB2556 sourceC2556 difference raw35335; decide +kernel
    rw [ha]
    exact (canonical35335 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2556 + difference 2 4) (sourceB2556 + difference 4 2) sourceC2556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3920) := by
    have ha : (tripleCharges (sourceA2556 + difference 2 4) (sourceB2556 + difference 4 2) sourceC2556) = raw35336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2556 sourceB2556 sourceC2556 difference raw35336; decide +kernel
    rw [ha]
    exact (canonical35336 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2556 + difference 2 5) (sourceB2556 + difference 5 2) sourceC2556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA2556 + difference 2 5) (sourceB2556 + difference 5 2) sourceC2556) = raw35337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2556 sourceB2556 sourceC2556 difference raw35337; decide +kernel
    rw [ha]
    exact (canonical35337 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2556 + sourceB2556) sourceC2556) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2556 + sourceB2556) sourceC2556) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA2556 sourceB2556 sourceC2556 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2556 sourceB2556 sourceC2556
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2556, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2557 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2557 + difference 0 2) (sourceB2557 + difference 2 0) sourceC2557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2557 + difference 0 2) (sourceB2557 + difference 2 0) sourceC2557) = raw35338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2557 sourceB2557 sourceC2557 difference raw35338; decide +kernel
    rw [ha]
    exact (canonical35338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2557 + difference 1 2) (sourceB2557 + difference 2 1) sourceC2557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2557 + difference 1 2) (sourceB2557 + difference 2 1) sourceC2557) = raw35339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2557 sourceB2557 sourceC2557 difference raw35339; decide +kernel
    rw [ha]
    exact (canonical35339 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2557 + difference 2 2) (sourceB2557 + difference 2 2) sourceC2557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2557 + difference 2 2) (sourceB2557 + difference 2 2) sourceC2557) = raw29809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2557 sourceB2557 sourceC2557 difference raw29809; decide +kernel
    rw [ha]
    exact (canonical29809 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2557 + difference 3 2) (sourceB2557 + difference 2 3) sourceC2557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3675) := by
    have ha : (tripleCharges (sourceA2557 + difference 3 2) (sourceB2557 + difference 2 3) sourceC2557) = raw35340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2557 sourceB2557 sourceC2557 difference raw35340; decide +kernel
    rw [ha]
    exact (canonical35340 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2557 + difference 4 2) (sourceB2557 + difference 2 4) sourceC2557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2322) := by
    have ha : (tripleCharges (sourceA2557 + difference 4 2) (sourceB2557 + difference 2 4) sourceC2557) = raw35341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2557 sourceB2557 sourceC2557 difference raw35341; decide +kernel
    rw [ha]
    exact (canonical35341 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2557 + difference 5 2) (sourceB2557 + difference 2 5) sourceC2557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2799) := by
    have ha : (tripleCharges (sourceA2557 + difference 5 2) (sourceB2557 + difference 2 5) sourceC2557) = raw35342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2557 sourceB2557 sourceC2557 difference raw35342; decide +kernel
    rw [ha]
    exact (canonical35342 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2557 + sourceB2557) sourceC2557) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2557 + sourceB2557) sourceC2557) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA2557 sourceB2557 sourceC2557 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2557 sourceB2557 sourceC2557
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2557, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2558 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2558 + difference 3 0) (sourceB2558 + difference 0 3) sourceC2558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2827) := by
    have ha : (tripleCharges (sourceA2558 + difference 3 0) (sourceB2558 + difference 0 3) sourceC2558) = raw29811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2558 sourceB2558 sourceC2558 difference raw29811; decide +kernel
    rw [ha]
    exact (canonical29811 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2558 + difference 3 1) (sourceB2558 + difference 1 3) sourceC2558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2827) := by
    have ha : (tripleCharges (sourceA2558 + difference 3 1) (sourceB2558 + difference 1 3) sourceC2558) = raw35343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2558 sourceB2558 sourceC2558 difference raw35343; decide +kernel
    rw [ha]
    exact (canonical35343 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2558 + difference 3 2) (sourceB2558 + difference 2 3) sourceC2558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3675) := by
    have ha : (tripleCharges (sourceA2558 + difference 3 2) (sourceB2558 + difference 2 3) sourceC2558) = raw35340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2558 sourceB2558 sourceC2558 difference raw35340; decide +kernel
    rw [ha]
    exact (canonical35340 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2558 + difference 3 3) (sourceB2558 + difference 3 3) sourceC2558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2558 + difference 3 3) (sourceB2558 + difference 3 3) sourceC2558) = raw29809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2558 sourceB2558 sourceC2558 difference raw29809; decide +kernel
    rw [ha]
    exact (canonical29809 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2558 + difference 3 4) (sourceB2558 + difference 4 3) sourceC2558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3929) := by
    have ha : (tripleCharges (sourceA2558 + difference 3 4) (sourceB2558 + difference 4 3) sourceC2558) = raw35344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2558 sourceB2558 sourceC2558 difference raw35344; decide +kernel
    rw [ha]
    exact (canonical35344 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2558 + difference 3 5) (sourceB2558 + difference 5 3) sourceC2558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA2558 + difference 3 5) (sourceB2558 + difference 5 3) sourceC2558) = raw35345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2558 sourceB2558 sourceC2558 difference raw35345; decide +kernel
    rw [ha]
    exact (canonical35345 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2558 + sourceB2558) sourceC2558) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2558 + sourceB2558) sourceC2558) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA2558 sourceB2558 sourceC2558 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2558 sourceB2558 sourceC2558
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2558, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources80
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2566 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2566 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2566 + difference 0 1) (sourceB2566 + difference 1 0) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA2566 + difference 0 1) (sourceB2566 + difference 1 0) sourceC2566) = raw35433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35433; decide +kernel
    rw [ha]
    exact (canonical35433 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2566 + difference 0 2) (sourceB2566 + difference 2 0) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2566 + difference 0 2) (sourceB2566 + difference 2 0) sourceC2566) = raw35434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35434; decide +kernel
    rw [ha]
    exact (canonical35434 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2566 + difference 0 3) (sourceB2566 + difference 3 0) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2566 + difference 0 3) (sourceB2566 + difference 3 0) sourceC2566) = raw35435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35435; decide +kernel
    rw [ha]
    exact (canonical35435 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2566 + difference 0 4) (sourceB2566 + difference 4 0) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA2566 + difference 0 4) (sourceB2566 + difference 4 0) sourceC2566) = raw18008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18008; decide +kernel
    rw [ha]
    exact (canonical18008 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2566 + difference 0 5) (sourceB2566 + difference 5 0) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2566 + difference 0 5) (sourceB2566 + difference 5 0) sourceC2566) = raw35436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35436; decide +kernel
    rw [ha]
    exact (canonical35436 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2566 + difference 1 0) (sourceB2566 + difference 0 1) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2566 + difference 1 0) (sourceB2566 + difference 0 1) sourceC2566) = raw18028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18028; decide +kernel
    rw [ha]
    exact (canonical18028 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2566 + difference 1 2) (sourceB2566 + difference 2 1) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2566 + difference 1 2) (sourceB2566 + difference 2 1) sourceC2566) = raw18030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18030; decide +kernel
    rw [ha]
    exact (canonical18030 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2566 + difference 1 3) (sourceB2566 + difference 3 1) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2566 + difference 1 3) (sourceB2566 + difference 3 1) sourceC2566) = raw18031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18031; decide +kernel
    rw [ha]
    exact (canonical18031 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2566 + difference 1 4) (sourceB2566 + difference 4 1) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA2566 + difference 1 4) (sourceB2566 + difference 4 1) sourceC2566) = raw30001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw30001; decide +kernel
    rw [ha]
    exact (canonical30001 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2566 + difference 1 5) (sourceB2566 + difference 5 1) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA2566 + difference 1 5) (sourceB2566 + difference 5 1) sourceC2566) = raw18032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18032; decide +kernel
    rw [ha]
    exact (canonical18032 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2566 + difference 2 0) (sourceB2566 + difference 0 2) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2566 + difference 2 0) (sourceB2566 + difference 0 2) sourceC2566) = raw30007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw30007; decide +kernel
    rw [ha]
    exact (canonical30007 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2566 + difference 2 1) (sourceB2566 + difference 1 2) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2566 + difference 2 1) (sourceB2566 + difference 1 2) sourceC2566) = raw35437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35437; decide +kernel
    rw [ha]
    exact (canonical35437 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2566 + difference 2 3) (sourceB2566 + difference 3 2) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3753) := by
    have ha : (tripleCharges (sourceA2566 + difference 2 3) (sourceB2566 + difference 3 2) sourceC2566) = raw35438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35438; decide +kernel
    rw [ha]
    exact (canonical35438 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2566 + difference 2 4) (sourceB2566 + difference 4 2) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2566 + difference 2 4) (sourceB2566 + difference 4 2) sourceC2566) = raw18019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18019; decide +kernel
    rw [ha]
    exact (canonical18019 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2566 + difference 2 5) (sourceB2566 + difference 5 2) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2566 + difference 2 5) (sourceB2566 + difference 5 2) sourceC2566) = raw35439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35439; decide +kernel
    rw [ha]
    exact (canonical35439 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2566 + difference 3 0) (sourceB2566 + difference 0 3) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2566 + difference 3 0) (sourceB2566 + difference 0 3) sourceC2566) = raw30011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw30011; decide +kernel
    rw [ha]
    exact (canonical30011 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2566 + difference 3 1) (sourceB2566 + difference 1 3) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2566 + difference 3 1) (sourceB2566 + difference 1 3) sourceC2566) = raw35440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35440; decide +kernel
    rw [ha]
    exact (canonical35440 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2566 + difference 3 2) (sourceB2566 + difference 2 3) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3753) := by
    have ha : (tripleCharges (sourceA2566 + difference 3 2) (sourceB2566 + difference 2 3) sourceC2566) = raw35441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35441; decide +kernel
    rw [ha]
    exact (canonical35441 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2566 + difference 3 4) (sourceB2566 + difference 4 3) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2566 + difference 3 4) (sourceB2566 + difference 4 3) sourceC2566) = raw18024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18024; decide +kernel
    rw [ha]
    exact (canonical18024 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2566 + difference 3 5) (sourceB2566 + difference 5 3) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2566 + difference 3 5) (sourceB2566 + difference 5 3) sourceC2566) = raw35442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35442; decide +kernel
    rw [ha]
    exact (canonical35442 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2566 + difference 4 0) (sourceB2566 + difference 0 4) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2566 + difference 4 0) (sourceB2566 + difference 0 4) sourceC2566) = raw30015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw30015; decide +kernel
    rw [ha]
    exact (canonical30015 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2566 + difference 4 1) (sourceB2566 + difference 1 4) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3422) := by
    have ha : (tripleCharges (sourceA2566 + difference 4 1) (sourceB2566 + difference 1 4) sourceC2566) = raw35443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35443; decide +kernel
    rw [ha]
    exact (canonical35443 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2566 + difference 4 2) (sourceB2566 + difference 2 4) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2566 + difference 4 2) (sourceB2566 + difference 2 4) sourceC2566) = raw35444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35444; decide +kernel
    rw [ha]
    exact (canonical35444 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2566 + difference 4 3) (sourceB2566 + difference 3 4) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2566 + difference 4 3) (sourceB2566 + difference 3 4) sourceC2566) = raw35445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35445; decide +kernel
    rw [ha]
    exact (canonical35445 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2566 + difference 4 5) (sourceB2566 + difference 5 4) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA2566 + difference 4 5) (sourceB2566 + difference 5 4) sourceC2566) = raw35446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35446; decide +kernel
    rw [ha]
    exact (canonical35446 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2566 + difference 5 0) (sourceB2566 + difference 0 5) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3596) := by
    have ha : (tripleCharges (sourceA2566 + difference 5 0) (sourceB2566 + difference 0 5) sourceC2566) = raw30020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw30020; decide +kernel
    rw [ha]
    exact (canonical30020 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2566 + difference 5 1) (sourceB2566 + difference 1 5) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2566 + difference 5 1) (sourceB2566 + difference 1 5) sourceC2566) = raw35447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35447; decide +kernel
    rw [ha]
    exact (canonical35447 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2566 + difference 5 2) (sourceB2566 + difference 2 5) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2566 + difference 5 2) (sourceB2566 + difference 2 5) sourceC2566) = raw35448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35448; decide +kernel
    rw [ha]
    exact (canonical35448 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2566 + difference 5 3) (sourceB2566 + difference 3 5) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2566 + difference 5 3) (sourceB2566 + difference 3 5) sourceC2566) = raw35449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35449; decide +kernel
    rw [ha]
    exact (canonical35449 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2566 + difference 5 4) (sourceB2566 + difference 4 5) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2566 + difference 5 4) (sourceB2566 + difference 4 5) sourceC2566) = raw18034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18034; decide +kernel
    rw [ha]
    exact (canonical18034 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2566 sourceB2566 sourceC2566
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2566, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2571 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2571 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2571 + difference 0 1) (sourceB2571 + difference 1 0) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2571 + difference 0 1) (sourceB2571 + difference 1 0) sourceC2571) = raw35534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35534; decide +kernel
    rw [ha]
    exact (canonical35534 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2571 + difference 0 2) (sourceB2571 + difference 2 0) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 0 2) (sourceB2571 + difference 2 0) sourceC2571) = raw35535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35535; decide +kernel
    rw [ha]
    exact (canonical35535 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2571 + difference 0 3) (sourceB2571 + difference 3 0) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 0 3) (sourceB2571 + difference 3 0) sourceC2571) = raw35536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35536; decide +kernel
    rw [ha]
    exact (canonical35536 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2571 + difference 0 4) (sourceB2571 + difference 4 0) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2571 + difference 0 4) (sourceB2571 + difference 4 0) sourceC2571) = raw3448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw3448; decide +kernel
    rw [ha]
    exact (canonical3448 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2571 + difference 0 5) (sourceB2571 + difference 5 0) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2571 + difference 0 5) (sourceB2571 + difference 5 0) sourceC2571) = raw3444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw3444; decide +kernel
    rw [ha]
    exact (canonical3444 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2571 + difference 1 0) (sourceB2571 + difference 0 1) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2571 + difference 1 0) (sourceB2571 + difference 0 1) sourceC2571) = raw11541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw11541; decide +kernel
    rw [ha]
    exact (canonical11541 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2571 + difference 1 2) (sourceB2571 + difference 2 1) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 1 2) (sourceB2571 + difference 2 1) sourceC2571) = raw18340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw18340; decide +kernel
    rw [ha]
    exact (canonical18340 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2571 + difference 1 3) (sourceB2571 + difference 3 1) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 1 3) (sourceB2571 + difference 3 1) sourceC2571) = raw18341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw18341; decide +kernel
    rw [ha]
    exact (canonical18341 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2571 + difference 1 4) (sourceB2571 + difference 4 1) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2571 + difference 1 4) (sourceB2571 + difference 4 1) sourceC2571) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2571 + difference 1 5) (sourceB2571 + difference 5 1) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2571 + difference 1 5) (sourceB2571 + difference 5 1) sourceC2571) = raw3336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw3336; decide +kernel
    rw [ha]
    exact (canonical3336 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2571 + difference 2 0) (sourceB2571 + difference 0 2) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 2 0) (sourceB2571 + difference 0 2) sourceC2571) = raw31877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw31877; decide +kernel
    rw [ha]
    exact (canonical31877 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2571 + difference 2 1) (sourceB2571 + difference 1 2) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 2 1) (sourceB2571 + difference 1 2) sourceC2571) = raw35537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35537; decide +kernel
    rw [ha]
    exact (canonical35537 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2571 + difference 2 3) (sourceB2571 + difference 3 2) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2571 + difference 2 3) (sourceB2571 + difference 3 2) sourceC2571) = raw35538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35538; decide +kernel
    rw [ha]
    exact (canonical35538 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2571 + difference 2 4) (sourceB2571 + difference 4 2) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 2 4) (sourceB2571 + difference 4 2) sourceC2571) = raw18335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw18335; decide +kernel
    rw [ha]
    exact (canonical18335 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2571 + difference 2 5) (sourceB2571 + difference 5 2) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 2 5) (sourceB2571 + difference 5 2) sourceC2571) = raw35539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35539; decide +kernel
    rw [ha]
    exact (canonical35539 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2571 + difference 3 0) (sourceB2571 + difference 0 3) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 3 0) (sourceB2571 + difference 0 3) sourceC2571) = raw31880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw31880; decide +kernel
    rw [ha]
    exact (canonical31880 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2571 + difference 3 1) (sourceB2571 + difference 1 3) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 3 1) (sourceB2571 + difference 1 3) sourceC2571) = raw35540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35540; decide +kernel
    rw [ha]
    exact (canonical35540 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2571 + difference 3 2) (sourceB2571 + difference 2 3) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2571 + difference 3 2) (sourceB2571 + difference 2 3) sourceC2571) = raw35541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35541; decide +kernel
    rw [ha]
    exact (canonical35541 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2571 + difference 3 4) (sourceB2571 + difference 4 3) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 3 4) (sourceB2571 + difference 4 3) sourceC2571) = raw18337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw18337; decide +kernel
    rw [ha]
    exact (canonical18337 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2571 + difference 3 5) (sourceB2571 + difference 5 3) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 3 5) (sourceB2571 + difference 5 3) sourceC2571) = raw19367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw19367; decide +kernel
    rw [ha]
    exact (canonical19367 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2571 + difference 4 0) (sourceB2571 + difference 0 4) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2571 + difference 4 0) (sourceB2571 + difference 0 4) sourceC2571) = raw31882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw31882; decide +kernel
    rw [ha]
    exact (canonical31882 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2571 + difference 4 1) (sourceB2571 + difference 1 4) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2571 + difference 4 1) (sourceB2571 + difference 1 4) sourceC2571) = raw35542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35542; decide +kernel
    rw [ha]
    exact (canonical35542 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2571 + difference 4 2) (sourceB2571 + difference 2 4) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 4 2) (sourceB2571 + difference 2 4) sourceC2571) = raw35543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35543; decide +kernel
    rw [ha]
    exact (canonical35543 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2571 + difference 4 3) (sourceB2571 + difference 3 4) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 4 3) (sourceB2571 + difference 3 4) sourceC2571) = raw35544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35544; decide +kernel
    rw [ha]
    exact (canonical35544 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2571 + difference 4 5) (sourceB2571 + difference 5 4) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2571 + difference 4 5) (sourceB2571 + difference 5 4) sourceC2571) = raw35545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35545; decide +kernel
    rw [ha]
    exact (canonical35545 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2571 + difference 5 0) (sourceB2571 + difference 0 5) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2571 + difference 5 0) (sourceB2571 + difference 0 5) sourceC2571) = raw29299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw29299; decide +kernel
    rw [ha]
    exact (canonical29299 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2571 + difference 5 1) (sourceB2571 + difference 1 5) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2571 + difference 5 1) (sourceB2571 + difference 1 5) sourceC2571) = raw35546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35546; decide +kernel
    rw [ha]
    exact (canonical35546 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2571 + difference 5 2) (sourceB2571 + difference 2 5) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 5 2) (sourceB2571 + difference 2 5) sourceC2571) = raw35547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35547; decide +kernel
    rw [ha]
    exact (canonical35547 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2571 + difference 5 3) (sourceB2571 + difference 3 5) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 5 3) (sourceB2571 + difference 3 5) sourceC2571) = raw35548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35548; decide +kernel
    rw [ha]
    exact (canonical35548 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2571 + difference 5 4) (sourceB2571 + difference 4 5) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2571 + difference 5 4) (sourceB2571 + difference 4 5) sourceC2571) = raw18342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw18342; decide +kernel
    rw [ha]
    exact (canonical18342 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2571 sourceB2571 sourceC2571
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2571, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2052 : Integer.Sparse.reindex keyMap MixedData.row2052 = numericRow2052 := by decide +kernel

theorem numericCheck2052 (x : Master → ℝ) : Integer.Sparse.eval numericRow2052 x =
    (1 : ℝ) * reducedSource2052 x := by
  norm_num [numericRow2052, reducedSource2052, Integer.Sparse.eval, Sparse.eval, nodeValue3409, nodeValue3414, nodeValue3415, nodeValue3418, nodeValue3419, nodeValue3421, nodeValue3482, nodeValue3511, nodeValue3542, nodeValue3592, nodeValue3612, nodeValue3756, nodeValue3763, nodeValue3764, nodeValue3774, nodeValue3797, nodeValue3815, nodeValue3816, nodeValue3951, nodeValue3960, nodeValue3961]

theorem reindexCheck2053 : Integer.Sparse.reindex keyMap MixedData.row2053 = numericRow2053 := by decide +kernel

theorem numericCheck2053 (x : Master → ℝ) : Integer.Sparse.eval numericRow2053 x =
    (1 : ℝ) * reducedSource2053 x := by
  norm_num [numericRow2053, reducedSource2053, Integer.Sparse.eval, Sparse.eval, nodeValue2822, nodeValue3672, nodeValue3694, nodeValue3779, nodeValue3920, nodeValue4091]

theorem reindexCheck2054 : Integer.Sparse.reindex keyMap MixedData.row2054 = numericRow2054 := by decide +kernel

theorem numericCheck2054 (x : Master → ℝ) : Integer.Sparse.eval numericRow2054 x =
    (1 : ℝ) * reducedSource2054 x := by
  norm_num [numericRow2054, reducedSource2054, Integer.Sparse.eval, Sparse.eval, nodeValue2322, nodeValue2799, nodeValue3675, nodeValue3690, nodeValue3694, nodeValue4091]

theorem reindexCheck2055 : Integer.Sparse.reindex keyMap MixedData.row2055 = numericRow2055 := by decide +kernel

theorem numericCheck2055 (x : Master → ℝ) : Integer.Sparse.eval numericRow2055 x =
    (1 : ℝ) * reducedSource2055 x := by
  norm_num [numericRow2055, reducedSource2055, Integer.Sparse.eval, Sparse.eval, nodeValue2827, nodeValue3675, nodeValue3694, nodeValue3790, nodeValue3929, nodeValue4091]

theorem reindexCheck2057 : Integer.Sparse.reindex keyMap MixedData.row2057 = numericRow2057 := by decide +kernel

theorem numericCheck2057 (x : Master → ℝ) : Integer.Sparse.eval numericRow2057 x =
    (1 : ℝ) * reducedSource2057 x := by
  norm_num [numericRow2057, reducedSource2057, Integer.Sparse.eval, Sparse.eval, nodeValue3412, nodeValue3422, nodeValue3423, nodeValue3485, nodeValue3595, nodeValue3596, nodeValue3631, nodeValue3753, nodeValue3766, nodeValue3767, nodeValue3817, nodeValue3963, nodeValue4092]

theorem reindexCheck2058 : Integer.Sparse.reindex keyMap MixedData.row2058 = numericRow2058 := by decide +kernel

theorem numericCheck2058 (x : Master → ℝ) : Integer.Sparse.eval numericRow2058 x =
    (1 : ℝ) * reducedSource2058 x := by
  norm_num [numericRow2058, reducedSource2058, Integer.Sparse.eval, Sparse.eval, nodeValue4075, nodeValue4076, nodeValue4082, nodeValue4086, nodeValue4088, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2052 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2052 (mixedVector B) = 0 := by
  have h3409 : mixedVector B (Sum.inr 3409) = Sparse.eval nodeValue3409 (mixedVector B) := by
    change mixedMoment B node3409 node3409Labels = _
    exact sound3409 B hB hF
  have h3414 : mixedVector B (Sum.inr 3414) = Sparse.eval nodeValue3414 (mixedVector B) := by
    change mixedMoment B node3414 node3414Labels = _
    exact sound3414 B hB hF
  have h3415 : mixedVector B (Sum.inr 3415) = Sparse.eval nodeValue3415 (mixedVector B) := by
    change mixedMoment B node3415 node3415Labels = _
    exact sound3415 B hB hF
  have h3418 : mixedVector B (Sum.inr 3418) = Sparse.eval nodeValue3418 (mixedVector B) := by
    change mixedMoment B node3418 node3418Labels = _
    exact sound3418 B hB hF
  have h3419 : mixedVector B (Sum.inr 3419) = Sparse.eval nodeValue3419 (mixedVector B) := by
    change mixedMoment B node3419 node3419Labels = _
    exact sound3419 B hB hF
  have h3421 : mixedVector B (Sum.inr 3421) = Sparse.eval nodeValue3421 (mixedVector B) := by
    change mixedMoment B node3421 node3421Labels = _
    exact sound3421 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3511 : mixedVector B (Sum.inr 3511) = Sparse.eval nodeValue3511 (mixedVector B) := by
    change mixedMoment B node3511 node3511Labels = _
    exact sound3511 B hB hF
  have h3542 : mixedVector B (Sum.inr 3542) = Sparse.eval nodeValue3542 (mixedVector B) := by
    change mixedMoment B node3542 node3542Labels = _
    exact sound3542 B hB hF
  have h3592 : mixedVector B (Sum.inr 3592) = Sparse.eval nodeValue3592 (mixedVector B) := by
    change mixedMoment B node3592 node3592Labels = _
    exact sound3592 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h3756 : mixedVector B (Sum.inr 3756) = Sparse.eval nodeValue3756 (mixedVector B) := by
    change mixedMoment B node3756 node3756Labels = _
    exact sound3756 B hB hF
  have h3763 : mixedVector B (Sum.inr 3763) = Sparse.eval nodeValue3763 (mixedVector B) := by
    change mixedMoment B node3763 node3763Labels = _
    exact sound3763 B hB hF
  have h3764 : mixedVector B (Sum.inr 3764) = Sparse.eval nodeValue3764 (mixedVector B) := by
    change mixedMoment B node3764 node3764Labels = _
    exact sound3764 B hB hF
  have h3774 : mixedVector B (Sum.inr 3774) = Sparse.eval nodeValue3774 (mixedVector B) := by
    change mixedMoment B node3774 node3774Labels = _
    exact sound3774 B hB hF
  have h3797 : mixedVector B (Sum.inr 3797) = Sparse.eval nodeValue3797 (mixedVector B) := by
    change mixedMoment B node3797 node3797Labels = _
    exact sound3797 B hB hF
  have h3815 : mixedVector B (Sum.inr 3815) = Sparse.eval nodeValue3815 (mixedVector B) := by
    change mixedMoment B node3815 node3815Labels = _
    exact sound3815 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3951 : mixedVector B (Sum.inr 3951) = Sparse.eval nodeValue3951 (mixedVector B) := by
    change mixedMoment B node3951 node3951Labels = _
    exact sound3951 B hB hF
  have h3960 : mixedVector B (Sum.inr 3960) = Sparse.eval nodeValue3960 (mixedVector B) := by
    change mixedMoment B node3960 node3960Labels = _
    exact sound3960 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  simpa only [sourceForm2555, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3409, h3414, h3415, h3418, h3419, h3421, h3482, h3511, h3542, h3592, h3612, h3756, h3763, h3764, h3774, h3797, h3815, h3816, h3951, h3960, h3961, reducedSource2052] using sourceEq2555 B hB

theorem rowSound2052 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2052 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2052, numericCheck2052, reducedZero2052 B hB hF, mul_zero]

theorem reducedZero2053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2053 (mixedVector B) = 0 := by
  have h2822 : mixedVector B (Sum.inr 2822) = Sparse.eval nodeValue2822 (mixedVector B) := by
    change mixedMoment B node2822 node2822Labels = _
    exact sound2822 B hB hF
  have h3672 : mixedVector B (Sum.inr 3672) = Sparse.eval nodeValue3672 (mixedVector B) := by
    change mixedMoment B node3672 node3672Labels = _
    exact sound3672 B hB hF
  have h3694 : mixedVector B (Sum.inr 3694) = Sparse.eval nodeValue3694 (mixedVector B) := by
    change mixedMoment B node3694 node3694Labels = _
    exact sound3694 B hB hF
  have h3779 : mixedVector B (Sum.inr 3779) = Sparse.eval nodeValue3779 (mixedVector B) := by
    change mixedMoment B node3779 node3779Labels = _
    exact sound3779 B hB hF
  have h3920 : mixedVector B (Sum.inr 3920) = Sparse.eval nodeValue3920 (mixedVector B) := by
    change mixedMoment B node3920 node3920Labels = _
    exact sound3920 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2556, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2822, h3672, h3694, h3779, h3920, h4091, reducedSource2053] using sourceEq2556 B hB

theorem rowSound2053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2053 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2053, numericCheck2053, reducedZero2053 B hB hF, mul_zero]

theorem reducedZero2054 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2054 (mixedVector B) = 0 := by
  have h2322 : mixedVector B (Sum.inr 2322) = Sparse.eval nodeValue2322 (mixedVector B) := by
    change mixedMoment B node2322 node2322Labels = _
    exact sound2322 B hB hF
  have h2799 : mixedVector B (Sum.inr 2799) = Sparse.eval nodeValue2799 (mixedVector B) := by
    change mixedMoment B node2799 node2799Labels = _
    exact sound2799 B hB hF
  have h3675 : mixedVector B (Sum.inr 3675) = Sparse.eval nodeValue3675 (mixedVector B) := by
    change mixedMoment B node3675 node3675Labels = _
    exact sound3675 B hB hF
  have h3690 : mixedVector B (Sum.inr 3690) = Sparse.eval nodeValue3690 (mixedVector B) := by
    change mixedMoment B node3690 node3690Labels = _
    exact sound3690 B hB hF
  have h3694 : mixedVector B (Sum.inr 3694) = Sparse.eval nodeValue3694 (mixedVector B) := by
    change mixedMoment B node3694 node3694Labels = _
    exact sound3694 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2557, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2322, h2799, h3675, h3690, h3694, h4091, reducedSource2054] using sourceEq2557 B hB

theorem rowSound2054 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2054 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2054, numericCheck2054, reducedZero2054 B hB hF, mul_zero]

theorem reducedZero2055 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2055 (mixedVector B) = 0 := by
  have h2827 : mixedVector B (Sum.inr 2827) = Sparse.eval nodeValue2827 (mixedVector B) := by
    change mixedMoment B node2827 node2827Labels = _
    exact sound2827 B hB hF
  have h3675 : mixedVector B (Sum.inr 3675) = Sparse.eval nodeValue3675 (mixedVector B) := by
    change mixedMoment B node3675 node3675Labels = _
    exact sound3675 B hB hF
  have h3694 : mixedVector B (Sum.inr 3694) = Sparse.eval nodeValue3694 (mixedVector B) := by
    change mixedMoment B node3694 node3694Labels = _
    exact sound3694 B hB hF
  have h3790 : mixedVector B (Sum.inr 3790) = Sparse.eval nodeValue3790 (mixedVector B) := by
    change mixedMoment B node3790 node3790Labels = _
    exact sound3790 B hB hF
  have h3929 : mixedVector B (Sum.inr 3929) = Sparse.eval nodeValue3929 (mixedVector B) := by
    change mixedMoment B node3929 node3929Labels = _
    exact sound3929 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2558, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2827, h3675, h3694, h3790, h3929, h4091, reducedSource2055] using sourceEq2558 B hB

theorem rowSound2055 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2055 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2055, numericCheck2055, reducedZero2055 B hB hF, mul_zero]

theorem reducedZero2057 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2057 (mixedVector B) = 0 := by
  have h3412 : mixedVector B (Sum.inr 3412) = Sparse.eval nodeValue3412 (mixedVector B) := by
    change mixedMoment B node3412 node3412Labels = _
    exact sound3412 B hB hF
  have h3422 : mixedVector B (Sum.inr 3422) = Sparse.eval nodeValue3422 (mixedVector B) := by
    change mixedMoment B node3422 node3422Labels = _
    exact sound3422 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h3485 : mixedVector B (Sum.inr 3485) = Sparse.eval nodeValue3485 (mixedVector B) := by
    change mixedMoment B node3485 node3485Labels = _
    exact sound3485 B hB hF
  have h3595 : mixedVector B (Sum.inr 3595) = Sparse.eval nodeValue3595 (mixedVector B) := by
    change mixedMoment B node3595 node3595Labels = _
    exact sound3595 B hB hF
  have h3596 : mixedVector B (Sum.inr 3596) = Sparse.eval nodeValue3596 (mixedVector B) := by
    change mixedMoment B node3596 node3596Labels = _
    exact sound3596 B hB hF
  have h3631 : mixedVector B (Sum.inr 3631) = Sparse.eval nodeValue3631 (mixedVector B) := by
    change mixedMoment B node3631 node3631Labels = _
    exact sound3631 B hB hF
  have h3753 : mixedVector B (Sum.inr 3753) = Sparse.eval nodeValue3753 (mixedVector B) := by
    change mixedMoment B node3753 node3753Labels = _
    exact sound3753 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3767 : mixedVector B (Sum.inr 3767) = Sparse.eval nodeValue3767 (mixedVector B) := by
    change mixedMoment B node3767 node3767Labels = _
    exact sound3767 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  have h3963 : mixedVector B (Sum.inr 3963) = Sparse.eval nodeValue3963 (mixedVector B) := by
    change mixedMoment B node3963 node3963Labels = _
    exact sound3963 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2566, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3412, h3422, h3423, h3485, h3595, h3596, h3631, h3753, h3766, h3767, h3817, h3963, h4092, reducedSource2057] using sourceEq2566 B hB

theorem rowSound2057 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2057 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2057, numericCheck2057, reducedZero2057 B hB hF, mul_zero]

theorem reducedZero2058 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2058 (mixedVector B) = 0 := by
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4086 : mixedVector B (Sum.inr 4086) = Sparse.eval nodeValue4086 (mixedVector B) := by
    change mixedMoment B node4086 node4086Labels = _
    exact sound4086 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2571, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4075, h4076, h4082, h4086, h4088, h4092, reducedSource2058] using sourceEq2571 B hB

theorem rowSound2058 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2058 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2058, numericCheck2058, reducedZero2058 B hB hF, mul_zero]

theorem sourceRowsAt2048 : MixedData.sourceRows (2048 : Fin 2425) =
    MixedData.row2048 := by decide +kernel

theorem sourceRowsAt2049 : MixedData.sourceRows (2049 : Fin 2425) =
    MixedData.row2049 := by decide +kernel

theorem sourceRowsAt2050 : MixedData.sourceRows (2050 : Fin 2425) =
    MixedData.row2050 := by decide +kernel

theorem sourceRowsAt2051 : MixedData.sourceRows (2051 : Fin 2425) =
    MixedData.row2051 := by decide +kernel

theorem sourceRowsAt2052 : MixedData.sourceRows (2052 : Fin 2425) =
    MixedData.row2052 := by decide +kernel

theorem sourceRowsAt2053 : MixedData.sourceRows (2053 : Fin 2425) =
    MixedData.row2053 := by decide +kernel

theorem sourceRowsAt2054 : MixedData.sourceRows (2054 : Fin 2425) =
    MixedData.row2054 := by decide +kernel

theorem sourceRowsAt2055 : MixedData.sourceRows (2055 : Fin 2425) =
    MixedData.row2055 := by decide +kernel

theorem sourceRowsAt2056 : MixedData.sourceRows (2056 : Fin 2425) =
    MixedData.row2056 := by decide +kernel

theorem sourceRowsAt2057 : MixedData.sourceRows (2057 : Fin 2425) =
    MixedData.row2057 := by decide +kernel

theorem sourceRowsAt2058 : MixedData.sourceRows (2058 : Fin 2425) =
    MixedData.row2058 := by decide +kernel

theorem sourceRowsAt2059 : MixedData.sourceRows (2059 : Fin 2425) =
    MixedData.row2059 := by decide +kernel

theorem sourceRowsAt2060 : MixedData.sourceRows (2060 : Fin 2425) =
    MixedData.row2060 := by decide +kernel

theorem sourceRowsAt2061 : MixedData.sourceRows (2061 : Fin 2425) =
    MixedData.row2061 := by decide +kernel

theorem sourceRowsAt2062 : MixedData.sourceRows (2062 : Fin 2425) =
    MixedData.row2062 := by decide +kernel

theorem sourceRowsAt2063 : MixedData.sourceRows (2063 : Fin 2425) =
    MixedData.row2063 := by decide +kernel

theorem chunkSound128_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 128) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2048 ∨ k.val = 2049 ∨ k.val = 2050 ∨ k.val = 2051 ∨ k.val = 2052 ∨ k.val = 2053 ∨ k.val = 2054 ∨ k.val = 2055 ∨ k.val = 2056 ∨ k.val = 2057 ∨ k.val = 2058 ∨ k.val = 2059 ∨ k.val = 2060 ∨ k.val = 2061 ∨ k.val = 2062 ∨ k.val = 2063 := by omega
  rcases heq with h2048 | h2049 | h2050 | h2051 | h2052 | h2053 | h2054 | h2055 | h2056 | h2057 | h2058 | h2059 | h2060 | h2061 | h2062 | h2063
  · have he : k = (2048 : Fin 2425) := Fin.ext h2048
    subst k
    rw [sourceRowsAt2048]
    exact rowSound2048_e B hB hF
  · have he : k = (2049 : Fin 2425) := Fin.ext h2049
    subst k
    rw [sourceRowsAt2049]
    exact rowSound2049_e B hB hF
  · have he : k = (2050 : Fin 2425) := Fin.ext h2050
    subst k
    rw [sourceRowsAt2050]
    exact rowSound2050_e B hB hF
  · have he : k = (2051 : Fin 2425) := Fin.ext h2051
    subst k
    rw [sourceRowsAt2051]
    exact rowSound2051_e B hB hF
  · have he : k = (2052 : Fin 2425) := Fin.ext h2052
    subst k
    rw [sourceRowsAt2052]
    exact rowSound2052 B hB hF
  · have he : k = (2053 : Fin 2425) := Fin.ext h2053
    subst k
    rw [sourceRowsAt2053]
    exact rowSound2053 B hB hF
  · have he : k = (2054 : Fin 2425) := Fin.ext h2054
    subst k
    rw [sourceRowsAt2054]
    exact rowSound2054 B hB hF
  · have he : k = (2055 : Fin 2425) := Fin.ext h2055
    subst k
    rw [sourceRowsAt2055]
    exact rowSound2055 B hB hF
  · have he : k = (2056 : Fin 2425) := Fin.ext h2056
    subst k
    rw [sourceRowsAt2056]
    exact rowSound2056_e B hB hF
  · have he : k = (2057 : Fin 2425) := Fin.ext h2057
    subst k
    rw [sourceRowsAt2057]
    exact rowSound2057 B hB hF
  · have he : k = (2058 : Fin 2425) := Fin.ext h2058
    subst k
    rw [sourceRowsAt2058]
    exact rowSound2058 B hB hF
  · have he : k = (2059 : Fin 2425) := Fin.ext h2059
    subst k
    rw [sourceRowsAt2059]
    exact rowSound2059_e B hB hF
  · have he : k = (2060 : Fin 2425) := Fin.ext h2060
    subst k
    rw [sourceRowsAt2060]
    exact rowSound2060_e B hB hF
  · have he : k = (2061 : Fin 2425) := Fin.ext h2061
    subst k
    rw [sourceRowsAt2061]
    exact rowSound2061_e B hB hF
  · have he : k = (2062 : Fin 2425) := Fin.ext h2062
    subst k
    rw [sourceRowsAt2062]
    exact rowSound2062_e B hB hF
  · have he : k = (2063 : Fin 2425) := Fin.ext h2063
    subst k
    rw [sourceRowsAt2063]
    exact rowSound2063_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e_oai
