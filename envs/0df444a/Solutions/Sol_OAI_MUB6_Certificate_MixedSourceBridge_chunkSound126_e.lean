-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:52:42.558233+00:00
-- url     : https://prove2.me/submissions/2b0bbeec-8ed6-40aa-80ea-1e01f5fd9941

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2016_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2018_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2019_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2021_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2022_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2023_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14286 raw14286Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw14286 raw14286Labels = mixedMoment B raw14286step0 raw14286step0Labels := by
      have ha : raw14286step0 = (fun i j => raw14286 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14286step0 raw14286; decide +kernel
      have hl : raw14286step0Labels = raw14286Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14286 raw14286Labels permutation240 permutation7
    mixedMoment B raw14286step0 raw14286step0Labels = mixedMoment B raw14286step1 raw14286step1Labels := by
      have ha : raw14286step1 = -raw14286step0 := by apply Matrix.ext; change ∀ i j, raw14286step1 i j = -(raw14286step0 i j); unfold raw14286step1 raw14286step0; decide +kernel
      have hl : raw14286step1Labels = raw14286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14286step1 raw14286step1Labels = mixedMoment B raw14286step2 raw14286step2Labels := by
      have ha : raw14286step2 = raw14286step1 := by apply Matrix.ext; unfold raw14286step2 raw14286step1; decide +kernel
      have hl : raw14286step1Labels = labelEmbedding1 ∘ raw14286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14286step1 raw14286step1Labels raw14286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical14294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14294 raw14294Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw14294 raw14294Labels = mixedMoment B raw14294step0 raw14294step0Labels := by
      have ha : raw14294step0 = (fun i j => raw14294 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14294step0 raw14294; decide +kernel
      have hl : raw14294step0Labels = raw14294Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14294 raw14294Labels permutation240 permutation7
    mixedMoment B raw14294step0 raw14294step0Labels = mixedMoment B raw14294step1 raw14294step1Labels := by
      have ha : raw14294step1 = -raw14294step0 := by apply Matrix.ext; change ∀ i j, raw14294step1 i j = -(raw14294step0 i j); unfold raw14294step1 raw14294step0; decide +kernel
      have hl : raw14294step1Labels = raw14294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14294step1 raw14294step1Labels = mixedMoment B raw14294step2 raw14294step2Labels := by
      have ha : raw14294step2 = raw14294step1 := by apply Matrix.ext; unfold raw14294step2 raw14294step1; decide +kernel
      have hl : raw14294step1Labels = labelEmbedding1 ∘ raw14294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14294step1 raw14294step1Labels raw14294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical14296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14296 raw14296Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw14296 raw14296Labels = mixedMoment B raw14296step0 raw14296step0Labels := by
      have hz : ∀ j, raw14296 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14296step0 = (fun i j => raw14296 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14296step0 raw14296; decide +kernel
      have hl : raw14296step0Labels = raw14296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14296 raw14296Labels permutation520 hz
    mixedMoment B raw14296step0 raw14296step0Labels = mixedMoment B raw14296step1 raw14296step1Labels := by
      have ha : raw14296step1 = (fun i j => raw14296step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14296step1 raw14296step0; decide +kernel
      have hl : raw14296step1Labels = raw14296step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14296step0 raw14296step0Labels permutation50 permutation7
    mixedMoment B raw14296step1 raw14296step1Labels = mixedMoment B raw14296step2 raw14296step2Labels := by
      have ha : raw14296step2 = -raw14296step1 := by apply Matrix.ext; change ∀ i j, raw14296step2 i j = -(raw14296step1 i j); unfold raw14296step2 raw14296step1; decide +kernel
      have hl : raw14296step2Labels = raw14296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14296step2 raw14296step2Labels = mixedMoment B raw14296step3 raw14296step3Labels := by
      have ha : raw14296step3 = raw14296step2 := by apply Matrix.ext; unfold raw14296step3 raw14296step2; decide +kernel
      have hl : raw14296step2Labels = labelEmbedding1 ∘ raw14296step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14296step2 raw14296step2Labels raw14296step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical14297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14297 raw14297Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw14297 raw14297Labels = mixedMoment B raw14297step0 raw14297step0Labels := by
      have hz : ∀ j, raw14297 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14297step0 = (fun i j => raw14297 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14297step0 raw14297; decide +kernel
      have hl : raw14297step0Labels = raw14297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14297 raw14297Labels permutation590 hz
    mixedMoment B raw14297step0 raw14297step0Labels = mixedMoment B raw14297step1 raw14297step1Labels := by
      have ha : raw14297step1 = (fun i j => raw14297step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14297step1 raw14297step0; decide +kernel
      have hl : raw14297step1Labels = raw14297step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14297step0 raw14297step0Labels permutation50 permutation7
    mixedMoment B raw14297step1 raw14297step1Labels = mixedMoment B raw14297step2 raw14297step2Labels := by
      have ha : raw14297step2 = -raw14297step1 := by apply Matrix.ext; change ∀ i j, raw14297step2 i j = -(raw14297step1 i j); unfold raw14297step2 raw14297step1; decide +kernel
      have hl : raw14297step2Labels = raw14297step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14297step2 raw14297step2Labels = mixedMoment B raw14297step3 raw14297step3Labels := by
      have ha : raw14297step3 = raw14297step2 := by apply Matrix.ext; unfold raw14297step3 raw14297step2; decide +kernel
      have hl : raw14297step2Labels = labelEmbedding1 ∘ raw14297step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14297step2 raw14297step2Labels raw14297step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical14299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14299 raw14299Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw14299 raw14299Labels = mixedMoment B raw14299step0 raw14299step0Labels := by
      have ha : raw14299step0 = (fun i j => raw14299 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14299step0 raw14299; decide +kernel
      have hl : raw14299step0Labels = raw14299Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14299 raw14299Labels permutation240 permutation7
    mixedMoment B raw14299step0 raw14299step0Labels = mixedMoment B raw14299step1 raw14299step1Labels := by
      have ha : raw14299step1 = -raw14299step0 := by apply Matrix.ext; change ∀ i j, raw14299step1 i j = -(raw14299step0 i j); unfold raw14299step1 raw14299step0; decide +kernel
      have hl : raw14299step1Labels = raw14299step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14299step1 raw14299step1Labels = mixedMoment B raw14299step2 raw14299step2Labels := by
      have ha : raw14299step2 = raw14299step1 := by apply Matrix.ext; unfold raw14299step2 raw14299step1; decide +kernel
      have hl : raw14299step1Labels = labelEmbedding1 ∘ raw14299step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14299step1 raw14299step1Labels raw14299step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical14304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14304 raw14304Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw14304 raw14304Labels = mixedMoment B raw14304step0 raw14304step0Labels := by
      have ha : raw14304step0 = (fun i j => raw14304 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14304step0 raw14304; decide +kernel
      have hl : raw14304step0Labels = raw14304Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14304 raw14304Labels permutation260 permutation7
    mixedMoment B raw14304step0 raw14304step0Labels = mixedMoment B raw14304step1 raw14304step1Labels := by
      have ha : raw14304step1 = -raw14304step0 := by apply Matrix.ext; change ∀ i j, raw14304step1 i j = -(raw14304step0 i j); unfold raw14304step1 raw14304step0; decide +kernel
      have hl : raw14304step1Labels = raw14304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14304step1 raw14304step1Labels = mixedMoment B raw14304step2 raw14304step2Labels := by
      have ha : raw14304step2 = raw14304step1 := by apply Matrix.ext; unfold raw14304step2 raw14304step1; decide +kernel
      have hl : raw14304step1Labels = labelEmbedding1 ∘ raw14304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14304step1 raw14304step1Labels raw14304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical14364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14364 raw14364Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw14364 raw14364Labels = mixedMoment B raw14364step0 raw14364step0Labels := by
      have hz : ∀ j, raw14364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14364step0 = (fun i j => raw14364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14364step0 raw14364; decide +kernel
      have hl : raw14364step0Labels = raw14364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14364 raw14364Labels permutation265 hz
    mixedMoment B raw14364step0 raw14364step0Labels = mixedMoment B raw14364step1 raw14364step1Labels := by
      have hz : ∀ i, raw14364step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14364step1 = (fun i j => raw14364step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14364step1 raw14364step0; decide +kernel
      have hl : raw14364step1Labels = (fun j => raw14364step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14364step0 raw14364step0Labels permutation6 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical14366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14366 raw14366Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw14366 raw14366Labels = mixedMoment B raw14366step0 raw14366step0Labels := by
      have hz : ∀ j, raw14366 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14366step0 = (fun i j => raw14366 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14366step0 raw14366; decide +kernel
      have hl : raw14366step0Labels = raw14366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14366 raw14366Labels permutation520 hz
    mixedMoment B raw14366step0 raw14366step0Labels = mixedMoment B raw14366step1 raw14366step1Labels := by
      have hz : ∀ j, raw14366step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14366step1 = (fun i j => raw14366step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14366step1 raw14366step0; decide +kernel
      have hl : raw14366step1Labels = raw14366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14366step0 raw14366step0Labels permutation56 hz
    mixedMoment B raw14366step1 raw14366step1Labels = mixedMoment B raw14366step2 raw14366step2Labels := by
      have hz : ∀ i, raw14366step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14366step2 = (fun i j => raw14366step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14366step2 raw14366step1; decide +kernel
      have hl : raw14366step2Labels = (fun j => raw14366step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14366step1 raw14366step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical14367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14367 raw14367Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw14367 raw14367Labels = mixedMoment B raw14367step0 raw14367step0Labels := by
      have hz : ∀ j, raw14367 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14367step0 = (fun i j => raw14367 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14367step0 raw14367; decide +kernel
      have hl : raw14367step0Labels = raw14367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14367 raw14367Labels permutation590 hz
    mixedMoment B raw14367step0 raw14367step0Labels = mixedMoment B raw14367step1 raw14367step1Labels := by
      have hz : ∀ j, raw14367step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14367step1 = (fun i j => raw14367step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14367step1 raw14367step0; decide +kernel
      have hl : raw14367step1Labels = raw14367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14367step0 raw14367step0Labels permutation56 hz
    mixedMoment B raw14367step1 raw14367step1Labels = mixedMoment B raw14367step2 raw14367step2Labels := by
      have hz : ∀ i, raw14367step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14367step2 = (fun i j => raw14367step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14367step2 raw14367step1; decide +kernel
      have hl : raw14367step2Labels = (fun j => raw14367step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14367step1 raw14367step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical191
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24552 raw24552Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw24552 raw24552Labels = mixedMoment B raw24552step0 raw24552step0Labels := by
      have hz : ∀ j, raw24552 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24552step0 = (fun i j => raw24552 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24552step0 raw24552; decide +kernel
      have hl : raw24552step0Labels = raw24552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24552 raw24552Labels permutation265 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical207
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26546 raw26546Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw26546 raw26546Labels = mixedMoment B raw26546step0 raw26546step0Labels := by
      have hz : ∀ j, raw26546 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26546step0 = (fun i j => raw26546 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26546step0 raw26546; decide +kernel
      have hl : raw26546step0Labels = raw26546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26546 raw26546Labels permutation265 hz
    mixedMoment B raw26546step0 raw26546step0Labels = mixedMoment B raw26546step1 raw26546step1Labels := by
      have ha : raw26546step1 = (fun i j => raw26546step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26546step1 raw26546step0; decide +kernel
      have hl : raw26546step1Labels = raw26546step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26546step0 raw26546step0Labels permutation54 permutation7
    mixedMoment B raw26546step1 raw26546step1Labels = mixedMoment B raw26546step2 raw26546step2Labels := by
      have ha : raw26546step2 = -raw26546step1 := by apply Matrix.ext; change ∀ i j, raw26546step2 i j = -(raw26546step1 i j); unfold raw26546step2 raw26546step1; decide +kernel
      have hl : raw26546step2Labels = raw26546step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26546step2 raw26546step2Labels = mixedMoment B raw26546step3 raw26546step3Labels := by
      have ha : raw26546step3 = raw26546step2 := by apply Matrix.ext; unfold raw26546step3 raw26546step2; decide +kernel
      have hl : raw26546step2Labels = labelEmbedding1 ∘ raw26546step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26546step2 raw26546step2Labels raw26546step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical26547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26547 raw26547Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw26547 raw26547Labels = mixedMoment B raw26547step0 raw26547step0Labels := by
      have hz : ∀ j, raw26547 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26547step0 = (fun i j => raw26547 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26547step0 raw26547; decide +kernel
      have hl : raw26547step0Labels = raw26547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26547 raw26547Labels permutation265 hz
    mixedMoment B raw26547step0 raw26547step0Labels = mixedMoment B raw26547step1 raw26547step1Labels := by
      have ha : raw26547step1 = (fun i j => raw26547step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26547step1 raw26547step0; decide +kernel
      have hl : raw26547step1Labels = raw26547step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26547step0 raw26547step0Labels permutation50 permutation7
    mixedMoment B raw26547step1 raw26547step1Labels = mixedMoment B raw26547step2 raw26547step2Labels := by
      have ha : raw26547step2 = -raw26547step1 := by apply Matrix.ext; change ∀ i j, raw26547step2 i j = -(raw26547step1 i j); unfold raw26547step2 raw26547step1; decide +kernel
      have hl : raw26547step2Labels = raw26547step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26547step2 raw26547step2Labels = mixedMoment B raw26547step3 raw26547step3Labels := by
      have ha : raw26547step3 = raw26547step2 := by apply Matrix.ext; unfold raw26547step3 raw26547step2; decide +kernel
      have hl : raw26547step2Labels = labelEmbedding1 ∘ raw26547step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26547step2 raw26547step2Labels raw26547step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

theorem canonical26554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26554 raw26554Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw26554 raw26554Labels = mixedMoment B raw26554step0 raw26554step0Labels := by
      have ha : raw26554step0 = (fun i j => raw26554 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26554step0 raw26554; decide +kernel
      have hl : raw26554step0Labels = raw26554Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26554 raw26554Labels permutation160 permutation5
    mixedMoment B raw26554step0 raw26554step0Labels = mixedMoment B raw26554step1 raw26554step1Labels := by
      have ha : raw26554step1 = -raw26554step0 := by apply Matrix.ext; change ∀ i j, raw26554step1 i j = -(raw26554step0 i j); unfold raw26554step1 raw26554step0; decide +kernel
      have hl : raw26554step1Labels = raw26554step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26554step1 raw26554step1Labels = mixedMoment B raw26554step2 raw26554step2Labels := by
      have ha : raw26554step2 = raw26554step1 := by apply Matrix.ext; unfold raw26554step2 raw26554step1; decide +kernel
      have hl : raw26554step1Labels = labelEmbedding1 ∘ raw26554step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26554step1 raw26554step1Labels raw26554step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

theorem canonical26559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26559 raw26559Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw26559 raw26559Labels = mixedMoment B raw26559step0 raw26559step0Labels := by
      have ha : raw26559step0 = (fun i j => raw26559 (permutation154 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26559step0 raw26559; decide +kernel
      have hl : raw26559step0Labels = raw26559Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26559 raw26559Labels permutation154 permutation5
    mixedMoment B raw26559step0 raw26559step0Labels = mixedMoment B raw26559step1 raw26559step1Labels := by
      have ha : raw26559step1 = -raw26559step0 := by apply Matrix.ext; change ∀ i j, raw26559step1 i j = -(raw26559step0 i j); unfold raw26559step1 raw26559step0; decide +kernel
      have hl : raw26559step1Labels = raw26559step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26559step1 raw26559step1Labels = mixedMoment B raw26559step2 raw26559step2Labels := by
      have ha : raw26559step2 = raw26559step1 := by apply Matrix.ext; unfold raw26559step2 raw26559step1; decide +kernel
      have hl : raw26559step1Labels = labelEmbedding1 ∘ raw26559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26559step1 raw26559step1Labels raw26559step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

theorem canonical26564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26564 raw26564Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw26564 raw26564Labels = mixedMoment B raw26564step0 raw26564step0Labels := by
      have ha : raw26564step0 = (fun i j => raw26564 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26564step0 raw26564; decide +kernel
      have hl : raw26564step0Labels = raw26564Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26564 raw26564Labels permutation152 permutation5
    mixedMoment B raw26564step0 raw26564step0Labels = mixedMoment B raw26564step1 raw26564step1Labels := by
      have ha : raw26564step1 = -raw26564step0 := by apply Matrix.ext; change ∀ i j, raw26564step1 i j = -(raw26564step0 i j); unfold raw26564step1 raw26564step0; decide +kernel
      have hl : raw26564step1Labels = raw26564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26564step1 raw26564step1Labels = mixedMoment B raw26564step2 raw26564step2Labels := by
      have ha : raw26564step2 = raw26564step1 := by apply Matrix.ext; unfold raw26564step2 raw26564step1; decide +kernel
      have hl : raw26564step1Labels = labelEmbedding1 ∘ raw26564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26564step1 raw26564step1Labels raw26564step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

theorem canonical26569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26569 raw26569Labels = mixedMoment B node2688 node2688Labels := by
  calc
    mixedMoment B raw26569 raw26569Labels = mixedMoment B raw26569step0 raw26569step0Labels := by
      have ha : raw26569step0 = (fun i j => raw26569 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26569step0 raw26569; decide +kernel
      have hl : raw26569step0Labels = raw26569Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26569 raw26569Labels permutation640 permutation5
    mixedMoment B raw26569step0 raw26569step0Labels = mixedMoment B raw26569step1 raw26569step1Labels := by
      have ha : raw26569step1 = raw26569step0 := by apply Matrix.ext; unfold raw26569step1 raw26569step0; decide +kernel
      have hl : raw26569step0Labels = labelEmbedding1 ∘ raw26569step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26569step0 raw26569step0Labels raw26569step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2688 node2688Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical210
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26951 raw26951Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw26951 raw26951Labels = mixedMoment B raw26951step0 raw26951step0Labels := by
      have ha : raw26951step0 = (fun i j => raw26951 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26951step0 raw26951; decide +kernel
      have hl : raw26951step0Labels = raw26951Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26951 raw26951Labels permutation241 permutation7
    mixedMoment B raw26951step0 raw26951step0Labels = mixedMoment B raw26951step1 raw26951step1Labels := by
      have ha : raw26951step1 = -raw26951step0 := by apply Matrix.ext; change ∀ i j, raw26951step1 i j = -(raw26951step0 i j); unfold raw26951step1 raw26951step0; decide +kernel
      have hl : raw26951step1Labels = raw26951step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26951step1 raw26951step1Labels = mixedMoment B raw26951step2 raw26951step2Labels := by
      have ha : raw26951step2 = raw26951step1 := by apply Matrix.ext; unfold raw26951step2 raw26951step1; decide +kernel
      have hl : raw26951step1Labels = labelEmbedding1 ∘ raw26951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26951step1 raw26951step1Labels raw26951step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

theorem canonical26956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26956 raw26956Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw26956 raw26956Labels = mixedMoment B raw26956step0 raw26956step0Labels := by
      have ha : raw26956step0 = (fun i j => raw26956 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26956step0 raw26956; decide +kernel
      have hl : raw26956step0Labels = raw26956Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26956 raw26956Labels permutation240 permutation7
    mixedMoment B raw26956step0 raw26956step0Labels = mixedMoment B raw26956step1 raw26956step1Labels := by
      have ha : raw26956step1 = -raw26956step0 := by apply Matrix.ext; change ∀ i j, raw26956step1 i j = -(raw26956step0 i j); unfold raw26956step1 raw26956step0; decide +kernel
      have hl : raw26956step1Labels = raw26956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26956step1 raw26956step1Labels = mixedMoment B raw26956step2 raw26956step2Labels := by
      have ha : raw26956step2 = raw26956step1 := by apply Matrix.ext; unfold raw26956step2 raw26956step1; decide +kernel
      have hl : raw26956step1Labels = labelEmbedding1 ∘ raw26956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26956step1 raw26956step1Labels raw26956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

theorem canonical26960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26960 raw26960Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw26960 raw26960Labels = mixedMoment B raw26960step0 raw26960step0Labels := by
      have ha : raw26960step0 = (fun i j => raw26960 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26960step0 raw26960; decide +kernel
      have hl : raw26960step0Labels = raw26960Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26960 raw26960Labels permutation260 permutation7
    mixedMoment B raw26960step0 raw26960step0Labels = mixedMoment B raw26960step1 raw26960step1Labels := by
      have ha : raw26960step1 = -raw26960step0 := by apply Matrix.ext; change ∀ i j, raw26960step1 i j = -(raw26960step0 i j); unfold raw26960step1 raw26960step0; decide +kernel
      have hl : raw26960step1Labels = raw26960step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26960step1 raw26960step1Labels = mixedMoment B raw26960step2 raw26960step2Labels := by
      have ha : raw26960step2 = raw26960step1 := by apply Matrix.ext; unfold raw26960step2 raw26960step1; decide +kernel
      have hl : raw26960step1Labels = labelEmbedding1 ∘ raw26960step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26960step1 raw26960step1Labels raw26960step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

theorem canonical26964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26964 raw26964Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw26964 raw26964Labels = mixedMoment B raw26964step0 raw26964step0Labels := by
      have ha : raw26964step0 = (fun i j => raw26964 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26964step0 raw26964; decide +kernel
      have hl : raw26964step0Labels = raw26964Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26964 raw26964Labels permutation240 permutation7
    mixedMoment B raw26964step0 raw26964step0Labels = mixedMoment B raw26964step1 raw26964step1Labels := by
      have ha : raw26964step1 = -raw26964step0 := by apply Matrix.ext; change ∀ i j, raw26964step1 i j = -(raw26964step0 i j); unfold raw26964step1 raw26964step0; decide +kernel
      have hl : raw26964step1Labels = raw26964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26964step1 raw26964step1Labels = mixedMoment B raw26964step2 raw26964step2Labels := by
      have ha : raw26964step2 = raw26964step1 := by apply Matrix.ext; unfold raw26964step2 raw26964step1; decide +kernel
      have hl : raw26964step1Labels = labelEmbedding1 ∘ raw26964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26964step1 raw26964step1Labels raw26964step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical211
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27092 raw27092Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw27092 raw27092Labels = mixedMoment B raw27092step0 raw27092step0Labels := by
      have hz : ∀ j, raw27092 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27092step0 = (fun i j => raw27092 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27092step0 raw27092; decide +kernel
      have hl : raw27092step0Labels = raw27092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27092 raw27092Labels permutation265 hz
    mixedMoment B raw27092step0 raw27092step0Labels = mixedMoment B raw27092step1 raw27092step1Labels := by
      have ha : raw27092step1 = (fun i j => raw27092step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27092step1 raw27092step0; decide +kernel
      have hl : raw27092step1Labels = raw27092step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27092step0 raw27092step0Labels permutation49 permutation7
    mixedMoment B raw27092step1 raw27092step1Labels = mixedMoment B raw27092step2 raw27092step2Labels := by
      have ha : raw27092step2 = -raw27092step1 := by apply Matrix.ext; change ∀ i j, raw27092step2 i j = -(raw27092step1 i j); unfold raw27092step2 raw27092step1; decide +kernel
      have hl : raw27092step2Labels = raw27092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27092step2 raw27092step2Labels = mixedMoment B raw27092step3 raw27092step3Labels := by
      have ha : raw27092step3 = raw27092step2 := by apply Matrix.ext; unfold raw27092step3 raw27092step2; decide +kernel
      have hl : raw27092step2Labels = labelEmbedding1 ∘ raw27092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27092step2 raw27092step2Labels raw27092step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical27093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27093 raw27093Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw27093 raw27093Labels = mixedMoment B raw27093step0 raw27093step0Labels := by
      have hz : ∀ j, raw27093 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27093step0 = (fun i j => raw27093 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27093step0 raw27093; decide +kernel
      have hl : raw27093step0Labels = raw27093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27093 raw27093Labels permutation265 hz
    mixedMoment B raw27093step0 raw27093step0Labels = mixedMoment B raw27093step1 raw27093step1Labels := by
      have ha : raw27093step1 = (fun i j => raw27093step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27093step1 raw27093step0; decide +kernel
      have hl : raw27093step1Labels = raw27093step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27093step0 raw27093step0Labels permutation49 permutation7
    mixedMoment B raw27093step1 raw27093step1Labels = mixedMoment B raw27093step2 raw27093step2Labels := by
      have ha : raw27093step2 = -raw27093step1 := by apply Matrix.ext; change ∀ i j, raw27093step2 i j = -(raw27093step1 i j); unfold raw27093step2 raw27093step1; decide +kernel
      have hl : raw27093step2Labels = raw27093step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27093step2 raw27093step2Labels = mixedMoment B raw27093step3 raw27093step3Labels := by
      have ha : raw27093step3 = raw27093step2 := by apply Matrix.ext; unfold raw27093step3 raw27093step2; decide +kernel
      have hl : raw27093step2Labels = labelEmbedding1 ∘ raw27093step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27093step2 raw27093step2Labels raw27093step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical27094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27094 raw27094Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw27094 raw27094Labels = mixedMoment B raw27094step0 raw27094step0Labels := by
      have hz : ∀ j, raw27094 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27094step0 = (fun i j => raw27094 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27094step0 raw27094; decide +kernel
      have hl : raw27094step0Labels = raw27094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27094 raw27094Labels permutation520 hz
    mixedMoment B raw27094step0 raw27094step0Labels = mixedMoment B raw27094step1 raw27094step1Labels := by
      have hz : ∀ j, raw27094step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27094step1 = (fun i j => raw27094step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27094step1 raw27094step0; decide +kernel
      have hl : raw27094step1Labels = raw27094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27094step0 raw27094step0Labels permutation56 hz
    mixedMoment B raw27094step1 raw27094step1Labels = mixedMoment B raw27094step2 raw27094step2Labels := by
      have ha : raw27094step2 = (fun i j => raw27094step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27094step2 raw27094step1; decide +kernel
      have hl : raw27094step2Labels = raw27094step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27094step1 raw27094step1Labels permutation13 permutation7
    mixedMoment B raw27094step2 raw27094step2Labels = mixedMoment B raw27094step3 raw27094step3Labels := by
      have ha : raw27094step3 = -raw27094step2 := by apply Matrix.ext; change ∀ i j, raw27094step3 i j = -(raw27094step2 i j); unfold raw27094step3 raw27094step2; decide +kernel
      have hl : raw27094step3Labels = raw27094step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27094step3 raw27094step3Labels = mixedMoment B raw27094step4 raw27094step4Labels := by
      have ha : raw27094step4 = raw27094step3 := by apply Matrix.ext; unfold raw27094step4 raw27094step3; decide +kernel
      have hl : raw27094step3Labels = labelEmbedding1 ∘ raw27094step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27094step3 raw27094step3Labels raw27094step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2265 node2265Labels := by rfl

theorem canonical27095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27095 raw27095Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw27095 raw27095Labels = mixedMoment B raw27095step0 raw27095step0Labels := by
      have hz : ∀ j, raw27095 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27095step0 = (fun i j => raw27095 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27095step0 raw27095; decide +kernel
      have hl : raw27095step0Labels = raw27095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27095 raw27095Labels permutation590 hz
    mixedMoment B raw27095step0 raw27095step0Labels = mixedMoment B raw27095step1 raw27095step1Labels := by
      have hz : ∀ j, raw27095step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27095step1 = (fun i j => raw27095step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27095step1 raw27095step0; decide +kernel
      have hl : raw27095step1Labels = raw27095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27095step0 raw27095step0Labels permutation56 hz
    mixedMoment B raw27095step1 raw27095step1Labels = mixedMoment B raw27095step2 raw27095step2Labels := by
      have ha : raw27095step2 = (fun i j => raw27095step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27095step2 raw27095step1; decide +kernel
      have hl : raw27095step2Labels = raw27095step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27095step1 raw27095step1Labels permutation13 permutation7
    mixedMoment B raw27095step2 raw27095step2Labels = mixedMoment B raw27095step3 raw27095step3Labels := by
      have ha : raw27095step3 = -raw27095step2 := by apply Matrix.ext; change ∀ i j, raw27095step3 i j = -(raw27095step2 i j); unfold raw27095step3 raw27095step2; decide +kernel
      have hl : raw27095step3Labels = raw27095step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27095step3 raw27095step3Labels = mixedMoment B raw27095step4 raw27095step4Labels := by
      have ha : raw27095step4 = raw27095step3 := by apply Matrix.ext; unfold raw27095step4 raw27095step3; decide +kernel
      have hl : raw27095step3Labels = labelEmbedding1 ∘ raw27095step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27095step3 raw27095step3Labels raw27095step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2265 node2265Labels := by rfl

theorem canonical27102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27102 raw27102Labels = mixedMoment B node1664 node1664Labels := by
  calc
    mixedMoment B raw27102 raw27102Labels = mixedMoment B raw27102step0 raw27102step0Labels := by
      have ha : raw27102step0 = (fun i j => raw27102 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27102step0 raw27102; decide +kernel
      have hl : raw27102step0Labels = raw27102Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27102 raw27102Labels permutation169 permutation7
    mixedMoment B raw27102step0 raw27102step0Labels = mixedMoment B raw27102step1 raw27102step1Labels := by
      have ha : raw27102step1 = -raw27102step0 := by apply Matrix.ext; change ∀ i j, raw27102step1 i j = -(raw27102step0 i j); unfold raw27102step1 raw27102step0; decide +kernel
      have hl : raw27102step1Labels = raw27102step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27102step1 raw27102step1Labels = mixedMoment B raw27102step2 raw27102step2Labels := by
      have ha : raw27102step2 = raw27102step1 := by apply Matrix.ext; unfold raw27102step2 raw27102step1; decide +kernel
      have hl : raw27102step1Labels = labelEmbedding1 ∘ raw27102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27102step1 raw27102step1Labels raw27102step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1664 node1664Labels := by rfl

theorem canonical27107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27107 raw27107Labels = mixedMoment B node1665 node1665Labels := by
  calc
    mixedMoment B raw27107 raw27107Labels = mixedMoment B raw27107step0 raw27107step0Labels := by
      have ha : raw27107step0 = (fun i j => raw27107 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27107step0 raw27107; decide +kernel
      have hl : raw27107step0Labels = raw27107Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27107 raw27107Labels permutation169 permutation7
    mixedMoment B raw27107step0 raw27107step0Labels = mixedMoment B raw27107step1 raw27107step1Labels := by
      have ha : raw27107step1 = -raw27107step0 := by apply Matrix.ext; change ∀ i j, raw27107step1 i j = -(raw27107step0 i j); unfold raw27107step1 raw27107step0; decide +kernel
      have hl : raw27107step1Labels = raw27107step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27107step1 raw27107step1Labels = mixedMoment B raw27107step2 raw27107step2Labels := by
      have ha : raw27107step2 = raw27107step1 := by apply Matrix.ext; unfold raw27107step2 raw27107step1; decide +kernel
      have hl : raw27107step1Labels = labelEmbedding1 ∘ raw27107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27107step1 raw27107step1Labels raw27107step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1665 node1665Labels := by rfl

theorem canonical27112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27112 raw27112Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw27112 raw27112Labels = mixedMoment B raw27112step0 raw27112step0Labels := by
      have ha : raw27112step0 = (fun i j => raw27112 (permutation175 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27112step0 raw27112; decide +kernel
      have hl : raw27112step0Labels = raw27112Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27112 raw27112Labels permutation175 permutation7
    mixedMoment B raw27112step0 raw27112step0Labels = mixedMoment B raw27112step1 raw27112step1Labels := by
      have ha : raw27112step1 = -raw27112step0 := by apply Matrix.ext; change ∀ i j, raw27112step1 i j = -(raw27112step0 i j); unfold raw27112step1 raw27112step0; decide +kernel
      have hl : raw27112step1Labels = raw27112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27112step1 raw27112step1Labels = mixedMoment B raw27112step2 raw27112step2Labels := by
      have ha : raw27112step2 = raw27112step1 := by apply Matrix.ext; unfold raw27112step2 raw27112step1; decide +kernel
      have hl : raw27112step1Labels = labelEmbedding1 ∘ raw27112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27112step1 raw27112step1Labels raw27112step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

theorem canonical27117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27117 raw27117Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw27117 raw27117Labels = mixedMoment B raw27117step0 raw27117step0Labels := by
      have ha : raw27117step0 = (fun i j => raw27117 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27117step0 raw27117; decide +kernel
      have hl : raw27117step0Labels = raw27117Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27117 raw27117Labels permutation169 permutation7
    mixedMoment B raw27117step0 raw27117step0Labels = mixedMoment B raw27117step1 raw27117step1Labels := by
      have ha : raw27117step1 = -raw27117step0 := by apply Matrix.ext; change ∀ i j, raw27117step1 i j = -(raw27117step0 i j); unfold raw27117step1 raw27117step0; decide +kernel
      have hl : raw27117step1Labels = raw27117step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27117step1 raw27117step1Labels = mixedMoment B raw27117step2 raw27117step2Labels := by
      have ha : raw27117step2 = raw27117step1 := by apply Matrix.ext; unfold raw27117step2 raw27117step1; decide +kernel
      have hl : raw27117step1Labels = labelEmbedding1 ∘ raw27117step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27117step1 raw27117step1Labels raw27117step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

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

theorem canonical27298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27298 raw27298Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw27298 raw27298Labels = mixedMoment B raw27298step0 raw27298step0Labels := by
      have hz : ∀ i, raw27298 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27298step0 = (fun i j => raw27298 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27298step0 raw27298; decide +kernel
      have hl : raw27298step0Labels = (fun j => raw27298Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27298 raw27298Labels permutation6 hz
    mixedMoment B raw27298step0 raw27298step0Labels = mixedMoment B raw27298step1 raw27298step1Labels := by
      have ha : raw27298step1 = (fun i j => raw27298step0 (permutation161 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27298step1 raw27298step0; decide +kernel
      have hl : raw27298step1Labels = raw27298step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27298step0 raw27298step0Labels permutation161 permutation0
    _ = mixedMoment B node4063 node4063Labels := by rfl

theorem canonical27303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27303 raw27303Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw27303 raw27303Labels = mixedMoment B raw27303step0 raw27303step0Labels := by
      have hz : ∀ i, raw27303 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27303step0 = (fun i j => raw27303 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27303step0 raw27303; decide +kernel
      have hl : raw27303step0Labels = (fun j => raw27303Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27303 raw27303Labels permutation6 hz
    mixedMoment B raw27303step0 raw27303step0Labels = mixedMoment B raw27303step1 raw27303step1Labels := by
      have ha : raw27303step1 = (fun i j => raw27303step0 (permutation155 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27303step1 raw27303step0; decide +kernel
      have hl : raw27303step1Labels = raw27303step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27303step0 raw27303step0Labels permutation155 permutation0
    _ = mixedMoment B node4063 node4063Labels := by rfl

theorem canonical27307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27307 raw27307Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw27307 raw27307Labels = mixedMoment B raw27307step0 raw27307step0Labels := by
      have hz : ∀ i, raw27307 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27307step0 = (fun i j => raw27307 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27307step0 raw27307; decide +kernel
      have hl : raw27307step0Labels = (fun j => raw27307Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27307 raw27307Labels permutation6 hz
    mixedMoment B raw27307step0 raw27307step0Labels = mixedMoment B raw27307step1 raw27307step1Labels := by
      have ha : raw27307step1 = (fun i j => raw27307step0 (permutation153 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27307step1 raw27307step0; decide +kernel
      have hl : raw27307step1Labels = raw27307step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27307step0 raw27307step0Labels permutation153 permutation0
    _ = mixedMoment B node4063 node4063Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29381 raw29381Labels = mixedMoment B node2343 node2343Labels := by
  calc
    mixedMoment B raw29381 raw29381Labels = mixedMoment B raw29381step0 raw29381step0Labels := by
      have hz : ∀ j, raw29381 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29381step0 = (fun i j => raw29381 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29381step0 raw29381; decide +kernel
      have hl : raw29381step0Labels = raw29381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29381 raw29381Labels permutation346 hz
    _ = mixedMoment B node2343 node2343Labels := by rfl

theorem canonical29405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29405 raw29405Labels = mixedMoment B node2324 node2324Labels := by
  calc
    mixedMoment B raw29405 raw29405Labels = mixedMoment B raw29405step0 raw29405step0Labels := by
      have ha : raw29405step0 = (fun i j => raw29405 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29405step0 raw29405; decide +kernel
      have hl : raw29405step0Labels = raw29405Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29405 raw29405Labels permutation158 permutation2
    _ = mixedMoment B node2324 node2324Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical230
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29455 raw29455Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw29455 raw29455Labels = mixedMoment B raw29455step0 raw29455step0Labels := by
      have ha : raw29455step0 = (fun i j => raw29455 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29455step0 raw29455; decide +kernel
      have hl : raw29455step0Labels = raw29455Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29455 raw29455Labels permutation686 permutation2
    mixedMoment B raw29455step0 raw29455step0Labels = mixedMoment B raw29455step1 raw29455step1Labels := by
      have ha : raw29455step1 = -raw29455step0 := by apply Matrix.ext; change ∀ i j, raw29455step1 i j = -(raw29455step0 i j); unfold raw29455step1 raw29455step0; decide +kernel
      have hl : raw29455step1Labels = raw29455step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3719 node3719Labels := by rfl

theorem canonical29482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29482 raw29482Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw29482 raw29482Labels = mixedMoment B raw29482step0 raw29482step0Labels := by
      have ha : raw29482step0 = (fun i j => raw29482 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29482step0 raw29482; decide +kernel
      have hl : raw29482step0Labels = raw29482Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29482 raw29482Labels permutation176 permutation2
    _ = mixedMoment B node3779 node3779Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3327 raw3327Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3327 raw3327Labels = mixedMoment B raw3327step0 raw3327step0Labels := by
      have hz : ∀ j, raw3327 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3327step0 = (fun i j => raw3327 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3327step0 raw3327; decide +kernel
      have hl : raw3327step0Labels = raw3327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3327 raw3327Labels permutation434 hz
    mixedMoment B raw3327step0 raw3327step0Labels = mixedMoment B raw3327step1 raw3327step1Labels := by
      have hz : ∀ j, raw3327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3327step1 = (fun i j => raw3327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3327step1 raw3327step0; decide +kernel
      have hl : raw3327step1Labels = raw3327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3327step0 raw3327step0Labels permutation56 hz
    mixedMoment B raw3327step1 raw3327step1Labels = mixedMoment B raw3327step2 raw3327step2Labels := by
      have hz : ∀ i, raw3327step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3327step2 = (fun i j => raw3327step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3327step2 raw3327step1; decide +kernel
      have hl : raw3327step2Labels = (fun j => raw3327step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3327step1 raw3327step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical269
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34498 raw34498Labels = mixedMoment B node3867 node3867Labels := by
  calc
    mixedMoment B raw34498 raw34498Labels = mixedMoment B raw34498step0 raw34498step0Labels := by
      have ha : raw34498step0 = (fun i j => raw34498 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34498step0 raw34498; decide +kernel
      have hl : raw34498step0Labels = raw34498Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34498 raw34498Labels permutation246 permutation7
    mixedMoment B raw34498step0 raw34498step0Labels = mixedMoment B raw34498step1 raw34498step1Labels := by
      have ha : raw34498step1 = -raw34498step0 := by apply Matrix.ext; change ∀ i j, raw34498step1 i j = -(raw34498step0 i j); unfold raw34498step1 raw34498step0; decide +kernel
      have hl : raw34498step1Labels = raw34498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34498step1 raw34498step1Labels = mixedMoment B raw34498step2 raw34498step2Labels := by
      have ha : raw34498step2 = raw34498step1 := by apply Matrix.ext; unfold raw34498step2 raw34498step1; decide +kernel
      have hl : raw34498step1Labels = labelEmbedding1 ∘ raw34498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34498step1 raw34498step1Labels raw34498step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3867 node3867Labels := by rfl

theorem canonical34499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34499 raw34499Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw34499 raw34499Labels = mixedMoment B raw34499step0 raw34499step0Labels := by
      have ha : raw34499step0 = (fun i j => raw34499 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34499step0 raw34499; decide +kernel
      have hl : raw34499step0Labels = raw34499Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34499 raw34499Labels permutation246 permutation7
    mixedMoment B raw34499step0 raw34499step0Labels = mixedMoment B raw34499step1 raw34499step1Labels := by
      have ha : raw34499step1 = -raw34499step0 := by apply Matrix.ext; change ∀ i j, raw34499step1 i j = -(raw34499step0 i j); unfold raw34499step1 raw34499step0; decide +kernel
      have hl : raw34499step1Labels = raw34499step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34499step1 raw34499step1Labels = mixedMoment B raw34499step2 raw34499step2Labels := by
      have ha : raw34499step2 = raw34499step1 := by apply Matrix.ext; unfold raw34499step2 raw34499step1; decide +kernel
      have hl : raw34499step1Labels = labelEmbedding1 ∘ raw34499step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34499step1 raw34499step1Labels raw34499step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical34500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34500 raw34500Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw34500 raw34500Labels = mixedMoment B raw34500step0 raw34500step0Labels := by
      have ha : raw34500step0 = (fun i j => raw34500 (permutation248 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34500step0 raw34500; decide +kernel
      have hl : raw34500step0Labels = raw34500Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34500 raw34500Labels permutation248 permutation7
    mixedMoment B raw34500step0 raw34500step0Labels = mixedMoment B raw34500step1 raw34500step1Labels := by
      have ha : raw34500step1 = -raw34500step0 := by apply Matrix.ext; change ∀ i j, raw34500step1 i j = -(raw34500step0 i j); unfold raw34500step1 raw34500step0; decide +kernel
      have hl : raw34500step1Labels = raw34500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34500step1 raw34500step1Labels = mixedMoment B raw34500step2 raw34500step2Labels := by
      have ha : raw34500step2 = raw34500step1 := by apply Matrix.ext; unfold raw34500step2 raw34500step1; decide +kernel
      have hl : raw34500step1Labels = labelEmbedding1 ∘ raw34500step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34500step1 raw34500step1Labels raw34500step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical34501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34501 raw34501Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw34501 raw34501Labels = mixedMoment B raw34501step0 raw34501step0Labels := by
      have ha : raw34501step0 = (fun i j => raw34501 (permutation250 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34501step0 raw34501; decide +kernel
      have hl : raw34501step0Labels = raw34501Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34501 raw34501Labels permutation250 permutation7
    mixedMoment B raw34501step0 raw34501step0Labels = mixedMoment B raw34501step1 raw34501step1Labels := by
      have ha : raw34501step1 = -raw34501step0 := by apply Matrix.ext; change ∀ i j, raw34501step1 i j = -(raw34501step0 i j); unfold raw34501step1 raw34501step0; decide +kernel
      have hl : raw34501step1Labels = raw34501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34501step1 raw34501step1Labels = mixedMoment B raw34501step2 raw34501step2Labels := by
      have ha : raw34501step2 = raw34501step1 := by apply Matrix.ext; unfold raw34501step2 raw34501step1; decide +kernel
      have hl : raw34501step1Labels = labelEmbedding1 ∘ raw34501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34501step1 raw34501step1Labels raw34501step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical34502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34502 raw34502Labels = mixedMoment B node3844 node3844Labels := by
  calc
    mixedMoment B raw34502 raw34502Labels = mixedMoment B raw34502step0 raw34502step0Labels := by
      have ha : raw34502step0 = (fun i j => raw34502 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34502step0 raw34502; decide +kernel
      have hl : raw34502step0Labels = raw34502Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34502 raw34502Labels permutation246 permutation7
    mixedMoment B raw34502step0 raw34502step0Labels = mixedMoment B raw34502step1 raw34502step1Labels := by
      have ha : raw34502step1 = -raw34502step0 := by apply Matrix.ext; change ∀ i j, raw34502step1 i j = -(raw34502step0 i j); unfold raw34502step1 raw34502step0; decide +kernel
      have hl : raw34502step1Labels = raw34502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34502step1 raw34502step1Labels = mixedMoment B raw34502step2 raw34502step2Labels := by
      have ha : raw34502step2 = raw34502step1 := by apply Matrix.ext; unfold raw34502step2 raw34502step1; decide +kernel
      have hl : raw34502step1Labels = labelEmbedding1 ∘ raw34502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34502step1 raw34502step1Labels raw34502step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3844 node3844Labels := by rfl

theorem canonical34503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34503 raw34503Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw34503 raw34503Labels = mixedMoment B raw34503step0 raw34503step0Labels := by
      have hz : ∀ j, raw34503 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34503step0 = (fun i j => raw34503 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34503step0 raw34503; decide +kernel
      have hl : raw34503step0Labels = raw34503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34503 raw34503Labels permutation265 hz
    mixedMoment B raw34503step0 raw34503step0Labels = mixedMoment B raw34503step1 raw34503step1Labels := by
      have ha : raw34503step1 = (fun i j => raw34503step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34503step1 raw34503step0; decide +kernel
      have hl : raw34503step1Labels = raw34503step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34503step0 raw34503step0Labels permutation50 permutation7
    mixedMoment B raw34503step1 raw34503step1Labels = mixedMoment B raw34503step2 raw34503step2Labels := by
      have ha : raw34503step2 = -raw34503step1 := by apply Matrix.ext; change ∀ i j, raw34503step2 i j = -(raw34503step1 i j); unfold raw34503step2 raw34503step1; decide +kernel
      have hl : raw34503step2Labels = raw34503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34503step2 raw34503step2Labels = mixedMoment B raw34503step3 raw34503step3Labels := by
      have ha : raw34503step3 = raw34503step2 := by apply Matrix.ext; unfold raw34503step3 raw34503step2; decide +kernel
      have hl : raw34503step2Labels = labelEmbedding1 ∘ raw34503step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34503step2 raw34503step2Labels raw34503step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3304 node3304Labels := by rfl

theorem canonical34504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34504 raw34504Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw34504 raw34504Labels = mixedMoment B raw34504step0 raw34504step0Labels := by
      have ha : raw34504step0 = (fun i j => raw34504 (permutation249 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34504step0 raw34504; decide +kernel
      have hl : raw34504step0Labels = raw34504Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34504 raw34504Labels permutation249 permutation7
    mixedMoment B raw34504step0 raw34504step0Labels = mixedMoment B raw34504step1 raw34504step1Labels := by
      have ha : raw34504step1 = -raw34504step0 := by apply Matrix.ext; change ∀ i j, raw34504step1 i j = -(raw34504step0 i j); unfold raw34504step1 raw34504step0; decide +kernel
      have hl : raw34504step1Labels = raw34504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34504step1 raw34504step1Labels = mixedMoment B raw34504step2 raw34504step2Labels := by
      have ha : raw34504step2 = raw34504step1 := by apply Matrix.ext; unfold raw34504step2 raw34504step1; decide +kernel
      have hl : raw34504step1Labels = labelEmbedding1 ∘ raw34504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34504step1 raw34504step1Labels raw34504step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

theorem canonical34505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34505 raw34505Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw34505 raw34505Labels = mixedMoment B raw34505step0 raw34505step0Labels := by
      have ha : raw34505step0 = (fun i j => raw34505 (permutation249 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34505step0 raw34505; decide +kernel
      have hl : raw34505step0Labels = raw34505Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34505 raw34505Labels permutation249 permutation7
    mixedMoment B raw34505step0 raw34505step0Labels = mixedMoment B raw34505step1 raw34505step1Labels := by
      have ha : raw34505step1 = -raw34505step0 := by apply Matrix.ext; change ∀ i j, raw34505step1 i j = -(raw34505step0 i j); unfold raw34505step1 raw34505step0; decide +kernel
      have hl : raw34505step1Labels = raw34505step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34505step1 raw34505step1Labels = mixedMoment B raw34505step2 raw34505step2Labels := by
      have ha : raw34505step2 = raw34505step1 := by apply Matrix.ext; unfold raw34505step2 raw34505step1; decide +kernel
      have hl : raw34505step1Labels = labelEmbedding1 ∘ raw34505step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34505step1 raw34505step1Labels raw34505step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical34506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34506 raw34506Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw34506 raw34506Labels = mixedMoment B raw34506step0 raw34506step0Labels := by
      have ha : raw34506step0 = (fun i j => raw34506 (permutation251 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34506step0 raw34506; decide +kernel
      have hl : raw34506step0Labels = raw34506Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34506 raw34506Labels permutation251 permutation7
    mixedMoment B raw34506step0 raw34506step0Labels = mixedMoment B raw34506step1 raw34506step1Labels := by
      have ha : raw34506step1 = -raw34506step0 := by apply Matrix.ext; change ∀ i j, raw34506step1 i j = -(raw34506step0 i j); unfold raw34506step1 raw34506step0; decide +kernel
      have hl : raw34506step1Labels = raw34506step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34506step1 raw34506step1Labels = mixedMoment B raw34506step2 raw34506step2Labels := by
      have ha : raw34506step2 = raw34506step1 := by apply Matrix.ext; unfold raw34506step2 raw34506step1; decide +kernel
      have hl : raw34506step1Labels = labelEmbedding1 ∘ raw34506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34506step1 raw34506step1Labels raw34506step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical34507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34507 raw34507Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw34507 raw34507Labels = mixedMoment B raw34507step0 raw34507step0Labels := by
      have ha : raw34507step0 = (fun i j => raw34507 (permutation249 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34507step0 raw34507; decide +kernel
      have hl : raw34507step0Labels = raw34507Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34507 raw34507Labels permutation249 permutation7
    mixedMoment B raw34507step0 raw34507step0Labels = mixedMoment B raw34507step1 raw34507step1Labels := by
      have ha : raw34507step1 = -raw34507step0 := by apply Matrix.ext; change ∀ i j, raw34507step1 i j = -(raw34507step0 i j); unfold raw34507step1 raw34507step0; decide +kernel
      have hl : raw34507step1Labels = raw34507step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34507step1 raw34507step1Labels = mixedMoment B raw34507step2 raw34507step2Labels := by
      have ha : raw34507step2 = raw34507step1 := by apply Matrix.ext; unfold raw34507step2 raw34507step1; decide +kernel
      have hl : raw34507step1Labels = labelEmbedding1 ∘ raw34507step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34507step1 raw34507step1Labels raw34507step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

theorem canonical34508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34508 raw34508Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw34508 raw34508Labels = mixedMoment B raw34508step0 raw34508step0Labels := by
      have ha : raw34508step0 = (fun i j => raw34508 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34508step0 raw34508; decide +kernel
      have hl : raw34508step0Labels = raw34508Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34508 raw34508Labels permutation247 permutation7
    mixedMoment B raw34508step0 raw34508step0Labels = mixedMoment B raw34508step1 raw34508step1Labels := by
      have ha : raw34508step1 = -raw34508step0 := by apply Matrix.ext; change ∀ i j, raw34508step1 i j = -(raw34508step0 i j); unfold raw34508step1 raw34508step0; decide +kernel
      have hl : raw34508step1Labels = raw34508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34508step1 raw34508step1Labels = mixedMoment B raw34508step2 raw34508step2Labels := by
      have ha : raw34508step2 = raw34508step1 := by apply Matrix.ext; unfold raw34508step2 raw34508step1; decide +kernel
      have hl : raw34508step1Labels = labelEmbedding1 ∘ raw34508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34508step1 raw34508step1Labels raw34508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

theorem canonical34509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34509 raw34509Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw34509 raw34509Labels = mixedMoment B raw34509step0 raw34509step0Labels := by
      have ha : raw34509step0 = (fun i j => raw34509 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34509step0 raw34509; decide +kernel
      have hl : raw34509step0Labels = raw34509Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34509 raw34509Labels permutation247 permutation7
    mixedMoment B raw34509step0 raw34509step0Labels = mixedMoment B raw34509step1 raw34509step1Labels := by
      have ha : raw34509step1 = -raw34509step0 := by apply Matrix.ext; change ∀ i j, raw34509step1 i j = -(raw34509step0 i j); unfold raw34509step1 raw34509step0; decide +kernel
      have hl : raw34509step1Labels = raw34509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34509step1 raw34509step1Labels = mixedMoment B raw34509step2 raw34509step2Labels := by
      have ha : raw34509step2 = raw34509step1 := by apply Matrix.ext; unfold raw34509step2 raw34509step1; decide +kernel
      have hl : raw34509step1Labels = labelEmbedding1 ∘ raw34509step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34509step1 raw34509step1Labels raw34509step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical34510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34510 raw34510Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw34510 raw34510Labels = mixedMoment B raw34510step0 raw34510step0Labels := by
      have ha : raw34510step0 = (fun i j => raw34510 (permutation250 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34510step0 raw34510; decide +kernel
      have hl : raw34510step0Labels = raw34510Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34510 raw34510Labels permutation250 permutation7
    mixedMoment B raw34510step0 raw34510step0Labels = mixedMoment B raw34510step1 raw34510step1Labels := by
      have ha : raw34510step1 = -raw34510step0 := by apply Matrix.ext; change ∀ i j, raw34510step1 i j = -(raw34510step0 i j); unfold raw34510step1 raw34510step0; decide +kernel
      have hl : raw34510step1Labels = raw34510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34510step1 raw34510step1Labels = mixedMoment B raw34510step2 raw34510step2Labels := by
      have ha : raw34510step2 = raw34510step1 := by apply Matrix.ext; unfold raw34510step2 raw34510step1; decide +kernel
      have hl : raw34510step1Labels = labelEmbedding1 ∘ raw34510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34510step1 raw34510step1Labels raw34510step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical34511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34511 raw34511Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw34511 raw34511Labels = mixedMoment B raw34511step0 raw34511step0Labels := by
      have ha : raw34511step0 = (fun i j => raw34511 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34511step0 raw34511; decide +kernel
      have hl : raw34511step0Labels = raw34511Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34511 raw34511Labels permutation247 permutation7
    mixedMoment B raw34511step0 raw34511step0Labels = mixedMoment B raw34511step1 raw34511step1Labels := by
      have ha : raw34511step1 = -raw34511step0 := by apply Matrix.ext; change ∀ i j, raw34511step1 i j = -(raw34511step0 i j); unfold raw34511step1 raw34511step0; decide +kernel
      have hl : raw34511step1Labels = raw34511step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34511step1 raw34511step1Labels = mixedMoment B raw34511step2 raw34511step2Labels := by
      have ha : raw34511step2 = raw34511step1 := by apply Matrix.ext; unfold raw34511step2 raw34511step1; decide +kernel
      have hl : raw34511step1Labels = labelEmbedding1 ∘ raw34511step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34511step1 raw34511step1Labels raw34511step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

theorem canonical34512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34512 raw34512Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw34512 raw34512Labels = mixedMoment B raw34512step0 raw34512step0Labels := by
      have ha : raw34512step0 = (fun i j => raw34512 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34512step0 raw34512; decide +kernel
      have hl : raw34512step0Labels = raw34512Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34512 raw34512Labels permutation246 permutation7
    mixedMoment B raw34512step0 raw34512step0Labels = mixedMoment B raw34512step1 raw34512step1Labels := by
      have ha : raw34512step1 = -raw34512step0 := by apply Matrix.ext; change ∀ i j, raw34512step1 i j = -(raw34512step0 i j); unfold raw34512step1 raw34512step0; decide +kernel
      have hl : raw34512step1Labels = raw34512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34512step1 raw34512step1Labels = mixedMoment B raw34512step2 raw34512step2Labels := by
      have ha : raw34512step2 = raw34512step1 := by apply Matrix.ext; unfold raw34512step2 raw34512step1; decide +kernel
      have hl : raw34512step1Labels = labelEmbedding1 ∘ raw34512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34512step1 raw34512step1Labels raw34512step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

theorem canonical34513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34513 raw34513Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw34513 raw34513Labels = mixedMoment B raw34513step0 raw34513step0Labels := by
      have ha : raw34513step0 = (fun i j => raw34513 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34513step0 raw34513; decide +kernel
      have hl : raw34513step0Labels = raw34513Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34513 raw34513Labels permutation246 permutation7
    mixedMoment B raw34513step0 raw34513step0Labels = mixedMoment B raw34513step1 raw34513step1Labels := by
      have ha : raw34513step1 = -raw34513step0 := by apply Matrix.ext; change ∀ i j, raw34513step1 i j = -(raw34513step0 i j); unfold raw34513step1 raw34513step0; decide +kernel
      have hl : raw34513step1Labels = raw34513step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34513step1 raw34513step1Labels = mixedMoment B raw34513step2 raw34513step2Labels := by
      have ha : raw34513step2 = raw34513step1 := by apply Matrix.ext; unfold raw34513step2 raw34513step1; decide +kernel
      have hl : raw34513step1Labels = labelEmbedding1 ∘ raw34513step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34513step1 raw34513step1Labels raw34513step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical34514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34514 raw34514Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw34514 raw34514Labels = mixedMoment B raw34514step0 raw34514step0Labels := by
      have ha : raw34514step0 = (fun i j => raw34514 (permutation248 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34514step0 raw34514; decide +kernel
      have hl : raw34514step0Labels = raw34514Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34514 raw34514Labels permutation248 permutation7
    mixedMoment B raw34514step0 raw34514step0Labels = mixedMoment B raw34514step1 raw34514step1Labels := by
      have ha : raw34514step1 = -raw34514step0 := by apply Matrix.ext; change ∀ i j, raw34514step1 i j = -(raw34514step0 i j); unfold raw34514step1 raw34514step0; decide +kernel
      have hl : raw34514step1Labels = raw34514step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34514step1 raw34514step1Labels = mixedMoment B raw34514step2 raw34514step2Labels := by
      have ha : raw34514step2 = raw34514step1 := by apply Matrix.ext; unfold raw34514step2 raw34514step1; decide +kernel
      have hl : raw34514step1Labels = labelEmbedding1 ∘ raw34514step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34514step1 raw34514step1Labels raw34514step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical34515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34515 raw34515Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw34515 raw34515Labels = mixedMoment B raw34515step0 raw34515step0Labels := by
      have ha : raw34515step0 = (fun i j => raw34515 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34515step0 raw34515; decide +kernel
      have hl : raw34515step0Labels = raw34515Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34515 raw34515Labels permutation246 permutation7
    mixedMoment B raw34515step0 raw34515step0Labels = mixedMoment B raw34515step1 raw34515step1Labels := by
      have ha : raw34515step1 = -raw34515step0 := by apply Matrix.ext; change ∀ i j, raw34515step1 i j = -(raw34515step0 i j); unfold raw34515step1 raw34515step0; decide +kernel
      have hl : raw34515step1Labels = raw34515step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34515step1 raw34515step1Labels = mixedMoment B raw34515step2 raw34515step2Labels := by
      have ha : raw34515step2 = raw34515step1 := by apply Matrix.ext; unfold raw34515step2 raw34515step1; decide +kernel
      have hl : raw34515step1Labels = labelEmbedding1 ∘ raw34515step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34515step1 raw34515step1Labels raw34515step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

theorem canonical34516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34516 raw34516Labels = mixedMoment B node2690 node2690Labels := by
  calc
    mixedMoment B raw34516 raw34516Labels = mixedMoment B raw34516step0 raw34516step0Labels := by
      have ha : raw34516step0 = (fun i j => raw34516 (permutation639 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34516step0 raw34516; decide +kernel
      have hl : raw34516step0Labels = raw34516Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34516 raw34516Labels permutation639 permutation5
    mixedMoment B raw34516step0 raw34516step0Labels = mixedMoment B raw34516step1 raw34516step1Labels := by
      have ha : raw34516step1 = raw34516step0 := by apply Matrix.ext; unfold raw34516step1 raw34516step0; decide +kernel
      have hl : raw34516step0Labels = labelEmbedding1 ∘ raw34516step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34516step0 raw34516step0Labels raw34516step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2690 node2690Labels := by rfl

theorem canonical34517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34517 raw34517Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw34517 raw34517Labels = mixedMoment B raw34517step0 raw34517step0Labels := by
      have ha : raw34517step0 = (fun i j => raw34517 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34517step0 raw34517; decide +kernel
      have hl : raw34517step0Labels = raw34517Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34517 raw34517Labels permutation640 permutation5
    mixedMoment B raw34517step0 raw34517step0Labels = mixedMoment B raw34517step1 raw34517step1Labels := by
      have ha : raw34517step1 = raw34517step0 := by apply Matrix.ext; unfold raw34517step1 raw34517step0; decide +kernel
      have hl : raw34517step0Labels = labelEmbedding1 ∘ raw34517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34517step0 raw34517step0Labels raw34517step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical270
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34620 raw34620Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw34620 raw34620Labels = mixedMoment B raw34620step0 raw34620step0Labels := by
      have ha : raw34620step0 = (fun i j => raw34620 (permutation295 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34620step0 raw34620; decide +kernel
      have hl : raw34620step0Labels = raw34620Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34620 raw34620Labels permutation295 permutation5
    mixedMoment B raw34620step0 raw34620step0Labels = mixedMoment B raw34620step1 raw34620step1Labels := by
      have ha : raw34620step1 = -raw34620step0 := by apply Matrix.ext; change ∀ i j, raw34620step1 i j = -(raw34620step0 i j); unfold raw34620step1 raw34620step0; decide +kernel
      have hl : raw34620step1Labels = raw34620step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34620step1 raw34620step1Labels = mixedMoment B raw34620step2 raw34620step2Labels := by
      have ha : raw34620step2 = raw34620step1 := by apply Matrix.ext; unfold raw34620step2 raw34620step1; decide +kernel
      have hl : raw34620step1Labels = labelEmbedding1 ∘ raw34620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34620step1 raw34620step1Labels raw34620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2747 node2747Labels := by rfl

theorem canonical34621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34621 raw34621Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw34621 raw34621Labels = mixedMoment B raw34621step0 raw34621step0Labels := by
      have ha : raw34621step0 = (fun i j => raw34621 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34621step0 raw34621; decide +kernel
      have hl : raw34621step0Labels = raw34621Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34621 raw34621Labels permutation241 permutation7
    mixedMoment B raw34621step0 raw34621step0Labels = mixedMoment B raw34621step1 raw34621step1Labels := by
      have ha : raw34621step1 = -raw34621step0 := by apply Matrix.ext; change ∀ i j, raw34621step1 i j = -(raw34621step0 i j); unfold raw34621step1 raw34621step0; decide +kernel
      have hl : raw34621step1Labels = raw34621step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34621step1 raw34621step1Labels = mixedMoment B raw34621step2 raw34621step2Labels := by
      have ha : raw34621step2 = raw34621step1 := by apply Matrix.ext; unfold raw34621step2 raw34621step1; decide +kernel
      have hl : raw34621step1Labels = labelEmbedding1 ∘ raw34621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34621step1 raw34621step1Labels raw34621step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical34622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34622 raw34622Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw34622 raw34622Labels = mixedMoment B raw34622step0 raw34622step0Labels := by
      have hz : ∀ j, raw34622 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34622step0 = (fun i j => raw34622 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34622step0 raw34622; decide +kernel
      have hl : raw34622step0Labels = raw34622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34622 raw34622Labels permutation520 hz
    mixedMoment B raw34622step0 raw34622step0Labels = mixedMoment B raw34622step1 raw34622step1Labels := by
      have ha : raw34622step1 = (fun i j => raw34622step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34622step1 raw34622step0; decide +kernel
      have hl : raw34622step1Labels = raw34622step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34622step0 raw34622step0Labels permutation50 permutation7
    mixedMoment B raw34622step1 raw34622step1Labels = mixedMoment B raw34622step2 raw34622step2Labels := by
      have ha : raw34622step2 = -raw34622step1 := by apply Matrix.ext; change ∀ i j, raw34622step2 i j = -(raw34622step1 i j); unfold raw34622step2 raw34622step1; decide +kernel
      have hl : raw34622step2Labels = raw34622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34622step2 raw34622step2Labels = mixedMoment B raw34622step3 raw34622step3Labels := by
      have ha : raw34622step3 = raw34622step2 := by apply Matrix.ext; unfold raw34622step3 raw34622step2; decide +kernel
      have hl : raw34622step2Labels = labelEmbedding1 ∘ raw34622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34622step2 raw34622step2Labels raw34622step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical34623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34623 raw34623Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw34623 raw34623Labels = mixedMoment B raw34623step0 raw34623step0Labels := by
      have hz : ∀ j, raw34623 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34623step0 = (fun i j => raw34623 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34623step0 raw34623; decide +kernel
      have hl : raw34623step0Labels = raw34623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34623 raw34623Labels permutation590 hz
    mixedMoment B raw34623step0 raw34623step0Labels = mixedMoment B raw34623step1 raw34623step1Labels := by
      have ha : raw34623step1 = (fun i j => raw34623step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34623step1 raw34623step0; decide +kernel
      have hl : raw34623step1Labels = raw34623step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34623step0 raw34623step0Labels permutation50 permutation7
    mixedMoment B raw34623step1 raw34623step1Labels = mixedMoment B raw34623step2 raw34623step2Labels := by
      have ha : raw34623step2 = -raw34623step1 := by apply Matrix.ext; change ∀ i j, raw34623step2 i j = -(raw34623step1 i j); unfold raw34623step2 raw34623step1; decide +kernel
      have hl : raw34623step2Labels = raw34623step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34623step2 raw34623step2Labels = mixedMoment B raw34623step3 raw34623step3Labels := by
      have ha : raw34623step3 = raw34623step2 := by apply Matrix.ext; unfold raw34623step3 raw34623step2; decide +kernel
      have hl : raw34623step2Labels = labelEmbedding1 ∘ raw34623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34623step2 raw34623step2Labels raw34623step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical34624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34624 raw34624Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw34624 raw34624Labels = mixedMoment B raw34624step0 raw34624step0Labels := by
      have ha : raw34624step0 = (fun i j => raw34624 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34624step0 raw34624; decide +kernel
      have hl : raw34624step0Labels = raw34624Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34624 raw34624Labels permutation241 permutation7
    mixedMoment B raw34624step0 raw34624step0Labels = mixedMoment B raw34624step1 raw34624step1Labels := by
      have ha : raw34624step1 = -raw34624step0 := by apply Matrix.ext; change ∀ i j, raw34624step1 i j = -(raw34624step0 i j); unfold raw34624step1 raw34624step0; decide +kernel
      have hl : raw34624step1Labels = raw34624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34624step1 raw34624step1Labels = mixedMoment B raw34624step2 raw34624step2Labels := by
      have ha : raw34624step2 = raw34624step1 := by apply Matrix.ext; unfold raw34624step2 raw34624step1; decide +kernel
      have hl : raw34624step1Labels = labelEmbedding1 ∘ raw34624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34624step1 raw34624step1Labels raw34624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

theorem canonical34625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34625 raw34625Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw34625 raw34625Labels = mixedMoment B raw34625step0 raw34625step0Labels := by
      have ha : raw34625step0 = (fun i j => raw34625 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34625step0 raw34625; decide +kernel
      have hl : raw34625step0Labels = raw34625Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34625 raw34625Labels permutation241 permutation7
    mixedMoment B raw34625step0 raw34625step0Labels = mixedMoment B raw34625step1 raw34625step1Labels := by
      have ha : raw34625step1 = -raw34625step0 := by apply Matrix.ext; change ∀ i j, raw34625step1 i j = -(raw34625step0 i j); unfold raw34625step1 raw34625step0; decide +kernel
      have hl : raw34625step1Labels = raw34625step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34625step1 raw34625step1Labels = mixedMoment B raw34625step2 raw34625step2Labels := by
      have ha : raw34625step2 = raw34625step1 := by apply Matrix.ext; unfold raw34625step2 raw34625step1; decide +kernel
      have hl : raw34625step1Labels = labelEmbedding1 ∘ raw34625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34625step1 raw34625step1Labels raw34625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical34626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34626 raw34626Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw34626 raw34626Labels = mixedMoment B raw34626step0 raw34626step0Labels := by
      have hz : ∀ j, raw34626 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34626step0 = (fun i j => raw34626 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34626step0 raw34626; decide +kernel
      have hl : raw34626step0Labels = raw34626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34626 raw34626Labels permutation520 hz
    mixedMoment B raw34626step0 raw34626step0Labels = mixedMoment B raw34626step1 raw34626step1Labels := by
      have ha : raw34626step1 = (fun i j => raw34626step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34626step1 raw34626step0; decide +kernel
      have hl : raw34626step1Labels = raw34626step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34626step0 raw34626step0Labels permutation51 permutation7
    mixedMoment B raw34626step1 raw34626step1Labels = mixedMoment B raw34626step2 raw34626step2Labels := by
      have ha : raw34626step2 = -raw34626step1 := by apply Matrix.ext; change ∀ i j, raw34626step2 i j = -(raw34626step1 i j); unfold raw34626step2 raw34626step1; decide +kernel
      have hl : raw34626step2Labels = raw34626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34626step2 raw34626step2Labels = mixedMoment B raw34626step3 raw34626step3Labels := by
      have ha : raw34626step3 = raw34626step2 := by apply Matrix.ext; unfold raw34626step3 raw34626step2; decide +kernel
      have hl : raw34626step2Labels = labelEmbedding1 ∘ raw34626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34626step2 raw34626step2Labels raw34626step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical34627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34627 raw34627Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw34627 raw34627Labels = mixedMoment B raw34627step0 raw34627step0Labels := by
      have hz : ∀ j, raw34627 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34627step0 = (fun i j => raw34627 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34627step0 raw34627; decide +kernel
      have hl : raw34627step0Labels = raw34627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34627 raw34627Labels permutation590 hz
    mixedMoment B raw34627step0 raw34627step0Labels = mixedMoment B raw34627step1 raw34627step1Labels := by
      have ha : raw34627step1 = (fun i j => raw34627step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34627step1 raw34627step0; decide +kernel
      have hl : raw34627step1Labels = raw34627step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34627step0 raw34627step0Labels permutation51 permutation7
    mixedMoment B raw34627step1 raw34627step1Labels = mixedMoment B raw34627step2 raw34627step2Labels := by
      have ha : raw34627step2 = -raw34627step1 := by apply Matrix.ext; change ∀ i j, raw34627step2 i j = -(raw34627step1 i j); unfold raw34627step2 raw34627step1; decide +kernel
      have hl : raw34627step2Labels = raw34627step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34627step2 raw34627step2Labels = mixedMoment B raw34627step3 raw34627step3Labels := by
      have ha : raw34627step3 = raw34627step2 := by apply Matrix.ext; unfold raw34627step3 raw34627step2; decide +kernel
      have hl : raw34627step2Labels = labelEmbedding1 ∘ raw34627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34627step2 raw34627step2Labels raw34627step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical34628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34628 raw34628Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw34628 raw34628Labels = mixedMoment B raw34628step0 raw34628step0Labels := by
      have ha : raw34628step0 = (fun i j => raw34628 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34628step0 raw34628; decide +kernel
      have hl : raw34628step0Labels = raw34628Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34628 raw34628Labels permutation240 permutation7
    mixedMoment B raw34628step0 raw34628step0Labels = mixedMoment B raw34628step1 raw34628step1Labels := by
      have ha : raw34628step1 = -raw34628step0 := by apply Matrix.ext; change ∀ i j, raw34628step1 i j = -(raw34628step0 i j); unfold raw34628step1 raw34628step0; decide +kernel
      have hl : raw34628step1Labels = raw34628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34628step1 raw34628step1Labels = mixedMoment B raw34628step2 raw34628step2Labels := by
      have ha : raw34628step2 = raw34628step1 := by apply Matrix.ext; unfold raw34628step2 raw34628step1; decide +kernel
      have hl : raw34628step1Labels = labelEmbedding1 ∘ raw34628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34628step1 raw34628step1Labels raw34628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

theorem canonical34629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34629 raw34629Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw34629 raw34629Labels = mixedMoment B raw34629step0 raw34629step0Labels := by
      have hz : ∀ j, raw34629 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34629step0 = (fun i j => raw34629 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34629step0 raw34629; decide +kernel
      have hl : raw34629step0Labels = raw34629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34629 raw34629Labels permutation520 hz
    mixedMoment B raw34629step0 raw34629step0Labels = mixedMoment B raw34629step1 raw34629step1Labels := by
      have ha : raw34629step1 = (fun i j => raw34629step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34629step1 raw34629step0; decide +kernel
      have hl : raw34629step1Labels = raw34629step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34629step0 raw34629step0Labels permutation50 permutation7
    mixedMoment B raw34629step1 raw34629step1Labels = mixedMoment B raw34629step2 raw34629step2Labels := by
      have ha : raw34629step2 = -raw34629step1 := by apply Matrix.ext; change ∀ i j, raw34629step2 i j = -(raw34629step1 i j); unfold raw34629step2 raw34629step1; decide +kernel
      have hl : raw34629step2Labels = raw34629step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34629step2 raw34629step2Labels = mixedMoment B raw34629step3 raw34629step3Labels := by
      have ha : raw34629step3 = raw34629step2 := by apply Matrix.ext; unfold raw34629step3 raw34629step2; decide +kernel
      have hl : raw34629step2Labels = labelEmbedding1 ∘ raw34629step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34629step2 raw34629step2Labels raw34629step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical34630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34630 raw34630Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw34630 raw34630Labels = mixedMoment B raw34630step0 raw34630step0Labels := by
      have hz : ∀ j, raw34630 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34630step0 = (fun i j => raw34630 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34630step0 raw34630; decide +kernel
      have hl : raw34630step0Labels = raw34630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34630 raw34630Labels permutation590 hz
    mixedMoment B raw34630step0 raw34630step0Labels = mixedMoment B raw34630step1 raw34630step1Labels := by
      have ha : raw34630step1 = (fun i j => raw34630step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34630step1 raw34630step0; decide +kernel
      have hl : raw34630step1Labels = raw34630step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34630step0 raw34630step0Labels permutation50 permutation7
    mixedMoment B raw34630step1 raw34630step1Labels = mixedMoment B raw34630step2 raw34630step2Labels := by
      have ha : raw34630step2 = -raw34630step1 := by apply Matrix.ext; change ∀ i j, raw34630step2 i j = -(raw34630step1 i j); unfold raw34630step2 raw34630step1; decide +kernel
      have hl : raw34630step2Labels = raw34630step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34630step2 raw34630step2Labels = mixedMoment B raw34630step3 raw34630step3Labels := by
      have ha : raw34630step3 = raw34630step2 := by apply Matrix.ext; unfold raw34630step3 raw34630step2; decide +kernel
      have hl : raw34630step2Labels = labelEmbedding1 ∘ raw34630step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34630step2 raw34630step2Labels raw34630step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical34631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34631 raw34631Labels = mixedMoment B node2248 node2248Labels := by
  calc
    mixedMoment B raw34631 raw34631Labels = mixedMoment B raw34631step0 raw34631step0Labels := by
      have ha : raw34631step0 = (fun i j => raw34631 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34631step0 raw34631; decide +kernel
      have hl : raw34631step0Labels = raw34631Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34631 raw34631Labels permutation260 permutation7
    mixedMoment B raw34631step0 raw34631step0Labels = mixedMoment B raw34631step1 raw34631step1Labels := by
      have ha : raw34631step1 = -raw34631step0 := by apply Matrix.ext; change ∀ i j, raw34631step1 i j = -(raw34631step0 i j); unfold raw34631step1 raw34631step0; decide +kernel
      have hl : raw34631step1Labels = raw34631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34631step1 raw34631step1Labels = mixedMoment B raw34631step2 raw34631step2Labels := by
      have ha : raw34631step2 = raw34631step1 := by apply Matrix.ext; unfold raw34631step2 raw34631step1; decide +kernel
      have hl : raw34631step1Labels = labelEmbedding1 ∘ raw34631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34631step1 raw34631step1Labels raw34631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2248 node2248Labels := by rfl

theorem canonical34632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34632 raw34632Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw34632 raw34632Labels = mixedMoment B raw34632step0 raw34632step0Labels := by
      have ha : raw34632step0 = (fun i j => raw34632 (permutation261 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34632step0 raw34632; decide +kernel
      have hl : raw34632step0Labels = raw34632Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34632 raw34632Labels permutation261 permutation7
    mixedMoment B raw34632step0 raw34632step0Labels = mixedMoment B raw34632step1 raw34632step1Labels := by
      have ha : raw34632step1 = -raw34632step0 := by apply Matrix.ext; change ∀ i j, raw34632step1 i j = -(raw34632step0 i j); unfold raw34632step1 raw34632step0; decide +kernel
      have hl : raw34632step1Labels = raw34632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34632step1 raw34632step1Labels = mixedMoment B raw34632step2 raw34632step2Labels := by
      have ha : raw34632step2 = raw34632step1 := by apply Matrix.ext; unfold raw34632step2 raw34632step1; decide +kernel
      have hl : raw34632step1Labels = labelEmbedding1 ∘ raw34632step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34632step1 raw34632step1Labels raw34632step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical34633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34633 raw34633Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw34633 raw34633Labels = mixedMoment B raw34633step0 raw34633step0Labels := by
      have hz : ∀ j, raw34633 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34633step0 = (fun i j => raw34633 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34633step0 raw34633; decide +kernel
      have hl : raw34633step0Labels = raw34633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34633 raw34633Labels permutation590 hz
    mixedMoment B raw34633step0 raw34633step0Labels = mixedMoment B raw34633step1 raw34633step1Labels := by
      have ha : raw34633step1 = (fun i j => raw34633step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34633step1 raw34633step0; decide +kernel
      have hl : raw34633step1Labels = raw34633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34633step0 raw34633step0Labels permutation50 permutation7
    mixedMoment B raw34633step1 raw34633step1Labels = mixedMoment B raw34633step2 raw34633step2Labels := by
      have ha : raw34633step2 = -raw34633step1 := by apply Matrix.ext; change ∀ i j, raw34633step2 i j = -(raw34633step1 i j); unfold raw34633step2 raw34633step1; decide +kernel
      have hl : raw34633step2Labels = raw34633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34633step2 raw34633step2Labels = mixedMoment B raw34633step3 raw34633step3Labels := by
      have ha : raw34633step3 = raw34633step2 := by apply Matrix.ext; unfold raw34633step3 raw34633step2; decide +kernel
      have hl : raw34633step2Labels = labelEmbedding1 ∘ raw34633step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34633step2 raw34633step2Labels raw34633step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

theorem canonical34634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34634 raw34634Labels = mixedMoment B node2248 node2248Labels := by
  calc
    mixedMoment B raw34634 raw34634Labels = mixedMoment B raw34634step0 raw34634step0Labels := by
      have ha : raw34634step0 = (fun i j => raw34634 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34634step0 raw34634; decide +kernel
      have hl : raw34634step0Labels = raw34634Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34634 raw34634Labels permutation240 permutation7
    mixedMoment B raw34634step0 raw34634step0Labels = mixedMoment B raw34634step1 raw34634step1Labels := by
      have ha : raw34634step1 = -raw34634step0 := by apply Matrix.ext; change ∀ i j, raw34634step1 i j = -(raw34634step0 i j); unfold raw34634step1 raw34634step0; decide +kernel
      have hl : raw34634step1Labels = raw34634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34634step1 raw34634step1Labels = mixedMoment B raw34634step2 raw34634step2Labels := by
      have ha : raw34634step2 = raw34634step1 := by apply Matrix.ext; unfold raw34634step2 raw34634step1; decide +kernel
      have hl : raw34634step1Labels = labelEmbedding1 ∘ raw34634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34634step1 raw34634step1Labels raw34634step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2248 node2248Labels := by rfl

theorem canonical34635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34635 raw34635Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw34635 raw34635Labels = mixedMoment B raw34635step0 raw34635step0Labels := by
      have hz : ∀ j, raw34635 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34635step0 = (fun i j => raw34635 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34635step0 raw34635; decide +kernel
      have hl : raw34635step0Labels = raw34635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34635 raw34635Labels permutation520 hz
    mixedMoment B raw34635step0 raw34635step0Labels = mixedMoment B raw34635step1 raw34635step1Labels := by
      have ha : raw34635step1 = (fun i j => raw34635step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34635step1 raw34635step0; decide +kernel
      have hl : raw34635step1Labels = raw34635step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34635step0 raw34635step0Labels permutation50 permutation7
    mixedMoment B raw34635step1 raw34635step1Labels = mixedMoment B raw34635step2 raw34635step2Labels := by
      have ha : raw34635step2 = -raw34635step1 := by apply Matrix.ext; change ∀ i j, raw34635step2 i j = -(raw34635step1 i j); unfold raw34635step2 raw34635step1; decide +kernel
      have hl : raw34635step2Labels = raw34635step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34635step2 raw34635step2Labels = mixedMoment B raw34635step3 raw34635step3Labels := by
      have ha : raw34635step3 = raw34635step2 := by apply Matrix.ext; unfold raw34635step3 raw34635step2; decide +kernel
      have hl : raw34635step2Labels = labelEmbedding1 ∘ raw34635step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34635step2 raw34635step2Labels raw34635step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

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

theorem canonical34702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34702 raw34702Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw34702 raw34702Labels = mixedMoment B raw34702step0 raw34702step0Labels := by
      have ha : raw34702step0 = (fun i j => raw34702 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34702step0 raw34702; decide +kernel
      have hl : raw34702step0Labels = raw34702Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34702 raw34702Labels permutation169 permutation7
    mixedMoment B raw34702step0 raw34702step0Labels = mixedMoment B raw34702step1 raw34702step1Labels := by
      have ha : raw34702step1 = -raw34702step0 := by apply Matrix.ext; change ∀ i j, raw34702step1 i j = -(raw34702step0 i j); unfold raw34702step1 raw34702step0; decide +kernel
      have hl : raw34702step1Labels = raw34702step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34702step1 raw34702step1Labels = mixedMoment B raw34702step2 raw34702step2Labels := by
      have ha : raw34702step2 = raw34702step1 := by apply Matrix.ext; unfold raw34702step2 raw34702step1; decide +kernel
      have hl : raw34702step1Labels = labelEmbedding1 ∘ raw34702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34702step1 raw34702step1Labels raw34702step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2662 node2662Labels := by rfl

theorem canonical34703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34703 raw34703Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw34703 raw34703Labels = mixedMoment B raw34703step0 raw34703step0Labels := by
      have ha : raw34703step0 = (fun i j => raw34703 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34703step0 raw34703; decide +kernel
      have hl : raw34703step0Labels = raw34703Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34703 raw34703Labels permutation169 permutation7
    mixedMoment B raw34703step0 raw34703step0Labels = mixedMoment B raw34703step1 raw34703step1Labels := by
      have ha : raw34703step1 = -raw34703step0 := by apply Matrix.ext; change ∀ i j, raw34703step1 i j = -(raw34703step0 i j); unfold raw34703step1 raw34703step0; decide +kernel
      have hl : raw34703step1Labels = raw34703step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34703step1 raw34703step1Labels = mixedMoment B raw34703step2 raw34703step2Labels := by
      have ha : raw34703step2 = raw34703step1 := by apply Matrix.ext; unfold raw34703step2 raw34703step1; decide +kernel
      have hl : raw34703step1Labels = labelEmbedding1 ∘ raw34703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34703step1 raw34703step1Labels raw34703step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2710 node2710Labels := by rfl

theorem canonical34704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34704 raw34704Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw34704 raw34704Labels = mixedMoment B raw34704step0 raw34704step0Labels := by
      have ha : raw34704step0 = (fun i j => raw34704 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34704step0 raw34704; decide +kernel
      have hl : raw34704step0Labels = raw34704Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34704 raw34704Labels permutation169 permutation7
    mixedMoment B raw34704step0 raw34704step0Labels = mixedMoment B raw34704step1 raw34704step1Labels := by
      have ha : raw34704step1 = -raw34704step0 := by apply Matrix.ext; change ∀ i j, raw34704step1 i j = -(raw34704step0 i j); unfold raw34704step1 raw34704step0; decide +kernel
      have hl : raw34704step1Labels = raw34704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34704step1 raw34704step1Labels = mixedMoment B raw34704step2 raw34704step2Labels := by
      have ha : raw34704step2 = raw34704step1 := by apply Matrix.ext; unfold raw34704step2 raw34704step1; decide +kernel
      have hl : raw34704step1Labels = labelEmbedding1 ∘ raw34704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34704step1 raw34704step1Labels raw34704step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2709 node2709Labels := by rfl

theorem canonical34705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34705 raw34705Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw34705 raw34705Labels = mixedMoment B raw34705step0 raw34705step0Labels := by
      have hz : ∀ j, raw34705 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34705step0 = (fun i j => raw34705 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34705step0 raw34705; decide +kernel
      have hl : raw34705step0Labels = raw34705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34705 raw34705Labels permutation520 hz
    mixedMoment B raw34705step0 raw34705step0Labels = mixedMoment B raw34705step1 raw34705step1Labels := by
      have ha : raw34705step1 = (fun i j => raw34705step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34705step1 raw34705step0; decide +kernel
      have hl : raw34705step1Labels = raw34705step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34705step0 raw34705step0Labels permutation37 permutation7
    mixedMoment B raw34705step1 raw34705step1Labels = mixedMoment B raw34705step2 raw34705step2Labels := by
      have ha : raw34705step2 = -raw34705step1 := by apply Matrix.ext; change ∀ i j, raw34705step2 i j = -(raw34705step1 i j); unfold raw34705step2 raw34705step1; decide +kernel
      have hl : raw34705step2Labels = raw34705step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34705step2 raw34705step2Labels = mixedMoment B raw34705step3 raw34705step3Labels := by
      have ha : raw34705step3 = raw34705step2 := by apply Matrix.ext; unfold raw34705step3 raw34705step2; decide +kernel
      have hl : raw34705step2Labels = labelEmbedding1 ∘ raw34705step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34705step2 raw34705step2Labels raw34705step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical34706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34706 raw34706Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw34706 raw34706Labels = mixedMoment B raw34706step0 raw34706step0Labels := by
      have hz : ∀ j, raw34706 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34706step0 = (fun i j => raw34706 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34706step0 raw34706; decide +kernel
      have hl : raw34706step0Labels = raw34706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34706 raw34706Labels permutation590 hz
    mixedMoment B raw34706step0 raw34706step0Labels = mixedMoment B raw34706step1 raw34706step1Labels := by
      have ha : raw34706step1 = (fun i j => raw34706step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34706step1 raw34706step0; decide +kernel
      have hl : raw34706step1Labels = raw34706step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34706step0 raw34706step0Labels permutation37 permutation7
    mixedMoment B raw34706step1 raw34706step1Labels = mixedMoment B raw34706step2 raw34706step2Labels := by
      have ha : raw34706step2 = -raw34706step1 := by apply Matrix.ext; change ∀ i j, raw34706step2 i j = -(raw34706step1 i j); unfold raw34706step2 raw34706step1; decide +kernel
      have hl : raw34706step2Labels = raw34706step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34706step2 raw34706step2Labels = mixedMoment B raw34706step3 raw34706step3Labels := by
      have ha : raw34706step3 = raw34706step2 := by apply Matrix.ext; unfold raw34706step3 raw34706step2; decide +kernel
      have hl : raw34706step2Labels = labelEmbedding1 ∘ raw34706step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34706step2 raw34706step2Labels raw34706step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical34707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34707 raw34707Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw34707 raw34707Labels = mixedMoment B raw34707step0 raw34707step0Labels := by
      have hz : ∀ j, raw34707 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34707step0 = (fun i j => raw34707 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34707step0 raw34707; decide +kernel
      have hl : raw34707step0Labels = raw34707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34707 raw34707Labels permutation265 hz
    mixedMoment B raw34707step0 raw34707step0Labels = mixedMoment B raw34707step1 raw34707step1Labels := by
      have ha : raw34707step1 = (fun i j => raw34707step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34707step1 raw34707step0; decide +kernel
      have hl : raw34707step1Labels = raw34707step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34707step0 raw34707step0Labels permutation49 permutation7
    mixedMoment B raw34707step1 raw34707step1Labels = mixedMoment B raw34707step2 raw34707step2Labels := by
      have ha : raw34707step2 = -raw34707step1 := by apply Matrix.ext; change ∀ i j, raw34707step2 i j = -(raw34707step1 i j); unfold raw34707step2 raw34707step1; decide +kernel
      have hl : raw34707step2Labels = raw34707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34707step2 raw34707step2Labels = mixedMoment B raw34707step3 raw34707step3Labels := by
      have ha : raw34707step3 = raw34707step2 := by apply Matrix.ext; unfold raw34707step3 raw34707step2; decide +kernel
      have hl : raw34707step2Labels = labelEmbedding1 ∘ raw34707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34707step2 raw34707step2Labels raw34707step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical34708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34708 raw34708Labels = mixedMoment B node2141 node2141Labels := by
  calc
    mixedMoment B raw34708 raw34708Labels = mixedMoment B raw34708step0 raw34708step0Labels := by
      have ha : raw34708step0 = (fun i j => raw34708 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34708step0 raw34708; decide +kernel
      have hl : raw34708step0Labels = raw34708Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34708 raw34708Labels permutation169 permutation7
    mixedMoment B raw34708step0 raw34708step0Labels = mixedMoment B raw34708step1 raw34708step1Labels := by
      have ha : raw34708step1 = -raw34708step0 := by apply Matrix.ext; change ∀ i j, raw34708step1 i j = -(raw34708step0 i j); unfold raw34708step1 raw34708step0; decide +kernel
      have hl : raw34708step1Labels = raw34708step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34708step1 raw34708step1Labels = mixedMoment B raw34708step2 raw34708step2Labels := by
      have ha : raw34708step2 = raw34708step1 := by apply Matrix.ext; unfold raw34708step2 raw34708step1; decide +kernel
      have hl : raw34708step1Labels = labelEmbedding1 ∘ raw34708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34708step1 raw34708step1Labels raw34708step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2141 node2141Labels := by rfl

theorem canonical34709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34709 raw34709Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw34709 raw34709Labels = mixedMoment B raw34709step0 raw34709step0Labels := by
      have ha : raw34709step0 = (fun i j => raw34709 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34709step0 raw34709; decide +kernel
      have hl : raw34709step0Labels = raw34709Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34709 raw34709Labels permutation169 permutation7
    mixedMoment B raw34709step0 raw34709step0Labels = mixedMoment B raw34709step1 raw34709step1Labels := by
      have ha : raw34709step1 = -raw34709step0 := by apply Matrix.ext; change ∀ i j, raw34709step1 i j = -(raw34709step0 i j); unfold raw34709step1 raw34709step0; decide +kernel
      have hl : raw34709step1Labels = raw34709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34709step1 raw34709step1Labels = mixedMoment B raw34709step2 raw34709step2Labels := by
      have ha : raw34709step2 = raw34709step1 := by apply Matrix.ext; unfold raw34709step2 raw34709step1; decide +kernel
      have hl : raw34709step1Labels = labelEmbedding1 ∘ raw34709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34709step1 raw34709step1Labels raw34709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

theorem canonical34710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34710 raw34710Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw34710 raw34710Labels = mixedMoment B raw34710step0 raw34710step0Labels := by
      have hz : ∀ j, raw34710 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34710step0 = (fun i j => raw34710 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34710step0 raw34710; decide +kernel
      have hl : raw34710step0Labels = raw34710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34710 raw34710Labels permutation520 hz
    mixedMoment B raw34710step0 raw34710step0Labels = mixedMoment B raw34710step1 raw34710step1Labels := by
      have ha : raw34710step1 = (fun i j => raw34710step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34710step1 raw34710step0; decide +kernel
      have hl : raw34710step1Labels = raw34710step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34710step0 raw34710step0Labels permutation37 permutation7
    mixedMoment B raw34710step1 raw34710step1Labels = mixedMoment B raw34710step2 raw34710step2Labels := by
      have ha : raw34710step2 = -raw34710step1 := by apply Matrix.ext; change ∀ i j, raw34710step2 i j = -(raw34710step1 i j); unfold raw34710step2 raw34710step1; decide +kernel
      have hl : raw34710step2Labels = raw34710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34710step2 raw34710step2Labels = mixedMoment B raw34710step3 raw34710step3Labels := by
      have ha : raw34710step3 = raw34710step2 := by apply Matrix.ext; unfold raw34710step3 raw34710step2; decide +kernel
      have hl : raw34710step2Labels = labelEmbedding1 ∘ raw34710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34710step2 raw34710step2Labels raw34710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical34711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34711 raw34711Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw34711 raw34711Labels = mixedMoment B raw34711step0 raw34711step0Labels := by
      have hz : ∀ j, raw34711 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34711step0 = (fun i j => raw34711 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34711step0 raw34711; decide +kernel
      have hl : raw34711step0Labels = raw34711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34711 raw34711Labels permutation590 hz
    mixedMoment B raw34711step0 raw34711step0Labels = mixedMoment B raw34711step1 raw34711step1Labels := by
      have ha : raw34711step1 = (fun i j => raw34711step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34711step1 raw34711step0; decide +kernel
      have hl : raw34711step1Labels = raw34711step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34711step0 raw34711step0Labels permutation37 permutation7
    mixedMoment B raw34711step1 raw34711step1Labels = mixedMoment B raw34711step2 raw34711step2Labels := by
      have ha : raw34711step2 = -raw34711step1 := by apply Matrix.ext; change ∀ i j, raw34711step2 i j = -(raw34711step1 i j); unfold raw34711step2 raw34711step1; decide +kernel
      have hl : raw34711step2Labels = raw34711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34711step2 raw34711step2Labels = mixedMoment B raw34711step3 raw34711step3Labels := by
      have ha : raw34711step3 = raw34711step2 := by apply Matrix.ext; unfold raw34711step3 raw34711step2; decide +kernel
      have hl : raw34711step2Labels = labelEmbedding1 ∘ raw34711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34711step2 raw34711step2Labels raw34711step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical34712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34712 raw34712Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw34712 raw34712Labels = mixedMoment B raw34712step0 raw34712step0Labels := by
      have ha : raw34712step0 = (fun i j => raw34712 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34712step0 raw34712; decide +kernel
      have hl : raw34712step0Labels = raw34712Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34712 raw34712Labels permutation169 permutation7
    mixedMoment B raw34712step0 raw34712step0Labels = mixedMoment B raw34712step1 raw34712step1Labels := by
      have ha : raw34712step1 = -raw34712step0 := by apply Matrix.ext; change ∀ i j, raw34712step1 i j = -(raw34712step0 i j); unfold raw34712step1 raw34712step0; decide +kernel
      have hl : raw34712step1Labels = raw34712step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34712step1 raw34712step1Labels = mixedMoment B raw34712step2 raw34712step2Labels := by
      have ha : raw34712step2 = raw34712step1 := by apply Matrix.ext; unfold raw34712step2 raw34712step1; decide +kernel
      have hl : raw34712step1Labels = labelEmbedding1 ∘ raw34712step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34712step1 raw34712step1Labels raw34712step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

theorem canonical34713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34713 raw34713Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw34713 raw34713Labels = mixedMoment B raw34713step0 raw34713step0Labels := by
      have ha : raw34713step0 = (fun i j => raw34713 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34713step0 raw34713; decide +kernel
      have hl : raw34713step0Labels = raw34713Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34713 raw34713Labels permutation169 permutation7
    mixedMoment B raw34713step0 raw34713step0Labels = mixedMoment B raw34713step1 raw34713step1Labels := by
      have ha : raw34713step1 = -raw34713step0 := by apply Matrix.ext; change ∀ i j, raw34713step1 i j = -(raw34713step0 i j); unfold raw34713step1 raw34713step0; decide +kernel
      have hl : raw34713step1Labels = raw34713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34713step1 raw34713step1Labels = mixedMoment B raw34713step2 raw34713step2Labels := by
      have ha : raw34713step2 = raw34713step1 := by apply Matrix.ext; unfold raw34713step2 raw34713step1; decide +kernel
      have hl : raw34713step1Labels = labelEmbedding1 ∘ raw34713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34713step1 raw34713step1Labels raw34713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2192 node2192Labels := by rfl

theorem canonical34714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34714 raw34714Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw34714 raw34714Labels = mixedMoment B raw34714step0 raw34714step0Labels := by
      have hz : ∀ j, raw34714 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34714step0 = (fun i j => raw34714 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34714step0 raw34714; decide +kernel
      have hl : raw34714step0Labels = raw34714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34714 raw34714Labels permutation520 hz
    mixedMoment B raw34714step0 raw34714step0Labels = mixedMoment B raw34714step1 raw34714step1Labels := by
      have ha : raw34714step1 = (fun i j => raw34714step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34714step1 raw34714step0; decide +kernel
      have hl : raw34714step1Labels = raw34714step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34714step0 raw34714step0Labels permutation37 permutation7
    mixedMoment B raw34714step1 raw34714step1Labels = mixedMoment B raw34714step2 raw34714step2Labels := by
      have ha : raw34714step2 = -raw34714step1 := by apply Matrix.ext; change ∀ i j, raw34714step2 i j = -(raw34714step1 i j); unfold raw34714step2 raw34714step1; decide +kernel
      have hl : raw34714step2Labels = raw34714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34714step2 raw34714step2Labels = mixedMoment B raw34714step3 raw34714step3Labels := by
      have ha : raw34714step3 = raw34714step2 := by apply Matrix.ext; unfold raw34714step3 raw34714step2; decide +kernel
      have hl : raw34714step2Labels = labelEmbedding1 ∘ raw34714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34714step2 raw34714step2Labels raw34714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical34715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34715 raw34715Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw34715 raw34715Labels = mixedMoment B raw34715step0 raw34715step0Labels := by
      have hz : ∀ j, raw34715 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34715step0 = (fun i j => raw34715 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34715step0 raw34715; decide +kernel
      have hl : raw34715step0Labels = raw34715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34715 raw34715Labels permutation590 hz
    mixedMoment B raw34715step0 raw34715step0Labels = mixedMoment B raw34715step1 raw34715step1Labels := by
      have ha : raw34715step1 = (fun i j => raw34715step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34715step1 raw34715step0; decide +kernel
      have hl : raw34715step1Labels = raw34715step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34715step0 raw34715step0Labels permutation37 permutation7
    mixedMoment B raw34715step1 raw34715step1Labels = mixedMoment B raw34715step2 raw34715step2Labels := by
      have ha : raw34715step2 = -raw34715step1 := by apply Matrix.ext; change ∀ i j, raw34715step2 i j = -(raw34715step1 i j); unfold raw34715step2 raw34715step1; decide +kernel
      have hl : raw34715step2Labels = raw34715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34715step2 raw34715step2Labels = mixedMoment B raw34715step3 raw34715step3Labels := by
      have ha : raw34715step3 = raw34715step2 := by apply Matrix.ext; unfold raw34715step3 raw34715step2; decide +kernel
      have hl : raw34715step2Labels = labelEmbedding1 ∘ raw34715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34715step2 raw34715step2Labels raw34715step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical34716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34716 raw34716Labels = mixedMoment B node2145 node2145Labels := by
  calc
    mixedMoment B raw34716 raw34716Labels = mixedMoment B raw34716step0 raw34716step0Labels := by
      have ha : raw34716step0 = (fun i j => raw34716 (permutation175 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34716step0 raw34716; decide +kernel
      have hl : raw34716step0Labels = raw34716Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34716 raw34716Labels permutation175 permutation7
    mixedMoment B raw34716step0 raw34716step0Labels = mixedMoment B raw34716step1 raw34716step1Labels := by
      have ha : raw34716step1 = -raw34716step0 := by apply Matrix.ext; change ∀ i j, raw34716step1 i j = -(raw34716step0 i j); unfold raw34716step1 raw34716step0; decide +kernel
      have hl : raw34716step1Labels = raw34716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34716step1 raw34716step1Labels = mixedMoment B raw34716step2 raw34716step2Labels := by
      have ha : raw34716step2 = raw34716step1 := by apply Matrix.ext; unfold raw34716step2 raw34716step1; decide +kernel
      have hl : raw34716step1Labels = labelEmbedding1 ∘ raw34716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34716step1 raw34716step1Labels raw34716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2145 node2145Labels := by rfl

theorem canonical34717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34717 raw34717Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw34717 raw34717Labels = mixedMoment B raw34717step0 raw34717step0Labels := by
      have ha : raw34717step0 = (fun i j => raw34717 (permutation175 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34717step0 raw34717; decide +kernel
      have hl : raw34717step0Labels = raw34717Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34717 raw34717Labels permutation175 permutation7
    mixedMoment B raw34717step0 raw34717step0Labels = mixedMoment B raw34717step1 raw34717step1Labels := by
      have ha : raw34717step1 = -raw34717step0 := by apply Matrix.ext; change ∀ i j, raw34717step1 i j = -(raw34717step0 i j); unfold raw34717step1 raw34717step0; decide +kernel
      have hl : raw34717step1Labels = raw34717step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34717step1 raw34717step1Labels = mixedMoment B raw34717step2 raw34717step2Labels := by
      have ha : raw34717step2 = raw34717step1 := by apply Matrix.ext; unfold raw34717step2 raw34717step1; decide +kernel
      have hl : raw34717step1Labels = labelEmbedding1 ∘ raw34717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34717step1 raw34717step1Labels raw34717step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

theorem canonical34718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34718 raw34718Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw34718 raw34718Labels = mixedMoment B raw34718step0 raw34718step0Labels := by
      have ha : raw34718step0 = (fun i j => raw34718 (permutation175 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34718step0 raw34718; decide +kernel
      have hl : raw34718step0Labels = raw34718Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34718 raw34718Labels permutation175 permutation7
    mixedMoment B raw34718step0 raw34718step0Labels = mixedMoment B raw34718step1 raw34718step1Labels := by
      have ha : raw34718step1 = -raw34718step0 := by apply Matrix.ext; change ∀ i j, raw34718step1 i j = -(raw34718step0 i j); unfold raw34718step1 raw34718step0; decide +kernel
      have hl : raw34718step1Labels = raw34718step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34718step1 raw34718step1Labels = mixedMoment B raw34718step2 raw34718step2Labels := by
      have ha : raw34718step2 = raw34718step1 := by apply Matrix.ext; unfold raw34718step2 raw34718step1; decide +kernel
      have hl : raw34718step1Labels = labelEmbedding1 ∘ raw34718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34718step1 raw34718step1Labels raw34718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical34719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34719 raw34719Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw34719 raw34719Labels = mixedMoment B raw34719step0 raw34719step0Labels := by
      have hz : ∀ j, raw34719 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34719step0 = (fun i j => raw34719 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34719step0 raw34719; decide +kernel
      have hl : raw34719step0Labels = raw34719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34719 raw34719Labels permutation590 hz
    mixedMoment B raw34719step0 raw34719step0Labels = mixedMoment B raw34719step1 raw34719step1Labels := by
      have ha : raw34719step1 = (fun i j => raw34719step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34719step1 raw34719step0; decide +kernel
      have hl : raw34719step1Labels = raw34719step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34719step0 raw34719step0Labels permutation37 permutation7
    mixedMoment B raw34719step1 raw34719step1Labels = mixedMoment B raw34719step2 raw34719step2Labels := by
      have ha : raw34719step2 = -raw34719step1 := by apply Matrix.ext; change ∀ i j, raw34719step2 i j = -(raw34719step1 i j); unfold raw34719step2 raw34719step1; decide +kernel
      have hl : raw34719step2Labels = raw34719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34719step2 raw34719step2Labels = mixedMoment B raw34719step3 raw34719step3Labels := by
      have ha : raw34719step3 = raw34719step2 := by apply Matrix.ext; unfold raw34719step3 raw34719step2; decide +kernel
      have hl : raw34719step2Labels = labelEmbedding1 ∘ raw34719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34719step2 raw34719step2Labels raw34719step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical34720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34720 raw34720Labels = mixedMoment B node2145 node2145Labels := by
  calc
    mixedMoment B raw34720 raw34720Labels = mixedMoment B raw34720step0 raw34720step0Labels := by
      have ha : raw34720step0 = (fun i j => raw34720 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34720step0 raw34720; decide +kernel
      have hl : raw34720step0Labels = raw34720Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34720 raw34720Labels permutation169 permutation7
    mixedMoment B raw34720step0 raw34720step0Labels = mixedMoment B raw34720step1 raw34720step1Labels := by
      have ha : raw34720step1 = -raw34720step0 := by apply Matrix.ext; change ∀ i j, raw34720step1 i j = -(raw34720step0 i j); unfold raw34720step1 raw34720step0; decide +kernel
      have hl : raw34720step1Labels = raw34720step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34720step1 raw34720step1Labels = mixedMoment B raw34720step2 raw34720step2Labels := by
      have ha : raw34720step2 = raw34720step1 := by apply Matrix.ext; unfold raw34720step2 raw34720step1; decide +kernel
      have hl : raw34720step1Labels = labelEmbedding1 ∘ raw34720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34720step1 raw34720step1Labels raw34720step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2145 node2145Labels := by rfl

theorem canonical34721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34721 raw34721Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw34721 raw34721Labels = mixedMoment B raw34721step0 raw34721step0Labels := by
      have ha : raw34721step0 = (fun i j => raw34721 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34721step0 raw34721; decide +kernel
      have hl : raw34721step0Labels = raw34721Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34721 raw34721Labels permutation169 permutation7
    mixedMoment B raw34721step0 raw34721step0Labels = mixedMoment B raw34721step1 raw34721step1Labels := by
      have ha : raw34721step1 = -raw34721step0 := by apply Matrix.ext; change ∀ i j, raw34721step1 i j = -(raw34721step0 i j); unfold raw34721step1 raw34721step0; decide +kernel
      have hl : raw34721step1Labels = raw34721step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34721step1 raw34721step1Labels = mixedMoment B raw34721step2 raw34721step2Labels := by
      have ha : raw34721step2 = raw34721step1 := by apply Matrix.ext; unfold raw34721step2 raw34721step1; decide +kernel
      have hl : raw34721step1Labels = labelEmbedding1 ∘ raw34721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34721step1 raw34721step1Labels raw34721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

theorem canonical34722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34722 raw34722Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw34722 raw34722Labels = mixedMoment B raw34722step0 raw34722step0Labels := by
      have ha : raw34722step0 = (fun i j => raw34722 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34722step0 raw34722; decide +kernel
      have hl : raw34722step0Labels = raw34722Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34722 raw34722Labels permutation169 permutation7
    mixedMoment B raw34722step0 raw34722step0Labels = mixedMoment B raw34722step1 raw34722step1Labels := by
      have ha : raw34722step1 = -raw34722step0 := by apply Matrix.ext; change ∀ i j, raw34722step1 i j = -(raw34722step0 i j); unfold raw34722step1 raw34722step0; decide +kernel
      have hl : raw34722step1Labels = raw34722step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34722step1 raw34722step1Labels = mixedMoment B raw34722step2 raw34722step2Labels := by
      have ha : raw34722step2 = raw34722step1 := by apply Matrix.ext; unfold raw34722step2 raw34722step1; decide +kernel
      have hl : raw34722step1Labels = labelEmbedding1 ∘ raw34722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34722step1 raw34722step1Labels raw34722step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical34723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34723 raw34723Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw34723 raw34723Labels = mixedMoment B raw34723step0 raw34723step0Labels := by
      have hz : ∀ j, raw34723 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34723step0 = (fun i j => raw34723 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34723step0 raw34723; decide +kernel
      have hl : raw34723step0Labels = raw34723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34723 raw34723Labels permutation520 hz
    mixedMoment B raw34723step0 raw34723step0Labels = mixedMoment B raw34723step1 raw34723step1Labels := by
      have ha : raw34723step1 = (fun i j => raw34723step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34723step1 raw34723step0; decide +kernel
      have hl : raw34723step1Labels = raw34723step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34723step0 raw34723step0Labels permutation37 permutation7
    mixedMoment B raw34723step1 raw34723step1Labels = mixedMoment B raw34723step2 raw34723step2Labels := by
      have ha : raw34723step2 = -raw34723step1 := by apply Matrix.ext; change ∀ i j, raw34723step2 i j = -(raw34723step1 i j); unfold raw34723step2 raw34723step1; decide +kernel
      have hl : raw34723step2Labels = raw34723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34723step2 raw34723step2Labels = mixedMoment B raw34723step3 raw34723step3Labels := by
      have ha : raw34723step3 = raw34723step2 := by apply Matrix.ext; unfold raw34723step3 raw34723step2; decide +kernel
      have hl : raw34723step2Labels = labelEmbedding1 ∘ raw34723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34723step2 raw34723step2Labels raw34723step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

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

theorem canonical34725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34725 raw34725Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34725 raw34725Labels = mixedMoment B raw34725step0 raw34725step0Labels := by
      have hz : ∀ j, raw34725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34725step0 = (fun i j => raw34725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34725step0 raw34725; decide +kernel
      have hl : raw34725step0Labels = raw34725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34725 raw34725Labels permutation434 hz
    mixedMoment B raw34725step0 raw34725step0Labels = mixedMoment B raw34725step1 raw34725step1Labels := by
      have hz : ∀ i, raw34725step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34725step1 = (fun i j => raw34725step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34725step1 raw34725step0; decide +kernel
      have hl : raw34725step1Labels = (fun j => raw34725step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34725step0 raw34725step0Labels permutation6 hz
    mixedMoment B raw34725step1 raw34725step1Labels = mixedMoment B raw34725step2 raw34725step2Labels := by
      have ha : raw34725step2 = (fun i j => raw34725step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34725step2 raw34725step1; decide +kernel
      have hl : raw34725step2Labels = raw34725step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34725step1 raw34725step1Labels permutation35 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical34726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34726 raw34726Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34726 raw34726Labels = mixedMoment B raw34726step0 raw34726step0Labels := by
      have hz : ∀ j, raw34726 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34726step0 = (fun i j => raw34726 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34726step0 raw34726; decide +kernel
      have hl : raw34726step0Labels = raw34726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34726 raw34726Labels permutation520 hz
    mixedMoment B raw34726step0 raw34726step0Labels = mixedMoment B raw34726step1 raw34726step1Labels := by
      have hz : ∀ i, raw34726step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34726step1 = (fun i j => raw34726step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34726step1 raw34726step0; decide +kernel
      have hl : raw34726step1Labels = (fun j => raw34726step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34726step0 raw34726step0Labels permutation6 hz
    mixedMoment B raw34726step1 raw34726step1Labels = mixedMoment B raw34726step2 raw34726step2Labels := by
      have ha : raw34726step2 = (fun i j => raw34726step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34726step2 raw34726step1; decide +kernel
      have hl : raw34726step2Labels = raw34726step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34726step1 raw34726step1Labels permutation35 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical34727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34727 raw34727Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34727 raw34727Labels = mixedMoment B raw34727step0 raw34727step0Labels := by
      have hz : ∀ j, raw34727 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34727step0 = (fun i j => raw34727 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34727step0 raw34727; decide +kernel
      have hl : raw34727step0Labels = raw34727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34727 raw34727Labels permutation590 hz
    mixedMoment B raw34727step0 raw34727step0Labels = mixedMoment B raw34727step1 raw34727step1Labels := by
      have hz : ∀ i, raw34727step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34727step1 = (fun i j => raw34727step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34727step1 raw34727step0; decide +kernel
      have hl : raw34727step1Labels = (fun j => raw34727step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34727step0 raw34727step0Labels permutation6 hz
    mixedMoment B raw34727step1 raw34727step1Labels = mixedMoment B raw34727step2 raw34727step2Labels := by
      have ha : raw34727step2 = (fun i j => raw34727step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34727step2 raw34727step1; decide +kernel
      have hl : raw34727step2Labels = raw34727step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34727step1 raw34727step1Labels permutation35 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

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

theorem canonical34729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34729 raw34729Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34729 raw34729Labels = mixedMoment B raw34729step0 raw34729step0Labels := by
      have hz : ∀ j, raw34729 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34729step0 = (fun i j => raw34729 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34729step0 raw34729; decide +kernel
      have hl : raw34729step0Labels = raw34729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34729 raw34729Labels permutation520 hz
    mixedMoment B raw34729step0 raw34729step0Labels = mixedMoment B raw34729step1 raw34729step1Labels := by
      have hz : ∀ i, raw34729step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34729step1 = (fun i j => raw34729step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34729step1 raw34729step0; decide +kernel
      have hl : raw34729step1Labels = (fun j => raw34729step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34729step0 raw34729step0Labels permutation6 hz
    mixedMoment B raw34729step1 raw34729step1Labels = mixedMoment B raw34729step2 raw34729step2Labels := by
      have ha : raw34729step2 = (fun i j => raw34729step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34729step2 raw34729step1; decide +kernel
      have hl : raw34729step2Labels = raw34729step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34729step1 raw34729step1Labels permutation33 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical34730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34730 raw34730Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34730 raw34730Labels = mixedMoment B raw34730step0 raw34730step0Labels := by
      have hz : ∀ j, raw34730 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34730step0 = (fun i j => raw34730 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34730step0 raw34730; decide +kernel
      have hl : raw34730step0Labels = raw34730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34730 raw34730Labels permutation590 hz
    mixedMoment B raw34730step0 raw34730step0Labels = mixedMoment B raw34730step1 raw34730step1Labels := by
      have hz : ∀ i, raw34730step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34730step1 = (fun i j => raw34730step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34730step1 raw34730step0; decide +kernel
      have hl : raw34730step1Labels = (fun j => raw34730step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34730step0 raw34730step0Labels permutation6 hz
    mixedMoment B raw34730step1 raw34730step1Labels = mixedMoment B raw34730step2 raw34730step2Labels := by
      have ha : raw34730step2 = (fun i j => raw34730step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34730step2 raw34730step1; decide +kernel
      have hl : raw34730step2Labels = raw34730step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34730step1 raw34730step1Labels permutation33 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

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

theorem canonical34732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34732 raw34732Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34732 raw34732Labels = mixedMoment B raw34732step0 raw34732step0Labels := by
      have hz : ∀ j, raw34732 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34732step0 = (fun i j => raw34732 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34732step0 raw34732; decide +kernel
      have hl : raw34732step0Labels = raw34732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34732 raw34732Labels permutation590 hz
    mixedMoment B raw34732step0 raw34732step0Labels = mixedMoment B raw34732step1 raw34732step1Labels := by
      have hz : ∀ i, raw34732step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34732step1 = (fun i j => raw34732step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34732step1 raw34732step0; decide +kernel
      have hl : raw34732step1Labels = (fun j => raw34732step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34732step0 raw34732step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical34733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34733 raw34733Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw34733 raw34733Labels = mixedMoment B raw34733step0 raw34733step0Labels := by
      have hz : ∀ j, raw34733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34733step0 = (fun i j => raw34733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34733step0 raw34733; decide +kernel
      have hl : raw34733step0Labels = raw34733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34733 raw34733Labels permutation346 hz
    _ = mixedMoment B node1814 node1814Labels := by rfl

theorem canonical34734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34734 raw34734Labels = mixedMoment B node3131 node3131Labels := by
  calc
    mixedMoment B raw34734 raw34734Labels = mixedMoment B raw34734step0 raw34734step0Labels := by
      have hz : ∀ j, raw34734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34734step0 = (fun i j => raw34734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34734step0 raw34734; decide +kernel
      have hl : raw34734step0Labels = raw34734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34734 raw34734Labels permutation346 hz
    mixedMoment B raw34734step0 raw34734step0Labels = mixedMoment B raw34734step1 raw34734step1Labels := by
      have ha : raw34734step1 = (fun i j => raw34734step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34734step1 raw34734step0; decide +kernel
      have hl : raw34734step1Labels = raw34734step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34734step0 raw34734step0Labels permutation56 permutation2
    _ = mixedMoment B node3131 node3131Labels := by rfl

theorem canonical34735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34735 raw34735Labels = mixedMoment B node3365 node3365Labels := by
  calc
    _ = mixedMoment B node3365 node3365Labels := by rfl

theorem canonical34736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34736 raw34736Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw34736 raw34736Labels = mixedMoment B raw34736step0 raw34736step0Labels := by
      have hz : ∀ j, raw34736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34736step0 = (fun i j => raw34736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34736step0 raw34736; decide +kernel
      have hl : raw34736step0Labels = raw34736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34736 raw34736Labels permutation346 hz
    _ = mixedMoment B node3379 node3379Labels := by rfl

theorem canonical34737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34737 raw34737Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw34737 raw34737Labels = mixedMoment B raw34737step0 raw34737step0Labels := by
      have hz : ∀ j, raw34737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34737step0 = (fun i j => raw34737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34737step0 raw34737; decide +kernel
      have hl : raw34737step0Labels = raw34737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34737 raw34737Labels permutation346 hz
    mixedMoment B raw34737step0 raw34737step0Labels = mixedMoment B raw34737step1 raw34737step1Labels := by
      have ha : raw34737step1 = (fun i j => raw34737step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34737step1 raw34737step0; decide +kernel
      have hl : raw34737step1Labels = raw34737step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34737step0 raw34737step0Labels permutation34 permutation2
    _ = mixedMoment B node3391 node3391Labels := by rfl

theorem canonical34738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34738 raw34738Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw34738 raw34738Labels = mixedMoment B raw34738step0 raw34738step0Labels := by
      have hz : ∀ j, raw34738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34738step0 = (fun i j => raw34738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34738step0 raw34738; decide +kernel
      have hl : raw34738step0Labels = raw34738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34738 raw34738Labels permutation346 hz
    mixedMoment B raw34738step0 raw34738step0Labels = mixedMoment B raw34738step1 raw34738step1Labels := by
      have ha : raw34738step1 = (fun i j => raw34738step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34738step1 raw34738step0; decide +kernel
      have hl : raw34738step1Labels = raw34738step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34738step0 raw34738step0Labels permutation33 permutation2
    _ = mixedMoment B node3395 node3395Labels := by rfl

theorem canonical34739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34739 raw34739Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw34739 raw34739Labels = mixedMoment B raw34739step0 raw34739step0Labels := by
      have hz : ∀ j, raw34739 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34739step0 = (fun i j => raw34739 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34739step0 raw34739; decide +kernel
      have hl : raw34739step0Labels = raw34739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34739 raw34739Labels permutation520 hz
    mixedMoment B raw34739step0 raw34739step0Labels = mixedMoment B raw34739step1 raw34739step1Labels := by
      have hz : ∀ j, raw34739step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34739step1 = (fun i j => raw34739step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34739step1 raw34739step0; decide +kernel
      have hl : raw34739step1Labels = raw34739step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34739step0 raw34739step0Labels permutation80 hz
    mixedMoment B raw34739step1 raw34739step1Labels = mixedMoment B raw34739step2 raw34739step2Labels := by
      have hz : ∀ j, raw34739step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw34739step2 = (fun i j => raw34739step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw34739step2 raw34739step1; decide +kernel
      have hl : raw34739step2Labels = raw34739step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34739step1 raw34739step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical34740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34740 raw34740Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw34740 raw34740Labels = mixedMoment B raw34740step0 raw34740step0Labels := by
      have hz : ∀ j, raw34740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34740step0 = (fun i j => raw34740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34740step0 raw34740; decide +kernel
      have hl : raw34740step0Labels = raw34740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34740 raw34740Labels permutation346 hz
    mixedMoment B raw34740step0 raw34740step0Labels = mixedMoment B raw34740step1 raw34740step1Labels := by
      have ha : raw34740step1 = (fun i j => raw34740step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34740step1 raw34740step0; decide +kernel
      have hl : raw34740step1Labels = raw34740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34740step0 raw34740step0Labels permutation123 permutation2
    mixedMoment B raw34740step1 raw34740step1Labels = mixedMoment B raw34740step2 raw34740step2Labels := by
      have ha : raw34740step2 = -raw34740step1 := by apply Matrix.ext; change ∀ i j, raw34740step2 i j = -(raw34740step1 i j); unfold raw34740step2 raw34740step1; decide +kernel
      have hl : raw34740step2Labels = raw34740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical34741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34741 raw34741Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw34741 raw34741Labels = mixedMoment B raw34741step0 raw34741step0Labels := by
      have hz : ∀ j, raw34741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34741step0 = (fun i j => raw34741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34741step0 raw34741; decide +kernel
      have hl : raw34741step0Labels = raw34741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34741 raw34741Labels permutation346 hz
    mixedMoment B raw34741step0 raw34741step0Labels = mixedMoment B raw34741step1 raw34741step1Labels := by
      have ha : raw34741step1 = (fun i j => raw34741step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34741step1 raw34741step0; decide +kernel
      have hl : raw34741step1Labels = raw34741step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34741step0 raw34741step0Labels permutation46 permutation4
    mixedMoment B raw34741step1 raw34741step1Labels = mixedMoment B raw34741step2 raw34741step2Labels := by
      have ha : raw34741step2 = -raw34741step1 := by apply Matrix.ext; change ∀ i j, raw34741step2 i j = -(raw34741step1 i j); unfold raw34741step2 raw34741step1; decide +kernel
      have hl : raw34741step2Labels = raw34741step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3040 node3040Labels := by rfl

theorem canonical34742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34742 raw34742Labels = mixedMoment B node3032 node3032Labels := by
  calc
    mixedMoment B raw34742 raw34742Labels = mixedMoment B raw34742step0 raw34742step0Labels := by
      have ha : raw34742step0 = (fun i j => raw34742 (permutation234 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34742step0 raw34742; decide +kernel
      have hl : raw34742step0Labels = raw34742Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34742 raw34742Labels permutation234 permutation4
    mixedMoment B raw34742step0 raw34742step0Labels = mixedMoment B raw34742step1 raw34742step1Labels := by
      have ha : raw34742step1 = -raw34742step0 := by apply Matrix.ext; change ∀ i j, raw34742step1 i j = -(raw34742step0 i j); unfold raw34742step1 raw34742step0; decide +kernel
      have hl : raw34742step1Labels = raw34742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3032 node3032Labels := by rfl

theorem canonical34743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34743 raw34743Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw34743 raw34743Labels = mixedMoment B raw34743step0 raw34743step0Labels := by
      have hz : ∀ j, raw34743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34743step0 = (fun i j => raw34743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34743step0 raw34743; decide +kernel
      have hl : raw34743step0Labels = raw34743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34743 raw34743Labels permutation346 hz
    mixedMoment B raw34743step0 raw34743step0Labels = mixedMoment B raw34743step1 raw34743step1Labels := by
      have ha : raw34743step1 = (fun i j => raw34743step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34743step1 raw34743step0; decide +kernel
      have hl : raw34743step1Labels = raw34743step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34743step0 raw34743step0Labels permutation44 permutation4
    mixedMoment B raw34743step1 raw34743step1Labels = mixedMoment B raw34743step2 raw34743step2Labels := by
      have ha : raw34743step2 = -raw34743step1 := by apply Matrix.ext; change ∀ i j, raw34743step2 i j = -(raw34743step1 i j); unfold raw34743step2 raw34743step1; decide +kernel
      have hl : raw34743step2Labels = raw34743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3045 node3045Labels := by rfl

theorem canonical34744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34744 raw34744Labels = mixedMoment B node2362 node2362Labels := by
  calc
    mixedMoment B raw34744 raw34744Labels = mixedMoment B raw34744step0 raw34744step0Labels := by
      have hz : ∀ j, raw34744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34744step0 = (fun i j => raw34744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34744step0 raw34744; decide +kernel
      have hl : raw34744step0Labels = raw34744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34744 raw34744Labels permutation346 hz
    mixedMoment B raw34744step0 raw34744step0Labels = mixedMoment B raw34744step1 raw34744step1Labels := by
      have ha : raw34744step1 = (fun i j => raw34744step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34744step1 raw34744step0; decide +kernel
      have hl : raw34744step1Labels = raw34744step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34744step0 raw34744step0Labels permutation126 permutation2
    mixedMoment B raw34744step1 raw34744step1Labels = mixedMoment B raw34744step2 raw34744step2Labels := by
      have ha : raw34744step2 = -raw34744step1 := by apply Matrix.ext; change ∀ i j, raw34744step2 i j = -(raw34744step1 i j); unfold raw34744step2 raw34744step1; decide +kernel
      have hl : raw34744step2Labels = raw34744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2362 node2362Labels := by rfl

theorem canonical34745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34745 raw34745Labels = mixedMoment B node3033 node3033Labels := by
  calc
    mixedMoment B raw34745 raw34745Labels = mixedMoment B raw34745step0 raw34745step0Labels := by
      have hz : ∀ j, raw34745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34745step0 = (fun i j => raw34745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34745step0 raw34745; decide +kernel
      have hl : raw34745step0Labels = raw34745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34745 raw34745Labels permutation346 hz
    mixedMoment B raw34745step0 raw34745step0Labels = mixedMoment B raw34745step1 raw34745step1Labels := by
      have ha : raw34745step1 = (fun i j => raw34745step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34745step1 raw34745step0; decide +kernel
      have hl : raw34745step1Labels = raw34745step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34745step0 raw34745step0Labels permutation46 permutation4
    mixedMoment B raw34745step1 raw34745step1Labels = mixedMoment B raw34745step2 raw34745step2Labels := by
      have ha : raw34745step2 = -raw34745step1 := by apply Matrix.ext; change ∀ i j, raw34745step2 i j = -(raw34745step1 i j); unfold raw34745step2 raw34745step1; decide +kernel
      have hl : raw34745step2Labels = raw34745step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3033 node3033Labels := by rfl

theorem canonical34746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34746 raw34746Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw34746 raw34746Labels = mixedMoment B raw34746step0 raw34746step0Labels := by
      have hz : ∀ j, raw34746 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34746step0 = (fun i j => raw34746 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34746step0 raw34746; decide +kernel
      have hl : raw34746step0Labels = raw34746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34746 raw34746Labels permutation590 hz
    mixedMoment B raw34746step0 raw34746step0Labels = mixedMoment B raw34746step1 raw34746step1Labels := by
      have hz : ∀ j, raw34746step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34746step1 = (fun i j => raw34746step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34746step1 raw34746step0; decide +kernel
      have hl : raw34746step1Labels = raw34746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34746step0 raw34746step0Labels permutation80 hz
    mixedMoment B raw34746step1 raw34746step1Labels = mixedMoment B raw34746step2 raw34746step2Labels := by
      have ha : raw34746step2 = (fun i j => raw34746step1 (permutation16 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34746step2 raw34746step1; decide +kernel
      have hl : raw34746step2Labels = raw34746step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34746step1 raw34746step1Labels permutation16 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical34760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34760 raw34760Labels = mixedMoment B node2819 node2819Labels := by
  calc
    mixedMoment B raw34760 raw34760Labels = mixedMoment B raw34760step0 raw34760step0Labels := by
      have hz : ∀ j, raw34760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34760step0 = (fun i j => raw34760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34760step0 raw34760; decide +kernel
      have hl : raw34760step0Labels = raw34760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34760 raw34760Labels permutation346 hz
    mixedMoment B raw34760step0 raw34760step0Labels = mixedMoment B raw34760step1 raw34760step1Labels := by
      have ha : raw34760step1 = (fun i j => raw34760step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34760step1 raw34760step0; decide +kernel
      have hl : raw34760step1Labels = raw34760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34760step0 raw34760step0Labels permutation56 permutation2
    _ = mixedMoment B node2819 node2819Labels := by rfl

theorem canonical34761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34761 raw34761Labels = mixedMoment B node3673 node3673Labels := by
  calc
    _ = mixedMoment B node3673 node3673Labels := by rfl

theorem canonical34762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34762 raw34762Labels = mixedMoment B node3699 node3699Labels := by
  calc
    mixedMoment B raw34762 raw34762Labels = mixedMoment B raw34762step0 raw34762step0Labels := by
      have hz : ∀ j, raw34762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34762step0 = (fun i j => raw34762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34762step0 raw34762; decide +kernel
      have hl : raw34762step0Labels = raw34762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34762 raw34762Labels permutation346 hz
    _ = mixedMoment B node3699 node3699Labels := by rfl

theorem canonical34763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34763 raw34763Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw34763 raw34763Labels = mixedMoment B raw34763step0 raw34763step0Labels := by
      have hz : ∀ j, raw34763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34763step0 = (fun i j => raw34763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34763step0 raw34763; decide +kernel
      have hl : raw34763step0Labels = raw34763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34763 raw34763Labels permutation346 hz
    mixedMoment B raw34763step0 raw34763step0Labels = mixedMoment B raw34763step1 raw34763step1Labels := by
      have ha : raw34763step1 = (fun i j => raw34763step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34763step1 raw34763step0; decide +kernel
      have hl : raw34763step1Labels = raw34763step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34763step0 raw34763step0Labels permutation34 permutation2
    _ = mixedMoment B node3705 node3705Labels := by rfl

theorem canonical34764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34764 raw34764Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw34764 raw34764Labels = mixedMoment B raw34764step0 raw34764step0Labels := by
      have hz : ∀ j, raw34764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34764step0 = (fun i j => raw34764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34764step0 raw34764; decide +kernel
      have hl : raw34764step0Labels = raw34764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34764 raw34764Labels permutation346 hz
    mixedMoment B raw34764step0 raw34764step0Labels = mixedMoment B raw34764step1 raw34764step1Labels := by
      have ha : raw34764step1 = (fun i j => raw34764step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34764step1 raw34764step0; decide +kernel
      have hl : raw34764step1Labels = raw34764step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34764step0 raw34764step0Labels permutation36 permutation2
    _ = mixedMoment B node3706 node3706Labels := by rfl

theorem canonical34765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34765 raw34765Labels = mixedMoment B node2801 node2801Labels := by
  calc
    mixedMoment B raw34765 raw34765Labels = mixedMoment B raw34765step0 raw34765step0Labels := by
      have ha : raw34765step0 = (fun i j => raw34765 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34765step0 raw34765; decide +kernel
      have hl : raw34765step0Labels = raw34765Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34765 raw34765Labels permutation271 permutation2
    _ = mixedMoment B node2801 node2801Labels := by rfl

theorem canonical34766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34766 raw34766Labels = mixedMoment B node3685 node3685Labels := by
  calc
    _ = mixedMoment B node3685 node3685Labels := by rfl

theorem canonical34767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34767 raw34767Labels = mixedMoment B node3676 node3676Labels := by
  calc
    mixedMoment B raw34767 raw34767Labels = mixedMoment B raw34767step0 raw34767step0Labels := by
      have ha : raw34767step0 = (fun i j => raw34767 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34767step0 raw34767; decide +kernel
      have hl : raw34767step0Labels = raw34767Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34767 raw34767Labels permutation158 permutation2
    _ = mixedMoment B node3676 node3676Labels := by rfl

theorem canonical34768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34768 raw34768Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw34768 raw34768Labels = mixedMoment B raw34768step0 raw34768step0Labels := by
      have ha : raw34768step0 = (fun i j => raw34768 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34768step0 raw34768; decide +kernel
      have hl : raw34768step0Labels = raw34768Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34768 raw34768Labels permutation160 permutation2
    _ = mixedMoment B node3690 node3690Labels := by rfl

theorem canonical34769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34769 raw34769Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw34769 raw34769Labels = mixedMoment B raw34769step0 raw34769step0Labels := by
      have ha : raw34769step0 = (fun i j => raw34769 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34769step0 raw34769; decide +kernel
      have hl : raw34769step0Labels = raw34769Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34769 raw34769Labels permutation159 permutation2
    _ = mixedMoment B node3692 node3692Labels := by rfl

theorem canonical34770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34770 raw34770Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw34770 raw34770Labels = mixedMoment B raw34770step0 raw34770step0Labels := by
      have ha : raw34770step0 = (fun i j => raw34770 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34770step0 raw34770; decide +kernel
      have hl : raw34770step0Labels = raw34770Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34770 raw34770Labels permutation687 permutation2
    mixedMoment B raw34770step0 raw34770step0Labels = mixedMoment B raw34770step1 raw34770step1Labels := by
      have ha : raw34770step1 = -raw34770step0 := by apply Matrix.ext; change ∀ i j, raw34770step1 i j = -(raw34770step0 i j); unfold raw34770step1 raw34770step0; decide +kernel
      have hl : raw34770step1Labels = raw34770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3722 node3722Labels := by rfl

theorem canonical34771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34771 raw34771Labels = mixedMoment B node3715 node3715Labels := by
  calc
    _ = mixedMoment B node3715 node3715Labels := by rfl

theorem canonical34772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34772 raw34772Labels = mixedMoment B node3708 node3708Labels := by
  calc
    _ = mixedMoment B node3708 node3708Labels := by rfl

theorem canonical34773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34773 raw34773Labels = mixedMoment B node3134 node3134Labels := by
  calc
    mixedMoment B raw34773 raw34773Labels = mixedMoment B raw34773step0 raw34773step0Labels := by
      have ha : raw34773step0 = (fun i j => raw34773 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34773step0 raw34773; decide +kernel
      have hl : raw34773step0Labels = raw34773Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34773 raw34773Labels permutation589 permutation2
    mixedMoment B raw34773step0 raw34773step0Labels = mixedMoment B raw34773step1 raw34773step1Labels := by
      have ha : raw34773step1 = -raw34773step0 := by apply Matrix.ext; change ∀ i j, raw34773step1 i j = -(raw34773step0 i j); unfold raw34773step1 raw34773step0; decide +kernel
      have hl : raw34773step1Labels = raw34773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3134 node3134Labels := by rfl

theorem canonical34774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34774 raw34774Labels = mixedMoment B node2350 node2350Labels := by
  calc
    mixedMoment B raw34774 raw34774Labels = mixedMoment B raw34774step0 raw34774step0Labels := by
      have ha : raw34774step0 = (fun i j => raw34774 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34774step0 raw34774; decide +kernel
      have hl : raw34774step0Labels = raw34774Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34774 raw34774Labels permutation688 permutation2
    mixedMoment B raw34774step0 raw34774step0Labels = mixedMoment B raw34774step1 raw34774step1Labels := by
      have ha : raw34774step1 = -raw34774step0 := by apply Matrix.ext; change ∀ i j, raw34774step1 i j = -(raw34774step0 i j); unfold raw34774step1 raw34774step0; decide +kernel
      have hl : raw34774step1Labels = raw34774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2350 node2350Labels := by rfl

theorem canonical34775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34775 raw34775Labels = mixedMoment B node3922 node3922Labels := by
  calc
    mixedMoment B raw34775 raw34775Labels = mixedMoment B raw34775step0 raw34775step0Labels := by
      have ha : raw34775step0 = (fun i j => raw34775 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34775step0 raw34775; decide +kernel
      have hl : raw34775step0Labels = raw34775Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34775 raw34775Labels permutation588 permutation2
    mixedMoment B raw34775step0 raw34775step0Labels = mixedMoment B raw34775step1 raw34775step1Labels := by
      have ha : raw34775step1 = -raw34775step0 := by apply Matrix.ext; change ∀ i j, raw34775step1 i j = -(raw34775step0 i j); unfold raw34775step1 raw34775step0; decide +kernel
      have hl : raw34775step1Labels = raw34775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3922 node3922Labels := by rfl

theorem canonical34776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34776 raw34776Labels = mixedMoment B node3716 node3716Labels := by
  calc
    _ = mixedMoment B node3716 node3716Labels := by rfl

theorem canonical34777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34777 raw34777Labels = mixedMoment B node3709 node3709Labels := by
  calc
    _ = mixedMoment B node3709 node3709Labels := by rfl

theorem canonical34778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34778 raw34778Labels = mixedMoment B node2824 node2824Labels := by
  calc
    mixedMoment B raw34778 raw34778Labels = mixedMoment B raw34778step0 raw34778step0Labels := by
      have ha : raw34778step0 = (fun i j => raw34778 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34778step0 raw34778; decide +kernel
      have hl : raw34778step0Labels = raw34778Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34778 raw34778Labels permutation589 permutation2
    mixedMoment B raw34778step0 raw34778step0Labels = mixedMoment B raw34778step1 raw34778step1Labels := by
      have ha : raw34778step1 = -raw34778step0 := by apply Matrix.ext; change ∀ i j, raw34778step1 i j = -(raw34778step0 i j); unfold raw34778step1 raw34778step0; decide +kernel
      have hl : raw34778step1Labels = raw34778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2824 node2824Labels := by rfl

theorem canonical34779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34779 raw34779Labels = mixedMoment B node2824 node2824Labels := by
  calc
    mixedMoment B raw34779 raw34779Labels = mixedMoment B raw34779step0 raw34779step0Labels := by
      have ha : raw34779step0 = (fun i j => raw34779 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34779step0 raw34779; decide +kernel
      have hl : raw34779step0Labels = raw34779Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34779 raw34779Labels permutation688 permutation2
    mixedMoment B raw34779step0 raw34779step0Labels = mixedMoment B raw34779step1 raw34779step1Labels := by
      have ha : raw34779step1 = -raw34779step0 := by apply Matrix.ext; change ∀ i j, raw34779step1 i j = -(raw34779step0 i j); unfold raw34779step1 raw34779step0; decide +kernel
      have hl : raw34779step1Labels = raw34779step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2824 node2824Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5498 raw5498Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw5498 raw5498Labels = mixedMoment B raw5498step0 raw5498step0Labels := by
      have ha : raw5498step0 = (fun i j => raw5498 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5498step0 raw5498; decide +kernel
      have hl : raw5498step0Labels = raw5498Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5498 raw5498Labels permutation241 permutation7
    mixedMoment B raw5498step0 raw5498step0Labels = mixedMoment B raw5498step1 raw5498step1Labels := by
      have ha : raw5498step1 = -raw5498step0 := by apply Matrix.ext; change ∀ i j, raw5498step1 i j = -(raw5498step0 i j); unfold raw5498step1 raw5498step0; decide +kernel
      have hl : raw5498step1Labels = raw5498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5498step1 raw5498step1Labels = mixedMoment B raw5498step2 raw5498step2Labels := by
      have ha : raw5498step2 = raw5498step1 := by apply Matrix.ext; unfold raw5498step2 raw5498step1; decide +kernel
      have hl : raw5498step1Labels = labelEmbedding1 ∘ raw5498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5498step1 raw5498step1Labels raw5498step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical5501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5501 raw5501Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw5501 raw5501Labels = mixedMoment B raw5501step0 raw5501step0Labels := by
      have ha : raw5501step0 = (fun i j => raw5501 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5501step0 raw5501; decide +kernel
      have hl : raw5501step0Labels = raw5501Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5501 raw5501Labels permutation241 permutation7
    mixedMoment B raw5501step0 raw5501step0Labels = mixedMoment B raw5501step1 raw5501step1Labels := by
      have ha : raw5501step1 = -raw5501step0 := by apply Matrix.ext; change ∀ i j, raw5501step1 i j = -(raw5501step0 i j); unfold raw5501step1 raw5501step0; decide +kernel
      have hl : raw5501step1Labels = raw5501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5501step1 raw5501step1Labels = mixedMoment B raw5501step2 raw5501step2Labels := by
      have ha : raw5501step2 = raw5501step1 := by apply Matrix.ext; unfold raw5501step2 raw5501step1; decide +kernel
      have hl : raw5501step1Labels = labelEmbedding1 ∘ raw5501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5501step1 raw5501step1Labels raw5501step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical5503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5503 raw5503Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw5503 raw5503Labels = mixedMoment B raw5503step0 raw5503step0Labels := by
      have ha : raw5503step0 = (fun i j => raw5503 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5503step0 raw5503; decide +kernel
      have hl : raw5503step0Labels = raw5503Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5503 raw5503Labels permutation240 permutation7
    mixedMoment B raw5503step0 raw5503step0Labels = mixedMoment B raw5503step1 raw5503step1Labels := by
      have ha : raw5503step1 = -raw5503step0 := by apply Matrix.ext; change ∀ i j, raw5503step1 i j = -(raw5503step0 i j); unfold raw5503step1 raw5503step0; decide +kernel
      have hl : raw5503step1Labels = raw5503step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5503step1 raw5503step1Labels = mixedMoment B raw5503step2 raw5503step2Labels := by
      have ha : raw5503step2 = raw5503step1 := by apply Matrix.ext; unfold raw5503step2 raw5503step1; decide +kernel
      have hl : raw5503step1Labels = labelEmbedding1 ∘ raw5503step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5503step1 raw5503step1Labels raw5503step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5506 raw5506Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw5506 raw5506Labels = mixedMoment B raw5506step0 raw5506step0Labels := by
      have ha : raw5506step0 = (fun i j => raw5506 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5506step0 raw5506; decide +kernel
      have hl : raw5506step0Labels = raw5506Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5506 raw5506Labels permutation240 permutation7
    mixedMoment B raw5506step0 raw5506step0Labels = mixedMoment B raw5506step1 raw5506step1Labels := by
      have ha : raw5506step1 = -raw5506step0 := by apply Matrix.ext; change ∀ i j, raw5506step1 i j = -(raw5506step0 i j); unfold raw5506step1 raw5506step0; decide +kernel
      have hl : raw5506step1Labels = raw5506step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5506step1 raw5506step1Labels = mixedMoment B raw5506step2 raw5506step2Labels := by
      have ha : raw5506step2 = raw5506step1 := by apply Matrix.ext; unfold raw5506step2 raw5506step1; decide +kernel
      have hl : raw5506step1Labels = labelEmbedding1 ∘ raw5506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5506step1 raw5506step1Labels raw5506step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6553 raw6553Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw6553 raw6553Labels = mixedMoment B raw6553step0 raw6553step0Labels := by
      have hz : ∀ j, raw6553 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6553step0 = (fun i j => raw6553 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6553step0 raw6553; decide +kernel
      have hl : raw6553step0Labels = raw6553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6553 raw6553Labels permutation520 hz
    mixedMoment B raw6553step0 raw6553step0Labels = mixedMoment B raw6553step1 raw6553step1Labels := by
      have hz : ∀ j, raw6553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6553step1 = (fun i j => raw6553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6553step1 raw6553step0; decide +kernel
      have hl : raw6553step1Labels = raw6553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6553step0 raw6553step0Labels permutation80 hz
    mixedMoment B raw6553step1 raw6553step1Labels = mixedMoment B raw6553step2 raw6553step2Labels := by
      have ha : raw6553step2 = (fun i j => raw6553step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw6553step2 raw6553step1; decide +kernel
      have hl : raw6553step2Labels = raw6553step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6553step1 raw6553step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7199 raw7199Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw7199 raw7199Labels = mixedMoment B raw7199step0 raw7199step0Labels := by
      have hz : ∀ j, raw7199 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7199step0 = (fun i j => raw7199 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7199step0 raw7199; decide +kernel
      have hl : raw7199step0Labels = raw7199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7199 raw7199Labels permutation520 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9323 raw9323Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw9323 raw9323Labels = mixedMoment B raw9323step0 raw9323step0Labels := by
      have ha : raw9323step0 = (fun i j => raw9323 (permutation646 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9323step0 raw9323; decide +kernel
      have hl : raw9323step0Labels = raw9323Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9323 raw9323Labels permutation646 permutation5
    mixedMoment B raw9323step0 raw9323step0Labels = mixedMoment B raw9323step1 raw9323step1Labels := by
      have ha : raw9323step1 = raw9323step0 := by apply Matrix.ext; unfold raw9323step1 raw9323step0; decide +kernel
      have hl : raw9323step0Labels = labelEmbedding1 ∘ raw9323step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9323step0 raw9323step0Labels raw9323step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

theorem canonical9326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9326 raw9326Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw9326 raw9326Labels = mixedMoment B raw9326step0 raw9326step0Labels := by
      have hz : ∀ j, raw9326 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9326step0 = (fun i j => raw9326 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9326step0 raw9326; decide +kernel
      have hl : raw9326step0Labels = raw9326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9326 raw9326Labels permutation265 hz
    mixedMoment B raw9326step0 raw9326step0Labels = mixedMoment B raw9326step1 raw9326step1Labels := by
      have ha : raw9326step1 = (fun i j => raw9326step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9326step1 raw9326step0; decide +kernel
      have hl : raw9326step1Labels = raw9326step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9326step0 raw9326step0Labels permutation52 permutation7
    mixedMoment B raw9326step1 raw9326step1Labels = mixedMoment B raw9326step2 raw9326step2Labels := by
      have ha : raw9326step2 = -raw9326step1 := by apply Matrix.ext; change ∀ i j, raw9326step2 i j = -(raw9326step1 i j); unfold raw9326step2 raw9326step1; decide +kernel
      have hl : raw9326step2Labels = raw9326step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9326step2 raw9326step2Labels = mixedMoment B raw9326step3 raw9326step3Labels := by
      have ha : raw9326step3 = raw9326step2 := by apply Matrix.ext; unfold raw9326step3 raw9326step2; decide +kernel
      have hl : raw9326step2Labels = labelEmbedding1 ∘ raw9326step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9326step2 raw9326step2Labels raw9326step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical9328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9328 raw9328Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw9328 raw9328Labels = mixedMoment B raw9328step0 raw9328step0Labels := by
      have ha : raw9328step0 = (fun i j => raw9328 (permutation664 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9328step0 raw9328; decide +kernel
      have hl : raw9328step0Labels = raw9328Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9328 raw9328Labels permutation664 permutation5
    mixedMoment B raw9328step0 raw9328step0Labels = mixedMoment B raw9328step1 raw9328step1Labels := by
      have ha : raw9328step1 = raw9328step0 := by apply Matrix.ext; unfold raw9328step1 raw9328step0; decide +kernel
      have hl : raw9328step0Labels = labelEmbedding1 ∘ raw9328step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9328step0 raw9328step0Labels raw9328step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

theorem canonical9331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9331 raw9331Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw9331 raw9331Labels = mixedMoment B raw9331step0 raw9331step0Labels := by
      have hz : ∀ j, raw9331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9331step0 = (fun i j => raw9331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9331step0 raw9331; decide +kernel
      have hl : raw9331step0Labels = raw9331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9331 raw9331Labels permutation265 hz
    mixedMoment B raw9331step0 raw9331step0Labels = mixedMoment B raw9331step1 raw9331step1Labels := by
      have ha : raw9331step1 = (fun i j => raw9331step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9331step1 raw9331step0; decide +kernel
      have hl : raw9331step1Labels = raw9331step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9331step0 raw9331step0Labels permutation50 permutation7
    mixedMoment B raw9331step1 raw9331step1Labels = mixedMoment B raw9331step2 raw9331step2Labels := by
      have ha : raw9331step2 = -raw9331step1 := by apply Matrix.ext; change ∀ i j, raw9331step2 i j = -(raw9331step1 i j); unfold raw9331step2 raw9331step1; decide +kernel
      have hl : raw9331step2Labels = raw9331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9331step2 raw9331step2Labels = mixedMoment B raw9331step3 raw9331step3Labels := by
      have ha : raw9331step3 = raw9331step2 := by apply Matrix.ext; unfold raw9331step3 raw9331step2; decide +kernel
      have hl : raw9331step2Labels = labelEmbedding1 ∘ raw9331step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9331step2 raw9331step2Labels raw9331step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

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

theorem sound1664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1664 node1664Labels = Sparse.eval nodeValue1664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1664) = mixedMoment B node1664 node1664Labels := rfl
  simpa [nodeValue1664, Sparse.eval] using hc.symm

theorem sound1665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1665 node1665Labels = Sparse.eval nodeValue1665 (mixedVector B) := by
  simpa only [nodeValue1665, Sparse.eval_nil] using zero1665 B _hB _hF

theorem sound1668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1668 node1668Labels = Sparse.eval nodeValue1668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1668) = mixedMoment B node1668 node1668Labels := rfl
  simpa [nodeValue1668, Sparse.eval] using hc.symm

theorem sound1703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1703 node1703Labels = Sparse.eval nodeValue1703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1703) = mixedMoment B node1703 node1703Labels := rfl
  simpa [nodeValue1703, Sparse.eval] using hc.symm

theorem sound1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1706 node1706Labels = Sparse.eval nodeValue1706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1706) = mixedMoment B node1706 node1706Labels := rfl
  simpa [nodeValue1706, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

theorem sound1711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1711 node1711Labels = Sparse.eval nodeValue1711 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1711) = mixedMoment B node1711 node1711Labels := rfl
  simpa [nodeValue1711, Sparse.eval] using hc.symm

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

theorem sound1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1814 node1814Labels = Sparse.eval nodeValue1814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1814) = mixedMoment B node1814 node1814Labels := rfl
  simpa [nodeValue1814, Sparse.eval] using hc.symm

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

theorem sound2141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2141 node2141Labels = Sparse.eval nodeValue2141 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2141) = mixedMoment B node2141 node2141Labels := rfl
  simpa [nodeValue2141, Sparse.eval] using hc.symm

theorem sound2142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2142 node2142Labels = Sparse.eval nodeValue2142 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2142) = mixedMoment B node2142 node2142Labels := rfl
  simpa [nodeValue2142, Sparse.eval] using hc.symm

theorem sound2145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2145 node2145Labels = Sparse.eval nodeValue2145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2145) = mixedMoment B node2145 node2145Labels := rfl
  simpa [nodeValue2145, Sparse.eval] using hc.symm

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

theorem sound2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2190 node2190Labels = Sparse.eval nodeValue2190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2190) = mixedMoment B node2190 node2190Labels := rfl
  simpa [nodeValue2190, Sparse.eval] using hc.symm

theorem sound2192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2192 node2192Labels = Sparse.eval nodeValue2192 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2192) = mixedMoment B node2192 node2192Labels := rfl
  simpa [nodeValue2192, Sparse.eval] using hc.symm

theorem sound2195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2195 node2195Labels = Sparse.eval nodeValue2195 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2195) = mixedMoment B node2195 node2195Labels := rfl
  simpa [nodeValue2195, Sparse.eval] using hc.symm

theorem sound2196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2196 node2196Labels = Sparse.eval nodeValue2196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2196) = mixedMoment B node2196 node2196Labels := rfl
  simpa [nodeValue2196, Sparse.eval] using hc.symm

theorem sound2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = Sparse.eval nodeValue2205 (mixedVector B) := by
  simpa only [nodeValue2205, Sparse.eval_nil] using zero2205 B _hB _hF

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

theorem sound2238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2238 node2238Labels = Sparse.eval nodeValue2238 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2238) = mixedMoment B node2238 node2238Labels := rfl
  simpa [nodeValue2238, Sparse.eval] using hc.symm

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

theorem zero2263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = 0 := by
  exact mixedMoment_order_one B hB node2263 node2263Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = 0 := by
  exact mixedMoment_order_one B hB node2265 node2265Labels 1
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

theorem sound2240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2240 node2240Labels = Sparse.eval nodeValue2240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2240) = mixedMoment B node2240 node2240Labels := rfl
  simpa [nodeValue2240, Sparse.eval] using hc.symm

theorem sound2243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2243 node2243Labels = Sparse.eval nodeValue2243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2243) = mixedMoment B node2243 node2243Labels := rfl
  simpa [nodeValue2243, Sparse.eval] using hc.symm

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2248 node2248Labels = Sparse.eval nodeValue2248 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2248) = mixedMoment B node2248 node2248Labels := rfl
  simpa [nodeValue2248, Sparse.eval] using hc.symm

theorem sound2250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2250 node2250Labels = Sparse.eval nodeValue2250 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2250) = mixedMoment B node2250 node2250Labels := rfl
  simpa [nodeValue2250, Sparse.eval] using hc.symm

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

theorem sound2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = Sparse.eval nodeValue2263 (mixedVector B) := by
  simpa only [nodeValue2263, Sparse.eval_nil] using zero2263 B _hB _hF

theorem sound2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = Sparse.eval nodeValue2265 (mixedVector B) := by
  simpa only [nodeValue2265, Sparse.eval_nil] using zero2265 B _hB _hF

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

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

theorem sound2324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2324 node2324Labels = Sparse.eval nodeValue2324 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2324) = mixedMoment B node2324 node2324Labels := rfl
  simpa [nodeValue2324, Sparse.eval] using hc.symm

theorem sound2343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2343 node2343Labels = Sparse.eval nodeValue2343 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2343) = mixedMoment B node2343 node2343Labels := rfl
  simpa [nodeValue2343, Sparse.eval] using hc.symm

theorem sound2350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2350 node2350Labels = Sparse.eval nodeValue2350 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2350) = mixedMoment B node2350 node2350Labels := rfl
  simpa [nodeValue2350, Sparse.eval] using hc.symm

theorem sound2362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2362 node2362Labels = Sparse.eval nodeValue2362 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2362) = mixedMoment B node2362 node2362Labels := rfl
  simpa [nodeValue2362, Sparse.eval] using hc.symm

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

theorem sound2662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2662 node2662Labels = Sparse.eval nodeValue2662 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2662) = mixedMoment B node2662 node2662Labels := rfl
  simpa [nodeValue2662, Sparse.eval] using hc.symm

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

theorem zero2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2709 node2709Labels = 0 := by
  exact mixedMoment_alpha B hF node2709 node2709Labels 1 permutation200
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

theorem sound2688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2688 node2688Labels = Sparse.eval nodeValue2688 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2688) = mixedMoment B node2688 node2688Labels := rfl
  simpa [nodeValue2688, Sparse.eval] using hc.symm

theorem sound2690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2690 node2690Labels = Sparse.eval nodeValue2690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2690) = mixedMoment B node2690 node2690Labels := rfl
  simpa [nodeValue2690, Sparse.eval] using hc.symm

theorem sound2700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2700 node2700Labels = Sparse.eval nodeValue2700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2700) = mixedMoment B node2700 node2700Labels := rfl
  simpa [nodeValue2700, Sparse.eval] using hc.symm

theorem sound2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2709 node2709Labels = Sparse.eval nodeValue2709 (mixedVector B) := by
  simpa only [nodeValue2709, Sparse.eval_nil] using zero2709 B _hB _hF

theorem sound2710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2710 node2710Labels = Sparse.eval nodeValue2710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2710) = mixedMoment B node2710 node2710Labels := rfl
  simpa [nodeValue2710, Sparse.eval] using hc.symm

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

theorem sound2747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2747 node2747Labels = Sparse.eval nodeValue2747 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2747) = mixedMoment B node2747 node2747Labels := rfl
  simpa [nodeValue2747, Sparse.eval] using hc.symm

theorem sound2750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2750 node2750Labels = Sparse.eval nodeValue2750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2750) = mixedMoment B node2750 node2750Labels := rfl
  simpa [nodeValue2750, Sparse.eval] using hc.symm

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

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

theorem sound2801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2801 node2801Labels = Sparse.eval nodeValue2801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2801) = mixedMoment B node2801 node2801Labels := rfl
  simpa [nodeValue2801, Sparse.eval] using hc.symm

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

theorem sound2819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2819 node2819Labels = Sparse.eval nodeValue2819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2819) = mixedMoment B node2819 node2819Labels := rfl
  simpa [nodeValue2819, Sparse.eval] using hc.symm

theorem sound2824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2824 node2824Labels = Sparse.eval nodeValue2824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2824) = mixedMoment B node2824 node2824Labels := rfl
  simpa [nodeValue2824, Sparse.eval] using hc.symm

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

theorem sound3032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3032 node3032Labels = Sparse.eval nodeValue3032 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3032) = mixedMoment B node3032 node3032Labels := rfl
  simpa [nodeValue3032, Sparse.eval] using hc.symm

theorem sound3033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3033 node3033Labels = Sparse.eval nodeValue3033 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3033) = mixedMoment B node3033 node3033Labels := rfl
  simpa [nodeValue3033, Sparse.eval] using hc.symm

theorem sound3040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3040 node3040Labels = Sparse.eval nodeValue3040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3040) = mixedMoment B node3040 node3040Labels := rfl
  simpa [nodeValue3040, Sparse.eval] using hc.symm

theorem sound3045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3045 node3045Labels = Sparse.eval nodeValue3045 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3045) = mixedMoment B node3045 node3045Labels := rfl
  simpa [nodeValue3045, Sparse.eval] using hc.symm

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

theorem sound3131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3131 node3131Labels = Sparse.eval nodeValue3131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3131) = mixedMoment B node3131 node3131Labels := rfl
  simpa [nodeValue3131, Sparse.eval] using hc.symm

theorem sound3134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3134 node3134Labels = Sparse.eval nodeValue3134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3134) = mixedMoment B node3134 node3134Labels := rfl
  simpa [nodeValue3134, Sparse.eval] using hc.symm

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

theorem sound3257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3257 node3257Labels = Sparse.eval nodeValue3257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3257) = mixedMoment B node3257 node3257Labels := rfl
  simpa [nodeValue3257, Sparse.eval] using hc.symm

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

theorem sound3304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3304 node3304Labels = Sparse.eval nodeValue3304 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3304) = mixedMoment B node3304 node3304Labels := rfl
  simpa [nodeValue3304, Sparse.eval] using hc.symm

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

theorem sound3365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3365 node3365Labels = Sparse.eval nodeValue3365 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3365) = mixedMoment B node3365 node3365Labels := rfl
  simpa [nodeValue3365, Sparse.eval] using hc.symm

theorem sound3379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3379 node3379Labels = Sparse.eval nodeValue3379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3379) = mixedMoment B node3379 node3379Labels := rfl
  simpa [nodeValue3379, Sparse.eval] using hc.symm

theorem sound3391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3391 node3391Labels = Sparse.eval nodeValue3391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3391) = mixedMoment B node3391 node3391Labels := rfl
  simpa [nodeValue3391, Sparse.eval] using hc.symm

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

theorem sound3395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3395 node3395Labels = Sparse.eval nodeValue3395 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3395) = mixedMoment B node3395 node3395Labels := rfl
  simpa [nodeValue3395, Sparse.eval] using hc.symm

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

theorem zero3546 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = 0 := by
  exact mixedMoment_order_one B hB node3546 node3546Labels 1
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

theorem sound3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3521 node3521Labels = Sparse.eval nodeValue3521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3521) = mixedMoment B node3521 node3521Labels := rfl
  simpa [nodeValue3521, Sparse.eval] using hc.symm

theorem sound3546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = Sparse.eval nodeValue3546 (mixedVector B) := by
  simpa only [nodeValue3546, Sparse.eval_nil] using zero3546 B _hB _hF

theorem sound3554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3554 node3554Labels = Sparse.eval nodeValue3554 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3554) = mixedMoment B node3554 node3554Labels := rfl
  simpa [nodeValue3554, Sparse.eval] using hc.symm

theorem sound3562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3562 node3562Labels = Sparse.eval nodeValue3562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3562) = mixedMoment B node3562 node3562Labels := rfl
  simpa [nodeValue3562, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

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

theorem sound3673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3673 node3673Labels = Sparse.eval nodeValue3673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3673) = mixedMoment B node3673 node3673Labels := rfl
  simpa [nodeValue3673, Sparse.eval] using hc.symm

theorem sound3676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3676 node3676Labels = Sparse.eval nodeValue3676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3676) = mixedMoment B node3676 node3676Labels := rfl
  simpa [nodeValue3676, Sparse.eval] using hc.symm

theorem sound3685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3685 node3685Labels = Sparse.eval nodeValue3685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3685) = mixedMoment B node3685 node3685Labels := rfl
  simpa [nodeValue3685, Sparse.eval] using hc.symm

theorem sound3690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3690 node3690Labels = Sparse.eval nodeValue3690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3690) = mixedMoment B node3690 node3690Labels := rfl
  simpa [nodeValue3690, Sparse.eval] using hc.symm

theorem sound3692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3692 node3692Labels = Sparse.eval nodeValue3692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3692) = mixedMoment B node3692 node3692Labels := rfl
  simpa [nodeValue3692, Sparse.eval] using hc.symm

theorem sound3699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3699 node3699Labels = Sparse.eval nodeValue3699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3699) = mixedMoment B node3699 node3699Labels := rfl
  simpa [nodeValue3699, Sparse.eval] using hc.symm

theorem sound3705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3705 node3705Labels = Sparse.eval nodeValue3705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3705) = mixedMoment B node3705 node3705Labels := rfl
  simpa [nodeValue3705, Sparse.eval] using hc.symm

theorem sound3706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3706 node3706Labels = Sparse.eval nodeValue3706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3706) = mixedMoment B node3706 node3706Labels := rfl
  simpa [nodeValue3706, Sparse.eval] using hc.symm

theorem sound3708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3708 node3708Labels = Sparse.eval nodeValue3708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3708) = mixedMoment B node3708 node3708Labels := rfl
  simpa [nodeValue3708, Sparse.eval] using hc.symm

theorem sound3709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3709 node3709Labels = Sparse.eval nodeValue3709 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3709) = mixedMoment B node3709 node3709Labels := rfl
  simpa [nodeValue3709, Sparse.eval] using hc.symm

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

theorem sound3715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3715 node3715Labels = Sparse.eval nodeValue3715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3715) = mixedMoment B node3715 node3715Labels := rfl
  simpa [nodeValue3715, Sparse.eval] using hc.symm

theorem sound3716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3716 node3716Labels = Sparse.eval nodeValue3716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3716) = mixedMoment B node3716 node3716Labels := rfl
  simpa [nodeValue3716, Sparse.eval] using hc.symm

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3722 node3722Labels = Sparse.eval nodeValue3722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3722) = mixedMoment B node3722 node3722Labels := rfl
  simpa [nodeValue3722, Sparse.eval] using hc.symm

theorem sound3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3732 node3732Labels = Sparse.eval nodeValue3732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3732) = mixedMoment B node3732 node3732Labels := rfl
  simpa [nodeValue3732, Sparse.eval] using hc.symm

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

theorem sound3844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3844 node3844Labels = Sparse.eval nodeValue3844 (mixedVector B) := by
  simpa only [nodeValue3844, Sparse.eval_nil] using zero3844 B _hB _hF

theorem sound3867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3867 node3867Labels = Sparse.eval nodeValue3867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3867) = mixedMoment B node3867 node3867Labels := rfl
  simpa [nodeValue3867, Sparse.eval] using hc.symm

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

theorem sound3922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3922 node3922Labels = Sparse.eval nodeValue3922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3922) = mixedMoment B node3922 node3922Labels := rfl
  simpa [nodeValue3922, Sparse.eval] using hc.symm

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

theorem sound4068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4068 node4068Labels = Sparse.eval nodeValue4068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4068) = mixedMoment B node4068 node4068Labels := rfl
  simpa [nodeValue4068, Sparse.eval] using hc.symm

theorem sound4073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4073 node4073Labels = Sparse.eval nodeValue4073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4073) = mixedMoment B node4073 node4073Labels := rfl
  simpa [nodeValue4073, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

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

theorem sound4087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4087 node4087Labels = Sparse.eval nodeValue4087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4087) = mixedMoment B node4087 node4087Labels := rfl
  simpa [nodeValue4087, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources78
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2503 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2503 + difference 0 1) (sourceB2503 + difference 1 0) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3867) := by
    have ha : (tripleCharges (sourceA2503 + difference 0 1) (sourceB2503 + difference 1 0) sourceC2503) = raw34498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34498; decide +kernel
    rw [ha]
    exact (canonical34498 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2503 + difference 0 2) (sourceB2503 + difference 2 0) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA2503 + difference 0 2) (sourceB2503 + difference 2 0) sourceC2503) = raw34499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34499; decide +kernel
    rw [ha]
    exact (canonical34499 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2503 + difference 0 3) (sourceB2503 + difference 3 0) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA2503 + difference 0 3) (sourceB2503 + difference 3 0) sourceC2503) = raw34500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34500; decide +kernel
    rw [ha]
    exact (canonical34500 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2503 + difference 0 4) (sourceB2503 + difference 4 0) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA2503 + difference 0 4) (sourceB2503 + difference 4 0) sourceC2503) = raw34501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34501; decide +kernel
    rw [ha]
    exact (canonical34501 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2503 + difference 0 5) (sourceB2503 + difference 5 0) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3844) := by
    have ha : (tripleCharges (sourceA2503 + difference 0 5) (sourceB2503 + difference 5 0) sourceC2503) = raw34502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34502; decide +kernel
    rw [ha]
    exact (canonical34502 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2503 + difference 1 0) (sourceB2503 + difference 0 1) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA2503 + difference 1 0) (sourceB2503 + difference 0 1) sourceC2503) = raw34503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34503; decide +kernel
    rw [ha]
    exact (canonical34503 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2503 + difference 1 2) (sourceB2503 + difference 2 1) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA2503 + difference 1 2) (sourceB2503 + difference 2 1) sourceC2503) = raw9331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw9331; decide +kernel
    rw [ha]
    exact (canonical9331 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2503 + difference 1 3) (sourceB2503 + difference 3 1) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA2503 + difference 1 3) (sourceB2503 + difference 3 1) sourceC2503) = raw9326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw9326; decide +kernel
    rw [ha]
    exact (canonical9326 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2503 + difference 1 4) (sourceB2503 + difference 4 1) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA2503 + difference 1 4) (sourceB2503 + difference 4 1) sourceC2503) = raw26546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw26546; decide +kernel
    rw [ha]
    exact (canonical26546 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2503 + difference 1 5) (sourceB2503 + difference 5 1) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA2503 + difference 1 5) (sourceB2503 + difference 5 1) sourceC2503) = raw26547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw26547; decide +kernel
    rw [ha]
    exact (canonical26547 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2503 + difference 2 0) (sourceB2503 + difference 0 2) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA2503 + difference 2 0) (sourceB2503 + difference 0 2) sourceC2503) = raw26554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw26554; decide +kernel
    rw [ha]
    exact (canonical26554 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2503 + difference 2 1) (sourceB2503 + difference 1 2) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2503 + difference 2 1) (sourceB2503 + difference 1 2) sourceC2503) = raw34504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34504; decide +kernel
    rw [ha]
    exact (canonical34504 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2503 + difference 2 3) (sourceB2503 + difference 3 2) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2503 + difference 2 3) (sourceB2503 + difference 3 2) sourceC2503) = raw34505 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34505; decide +kernel
    rw [ha]
    exact (canonical34505 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2503 + difference 2 4) (sourceB2503 + difference 4 2) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2503 + difference 2 4) (sourceB2503 + difference 4 2) sourceC2503) = raw34506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34506; decide +kernel
    rw [ha]
    exact (canonical34506 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2503 + difference 2 5) (sourceB2503 + difference 5 2) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA2503 + difference 2 5) (sourceB2503 + difference 5 2) sourceC2503) = raw34507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34507; decide +kernel
    rw [ha]
    exact (canonical34507 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2503 + difference 3 0) (sourceB2503 + difference 0 3) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA2503 + difference 3 0) (sourceB2503 + difference 0 3) sourceC2503) = raw26559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw26559; decide +kernel
    rw [ha]
    exact (canonical26559 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2503 + difference 3 1) (sourceB2503 + difference 1 3) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2503 + difference 3 1) (sourceB2503 + difference 1 3) sourceC2503) = raw34508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34508; decide +kernel
    rw [ha]
    exact (canonical34508 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2503 + difference 3 2) (sourceB2503 + difference 2 3) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2503 + difference 3 2) (sourceB2503 + difference 2 3) sourceC2503) = raw34509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34509; decide +kernel
    rw [ha]
    exact (canonical34509 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2503 + difference 3 4) (sourceB2503 + difference 4 3) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2503 + difference 3 4) (sourceB2503 + difference 4 3) sourceC2503) = raw34510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34510; decide +kernel
    rw [ha]
    exact (canonical34510 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2503 + difference 3 5) (sourceB2503 + difference 5 3) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA2503 + difference 3 5) (sourceB2503 + difference 5 3) sourceC2503) = raw34511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34511; decide +kernel
    rw [ha]
    exact (canonical34511 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2503 + difference 4 0) (sourceB2503 + difference 0 4) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA2503 + difference 4 0) (sourceB2503 + difference 0 4) sourceC2503) = raw26564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw26564; decide +kernel
    rw [ha]
    exact (canonical26564 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2503 + difference 4 1) (sourceB2503 + difference 1 4) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2503 + difference 4 1) (sourceB2503 + difference 1 4) sourceC2503) = raw34512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34512; decide +kernel
    rw [ha]
    exact (canonical34512 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2503 + difference 4 2) (sourceB2503 + difference 2 4) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2503 + difference 4 2) (sourceB2503 + difference 2 4) sourceC2503) = raw34513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34513; decide +kernel
    rw [ha]
    exact (canonical34513 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2503 + difference 4 3) (sourceB2503 + difference 3 4) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2503 + difference 4 3) (sourceB2503 + difference 3 4) sourceC2503) = raw34514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34514; decide +kernel
    rw [ha]
    exact (canonical34514 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2503 + difference 4 5) (sourceB2503 + difference 5 4) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA2503 + difference 4 5) (sourceB2503 + difference 5 4) sourceC2503) = raw34515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34515; decide +kernel
    rw [ha]
    exact (canonical34515 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2503 + difference 5 0) (sourceB2503 + difference 0 5) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2688) := by
    have ha : (tripleCharges (sourceA2503 + difference 5 0) (sourceB2503 + difference 0 5) sourceC2503) = raw26569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw26569; decide +kernel
    rw [ha]
    exact (canonical26569 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2503 + difference 5 1) (sourceB2503 + difference 1 5) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2690) := by
    have ha : (tripleCharges (sourceA2503 + difference 5 1) (sourceB2503 + difference 1 5) sourceC2503) = raw34516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34516; decide +kernel
    rw [ha]
    exact (canonical34516 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2503 + difference 5 2) (sourceB2503 + difference 2 5) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA2503 + difference 5 2) (sourceB2503 + difference 2 5) sourceC2503) = raw9328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw9328; decide +kernel
    rw [ha]
    exact (canonical9328 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2503 + difference 5 3) (sourceB2503 + difference 3 5) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA2503 + difference 5 3) (sourceB2503 + difference 3 5) sourceC2503) = raw9323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw9323; decide +kernel
    rw [ha]
    exact (canonical9323 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2503 + difference 5 4) (sourceB2503 + difference 4 5) sourceC2503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA2503 + difference 5 4) (sourceB2503 + difference 4 5) sourceC2503) = raw34517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2503 sourceB2503 sourceC2503 difference raw34517; decide +kernel
    rw [ha]
    exact (canonical34517 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2503 sourceB2503 sourceC2503
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2503, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2509 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2509 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2509 + difference 0 1) (sourceB2509 + difference 1 0) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2747) := by
    have ha : (tripleCharges (sourceA2509 + difference 0 1) (sourceB2509 + difference 1 0) sourceC2509) = raw34620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34620; decide +kernel
    rw [ha]
    exact (canonical34620 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2509 + difference 0 2) (sourceB2509 + difference 2 0) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA2509 + difference 0 2) (sourceB2509 + difference 2 0) sourceC2509) = raw14286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw14286; decide +kernel
    rw [ha]
    exact (canonical14286 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2509 + difference 0 3) (sourceB2509 + difference 3 0) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA2509 + difference 0 3) (sourceB2509 + difference 3 0) sourceC2509) = raw34621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34621; decide +kernel
    rw [ha]
    exact (canonical34621 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2509 + difference 0 4) (sourceB2509 + difference 4 0) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA2509 + difference 0 4) (sourceB2509 + difference 4 0) sourceC2509) = raw34622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34622; decide +kernel
    rw [ha]
    exact (canonical34622 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2509 + difference 0 5) (sourceB2509 + difference 5 0) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA2509 + difference 0 5) (sourceB2509 + difference 5 0) sourceC2509) = raw34623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34623; decide +kernel
    rw [ha]
    exact (canonical34623 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2509 + difference 1 0) (sourceB2509 + difference 0 1) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA2509 + difference 1 0) (sourceB2509 + difference 0 1) sourceC2509) = raw14294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw14294; decide +kernel
    rw [ha]
    exact (canonical14294 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2509 + difference 1 2) (sourceB2509 + difference 2 1) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA2509 + difference 1 2) (sourceB2509 + difference 2 1) sourceC2509) = raw5506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw5506; decide +kernel
    rw [ha]
    exact (canonical5506 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2509 + difference 1 3) (sourceB2509 + difference 3 1) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA2509 + difference 1 3) (sourceB2509 + difference 3 1) sourceC2509) = raw5501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw5501; decide +kernel
    rw [ha]
    exact (canonical5501 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2509 + difference 1 4) (sourceB2509 + difference 4 1) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA2509 + difference 1 4) (sourceB2509 + difference 4 1) sourceC2509) = raw14296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw14296; decide +kernel
    rw [ha]
    exact (canonical14296 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2509 + difference 1 5) (sourceB2509 + difference 5 1) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA2509 + difference 1 5) (sourceB2509 + difference 5 1) sourceC2509) = raw14297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw14297; decide +kernel
    rw [ha]
    exact (canonical14297 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2509 + difference 2 0) (sourceB2509 + difference 0 2) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1703) := by
    have ha : (tripleCharges (sourceA2509 + difference 2 0) (sourceB2509 + difference 0 2) sourceC2509) = raw26951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw26951; decide +kernel
    rw [ha]
    exact (canonical26951 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2509 + difference 2 1) (sourceB2509 + difference 1 2) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2238) := by
    have ha : (tripleCharges (sourceA2509 + difference 2 1) (sourceB2509 + difference 1 2) sourceC2509) = raw34624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34624; decide +kernel
    rw [ha]
    exact (canonical34624 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2509 + difference 2 3) (sourceB2509 + difference 3 2) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA2509 + difference 2 3) (sourceB2509 + difference 3 2) sourceC2509) = raw34625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34625; decide +kernel
    rw [ha]
    exact (canonical34625 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2509 + difference 2 4) (sourceB2509 + difference 4 2) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2509 + difference 2 4) (sourceB2509 + difference 4 2) sourceC2509) = raw34626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34626; decide +kernel
    rw [ha]
    exact (canonical34626 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2509 + difference 2 5) (sourceB2509 + difference 5 2) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2509 + difference 2 5) (sourceB2509 + difference 5 2) sourceC2509) = raw34627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34627; decide +kernel
    rw [ha]
    exact (canonical34627 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2509 + difference 3 0) (sourceB2509 + difference 0 3) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1703) := by
    have ha : (tripleCharges (sourceA2509 + difference 3 0) (sourceB2509 + difference 0 3) sourceC2509) = raw26956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw26956; decide +kernel
    rw [ha]
    exact (canonical26956 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2509 + difference 3 1) (sourceB2509 + difference 1 3) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2238) := by
    have ha : (tripleCharges (sourceA2509 + difference 3 1) (sourceB2509 + difference 1 3) sourceC2509) = raw34628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34628; decide +kernel
    rw [ha]
    exact (canonical34628 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2509 + difference 3 2) (sourceB2509 + difference 2 3) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA2509 + difference 3 2) (sourceB2509 + difference 2 3) sourceC2509) = raw14299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw14299; decide +kernel
    rw [ha]
    exact (canonical14299 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2509 + difference 3 4) (sourceB2509 + difference 4 3) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2509 + difference 3 4) (sourceB2509 + difference 4 3) sourceC2509) = raw34629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34629; decide +kernel
    rw [ha]
    exact (canonical34629 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2509 + difference 3 5) (sourceB2509 + difference 5 3) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2509 + difference 3 5) (sourceB2509 + difference 5 3) sourceC2509) = raw34630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34630; decide +kernel
    rw [ha]
    exact (canonical34630 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2509 + difference 4 0) (sourceB2509 + difference 0 4) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1711) := by
    have ha : (tripleCharges (sourceA2509 + difference 4 0) (sourceB2509 + difference 0 4) sourceC2509) = raw26960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw26960; decide +kernel
    rw [ha]
    exact (canonical26960 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2509 + difference 4 1) (sourceB2509 + difference 1 4) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2248) := by
    have ha : (tripleCharges (sourceA2509 + difference 4 1) (sourceB2509 + difference 1 4) sourceC2509) = raw34631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34631; decide +kernel
    rw [ha]
    exact (canonical34631 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2509 + difference 4 2) (sourceB2509 + difference 2 4) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA2509 + difference 4 2) (sourceB2509 + difference 2 4) sourceC2509) = raw14304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw14304; decide +kernel
    rw [ha]
    exact (canonical14304 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2509 + difference 4 3) (sourceB2509 + difference 3 4) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA2509 + difference 4 3) (sourceB2509 + difference 3 4) sourceC2509) = raw34632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34632; decide +kernel
    rw [ha]
    exact (canonical34632 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2509 + difference 4 5) (sourceB2509 + difference 5 4) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA2509 + difference 4 5) (sourceB2509 + difference 5 4) sourceC2509) = raw34633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34633; decide +kernel
    rw [ha]
    exact (canonical34633 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2509 + difference 5 0) (sourceB2509 + difference 0 5) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1711) := by
    have ha : (tripleCharges (sourceA2509 + difference 5 0) (sourceB2509 + difference 0 5) sourceC2509) = raw26964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw26964; decide +kernel
    rw [ha]
    exact (canonical26964 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2509 + difference 5 1) (sourceB2509 + difference 1 5) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2248) := by
    have ha : (tripleCharges (sourceA2509 + difference 5 1) (sourceB2509 + difference 1 5) sourceC2509) = raw34634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34634; decide +kernel
    rw [ha]
    exact (canonical34634 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2509 + difference 5 2) (sourceB2509 + difference 2 5) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA2509 + difference 5 2) (sourceB2509 + difference 2 5) sourceC2509) = raw5503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw5503; decide +kernel
    rw [ha]
    exact (canonical5503 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2509 + difference 5 3) (sourceB2509 + difference 3 5) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA2509 + difference 5 3) (sourceB2509 + difference 3 5) sourceC2509) = raw5498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw5498; decide +kernel
    rw [ha]
    exact (canonical5498 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2509 + difference 5 4) (sourceB2509 + difference 4 5) sourceC2509) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA2509 + difference 5 4) (sourceB2509 + difference 4 5) sourceC2509) = raw34635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2509 sourceB2509 sourceC2509 difference raw34635; decide +kernel
    rw [ha]
    exact (canonical34635 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2509 sourceB2509 sourceC2509
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2509, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2513 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2513 + difference 0 1) (sourceB2513 + difference 1 0) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA2513 + difference 0 1) (sourceB2513 + difference 1 0) sourceC2513) = raw34702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34702; decide +kernel
    rw [ha]
    exact (canonical34702 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2513 + difference 0 2) (sourceB2513 + difference 2 0) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA2513 + difference 0 2) (sourceB2513 + difference 2 0) sourceC2513) = raw34703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34703; decide +kernel
    rw [ha]
    exact (canonical34703 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2513 + difference 0 3) (sourceB2513 + difference 3 0) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA2513 + difference 0 3) (sourceB2513 + difference 3 0) sourceC2513) = raw34704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34704; decide +kernel
    rw [ha]
    exact (canonical34704 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2513 + difference 0 4) (sourceB2513 + difference 4 0) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA2513 + difference 0 4) (sourceB2513 + difference 4 0) sourceC2513) = raw34705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34705; decide +kernel
    rw [ha]
    exact (canonical34705 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2513 + difference 0 5) (sourceB2513 + difference 5 0) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA2513 + difference 0 5) (sourceB2513 + difference 5 0) sourceC2513) = raw34706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34706; decide +kernel
    rw [ha]
    exact (canonical34706 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2513 + difference 1 0) (sourceB2513 + difference 0 1) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA2513 + difference 1 0) (sourceB2513 + difference 0 1) sourceC2513) = raw34707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34707; decide +kernel
    rw [ha]
    exact (canonical34707 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2513 + difference 1 2) (sourceB2513 + difference 2 1) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA2513 + difference 1 2) (sourceB2513 + difference 2 1) sourceC2513) = raw27092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw27092; decide +kernel
    rw [ha]
    exact (canonical27092 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2513 + difference 1 3) (sourceB2513 + difference 3 1) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA2513 + difference 1 3) (sourceB2513 + difference 3 1) sourceC2513) = raw27093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw27093; decide +kernel
    rw [ha]
    exact (canonical27093 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2513 + difference 1 4) (sourceB2513 + difference 4 1) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA2513 + difference 1 4) (sourceB2513 + difference 4 1) sourceC2513) = raw27094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw27094; decide +kernel
    rw [ha]
    exact (canonical27094 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2513 + difference 1 5) (sourceB2513 + difference 5 1) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA2513 + difference 1 5) (sourceB2513 + difference 5 1) sourceC2513) = raw27095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw27095; decide +kernel
    rw [ha]
    exact (canonical27095 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2513 + difference 2 0) (sourceB2513 + difference 0 2) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1664) := by
    have ha : (tripleCharges (sourceA2513 + difference 2 0) (sourceB2513 + difference 0 2) sourceC2513) = raw27102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw27102; decide +kernel
    rw [ha]
    exact (canonical27102 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2513 + difference 2 1) (sourceB2513 + difference 1 2) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2141) := by
    have ha : (tripleCharges (sourceA2513 + difference 2 1) (sourceB2513 + difference 1 2) sourceC2513) = raw34708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34708; decide +kernel
    rw [ha]
    exact (canonical34708 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2513 + difference 2 3) (sourceB2513 + difference 3 2) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA2513 + difference 2 3) (sourceB2513 + difference 3 2) sourceC2513) = raw34709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34709; decide +kernel
    rw [ha]
    exact (canonical34709 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2513 + difference 2 4) (sourceB2513 + difference 4 2) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2513 + difference 2 4) (sourceB2513 + difference 4 2) sourceC2513) = raw34710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34710; decide +kernel
    rw [ha]
    exact (canonical34710 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2513 + difference 2 5) (sourceB2513 + difference 5 2) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2513 + difference 2 5) (sourceB2513 + difference 5 2) sourceC2513) = raw34711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34711; decide +kernel
    rw [ha]
    exact (canonical34711 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2513 + difference 3 0) (sourceB2513 + difference 0 3) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1665) := by
    have ha : (tripleCharges (sourceA2513 + difference 3 0) (sourceB2513 + difference 0 3) sourceC2513) = raw27107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw27107; decide +kernel
    rw [ha]
    exact (canonical27107 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2513 + difference 3 1) (sourceB2513 + difference 1 3) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2142) := by
    have ha : (tripleCharges (sourceA2513 + difference 3 1) (sourceB2513 + difference 1 3) sourceC2513) = raw34712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34712; decide +kernel
    rw [ha]
    exact (canonical34712 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2513 + difference 3 2) (sourceB2513 + difference 2 3) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA2513 + difference 3 2) (sourceB2513 + difference 2 3) sourceC2513) = raw34713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34713; decide +kernel
    rw [ha]
    exact (canonical34713 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2513 + difference 3 4) (sourceB2513 + difference 4 3) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2513 + difference 3 4) (sourceB2513 + difference 4 3) sourceC2513) = raw34714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34714; decide +kernel
    rw [ha]
    exact (canonical34714 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2513 + difference 3 5) (sourceB2513 + difference 5 3) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2513 + difference 3 5) (sourceB2513 + difference 5 3) sourceC2513) = raw34715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34715; decide +kernel
    rw [ha]
    exact (canonical34715 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2513 + difference 4 0) (sourceB2513 + difference 0 4) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA2513 + difference 4 0) (sourceB2513 + difference 0 4) sourceC2513) = raw27112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw27112; decide +kernel
    rw [ha]
    exact (canonical27112 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2513 + difference 4 1) (sourceB2513 + difference 1 4) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2145) := by
    have ha : (tripleCharges (sourceA2513 + difference 4 1) (sourceB2513 + difference 1 4) sourceC2513) = raw34716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34716; decide +kernel
    rw [ha]
    exact (canonical34716 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2513 + difference 4 2) (sourceB2513 + difference 2 4) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA2513 + difference 4 2) (sourceB2513 + difference 2 4) sourceC2513) = raw34717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34717; decide +kernel
    rw [ha]
    exact (canonical34717 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2513 + difference 4 3) (sourceB2513 + difference 3 4) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2513 + difference 4 3) (sourceB2513 + difference 3 4) sourceC2513) = raw34718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34718; decide +kernel
    rw [ha]
    exact (canonical34718 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2513 + difference 4 5) (sourceB2513 + difference 5 4) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA2513 + difference 4 5) (sourceB2513 + difference 5 4) sourceC2513) = raw34719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34719; decide +kernel
    rw [ha]
    exact (canonical34719 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2513 + difference 5 0) (sourceB2513 + difference 0 5) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA2513 + difference 5 0) (sourceB2513 + difference 0 5) sourceC2513) = raw27117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw27117; decide +kernel
    rw [ha]
    exact (canonical27117 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2513 + difference 5 1) (sourceB2513 + difference 1 5) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2145) := by
    have ha : (tripleCharges (sourceA2513 + difference 5 1) (sourceB2513 + difference 1 5) sourceC2513) = raw34720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34720; decide +kernel
    rw [ha]
    exact (canonical34720 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2513 + difference 5 2) (sourceB2513 + difference 2 5) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA2513 + difference 5 2) (sourceB2513 + difference 2 5) sourceC2513) = raw34721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34721; decide +kernel
    rw [ha]
    exact (canonical34721 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2513 + difference 5 3) (sourceB2513 + difference 3 5) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2513 + difference 5 3) (sourceB2513 + difference 3 5) sourceC2513) = raw34722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34722; decide +kernel
    rw [ha]
    exact (canonical34722 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2513 + difference 5 4) (sourceB2513 + difference 4 5) sourceC2513) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA2513 + difference 5 4) (sourceB2513 + difference 4 5) sourceC2513) = raw34723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2513 sourceB2513 sourceC2513 difference raw34723; decide +kernel
    rw [ha]
    exact (canonical34723 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2513 sourceB2513 sourceC2513
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2513, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2514 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2514 + difference 0 1) (sourceB2514 + difference 1 0) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (tripleCharges (sourceA2514 + difference 0 1) (sourceB2514 + difference 1 0) sourceC2514) = raw19360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw19360; decide +kernel
    rw [ha]
    exact (canonical19360 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2514 + difference 0 2) (sourceB2514 + difference 2 0) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2514 + difference 0 2) (sourceB2514 + difference 2 0) sourceC2514) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2514 + difference 0 3) (sourceB2514 + difference 3 0) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2514 + difference 0 3) (sourceB2514 + difference 3 0) sourceC2514) = raw3328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw3328; decide +kernel
    rw [ha]
    exact (canonical3328 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2514 + difference 0 4) (sourceB2514 + difference 4 0) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2514 + difference 0 4) (sourceB2514 + difference 4 0) sourceC2514) = raw19361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw19361; decide +kernel
    rw [ha]
    exact (canonical19361 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2514 + difference 0 5) (sourceB2514 + difference 5 0) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2514 + difference 0 5) (sourceB2514 + difference 5 0) sourceC2514) = raw19362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw19362; decide +kernel
    rw [ha]
    exact (canonical19362 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2514 + difference 1 0) (sourceB2514 + difference 0 1) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA2514 + difference 1 0) (sourceB2514 + difference 0 1) sourceC2514) = raw14364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw14364; decide +kernel
    rw [ha]
    exact (canonical14364 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2514 + difference 1 2) (sourceB2514 + difference 2 1) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA2514 + difference 1 2) (sourceB2514 + difference 2 1) sourceC2514) = raw3331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw3331; decide +kernel
    rw [ha]
    exact (canonical3331 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2514 + difference 1 3) (sourceB2514 + difference 3 1) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA2514 + difference 1 3) (sourceB2514 + difference 3 1) sourceC2514) = raw3327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw3327; decide +kernel
    rw [ha]
    exact (canonical3327 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2514 + difference 1 4) (sourceB2514 + difference 4 1) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA2514 + difference 1 4) (sourceB2514 + difference 4 1) sourceC2514) = raw14366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw14366; decide +kernel
    rw [ha]
    exact (canonical14366 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2514 + difference 1 5) (sourceB2514 + difference 5 1) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA2514 + difference 1 5) (sourceB2514 + difference 5 1) sourceC2514) = raw14367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw14367; decide +kernel
    rw [ha]
    exact (canonical14367 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2514 + difference 2 0) (sourceB2514 + difference 0 2) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA2514 + difference 2 0) (sourceB2514 + difference 0 2) sourceC2514) = raw27298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw27298; decide +kernel
    rw [ha]
    exact (canonical27298 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2514 + difference 2 1) (sourceB2514 + difference 1 2) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2514 + difference 2 1) (sourceB2514 + difference 1 2) sourceC2514) = raw34724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw34724; decide +kernel
    rw [ha]
    exact (canonical34724 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2514 + difference 2 3) (sourceB2514 + difference 3 2) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2514 + difference 2 3) (sourceB2514 + difference 3 2) sourceC2514) = raw34725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw34725; decide +kernel
    rw [ha]
    exact (canonical34725 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2514 + difference 2 4) (sourceB2514 + difference 4 2) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2514 + difference 2 4) (sourceB2514 + difference 4 2) sourceC2514) = raw34726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw34726; decide +kernel
    rw [ha]
    exact (canonical34726 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2514 + difference 2 5) (sourceB2514 + difference 5 2) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2514 + difference 2 5) (sourceB2514 + difference 5 2) sourceC2514) = raw34727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw34727; decide +kernel
    rw [ha]
    exact (canonical34727 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2514 + difference 3 0) (sourceB2514 + difference 0 3) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA2514 + difference 3 0) (sourceB2514 + difference 0 3) sourceC2514) = raw27303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw27303; decide +kernel
    rw [ha]
    exact (canonical27303 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2514 + difference 3 1) (sourceB2514 + difference 1 3) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2514 + difference 3 1) (sourceB2514 + difference 1 3) sourceC2514) = raw34728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw34728; decide +kernel
    rw [ha]
    exact (canonical34728 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2514 + difference 3 2) (sourceB2514 + difference 2 3) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2514 + difference 3 2) (sourceB2514 + difference 2 3) sourceC2514) = raw14369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw14369; decide +kernel
    rw [ha]
    exact (canonical14369 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2514 + difference 3 4) (sourceB2514 + difference 4 3) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2514 + difference 3 4) (sourceB2514 + difference 4 3) sourceC2514) = raw34729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw34729; decide +kernel
    rw [ha]
    exact (canonical34729 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2514 + difference 3 5) (sourceB2514 + difference 5 3) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2514 + difference 3 5) (sourceB2514 + difference 5 3) sourceC2514) = raw34730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw34730; decide +kernel
    rw [ha]
    exact (canonical34730 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2514 + difference 4 0) (sourceB2514 + difference 0 4) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA2514 + difference 4 0) (sourceB2514 + difference 0 4) sourceC2514) = raw27307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw27307; decide +kernel
    rw [ha]
    exact (canonical27307 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2514 + difference 4 1) (sourceB2514 + difference 1 4) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2514 + difference 4 1) (sourceB2514 + difference 1 4) sourceC2514) = raw34731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw34731; decide +kernel
    rw [ha]
    exact (canonical34731 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2514 + difference 4 2) (sourceB2514 + difference 2 4) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2514 + difference 4 2) (sourceB2514 + difference 2 4) sourceC2514) = raw14374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw14374; decide +kernel
    rw [ha]
    exact (canonical14374 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2514 + difference 4 3) (sourceB2514 + difference 3 4) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2514 + difference 4 3) (sourceB2514 + difference 3 4) sourceC2514) = raw31879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw31879; decide +kernel
    rw [ha]
    exact (canonical31879 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2514 + difference 4 5) (sourceB2514 + difference 5 4) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2514 + difference 4 5) (sourceB2514 + difference 5 4) sourceC2514) = raw34732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw34732; decide +kernel
    rw [ha]
    exact (canonical34732 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2514 + difference 5 0) (sourceB2514 + difference 0 5) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA2514 + difference 5 0) (sourceB2514 + difference 0 5) sourceC2514) = raw26358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw26358; decide +kernel
    rw [ha]
    exact (canonical26358 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2514 + difference 5 1) (sourceB2514 + difference 1 5) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2514 + difference 5 1) (sourceB2514 + difference 1 5) sourceC2514) = raw34405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw34405; decide +kernel
    rw [ha]
    exact (canonical34405 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2514 + difference 5 2) (sourceB2514 + difference 2 5) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2514 + difference 5 2) (sourceB2514 + difference 2 5) sourceC2514) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2514 + difference 5 3) (sourceB2514 + difference 3 5) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2514 + difference 5 3) (sourceB2514 + difference 3 5) sourceC2514) = raw11535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw11535; decide +kernel
    rw [ha]
    exact (canonical11535 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2514 + difference 5 4) (sourceB2514 + difference 4 5) sourceC2514) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2514 + difference 5 4) (sourceB2514 + difference 4 5) sourceC2514) = raw34406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2514 sourceB2514 sourceC2514 difference raw34406; decide +kernel
    rw [ha]
    exact (canonical34406 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2514 sourceB2514 sourceC2514
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2514, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2515 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2515 + difference 3 0) (sourceB2515 + difference 0 3) sourceC2515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1814) := by
    have ha : (tripleCharges (sourceA2515 + difference 3 0) (sourceB2515 + difference 0 3) sourceC2515) = raw34733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2515 sourceB2515 sourceC2515 difference raw34733; decide +kernel
    rw [ha]
    exact (canonical34733 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2515 + difference 3 1) (sourceB2515 + difference 1 3) sourceC2515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3131) := by
    have ha : (tripleCharges (sourceA2515 + difference 3 1) (sourceB2515 + difference 1 3) sourceC2515) = raw34734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2515 sourceB2515 sourceC2515 difference raw34734; decide +kernel
    rw [ha]
    exact (canonical34734 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2515 + difference 3 2) (sourceB2515 + difference 2 3) sourceC2515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3365) := by
    have ha : (tripleCharges (sourceA2515 + difference 3 2) (sourceB2515 + difference 2 3) sourceC2515) = raw34735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2515 sourceB2515 sourceC2515 difference raw34735; decide +kernel
    rw [ha]
    exact (canonical34735 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2515 + difference 3 3) (sourceB2515 + difference 3 3) sourceC2515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA2515 + difference 3 3) (sourceB2515 + difference 3 3) sourceC2515) = raw34736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2515 sourceB2515 sourceC2515 difference raw34736; decide +kernel
    rw [ha]
    exact (canonical34736 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2515 + difference 3 4) (sourceB2515 + difference 4 3) sourceC2515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA2515 + difference 3 4) (sourceB2515 + difference 4 3) sourceC2515) = raw34737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2515 sourceB2515 sourceC2515 difference raw34737; decide +kernel
    rw [ha]
    exact (canonical34737 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2515 + difference 3 5) (sourceB2515 + difference 5 3) sourceC2515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA2515 + difference 3 5) (sourceB2515 + difference 5 3) sourceC2515) = raw34738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2515 sourceB2515 sourceC2515 difference raw34738; decide +kernel
    rw [ha]
    exact (canonical34738 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2515 + sourceB2515) sourceC2515) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2515 + sourceB2515) sourceC2515) = raw34739 := by
      apply Matrix.ext; unfold doubleCharges sourceA2515 sourceB2515 sourceC2515 raw34739; decide +kernel
    rw [ha]
    exact (canonical34739 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2515 sourceB2515 sourceC2515
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2515, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2516 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2516 + difference 0 3) (sourceB2516 + difference 3 0) sourceC2516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2516 + difference 0 3) (sourceB2516 + difference 3 0) sourceC2516) = raw34740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2516 sourceB2516 sourceC2516 difference raw34740; decide +kernel
    rw [ha]
    exact (canonical34740 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2516 + difference 1 3) (sourceB2516 + difference 3 1) sourceC2516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA2516 + difference 1 3) (sourceB2516 + difference 3 1) sourceC2516) = raw34741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2516 sourceB2516 sourceC2516 difference raw34741; decide +kernel
    rw [ha]
    exact (canonical34741 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2516 + difference 2 3) (sourceB2516 + difference 3 2) sourceC2516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3032) := by
    have ha : (tripleCharges (sourceA2516 + difference 2 3) (sourceB2516 + difference 3 2) sourceC2516) = raw34742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2516 sourceB2516 sourceC2516 difference raw34742; decide +kernel
    rw [ha]
    exact (canonical34742 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2516 + difference 3 3) (sourceB2516 + difference 3 3) sourceC2516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3045) := by
    have ha : (tripleCharges (sourceA2516 + difference 3 3) (sourceB2516 + difference 3 3) sourceC2516) = raw34743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2516 sourceB2516 sourceC2516 difference raw34743; decide +kernel
    rw [ha]
    exact (canonical34743 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2516 + difference 4 3) (sourceB2516 + difference 3 4) sourceC2516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2362) := by
    have ha : (tripleCharges (sourceA2516 + difference 4 3) (sourceB2516 + difference 3 4) sourceC2516) = raw34744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2516 sourceB2516 sourceC2516 difference raw34744; decide +kernel
    rw [ha]
    exact (canonical34744 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2516 + difference 5 3) (sourceB2516 + difference 3 5) sourceC2516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3033) := by
    have ha : (tripleCharges (sourceA2516 + difference 5 3) (sourceB2516 + difference 3 5) sourceC2516) = raw34745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2516 sourceB2516 sourceC2516 difference raw34745; decide +kernel
    rw [ha]
    exact (canonical34745 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2516 + sourceB2516) sourceC2516) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2516 + sourceB2516) sourceC2516) = raw34746 := by
      apply Matrix.ext; unfold doubleCharges sourceA2516 sourceB2516 sourceC2516 raw34746; decide +kernel
    rw [ha]
    exact (canonical34746 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2516 sourceB2516 sourceC2516
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2516, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2519 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2519 + difference 3 0) (sourceB2519 + difference 0 3) sourceC2519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2343) := by
    have ha : (tripleCharges (sourceA2519 + difference 3 0) (sourceB2519 + difference 0 3) sourceC2519) = raw29381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2519 sourceB2519 sourceC2519 difference raw29381; decide +kernel
    rw [ha]
    exact (canonical29381 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2519 + difference 3 1) (sourceB2519 + difference 1 3) sourceC2519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2819) := by
    have ha : (tripleCharges (sourceA2519 + difference 3 1) (sourceB2519 + difference 1 3) sourceC2519) = raw34760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2519 sourceB2519 sourceC2519 difference raw34760; decide +kernel
    rw [ha]
    exact (canonical34760 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2519 + difference 3 2) (sourceB2519 + difference 2 3) sourceC2519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3673) := by
    have ha : (tripleCharges (sourceA2519 + difference 3 2) (sourceB2519 + difference 2 3) sourceC2519) = raw34761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2519 sourceB2519 sourceC2519 difference raw34761; decide +kernel
    rw [ha]
    exact (canonical34761 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2519 + difference 3 3) (sourceB2519 + difference 3 3) sourceC2519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3699) := by
    have ha : (tripleCharges (sourceA2519 + difference 3 3) (sourceB2519 + difference 3 3) sourceC2519) = raw34762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2519 sourceB2519 sourceC2519 difference raw34762; decide +kernel
    rw [ha]
    exact (canonical34762 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2519 + difference 3 4) (sourceB2519 + difference 4 3) sourceC2519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA2519 + difference 3 4) (sourceB2519 + difference 4 3) sourceC2519) = raw34763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2519 sourceB2519 sourceC2519 difference raw34763; decide +kernel
    rw [ha]
    exact (canonical34763 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2519 + difference 3 5) (sourceB2519 + difference 5 3) sourceC2519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA2519 + difference 3 5) (sourceB2519 + difference 5 3) sourceC2519) = raw34764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2519 sourceB2519 sourceC2519 difference raw34764; decide +kernel
    rw [ha]
    exact (canonical34764 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2519 + sourceB2519) sourceC2519) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2519 + sourceB2519) sourceC2519) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA2519 sourceB2519 sourceC2519 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2519 sourceB2519 sourceC2519
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2519, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2520 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2520 + difference 2 0) (sourceB2520 + difference 0 2) sourceC2520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2324) := by
    have ha : (tripleCharges (sourceA2520 + difference 2 0) (sourceB2520 + difference 0 2) sourceC2520) = raw29405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2520 sourceB2520 sourceC2520 difference raw29405; decide +kernel
    rw [ha]
    exact (canonical29405 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2520 + difference 2 1) (sourceB2520 + difference 1 2) sourceC2520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2801) := by
    have ha : (tripleCharges (sourceA2520 + difference 2 1) (sourceB2520 + difference 1 2) sourceC2520) = raw34765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2520 sourceB2520 sourceC2520 difference raw34765; decide +kernel
    rw [ha]
    exact (canonical34765 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2520 + difference 2 2) (sourceB2520 + difference 2 2) sourceC2520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3685) := by
    have ha : (tripleCharges (sourceA2520 + difference 2 2) (sourceB2520 + difference 2 2) sourceC2520) = raw34766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2520 sourceB2520 sourceC2520 difference raw34766; decide +kernel
    rw [ha]
    exact (canonical34766 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2520 + difference 2 3) (sourceB2520 + difference 3 2) sourceC2520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3676) := by
    have ha : (tripleCharges (sourceA2520 + difference 2 3) (sourceB2520 + difference 3 2) sourceC2520) = raw34767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2520 sourceB2520 sourceC2520 difference raw34767; decide +kernel
    rw [ha]
    exact (canonical34767 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2520 + difference 2 4) (sourceB2520 + difference 4 2) sourceC2520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2520 + difference 2 4) (sourceB2520 + difference 4 2) sourceC2520) = raw34768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2520 sourceB2520 sourceC2520 difference raw34768; decide +kernel
    rw [ha]
    exact (canonical34768 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2520 + difference 2 5) (sourceB2520 + difference 5 2) sourceC2520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA2520 + difference 2 5) (sourceB2520 + difference 5 2) sourceC2520) = raw34769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2520 sourceB2520 sourceC2520 difference raw34769; decide +kernel
    rw [ha]
    exact (canonical34769 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2520 + sourceB2520) sourceC2520) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2520 + sourceB2520) sourceC2520) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA2520 sourceB2520 sourceC2520 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2520 sourceB2520 sourceC2520
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2520, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2521 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2521 + difference 0 2) (sourceB2521 + difference 2 0) sourceC2521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3722) := by
    have ha : (tripleCharges (sourceA2521 + difference 0 2) (sourceB2521 + difference 2 0) sourceC2521) = raw34770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2521 sourceB2521 sourceC2521 difference raw34770; decide +kernel
    rw [ha]
    exact (canonical34770 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2521 + difference 1 2) (sourceB2521 + difference 2 1) sourceC2521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA2521 + difference 1 2) (sourceB2521 + difference 2 1) sourceC2521) = raw29455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2521 sourceB2521 sourceC2521 difference raw29455; decide +kernel
    rw [ha]
    exact (canonical29455 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2521 + difference 2 2) (sourceB2521 + difference 2 2) sourceC2521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3715) := by
    have ha : (tripleCharges (sourceA2521 + difference 2 2) (sourceB2521 + difference 2 2) sourceC2521) = raw34771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2521 sourceB2521 sourceC2521 difference raw34771; decide +kernel
    rw [ha]
    exact (canonical34771 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2521 + difference 3 2) (sourceB2521 + difference 2 3) sourceC2521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3708) := by
    have ha : (tripleCharges (sourceA2521 + difference 3 2) (sourceB2521 + difference 2 3) sourceC2521) = raw34772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2521 sourceB2521 sourceC2521 difference raw34772; decide +kernel
    rw [ha]
    exact (canonical34772 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2521 + difference 4 2) (sourceB2521 + difference 2 4) sourceC2521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3134) := by
    have ha : (tripleCharges (sourceA2521 + difference 4 2) (sourceB2521 + difference 2 4) sourceC2521) = raw34773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2521 sourceB2521 sourceC2521 difference raw34773; decide +kernel
    rw [ha]
    exact (canonical34773 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2521 + difference 5 2) (sourceB2521 + difference 2 5) sourceC2521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2350) := by
    have ha : (tripleCharges (sourceA2521 + difference 5 2) (sourceB2521 + difference 2 5) sourceC2521) = raw34774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2521 sourceB2521 sourceC2521 difference raw34774; decide +kernel
    rw [ha]
    exact (canonical34774 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2521 + sourceB2521) sourceC2521) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2521 + sourceB2521) sourceC2521) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA2521 sourceB2521 sourceC2521 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2521 sourceB2521 sourceC2521
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2521, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2522 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2522 + difference 0 2) (sourceB2522 + difference 2 0) sourceC2522) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3922) := by
    have ha : (tripleCharges (sourceA2522 + difference 0 2) (sourceB2522 + difference 2 0) sourceC2522) = raw34775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2522 sourceB2522 sourceC2522 difference raw34775; decide +kernel
    rw [ha]
    exact (canonical34775 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2522 + difference 1 2) (sourceB2522 + difference 2 1) sourceC2522) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA2522 + difference 1 2) (sourceB2522 + difference 2 1) sourceC2522) = raw29482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2522 sourceB2522 sourceC2522 difference raw29482; decide +kernel
    rw [ha]
    exact (canonical29482 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2522 + difference 2 2) (sourceB2522 + difference 2 2) sourceC2522) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3716) := by
    have ha : (tripleCharges (sourceA2522 + difference 2 2) (sourceB2522 + difference 2 2) sourceC2522) = raw34776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2522 sourceB2522 sourceC2522 difference raw34776; decide +kernel
    rw [ha]
    exact (canonical34776 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2522 + difference 3 2) (sourceB2522 + difference 2 3) sourceC2522) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3709) := by
    have ha : (tripleCharges (sourceA2522 + difference 3 2) (sourceB2522 + difference 2 3) sourceC2522) = raw34777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2522 sourceB2522 sourceC2522 difference raw34777; decide +kernel
    rw [ha]
    exact (canonical34777 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2522 + difference 4 2) (sourceB2522 + difference 2 4) sourceC2522) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2824) := by
    have ha : (tripleCharges (sourceA2522 + difference 4 2) (sourceB2522 + difference 2 4) sourceC2522) = raw34778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2522 sourceB2522 sourceC2522 difference raw34778; decide +kernel
    rw [ha]
    exact (canonical34778 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2522 + difference 5 2) (sourceB2522 + difference 2 5) sourceC2522) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2824) := by
    have ha : (tripleCharges (sourceA2522 + difference 5 2) (sourceB2522 + difference 2 5) sourceC2522) = raw34779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2522 sourceB2522 sourceC2522 difference raw34779; decide +kernel
    rw [ha]
    exact (canonical34779 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2522 + sourceB2522) sourceC2522) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2522 + sourceB2522) sourceC2522) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA2522 sourceB2522 sourceC2522 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2522 sourceB2522 sourceC2522
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2522, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2017 : Integer.Sparse.reindex keyMap MixedData.row2017 = numericRow2017 := by decide +kernel

theorem numericCheck2017 (x : Master → ℝ) : Integer.Sparse.eval numericRow2017 x =
    (1 : ℝ) * reducedSource2017 x := by
  norm_num [numericRow2017, reducedSource2017, Integer.Sparse.eval, Sparse.eval, nodeValue2688, nodeValue2690, nodeValue2700, nodeValue3257, nodeValue3304, nodeValue3521, nodeValue3546, nodeValue3554, nodeValue3562, nodeValue3581, nodeValue3844, nodeValue3867, nodeValue3875]

theorem reindexCheck2020 : Integer.Sparse.reindex keyMap MixedData.row2020 = numericRow2020 := by decide +kernel

theorem numericCheck2020 (x : Master → ℝ) : Integer.Sparse.eval numericRow2020 x =
    (1 : ℝ) * reducedSource2020 x := by
  norm_num [numericRow2020, reducedSource2020, Integer.Sparse.eval, Sparse.eval, nodeValue1703, nodeValue1706, nodeValue1711, nodeValue2238, nodeValue2240, nodeValue2243, nodeValue2248, nodeValue2250, nodeValue2260, nodeValue2263, nodeValue2275, nodeValue2747, nodeValue2750, nodeValue2764]

theorem reindexCheck2024 : Integer.Sparse.reindex keyMap MixedData.row2024 = numericRow2024 := by decide +kernel

theorem numericCheck2024 (x : Master → ℝ) : Integer.Sparse.eval numericRow2024 x =
    (1 : ℝ) * reducedSource2024 x := by
  norm_num [numericRow2024, reducedSource2024, Integer.Sparse.eval, Sparse.eval, nodeValue1664, nodeValue1665, nodeValue1668, nodeValue1708, nodeValue2141, nodeValue2142, nodeValue2145, nodeValue2190, nodeValue2192, nodeValue2195, nodeValue2196, nodeValue2205, nodeValue2206, nodeValue2216, nodeValue2244, nodeValue2245, nodeValue2265, nodeValue2662, nodeValue2709, nodeValue2710, nodeValue2723]

theorem reindexCheck2025 : Integer.Sparse.reindex keyMap MixedData.row2025 = numericRow2025 := by decide +kernel

theorem numericCheck2025 (x : Master → ℝ) : Integer.Sparse.eval numericRow2025 x =
    (1 : ℝ) * reducedSource2025 x := by
  norm_num [numericRow2025, reducedSource2025, Integer.Sparse.eval, Sparse.eval, nodeValue4063, nodeValue4068, nodeValue4073, nodeValue4080, nodeValue4083, nodeValue4087, nodeValue4091]

theorem reindexCheck2026 : Integer.Sparse.reindex keyMap MixedData.row2026 = numericRow2026 := by decide +kernel

theorem numericCheck2026 (x : Master → ℝ) : Integer.Sparse.eval numericRow2026 x =
    (1 : ℝ) * reducedSource2026 x := by
  norm_num [numericRow2026, reducedSource2026, Integer.Sparse.eval, Sparse.eval, nodeValue1814, nodeValue3131, nodeValue3365, nodeValue3379, nodeValue3391, nodeValue3395, nodeValue4084]

theorem reindexCheck2027 : Integer.Sparse.reindex keyMap MixedData.row2027 = numericRow2027 := by decide +kernel

theorem numericCheck2027 (x : Master → ℝ) : Integer.Sparse.eval numericRow2027 x =
    (1 : ℝ) * reducedSource2027 x := by
  norm_num [numericRow2027, reducedSource2027, Integer.Sparse.eval, Sparse.eval, nodeValue2362, nodeValue3032, nodeValue3033, nodeValue3040, nodeValue3045, nodeValue3732, nodeValue4092]

theorem reindexCheck2028 : Integer.Sparse.reindex keyMap MixedData.row2028 = numericRow2028 := by decide +kernel

theorem numericCheck2028 (x : Master → ℝ) : Integer.Sparse.eval numericRow2028 x =
    (1 : ℝ) * reducedSource2028 x := by
  norm_num [numericRow2028, reducedSource2028, Integer.Sparse.eval, Sparse.eval, nodeValue2343, nodeValue2819, nodeValue3673, nodeValue3699, nodeValue3705, nodeValue3706, nodeValue4092]

theorem reindexCheck2029 : Integer.Sparse.reindex keyMap MixedData.row2029 = numericRow2029 := by decide +kernel

theorem numericCheck2029 (x : Master → ℝ) : Integer.Sparse.eval numericRow2029 x =
    (1 : ℝ) * reducedSource2029 x := by
  norm_num [numericRow2029, reducedSource2029, Integer.Sparse.eval, Sparse.eval, nodeValue2324, nodeValue2801, nodeValue3676, nodeValue3685, nodeValue3690, nodeValue3692, nodeValue4091]

theorem reindexCheck2030 : Integer.Sparse.reindex keyMap MixedData.row2030 = numericRow2030 := by decide +kernel

theorem numericCheck2030 (x : Master → ℝ) : Integer.Sparse.eval numericRow2030 x =
    (1 : ℝ) * reducedSource2030 x := by
  norm_num [numericRow2030, reducedSource2030, Integer.Sparse.eval, Sparse.eval, nodeValue2350, nodeValue3134, nodeValue3708, nodeValue3715, nodeValue3719, nodeValue3722, nodeValue4092]

theorem reindexCheck2031 : Integer.Sparse.reindex keyMap MixedData.row2031 = numericRow2031 := by decide +kernel

theorem numericCheck2031 (x : Master → ℝ) : Integer.Sparse.eval numericRow2031 x =
    (1 : ℝ) * reducedSource2031 x := by
  norm_num [numericRow2031, reducedSource2031, Integer.Sparse.eval, Sparse.eval, nodeValue2824, nodeValue3709, nodeValue3716, nodeValue3779, nodeValue3922, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2017 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2017 (mixedVector B) = 0 := by
  have h2688 : mixedVector B (Sum.inr 2688) = Sparse.eval nodeValue2688 (mixedVector B) := by
    change mixedMoment B node2688 node2688Labels = _
    exact sound2688 B hB hF
  have h2690 : mixedVector B (Sum.inr 2690) = Sparse.eval nodeValue2690 (mixedVector B) := by
    change mixedMoment B node2690 node2690Labels = _
    exact sound2690 B hB hF
  have h2700 : mixedVector B (Sum.inr 2700) = Sparse.eval nodeValue2700 (mixedVector B) := by
    change mixedMoment B node2700 node2700Labels = _
    exact sound2700 B hB hF
  have h3257 : mixedVector B (Sum.inr 3257) = Sparse.eval nodeValue3257 (mixedVector B) := by
    change mixedMoment B node3257 node3257Labels = _
    exact sound3257 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h3521 : mixedVector B (Sum.inr 3521) = Sparse.eval nodeValue3521 (mixedVector B) := by
    change mixedMoment B node3521 node3521Labels = _
    exact sound3521 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  have h3554 : mixedVector B (Sum.inr 3554) = Sparse.eval nodeValue3554 (mixedVector B) := by
    change mixedMoment B node3554 node3554Labels = _
    exact sound3554 B hB hF
  have h3562 : mixedVector B (Sum.inr 3562) = Sparse.eval nodeValue3562 (mixedVector B) := by
    change mixedMoment B node3562 node3562Labels = _
    exact sound3562 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h3844 : mixedVector B (Sum.inr 3844) = Sparse.eval nodeValue3844 (mixedVector B) := by
    change mixedMoment B node3844 node3844Labels = _
    exact sound3844 B hB hF
  have h3867 : mixedVector B (Sum.inr 3867) = Sparse.eval nodeValue3867 (mixedVector B) := by
    change mixedMoment B node3867 node3867Labels = _
    exact sound3867 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  simpa only [sourceForm2503, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2688, h2690, h2700, h3257, h3304, h3521, h3546, h3554, h3562, h3581, h3844, h3867, h3875, reducedSource2017] using sourceEq2503 B hB

theorem rowSound2017 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2017 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2017, numericCheck2017, reducedZero2017 B hB hF, mul_zero]

theorem reducedZero2020 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2020 (mixedVector B) = 0 := by
  have h1703 : mixedVector B (Sum.inr 1703) = Sparse.eval nodeValue1703 (mixedVector B) := by
    change mixedMoment B node1703 node1703Labels = _
    exact sound1703 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h1711 : mixedVector B (Sum.inr 1711) = Sparse.eval nodeValue1711 (mixedVector B) := by
    change mixedMoment B node1711 node1711Labels = _
    exact sound1711 B hB hF
  have h2238 : mixedVector B (Sum.inr 2238) = Sparse.eval nodeValue2238 (mixedVector B) := by
    change mixedMoment B node2238 node2238Labels = _
    exact sound2238 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h2248 : mixedVector B (Sum.inr 2248) = Sparse.eval nodeValue2248 (mixedVector B) := by
    change mixedMoment B node2248 node2248Labels = _
    exact sound2248 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h2747 : mixedVector B (Sum.inr 2747) = Sparse.eval nodeValue2747 (mixedVector B) := by
    change mixedMoment B node2747 node2747Labels = _
    exact sound2747 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  simpa only [sourceForm2509, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1703, h1706, h1711, h2238, h2240, h2243, h2248, h2250, h2260, h2263, h2275, h2747, h2750, h2764, reducedSource2020] using sourceEq2509 B hB

theorem rowSound2020 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2020 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2020, numericCheck2020, reducedZero2020 B hB hF, mul_zero]

theorem reducedZero2024 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2024 (mixedVector B) = 0 := by
  have h1664 : mixedVector B (Sum.inr 1664) = Sparse.eval nodeValue1664 (mixedVector B) := by
    change mixedMoment B node1664 node1664Labels = _
    exact sound1664 B hB hF
  have h1665 : mixedVector B (Sum.inr 1665) = Sparse.eval nodeValue1665 (mixedVector B) := by
    change mixedMoment B node1665 node1665Labels = _
    exact sound1665 B hB hF
  have h1668 : mixedVector B (Sum.inr 1668) = Sparse.eval nodeValue1668 (mixedVector B) := by
    change mixedMoment B node1668 node1668Labels = _
    exact sound1668 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h2141 : mixedVector B (Sum.inr 2141) = Sparse.eval nodeValue2141 (mixedVector B) := by
    change mixedMoment B node2141 node2141Labels = _
    exact sound2141 B hB hF
  have h2142 : mixedVector B (Sum.inr 2142) = Sparse.eval nodeValue2142 (mixedVector B) := by
    change mixedMoment B node2142 node2142Labels = _
    exact sound2142 B hB hF
  have h2145 : mixedVector B (Sum.inr 2145) = Sparse.eval nodeValue2145 (mixedVector B) := by
    change mixedMoment B node2145 node2145Labels = _
    exact sound2145 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2192 : mixedVector B (Sum.inr 2192) = Sparse.eval nodeValue2192 (mixedVector B) := by
    change mixedMoment B node2192 node2192Labels = _
    exact sound2192 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2196 : mixedVector B (Sum.inr 2196) = Sparse.eval nodeValue2196 (mixedVector B) := by
    change mixedMoment B node2196 node2196Labels = _
    exact sound2196 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h2662 : mixedVector B (Sum.inr 2662) = Sparse.eval nodeValue2662 (mixedVector B) := by
    change mixedMoment B node2662 node2662Labels = _
    exact sound2662 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  simpa only [sourceForm2513, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1664, h1665, h1668, h1708, h2141, h2142, h2145, h2190, h2192, h2195, h2196, h2205, h2206, h2216, h2244, h2245, h2265, h2662, h2709, h2710, h2723, reducedSource2024] using sourceEq2513 B hB

theorem rowSound2024 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2024 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2024, numericCheck2024, reducedZero2024 B hB hF, mul_zero]

theorem reducedZero2025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2025 (mixedVector B) = 0 := by
  have h4063 : mixedVector B (Sum.inr 4063) = Sparse.eval nodeValue4063 (mixedVector B) := by
    change mixedMoment B node4063 node4063Labels = _
    exact sound4063 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  have h4073 : mixedVector B (Sum.inr 4073) = Sparse.eval nodeValue4073 (mixedVector B) := by
    change mixedMoment B node4073 node4073Labels = _
    exact sound4073 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2514, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4063, h4068, h4073, h4080, h4083, h4087, h4091, reducedSource2025] using sourceEq2514 B hB

theorem rowSound2025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2025 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2025, numericCheck2025, reducedZero2025 B hB hF, mul_zero]

theorem reducedZero2026 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2026 (mixedVector B) = 0 := by
  have h1814 : mixedVector B (Sum.inr 1814) = Sparse.eval nodeValue1814 (mixedVector B) := by
    change mixedMoment B node1814 node1814Labels = _
    exact sound1814 B hB hF
  have h3131 : mixedVector B (Sum.inr 3131) = Sparse.eval nodeValue3131 (mixedVector B) := by
    change mixedMoment B node3131 node3131Labels = _
    exact sound3131 B hB hF
  have h3365 : mixedVector B (Sum.inr 3365) = Sparse.eval nodeValue3365 (mixedVector B) := by
    change mixedMoment B node3365 node3365Labels = _
    exact sound3365 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h3391 : mixedVector B (Sum.inr 3391) = Sparse.eval nodeValue3391 (mixedVector B) := by
    change mixedMoment B node3391 node3391Labels = _
    exact sound3391 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2515, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1814, h3131, h3365, h3379, h3391, h3395, h4084, reducedSource2026] using sourceEq2515 B hB

theorem rowSound2026 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2026 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2026, numericCheck2026, reducedZero2026 B hB hF, mul_zero]

theorem reducedZero2027 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2027 (mixedVector B) = 0 := by
  have h2362 : mixedVector B (Sum.inr 2362) = Sparse.eval nodeValue2362 (mixedVector B) := by
    change mixedMoment B node2362 node2362Labels = _
    exact sound2362 B hB hF
  have h3032 : mixedVector B (Sum.inr 3032) = Sparse.eval nodeValue3032 (mixedVector B) := by
    change mixedMoment B node3032 node3032Labels = _
    exact sound3032 B hB hF
  have h3033 : mixedVector B (Sum.inr 3033) = Sparse.eval nodeValue3033 (mixedVector B) := by
    change mixedMoment B node3033 node3033Labels = _
    exact sound3033 B hB hF
  have h3040 : mixedVector B (Sum.inr 3040) = Sparse.eval nodeValue3040 (mixedVector B) := by
    change mixedMoment B node3040 node3040Labels = _
    exact sound3040 B hB hF
  have h3045 : mixedVector B (Sum.inr 3045) = Sparse.eval nodeValue3045 (mixedVector B) := by
    change mixedMoment B node3045 node3045Labels = _
    exact sound3045 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2516, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2362, h3032, h3033, h3040, h3045, h3732, h4092, reducedSource2027] using sourceEq2516 B hB

theorem rowSound2027 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2027 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2027, numericCheck2027, reducedZero2027 B hB hF, mul_zero]

theorem reducedZero2028 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2028 (mixedVector B) = 0 := by
  have h2343 : mixedVector B (Sum.inr 2343) = Sparse.eval nodeValue2343 (mixedVector B) := by
    change mixedMoment B node2343 node2343Labels = _
    exact sound2343 B hB hF
  have h2819 : mixedVector B (Sum.inr 2819) = Sparse.eval nodeValue2819 (mixedVector B) := by
    change mixedMoment B node2819 node2819Labels = _
    exact sound2819 B hB hF
  have h3673 : mixedVector B (Sum.inr 3673) = Sparse.eval nodeValue3673 (mixedVector B) := by
    change mixedMoment B node3673 node3673Labels = _
    exact sound3673 B hB hF
  have h3699 : mixedVector B (Sum.inr 3699) = Sparse.eval nodeValue3699 (mixedVector B) := by
    change mixedMoment B node3699 node3699Labels = _
    exact sound3699 B hB hF
  have h3705 : mixedVector B (Sum.inr 3705) = Sparse.eval nodeValue3705 (mixedVector B) := by
    change mixedMoment B node3705 node3705Labels = _
    exact sound3705 B hB hF
  have h3706 : mixedVector B (Sum.inr 3706) = Sparse.eval nodeValue3706 (mixedVector B) := by
    change mixedMoment B node3706 node3706Labels = _
    exact sound3706 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2519, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2343, h2819, h3673, h3699, h3705, h3706, h4092, reducedSource2028] using sourceEq2519 B hB

theorem rowSound2028 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2028 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2028, numericCheck2028, reducedZero2028 B hB hF, mul_zero]

theorem reducedZero2029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2029 (mixedVector B) = 0 := by
  have h2324 : mixedVector B (Sum.inr 2324) = Sparse.eval nodeValue2324 (mixedVector B) := by
    change mixedMoment B node2324 node2324Labels = _
    exact sound2324 B hB hF
  have h2801 : mixedVector B (Sum.inr 2801) = Sparse.eval nodeValue2801 (mixedVector B) := by
    change mixedMoment B node2801 node2801Labels = _
    exact sound2801 B hB hF
  have h3676 : mixedVector B (Sum.inr 3676) = Sparse.eval nodeValue3676 (mixedVector B) := by
    change mixedMoment B node3676 node3676Labels = _
    exact sound3676 B hB hF
  have h3685 : mixedVector B (Sum.inr 3685) = Sparse.eval nodeValue3685 (mixedVector B) := by
    change mixedMoment B node3685 node3685Labels = _
    exact sound3685 B hB hF
  have h3690 : mixedVector B (Sum.inr 3690) = Sparse.eval nodeValue3690 (mixedVector B) := by
    change mixedMoment B node3690 node3690Labels = _
    exact sound3690 B hB hF
  have h3692 : mixedVector B (Sum.inr 3692) = Sparse.eval nodeValue3692 (mixedVector B) := by
    change mixedMoment B node3692 node3692Labels = _
    exact sound3692 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2520, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2324, h2801, h3676, h3685, h3690, h3692, h4091, reducedSource2029] using sourceEq2520 B hB

theorem rowSound2029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2029 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2029, numericCheck2029, reducedZero2029 B hB hF, mul_zero]

theorem reducedZero2030 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2030 (mixedVector B) = 0 := by
  have h2350 : mixedVector B (Sum.inr 2350) = Sparse.eval nodeValue2350 (mixedVector B) := by
    change mixedMoment B node2350 node2350Labels = _
    exact sound2350 B hB hF
  have h3134 : mixedVector B (Sum.inr 3134) = Sparse.eval nodeValue3134 (mixedVector B) := by
    change mixedMoment B node3134 node3134Labels = _
    exact sound3134 B hB hF
  have h3708 : mixedVector B (Sum.inr 3708) = Sparse.eval nodeValue3708 (mixedVector B) := by
    change mixedMoment B node3708 node3708Labels = _
    exact sound3708 B hB hF
  have h3715 : mixedVector B (Sum.inr 3715) = Sparse.eval nodeValue3715 (mixedVector B) := by
    change mixedMoment B node3715 node3715Labels = _
    exact sound3715 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h3722 : mixedVector B (Sum.inr 3722) = Sparse.eval nodeValue3722 (mixedVector B) := by
    change mixedMoment B node3722 node3722Labels = _
    exact sound3722 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2521, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2350, h3134, h3708, h3715, h3719, h3722, h4092, reducedSource2030] using sourceEq2521 B hB

theorem rowSound2030 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2030 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2030, numericCheck2030, reducedZero2030 B hB hF, mul_zero]

theorem reducedZero2031 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2031 (mixedVector B) = 0 := by
  have h2824 : mixedVector B (Sum.inr 2824) = Sparse.eval nodeValue2824 (mixedVector B) := by
    change mixedMoment B node2824 node2824Labels = _
    exact sound2824 B hB hF
  have h3709 : mixedVector B (Sum.inr 3709) = Sparse.eval nodeValue3709 (mixedVector B) := by
    change mixedMoment B node3709 node3709Labels = _
    exact sound3709 B hB hF
  have h3716 : mixedVector B (Sum.inr 3716) = Sparse.eval nodeValue3716 (mixedVector B) := by
    change mixedMoment B node3716 node3716Labels = _
    exact sound3716 B hB hF
  have h3779 : mixedVector B (Sum.inr 3779) = Sparse.eval nodeValue3779 (mixedVector B) := by
    change mixedMoment B node3779 node3779Labels = _
    exact sound3779 B hB hF
  have h3922 : mixedVector B (Sum.inr 3922) = Sparse.eval nodeValue3922 (mixedVector B) := by
    change mixedMoment B node3922 node3922Labels = _
    exact sound3922 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2522, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2824, h3709, h3716, h3779, h3922, h4091, reducedSource2031] using sourceEq2522 B hB

theorem rowSound2031 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2031 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2031, numericCheck2031, reducedZero2031 B hB hF, mul_zero]

theorem sourceRowsAt2016 : MixedData.sourceRows (2016 : Fin 2425) =
    MixedData.row2016 := by decide +kernel

theorem sourceRowsAt2017 : MixedData.sourceRows (2017 : Fin 2425) =
    MixedData.row2017 := by decide +kernel

theorem sourceRowsAt2018 : MixedData.sourceRows (2018 : Fin 2425) =
    MixedData.row2018 := by decide +kernel

theorem sourceRowsAt2019 : MixedData.sourceRows (2019 : Fin 2425) =
    MixedData.row2019 := by decide +kernel

theorem sourceRowsAt2020 : MixedData.sourceRows (2020 : Fin 2425) =
    MixedData.row2020 := by decide +kernel

theorem sourceRowsAt2021 : MixedData.sourceRows (2021 : Fin 2425) =
    MixedData.row2021 := by decide +kernel

theorem sourceRowsAt2022 : MixedData.sourceRows (2022 : Fin 2425) =
    MixedData.row2022 := by decide +kernel

theorem sourceRowsAt2023 : MixedData.sourceRows (2023 : Fin 2425) =
    MixedData.row2023 := by decide +kernel

theorem sourceRowsAt2024 : MixedData.sourceRows (2024 : Fin 2425) =
    MixedData.row2024 := by decide +kernel

theorem sourceRowsAt2025 : MixedData.sourceRows (2025 : Fin 2425) =
    MixedData.row2025 := by decide +kernel

theorem sourceRowsAt2026 : MixedData.sourceRows (2026 : Fin 2425) =
    MixedData.row2026 := by decide +kernel

theorem sourceRowsAt2027 : MixedData.sourceRows (2027 : Fin 2425) =
    MixedData.row2027 := by decide +kernel

theorem sourceRowsAt2028 : MixedData.sourceRows (2028 : Fin 2425) =
    MixedData.row2028 := by decide +kernel

theorem sourceRowsAt2029 : MixedData.sourceRows (2029 : Fin 2425) =
    MixedData.row2029 := by decide +kernel

theorem sourceRowsAt2030 : MixedData.sourceRows (2030 : Fin 2425) =
    MixedData.row2030 := by decide +kernel

theorem sourceRowsAt2031 : MixedData.sourceRows (2031 : Fin 2425) =
    MixedData.row2031 := by decide +kernel

theorem chunkSound126_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 126) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2016 ∨ k.val = 2017 ∨ k.val = 2018 ∨ k.val = 2019 ∨ k.val = 2020 ∨ k.val = 2021 ∨ k.val = 2022 ∨ k.val = 2023 ∨ k.val = 2024 ∨ k.val = 2025 ∨ k.val = 2026 ∨ k.val = 2027 ∨ k.val = 2028 ∨ k.val = 2029 ∨ k.val = 2030 ∨ k.val = 2031 := by omega
  rcases heq with h2016 | h2017 | h2018 | h2019 | h2020 | h2021 | h2022 | h2023 | h2024 | h2025 | h2026 | h2027 | h2028 | h2029 | h2030 | h2031
  · have he : k = (2016 : Fin 2425) := Fin.ext h2016
    subst k
    rw [sourceRowsAt2016]
    exact rowSound2016_e B hB hF
  · have he : k = (2017 : Fin 2425) := Fin.ext h2017
    subst k
    rw [sourceRowsAt2017]
    exact rowSound2017 B hB hF
  · have he : k = (2018 : Fin 2425) := Fin.ext h2018
    subst k
    rw [sourceRowsAt2018]
    exact rowSound2018_e B hB hF
  · have he : k = (2019 : Fin 2425) := Fin.ext h2019
    subst k
    rw [sourceRowsAt2019]
    exact rowSound2019_e B hB hF
  · have he : k = (2020 : Fin 2425) := Fin.ext h2020
    subst k
    rw [sourceRowsAt2020]
    exact rowSound2020 B hB hF
  · have he : k = (2021 : Fin 2425) := Fin.ext h2021
    subst k
    rw [sourceRowsAt2021]
    exact rowSound2021_e B hB hF
  · have he : k = (2022 : Fin 2425) := Fin.ext h2022
    subst k
    rw [sourceRowsAt2022]
    exact rowSound2022_e B hB hF
  · have he : k = (2023 : Fin 2425) := Fin.ext h2023
    subst k
    rw [sourceRowsAt2023]
    exact rowSound2023_e B hB hF
  · have he : k = (2024 : Fin 2425) := Fin.ext h2024
    subst k
    rw [sourceRowsAt2024]
    exact rowSound2024 B hB hF
  · have he : k = (2025 : Fin 2425) := Fin.ext h2025
    subst k
    rw [sourceRowsAt2025]
    exact rowSound2025 B hB hF
  · have he : k = (2026 : Fin 2425) := Fin.ext h2026
    subst k
    rw [sourceRowsAt2026]
    exact rowSound2026 B hB hF
  · have he : k = (2027 : Fin 2425) := Fin.ext h2027
    subst k
    rw [sourceRowsAt2027]
    exact rowSound2027 B hB hF
  · have he : k = (2028 : Fin 2425) := Fin.ext h2028
    subst k
    rw [sourceRowsAt2028]
    exact rowSound2028 B hB hF
  · have he : k = (2029 : Fin 2425) := Fin.ext h2029
    subst k
    rw [sourceRowsAt2029]
    exact rowSound2029 B hB hF
  · have he : k = (2030 : Fin 2425) := Fin.ext h2030
    subst k
    rw [sourceRowsAt2030]
    exact rowSound2030 B hB hF
  · have he : k = (2031 : Fin 2425) := Fin.ext h2031
    subst k
    rw [sourceRowsAt2031]
    exact rowSound2031 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e_oai
