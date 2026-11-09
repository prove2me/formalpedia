-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:35:48.300597+00:00
-- url     : https://prove2.me/submissions/f2beefef-c9ea-4d8c-9aa3-4abed4898428

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1108_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1109_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1110_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1111_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1114_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1115_e

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

theorem canonical19680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19680 raw19680Labels = mixedMoment B node1540 node1540Labels := by
  calc
    mixedMoment B raw19680 raw19680Labels = mixedMoment B raw19680step0 raw19680step0Labels := by
      have hz : ∀ j, raw19680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19680step0 = (fun i j => raw19680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19680step0 raw19680; decide +kernel
      have hl : raw19680step0Labels = raw19680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19680 raw19680Labels permutation434 hz
    mixedMoment B raw19680step0 raw19680step0Labels = mixedMoment B raw19680step1 raw19680step1Labels := by
      have hz : ∀ j, raw19680step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19680step1 = (fun i j => raw19680step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19680step1 raw19680step0; decide +kernel
      have hl : raw19680step1Labels = raw19680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19680step0 raw19680step0Labels permutation80 hz
    mixedMoment B raw19680step1 raw19680step1Labels = mixedMoment B raw19680step2 raw19680step2Labels := by
      have hz : ∀ j, raw19680step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19680step2 = (fun i j => raw19680step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19680step2 raw19680step1; decide +kernel
      have hl : raw19680step2Labels = raw19680step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19680step1 raw19680step1Labels permutation14 hz
    mixedMoment B raw19680step2 raw19680step2Labels = mixedMoment B raw19680step3 raw19680step3Labels := by
      have ha : raw19680step3 = (fun i j => raw19680step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19680step3 raw19680step2; decide +kernel
      have hl : raw19680step3Labels = raw19680step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19680step2 raw19680step2Labels permutation3 permutation5
    mixedMoment B raw19680step3 raw19680step3Labels = mixedMoment B raw19680step4 raw19680step4Labels := by
      have ha : raw19680step4 = -raw19680step3 := by apply Matrix.ext; change ∀ i j, raw19680step4 i j = -(raw19680step3 i j); unfold raw19680step4 raw19680step3; decide +kernel
      have hl : raw19680step4Labels = raw19680step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19680step4 raw19680step4Labels = mixedMoment B raw19680step5 raw19680step5Labels := by
      have ha : raw19680step5 = raw19680step4 := by apply Matrix.ext; unfold raw19680step5 raw19680step4; decide +kernel
      have hl : raw19680step4Labels = labelEmbedding1 ∘ raw19680step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19680step4 raw19680step4Labels raw19680step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1540 node1540Labels := by rfl

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

theorem canonical19682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19682 raw19682Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw19682 raw19682Labels = mixedMoment B raw19682step0 raw19682step0Labels := by
      have hz : ∀ j, raw19682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19682step0 = (fun i j => raw19682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19682step0 raw19682; decide +kernel
      have hl : raw19682step0Labels = raw19682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19682 raw19682Labels permutation434 hz
    mixedMoment B raw19682step0 raw19682step0Labels = mixedMoment B raw19682step1 raw19682step1Labels := by
      have hz : ∀ j, raw19682step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19682step1 = (fun i j => raw19682step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19682step1 raw19682step0; decide +kernel
      have hl : raw19682step1Labels = raw19682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19682step0 raw19682step0Labels permutation56 hz
    mixedMoment B raw19682step1 raw19682step1Labels = mixedMoment B raw19682step2 raw19682step2Labels := by
      have ha : raw19682step2 = (fun i j => raw19682step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19682step2 raw19682step1; decide +kernel
      have hl : raw19682step2Labels = raw19682step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19682step1 raw19682step1Labels permutation29 permutation7
    mixedMoment B raw19682step2 raw19682step2Labels = mixedMoment B raw19682step3 raw19682step3Labels := by
      have ha : raw19682step3 = raw19682step2 := by apply Matrix.ext; unfold raw19682step3 raw19682step2; decide +kernel
      have hl : raw19682step2Labels = labelEmbedding1 ∘ raw19682step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19682step2 raw19682step2Labels raw19682step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

theorem canonical19683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19683 raw19683Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw19683 raw19683Labels = mixedMoment B raw19683step0 raw19683step0Labels := by
      have hz : ∀ j, raw19683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19683step0 = (fun i j => raw19683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19683step0 raw19683; decide +kernel
      have hl : raw19683step0Labels = raw19683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19683 raw19683Labels permutation346 hz
    mixedMoment B raw19683step0 raw19683step0Labels = mixedMoment B raw19683step1 raw19683step1Labels := by
      have hz : ∀ j, raw19683step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19683step1 = (fun i j => raw19683step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19683step1 raw19683step0; decide +kernel
      have hl : raw19683step1Labels = raw19683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19683step0 raw19683step0Labels permutation56 hz
    mixedMoment B raw19683step1 raw19683step1Labels = mixedMoment B raw19683step2 raw19683step2Labels := by
      have ha : raw19683step2 = (fun i j => raw19683step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19683step2 raw19683step1; decide +kernel
      have hl : raw19683step2Labels = raw19683step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19683step1 raw19683step1Labels permutation29 permutation7
    mixedMoment B raw19683step2 raw19683step2Labels = mixedMoment B raw19683step3 raw19683step3Labels := by
      have ha : raw19683step3 = raw19683step2 := by apply Matrix.ext; unfold raw19683step3 raw19683step2; decide +kernel
      have hl : raw19683step2Labels = labelEmbedding1 ∘ raw19683step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19683step2 raw19683step2Labels raw19683step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

theorem canonical19692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19692 raw19692Labels = mixedMoment B node643 node643Labels := by
  calc
    mixedMoment B raw19692 raw19692Labels = mixedMoment B raw19692step0 raw19692step0Labels := by
      have hz : ∀ j, raw19692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19692step0 = (fun i j => raw19692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19692step0 raw19692; decide +kernel
      have hl : raw19692step0Labels = raw19692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19692 raw19692Labels permutation434 hz
    mixedMoment B raw19692step0 raw19692step0Labels = mixedMoment B raw19692step1 raw19692step1Labels := by
      have hz : ∀ j, raw19692step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19692step1 = (fun i j => raw19692step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19692step1 raw19692step0; decide +kernel
      have hl : raw19692step1Labels = raw19692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19692step0 raw19692step0Labels permutation80 hz
    mixedMoment B raw19692step1 raw19692step1Labels = mixedMoment B raw19692step2 raw19692step2Labels := by
      have hz : ∀ j, raw19692step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19692step2 = (fun i j => raw19692step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19692step2 raw19692step1; decide +kernel
      have hl : raw19692step2Labels = raw19692step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19692step1 raw19692step1Labels permutation14 hz
    _ = mixedMoment B node643 node643Labels := by rfl

theorem canonical19699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19699 raw19699Labels = mixedMoment B node948 node948Labels := by
  calc
    mixedMoment B raw19699 raw19699Labels = mixedMoment B raw19699step0 raw19699step0Labels := by
      have hz : ∀ j, raw19699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19699step0 = (fun i j => raw19699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19699step0 raw19699; decide +kernel
      have hl : raw19699step0Labels = raw19699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19699 raw19699Labels permutation434 hz
    mixedMoment B raw19699step0 raw19699step0Labels = mixedMoment B raw19699step1 raw19699step1Labels := by
      have hz : ∀ j, raw19699step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19699step1 = (fun i j => raw19699step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19699step1 raw19699step0; decide +kernel
      have hl : raw19699step1Labels = raw19699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19699step0 raw19699step0Labels permutation80 hz
    mixedMoment B raw19699step1 raw19699step1Labels = mixedMoment B raw19699step2 raw19699step2Labels := by
      have ha : raw19699step2 = (fun i j => raw19699step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19699step2 raw19699step1; decide +kernel
      have hl : raw19699step2Labels = raw19699step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19699step1 raw19699step1Labels permutation31 permutation2
    mixedMoment B raw19699step2 raw19699step2Labels = mixedMoment B raw19699step3 raw19699step3Labels := by
      have ha : raw19699step3 = -raw19699step2 := by apply Matrix.ext; change ∀ i j, raw19699step3 i j = -(raw19699step2 i j); unfold raw19699step3 raw19699step2; decide +kernel
      have hl : raw19699step3Labels = raw19699step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node948 node948Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19835 raw19835Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw19835 raw19835Labels = mixedMoment B raw19835step0 raw19835step0Labels := by
      have hz : ∀ j, raw19835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19835step0 = (fun i j => raw19835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19835step0 raw19835; decide +kernel
      have hl : raw19835step0Labels = raw19835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19835 raw19835Labels permutation434 hz
    mixedMoment B raw19835step0 raw19835step0Labels = mixedMoment B raw19835step1 raw19835step1Labels := by
      have hz : ∀ j, raw19835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19835step1 = (fun i j => raw19835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19835step1 raw19835step0; decide +kernel
      have hl : raw19835step1Labels = raw19835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19835step0 raw19835step0Labels permutation80 hz
    mixedMoment B raw19835step1 raw19835step1Labels = mixedMoment B raw19835step2 raw19835step2Labels := by
      have hz : ∀ j, raw19835step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19835step2 = (fun i j => raw19835step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19835step2 raw19835step1; decide +kernel
      have hl : raw19835step2Labels = raw19835step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19835step1 raw19835step1Labels permutation14 hz
    mixedMoment B raw19835step2 raw19835step2Labels = mixedMoment B raw19835step3 raw19835step3Labels := by
      have ha : raw19835step3 = (fun i j => raw19835step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19835step3 raw19835step2; decide +kernel
      have hl : raw19835step3Labels = raw19835step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19835step2 raw19835step2Labels permutation7 permutation2
    mixedMoment B raw19835step3 raw19835step3Labels = mixedMoment B raw19835step4 raw19835step4Labels := by
      have ha : raw19835step4 = -raw19835step3 := by apply Matrix.ext; change ∀ i j, raw19835step4 i j = -(raw19835step3 i j); unfold raw19835step4 raw19835step3; decide +kernel
      have hl : raw19835step4Labels = raw19835step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1741 node1741Labels := by rfl

theorem canonical19836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19836 raw19836Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw19836 raw19836Labels = mixedMoment B raw19836step0 raw19836step0Labels := by
      have hz : ∀ j, raw19836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19836step0 = (fun i j => raw19836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19836step0 raw19836; decide +kernel
      have hl : raw19836step0Labels = raw19836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19836 raw19836Labels permutation434 hz
    mixedMoment B raw19836step0 raw19836step0Labels = mixedMoment B raw19836step1 raw19836step1Labels := by
      have hz : ∀ j, raw19836step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19836step1 = (fun i j => raw19836step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19836step1 raw19836step0; decide +kernel
      have hl : raw19836step1Labels = raw19836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19836step0 raw19836step0Labels permutation80 hz
    mixedMoment B raw19836step1 raw19836step1Labels = mixedMoment B raw19836step2 raw19836step2Labels := by
      have hz : ∀ j, raw19836step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19836step2 = (fun i j => raw19836step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19836step2 raw19836step1; decide +kernel
      have hl : raw19836step2Labels = raw19836step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19836step1 raw19836step1Labels permutation14 hz
    mixedMoment B raw19836step2 raw19836step2Labels = mixedMoment B raw19836step3 raw19836step3Labels := by
      have ha : raw19836step3 = (fun i j => raw19836step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19836step3 raw19836step2; decide +kernel
      have hl : raw19836step3Labels = raw19836step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19836step2 raw19836step2Labels permutation6 permutation0
    mixedMoment B raw19836step3 raw19836step3Labels = mixedMoment B raw19836step4 raw19836step4Labels := by
      have ha : raw19836step4 = -raw19836step3 := by apply Matrix.ext; change ∀ i j, raw19836step4 i j = -(raw19836step3 i j); unfold raw19836step4 raw19836step3; decide +kernel
      have hl : raw19836step4Labels = raw19836step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4071 node4071Labels := by rfl

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

theorem canonical19844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19844 raw19844Labels = mixedMoment B node1289 node1289Labels := by
  calc
    mixedMoment B raw19844 raw19844Labels = mixedMoment B raw19844step0 raw19844step0Labels := by
      have hz : ∀ j, raw19844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19844step0 = (fun i j => raw19844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19844step0 raw19844; decide +kernel
      have hl : raw19844step0Labels = raw19844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19844 raw19844Labels permutation434 hz
    mixedMoment B raw19844step0 raw19844step0Labels = mixedMoment B raw19844step1 raw19844step1Labels := by
      have hz : ∀ j, raw19844step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19844step1 = (fun i j => raw19844step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19844step1 raw19844step0; decide +kernel
      have hl : raw19844step1Labels = raw19844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19844step0 raw19844step0Labels permutation80 hz
    mixedMoment B raw19844step1 raw19844step1Labels = mixedMoment B raw19844step2 raw19844step2Labels := by
      have hz : ∀ j, raw19844step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19844step2 = (fun i j => raw19844step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19844step2 raw19844step1; decide +kernel
      have hl : raw19844step2Labels = raw19844step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19844step1 raw19844step1Labels permutation14 hz
    _ = mixedMoment B node1289 node1289Labels := by rfl

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

theorem canonical20099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20099 raw20099Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw20099 raw20099Labels = mixedMoment B raw20099step0 raw20099step0Labels := by
      have hz : ∀ j, raw20099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20099step0 = (fun i j => raw20099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20099step0 raw20099; decide +kernel
      have hl : raw20099step0Labels = raw20099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099 raw20099Labels permutation434 hz
    mixedMoment B raw20099step0 raw20099step0Labels = mixedMoment B raw20099step1 raw20099step1Labels := by
      have hz : ∀ j, raw20099step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20099step1 = (fun i j => raw20099step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20099step1 raw20099step0; decide +kernel
      have hl : raw20099step1Labels = raw20099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step0 raw20099step0Labels permutation80 hz
    mixedMoment B raw20099step1 raw20099step1Labels = mixedMoment B raw20099step2 raw20099step2Labels := by
      have hz : ∀ j, raw20099step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20099step2 = (fun i j => raw20099step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20099step2 raw20099step1; decide +kernel
      have hl : raw20099step2Labels = raw20099step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step1 raw20099step1Labels permutation14 hz
    mixedMoment B raw20099step2 raw20099step2Labels = mixedMoment B raw20099step3 raw20099step3Labels := by
      have ha : raw20099step3 = -raw20099step2 := by apply Matrix.ext; change ∀ i j, raw20099step3 i j = -(raw20099step2 i j); unfold raw20099step3 raw20099step2; decide +kernel
      have hl : raw20099step3Labels = raw20099step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

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

theorem canonical20480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20480 raw20480Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw20480 raw20480Labels = mixedMoment B raw20480step0 raw20480step0Labels := by
      have hz : ∀ j, raw20480 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20480step0 = (fun i j => raw20480 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20480step0 raw20480; decide +kernel
      have hl : raw20480step0Labels = raw20480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20480 raw20480Labels permutation434 hz
    mixedMoment B raw20480step0 raw20480step0Labels = mixedMoment B raw20480step1 raw20480step1Labels := by
      have hz : ∀ j, raw20480step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20480step1 = (fun i j => raw20480step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20480step1 raw20480step0; decide +kernel
      have hl : raw20480step1Labels = raw20480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20480step0 raw20480step0Labels permutation80 hz
    mixedMoment B raw20480step1 raw20480step1Labels = mixedMoment B raw20480step2 raw20480step2Labels := by
      have hz : ∀ j, raw20480step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20480step2 = (fun i j => raw20480step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20480step2 raw20480step1; decide +kernel
      have hl : raw20480step2Labels = raw20480step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20480step1 raw20480step1Labels permutation14 hz
    mixedMoment B raw20480step2 raw20480step2Labels = mixedMoment B raw20480step3 raw20480step3Labels := by
      have ha : raw20480step3 = (fun i j => raw20480step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20480step3 raw20480step2; decide +kernel
      have hl : raw20480step3Labels = raw20480step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20480step2 raw20480step2Labels permutation2 permutation4
    mixedMoment B raw20480step3 raw20480step3Labels = mixedMoment B raw20480step4 raw20480step4Labels := by
      have ha : raw20480step4 = -raw20480step3 := by apply Matrix.ext; change ∀ i j, raw20480step4 i j = -(raw20480step3 i j); unfold raw20480step4 raw20480step3; decide +kernel
      have hl : raw20480step4Labels = raw20480step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1730 node1730Labels := by rfl

theorem canonical20511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20511 raw20511Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw20511 raw20511Labels = mixedMoment B raw20511step0 raw20511step0Labels := by
      have hz : ∀ j, raw20511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20511step0 = (fun i j => raw20511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20511step0 raw20511; decide +kernel
      have hl : raw20511step0Labels = raw20511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20511 raw20511Labels permutation434 hz
    mixedMoment B raw20511step0 raw20511step0Labels = mixedMoment B raw20511step1 raw20511step1Labels := by
      have hz : ∀ j, raw20511step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20511step1 = (fun i j => raw20511step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20511step1 raw20511step0; decide +kernel
      have hl : raw20511step1Labels = raw20511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20511step0 raw20511step0Labels permutation80 hz
    mixedMoment B raw20511step1 raw20511step1Labels = mixedMoment B raw20511step2 raw20511step2Labels := by
      have ha : raw20511step2 = (fun i j => raw20511step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20511step2 raw20511step1; decide +kernel
      have hl : raw20511step2Labels = raw20511step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20511step1 raw20511step1Labels permutation12 permutation5
    mixedMoment B raw20511step2 raw20511step2Labels = mixedMoment B raw20511step3 raw20511step3Labels := by
      have ha : raw20511step3 = -raw20511step2 := by apply Matrix.ext; change ∀ i j, raw20511step3 i j = -(raw20511step2 i j); unfold raw20511step3 raw20511step2; decide +kernel
      have hl : raw20511step3Labels = raw20511step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20511step3 raw20511step3Labels = mixedMoment B raw20511step4 raw20511step4Labels := by
      have ha : raw20511step4 = raw20511step3 := by apply Matrix.ext; unfold raw20511step4 raw20511step3; decide +kernel
      have hl : raw20511step3Labels = labelEmbedding1 ∘ raw20511step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20511step3 raw20511step3Labels raw20511step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1530 node1530Labels := by rfl

theorem canonical20512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20512 raw20512Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20512 raw20512Labels = mixedMoment B raw20512step0 raw20512step0Labels := by
      have hz : ∀ j, raw20512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20512step0 = (fun i j => raw20512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20512step0 raw20512; decide +kernel
      have hl : raw20512step0Labels = raw20512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20512 raw20512Labels permutation434 hz
    mixedMoment B raw20512step0 raw20512step0Labels = mixedMoment B raw20512step1 raw20512step1Labels := by
      have ha : raw20512step1 = (fun i j => raw20512step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20512step1 raw20512step0; decide +kernel
      have hl : raw20512step1Labels = raw20512step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20512step0 raw20512step0Labels permutation137 permutation7
    mixedMoment B raw20512step1 raw20512step1Labels = mixedMoment B raw20512step2 raw20512step2Labels := by
      have ha : raw20512step2 = raw20512step1 := by apply Matrix.ext; unfold raw20512step2 raw20512step1; decide +kernel
      have hl : raw20512step1Labels = labelEmbedding1 ∘ raw20512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20512step1 raw20512step1Labels raw20512step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

theorem canonical20513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20513 raw20513Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20513 raw20513Labels = mixedMoment B raw20513step0 raw20513step0Labels := by
      have hz : ∀ j, raw20513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20513step0 = (fun i j => raw20513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20513step0 raw20513; decide +kernel
      have hl : raw20513step0Labels = raw20513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20513 raw20513Labels permutation346 hz
    mixedMoment B raw20513step0 raw20513step0Labels = mixedMoment B raw20513step1 raw20513step1Labels := by
      have ha : raw20513step1 = (fun i j => raw20513step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20513step1 raw20513step0; decide +kernel
      have hl : raw20513step1Labels = raw20513step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20513step0 raw20513step0Labels permutation137 permutation7
    mixedMoment B raw20513step1 raw20513step1Labels = mixedMoment B raw20513step2 raw20513step2Labels := by
      have ha : raw20513step2 = raw20513step1 := by apply Matrix.ext; unfold raw20513step2 raw20513step1; decide +kernel
      have hl : raw20513step1Labels = labelEmbedding1 ∘ raw20513step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20513step1 raw20513step1Labels raw20513step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

theorem canonical20514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20514 raw20514Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw20514 raw20514Labels = mixedMoment B raw20514step0 raw20514step0Labels := by
      have hz : ∀ j, raw20514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20514step0 = (fun i j => raw20514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20514step0 raw20514; decide +kernel
      have hl : raw20514step0Labels = raw20514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20514 raw20514Labels permutation434 hz
    mixedMoment B raw20514step0 raw20514step0Labels = mixedMoment B raw20514step1 raw20514step1Labels := by
      have hz : ∀ j, raw20514step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20514step1 = (fun i j => raw20514step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20514step1 raw20514step0; decide +kernel
      have hl : raw20514step1Labels = raw20514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20514step0 raw20514step0Labels permutation56 hz
    mixedMoment B raw20514step1 raw20514step1Labels = mixedMoment B raw20514step2 raw20514step2Labels := by
      have ha : raw20514step2 = (fun i j => raw20514step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20514step2 raw20514step1; decide +kernel
      have hl : raw20514step2Labels = raw20514step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20514step1 raw20514step1Labels permutation12 permutation5
    mixedMoment B raw20514step2 raw20514step2Labels = mixedMoment B raw20514step3 raw20514step3Labels := by
      have ha : raw20514step3 = -raw20514step2 := by apply Matrix.ext; change ∀ i j, raw20514step3 i j = -(raw20514step2 i j); unfold raw20514step3 raw20514step2; decide +kernel
      have hl : raw20514step3Labels = raw20514step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20514step3 raw20514step3Labels = mixedMoment B raw20514step4 raw20514step4Labels := by
      have ha : raw20514step4 = raw20514step3 := by apply Matrix.ext; unfold raw20514step4 raw20514step3; decide +kernel
      have hl : raw20514step3Labels = labelEmbedding1 ∘ raw20514step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20514step3 raw20514step3Labels raw20514step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1530 node1530Labels := by rfl

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

theorem canonical20516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20516 raw20516Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20516 raw20516Labels = mixedMoment B raw20516step0 raw20516step0Labels := by
      have hz : ∀ j, raw20516 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20516step0 = (fun i j => raw20516 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20516step0 raw20516; decide +kernel
      have hl : raw20516step0Labels = raw20516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20516 raw20516Labels permutation265 hz
    mixedMoment B raw20516step0 raw20516step0Labels = mixedMoment B raw20516step1 raw20516step1Labels := by
      have ha : raw20516step1 = (fun i j => raw20516step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20516step1 raw20516step0; decide +kernel
      have hl : raw20516step1Labels = raw20516step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20516step0 raw20516step0Labels permutation137 permutation7
    mixedMoment B raw20516step1 raw20516step1Labels = mixedMoment B raw20516step2 raw20516step2Labels := by
      have ha : raw20516step2 = raw20516step1 := by apply Matrix.ext; unfold raw20516step2 raw20516step1; decide +kernel
      have hl : raw20516step1Labels = labelEmbedding1 ∘ raw20516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20516step1 raw20516step1Labels raw20516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

theorem canonical20517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20517 raw20517Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw20517 raw20517Labels = mixedMoment B raw20517step0 raw20517step0Labels := by
      have hz : ∀ j, raw20517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20517step0 = (fun i j => raw20517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20517step0 raw20517; decide +kernel
      have hl : raw20517step0Labels = raw20517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20517 raw20517Labels permutation346 hz
    mixedMoment B raw20517step0 raw20517step0Labels = mixedMoment B raw20517step1 raw20517step1Labels := by
      have hz : ∀ j, raw20517step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20517step1 = (fun i j => raw20517step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20517step1 raw20517step0; decide +kernel
      have hl : raw20517step1Labels = raw20517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20517step0 raw20517step0Labels permutation56 hz
    mixedMoment B raw20517step1 raw20517step1Labels = mixedMoment B raw20517step2 raw20517step2Labels := by
      have ha : raw20517step2 = (fun i j => raw20517step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20517step2 raw20517step1; decide +kernel
      have hl : raw20517step2Labels = raw20517step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20517step1 raw20517step1Labels permutation12 permutation5
    mixedMoment B raw20517step2 raw20517step2Labels = mixedMoment B raw20517step3 raw20517step3Labels := by
      have ha : raw20517step3 = -raw20517step2 := by apply Matrix.ext; change ∀ i j, raw20517step3 i j = -(raw20517step2 i j); unfold raw20517step3 raw20517step2; decide +kernel
      have hl : raw20517step3Labels = raw20517step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20517step3 raw20517step3Labels = mixedMoment B raw20517step4 raw20517step4Labels := by
      have ha : raw20517step4 = raw20517step3 := by apply Matrix.ext; unfold raw20517step4 raw20517step3; decide +kernel
      have hl : raw20517step3Labels = labelEmbedding1 ∘ raw20517step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20517step3 raw20517step3Labels raw20517step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1530 node1530Labels := by rfl

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

theorem canonical20519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20519 raw20519Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20519 raw20519Labels = mixedMoment B raw20519step0 raw20519step0Labels := by
      have hz : ∀ j, raw20519 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20519step0 = (fun i j => raw20519 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20519step0 raw20519; decide +kernel
      have hl : raw20519step0Labels = raw20519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20519 raw20519Labels permutation265 hz
    mixedMoment B raw20519step0 raw20519step0Labels = mixedMoment B raw20519step1 raw20519step1Labels := by
      have ha : raw20519step1 = (fun i j => raw20519step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20519step1 raw20519step0; decide +kernel
      have hl : raw20519step1Labels = raw20519step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20519step0 raw20519step0Labels permutation143 permutation7
    mixedMoment B raw20519step1 raw20519step1Labels = mixedMoment B raw20519step2 raw20519step2Labels := by
      have ha : raw20519step2 = raw20519step1 := by apply Matrix.ext; unfold raw20519step2 raw20519step1; decide +kernel
      have hl : raw20519step1Labels = labelEmbedding1 ∘ raw20519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20519step1 raw20519step1Labels raw20519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

theorem canonical20520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20520 raw20520Labels = mixedMoment B node1531 node1531Labels := by
  calc
    mixedMoment B raw20520 raw20520Labels = mixedMoment B raw20520step0 raw20520step0Labels := by
      have hz : ∀ j, raw20520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20520step0 = (fun i j => raw20520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20520step0 raw20520; decide +kernel
      have hl : raw20520step0Labels = raw20520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20520 raw20520Labels permutation434 hz
    mixedMoment B raw20520step0 raw20520step0Labels = mixedMoment B raw20520step1 raw20520step1Labels := by
      have hz : ∀ j, raw20520step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20520step1 = (fun i j => raw20520step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20520step1 raw20520step0; decide +kernel
      have hl : raw20520step1Labels = raw20520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20520step0 raw20520step0Labels permutation80 hz
    mixedMoment B raw20520step1 raw20520step1Labels = mixedMoment B raw20520step2 raw20520step2Labels := by
      have hz : ∀ j, raw20520step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20520step2 = (fun i j => raw20520step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20520step2 raw20520step1; decide +kernel
      have hl : raw20520step2Labels = raw20520step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20520step1 raw20520step1Labels permutation14 hz
    mixedMoment B raw20520step2 raw20520step2Labels = mixedMoment B raw20520step3 raw20520step3Labels := by
      have ha : raw20520step3 = (fun i j => raw20520step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20520step3 raw20520step2; decide +kernel
      have hl : raw20520step3Labels = raw20520step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20520step2 raw20520step2Labels permutation3 permutation5
    mixedMoment B raw20520step3 raw20520step3Labels = mixedMoment B raw20520step4 raw20520step4Labels := by
      have ha : raw20520step4 = -raw20520step3 := by apply Matrix.ext; change ∀ i j, raw20520step4 i j = -(raw20520step3 i j); unfold raw20520step4 raw20520step3; decide +kernel
      have hl : raw20520step4Labels = raw20520step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20520step4 raw20520step4Labels = mixedMoment B raw20520step5 raw20520step5Labels := by
      have ha : raw20520step5 = raw20520step4 := by apply Matrix.ext; unfold raw20520step5 raw20520step4; decide +kernel
      have hl : raw20520step4Labels = labelEmbedding1 ∘ raw20520step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20520step4 raw20520step4Labels raw20520step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1531 node1531Labels := by rfl

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

theorem canonical20522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20522 raw20522Labels = mixedMoment B node2258 node2258Labels := by
  calc
    mixedMoment B raw20522 raw20522Labels = mixedMoment B raw20522step0 raw20522step0Labels := by
      have hz : ∀ j, raw20522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20522step0 = (fun i j => raw20522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20522step0 raw20522; decide +kernel
      have hl : raw20522step0Labels = raw20522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20522 raw20522Labels permutation434 hz
    mixedMoment B raw20522step0 raw20522step0Labels = mixedMoment B raw20522step1 raw20522step1Labels := by
      have hz : ∀ j, raw20522step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20522step1 = (fun i j => raw20522step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20522step1 raw20522step0; decide +kernel
      have hl : raw20522step1Labels = raw20522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20522step0 raw20522step0Labels permutation56 hz
    mixedMoment B raw20522step1 raw20522step1Labels = mixedMoment B raw20522step2 raw20522step2Labels := by
      have ha : raw20522step2 = (fun i j => raw20522step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20522step2 raw20522step1; decide +kernel
      have hl : raw20522step2Labels = raw20522step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20522step1 raw20522step1Labels permutation29 permutation7
    mixedMoment B raw20522step2 raw20522step2Labels = mixedMoment B raw20522step3 raw20522step3Labels := by
      have ha : raw20522step3 = raw20522step2 := by apply Matrix.ext; unfold raw20522step3 raw20522step2; decide +kernel
      have hl : raw20522step2Labels = labelEmbedding1 ∘ raw20522step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20522step2 raw20522step2Labels raw20522step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2258 node2258Labels := by rfl

theorem canonical20523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20523 raw20523Labels = mixedMoment B node2258 node2258Labels := by
  calc
    mixedMoment B raw20523 raw20523Labels = mixedMoment B raw20523step0 raw20523step0Labels := by
      have hz : ∀ j, raw20523 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20523step0 = (fun i j => raw20523 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20523step0 raw20523; decide +kernel
      have hl : raw20523step0Labels = raw20523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20523 raw20523Labels permutation346 hz
    mixedMoment B raw20523step0 raw20523step0Labels = mixedMoment B raw20523step1 raw20523step1Labels := by
      have hz : ∀ j, raw20523step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20523step1 = (fun i j => raw20523step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20523step1 raw20523step0; decide +kernel
      have hl : raw20523step1Labels = raw20523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20523step0 raw20523step0Labels permutation56 hz
    mixedMoment B raw20523step1 raw20523step1Labels = mixedMoment B raw20523step2 raw20523step2Labels := by
      have ha : raw20523step2 = (fun i j => raw20523step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20523step2 raw20523step1; decide +kernel
      have hl : raw20523step2Labels = raw20523step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20523step1 raw20523step1Labels permutation29 permutation7
    mixedMoment B raw20523step2 raw20523step2Labels = mixedMoment B raw20523step3 raw20523step3Labels := by
      have ha : raw20523step3 = raw20523step2 := by apply Matrix.ext; unfold raw20523step3 raw20523step2; decide +kernel
      have hl : raw20523step2Labels = labelEmbedding1 ∘ raw20523step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20523step2 raw20523step2Labels raw20523step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2258 node2258Labels := by rfl

theorem canonical20524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20524 raw20524Labels = mixedMoment B node639 node639Labels := by
  calc
    mixedMoment B raw20524 raw20524Labels = mixedMoment B raw20524step0 raw20524step0Labels := by
      have hz : ∀ j, raw20524 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20524step0 = (fun i j => raw20524 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20524step0 raw20524; decide +kernel
      have hl : raw20524step0Labels = raw20524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20524 raw20524Labels permutation434 hz
    mixedMoment B raw20524step0 raw20524step0Labels = mixedMoment B raw20524step1 raw20524step1Labels := by
      have hz : ∀ j, raw20524step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20524step1 = (fun i j => raw20524step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20524step1 raw20524step0; decide +kernel
      have hl : raw20524step1Labels = raw20524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20524step0 raw20524step0Labels permutation80 hz
    mixedMoment B raw20524step1 raw20524step1Labels = mixedMoment B raw20524step2 raw20524step2Labels := by
      have ha : raw20524step2 = (fun i j => raw20524step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20524step2 raw20524step1; decide +kernel
      have hl : raw20524step2Labels = raw20524step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20524step1 raw20524step1Labels permutation10 permutation2
    _ = mixedMoment B node639 node639Labels := by rfl

theorem canonical20525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20525 raw20525Labels = mixedMoment B node639 node639Labels := by
  calc
    mixedMoment B raw20525 raw20525Labels = mixedMoment B raw20525step0 raw20525step0Labels := by
      have hz : ∀ j, raw20525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20525step0 = (fun i j => raw20525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20525step0 raw20525; decide +kernel
      have hl : raw20525step0Labels = raw20525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20525 raw20525Labels permutation434 hz
    mixedMoment B raw20525step0 raw20525step0Labels = mixedMoment B raw20525step1 raw20525step1Labels := by
      have hz : ∀ j, raw20525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20525step1 = (fun i j => raw20525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20525step1 raw20525step0; decide +kernel
      have hl : raw20525step1Labels = raw20525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20525step0 raw20525step0Labels permutation56 hz
    mixedMoment B raw20525step1 raw20525step1Labels = mixedMoment B raw20525step2 raw20525step2Labels := by
      have ha : raw20525step2 = (fun i j => raw20525step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20525step2 raw20525step1; decide +kernel
      have hl : raw20525step2Labels = raw20525step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20525step1 raw20525step1Labels permutation10 permutation2
    _ = mixedMoment B node639 node639Labels := by rfl

theorem canonical20526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20526 raw20526Labels = mixedMoment B node639 node639Labels := by
  calc
    mixedMoment B raw20526 raw20526Labels = mixedMoment B raw20526step0 raw20526step0Labels := by
      have hz : ∀ j, raw20526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20526step0 = (fun i j => raw20526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20526step0 raw20526; decide +kernel
      have hl : raw20526step0Labels = raw20526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20526 raw20526Labels permutation346 hz
    mixedMoment B raw20526step0 raw20526step0Labels = mixedMoment B raw20526step1 raw20526step1Labels := by
      have hz : ∀ j, raw20526step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20526step1 = (fun i j => raw20526step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20526step1 raw20526step0; decide +kernel
      have hl : raw20526step1Labels = raw20526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20526step0 raw20526step0Labels permutation56 hz
    mixedMoment B raw20526step1 raw20526step1Labels = mixedMoment B raw20526step2 raw20526step2Labels := by
      have ha : raw20526step2 = (fun i j => raw20526step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20526step2 raw20526step1; decide +kernel
      have hl : raw20526step2Labels = raw20526step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20526step1 raw20526step1Labels permutation10 permutation2
    _ = mixedMoment B node639 node639Labels := by rfl

theorem canonical20527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20527 raw20527Labels = mixedMoment B node654 node654Labels := by
  calc
    mixedMoment B raw20527 raw20527Labels = mixedMoment B raw20527step0 raw20527step0Labels := by
      have hz : ∀ j, raw20527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20527step0 = (fun i j => raw20527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20527step0 raw20527; decide +kernel
      have hl : raw20527step0Labels = raw20527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20527 raw20527Labels permutation434 hz
    mixedMoment B raw20527step0 raw20527step0Labels = mixedMoment B raw20527step1 raw20527step1Labels := by
      have hz : ∀ j, raw20527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20527step1 = (fun i j => raw20527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20527step1 raw20527step0; decide +kernel
      have hl : raw20527step1Labels = raw20527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20527step0 raw20527step0Labels permutation80 hz
    mixedMoment B raw20527step1 raw20527step1Labels = mixedMoment B raw20527step2 raw20527step2Labels := by
      have hz : ∀ j, raw20527step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20527step2 = (fun i j => raw20527step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20527step2 raw20527step1; decide +kernel
      have hl : raw20527step2Labels = raw20527step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20527step1 raw20527step1Labels permutation14 hz
    _ = mixedMoment B node654 node654Labels := by rfl

theorem canonical20528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20528 raw20528Labels = mixedMoment B node1157 node1157Labels := by
  calc
    mixedMoment B raw20528 raw20528Labels = mixedMoment B raw20528step0 raw20528step0Labels := by
      have hz : ∀ j, raw20528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20528step0 = (fun i j => raw20528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20528step0 raw20528; decide +kernel
      have hl : raw20528step0Labels = raw20528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20528 raw20528Labels permutation434 hz
    mixedMoment B raw20528step0 raw20528step0Labels = mixedMoment B raw20528step1 raw20528step1Labels := by
      have ha : raw20528step1 = (fun i j => raw20528step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20528step1 raw20528step0; decide +kernel
      have hl : raw20528step1Labels = raw20528step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20528step0 raw20528step0Labels permutation40 permutation2
    _ = mixedMoment B node1157 node1157Labels := by rfl

theorem canonical20529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20529 raw20529Labels = mixedMoment B node1157 node1157Labels := by
  calc
    mixedMoment B raw20529 raw20529Labels = mixedMoment B raw20529step0 raw20529step0Labels := by
      have hz : ∀ j, raw20529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20529step0 = (fun i j => raw20529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20529step0 raw20529; decide +kernel
      have hl : raw20529step0Labels = raw20529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20529 raw20529Labels permutation346 hz
    mixedMoment B raw20529step0 raw20529step0Labels = mixedMoment B raw20529step1 raw20529step1Labels := by
      have ha : raw20529step1 = (fun i j => raw20529step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20529step1 raw20529step0; decide +kernel
      have hl : raw20529step1Labels = raw20529step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20529step0 raw20529step0Labels permutation40 permutation2
    _ = mixedMoment B node1157 node1157Labels := by rfl

theorem canonical20530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20530 raw20530Labels = mixedMoment B node1292 node1292Labels := by
  calc
    mixedMoment B raw20530 raw20530Labels = mixedMoment B raw20530step0 raw20530step0Labels := by
      have hz : ∀ j, raw20530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20530step0 = (fun i j => raw20530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20530step0 raw20530; decide +kernel
      have hl : raw20530step0Labels = raw20530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20530 raw20530Labels permutation434 hz
    mixedMoment B raw20530step0 raw20530step0Labels = mixedMoment B raw20530step1 raw20530step1Labels := by
      have hz : ∀ j, raw20530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20530step1 = (fun i j => raw20530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20530step1 raw20530step0; decide +kernel
      have hl : raw20530step1Labels = raw20530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20530step0 raw20530step0Labels permutation80 hz
    mixedMoment B raw20530step1 raw20530step1Labels = mixedMoment B raw20530step2 raw20530step2Labels := by
      have ha : raw20530step2 = (fun i j => raw20530step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20530step2 raw20530step1; decide +kernel
      have hl : raw20530step2Labels = raw20530step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20530step1 raw20530step1Labels permutation10 permutation2
    _ = mixedMoment B node1292 node1292Labels := by rfl

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

theorem canonical20532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20532 raw20532Labels = mixedMoment B node1157 node1157Labels := by
  calc
    mixedMoment B raw20532 raw20532Labels = mixedMoment B raw20532step0 raw20532step0Labels := by
      have hz : ∀ j, raw20532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20532step0 = (fun i j => raw20532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20532step0 raw20532; decide +kernel
      have hl : raw20532step0Labels = raw20532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20532 raw20532Labels permutation346 hz
    mixedMoment B raw20532step0 raw20532step0Labels = mixedMoment B raw20532step1 raw20532step1Labels := by
      have ha : raw20532step1 = (fun i j => raw20532step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20532step1 raw20532step0; decide +kernel
      have hl : raw20532step1Labels = raw20532step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20532step0 raw20532step0Labels permutation34 permutation2
    _ = mixedMoment B node1157 node1157Labels := by rfl

theorem canonical20533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20533 raw20533Labels = mixedMoment B node1174 node1174Labels := by
  calc
    mixedMoment B raw20533 raw20533Labels = mixedMoment B raw20533step0 raw20533step0Labels := by
      have hz : ∀ j, raw20533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20533step0 = (fun i j => raw20533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20533step0 raw20533; decide +kernel
      have hl : raw20533step0Labels = raw20533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20533 raw20533Labels permutation434 hz
    mixedMoment B raw20533step0 raw20533step0Labels = mixedMoment B raw20533step1 raw20533step1Labels := by
      have hz : ∀ j, raw20533step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20533step1 = (fun i j => raw20533step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20533step1 raw20533step0; decide +kernel
      have hl : raw20533step1Labels = raw20533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20533step0 raw20533step0Labels permutation80 hz
    _ = mixedMoment B node1174 node1174Labels := by rfl

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

theorem canonical20642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20642 raw20642Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw20642 raw20642Labels = mixedMoment B raw20642step0 raw20642step0Labels := by
      have hz : ∀ j, raw20642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20642step0 = (fun i j => raw20642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20642step0 raw20642; decide +kernel
      have hl : raw20642step0Labels = raw20642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20642 raw20642Labels permutation434 hz
    mixedMoment B raw20642step0 raw20642step0Labels = mixedMoment B raw20642step1 raw20642step1Labels := by
      have hz : ∀ j, raw20642step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20642step1 = (fun i j => raw20642step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20642step1 raw20642step0; decide +kernel
      have hl : raw20642step1Labels = raw20642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20642step0 raw20642step0Labels permutation80 hz
    mixedMoment B raw20642step1 raw20642step1Labels = mixedMoment B raw20642step2 raw20642step2Labels := by
      have hz : ∀ j, raw20642step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20642step2 = (fun i j => raw20642step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20642step2 raw20642step1; decide +kernel
      have hl : raw20642step2Labels = raw20642step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20642step1 raw20642step1Labels permutation14 hz
    mixedMoment B raw20642step2 raw20642step2Labels = mixedMoment B raw20642step3 raw20642step3Labels := by
      have ha : raw20642step3 = (fun i j => raw20642step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20642step3 raw20642step2; decide +kernel
      have hl : raw20642step3Labels = raw20642step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20642step2 raw20642step2Labels permutation7 permutation4
    _ = mixedMoment B node2289 node2289Labels := by rfl

theorem canonical20643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20643 raw20643Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw20643 raw20643Labels = mixedMoment B raw20643step0 raw20643step0Labels := by
      have hz : ∀ j, raw20643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20643step0 = (fun i j => raw20643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20643step0 raw20643; decide +kernel
      have hl : raw20643step0Labels = raw20643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20643 raw20643Labels permutation434 hz
    mixedMoment B raw20643step0 raw20643step0Labels = mixedMoment B raw20643step1 raw20643step1Labels := by
      have hz : ∀ j, raw20643step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20643step1 = (fun i j => raw20643step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20643step1 raw20643step0; decide +kernel
      have hl : raw20643step1Labels = raw20643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20643step0 raw20643step0Labels permutation80 hz
    mixedMoment B raw20643step1 raw20643step1Labels = mixedMoment B raw20643step2 raw20643step2Labels := by
      have ha : raw20643step2 = (fun i j => raw20643step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20643step2 raw20643step1; decide +kernel
      have hl : raw20643step2Labels = raw20643step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20643step1 raw20643step1Labels permutation10 permutation4
    mixedMoment B raw20643step2 raw20643step2Labels = mixedMoment B raw20643step3 raw20643step3Labels := by
      have ha : raw20643step3 = -raw20643step2 := by apply Matrix.ext; change ∀ i j, raw20643step3 i j = -(raw20643step2 i j); unfold raw20643step3 raw20643step2; decide +kernel
      have hl : raw20643step3Labels = raw20643step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1647 node1647Labels := by rfl

theorem canonical20644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20644 raw20644Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw20644 raw20644Labels = mixedMoment B raw20644step0 raw20644step0Labels := by
      have hz : ∀ j, raw20644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20644step0 = (fun i j => raw20644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20644step0 raw20644; decide +kernel
      have hl : raw20644step0Labels = raw20644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20644 raw20644Labels permutation434 hz
    mixedMoment B raw20644step0 raw20644step0Labels = mixedMoment B raw20644step1 raw20644step1Labels := by
      have hz : ∀ j, raw20644step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20644step1 = (fun i j => raw20644step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20644step1 raw20644step0; decide +kernel
      have hl : raw20644step1Labels = raw20644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20644step0 raw20644step0Labels permutation56 hz
    mixedMoment B raw20644step1 raw20644step1Labels = mixedMoment B raw20644step2 raw20644step2Labels := by
      have ha : raw20644step2 = (fun i j => raw20644step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20644step2 raw20644step1; decide +kernel
      have hl : raw20644step2Labels = raw20644step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20644step1 raw20644step1Labels permutation10 permutation4
    mixedMoment B raw20644step2 raw20644step2Labels = mixedMoment B raw20644step3 raw20644step3Labels := by
      have ha : raw20644step3 = -raw20644step2 := by apply Matrix.ext; change ∀ i j, raw20644step3 i j = -(raw20644step2 i j); unfold raw20644step3 raw20644step2; decide +kernel
      have hl : raw20644step3Labels = raw20644step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1647 node1647Labels := by rfl

theorem canonical20645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20645 raw20645Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw20645 raw20645Labels = mixedMoment B raw20645step0 raw20645step0Labels := by
      have hz : ∀ j, raw20645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20645step0 = (fun i j => raw20645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20645step0 raw20645; decide +kernel
      have hl : raw20645step0Labels = raw20645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20645 raw20645Labels permutation346 hz
    mixedMoment B raw20645step0 raw20645step0Labels = mixedMoment B raw20645step1 raw20645step1Labels := by
      have hz : ∀ j, raw20645step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20645step1 = (fun i j => raw20645step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20645step1 raw20645step0; decide +kernel
      have hl : raw20645step1Labels = raw20645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20645step0 raw20645step0Labels permutation56 hz
    mixedMoment B raw20645step1 raw20645step1Labels = mixedMoment B raw20645step2 raw20645step2Labels := by
      have ha : raw20645step2 = (fun i j => raw20645step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20645step2 raw20645step1; decide +kernel
      have hl : raw20645step2Labels = raw20645step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20645step1 raw20645step1Labels permutation10 permutation4
    mixedMoment B raw20645step2 raw20645step2Labels = mixedMoment B raw20645step3 raw20645step3Labels := by
      have ha : raw20645step3 = -raw20645step2 := by apply Matrix.ext; change ∀ i j, raw20645step3 i j = -(raw20645step2 i j); unfold raw20645step3 raw20645step2; decide +kernel
      have hl : raw20645step3Labels = raw20645step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1647 node1647Labels := by rfl

theorem canonical20646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20646 raw20646Labels = mixedMoment B node1077 node1077Labels := by
  calc
    mixedMoment B raw20646 raw20646Labels = mixedMoment B raw20646step0 raw20646step0Labels := by
      have hz : ∀ j, raw20646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20646step0 = (fun i j => raw20646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20646step0 raw20646; decide +kernel
      have hl : raw20646step0Labels = raw20646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20646 raw20646Labels permutation434 hz
    mixedMoment B raw20646step0 raw20646step0Labels = mixedMoment B raw20646step1 raw20646step1Labels := by
      have hz : ∀ j, raw20646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20646step1 = (fun i j => raw20646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20646step1 raw20646step0; decide +kernel
      have hl : raw20646step1Labels = raw20646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20646step0 raw20646step0Labels permutation80 hz
    mixedMoment B raw20646step1 raw20646step1Labels = mixedMoment B raw20646step2 raw20646step2Labels := by
      have hz : ∀ j, raw20646step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20646step2 = (fun i j => raw20646step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20646step2 raw20646step1; decide +kernel
      have hl : raw20646step2Labels = raw20646step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20646step1 raw20646step1Labels permutation14 hz
    mixedMoment B raw20646step2 raw20646step2Labels = mixedMoment B raw20646step3 raw20646step3Labels := by
      have ha : raw20646step3 = (fun i j => raw20646step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20646step3 raw20646step2; decide +kernel
      have hl : raw20646step3Labels = raw20646step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20646step2 raw20646step2Labels permutation7 permutation4
    _ = mixedMoment B node1077 node1077Labels := by rfl

theorem canonical20647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20647 raw20647Labels = mixedMoment B node1657 node1657Labels := by
  calc
    mixedMoment B raw20647 raw20647Labels = mixedMoment B raw20647step0 raw20647step0Labels := by
      have hz : ∀ j, raw20647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20647step0 = (fun i j => raw20647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20647step0 raw20647; decide +kernel
      have hl : raw20647step0Labels = raw20647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20647 raw20647Labels permutation434 hz
    mixedMoment B raw20647step0 raw20647step0Labels = mixedMoment B raw20647step1 raw20647step1Labels := by
      have hz : ∀ j, raw20647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20647step1 = (fun i j => raw20647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20647step1 raw20647step0; decide +kernel
      have hl : raw20647step1Labels = raw20647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20647step0 raw20647step0Labels permutation80 hz
    mixedMoment B raw20647step1 raw20647step1Labels = mixedMoment B raw20647step2 raw20647step2Labels := by
      have ha : raw20647step2 = (fun i j => raw20647step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20647step2 raw20647step1; decide +kernel
      have hl : raw20647step2Labels = raw20647step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20647step1 raw20647step1Labels permutation31 permutation2
    mixedMoment B raw20647step2 raw20647step2Labels = mixedMoment B raw20647step3 raw20647step3Labels := by
      have ha : raw20647step3 = -raw20647step2 := by apply Matrix.ext; change ∀ i j, raw20647step3 i j = -(raw20647step2 i j); unfold raw20647step3 raw20647step2; decide +kernel
      have hl : raw20647step3Labels = raw20647step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1657 node1657Labels := by rfl

theorem canonical20648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20648 raw20648Labels = mixedMoment B node1657 node1657Labels := by
  calc
    mixedMoment B raw20648 raw20648Labels = mixedMoment B raw20648step0 raw20648step0Labels := by
      have hz : ∀ j, raw20648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20648step0 = (fun i j => raw20648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20648step0 raw20648; decide +kernel
      have hl : raw20648step0Labels = raw20648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20648 raw20648Labels permutation434 hz
    mixedMoment B raw20648step0 raw20648step0Labels = mixedMoment B raw20648step1 raw20648step1Labels := by
      have hz : ∀ j, raw20648step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20648step1 = (fun i j => raw20648step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20648step1 raw20648step0; decide +kernel
      have hl : raw20648step1Labels = raw20648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20648step0 raw20648step0Labels permutation56 hz
    mixedMoment B raw20648step1 raw20648step1Labels = mixedMoment B raw20648step2 raw20648step2Labels := by
      have ha : raw20648step2 = (fun i j => raw20648step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20648step2 raw20648step1; decide +kernel
      have hl : raw20648step2Labels = raw20648step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20648step1 raw20648step1Labels permutation31 permutation2
    mixedMoment B raw20648step2 raw20648step2Labels = mixedMoment B raw20648step3 raw20648step3Labels := by
      have ha : raw20648step3 = -raw20648step2 := by apply Matrix.ext; change ∀ i j, raw20648step3 i j = -(raw20648step2 i j); unfold raw20648step3 raw20648step2; decide +kernel
      have hl : raw20648step3Labels = raw20648step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1657 node1657Labels := by rfl

theorem canonical20649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20649 raw20649Labels = mixedMoment B node1657 node1657Labels := by
  calc
    mixedMoment B raw20649 raw20649Labels = mixedMoment B raw20649step0 raw20649step0Labels := by
      have hz : ∀ j, raw20649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20649step0 = (fun i j => raw20649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20649step0 raw20649; decide +kernel
      have hl : raw20649step0Labels = raw20649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20649 raw20649Labels permutation346 hz
    mixedMoment B raw20649step0 raw20649step0Labels = mixedMoment B raw20649step1 raw20649step1Labels := by
      have hz : ∀ j, raw20649step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20649step1 = (fun i j => raw20649step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20649step1 raw20649step0; decide +kernel
      have hl : raw20649step1Labels = raw20649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20649step0 raw20649step0Labels permutation56 hz
    mixedMoment B raw20649step1 raw20649step1Labels = mixedMoment B raw20649step2 raw20649step2Labels := by
      have ha : raw20649step2 = (fun i j => raw20649step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20649step2 raw20649step1; decide +kernel
      have hl : raw20649step2Labels = raw20649step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20649step1 raw20649step1Labels permutation31 permutation2
    mixedMoment B raw20649step2 raw20649step2Labels = mixedMoment B raw20649step3 raw20649step3Labels := by
      have ha : raw20649step3 = -raw20649step2 := by apply Matrix.ext; change ∀ i j, raw20649step3 i j = -(raw20649step2 i j); unfold raw20649step3 raw20649step2; decide +kernel
      have hl : raw20649step3Labels = raw20649step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1657 node1657Labels := by rfl

theorem canonical20650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20650 raw20650Labels = mixedMoment B node2780 node2780Labels := by
  calc
    mixedMoment B raw20650 raw20650Labels = mixedMoment B raw20650step0 raw20650step0Labels := by
      have hz : ∀ j, raw20650 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20650step0 = (fun i j => raw20650 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20650step0 raw20650; decide +kernel
      have hl : raw20650step0Labels = raw20650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20650 raw20650Labels permutation434 hz
    mixedMoment B raw20650step0 raw20650step0Labels = mixedMoment B raw20650step1 raw20650step1Labels := by
      have hz : ∀ j, raw20650step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20650step1 = (fun i j => raw20650step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20650step1 raw20650step0; decide +kernel
      have hl : raw20650step1Labels = raw20650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20650step0 raw20650step0Labels permutation80 hz
    mixedMoment B raw20650step1 raw20650step1Labels = mixedMoment B raw20650step2 raw20650step2Labels := by
      have hz : ∀ j, raw20650step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20650step2 = (fun i j => raw20650step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20650step2 raw20650step1; decide +kernel
      have hl : raw20650step2Labels = raw20650step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20650step1 raw20650step1Labels permutation14 hz
    _ = mixedMoment B node2780 node2780Labels := by rfl

theorem canonical20702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20702 raw20702Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw20702 raw20702Labels = mixedMoment B raw20702step0 raw20702step0Labels := by
      have hz : ∀ j, raw20702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20702step0 = (fun i j => raw20702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20702step0 raw20702; decide +kernel
      have hl : raw20702step0Labels = raw20702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20702 raw20702Labels permutation346 hz
    mixedMoment B raw20702step0 raw20702step0Labels = mixedMoment B raw20702step1 raw20702step1Labels := by
      have ha : raw20702step1 = (fun i j => raw20702step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20702step1 raw20702step0; decide +kernel
      have hl : raw20702step1Labels = raw20702step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20702step0 raw20702step0Labels permutation149 permutation7
    mixedMoment B raw20702step1 raw20702step1Labels = mixedMoment B raw20702step2 raw20702step2Labels := by
      have ha : raw20702step2 = raw20702step1 := by apply Matrix.ext; unfold raw20702step2 raw20702step1; decide +kernel
      have hl : raw20702step1Labels = labelEmbedding1 ∘ raw20702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20702step1 raw20702step1Labels raw20702step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

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

theorem canonical20707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20707 raw20707Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw20707 raw20707Labels = mixedMoment B raw20707step0 raw20707step0Labels := by
      have hz : ∀ j, raw20707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20707step0 = (fun i j => raw20707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20707step0 raw20707; decide +kernel
      have hl : raw20707step0Labels = raw20707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20707 raw20707Labels permutation346 hz
    mixedMoment B raw20707step0 raw20707step0Labels = mixedMoment B raw20707step1 raw20707step1Labels := by
      have ha : raw20707step1 = (fun i j => raw20707step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20707step1 raw20707step0; decide +kernel
      have hl : raw20707step1Labels = raw20707step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20707step0 raw20707step0Labels permutation46 permutation5
    mixedMoment B raw20707step1 raw20707step1Labels = mixedMoment B raw20707step2 raw20707step2Labels := by
      have ha : raw20707step2 = -raw20707step1 := by apply Matrix.ext; change ∀ i j, raw20707step2 i j = -(raw20707step1 i j); unfold raw20707step2 raw20707step1; decide +kernel
      have hl : raw20707step2Labels = raw20707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20707step2 raw20707step2Labels = mixedMoment B raw20707step3 raw20707step3Labels := by
      have ha : raw20707step3 = raw20707step2 := by apply Matrix.ext; unfold raw20707step3 raw20707step2; decide +kernel
      have hl : raw20707step2Labels = labelEmbedding1 ∘ raw20707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20707step2 raw20707step2Labels raw20707step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

theorem canonical20708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20708 raw20708Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw20708 raw20708Labels = mixedMoment B raw20708step0 raw20708step0Labels := by
      have ha : raw20708step0 = (fun i j => raw20708 (permutation190 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20708step0 raw20708; decide +kernel
      have hl : raw20708step0Labels = raw20708Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20708 raw20708Labels permutation190 permutation5
    mixedMoment B raw20708step0 raw20708step0Labels = mixedMoment B raw20708step1 raw20708step1Labels := by
      have ha : raw20708step1 = -raw20708step0 := by apply Matrix.ext; change ∀ i j, raw20708step1 i j = -(raw20708step0 i j); unfold raw20708step1 raw20708step0; decide +kernel
      have hl : raw20708step1Labels = raw20708step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20708step1 raw20708step1Labels = mixedMoment B raw20708step2 raw20708step2Labels := by
      have ha : raw20708step2 = raw20708step1 := by apply Matrix.ext; unfold raw20708step2 raw20708step1; decide +kernel
      have hl : raw20708step1Labels = labelEmbedding1 ∘ raw20708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20708step1 raw20708step1Labels raw20708step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

theorem canonical20709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20709 raw20709Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw20709 raw20709Labels = mixedMoment B raw20709step0 raw20709step0Labels := by
      have hz : ∀ j, raw20709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20709step0 = (fun i j => raw20709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20709step0 raw20709; decide +kernel
      have hl : raw20709step0Labels = raw20709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20709 raw20709Labels permutation346 hz
    mixedMoment B raw20709step0 raw20709step0Labels = mixedMoment B raw20709step1 raw20709step1Labels := by
      have ha : raw20709step1 = (fun i j => raw20709step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20709step1 raw20709step0; decide +kernel
      have hl : raw20709step1Labels = raw20709step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20709step0 raw20709step0Labels permutation38 permutation7
    mixedMoment B raw20709step1 raw20709step1Labels = mixedMoment B raw20709step2 raw20709step2Labels := by
      have ha : raw20709step2 = -raw20709step1 := by apply Matrix.ext; change ∀ i j, raw20709step2 i j = -(raw20709step1 i j); unfold raw20709step2 raw20709step1; decide +kernel
      have hl : raw20709step2Labels = raw20709step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20709step2 raw20709step2Labels = mixedMoment B raw20709step3 raw20709step3Labels := by
      have ha : raw20709step3 = raw20709step2 := by apply Matrix.ext; unfold raw20709step3 raw20709step2; decide +kernel
      have hl : raw20709step2Labels = labelEmbedding1 ∘ raw20709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20709step2 raw20709step2Labels raw20709step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

theorem canonical20710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20710 raw20710Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw20710 raw20710Labels = mixedMoment B raw20710step0 raw20710step0Labels := by
      have hz : ∀ j, raw20710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20710step0 = (fun i j => raw20710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20710step0 raw20710; decide +kernel
      have hl : raw20710step0Labels = raw20710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20710 raw20710Labels permutation346 hz
    mixedMoment B raw20710step0 raw20710step0Labels = mixedMoment B raw20710step1 raw20710step1Labels := by
      have ha : raw20710step1 = (fun i j => raw20710step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20710step1 raw20710step0; decide +kernel
      have hl : raw20710step1Labels = raw20710step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20710step0 raw20710step0Labels permutation38 permutation7
    mixedMoment B raw20710step1 raw20710step1Labels = mixedMoment B raw20710step2 raw20710step2Labels := by
      have ha : raw20710step2 = -raw20710step1 := by apply Matrix.ext; change ∀ i j, raw20710step2 i j = -(raw20710step1 i j); unfold raw20710step2 raw20710step1; decide +kernel
      have hl : raw20710step2Labels = raw20710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20710step2 raw20710step2Labels = mixedMoment B raw20710step3 raw20710step3Labels := by
      have ha : raw20710step3 = raw20710step2 := by apply Matrix.ext; unfold raw20710step3 raw20710step2; decide +kernel
      have hl : raw20710step2Labels = labelEmbedding1 ∘ raw20710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20710step2 raw20710step2Labels raw20710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical20711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20711 raw20711Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw20711 raw20711Labels = mixedMoment B raw20711step0 raw20711step0Labels := by
      have hz : ∀ j, raw20711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20711step0 = (fun i j => raw20711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20711step0 raw20711; decide +kernel
      have hl : raw20711step0Labels = raw20711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20711 raw20711Labels permutation346 hz
    mixedMoment B raw20711step0 raw20711step0Labels = mixedMoment B raw20711step1 raw20711step1Labels := by
      have ha : raw20711step1 = (fun i j => raw20711step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20711step1 raw20711step0; decide +kernel
      have hl : raw20711step1Labels = raw20711step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20711step0 raw20711step0Labels permutation38 permutation7
    mixedMoment B raw20711step1 raw20711step1Labels = mixedMoment B raw20711step2 raw20711step2Labels := by
      have ha : raw20711step2 = -raw20711step1 := by apply Matrix.ext; change ∀ i j, raw20711step2 i j = -(raw20711step1 i j); unfold raw20711step2 raw20711step1; decide +kernel
      have hl : raw20711step2Labels = raw20711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20711step2 raw20711step2Labels = mixedMoment B raw20711step3 raw20711step3Labels := by
      have ha : raw20711step3 = raw20711step2 := by apply Matrix.ext; unfold raw20711step3 raw20711step2; decide +kernel
      have hl : raw20711step2Labels = labelEmbedding1 ∘ raw20711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20711step2 raw20711step2Labels raw20711step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical20712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20712 raw20712Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw20712 raw20712Labels = mixedMoment B raw20712step0 raw20712step0Labels := by
      have hz : ∀ j, raw20712 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20712step0 = (fun i j => raw20712 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20712step0 raw20712; decide +kernel
      have hl : raw20712step0Labels = raw20712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20712 raw20712Labels permutation265 hz
    mixedMoment B raw20712step0 raw20712step0Labels = mixedMoment B raw20712step1 raw20712step1Labels := by
      have ha : raw20712step1 = (fun i j => raw20712step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20712step1 raw20712step0; decide +kernel
      have hl : raw20712step1Labels = raw20712step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20712step0 raw20712step0Labels permutation46 permutation5
    mixedMoment B raw20712step1 raw20712step1Labels = mixedMoment B raw20712step2 raw20712step2Labels := by
      have ha : raw20712step2 = -raw20712step1 := by apply Matrix.ext; change ∀ i j, raw20712step2 i j = -(raw20712step1 i j); unfold raw20712step2 raw20712step1; decide +kernel
      have hl : raw20712step2Labels = raw20712step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20712step2 raw20712step2Labels = mixedMoment B raw20712step3 raw20712step3Labels := by
      have ha : raw20712step3 = raw20712step2 := by apply Matrix.ext; unfold raw20712step3 raw20712step2; decide +kernel
      have hl : raw20712step2Labels = labelEmbedding1 ∘ raw20712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20712step2 raw20712step2Labels raw20712step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

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

theorem canonical20714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20714 raw20714Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw20714 raw20714Labels = mixedMoment B raw20714step0 raw20714step0Labels := by
      have hz : ∀ j, raw20714 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20714step0 = (fun i j => raw20714 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20714step0 raw20714; decide +kernel
      have hl : raw20714step0Labels = raw20714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20714 raw20714Labels permutation265 hz
    mixedMoment B raw20714step0 raw20714step0Labels = mixedMoment B raw20714step1 raw20714step1Labels := by
      have ha : raw20714step1 = (fun i j => raw20714step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20714step1 raw20714step0; decide +kernel
      have hl : raw20714step1Labels = raw20714step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20714step0 raw20714step0Labels permutation38 permutation7
    mixedMoment B raw20714step1 raw20714step1Labels = mixedMoment B raw20714step2 raw20714step2Labels := by
      have ha : raw20714step2 = -raw20714step1 := by apply Matrix.ext; change ∀ i j, raw20714step2 i j = -(raw20714step1 i j); unfold raw20714step2 raw20714step1; decide +kernel
      have hl : raw20714step2Labels = raw20714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20714step2 raw20714step2Labels = mixedMoment B raw20714step3 raw20714step3Labels := by
      have ha : raw20714step3 = raw20714step2 := by apply Matrix.ext; unfold raw20714step3 raw20714step2; decide +kernel
      have hl : raw20714step2Labels = labelEmbedding1 ∘ raw20714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20714step2 raw20714step2Labels raw20714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

theorem canonical20715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20715 raw20715Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw20715 raw20715Labels = mixedMoment B raw20715step0 raw20715step0Labels := by
      have hz : ∀ j, raw20715 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20715step0 = (fun i j => raw20715 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20715step0 raw20715; decide +kernel
      have hl : raw20715step0Labels = raw20715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20715 raw20715Labels permutation265 hz
    mixedMoment B raw20715step0 raw20715step0Labels = mixedMoment B raw20715step1 raw20715step1Labels := by
      have ha : raw20715step1 = (fun i j => raw20715step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20715step1 raw20715step0; decide +kernel
      have hl : raw20715step1Labels = raw20715step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20715step0 raw20715step0Labels permutation38 permutation7
    mixedMoment B raw20715step1 raw20715step1Labels = mixedMoment B raw20715step2 raw20715step2Labels := by
      have ha : raw20715step2 = -raw20715step1 := by apply Matrix.ext; change ∀ i j, raw20715step2 i j = -(raw20715step1 i j); unfold raw20715step2 raw20715step1; decide +kernel
      have hl : raw20715step2Labels = raw20715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20715step2 raw20715step2Labels = mixedMoment B raw20715step3 raw20715step3Labels := by
      have ha : raw20715step3 = raw20715step2 := by apply Matrix.ext; unfold raw20715step3 raw20715step2; decide +kernel
      have hl : raw20715step2Labels = labelEmbedding1 ∘ raw20715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20715step2 raw20715step2Labels raw20715step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical20716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20716 raw20716Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw20716 raw20716Labels = mixedMoment B raw20716step0 raw20716step0Labels := by
      have hz : ∀ j, raw20716 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20716step0 = (fun i j => raw20716 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20716step0 raw20716; decide +kernel
      have hl : raw20716step0Labels = raw20716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20716 raw20716Labels permutation265 hz
    mixedMoment B raw20716step0 raw20716step0Labels = mixedMoment B raw20716step1 raw20716step1Labels := by
      have ha : raw20716step1 = (fun i j => raw20716step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20716step1 raw20716step0; decide +kernel
      have hl : raw20716step1Labels = raw20716step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20716step0 raw20716step0Labels permutation38 permutation7
    mixedMoment B raw20716step1 raw20716step1Labels = mixedMoment B raw20716step2 raw20716step2Labels := by
      have ha : raw20716step2 = -raw20716step1 := by apply Matrix.ext; change ∀ i j, raw20716step2 i j = -(raw20716step1 i j); unfold raw20716step2 raw20716step1; decide +kernel
      have hl : raw20716step2Labels = raw20716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20716step2 raw20716step2Labels = mixedMoment B raw20716step3 raw20716step3Labels := by
      have ha : raw20716step3 = raw20716step2 := by apply Matrix.ext; unfold raw20716step3 raw20716step2; decide +kernel
      have hl : raw20716step2Labels = labelEmbedding1 ∘ raw20716step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20716step2 raw20716step2Labels raw20716step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical20717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20717 raw20717Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw20717 raw20717Labels = mixedMoment B raw20717step0 raw20717step0Labels := by
      have hz : ∀ j, raw20717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20717step0 = (fun i j => raw20717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20717step0 raw20717; decide +kernel
      have hl : raw20717step0Labels = raw20717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20717 raw20717Labels permutation346 hz
    mixedMoment B raw20717step0 raw20717step0Labels = mixedMoment B raw20717step1 raw20717step1Labels := by
      have hz : ∀ j, raw20717step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20717step1 = (fun i j => raw20717step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20717step1 raw20717step0; decide +kernel
      have hl : raw20717step1Labels = raw20717step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20717step0 raw20717step0Labels permutation56 hz
    mixedMoment B raw20717step1 raw20717step1Labels = mixedMoment B raw20717step2 raw20717step2Labels := by
      have ha : raw20717step2 = (fun i j => raw20717step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20717step2 raw20717step1; decide +kernel
      have hl : raw20717step2Labels = raw20717step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20717step1 raw20717step1Labels permutation11 permutation5
    mixedMoment B raw20717step2 raw20717step2Labels = mixedMoment B raw20717step3 raw20717step3Labels := by
      have ha : raw20717step3 = -raw20717step2 := by apply Matrix.ext; change ∀ i j, raw20717step3 i j = -(raw20717step2 i j); unfold raw20717step3 raw20717step2; decide +kernel
      have hl : raw20717step3Labels = raw20717step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20717step3 raw20717step3Labels = mixedMoment B raw20717step4 raw20717step4Labels := by
      have ha : raw20717step4 = raw20717step3 := by apply Matrix.ext; unfold raw20717step4 raw20717step3; decide +kernel
      have hl : raw20717step3Labels = labelEmbedding1 ∘ raw20717step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20717step3 raw20717step3Labels raw20717step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

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

theorem canonical20719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20719 raw20719Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw20719 raw20719Labels = mixedMoment B raw20719step0 raw20719step0Labels := by
      have hz : ∀ j, raw20719 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20719step0 = (fun i j => raw20719 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20719step0 raw20719; decide +kernel
      have hl : raw20719step0Labels = raw20719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20719 raw20719Labels permutation265 hz
    mixedMoment B raw20719step0 raw20719step0Labels = mixedMoment B raw20719step1 raw20719step1Labels := by
      have ha : raw20719step1 = (fun i j => raw20719step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20719step1 raw20719step0; decide +kernel
      have hl : raw20719step1Labels = raw20719step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20719step0 raw20719step0Labels permutation35 permutation5
    mixedMoment B raw20719step1 raw20719step1Labels = mixedMoment B raw20719step2 raw20719step2Labels := by
      have ha : raw20719step2 = -raw20719step1 := by apply Matrix.ext; change ∀ i j, raw20719step2 i j = -(raw20719step1 i j); unfold raw20719step2 raw20719step1; decide +kernel
      have hl : raw20719step2Labels = raw20719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20719step2 raw20719step2Labels = mixedMoment B raw20719step3 raw20719step3Labels := by
      have ha : raw20719step3 = raw20719step2 := by apply Matrix.ext; unfold raw20719step3 raw20719step2; decide +kernel
      have hl : raw20719step2Labels = labelEmbedding1 ∘ raw20719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20719step2 raw20719step2Labels raw20719step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

theorem canonical20720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20720 raw20720Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw20720 raw20720Labels = mixedMoment B raw20720step0 raw20720step0Labels := by
      have hz : ∀ j, raw20720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20720step0 = (fun i j => raw20720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20720step0 raw20720; decide +kernel
      have hl : raw20720step0Labels = raw20720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20720 raw20720Labels permutation346 hz
    mixedMoment B raw20720step0 raw20720step0Labels = mixedMoment B raw20720step1 raw20720step1Labels := by
      have hz : ∀ j, raw20720step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20720step1 = (fun i j => raw20720step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20720step1 raw20720step0; decide +kernel
      have hl : raw20720step1Labels = raw20720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20720step0 raw20720step0Labels permutation56 hz
    mixedMoment B raw20720step1 raw20720step1Labels = mixedMoment B raw20720step2 raw20720step2Labels := by
      have ha : raw20720step2 = (fun i j => raw20720step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20720step2 raw20720step1; decide +kernel
      have hl : raw20720step2Labels = raw20720step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20720step1 raw20720step1Labels permutation11 permutation5
    mixedMoment B raw20720step2 raw20720step2Labels = mixedMoment B raw20720step3 raw20720step3Labels := by
      have ha : raw20720step3 = -raw20720step2 := by apply Matrix.ext; change ∀ i j, raw20720step3 i j = -(raw20720step2 i j); unfold raw20720step3 raw20720step2; decide +kernel
      have hl : raw20720step3Labels = raw20720step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20720step3 raw20720step3Labels = mixedMoment B raw20720step4 raw20720step4Labels := by
      have ha : raw20720step4 = raw20720step3 := by apply Matrix.ext; unfold raw20720step4 raw20720step3; decide +kernel
      have hl : raw20720step3Labels = labelEmbedding1 ∘ raw20720step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20720step3 raw20720step3Labels raw20720step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical20721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20721 raw20721Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw20721 raw20721Labels = mixedMoment B raw20721step0 raw20721step0Labels := by
      have hz : ∀ j, raw20721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20721step0 = (fun i j => raw20721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20721step0 raw20721; decide +kernel
      have hl : raw20721step0Labels = raw20721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20721 raw20721Labels permutation346 hz
    mixedMoment B raw20721step0 raw20721step0Labels = mixedMoment B raw20721step1 raw20721step1Labels := by
      have hz : ∀ j, raw20721step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20721step1 = (fun i j => raw20721step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20721step1 raw20721step0; decide +kernel
      have hl : raw20721step1Labels = raw20721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20721step0 raw20721step0Labels permutation56 hz
    mixedMoment B raw20721step1 raw20721step1Labels = mixedMoment B raw20721step2 raw20721step2Labels := by
      have ha : raw20721step2 = (fun i j => raw20721step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20721step2 raw20721step1; decide +kernel
      have hl : raw20721step2Labels = raw20721step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20721step1 raw20721step1Labels permutation8 permutation7
    mixedMoment B raw20721step2 raw20721step2Labels = mixedMoment B raw20721step3 raw20721step3Labels := by
      have ha : raw20721step3 = -raw20721step2 := by apply Matrix.ext; change ∀ i j, raw20721step3 i j = -(raw20721step2 i j); unfold raw20721step3 raw20721step2; decide +kernel
      have hl : raw20721step3Labels = raw20721step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20721step3 raw20721step3Labels = mixedMoment B raw20721step4 raw20721step4Labels := by
      have ha : raw20721step4 = raw20721step3 := by apply Matrix.ext; unfold raw20721step4 raw20721step3; decide +kernel
      have hl : raw20721step3Labels = labelEmbedding1 ∘ raw20721step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20721step3 raw20721step3Labels raw20721step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

theorem canonical20722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20722 raw20722Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw20722 raw20722Labels = mixedMoment B raw20722step0 raw20722step0Labels := by
      have hz : ∀ j, raw20722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20722step0 = (fun i j => raw20722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20722step0 raw20722; decide +kernel
      have hl : raw20722step0Labels = raw20722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20722 raw20722Labels permutation346 hz
    mixedMoment B raw20722step0 raw20722step0Labels = mixedMoment B raw20722step1 raw20722step1Labels := by
      have hz : ∀ j, raw20722step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20722step1 = (fun i j => raw20722step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20722step1 raw20722step0; decide +kernel
      have hl : raw20722step1Labels = raw20722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20722step0 raw20722step0Labels permutation56 hz
    mixedMoment B raw20722step1 raw20722step1Labels = mixedMoment B raw20722step2 raw20722step2Labels := by
      have ha : raw20722step2 = (fun i j => raw20722step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20722step2 raw20722step1; decide +kernel
      have hl : raw20722step2Labels = raw20722step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20722step1 raw20722step1Labels permutation8 permutation5
    mixedMoment B raw20722step2 raw20722step2Labels = mixedMoment B raw20722step3 raw20722step3Labels := by
      have ha : raw20722step3 = -raw20722step2 := by apply Matrix.ext; change ∀ i j, raw20722step3 i j = -(raw20722step2 i j); unfold raw20722step3 raw20722step2; decide +kernel
      have hl : raw20722step3Labels = raw20722step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20722step3 raw20722step3Labels = mixedMoment B raw20722step4 raw20722step4Labels := by
      have ha : raw20722step4 = raw20722step3 := by apply Matrix.ext; unfold raw20722step4 raw20722step3; decide +kernel
      have hl : raw20722step3Labels = labelEmbedding1 ∘ raw20722step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20722step3 raw20722step3Labels raw20722step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

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

theorem canonical20724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20724 raw20724Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw20724 raw20724Labels = mixedMoment B raw20724step0 raw20724step0Labels := by
      have hz : ∀ j, raw20724 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20724step0 = (fun i j => raw20724 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20724step0 raw20724; decide +kernel
      have hl : raw20724step0Labels = raw20724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20724 raw20724Labels permutation265 hz
    mixedMoment B raw20724step0 raw20724step0Labels = mixedMoment B raw20724step1 raw20724step1Labels := by
      have ha : raw20724step1 = (fun i j => raw20724step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20724step1 raw20724step0; decide +kernel
      have hl : raw20724step1Labels = raw20724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20724step0 raw20724step0Labels permutation32 permutation5
    mixedMoment B raw20724step1 raw20724step1Labels = mixedMoment B raw20724step2 raw20724step2Labels := by
      have ha : raw20724step2 = -raw20724step1 := by apply Matrix.ext; change ∀ i j, raw20724step2 i j = -(raw20724step1 i j); unfold raw20724step2 raw20724step1; decide +kernel
      have hl : raw20724step2Labels = raw20724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20724step2 raw20724step2Labels = mixedMoment B raw20724step3 raw20724step3Labels := by
      have ha : raw20724step3 = raw20724step2 := by apply Matrix.ext; unfold raw20724step3 raw20724step2; decide +kernel
      have hl : raw20724step2Labels = labelEmbedding1 ∘ raw20724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20724step2 raw20724step2Labels raw20724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

theorem canonical20725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20725 raw20725Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw20725 raw20725Labels = mixedMoment B raw20725step0 raw20725step0Labels := by
      have hz : ∀ j, raw20725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20725step0 = (fun i j => raw20725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20725step0 raw20725; decide +kernel
      have hl : raw20725step0Labels = raw20725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20725 raw20725Labels permutation346 hz
    mixedMoment B raw20725step0 raw20725step0Labels = mixedMoment B raw20725step1 raw20725step1Labels := by
      have hz : ∀ j, raw20725step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20725step1 = (fun i j => raw20725step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20725step1 raw20725step0; decide +kernel
      have hl : raw20725step1Labels = raw20725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20725step0 raw20725step0Labels permutation56 hz
    mixedMoment B raw20725step1 raw20725step1Labels = mixedMoment B raw20725step2 raw20725step2Labels := by
      have ha : raw20725step2 = (fun i j => raw20725step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20725step2 raw20725step1; decide +kernel
      have hl : raw20725step2Labels = raw20725step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20725step1 raw20725step1Labels permutation8 permutation7
    mixedMoment B raw20725step2 raw20725step2Labels = mixedMoment B raw20725step3 raw20725step3Labels := by
      have ha : raw20725step3 = -raw20725step2 := by apply Matrix.ext; change ∀ i j, raw20725step3 i j = -(raw20725step2 i j); unfold raw20725step3 raw20725step2; decide +kernel
      have hl : raw20725step3Labels = raw20725step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20725step3 raw20725step3Labels = mixedMoment B raw20725step4 raw20725step4Labels := by
      have ha : raw20725step4 = raw20725step3 := by apply Matrix.ext; unfold raw20725step4 raw20725step3; decide +kernel
      have hl : raw20725step3Labels = labelEmbedding1 ∘ raw20725step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20725step3 raw20725step3Labels raw20725step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3276 node3276Labels := by rfl

theorem canonical20726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20726 raw20726Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw20726 raw20726Labels = mixedMoment B raw20726step0 raw20726step0Labels := by
      have hz : ∀ j, raw20726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20726step0 = (fun i j => raw20726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20726step0 raw20726; decide +kernel
      have hl : raw20726step0Labels = raw20726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20726 raw20726Labels permutation346 hz
    mixedMoment B raw20726step0 raw20726step0Labels = mixedMoment B raw20726step1 raw20726step1Labels := by
      have hz : ∀ j, raw20726step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20726step1 = (fun i j => raw20726step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20726step1 raw20726step0; decide +kernel
      have hl : raw20726step1Labels = raw20726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20726step0 raw20726step0Labels permutation56 hz
    mixedMoment B raw20726step1 raw20726step1Labels = mixedMoment B raw20726step2 raw20726step2Labels := by
      have ha : raw20726step2 = (fun i j => raw20726step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20726step2 raw20726step1; decide +kernel
      have hl : raw20726step2Labels = raw20726step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20726step1 raw20726step1Labels permutation8 permutation7
    mixedMoment B raw20726step2 raw20726step2Labels = mixedMoment B raw20726step3 raw20726step3Labels := by
      have ha : raw20726step3 = -raw20726step2 := by apply Matrix.ext; change ∀ i j, raw20726step3 i j = -(raw20726step2 i j); unfold raw20726step3 raw20726step2; decide +kernel
      have hl : raw20726step3Labels = raw20726step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20726step3 raw20726step3Labels = mixedMoment B raw20726step4 raw20726step4Labels := by
      have ha : raw20726step4 = raw20726step3 := by apply Matrix.ext; unfold raw20726step4 raw20726step3; decide +kernel
      have hl : raw20726step3Labels = labelEmbedding1 ∘ raw20726step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20726step3 raw20726step3Labels raw20726step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical20727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20727 raw20727Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw20727 raw20727Labels = mixedMoment B raw20727step0 raw20727step0Labels := by
      have hz : ∀ j, raw20727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20727step0 = (fun i j => raw20727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20727step0 raw20727; decide +kernel
      have hl : raw20727step0Labels = raw20727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20727 raw20727Labels permutation346 hz
    mixedMoment B raw20727step0 raw20727step0Labels = mixedMoment B raw20727step1 raw20727step1Labels := by
      have hz : ∀ j, raw20727step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20727step1 = (fun i j => raw20727step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20727step1 raw20727step0; decide +kernel
      have hl : raw20727step1Labels = raw20727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20727step0 raw20727step0Labels permutation56 hz
    mixedMoment B raw20727step1 raw20727step1Labels = mixedMoment B raw20727step2 raw20727step2Labels := by
      have ha : raw20727step2 = (fun i j => raw20727step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20727step2 raw20727step1; decide +kernel
      have hl : raw20727step2Labels = raw20727step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20727step1 raw20727step1Labels permutation10 permutation5
    mixedMoment B raw20727step2 raw20727step2Labels = mixedMoment B raw20727step3 raw20727step3Labels := by
      have ha : raw20727step3 = -raw20727step2 := by apply Matrix.ext; change ∀ i j, raw20727step3 i j = -(raw20727step2 i j); unfold raw20727step3 raw20727step2; decide +kernel
      have hl : raw20727step3Labels = raw20727step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20727step3 raw20727step3Labels = mixedMoment B raw20727step4 raw20727step4Labels := by
      have ha : raw20727step4 = raw20727step3 := by apply Matrix.ext; unfold raw20727step4 raw20727step3; decide +kernel
      have hl : raw20727step3Labels = labelEmbedding1 ∘ raw20727step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20727step3 raw20727step3Labels raw20727step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

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

theorem canonical20729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20729 raw20729Labels = mixedMoment B node3262 node3262Labels := by
  calc
    mixedMoment B raw20729 raw20729Labels = mixedMoment B raw20729step0 raw20729step0Labels := by
      have hz : ∀ j, raw20729 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20729step0 = (fun i j => raw20729 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20729step0 raw20729; decide +kernel
      have hl : raw20729step0Labels = raw20729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20729 raw20729Labels permutation265 hz
    mixedMoment B raw20729step0 raw20729step0Labels = mixedMoment B raw20729step1 raw20729step1Labels := by
      have ha : raw20729step1 = (fun i j => raw20729step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20729step1 raw20729step0; decide +kernel
      have hl : raw20729step1Labels = raw20729step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20729step0 raw20729step0Labels permutation34 permutation5
    mixedMoment B raw20729step1 raw20729step1Labels = mixedMoment B raw20729step2 raw20729step2Labels := by
      have ha : raw20729step2 = -raw20729step1 := by apply Matrix.ext; change ∀ i j, raw20729step2 i j = -(raw20729step1 i j); unfold raw20729step2 raw20729step1; decide +kernel
      have hl : raw20729step2Labels = raw20729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20729step2 raw20729step2Labels = mixedMoment B raw20729step3 raw20729step3Labels := by
      have ha : raw20729step3 = raw20729step2 := by apply Matrix.ext; unfold raw20729step3 raw20729step2; decide +kernel
      have hl : raw20729step2Labels = labelEmbedding1 ∘ raw20729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20729step2 raw20729step2Labels raw20729step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3262 node3262Labels := by rfl

theorem canonical20730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20730 raw20730Labels = mixedMoment B node3275 node3275Labels := by
  calc
    mixedMoment B raw20730 raw20730Labels = mixedMoment B raw20730step0 raw20730step0Labels := by
      have hz : ∀ j, raw20730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20730step0 = (fun i j => raw20730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20730step0 raw20730; decide +kernel
      have hl : raw20730step0Labels = raw20730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20730 raw20730Labels permutation346 hz
    mixedMoment B raw20730step0 raw20730step0Labels = mixedMoment B raw20730step1 raw20730step1Labels := by
      have hz : ∀ j, raw20730step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20730step1 = (fun i j => raw20730step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20730step1 raw20730step0; decide +kernel
      have hl : raw20730step1Labels = raw20730step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20730step0 raw20730step0Labels permutation56 hz
    mixedMoment B raw20730step1 raw20730step1Labels = mixedMoment B raw20730step2 raw20730step2Labels := by
      have ha : raw20730step2 = (fun i j => raw20730step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20730step2 raw20730step1; decide +kernel
      have hl : raw20730step2Labels = raw20730step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20730step1 raw20730step1Labels permutation31 permutation7
    mixedMoment B raw20730step2 raw20730step2Labels = mixedMoment B raw20730step3 raw20730step3Labels := by
      have ha : raw20730step3 = raw20730step2 := by apply Matrix.ext; unfold raw20730step3 raw20730step2; decide +kernel
      have hl : raw20730step2Labels = labelEmbedding1 ∘ raw20730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20730step2 raw20730step2Labels raw20730step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3275 node3275Labels := by rfl

theorem canonical20731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20731 raw20731Labels = mixedMoment B node3298 node3298Labels := by
  calc
    mixedMoment B raw20731 raw20731Labels = mixedMoment B raw20731step0 raw20731step0Labels := by
      have hz : ∀ j, raw20731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20731step0 = (fun i j => raw20731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20731step0 raw20731; decide +kernel
      have hl : raw20731step0Labels = raw20731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20731 raw20731Labels permutation346 hz
    mixedMoment B raw20731step0 raw20731step0Labels = mixedMoment B raw20731step1 raw20731step1Labels := by
      have hz : ∀ j, raw20731step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20731step1 = (fun i j => raw20731step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20731step1 raw20731step0; decide +kernel
      have hl : raw20731step1Labels = raw20731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20731step0 raw20731step0Labels permutation56 hz
    mixedMoment B raw20731step1 raw20731step1Labels = mixedMoment B raw20731step2 raw20731step2Labels := by
      have ha : raw20731step2 = (fun i j => raw20731step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20731step2 raw20731step1; decide +kernel
      have hl : raw20731step2Labels = raw20731step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20731step1 raw20731step1Labels permutation29 permutation5
    mixedMoment B raw20731step2 raw20731step2Labels = mixedMoment B raw20731step3 raw20731step3Labels := by
      have ha : raw20731step3 = raw20731step2 := by apply Matrix.ext; unfold raw20731step3 raw20731step2; decide +kernel
      have hl : raw20731step2Labels = labelEmbedding1 ∘ raw20731step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20731step2 raw20731step2Labels raw20731step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3298 node3298Labels := by rfl

theorem canonical20732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20732 raw20732Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw20732 raw20732Labels = mixedMoment B raw20732step0 raw20732step0Labels := by
      have hz : ∀ j, raw20732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20732step0 = (fun i j => raw20732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20732step0 raw20732; decide +kernel
      have hl : raw20732step0Labels = raw20732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20732 raw20732Labels permutation346 hz
    mixedMoment B raw20732step0 raw20732step0Labels = mixedMoment B raw20732step1 raw20732step1Labels := by
      have hz : ∀ j, raw20732step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20732step1 = (fun i j => raw20732step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20732step1 raw20732step0; decide +kernel
      have hl : raw20732step1Labels = raw20732step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20732step0 raw20732step0Labels permutation56 hz
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical20733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20733 raw20733Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw20733 raw20733Labels = mixedMoment B raw20733step0 raw20733step0Labels := by
      have hz : ∀ j, raw20733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20733step0 = (fun i j => raw20733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20733step0 raw20733; decide +kernel
      have hl : raw20733step0Labels = raw20733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20733 raw20733Labels permutation346 hz
    mixedMoment B raw20733step0 raw20733step0Labels = mixedMoment B raw20733step1 raw20733step1Labels := by
      have ha : raw20733step1 = (fun i j => raw20733step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20733step1 raw20733step0; decide +kernel
      have hl : raw20733step1Labels = raw20733step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20733step0 raw20733step0Labels permutation38 permutation2
    _ = mixedMoment B node626 node626Labels := by rfl

theorem canonical20734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20734 raw20734Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw20734 raw20734Labels = mixedMoment B raw20734step0 raw20734step0Labels := by
      have hz : ∀ j, raw20734 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20734step0 = (fun i j => raw20734 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20734step0 raw20734; decide +kernel
      have hl : raw20734step0Labels = raw20734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20734 raw20734Labels permutation265 hz
    mixedMoment B raw20734step0 raw20734step0Labels = mixedMoment B raw20734step1 raw20734step1Labels := by
      have ha : raw20734step1 = (fun i j => raw20734step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20734step1 raw20734step0; decide +kernel
      have hl : raw20734step1Labels = raw20734step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20734step0 raw20734step0Labels permutation38 permutation2
    _ = mixedMoment B node626 node626Labels := by rfl

theorem canonical20735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20735 raw20735Labels = mixedMoment B node641 node641Labels := by
  calc
    mixedMoment B raw20735 raw20735Labels = mixedMoment B raw20735step0 raw20735step0Labels := by
      have hz : ∀ j, raw20735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20735step0 = (fun i j => raw20735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20735step0 raw20735; decide +kernel
      have hl : raw20735step0Labels = raw20735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20735 raw20735Labels permutation346 hz
    mixedMoment B raw20735step0 raw20735step0Labels = mixedMoment B raw20735step1 raw20735step1Labels := by
      have hz : ∀ j, raw20735step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20735step1 = (fun i j => raw20735step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20735step1 raw20735step0; decide +kernel
      have hl : raw20735step1Labels = raw20735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20735step0 raw20735step0Labels permutation56 hz
    _ = mixedMoment B node641 node641Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20736 raw20736Labels = mixedMoment B node635 node635Labels := by
  calc
    mixedMoment B raw20736 raw20736Labels = mixedMoment B raw20736step0 raw20736step0Labels := by
      have hz : ∀ j, raw20736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20736step0 = (fun i j => raw20736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20736step0 raw20736; decide +kernel
      have hl : raw20736step0Labels = raw20736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20736 raw20736Labels permutation346 hz
    mixedMoment B raw20736step0 raw20736step0Labels = mixedMoment B raw20736step1 raw20736step1Labels := by
      have hz : ∀ j, raw20736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20736step1 = (fun i j => raw20736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20736step1 raw20736step0; decide +kernel
      have hl : raw20736step1Labels = raw20736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20736step0 raw20736step0Labels permutation56 hz
    _ = mixedMoment B node635 node635Labels := by rfl

theorem canonical20737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20737 raw20737Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw20737 raw20737Labels = mixedMoment B raw20737step0 raw20737step0Labels := by
      have hz : ∀ j, raw20737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20737step0 = (fun i j => raw20737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20737step0 raw20737; decide +kernel
      have hl : raw20737step0Labels = raw20737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20737 raw20737Labels permutation346 hz
    mixedMoment B raw20737step0 raw20737step0Labels = mixedMoment B raw20737step1 raw20737step1Labels := by
      have hz : ∀ j, raw20737step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20737step1 = (fun i j => raw20737step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20737step1 raw20737step0; decide +kernel
      have hl : raw20737step1Labels = raw20737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20737step0 raw20737step0Labels permutation56 hz
    _ = mixedMoment B node633 node633Labels := by rfl

theorem canonical20738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20738 raw20738Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw20738 raw20738Labels = mixedMoment B raw20738step0 raw20738step0Labels := by
      have hz : ∀ j, raw20738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20738step0 = (fun i j => raw20738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20738step0 raw20738; decide +kernel
      have hl : raw20738step0Labels = raw20738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20738 raw20738Labels permutation346 hz
    mixedMoment B raw20738step0 raw20738step0Labels = mixedMoment B raw20738step1 raw20738step1Labels := by
      have hz : ∀ j, raw20738step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20738step1 = (fun i j => raw20738step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20738step1 raw20738step0; decide +kernel
      have hl : raw20738step1Labels = raw20738step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20738step0 raw20738step0Labels permutation56 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical20739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20739 raw20739Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw20739 raw20739Labels = mixedMoment B raw20739step0 raw20739step0Labels := by
      have hz : ∀ j, raw20739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20739step0 = (fun i j => raw20739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20739step0 raw20739; decide +kernel
      have hl : raw20739step0Labels = raw20739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20739 raw20739Labels permutation346 hz
    mixedMoment B raw20739step0 raw20739step0Labels = mixedMoment B raw20739step1 raw20739step1Labels := by
      have ha : raw20739step1 = (fun i j => raw20739step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20739step1 raw20739step0; decide +kernel
      have hl : raw20739step1Labels = raw20739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20739step0 raw20739step0Labels permutation151 permutation2
    mixedMoment B raw20739step1 raw20739step1Labels = mixedMoment B raw20739step2 raw20739step2Labels := by
      have ha : raw20739step2 = -raw20739step1 := by apply Matrix.ext; change ∀ i j, raw20739step2 i j = -(raw20739step1 i j); unfold raw20739step2 raw20739step1; decide +kernel
      have hl : raw20739step2Labels = raw20739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical20740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20740 raw20740Labels = mixedMoment B node1148 node1148Labels := by
  calc
    mixedMoment B raw20740 raw20740Labels = mixedMoment B raw20740step0 raw20740step0Labels := by
      have ha : raw20740step0 = (fun i j => raw20740 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20740step0 raw20740; decide +kernel
      have hl : raw20740step0Labels = raw20740Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20740 raw20740Labels permutation158 permutation2
    _ = mixedMoment B node1148 node1148Labels := by rfl

theorem canonical20741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20741 raw20741Labels = mixedMoment B node1159 node1159Labels := by
  calc
    mixedMoment B raw20741 raw20741Labels = mixedMoment B raw20741step0 raw20741step0Labels := by
      have hz : ∀ j, raw20741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20741step0 = (fun i j => raw20741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20741step0 raw20741; decide +kernel
      have hl : raw20741step0Labels = raw20741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20741 raw20741Labels permutation346 hz
    _ = mixedMoment B node1159 node1159Labels := by rfl

theorem canonical20742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20742 raw20742Labels = mixedMoment B node1154 node1154Labels := by
  calc
    mixedMoment B raw20742 raw20742Labels = mixedMoment B raw20742step0 raw20742step0Labels := by
      have hz : ∀ j, raw20742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20742step0 = (fun i j => raw20742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20742step0 raw20742; decide +kernel
      have hl : raw20742step0Labels = raw20742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20742 raw20742Labels permutation346 hz
    _ = mixedMoment B node1154 node1154Labels := by rfl

theorem canonical20743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20743 raw20743Labels = mixedMoment B node1115 node1115Labels := by
  calc
    mixedMoment B raw20743 raw20743Labels = mixedMoment B raw20743step0 raw20743step0Labels := by
      have hz : ∀ j, raw20743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20743step0 = (fun i j => raw20743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20743step0 raw20743; decide +kernel
      have hl : raw20743step0Labels = raw20743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20743 raw20743Labels permutation346 hz
    mixedMoment B raw20743step0 raw20743step0Labels = mixedMoment B raw20743step1 raw20743step1Labels := by
      have ha : raw20743step1 = (fun i j => raw20743step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20743step1 raw20743step0; decide +kernel
      have hl : raw20743step1Labels = raw20743step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20743step0 raw20743step0Labels permutation151 permutation2
    mixedMoment B raw20743step1 raw20743step1Labels = mixedMoment B raw20743step2 raw20743step2Labels := by
      have ha : raw20743step2 = -raw20743step1 := by apply Matrix.ext; change ∀ i j, raw20743step2 i j = -(raw20743step1 i j); unfold raw20743step2 raw20743step1; decide +kernel
      have hl : raw20743step2Labels = raw20743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1115 node1115Labels := by rfl

theorem canonical20744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20744 raw20744Labels = mixedMoment B node2517 node2517Labels := by
  calc
    mixedMoment B raw20744 raw20744Labels = mixedMoment B raw20744step0 raw20744step0Labels := by
      have hz : ∀ j, raw20744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20744step0 = (fun i j => raw20744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20744step0 raw20744; decide +kernel
      have hl : raw20744step0Labels = raw20744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20744 raw20744Labels permutation346 hz
    mixedMoment B raw20744step0 raw20744step0Labels = mixedMoment B raw20744step1 raw20744step1Labels := by
      have hz : ∀ j, raw20744step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20744step1 = (fun i j => raw20744step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20744step1 raw20744step0; decide +kernel
      have hl : raw20744step1Labels = raw20744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20744step0 raw20744step0Labels permutation56 hz
    _ = mixedMoment B node2517 node2517Labels := by rfl

theorem canonical20745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20745 raw20745Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20745 raw20745Labels = mixedMoment B raw20745step0 raw20745step0Labels := by
      have hz : ∀ j, raw20745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20745step0 = (fun i j => raw20745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20745step0 raw20745; decide +kernel
      have hl : raw20745step0Labels = raw20745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20745 raw20745Labels permutation346 hz
    mixedMoment B raw20745step0 raw20745step0Labels = mixedMoment B raw20745step1 raw20745step1Labels := by
      have ha : raw20745step1 = (fun i j => raw20745step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20745step1 raw20745step0; decide +kernel
      have hl : raw20745step1Labels = raw20745step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20745step0 raw20745step0Labels permutation38 permutation2
    _ = mixedMoment B node1131 node1131Labels := by rfl

theorem canonical20746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20746 raw20746Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20746 raw20746Labels = mixedMoment B raw20746step0 raw20746step0Labels := by
      have hz : ∀ j, raw20746 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20746step0 = (fun i j => raw20746 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20746step0 raw20746; decide +kernel
      have hl : raw20746step0Labels = raw20746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20746 raw20746Labels permutation265 hz
    mixedMoment B raw20746step0 raw20746step0Labels = mixedMoment B raw20746step1 raw20746step1Labels := by
      have ha : raw20746step1 = (fun i j => raw20746step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20746step1 raw20746step0; decide +kernel
      have hl : raw20746step1Labels = raw20746step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20746step0 raw20746step0Labels permutation38 permutation2
    _ = mixedMoment B node1131 node1131Labels := by rfl

theorem canonical20747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20747 raw20747Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw20747 raw20747Labels = mixedMoment B raw20747step0 raw20747step0Labels := by
      have hz : ∀ j, raw20747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20747step0 = (fun i j => raw20747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20747step0 raw20747; decide +kernel
      have hl : raw20747step0Labels = raw20747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20747 raw20747Labels permutation346 hz
    mixedMoment B raw20747step0 raw20747step0Labels = mixedMoment B raw20747step1 raw20747step1Labels := by
      have hz : ∀ j, raw20747step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20747step1 = (fun i j => raw20747step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20747step1 raw20747step0; decide +kernel
      have hl : raw20747step1Labels = raw20747step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20747step0 raw20747step0Labels permutation56 hz
    _ = mixedMoment B node1144 node1144Labels := by rfl

theorem canonical20748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20748 raw20748Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw20748 raw20748Labels = mixedMoment B raw20748step0 raw20748step0Labels := by
      have hz : ∀ j, raw20748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20748step0 = (fun i j => raw20748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20748step0 raw20748; decide +kernel
      have hl : raw20748step0Labels = raw20748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20748 raw20748Labels permutation346 hz
    mixedMoment B raw20748step0 raw20748step0Labels = mixedMoment B raw20748step1 raw20748step1Labels := by
      have hz : ∀ j, raw20748step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20748step1 = (fun i j => raw20748step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20748step1 raw20748step0; decide +kernel
      have hl : raw20748step1Labels = raw20748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20748step0 raw20748step0Labels permutation56 hz
    _ = mixedMoment B node1140 node1140Labels := by rfl

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

theorem canonical5136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5136 raw5136Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw5136 raw5136Labels = mixedMoment B raw5136step0 raw5136step0Labels := by
      have hz : ∀ j, raw5136 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5136step0 = (fun i j => raw5136 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5136step0 raw5136; decide +kernel
      have hl : raw5136step0Labels = raw5136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5136 raw5136Labels permutation434 hz
    mixedMoment B raw5136step0 raw5136step0Labels = mixedMoment B raw5136step1 raw5136step1Labels := by
      have hz : ∀ j, raw5136step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5136step1 = (fun i j => raw5136step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5136step1 raw5136step0; decide +kernel
      have hl : raw5136step1Labels = raw5136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5136step0 raw5136step0Labels permutation80 hz
    mixedMoment B raw5136step1 raw5136step1Labels = mixedMoment B raw5136step2 raw5136step2Labels := by
      have ha : raw5136step2 = (fun i j => raw5136step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5136step2 raw5136step1; decide +kernel
      have hl : raw5136step2Labels = raw5136step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5136step1 raw5136step1Labels permutation29 permutation7
    mixedMoment B raw5136step2 raw5136step2Labels = mixedMoment B raw5136step3 raw5136step3Labels := by
      have ha : raw5136step3 = raw5136step2 := by apply Matrix.ext; unfold raw5136step3 raw5136step2; decide +kernel
      have hl : raw5136step2Labels = labelEmbedding1 ∘ raw5136step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5136step2 raw5136step2Labels raw5136step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5141 raw5141Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw5141 raw5141Labels = mixedMoment B raw5141step0 raw5141step0Labels := by
      have hz : ∀ j, raw5141 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5141step0 = (fun i j => raw5141 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5141step0 raw5141; decide +kernel
      have hl : raw5141step0Labels = raw5141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5141 raw5141Labels permutation434 hz
    mixedMoment B raw5141step0 raw5141step0Labels = mixedMoment B raw5141step1 raw5141step1Labels := by
      have hz : ∀ j, raw5141step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5141step1 = (fun i j => raw5141step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5141step1 raw5141step0; decide +kernel
      have hl : raw5141step1Labels = raw5141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5141step0 raw5141step0Labels permutation56 hz
    mixedMoment B raw5141step1 raw5141step1Labels = mixedMoment B raw5141step2 raw5141step2Labels := by
      have ha : raw5141step2 = (fun i j => raw5141step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5141step2 raw5141step1; decide +kernel
      have hl : raw5141step2Labels = raw5141step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5141step1 raw5141step1Labels permutation29 permutation7
    mixedMoment B raw5141step2 raw5141step2Labels = mixedMoment B raw5141step3 raw5141step3Labels := by
      have ha : raw5141step3 = raw5141step2 := by apply Matrix.ext; unfold raw5141step3 raw5141step2; decide +kernel
      have hl : raw5141step2Labels = labelEmbedding1 ∘ raw5141step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5141step2 raw5141step2Labels raw5141step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical5146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5146 raw5146Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw5146 raw5146Labels = mixedMoment B raw5146step0 raw5146step0Labels := by
      have hz : ∀ j, raw5146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5146step0 = (fun i j => raw5146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5146step0 raw5146; decide +kernel
      have hl : raw5146step0Labels = raw5146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5146 raw5146Labels permutation346 hz
    mixedMoment B raw5146step0 raw5146step0Labels = mixedMoment B raw5146step1 raw5146step1Labels := by
      have hz : ∀ j, raw5146step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5146step1 = (fun i j => raw5146step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5146step1 raw5146step0; decide +kernel
      have hl : raw5146step1Labels = raw5146step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5146step0 raw5146step0Labels permutation56 hz
    mixedMoment B raw5146step1 raw5146step1Labels = mixedMoment B raw5146step2 raw5146step2Labels := by
      have ha : raw5146step2 = (fun i j => raw5146step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5146step2 raw5146step1; decide +kernel
      have hl : raw5146step2Labels = raw5146step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5146step1 raw5146step1Labels permutation29 permutation7
    mixedMoment B raw5146step2 raw5146step2Labels = mixedMoment B raw5146step3 raw5146step3Labels := by
      have ha : raw5146step3 = raw5146step2 := by apply Matrix.ext; unfold raw5146step3 raw5146step2; decide +kernel
      have hl : raw5146step2Labels = labelEmbedding1 ∘ raw5146step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5146step2 raw5146step2Labels raw5146step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical5152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5152 raw5152Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw5152 raw5152Labels = mixedMoment B raw5152step0 raw5152step0Labels := by
      have hz : ∀ j, raw5152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5152step0 = (fun i j => raw5152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5152step0 raw5152; decide +kernel
      have hl : raw5152step0Labels = raw5152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5152 raw5152Labels permutation434 hz
    mixedMoment B raw5152step0 raw5152step0Labels = mixedMoment B raw5152step1 raw5152step1Labels := by
      have hz : ∀ j, raw5152step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5152step1 = (fun i j => raw5152step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5152step1 raw5152step0; decide +kernel
      have hl : raw5152step1Labels = raw5152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5152step0 raw5152step0Labels permutation80 hz
    mixedMoment B raw5152step1 raw5152step1Labels = mixedMoment B raw5152step2 raw5152step2Labels := by
      have ha : raw5152step2 = (fun i j => raw5152step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5152step2 raw5152step1; decide +kernel
      have hl : raw5152step2Labels = raw5152step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5152step1 raw5152step1Labels permutation29 permutation7
    mixedMoment B raw5152step2 raw5152step2Labels = mixedMoment B raw5152step3 raw5152step3Labels := by
      have ha : raw5152step3 = raw5152step2 := by apply Matrix.ext; unfold raw5152step3 raw5152step2; decide +kernel
      have hl : raw5152step2Labels = labelEmbedding1 ∘ raw5152step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5152step2 raw5152step2Labels raw5152step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

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

theorem canonical5156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5156 raw5156Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw5156 raw5156Labels = mixedMoment B raw5156step0 raw5156step0Labels := by
      have hz : ∀ j, raw5156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5156step0 = (fun i j => raw5156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5156step0 raw5156; decide +kernel
      have hl : raw5156step0Labels = raw5156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5156 raw5156Labels permutation434 hz
    mixedMoment B raw5156step0 raw5156step0Labels = mixedMoment B raw5156step1 raw5156step1Labels := by
      have hz : ∀ j, raw5156step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5156step1 = (fun i j => raw5156step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5156step1 raw5156step0; decide +kernel
      have hl : raw5156step1Labels = raw5156step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5156step0 raw5156step0Labels permutation80 hz
    mixedMoment B raw5156step1 raw5156step1Labels = mixedMoment B raw5156step2 raw5156step2Labels := by
      have hz : ∀ j, raw5156step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5156step2 = (fun i j => raw5156step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5156step2 raw5156step1; decide +kernel
      have hl : raw5156step2Labels = raw5156step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5156step1 raw5156step1Labels permutation14 hz
    mixedMoment B raw5156step2 raw5156step2Labels = mixedMoment B raw5156step3 raw5156step3Labels := by
      have ha : raw5156step3 = (fun i j => raw5156step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5156step3 raw5156step2; decide +kernel
      have hl : raw5156step3Labels = raw5156step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5156step2 raw5156step2Labels permutation7 permutation7
    mixedMoment B raw5156step3 raw5156step3Labels = mixedMoment B raw5156step4 raw5156step4Labels := by
      have ha : raw5156step4 = raw5156step3 := by apply Matrix.ext; unfold raw5156step4 raw5156step3; decide +kernel
      have hl : raw5156step3Labels = labelEmbedding1 ∘ raw5156step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5156step3 raw5156step3Labels raw5156step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical5162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5162 raw5162Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw5162 raw5162Labels = mixedMoment B raw5162step0 raw5162step0Labels := by
      have hz : ∀ j, raw5162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5162step0 = (fun i j => raw5162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5162step0 raw5162; decide +kernel
      have hl : raw5162step0Labels = raw5162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5162 raw5162Labels permutation434 hz
    mixedMoment B raw5162step0 raw5162step0Labels = mixedMoment B raw5162step1 raw5162step1Labels := by
      have hz : ∀ j, raw5162step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5162step1 = (fun i j => raw5162step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5162step1 raw5162step0; decide +kernel
      have hl : raw5162step1Labels = raw5162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5162step0 raw5162step0Labels permutation80 hz
    mixedMoment B raw5162step1 raw5162step1Labels = mixedMoment B raw5162step2 raw5162step2Labels := by
      have ha : raw5162step2 = (fun i j => raw5162step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5162step2 raw5162step1; decide +kernel
      have hl : raw5162step2Labels = raw5162step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5162step1 raw5162step1Labels permutation10 permutation2
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical5165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5165 raw5165Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw5165 raw5165Labels = mixedMoment B raw5165step0 raw5165step0Labels := by
      have hz : ∀ j, raw5165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5165step0 = (fun i j => raw5165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5165step0 raw5165; decide +kernel
      have hl : raw5165step0Labels = raw5165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5165 raw5165Labels permutation434 hz
    mixedMoment B raw5165step0 raw5165step0Labels = mixedMoment B raw5165step1 raw5165step1Labels := by
      have hz : ∀ j, raw5165step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5165step1 = (fun i j => raw5165step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5165step1 raw5165step0; decide +kernel
      have hl : raw5165step1Labels = raw5165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5165step0 raw5165step0Labels permutation80 hz
    mixedMoment B raw5165step1 raw5165step1Labels = mixedMoment B raw5165step2 raw5165step2Labels := by
      have hz : ∀ j, raw5165step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5165step2 = (fun i j => raw5165step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5165step2 raw5165step1; decide +kernel
      have hl : raw5165step2Labels = raw5165step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5165step1 raw5165step1Labels permutation14 hz
    _ = mixedMoment B node1297 node1297Labels := by rfl

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

theorem canonical10294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10294 raw10294Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw10294 raw10294Labels = mixedMoment B raw10294step0 raw10294step0Labels := by
      have hz : ∀ j, raw10294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10294step0 = (fun i j => raw10294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10294step0 raw10294; decide +kernel
      have hl : raw10294step0Labels = raw10294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10294 raw10294Labels permutation434 hz
    mixedMoment B raw10294step0 raw10294step0Labels = mixedMoment B raw10294step1 raw10294step1Labels := by
      have hz : ∀ j, raw10294step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10294step1 = (fun i j => raw10294step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10294step1 raw10294step0; decide +kernel
      have hl : raw10294step1Labels = raw10294step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10294step0 raw10294step0Labels permutation80 hz
    mixedMoment B raw10294step1 raw10294step1Labels = mixedMoment B raw10294step2 raw10294step2Labels := by
      have ha : raw10294step2 = (fun i j => raw10294step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10294step2 raw10294step1; decide +kernel
      have hl : raw10294step2Labels = raw10294step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10294step1 raw10294step1Labels permutation29 permutation7
    mixedMoment B raw10294step2 raw10294step2Labels = mixedMoment B raw10294step3 raw10294step3Labels := by
      have ha : raw10294step3 = raw10294step2 := by apply Matrix.ext; unfold raw10294step3 raw10294step2; decide +kernel
      have hl : raw10294step2Labels = labelEmbedding1 ∘ raw10294step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10294step2 raw10294step2Labels raw10294step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical10298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10298 raw10298Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw10298 raw10298Labels = mixedMoment B raw10298step0 raw10298step0Labels := by
      have hz : ∀ j, raw10298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10298step0 = (fun i j => raw10298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10298step0 raw10298; decide +kernel
      have hl : raw10298step0Labels = raw10298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10298 raw10298Labels permutation434 hz
    mixedMoment B raw10298step0 raw10298step0Labels = mixedMoment B raw10298step1 raw10298step1Labels := by
      have hz : ∀ j, raw10298step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10298step1 = (fun i j => raw10298step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10298step1 raw10298step0; decide +kernel
      have hl : raw10298step1Labels = raw10298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10298step0 raw10298step0Labels permutation56 hz
    mixedMoment B raw10298step1 raw10298step1Labels = mixedMoment B raw10298step2 raw10298step2Labels := by
      have ha : raw10298step2 = (fun i j => raw10298step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10298step2 raw10298step1; decide +kernel
      have hl : raw10298step2Labels = raw10298step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10298step1 raw10298step1Labels permutation29 permutation7
    mixedMoment B raw10298step2 raw10298step2Labels = mixedMoment B raw10298step3 raw10298step3Labels := by
      have ha : raw10298step3 = raw10298step2 := by apply Matrix.ext; unfold raw10298step3 raw10298step2; decide +kernel
      have hl : raw10298step2Labels = labelEmbedding1 ∘ raw10298step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10298step2 raw10298step2Labels raw10298step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical10302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10302 raw10302Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw10302 raw10302Labels = mixedMoment B raw10302step0 raw10302step0Labels := by
      have hz : ∀ j, raw10302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10302step0 = (fun i j => raw10302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10302step0 raw10302; decide +kernel
      have hl : raw10302step0Labels = raw10302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10302 raw10302Labels permutation346 hz
    mixedMoment B raw10302step0 raw10302step0Labels = mixedMoment B raw10302step1 raw10302step1Labels := by
      have hz : ∀ j, raw10302step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10302step1 = (fun i j => raw10302step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10302step1 raw10302step0; decide +kernel
      have hl : raw10302step1Labels = raw10302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10302step0 raw10302step0Labels permutation56 hz
    mixedMoment B raw10302step1 raw10302step1Labels = mixedMoment B raw10302step2 raw10302step2Labels := by
      have ha : raw10302step2 = (fun i j => raw10302step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10302step2 raw10302step1; decide +kernel
      have hl : raw10302step2Labels = raw10302step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10302step1 raw10302step1Labels permutation29 permutation7
    mixedMoment B raw10302step2 raw10302step2Labels = mixedMoment B raw10302step3 raw10302step3Labels := by
      have ha : raw10302step3 = raw10302step2 := by apply Matrix.ext; unfold raw10302step3 raw10302step2; decide +kernel
      have hl : raw10302step2Labels = labelEmbedding1 ∘ raw10302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10302step2 raw10302step2Labels raw10302step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical10306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10306 raw10306Labels = mixedMoment B node2780 node2780Labels := by
  calc
    mixedMoment B raw10306 raw10306Labels = mixedMoment B raw10306step0 raw10306step0Labels := by
      have hz : ∀ j, raw10306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10306step0 = (fun i j => raw10306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10306step0 raw10306; decide +kernel
      have hl : raw10306step0Labels = raw10306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10306 raw10306Labels permutation434 hz
    mixedMoment B raw10306step0 raw10306step0Labels = mixedMoment B raw10306step1 raw10306step1Labels := by
      have hz : ∀ j, raw10306step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10306step1 = (fun i j => raw10306step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10306step1 raw10306step0; decide +kernel
      have hl : raw10306step1Labels = raw10306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10306step0 raw10306step0Labels permutation80 hz
    mixedMoment B raw10306step1 raw10306step1Labels = mixedMoment B raw10306step2 raw10306step2Labels := by
      have hz : ∀ j, raw10306step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10306step2 = (fun i j => raw10306step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10306step2 raw10306step1; decide +kernel
      have hl : raw10306step2Labels = raw10306step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10306step1 raw10306step1Labels permutation14 hz
    mixedMoment B raw10306step2 raw10306step2Labels = mixedMoment B raw10306step3 raw10306step3Labels := by
      have ha : raw10306step3 = (fun i j => raw10306step2 (permutation5 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10306step3 raw10306step2; decide +kernel
      have hl : raw10306step3Labels = raw10306step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10306step2 raw10306step2Labels permutation5 permutation5
    mixedMoment B raw10306step3 raw10306step3Labels = mixedMoment B raw10306step4 raw10306step4Labels := by
      have ha : raw10306step4 = raw10306step3 := by apply Matrix.ext; unfold raw10306step4 raw10306step3; decide +kernel
      have hl : raw10306step3Labels = labelEmbedding1 ∘ raw10306step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10306step3 raw10306step3Labels raw10306step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2780 node2780Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node641 node641Labels = Sparse.eval nodeValue641 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 641) = mixedMoment B node641 node641Labels := rfl
  simpa [nodeValue641, Sparse.eval] using hc.symm

theorem sound643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node643 node643Labels = Sparse.eval nodeValue643 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 643) = mixedMoment B node643 node643Labels := rfl
  simpa [nodeValue643, Sparse.eval] using hc.symm

theorem sound654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node654 node654Labels = Sparse.eval nodeValue654 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 654) = mixedMoment B node654 node654Labels := rfl
  simpa [nodeValue654, Sparse.eval] using hc.symm

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

theorem sound948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node948 node948Labels = Sparse.eval nodeValue948 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 948) = mixedMoment B node948 node948Labels := rfl
  simpa [nodeValue948, Sparse.eval] using hc.symm

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

theorem sound1077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1077 node1077Labels = Sparse.eval nodeValue1077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1077) = mixedMoment B node1077 node1077Labels := rfl
  simpa [nodeValue1077, Sparse.eval] using hc.symm

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

theorem sound1115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1115 node1115Labels = Sparse.eval nodeValue1115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1115) = mixedMoment B node1115 node1115Labels := rfl
  simpa [nodeValue1115, Sparse.eval] using hc.symm

theorem sound1131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1131 node1131Labels = Sparse.eval nodeValue1131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1131) = mixedMoment B node1131 node1131Labels := rfl
  simpa [nodeValue1131, Sparse.eval] using hc.symm

theorem sound1140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1140 node1140Labels = Sparse.eval nodeValue1140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1140) = mixedMoment B node1140 node1140Labels := rfl
  simpa [nodeValue1140, Sparse.eval] using hc.symm

theorem sound1144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1144 node1144Labels = Sparse.eval nodeValue1144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1144) = mixedMoment B node1144 node1144Labels := rfl
  simpa [nodeValue1144, Sparse.eval] using hc.symm

theorem sound1148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1148 node1148Labels = Sparse.eval nodeValue1148 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1148) = mixedMoment B node1148 node1148Labels := rfl
  simpa [nodeValue1148, Sparse.eval] using hc.symm

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

theorem sound1154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1154 node1154Labels = Sparse.eval nodeValue1154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1154) = mixedMoment B node1154 node1154Labels := rfl
  simpa [nodeValue1154, Sparse.eval] using hc.symm

theorem sound1157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1157 node1157Labels = Sparse.eval nodeValue1157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1157) = mixedMoment B node1157 node1157Labels := rfl
  simpa [nodeValue1157, Sparse.eval] using hc.symm

theorem sound1159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1159 node1159Labels = Sparse.eval nodeValue1159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1159) = mixedMoment B node1159 node1159Labels := rfl
  simpa [nodeValue1159, Sparse.eval] using hc.symm

theorem sound1174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1174 node1174Labels = Sparse.eval nodeValue1174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1174) = mixedMoment B node1174 node1174Labels := rfl
  simpa [nodeValue1174, Sparse.eval] using hc.symm

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

theorem sound1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1239 node1239Labels = Sparse.eval nodeValue1239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1239) = mixedMoment B node1239 node1239Labels := rfl
  simpa [nodeValue1239, Sparse.eval] using hc.symm

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

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

theorem sound1289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1289 node1289Labels = Sparse.eval nodeValue1289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1289) = mixedMoment B node1289 node1289Labels := rfl
  simpa [nodeValue1289, Sparse.eval] using hc.symm

theorem sound1292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1292 node1292Labels = Sparse.eval nodeValue1292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1292) = mixedMoment B node1292 node1292Labels := rfl
  simpa [nodeValue1292, Sparse.eval] using hc.symm

theorem sound1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1297 node1297Labels = Sparse.eval nodeValue1297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1297) = mixedMoment B node1297 node1297Labels := rfl
  simpa [nodeValue1297, Sparse.eval] using hc.symm

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

theorem sound1514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1514 node1514Labels = Sparse.eval nodeValue1514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1514) = mixedMoment B node1514 node1514Labels := rfl
  simpa [nodeValue1514, Sparse.eval] using hc.symm

theorem sound1516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1516 node1516Labels = Sparse.eval nodeValue1516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1516) = mixedMoment B node1516 node1516Labels := rfl
  simpa [nodeValue1516, Sparse.eval] using hc.symm

theorem sound1520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1520 node1520Labels = Sparse.eval nodeValue1520 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1520) = mixedMoment B node1520 node1520Labels := rfl
  simpa [nodeValue1520, Sparse.eval] using hc.symm

theorem sound1530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1530 node1530Labels = Sparse.eval nodeValue1530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1530) = mixedMoment B node1530 node1530Labels := rfl
  simpa [nodeValue1530, Sparse.eval] using hc.symm

theorem sound1531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1531 node1531Labels = Sparse.eval nodeValue1531 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1531) = mixedMoment B node1531 node1531Labels := rfl
  simpa [nodeValue1531, Sparse.eval] using hc.symm

theorem sound1533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1533 node1533Labels = Sparse.eval nodeValue1533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1533) = mixedMoment B node1533 node1533Labels := rfl
  simpa [nodeValue1533, Sparse.eval] using hc.symm

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

theorem sound1540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1540 node1540Labels = Sparse.eval nodeValue1540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1540) = mixedMoment B node1540 node1540Labels := rfl
  simpa [nodeValue1540, Sparse.eval] using hc.symm

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

theorem sound1647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1647 node1647Labels = Sparse.eval nodeValue1647 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1647) = mixedMoment B node1647 node1647Labels := rfl
  simpa [nodeValue1647, Sparse.eval] using hc.symm

theorem sound1657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1657 node1657Labels = Sparse.eval nodeValue1657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1657) = mixedMoment B node1657 node1657Labels := rfl
  simpa [nodeValue1657, Sparse.eval] using hc.symm

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

theorem sound1722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1722 node1722Labels = Sparse.eval nodeValue1722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1722) = mixedMoment B node1722 node1722Labels := rfl
  simpa [nodeValue1722, Sparse.eval] using hc.symm

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

theorem zero1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1730 node1730Labels = 0 := by
  exact mixedMoment_order_one B hB node1730 node1730Labels 1
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

theorem sound1730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1730 node1730Labels = Sparse.eval nodeValue1730 (mixedVector B) := by
  simpa only [nodeValue1730, Sparse.eval_nil] using zero1730 B _hB _hF

theorem sound1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1741 node1741Labels = Sparse.eval nodeValue1741 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1741) = mixedMoment B node1741 node1741Labels := rfl
  simpa [nodeValue1741, Sparse.eval] using hc.symm

theorem sound1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1752 node1752Labels = Sparse.eval nodeValue1752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1752) = mixedMoment B node1752 node1752Labels := rfl
  simpa [nodeValue1752, Sparse.eval] using hc.symm

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

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

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

theorem sound2200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2200 node2200Labels = Sparse.eval nodeValue2200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2200) = mixedMoment B node2200 node2200Labels := rfl
  simpa [nodeValue2200, Sparse.eval] using hc.symm

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

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

theorem sound2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2482 node2482Labels = Sparse.eval nodeValue2482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2482) = mixedMoment B node2482 node2482Labels := rfl
  simpa [nodeValue2482, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2517 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2517 node2517Labels = 0 := by
  exact mixedMoment_order_one B hB node2517 node2517Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2517 node2517Labels = Sparse.eval nodeValue2517 (mixedVector B) := by
  simpa only [nodeValue2517, Sparse.eval_nil] using zero2517 B _hB _hF

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

theorem sound2737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2737 node2737Labels = Sparse.eval nodeValue2737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2737) = mixedMoment B node2737 node2737Labels := rfl
  simpa [nodeValue2737, Sparse.eval] using hc.symm

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

theorem sound2780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2780 node2780Labels = Sparse.eval nodeValue2780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2780) = mixedMoment B node2780 node2780Labels := rfl
  simpa [nodeValue2780, Sparse.eval] using hc.symm

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

theorem sound3291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3291 node3291Labels = Sparse.eval nodeValue3291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3291) = mixedMoment B node3291 node3291Labels := rfl
  simpa [nodeValue3291, Sparse.eval] using hc.symm

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

theorem sound3298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3298 node3298Labels = Sparse.eval nodeValue3298 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3298) = mixedMoment B node3298 node3298Labels := rfl
  simpa [nodeValue3298, Sparse.eval] using hc.symm

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

theorem sound3302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3302 node3302Labels = Sparse.eval nodeValue3302 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3302) = mixedMoment B node3302 node3302Labels := rfl
  simpa [nodeValue3302, Sparse.eval] using hc.symm

theorem sound3305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3305 node3305Labels = Sparse.eval nodeValue3305 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3305) = mixedMoment B node3305 node3305Labels := rfl
  simpa [nodeValue3305, Sparse.eval] using hc.symm

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

theorem zero3484 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3484 node3484Labels = 0 := by
  exact mixedMoment_order_one B hB node3484 node3484Labels 1
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

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3484 node3484Labels = Sparse.eval nodeValue3484 (mixedVector B) := by
  simpa only [nodeValue3484, Sparse.eval_nil] using zero3484 B _hB _hF

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

theorem sound3545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3545 node3545Labels = Sparse.eval nodeValue3545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3545) = mixedMoment B node3545 node3545Labels := rfl
  simpa [nodeValue3545, Sparse.eval] using hc.symm

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

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

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node626 node626Labels = Sparse.eval nodeValue626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 626) = mixedMoment B node626 node626Labels := rfl
  simpa [nodeValue626, Sparse.eval] using hc.symm

theorem sound633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node633 node633Labels = Sparse.eval nodeValue633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 633) = mixedMoment B node633 node633Labels := rfl
  simpa [nodeValue633, Sparse.eval] using hc.symm

theorem sound635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node635 node635Labels = Sparse.eval nodeValue635 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 635) = mixedMoment B node635 node635Labels := rfl
  simpa [nodeValue635, Sparse.eval] using hc.symm

theorem sound639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node639 node639Labels = Sparse.eval nodeValue639 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 639) = mixedMoment B node639 node639Labels := rfl
  simpa [nodeValue639, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources39
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1274 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1274 + difference 0 1) (sourceB1274 + difference 1 0) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1274 + difference 0 1) (sourceB1274 + difference 1 0) sourceC1274) = raw5152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5152; decide +kernel
    rw [ha]
    exact (canonical5152 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1274 + difference 0 2) (sourceB1274 + difference 2 0) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1274 + difference 0 2) (sourceB1274 + difference 2 0) sourceC1274) = raw5153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5153; decide +kernel
    rw [ha]
    exact (canonical5153 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1274 + difference 0 3) (sourceB1274 + difference 3 0) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1274 + difference 0 3) (sourceB1274 + difference 3 0) sourceC1274) = raw5154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5154; decide +kernel
    rw [ha]
    exact (canonical5154 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1274 + difference 0 4) (sourceB1274 + difference 4 0) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA1274 + difference 0 4) (sourceB1274 + difference 4 0) sourceC1274) = raw10311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw10311; decide +kernel
    rw [ha]
    exact (canonical10311 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1274 + difference 0 5) (sourceB1274 + difference 5 0) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA1274 + difference 0 5) (sourceB1274 + difference 5 0) sourceC1274) = raw5155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5155; decide +kernel
    rw [ha]
    exact (canonical5155 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1274 + difference 1 0) (sourceB1274 + difference 0 1) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA1274 + difference 1 0) (sourceB1274 + difference 0 1) sourceC1274) = raw20511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20511; decide +kernel
    rw [ha]
    exact (canonical20511 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1274 + difference 1 2) (sourceB1274 + difference 2 1) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1274 + difference 1 2) (sourceB1274 + difference 2 1) sourceC1274) = raw20512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20512; decide +kernel
    rw [ha]
    exact (canonical20512 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1274 + difference 1 3) (sourceB1274 + difference 3 1) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1274 + difference 1 3) (sourceB1274 + difference 3 1) sourceC1274) = raw20513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20513; decide +kernel
    rw [ha]
    exact (canonical20513 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1274 + difference 1 4) (sourceB1274 + difference 4 1) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1274 + difference 1 4) (sourceB1274 + difference 4 1) sourceC1274) = raw5136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5136; decide +kernel
    rw [ha]
    exact (canonical5136 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1274 + difference 1 5) (sourceB1274 + difference 5 1) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1274 + difference 1 5) (sourceB1274 + difference 5 1) sourceC1274) = raw10294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw10294; decide +kernel
    rw [ha]
    exact (canonical10294 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1274 + difference 2 0) (sourceB1274 + difference 0 2) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA1274 + difference 2 0) (sourceB1274 + difference 0 2) sourceC1274) = raw20514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20514; decide +kernel
    rw [ha]
    exact (canonical20514 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1274 + difference 2 1) (sourceB1274 + difference 1 2) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1274 + difference 2 1) (sourceB1274 + difference 1 2) sourceC1274) = raw20515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20515; decide +kernel
    rw [ha]
    exact (canonical20515 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1274 + difference 2 3) (sourceB1274 + difference 3 2) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1274 + difference 2 3) (sourceB1274 + difference 3 2) sourceC1274) = raw20516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20516; decide +kernel
    rw [ha]
    exact (canonical20516 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1274 + difference 2 4) (sourceB1274 + difference 4 2) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1274 + difference 2 4) (sourceB1274 + difference 4 2) sourceC1274) = raw5141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5141; decide +kernel
    rw [ha]
    exact (canonical5141 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1274 + difference 2 5) (sourceB1274 + difference 5 2) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1274 + difference 2 5) (sourceB1274 + difference 5 2) sourceC1274) = raw10298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw10298; decide +kernel
    rw [ha]
    exact (canonical10298 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1274 + difference 3 0) (sourceB1274 + difference 0 3) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA1274 + difference 3 0) (sourceB1274 + difference 0 3) sourceC1274) = raw20517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20517; decide +kernel
    rw [ha]
    exact (canonical20517 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1274 + difference 3 1) (sourceB1274 + difference 1 3) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1274 + difference 3 1) (sourceB1274 + difference 1 3) sourceC1274) = raw20518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20518; decide +kernel
    rw [ha]
    exact (canonical20518 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1274 + difference 3 2) (sourceB1274 + difference 2 3) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1274 + difference 3 2) (sourceB1274 + difference 2 3) sourceC1274) = raw20519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20519; decide +kernel
    rw [ha]
    exact (canonical20519 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1274 + difference 3 4) (sourceB1274 + difference 4 3) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1274 + difference 3 4) (sourceB1274 + difference 4 3) sourceC1274) = raw5146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5146; decide +kernel
    rw [ha]
    exact (canonical5146 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1274 + difference 3 5) (sourceB1274 + difference 5 3) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1274 + difference 3 5) (sourceB1274 + difference 5 3) sourceC1274) = raw10302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw10302; decide +kernel
    rw [ha]
    exact (canonical10302 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1274 + difference 4 0) (sourceB1274 + difference 0 4) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1531) := by
    have ha : (tripleCharges (sourceA1274 + difference 4 0) (sourceB1274 + difference 0 4) sourceC1274) = raw20520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20520; decide +kernel
    rw [ha]
    exact (canonical20520 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1274 + difference 4 1) (sourceB1274 + difference 1 4) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2258) := by
    have ha : (tripleCharges (sourceA1274 + difference 4 1) (sourceB1274 + difference 1 4) sourceC1274) = raw20521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20521; decide +kernel
    rw [ha]
    exact (canonical20521 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1274 + difference 4 2) (sourceB1274 + difference 2 4) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2258) := by
    have ha : (tripleCharges (sourceA1274 + difference 4 2) (sourceB1274 + difference 2 4) sourceC1274) = raw20522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20522; decide +kernel
    rw [ha]
    exact (canonical20522 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1274 + difference 4 3) (sourceB1274 + difference 3 4) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2258) := by
    have ha : (tripleCharges (sourceA1274 + difference 4 3) (sourceB1274 + difference 3 4) sourceC1274) = raw20523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20523; decide +kernel
    rw [ha]
    exact (canonical20523 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1274 + difference 4 5) (sourceB1274 + difference 5 4) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2780) := by
    have ha : (tripleCharges (sourceA1274 + difference 4 5) (sourceB1274 + difference 5 4) sourceC1274) = raw10306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw10306; decide +kernel
    rw [ha]
    exact (canonical10306 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1274 + difference 5 0) (sourceB1274 + difference 0 5) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1540) := by
    have ha : (tripleCharges (sourceA1274 + difference 5 0) (sourceB1274 + difference 0 5) sourceC1274) = raw19680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw19680; decide +kernel
    rw [ha]
    exact (canonical19680 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1274 + difference 5 1) (sourceB1274 + difference 1 5) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1274 + difference 5 1) (sourceB1274 + difference 1 5) sourceC1274) = raw19681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw19681; decide +kernel
    rw [ha]
    exact (canonical19681 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1274 + difference 5 2) (sourceB1274 + difference 2 5) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1274 + difference 5 2) (sourceB1274 + difference 2 5) sourceC1274) = raw19682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw19682; decide +kernel
    rw [ha]
    exact (canonical19682 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1274 + difference 5 3) (sourceB1274 + difference 3 5) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1274 + difference 5 3) (sourceB1274 + difference 3 5) sourceC1274) = raw19683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw19683; decide +kernel
    rw [ha]
    exact (canonical19683 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1274 + difference 5 4) (sourceB1274 + difference 4 5) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1274 + difference 5 4) (sourceB1274 + difference 4 5) sourceC1274) = raw5156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5156; decide +kernel
    rw [ha]
    exact (canonical5156 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1274 sourceB1274 sourceC1274
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1274, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1275 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1275 + difference 0 0) (sourceB1275 + difference 0 0) sourceC1275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA1275 + difference 0 0) (sourceB1275 + difference 0 0) sourceC1275) = raw5165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1275 sourceB1275 sourceC1275 difference raw5165; decide +kernel
    rw [ha]
    exact (canonical5165 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1275 + difference 1 0) (sourceB1275 + difference 0 1) sourceC1275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 639) := by
    have ha : (tripleCharges (sourceA1275 + difference 1 0) (sourceB1275 + difference 0 1) sourceC1275) = raw20524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1275 sourceB1275 sourceC1275 difference raw20524; decide +kernel
    rw [ha]
    exact (canonical20524 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1275 + difference 2 0) (sourceB1275 + difference 0 2) sourceC1275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 639) := by
    have ha : (tripleCharges (sourceA1275 + difference 2 0) (sourceB1275 + difference 0 2) sourceC1275) = raw20525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1275 sourceB1275 sourceC1275 difference raw20525; decide +kernel
    rw [ha]
    exact (canonical20525 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1275 + difference 3 0) (sourceB1275 + difference 0 3) sourceC1275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 639) := by
    have ha : (tripleCharges (sourceA1275 + difference 3 0) (sourceB1275 + difference 0 3) sourceC1275) = raw20526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1275 sourceB1275 sourceC1275 difference raw20526; decide +kernel
    rw [ha]
    exact (canonical20526 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1275 + difference 4 0) (sourceB1275 + difference 0 4) sourceC1275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 654) := by
    have ha : (tripleCharges (sourceA1275 + difference 4 0) (sourceB1275 + difference 0 4) sourceC1275) = raw20527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1275 sourceB1275 sourceC1275 difference raw20527; decide +kernel
    rw [ha]
    exact (canonical20527 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1275 + difference 5 0) (sourceB1275 + difference 0 5) sourceC1275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 643) := by
    have ha : (tripleCharges (sourceA1275 + difference 5 0) (sourceB1275 + difference 0 5) sourceC1275) = raw19692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1275 sourceB1275 sourceC1275 difference raw19692; decide +kernel
    rw [ha]
    exact (canonical19692 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1275 + sourceB1275) sourceC1275) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1275 + sourceB1275) sourceC1275) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1275 sourceB1275 sourceC1275 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1275 sourceB1275 sourceC1275
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1275, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1276 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1276 + difference 1 0) (sourceB1276 + difference 0 1) sourceC1276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 639) := by
    have ha : (tripleCharges (sourceA1276 + difference 1 0) (sourceB1276 + difference 0 1) sourceC1276) = raw20524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1276 sourceB1276 sourceC1276 difference raw20524; decide +kernel
    rw [ha]
    exact (canonical20524 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1276 + difference 1 1) (sourceB1276 + difference 1 1) sourceC1276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA1276 + difference 1 1) (sourceB1276 + difference 1 1) sourceC1276) = raw5165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1276 sourceB1276 sourceC1276 difference raw5165; decide +kernel
    rw [ha]
    exact (canonical5165 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1276 + difference 1 2) (sourceB1276 + difference 2 1) sourceC1276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1157) := by
    have ha : (tripleCharges (sourceA1276 + difference 1 2) (sourceB1276 + difference 2 1) sourceC1276) = raw20528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1276 sourceB1276 sourceC1276 difference raw20528; decide +kernel
    rw [ha]
    exact (canonical20528 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1276 + difference 1 3) (sourceB1276 + difference 3 1) sourceC1276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1157) := by
    have ha : (tripleCharges (sourceA1276 + difference 1 3) (sourceB1276 + difference 3 1) sourceC1276) = raw20529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1276 sourceB1276 sourceC1276 difference raw20529; decide +kernel
    rw [ha]
    exact (canonical20529 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1276 + difference 1 4) (sourceB1276 + difference 4 1) sourceC1276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1276 + difference 1 4) (sourceB1276 + difference 4 1) sourceC1276) = raw5162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1276 sourceB1276 sourceC1276 difference raw5162; decide +kernel
    rw [ha]
    exact (canonical5162 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1276 + difference 1 5) (sourceB1276 + difference 5 1) sourceC1276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1292) := by
    have ha : (tripleCharges (sourceA1276 + difference 1 5) (sourceB1276 + difference 5 1) sourceC1276) = raw20530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1276 sourceB1276 sourceC1276 difference raw20530; decide +kernel
    rw [ha]
    exact (canonical20530 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1276 + sourceB1276) sourceC1276) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1276 + sourceB1276) sourceC1276) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1276 sourceB1276 sourceC1276 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1276 sourceB1276 sourceC1276
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1276, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1277 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1277 + difference 0 1) (sourceB1277 + difference 1 0) sourceC1277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA1277 + difference 0 1) (sourceB1277 + difference 1 0) sourceC1277) = raw5175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1277 sourceB1277 sourceC1277 difference raw5175; decide +kernel
    rw [ha]
    exact (canonical5175 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1277 + difference 1 1) (sourceB1277 + difference 1 1) sourceC1277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA1277 + difference 1 1) (sourceB1277 + difference 1 1) sourceC1277) = raw5165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1277 sourceB1277 sourceC1277 difference raw5165; decide +kernel
    rw [ha]
    exact (canonical5165 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1277 + difference 2 1) (sourceB1277 + difference 1 2) sourceC1277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1157) := by
    have ha : (tripleCharges (sourceA1277 + difference 2 1) (sourceB1277 + difference 1 2) sourceC1277) = raw20531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1277 sourceB1277 sourceC1277 difference raw20531; decide +kernel
    rw [ha]
    exact (canonical20531 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1277 + difference 3 1) (sourceB1277 + difference 1 3) sourceC1277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1157) := by
    have ha : (tripleCharges (sourceA1277 + difference 3 1) (sourceB1277 + difference 1 3) sourceC1277) = raw20532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1277 sourceB1277 sourceC1277 difference raw20532; decide +kernel
    rw [ha]
    exact (canonical20532 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1277 + difference 4 1) (sourceB1277 + difference 1 4) sourceC1277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1174) := by
    have ha : (tripleCharges (sourceA1277 + difference 4 1) (sourceB1277 + difference 1 4) sourceC1277) = raw20533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1277 sourceB1277 sourceC1277 difference raw20533; decide +kernel
    rw [ha]
    exact (canonical20533 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1277 + difference 5 1) (sourceB1277 + difference 1 5) sourceC1277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 948) := by
    have ha : (tripleCharges (sourceA1277 + difference 5 1) (sourceB1277 + difference 1 5) sourceC1277) = raw19699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1277 sourceB1277 sourceC1277 difference raw19699; decide +kernel
    rw [ha]
    exact (canonical19699 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1277 + sourceB1277) sourceC1277) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1277 + sourceB1277) sourceC1277) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1277 sourceB1277 sourceC1277 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1277 sourceB1277 sourceC1277
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1277, Integer.Sparse.eval]
  linarith only [hs]

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

theorem sourceEq1283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1283 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1283 + difference 0 0) (sourceB1283 + difference 0 0) sourceC1283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1283 + difference 0 0) (sourceB1283 + difference 0 0) sourceC1283) = raw20642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1283 sourceB1283 sourceC1283 difference raw20642; decide +kernel
    rw [ha]
    exact (canonical20642 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1283 + difference 1 0) (sourceB1283 + difference 0 1) sourceC1283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1283 + difference 1 0) (sourceB1283 + difference 0 1) sourceC1283) = raw20643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1283 sourceB1283 sourceC1283 difference raw20643; decide +kernel
    rw [ha]
    exact (canonical20643 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1283 + difference 2 0) (sourceB1283 + difference 0 2) sourceC1283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1283 + difference 2 0) (sourceB1283 + difference 0 2) sourceC1283) = raw20644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1283 sourceB1283 sourceC1283 difference raw20644; decide +kernel
    rw [ha]
    exact (canonical20644 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1283 + difference 3 0) (sourceB1283 + difference 0 3) sourceC1283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1283 + difference 3 0) (sourceB1283 + difference 0 3) sourceC1283) = raw20645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1283 sourceB1283 sourceC1283 difference raw20645; decide +kernel
    rw [ha]
    exact (canonical20645 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1283 + difference 4 0) (sourceB1283 + difference 0 4) sourceC1283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1283 + difference 4 0) (sourceB1283 + difference 0 4) sourceC1283) = raw20480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1283 sourceB1283 sourceC1283 difference raw20480; decide +kernel
    rw [ha]
    exact (canonical20480 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1283 + difference 5 0) (sourceB1283 + difference 0 5) sourceC1283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1077) := by
    have ha : (tripleCharges (sourceA1283 + difference 5 0) (sourceB1283 + difference 0 5) sourceC1283) = raw20646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1283 sourceB1283 sourceC1283 difference raw20646; decide +kernel
    rw [ha]
    exact (canonical20646 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1283 + sourceB1283) sourceC1283) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1283 + sourceB1283) sourceC1283) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1283 sourceB1283 sourceC1283 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1283 sourceB1283 sourceC1283
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1283, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1284 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1284 + difference 0 0) (sourceB1284 + difference 0 0) sourceC1284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1289) := by
    have ha : (tripleCharges (sourceA1284 + difference 0 0) (sourceB1284 + difference 0 0) sourceC1284) = raw19844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1284 sourceB1284 sourceC1284 difference raw19844; decide +kernel
    rw [ha]
    exact (canonical19844 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1284 + difference 0 1) (sourceB1284 + difference 1 0) sourceC1284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1657) := by
    have ha : (tripleCharges (sourceA1284 + difference 0 1) (sourceB1284 + difference 1 0) sourceC1284) = raw20647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1284 sourceB1284 sourceC1284 difference raw20647; decide +kernel
    rw [ha]
    exact (canonical20647 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1284 + difference 0 2) (sourceB1284 + difference 2 0) sourceC1284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1657) := by
    have ha : (tripleCharges (sourceA1284 + difference 0 2) (sourceB1284 + difference 2 0) sourceC1284) = raw20648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1284 sourceB1284 sourceC1284 difference raw20648; decide +kernel
    rw [ha]
    exact (canonical20648 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1284 + difference 0 3) (sourceB1284 + difference 3 0) sourceC1284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1657) := by
    have ha : (tripleCharges (sourceA1284 + difference 0 3) (sourceB1284 + difference 3 0) sourceC1284) = raw20649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1284 sourceB1284 sourceC1284 difference raw20649; decide +kernel
    rw [ha]
    exact (canonical20649 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1284 + difference 0 4) (sourceB1284 + difference 4 0) sourceC1284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1284 + difference 0 4) (sourceB1284 + difference 4 0) sourceC1284) = raw19835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1284 sourceB1284 sourceC1284 difference raw19835; decide +kernel
    rw [ha]
    exact (canonical19835 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1284 + difference 0 5) (sourceB1284 + difference 5 0) sourceC1284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2780) := by
    have ha : (tripleCharges (sourceA1284 + difference 0 5) (sourceB1284 + difference 5 0) sourceC1284) = raw20650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1284 sourceB1284 sourceC1284 difference raw20650; decide +kernel
    rw [ha]
    exact (canonical20650 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1284 + sourceB1284) sourceC1284) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1284 + sourceB1284) sourceC1284) = raw19836 := by
      apply Matrix.ext; unfold doubleCharges sourceA1284 sourceB1284 sourceC1284 raw19836; decide +kernel
    rw [ha]
    exact (canonical19836 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1284 sourceB1284 sourceC1284
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1284, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1287 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1287 + difference 0 1) (sourceB1287 + difference 1 0) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1287 + difference 0 1) (sourceB1287 + difference 1 0) sourceC1287) = raw20702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20702; decide +kernel
    rw [ha]
    exact (canonical20702 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1287 + difference 0 2) (sourceB1287 + difference 2 0) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1287 + difference 0 2) (sourceB1287 + difference 2 0) sourceC1287) = raw20703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20703; decide +kernel
    rw [ha]
    exact (canonical20703 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1287 + difference 0 3) (sourceB1287 + difference 3 0) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3484) := by
    have ha : (tripleCharges (sourceA1287 + difference 0 3) (sourceB1287 + difference 3 0) sourceC1287) = raw20704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20704; decide +kernel
    rw [ha]
    exact (canonical20704 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1287 + difference 0 4) (sourceB1287 + difference 4 0) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA1287 + difference 0 4) (sourceB1287 + difference 4 0) sourceC1287) = raw20705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20705; decide +kernel
    rw [ha]
    exact (canonical20705 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1287 + difference 0 5) (sourceB1287 + difference 5 0) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA1287 + difference 0 5) (sourceB1287 + difference 5 0) sourceC1287) = raw20706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20706; decide +kernel
    rw [ha]
    exact (canonical20706 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1287 + difference 1 0) (sourceB1287 + difference 0 1) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA1287 + difference 1 0) (sourceB1287 + difference 0 1) sourceC1287) = raw20707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20707; decide +kernel
    rw [ha]
    exact (canonical20707 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1287 + difference 1 2) (sourceB1287 + difference 2 1) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA1287 + difference 1 2) (sourceB1287 + difference 2 1) sourceC1287) = raw20708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20708; decide +kernel
    rw [ha]
    exact (canonical20708 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1287 + difference 1 3) (sourceB1287 + difference 3 1) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3264) := by
    have ha : (tripleCharges (sourceA1287 + difference 1 3) (sourceB1287 + difference 3 1) sourceC1287) = raw20709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20709; decide +kernel
    rw [ha]
    exact (canonical20709 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1287 + difference 1 4) (sourceB1287 + difference 4 1) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1287 + difference 1 4) (sourceB1287 + difference 4 1) sourceC1287) = raw20710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20710; decide +kernel
    rw [ha]
    exact (canonical20710 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1287 + difference 1 5) (sourceB1287 + difference 5 1) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1287 + difference 1 5) (sourceB1287 + difference 5 1) sourceC1287) = raw20711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20711; decide +kernel
    rw [ha]
    exact (canonical20711 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1287 + difference 2 0) (sourceB1287 + difference 0 2) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA1287 + difference 2 0) (sourceB1287 + difference 0 2) sourceC1287) = raw20712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20712; decide +kernel
    rw [ha]
    exact (canonical20712 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1287 + difference 2 1) (sourceB1287 + difference 1 2) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA1287 + difference 2 1) (sourceB1287 + difference 1 2) sourceC1287) = raw20713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20713; decide +kernel
    rw [ha]
    exact (canonical20713 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1287 + difference 2 3) (sourceB1287 + difference 3 2) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3264) := by
    have ha : (tripleCharges (sourceA1287 + difference 2 3) (sourceB1287 + difference 3 2) sourceC1287) = raw20714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20714; decide +kernel
    rw [ha]
    exact (canonical20714 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1287 + difference 2 4) (sourceB1287 + difference 4 2) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1287 + difference 2 4) (sourceB1287 + difference 4 2) sourceC1287) = raw20715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20715; decide +kernel
    rw [ha]
    exact (canonical20715 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1287 + difference 2 5) (sourceB1287 + difference 5 2) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1287 + difference 2 5) (sourceB1287 + difference 5 2) sourceC1287) = raw20716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20716; decide +kernel
    rw [ha]
    exact (canonical20716 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1287 + difference 3 0) (sourceB1287 + difference 0 3) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA1287 + difference 3 0) (sourceB1287 + difference 0 3) sourceC1287) = raw20717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20717; decide +kernel
    rw [ha]
    exact (canonical20717 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1287 + difference 3 1) (sourceB1287 + difference 1 3) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA1287 + difference 3 1) (sourceB1287 + difference 1 3) sourceC1287) = raw20718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20718; decide +kernel
    rw [ha]
    exact (canonical20718 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1287 + difference 3 2) (sourceB1287 + difference 2 3) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA1287 + difference 3 2) (sourceB1287 + difference 2 3) sourceC1287) = raw20719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20719; decide +kernel
    rw [ha]
    exact (canonical20719 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1287 + difference 3 4) (sourceB1287 + difference 4 3) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1287 + difference 3 4) (sourceB1287 + difference 4 3) sourceC1287) = raw20720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20720; decide +kernel
    rw [ha]
    exact (canonical20720 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1287 + difference 3 5) (sourceB1287 + difference 5 3) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1287 + difference 3 5) (sourceB1287 + difference 5 3) sourceC1287) = raw20721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20721; decide +kernel
    rw [ha]
    exact (canonical20721 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1287 + difference 4 0) (sourceB1287 + difference 0 4) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA1287 + difference 4 0) (sourceB1287 + difference 0 4) sourceC1287) = raw20722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20722; decide +kernel
    rw [ha]
    exact (canonical20722 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1287 + difference 4 1) (sourceB1287 + difference 1 4) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA1287 + difference 4 1) (sourceB1287 + difference 1 4) sourceC1287) = raw20723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20723; decide +kernel
    rw [ha]
    exact (canonical20723 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1287 + difference 4 2) (sourceB1287 + difference 2 4) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA1287 + difference 4 2) (sourceB1287 + difference 2 4) sourceC1287) = raw20724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20724; decide +kernel
    rw [ha]
    exact (canonical20724 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1287 + difference 4 3) (sourceB1287 + difference 3 4) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA1287 + difference 4 3) (sourceB1287 + difference 3 4) sourceC1287) = raw20725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20725; decide +kernel
    rw [ha]
    exact (canonical20725 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1287 + difference 4 5) (sourceB1287 + difference 5 4) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1287 + difference 4 5) (sourceB1287 + difference 5 4) sourceC1287) = raw20726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20726; decide +kernel
    rw [ha]
    exact (canonical20726 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1287 + difference 5 0) (sourceB1287 + difference 0 5) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA1287 + difference 5 0) (sourceB1287 + difference 0 5) sourceC1287) = raw20727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20727; decide +kernel
    rw [ha]
    exact (canonical20727 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1287 + difference 5 1) (sourceB1287 + difference 1 5) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3262) := by
    have ha : (tripleCharges (sourceA1287 + difference 5 1) (sourceB1287 + difference 1 5) sourceC1287) = raw20728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20728; decide +kernel
    rw [ha]
    exact (canonical20728 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1287 + difference 5 2) (sourceB1287 + difference 2 5) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3262) := by
    have ha : (tripleCharges (sourceA1287 + difference 5 2) (sourceB1287 + difference 2 5) sourceC1287) = raw20729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20729; decide +kernel
    rw [ha]
    exact (canonical20729 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1287 + difference 5 3) (sourceB1287 + difference 3 5) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3275) := by
    have ha : (tripleCharges (sourceA1287 + difference 5 3) (sourceB1287 + difference 3 5) sourceC1287) = raw20730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20730; decide +kernel
    rw [ha]
    exact (canonical20730 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1287 + difference 5 4) (sourceB1287 + difference 4 5) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3298) := by
    have ha : (tripleCharges (sourceA1287 + difference 5 4) (sourceB1287 + difference 4 5) sourceC1287) = raw20731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20731; decide +kernel
    rw [ha]
    exact (canonical20731 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1287 sourceB1287 sourceC1287
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1287, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1288 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1288 + difference 0 0) (sourceB1288 + difference 0 0) sourceC1288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1288 + difference 0 0) (sourceB1288 + difference 0 0) sourceC1288) = raw20732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1288 sourceB1288 sourceC1288 difference raw20732; decide +kernel
    rw [ha]
    exact (canonical20732 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1288 + difference 1 0) (sourceB1288 + difference 0 1) sourceC1288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 626) := by
    have ha : (tripleCharges (sourceA1288 + difference 1 0) (sourceB1288 + difference 0 1) sourceC1288) = raw20733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1288 sourceB1288 sourceC1288 difference raw20733; decide +kernel
    rw [ha]
    exact (canonical20733 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1288 + difference 2 0) (sourceB1288 + difference 0 2) sourceC1288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 626) := by
    have ha : (tripleCharges (sourceA1288 + difference 2 0) (sourceB1288 + difference 0 2) sourceC1288) = raw20734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1288 sourceB1288 sourceC1288 difference raw20734; decide +kernel
    rw [ha]
    exact (canonical20734 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1288 + difference 3 0) (sourceB1288 + difference 0 3) sourceC1288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 641) := by
    have ha : (tripleCharges (sourceA1288 + difference 3 0) (sourceB1288 + difference 0 3) sourceC1288) = raw20735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1288 sourceB1288 sourceC1288 difference raw20735; decide +kernel
    rw [ha]
    exact (canonical20735 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1288 + difference 4 0) (sourceB1288 + difference 0 4) sourceC1288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 635) := by
    have ha : (tripleCharges (sourceA1288 + difference 4 0) (sourceB1288 + difference 0 4) sourceC1288) = raw20736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1288 sourceB1288 sourceC1288 difference raw20736; decide +kernel
    rw [ha]
    exact (canonical20736 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1288 + difference 5 0) (sourceB1288 + difference 0 5) sourceC1288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 633) := by
    have ha : (tripleCharges (sourceA1288 + difference 5 0) (sourceB1288 + difference 0 5) sourceC1288) = raw20737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1288 sourceB1288 sourceC1288 difference raw20737; decide +kernel
    rw [ha]
    exact (canonical20737 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1288 + sourceB1288) sourceC1288) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1288 + sourceB1288) sourceC1288) = raw20738 := by
      apply Matrix.ext; unfold doubleCharges sourceA1288 sourceB1288 sourceC1288 raw20738; decide +kernel
    rw [ha]
    exact (canonical20738 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1288 sourceB1288 sourceC1288
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1288, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1289 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1289 + difference 0 1) (sourceB1289 + difference 1 0) sourceC1289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1289 + difference 0 1) (sourceB1289 + difference 1 0) sourceC1289) = raw20739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1289 sourceB1289 sourceC1289 difference raw20739; decide +kernel
    rw [ha]
    exact (canonical20739 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1289 + difference 1 1) (sourceB1289 + difference 1 1) sourceC1289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1289 + difference 1 1) (sourceB1289 + difference 1 1) sourceC1289) = raw20732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1289 sourceB1289 sourceC1289 difference raw20732; decide +kernel
    rw [ha]
    exact (canonical20732 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1289 + difference 2 1) (sourceB1289 + difference 1 2) sourceC1289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1148) := by
    have ha : (tripleCharges (sourceA1289 + difference 2 1) (sourceB1289 + difference 1 2) sourceC1289) = raw20740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1289 sourceB1289 sourceC1289 difference raw20740; decide +kernel
    rw [ha]
    exact (canonical20740 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1289 + difference 3 1) (sourceB1289 + difference 1 3) sourceC1289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1159) := by
    have ha : (tripleCharges (sourceA1289 + difference 3 1) (sourceB1289 + difference 1 3) sourceC1289) = raw20741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1289 sourceB1289 sourceC1289 difference raw20741; decide +kernel
    rw [ha]
    exact (canonical20741 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1289 + difference 4 1) (sourceB1289 + difference 1 4) sourceC1289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1154) := by
    have ha : (tripleCharges (sourceA1289 + difference 4 1) (sourceB1289 + difference 1 4) sourceC1289) = raw20742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1289 sourceB1289 sourceC1289 difference raw20742; decide +kernel
    rw [ha]
    exact (canonical20742 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1289 + difference 5 1) (sourceB1289 + difference 1 5) sourceC1289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1115) := by
    have ha : (tripleCharges (sourceA1289 + difference 5 1) (sourceB1289 + difference 1 5) sourceC1289) = raw20743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1289 sourceB1289 sourceC1289 difference raw20743; decide +kernel
    rw [ha]
    exact (canonical20743 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1289 + sourceB1289) sourceC1289) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1289 + sourceB1289) sourceC1289) = raw20738 := by
      apply Matrix.ext; unfold doubleCharges sourceA1289 sourceB1289 sourceC1289 raw20738; decide +kernel
    rw [ha]
    exact (canonical20738 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1289 sourceB1289 sourceC1289
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1289, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1290 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1290 + difference 0 3) (sourceB1290 + difference 3 0) sourceC1290) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2517) := by
    have ha : (tripleCharges (sourceA1290 + difference 0 3) (sourceB1290 + difference 3 0) sourceC1290) = raw20744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1290 sourceB1290 sourceC1290 difference raw20744; decide +kernel
    rw [ha]
    exact (canonical20744 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1290 + difference 1 3) (sourceB1290 + difference 3 1) sourceC1290) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1290 + difference 1 3) (sourceB1290 + difference 3 1) sourceC1290) = raw20745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1290 sourceB1290 sourceC1290 difference raw20745; decide +kernel
    rw [ha]
    exact (canonical20745 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1290 + difference 2 3) (sourceB1290 + difference 3 2) sourceC1290) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1290 + difference 2 3) (sourceB1290 + difference 3 2) sourceC1290) = raw20746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1290 sourceB1290 sourceC1290 difference raw20746; decide +kernel
    rw [ha]
    exact (canonical20746 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1290 + difference 3 3) (sourceB1290 + difference 3 3) sourceC1290) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1290 + difference 3 3) (sourceB1290 + difference 3 3) sourceC1290) = raw20732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1290 sourceB1290 sourceC1290 difference raw20732; decide +kernel
    rw [ha]
    exact (canonical20732 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1290 + difference 4 3) (sourceB1290 + difference 3 4) sourceC1290) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA1290 + difference 4 3) (sourceB1290 + difference 3 4) sourceC1290) = raw20747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1290 sourceB1290 sourceC1290 difference raw20747; decide +kernel
    rw [ha]
    exact (canonical20747 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1290 + difference 5 3) (sourceB1290 + difference 3 5) sourceC1290) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1290 + difference 5 3) (sourceB1290 + difference 3 5) sourceC1290) = raw20748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1290 sourceB1290 sourceC1290 difference raw20748; decide +kernel
    rw [ha]
    exact (canonical20748 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1290 + sourceB1290) sourceC1290) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1290 + sourceB1290) sourceC1290) = raw20738 := by
      apply Matrix.ext; unfold doubleCharges sourceA1290 sourceB1290 sourceC1290 raw20738; decide +kernel
    rw [ha]
    exact (canonical20738 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1290 sourceB1290 sourceC1290
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1290, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1104 : Integer.Sparse.reindex keyMap MixedData.row1104 = numericRow1104 := by decide +kernel

theorem numericCheck1104 (x : Master → ℝ) : Integer.Sparse.eval numericRow1104 x =
    (1 : ℝ) * reducedSource1104 x := by
  norm_num [numericRow1104, reducedSource1104, Integer.Sparse.eval, Sparse.eval, nodeValue1530, nodeValue1531, nodeValue1540, nodeValue1722, nodeValue1752, nodeValue2200, nodeValue2226, nodeValue2258, nodeValue2261, nodeValue2292, nodeValue2737, nodeValue2780, nodeValue2783]

theorem reindexCheck1105 : Integer.Sparse.reindex keyMap MixedData.row1105 = numericRow1105 := by decide +kernel

theorem numericCheck1105 (x : Master → ℝ) : Integer.Sparse.eval numericRow1105 x =
    (1 : ℝ) * reducedSource1105 x := by
  norm_num [numericRow1105, reducedSource1105, Integer.Sparse.eval, Sparse.eval, nodeValue639, nodeValue643, nodeValue654, nodeValue1297, nodeValue4084]

theorem reindexCheck1106 : Integer.Sparse.reindex keyMap MixedData.row1106 = numericRow1106 := by decide +kernel

theorem numericCheck1106 (x : Master → ℝ) : Integer.Sparse.eval numericRow1106 x =
    (1 : ℝ) * reducedSource1106 x := by
  norm_num [numericRow1106, reducedSource1106, Integer.Sparse.eval, Sparse.eval, nodeValue639, nodeValue1157, nodeValue1239, nodeValue1292, nodeValue1297, nodeValue4084]

theorem reindexCheck1107 : Integer.Sparse.reindex keyMap MixedData.row1107 = numericRow1107 := by decide +kernel

theorem numericCheck1107 (x : Master → ℝ) : Integer.Sparse.eval numericRow1107 x =
    (1 : ℝ) * reducedSource1107 x := by
  norm_num [numericRow1107, reducedSource1107, Integer.Sparse.eval, Sparse.eval, nodeValue948, nodeValue1157, nodeValue1174, nodeValue1297, nodeValue2109, nodeValue4084]

theorem reindexCheck1112 : Integer.Sparse.reindex keyMap MixedData.row1112 = numericRow1112 := by decide +kernel

theorem numericCheck1112 (x : Master → ℝ) : Integer.Sparse.eval numericRow1112 x =
    (1 : ℝ) * reducedSource1112 x := by
  norm_num [numericRow1112, reducedSource1112, Integer.Sparse.eval, Sparse.eval, nodeValue1077, nodeValue1647, nodeValue1730, nodeValue2289, nodeValue4070]

theorem reindexCheck1113 : Integer.Sparse.reindex keyMap MixedData.row1113 = numericRow1113 := by decide +kernel

theorem numericCheck1113 (x : Master → ℝ) : Integer.Sparse.eval numericRow1113 x =
    (1 : ℝ) * reducedSource1113 x := by
  norm_num [numericRow1113, reducedSource1113, Integer.Sparse.eval, Sparse.eval, nodeValue1289, nodeValue1657, nodeValue1741, nodeValue2780, nodeValue4071]

theorem reindexCheck1116 : Integer.Sparse.reindex keyMap MixedData.row1116 = numericRow1116 := by decide +kernel

theorem numericCheck1116 (x : Master → ℝ) : Integer.Sparse.eval numericRow1116 x =
    (1 : ℝ) * reducedSource1116 x := by
  norm_num [numericRow1116, reducedSource1116, Integer.Sparse.eval, Sparse.eval, nodeValue1514, nodeValue1516, nodeValue1520, nodeValue1533, nodeValue3260, nodeValue3262, nodeValue3264, nodeValue3266, nodeValue3272, nodeValue3275, nodeValue3276, nodeValue3291, nodeValue3293, nodeValue3298, nodeValue3301, nodeValue3302, nodeValue3305, nodeValue3468, nodeValue3484, nodeValue3545, nodeValue3547]

theorem reindexCheck1117 : Integer.Sparse.reindex keyMap MixedData.row1117 = numericRow1117 := by decide +kernel

theorem numericCheck1117 (x : Master → ℝ) : Integer.Sparse.eval numericRow1117 x =
    (1 : ℝ) * reducedSource1117 x := by
  norm_num [numericRow1117, reducedSource1117, Integer.Sparse.eval, Sparse.eval, nodeValue626, nodeValue633, nodeValue635, nodeValue641, nodeValue1242, nodeValue4092]

theorem reindexCheck1118 : Integer.Sparse.reindex keyMap MixedData.row1118 = numericRow1118 := by decide +kernel

theorem numericCheck1118 (x : Master → ℝ) : Integer.Sparse.eval numericRow1118 x =
    (1 : ℝ) * reducedSource1118 x := by
  norm_num [numericRow1118, reducedSource1118, Integer.Sparse.eval, Sparse.eval, nodeValue1115, nodeValue1148, nodeValue1154, nodeValue1159, nodeValue1242, nodeValue2482, nodeValue4092]

theorem reindexCheck1119 : Integer.Sparse.reindex keyMap MixedData.row1119 = numericRow1119 := by decide +kernel

theorem numericCheck1119 (x : Master → ℝ) : Integer.Sparse.eval numericRow1119 x =
    (1 : ℝ) * reducedSource1119 x := by
  norm_num [numericRow1119, reducedSource1119, Integer.Sparse.eval, Sparse.eval, nodeValue1131, nodeValue1140, nodeValue1144, nodeValue1242, nodeValue2517, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1104 (mixedVector B) = 0 := by
  have h1530 : mixedVector B (Sum.inr 1530) = Sparse.eval nodeValue1530 (mixedVector B) := by
    change mixedMoment B node1530 node1530Labels = _
    exact sound1530 B hB hF
  have h1531 : mixedVector B (Sum.inr 1531) = Sparse.eval nodeValue1531 (mixedVector B) := by
    change mixedMoment B node1531 node1531Labels = _
    exact sound1531 B hB hF
  have h1540 : mixedVector B (Sum.inr 1540) = Sparse.eval nodeValue1540 (mixedVector B) := by
    change mixedMoment B node1540 node1540Labels = _
    exact sound1540 B hB hF
  have h1722 : mixedVector B (Sum.inr 1722) = Sparse.eval nodeValue1722 (mixedVector B) := by
    change mixedMoment B node1722 node1722Labels = _
    exact sound1722 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h2200 : mixedVector B (Sum.inr 2200) = Sparse.eval nodeValue2200 (mixedVector B) := by
    change mixedMoment B node2200 node2200Labels = _
    exact sound2200 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2258 : mixedVector B (Sum.inr 2258) = Sparse.eval nodeValue2258 (mixedVector B) := by
    change mixedMoment B node2258 node2258Labels = _
    exact sound2258 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h2780 : mixedVector B (Sum.inr 2780) = Sparse.eval nodeValue2780 (mixedVector B) := by
    change mixedMoment B node2780 node2780Labels = _
    exact sound2780 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  simpa only [sourceForm1274, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1530, h1531, h1540, h1722, h1752, h2200, h2226, h2258, h2261, h2292, h2737, h2780, h2783, reducedSource1104] using sourceEq1274 B hB

theorem rowSound1104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1104 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1104, numericCheck1104, reducedZero1104 B hB hF, mul_zero]

theorem reducedZero1105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1105 (mixedVector B) = 0 := by
  have h639 : mixedVector B (Sum.inr 639) = Sparse.eval nodeValue639 (mixedVector B) := by
    change mixedMoment B node639 node639Labels = _
    exact sound639 B hB hF
  have h643 : mixedVector B (Sum.inr 643) = Sparse.eval nodeValue643 (mixedVector B) := by
    change mixedMoment B node643 node643Labels = _
    exact sound643 B hB hF
  have h654 : mixedVector B (Sum.inr 654) = Sparse.eval nodeValue654 (mixedVector B) := by
    change mixedMoment B node654 node654Labels = _
    exact sound654 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1275, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h639, h643, h654, h1297, h4084, reducedSource1105] using sourceEq1275 B hB

theorem rowSound1105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1105 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1105, numericCheck1105, reducedZero1105 B hB hF, mul_zero]

theorem reducedZero1106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1106 (mixedVector B) = 0 := by
  have h639 : mixedVector B (Sum.inr 639) = Sparse.eval nodeValue639 (mixedVector B) := by
    change mixedMoment B node639 node639Labels = _
    exact sound639 B hB hF
  have h1157 : mixedVector B (Sum.inr 1157) = Sparse.eval nodeValue1157 (mixedVector B) := by
    change mixedMoment B node1157 node1157Labels = _
    exact sound1157 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h1292 : mixedVector B (Sum.inr 1292) = Sparse.eval nodeValue1292 (mixedVector B) := by
    change mixedMoment B node1292 node1292Labels = _
    exact sound1292 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1276, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h639, h1157, h1239, h1292, h1297, h4084, reducedSource1106] using sourceEq1276 B hB

theorem rowSound1106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1106 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1106, numericCheck1106, reducedZero1106 B hB hF, mul_zero]

theorem reducedZero1107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1107 (mixedVector B) = 0 := by
  have h948 : mixedVector B (Sum.inr 948) = Sparse.eval nodeValue948 (mixedVector B) := by
    change mixedMoment B node948 node948Labels = _
    exact sound948 B hB hF
  have h1157 : mixedVector B (Sum.inr 1157) = Sparse.eval nodeValue1157 (mixedVector B) := by
    change mixedMoment B node1157 node1157Labels = _
    exact sound1157 B hB hF
  have h1174 : mixedVector B (Sum.inr 1174) = Sparse.eval nodeValue1174 (mixedVector B) := by
    change mixedMoment B node1174 node1174Labels = _
    exact sound1174 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1277, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h948, h1157, h1174, h1297, h2109, h4084, reducedSource1107] using sourceEq1277 B hB

theorem rowSound1107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1107 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1107, numericCheck1107, reducedZero1107 B hB hF, mul_zero]

theorem reducedZero1112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1112 (mixedVector B) = 0 := by
  have h1077 : mixedVector B (Sum.inr 1077) = Sparse.eval nodeValue1077 (mixedVector B) := by
    change mixedMoment B node1077 node1077Labels = _
    exact sound1077 B hB hF
  have h1647 : mixedVector B (Sum.inr 1647) = Sparse.eval nodeValue1647 (mixedVector B) := by
    change mixedMoment B node1647 node1647Labels = _
    exact sound1647 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1283, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1077, h1647, h1730, h2289, h4070, reducedSource1112] using sourceEq1283 B hB

theorem rowSound1112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1112 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1112, numericCheck1112, reducedZero1112 B hB hF, mul_zero]

theorem reducedZero1113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1113 (mixedVector B) = 0 := by
  have h1289 : mixedVector B (Sum.inr 1289) = Sparse.eval nodeValue1289 (mixedVector B) := by
    change mixedMoment B node1289 node1289Labels = _
    exact sound1289 B hB hF
  have h1657 : mixedVector B (Sum.inr 1657) = Sparse.eval nodeValue1657 (mixedVector B) := by
    change mixedMoment B node1657 node1657Labels = _
    exact sound1657 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h2780 : mixedVector B (Sum.inr 2780) = Sparse.eval nodeValue2780 (mixedVector B) := by
    change mixedMoment B node2780 node2780Labels = _
    exact sound2780 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1284, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1289, h1657, h1741, h2780, h4071, reducedSource1113] using sourceEq1284 B hB

theorem rowSound1113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1113 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1113, numericCheck1113, reducedZero1113 B hB hF, mul_zero]

theorem reducedZero1116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1116 (mixedVector B) = 0 := by
  have h1514 : mixedVector B (Sum.inr 1514) = Sparse.eval nodeValue1514 (mixedVector B) := by
    change mixedMoment B node1514 node1514Labels = _
    exact sound1514 B hB hF
  have h1516 : mixedVector B (Sum.inr 1516) = Sparse.eval nodeValue1516 (mixedVector B) := by
    change mixedMoment B node1516 node1516Labels = _
    exact sound1516 B hB hF
  have h1520 : mixedVector B (Sum.inr 1520) = Sparse.eval nodeValue1520 (mixedVector B) := by
    change mixedMoment B node1520 node1520Labels = _
    exact sound1520 B hB hF
  have h1533 : mixedVector B (Sum.inr 1533) = Sparse.eval nodeValue1533 (mixedVector B) := by
    change mixedMoment B node1533 node1533Labels = _
    exact sound1533 B hB hF
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
  have h3272 : mixedVector B (Sum.inr 3272) = Sparse.eval nodeValue3272 (mixedVector B) := by
    change mixedMoment B node3272 node3272Labels = _
    exact sound3272 B hB hF
  have h3275 : mixedVector B (Sum.inr 3275) = Sparse.eval nodeValue3275 (mixedVector B) := by
    change mixedMoment B node3275 node3275Labels = _
    exact sound3275 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3298 : mixedVector B (Sum.inr 3298) = Sparse.eval nodeValue3298 (mixedVector B) := by
    change mixedMoment B node3298 node3298Labels = _
    exact sound3298 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3484 : mixedVector B (Sum.inr 3484) = Sparse.eval nodeValue3484 (mixedVector B) := by
    change mixedMoment B node3484 node3484Labels = _
    exact sound3484 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  simpa only [sourceForm1287, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1514, h1516, h1520, h1533, h3260, h3262, h3264, h3266, h3272, h3275, h3276, h3291, h3293, h3298, h3301, h3302, h3305, h3468, h3484, h3545, h3547, reducedSource1116] using sourceEq1287 B hB

theorem rowSound1116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1116 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1116, numericCheck1116, reducedZero1116 B hB hF, mul_zero]

theorem reducedZero1117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1117 (mixedVector B) = 0 := by
  have h626 : mixedVector B (Sum.inr 626) = Sparse.eval nodeValue626 (mixedVector B) := by
    change mixedMoment B node626 node626Labels = _
    exact sound626 B hB hF
  have h633 : mixedVector B (Sum.inr 633) = Sparse.eval nodeValue633 (mixedVector B) := by
    change mixedMoment B node633 node633Labels = _
    exact sound633 B hB hF
  have h635 : mixedVector B (Sum.inr 635) = Sparse.eval nodeValue635 (mixedVector B) := by
    change mixedMoment B node635 node635Labels = _
    exact sound635 B hB hF
  have h641 : mixedVector B (Sum.inr 641) = Sparse.eval nodeValue641 (mixedVector B) := by
    change mixedMoment B node641 node641Labels = _
    exact sound641 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1288, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h626, h633, h635, h641, h1242, h4092, reducedSource1117] using sourceEq1288 B hB

theorem rowSound1117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1117 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1117, numericCheck1117, reducedZero1117 B hB hF, mul_zero]

theorem reducedZero1118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1118 (mixedVector B) = 0 := by
  have h1115 : mixedVector B (Sum.inr 1115) = Sparse.eval nodeValue1115 (mixedVector B) := by
    change mixedMoment B node1115 node1115Labels = _
    exact sound1115 B hB hF
  have h1148 : mixedVector B (Sum.inr 1148) = Sparse.eval nodeValue1148 (mixedVector B) := by
    change mixedMoment B node1148 node1148Labels = _
    exact sound1148 B hB hF
  have h1154 : mixedVector B (Sum.inr 1154) = Sparse.eval nodeValue1154 (mixedVector B) := by
    change mixedMoment B node1154 node1154Labels = _
    exact sound1154 B hB hF
  have h1159 : mixedVector B (Sum.inr 1159) = Sparse.eval nodeValue1159 (mixedVector B) := by
    change mixedMoment B node1159 node1159Labels = _
    exact sound1159 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1289, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1115, h1148, h1154, h1159, h1242, h2482, h4092, reducedSource1118] using sourceEq1289 B hB

theorem rowSound1118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1118 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1118, numericCheck1118, reducedZero1118 B hB hF, mul_zero]

theorem reducedZero1119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1119 (mixedVector B) = 0 := by
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h1140 : mixedVector B (Sum.inr 1140) = Sparse.eval nodeValue1140 (mixedVector B) := by
    change mixedMoment B node1140 node1140Labels = _
    exact sound1140 B hB hF
  have h1144 : mixedVector B (Sum.inr 1144) = Sparse.eval nodeValue1144 (mixedVector B) := by
    change mixedMoment B node1144 node1144Labels = _
    exact sound1144 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h2517 : mixedVector B (Sum.inr 2517) = Sparse.eval nodeValue2517 (mixedVector B) := by
    change mixedMoment B node2517 node2517Labels = _
    exact sound2517 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1290, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1131, h1140, h1144, h1242, h2517, h4092, reducedSource1119] using sourceEq1290 B hB

theorem rowSound1119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1119 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1119, numericCheck1119, reducedZero1119 B hB hF, mul_zero]

theorem sourceRowsAt1104 : MixedData.sourceRows (1104 : Fin 2425) =
    MixedData.row1104 := by decide +kernel

theorem sourceRowsAt1105 : MixedData.sourceRows (1105 : Fin 2425) =
    MixedData.row1105 := by decide +kernel

theorem sourceRowsAt1106 : MixedData.sourceRows (1106 : Fin 2425) =
    MixedData.row1106 := by decide +kernel

theorem sourceRowsAt1107 : MixedData.sourceRows (1107 : Fin 2425) =
    MixedData.row1107 := by decide +kernel

theorem sourceRowsAt1108 : MixedData.sourceRows (1108 : Fin 2425) =
    MixedData.row1108 := by decide +kernel

theorem sourceRowsAt1109 : MixedData.sourceRows (1109 : Fin 2425) =
    MixedData.row1109 := by decide +kernel

theorem sourceRowsAt1110 : MixedData.sourceRows (1110 : Fin 2425) =
    MixedData.row1110 := by decide +kernel

theorem sourceRowsAt1111 : MixedData.sourceRows (1111 : Fin 2425) =
    MixedData.row1111 := by decide +kernel

theorem sourceRowsAt1112 : MixedData.sourceRows (1112 : Fin 2425) =
    MixedData.row1112 := by decide +kernel

theorem sourceRowsAt1113 : MixedData.sourceRows (1113 : Fin 2425) =
    MixedData.row1113 := by decide +kernel

theorem sourceRowsAt1114 : MixedData.sourceRows (1114 : Fin 2425) =
    MixedData.row1114 := by decide +kernel

theorem sourceRowsAt1115 : MixedData.sourceRows (1115 : Fin 2425) =
    MixedData.row1115 := by decide +kernel

theorem sourceRowsAt1116 : MixedData.sourceRows (1116 : Fin 2425) =
    MixedData.row1116 := by decide +kernel

theorem sourceRowsAt1117 : MixedData.sourceRows (1117 : Fin 2425) =
    MixedData.row1117 := by decide +kernel

theorem sourceRowsAt1118 : MixedData.sourceRows (1118 : Fin 2425) =
    MixedData.row1118 := by decide +kernel

theorem sourceRowsAt1119 : MixedData.sourceRows (1119 : Fin 2425) =
    MixedData.row1119 := by decide +kernel

theorem chunkSound69_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 69) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1104 ∨ k.val = 1105 ∨ k.val = 1106 ∨ k.val = 1107 ∨ k.val = 1108 ∨ k.val = 1109 ∨ k.val = 1110 ∨ k.val = 1111 ∨ k.val = 1112 ∨ k.val = 1113 ∨ k.val = 1114 ∨ k.val = 1115 ∨ k.val = 1116 ∨ k.val = 1117 ∨ k.val = 1118 ∨ k.val = 1119 := by omega
  rcases heq with h1104 | h1105 | h1106 | h1107 | h1108 | h1109 | h1110 | h1111 | h1112 | h1113 | h1114 | h1115 | h1116 | h1117 | h1118 | h1119
  · have he : k = (1104 : Fin 2425) := Fin.ext h1104
    subst k
    rw [sourceRowsAt1104]
    exact rowSound1104 B hB hF
  · have he : k = (1105 : Fin 2425) := Fin.ext h1105
    subst k
    rw [sourceRowsAt1105]
    exact rowSound1105 B hB hF
  · have he : k = (1106 : Fin 2425) := Fin.ext h1106
    subst k
    rw [sourceRowsAt1106]
    exact rowSound1106 B hB hF
  · have he : k = (1107 : Fin 2425) := Fin.ext h1107
    subst k
    rw [sourceRowsAt1107]
    exact rowSound1107 B hB hF
  · have he : k = (1108 : Fin 2425) := Fin.ext h1108
    subst k
    rw [sourceRowsAt1108]
    exact rowSound1108_e B hB hF
  · have he : k = (1109 : Fin 2425) := Fin.ext h1109
    subst k
    rw [sourceRowsAt1109]
    exact rowSound1109_e B hB hF
  · have he : k = (1110 : Fin 2425) := Fin.ext h1110
    subst k
    rw [sourceRowsAt1110]
    exact rowSound1110_e B hB hF
  · have he : k = (1111 : Fin 2425) := Fin.ext h1111
    subst k
    rw [sourceRowsAt1111]
    exact rowSound1111_e B hB hF
  · have he : k = (1112 : Fin 2425) := Fin.ext h1112
    subst k
    rw [sourceRowsAt1112]
    exact rowSound1112 B hB hF
  · have he : k = (1113 : Fin 2425) := Fin.ext h1113
    subst k
    rw [sourceRowsAt1113]
    exact rowSound1113 B hB hF
  · have he : k = (1114 : Fin 2425) := Fin.ext h1114
    subst k
    rw [sourceRowsAt1114]
    exact rowSound1114_e B hB hF
  · have he : k = (1115 : Fin 2425) := Fin.ext h1115
    subst k
    rw [sourceRowsAt1115]
    exact rowSound1115_e B hB hF
  · have he : k = (1116 : Fin 2425) := Fin.ext h1116
    subst k
    rw [sourceRowsAt1116]
    exact rowSound1116 B hB hF
  · have he : k = (1117 : Fin 2425) := Fin.ext h1117
    subst k
    rw [sourceRowsAt1117]
    exact rowSound1117 B hB hF
  · have he : k = (1118 : Fin 2425) := Fin.ext h1118
    subst k
    rw [sourceRowsAt1118]
    exact rowSound1118 B hB hF
  · have he : k = (1119 : Fin 2425) := Fin.ext h1119
    subst k
    rw [sourceRowsAt1119]
    exact rowSound1119 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69_e_oai
