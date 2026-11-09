-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:52:10.479786+00:00
-- url     : https://prove2.me/submissions/1916e101-7e69-477a-a5b6-caa900829124

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1734_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1738_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1739_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1740_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1743_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19917 raw19917Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19917 raw19917Labels = mixedMoment B raw19917step0 raw19917step0Labels := by
      have hz : ∀ j, raw19917 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19917step0 = (fun i j => raw19917 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19917step0 raw19917; decide +kernel
      have hl : raw19917step0Labels = raw19917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19917 raw19917Labels permutation520 hz
    mixedMoment B raw19917step0 raw19917step0Labels = mixedMoment B raw19917step1 raw19917step1Labels := by
      have hz : ∀ j, raw19917step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19917step1 = (fun i j => raw19917step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19917step1 raw19917step0; decide +kernel
      have hl : raw19917step1Labels = raw19917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19917step0 raw19917step0Labels permutation104 hz
    mixedMoment B raw19917step1 raw19917step1Labels = mixedMoment B raw19917step2 raw19917step2Labels := by
      have hz : ∀ j, raw19917step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19917step2 = (fun i j => raw19917step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19917step2 raw19917step1; decide +kernel
      have hl : raw19917step2Labels = raw19917step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19917step1 raw19917step1Labels permutation20 hz
    mixedMoment B raw19917step2 raw19917step2Labels = mixedMoment B raw19917step3 raw19917step3Labels := by
      have ha : raw19917step3 = (fun i j => raw19917step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19917step3 raw19917step2; decide +kernel
      have hl : raw19917step3Labels = raw19917step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19917step2 raw19917step2Labels permutation7 permutation7
    mixedMoment B raw19917step3 raw19917step3Labels = mixedMoment B raw19917step4 raw19917step4Labels := by
      have ha : raw19917step4 = raw19917step3 := by apply Matrix.ext; unfold raw19917step4 raw19917step3; decide +kernel
      have hl : raw19917step3Labels = labelEmbedding1 ∘ raw19917step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19917step3 raw19917step3Labels raw19917step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

theorem canonical19921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19921 raw19921Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw19921 raw19921Labels = mixedMoment B raw19921step0 raw19921step0Labels := by
      have hz : ∀ j, raw19921 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19921step0 = (fun i j => raw19921 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19921step0 raw19921; decide +kernel
      have hl : raw19921step0Labels = raw19921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19921 raw19921Labels permutation520 hz
    mixedMoment B raw19921step0 raw19921step0Labels = mixedMoment B raw19921step1 raw19921step1Labels := by
      have hz : ∀ j, raw19921step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19921step1 = (fun i j => raw19921step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19921step1 raw19921step0; decide +kernel
      have hl : raw19921step1Labels = raw19921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19921step0 raw19921step0Labels permutation104 hz
    mixedMoment B raw19921step1 raw19921step1Labels = mixedMoment B raw19921step2 raw19921step2Labels := by
      have hz : ∀ j, raw19921step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19921step2 = (fun i j => raw19921step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19921step2 raw19921step1; decide +kernel
      have hl : raw19921step2Labels = raw19921step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19921step1 raw19921step1Labels permutation20 hz
    mixedMoment B raw19921step2 raw19921step2Labels = mixedMoment B raw19921step3 raw19921step3Labels := by
      have hz : ∀ j, raw19921step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19921step3 = (fun i j => raw19921step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19921step3 raw19921step2; decide +kernel
      have hl : raw19921step3Labels = raw19921step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19921step2 raw19921step2Labels permutation4 hz
    mixedMoment B raw19921step3 raw19921step3Labels = mixedMoment B raw19921step4 raw19921step4Labels := by
      have hz : ∀ i, raw19921step3 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw19921step4 = (fun i j => raw19921step3 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw19921step4 raw19921step3; decide +kernel
      have hl : raw19921step4Labels = (fun j => raw19921step3Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19921step3 raw19921step3Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical19938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19938 raw19938Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19938 raw19938Labels = mixedMoment B raw19938step0 raw19938step0Labels := by
      have hz : ∀ j, raw19938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19938step0 = (fun i j => raw19938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19938step0 raw19938; decide +kernel
      have hl : raw19938step0Labels = raw19938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19938 raw19938Labels permutation434 hz
    mixedMoment B raw19938step0 raw19938step0Labels = mixedMoment B raw19938step1 raw19938step1Labels := by
      have hz : ∀ j, raw19938step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19938step1 = (fun i j => raw19938step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19938step1 raw19938step0; decide +kernel
      have hl : raw19938step1Labels = raw19938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19938step0 raw19938step0Labels permutation80 hz
    mixedMoment B raw19938step1 raw19938step1Labels = mixedMoment B raw19938step2 raw19938step2Labels := by
      have ha : raw19938step2 = (fun i j => raw19938step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19938step2 raw19938step1; decide +kernel
      have hl : raw19938step2Labels = raw19938step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19938step1 raw19938step1Labels permutation31 permutation7
    mixedMoment B raw19938step2 raw19938step2Labels = mixedMoment B raw19938step3 raw19938step3Labels := by
      have ha : raw19938step3 = raw19938step2 := by apply Matrix.ext; unfold raw19938step3 raw19938step2; decide +kernel
      have hl : raw19938step2Labels = labelEmbedding1 ∘ raw19938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19938step2 raw19938step2Labels raw19938step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19941 raw19941Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19941 raw19941Labels = mixedMoment B raw19941step0 raw19941step0Labels := by
      have hz : ∀ j, raw19941 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19941step0 = (fun i j => raw19941 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19941step0 raw19941; decide +kernel
      have hl : raw19941step0Labels = raw19941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19941 raw19941Labels permutation434 hz
    mixedMoment B raw19941step0 raw19941step0Labels = mixedMoment B raw19941step1 raw19941step1Labels := by
      have hz : ∀ j, raw19941step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19941step1 = (fun i j => raw19941step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19941step1 raw19941step0; decide +kernel
      have hl : raw19941step1Labels = raw19941step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19941step0 raw19941step0Labels permutation80 hz
    mixedMoment B raw19941step1 raw19941step1Labels = mixedMoment B raw19941step2 raw19941step2Labels := by
      have hz : ∀ j, raw19941step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19941step2 = (fun i j => raw19941step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19941step2 raw19941step1; decide +kernel
      have hl : raw19941step2Labels = raw19941step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19941step1 raw19941step1Labels permutation14 hz
    mixedMoment B raw19941step2 raw19941step2Labels = mixedMoment B raw19941step3 raw19941step3Labels := by
      have ha : raw19941step3 = (fun i j => raw19941step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19941step3 raw19941step2; decide +kernel
      have hl : raw19941step3Labels = raw19941step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19941step2 raw19941step2Labels permutation2 permutation7
    mixedMoment B raw19941step3 raw19941step3Labels = mixedMoment B raw19941step4 raw19941step4Labels := by
      have ha : raw19941step4 = -raw19941step3 := by apply Matrix.ext; change ∀ i j, raw19941step4 i j = -(raw19941step3 i j); unfold raw19941step4 raw19941step3; decide +kernel
      have hl : raw19941step4Labels = raw19941step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19941step4 raw19941step4Labels = mixedMoment B raw19941step5 raw19941step5Labels := by
      have ha : raw19941step5 = raw19941step4 := by apply Matrix.ext; unfold raw19941step5 raw19941step4; decide +kernel
      have hl : raw19941step4Labels = labelEmbedding1 ∘ raw19941step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19941step4 raw19941step4Labels raw19941step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical21854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21854 raw21854Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw21854 raw21854Labels = mixedMoment B raw21854step0 raw21854step0Labels := by
      have hz : ∀ j, raw21854 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21854step0 = (fun i j => raw21854 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21854step0 raw21854; decide +kernel
      have hl : raw21854step0Labels = raw21854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21854 raw21854Labels permutation434 hz
    mixedMoment B raw21854step0 raw21854step0Labels = mixedMoment B raw21854step1 raw21854step1Labels := by
      have hz : ∀ j, raw21854step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21854step1 = (fun i j => raw21854step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21854step1 raw21854step0; decide +kernel
      have hl : raw21854step1Labels = raw21854step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21854step0 raw21854step0Labels permutation56 hz
    mixedMoment B raw21854step1 raw21854step1Labels = mixedMoment B raw21854step2 raw21854step2Labels := by
      have ha : raw21854step2 = (fun i j => raw21854step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21854step2 raw21854step1; decide +kernel
      have hl : raw21854step2Labels = raw21854step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21854step1 raw21854step1Labels permutation31 permutation7
    mixedMoment B raw21854step2 raw21854step2Labels = mixedMoment B raw21854step3 raw21854step3Labels := by
      have ha : raw21854step3 = raw21854step2 := by apply Matrix.ext; unfold raw21854step3 raw21854step2; decide +kernel
      have hl : raw21854step2Labels = labelEmbedding1 ∘ raw21854step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21854step2 raw21854step2Labels raw21854step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

theorem canonical21855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21855 raw21855Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw21855 raw21855Labels = mixedMoment B raw21855step0 raw21855step0Labels := by
      have hz : ∀ j, raw21855 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21855step0 = (fun i j => raw21855 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21855step0 raw21855; decide +kernel
      have hl : raw21855step0Labels = raw21855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21855 raw21855Labels permutation346 hz
    mixedMoment B raw21855step0 raw21855step0Labels = mixedMoment B raw21855step1 raw21855step1Labels := by
      have hz : ∀ j, raw21855step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21855step1 = (fun i j => raw21855step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21855step1 raw21855step0; decide +kernel
      have hl : raw21855step1Labels = raw21855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21855step0 raw21855step0Labels permutation56 hz
    mixedMoment B raw21855step1 raw21855step1Labels = mixedMoment B raw21855step2 raw21855step2Labels := by
      have ha : raw21855step2 = (fun i j => raw21855step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21855step2 raw21855step1; decide +kernel
      have hl : raw21855step2Labels = raw21855step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21855step1 raw21855step1Labels permutation31 permutation7
    mixedMoment B raw21855step2 raw21855step2Labels = mixedMoment B raw21855step3 raw21855step3Labels := by
      have ha : raw21855step3 = raw21855step2 := by apply Matrix.ext; unfold raw21855step3 raw21855step2; decide +kernel
      have hl : raw21855step2Labels = labelEmbedding1 ∘ raw21855step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21855step2 raw21855step2Labels raw21855step3Labels labelEmbedding1 hl
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

theorem canonical21862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21862 raw21862Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21862 raw21862Labels = mixedMoment B raw21862step0 raw21862step0Labels := by
      have hz : ∀ j, raw21862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21862step0 = (fun i j => raw21862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21862step0 raw21862; decide +kernel
      have hl : raw21862step0Labels = raw21862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21862 raw21862Labels permutation434 hz
    mixedMoment B raw21862step0 raw21862step0Labels = mixedMoment B raw21862step1 raw21862step1Labels := by
      have ha : raw21862step1 = (fun i j => raw21862step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21862step1 raw21862step0; decide +kernel
      have hl : raw21862step1Labels = raw21862step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21862step0 raw21862step0Labels permutation32 permutation7
    mixedMoment B raw21862step1 raw21862step1Labels = mixedMoment B raw21862step2 raw21862step2Labels := by
      have ha : raw21862step2 = -raw21862step1 := by apply Matrix.ext; change ∀ i j, raw21862step2 i j = -(raw21862step1 i j); unfold raw21862step2 raw21862step1; decide +kernel
      have hl : raw21862step2Labels = raw21862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21862step2 raw21862step2Labels = mixedMoment B raw21862step3 raw21862step3Labels := by
      have ha : raw21862step3 = raw21862step2 := by apply Matrix.ext; unfold raw21862step3 raw21862step2; decide +kernel
      have hl : raw21862step2Labels = labelEmbedding1 ∘ raw21862step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21862step2 raw21862step2Labels raw21862step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

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

theorem canonical21870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21870 raw21870Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw21870 raw21870Labels = mixedMoment B raw21870step0 raw21870step0Labels := by
      have hz : ∀ j, raw21870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21870step0 = (fun i j => raw21870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21870step0 raw21870; decide +kernel
      have hl : raw21870step0Labels = raw21870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21870 raw21870Labels permutation434 hz
    mixedMoment B raw21870step0 raw21870step0Labels = mixedMoment B raw21870step1 raw21870step1Labels := by
      have hz : ∀ j, raw21870step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21870step1 = (fun i j => raw21870step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21870step1 raw21870step0; decide +kernel
      have hl : raw21870step1Labels = raw21870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21870step0 raw21870step0Labels permutation80 hz
    mixedMoment B raw21870step1 raw21870step1Labels = mixedMoment B raw21870step2 raw21870step2Labels := by
      have ha : raw21870step2 = (fun i j => raw21870step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21870step2 raw21870step1; decide +kernel
      have hl : raw21870step2Labels = raw21870step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21870step1 raw21870step1Labels permutation8 permutation7
    mixedMoment B raw21870step2 raw21870step2Labels = mixedMoment B raw21870step3 raw21870step3Labels := by
      have ha : raw21870step3 = -raw21870step2 := by apply Matrix.ext; change ∀ i j, raw21870step3 i j = -(raw21870step2 i j); unfold raw21870step3 raw21870step2; decide +kernel
      have hl : raw21870step3Labels = raw21870step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21870step3 raw21870step3Labels = mixedMoment B raw21870step4 raw21870step4Labels := by
      have ha : raw21870step4 = raw21870step3 := by apply Matrix.ext; unfold raw21870step4 raw21870step3; decide +kernel
      have hl : raw21870step3Labels = labelEmbedding1 ∘ raw21870step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21870step3 raw21870step3Labels raw21870step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22871 raw22871Labels = mixedMoment B node2541 node2541Labels := by
  calc
    _ = mixedMoment B node2541 node2541Labels := by rfl

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

theorem canonical25973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25973 raw25973Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw25973 raw25973Labels = mixedMoment B raw25973step0 raw25973step0Labels := by
      have hz : ∀ j, raw25973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25973step0 = (fun i j => raw25973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25973step0 raw25973; decide +kernel
      have hl : raw25973step0Labels = raw25973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25973 raw25973Labels permutation346 hz
    mixedMoment B raw25973step0 raw25973step0Labels = mixedMoment B raw25973step1 raw25973step1Labels := by
      have ha : raw25973step1 = (fun i j => raw25973step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25973step1 raw25973step0; decide +kernel
      have hl : raw25973step1Labels = raw25973step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25973step0 raw25973step0Labels permutation32 permutation7
    mixedMoment B raw25973step1 raw25973step1Labels = mixedMoment B raw25973step2 raw25973step2Labels := by
      have ha : raw25973step2 = -raw25973step1 := by apply Matrix.ext; change ∀ i j, raw25973step2 i j = -(raw25973step1 i j); unfold raw25973step2 raw25973step1; decide +kernel
      have hl : raw25973step2Labels = raw25973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25973step2 raw25973step2Labels = mixedMoment B raw25973step3 raw25973step3Labels := by
      have ha : raw25973step3 = raw25973step2 := by apply Matrix.ext; unfold raw25973step3 raw25973step2; decide +kernel
      have hl : raw25973step2Labels = labelEmbedding1 ∘ raw25973step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25973step2 raw25973step2Labels raw25973step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

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

theorem canonical27319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27319 raw27319Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw27319 raw27319Labels = mixedMoment B raw27319step0 raw27319step0Labels := by
      have hz : ∀ j, raw27319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27319step0 = (fun i j => raw27319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27319step0 raw27319; decide +kernel
      have hl : raw27319step0Labels = raw27319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27319 raw27319Labels permutation434 hz
    mixedMoment B raw27319step0 raw27319step0Labels = mixedMoment B raw27319step1 raw27319step1Labels := by
      have hz : ∀ j, raw27319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27319step1 = (fun i j => raw27319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27319step1 raw27319step0; decide +kernel
      have hl : raw27319step1Labels = raw27319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27319step0 raw27319step0Labels permutation80 hz
    mixedMoment B raw27319step1 raw27319step1Labels = mixedMoment B raw27319step2 raw27319step2Labels := by
      have ha : raw27319step2 = (fun i j => raw27319step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27319step2 raw27319step1; decide +kernel
      have hl : raw27319step2Labels = raw27319step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27319step1 raw27319step1Labels permutation31 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical226
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28989 raw28989Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw28989 raw28989Labels = mixedMoment B raw28989step0 raw28989step0Labels := by
      have ha : raw28989step0 = (fun i j => raw28989 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28989step0 raw28989; decide +kernel
      have hl : raw28989step0Labels = raw28989Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28989 raw28989Labels permutation682 permutation2
    mixedMoment B raw28989step0 raw28989step0Labels = mixedMoment B raw28989step1 raw28989step1Labels := by
      have ha : raw28989step1 = -raw28989step0 := by apply Matrix.ext; change ∀ i j, raw28989step1 i j = -(raw28989step0 i j); unfold raw28989step1 raw28989step0; decide +kernel
      have hl : raw28989step1Labels = raw28989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3757 node3757Labels := by rfl

theorem canonical28990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28990 raw28990Labels = mixedMoment B node2551 node2551Labels := by
  calc
    mixedMoment B raw28990 raw28990Labels = mixedMoment B raw28990step0 raw28990step0Labels := by
      have ha : raw28990step0 = (fun i j => raw28990 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28990step0 raw28990; decide +kernel
      have hl : raw28990step0Labels = raw28990Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28990 raw28990Labels permutation158 permutation2
    _ = mixedMoment B node2551 node2551Labels := by rfl

theorem canonical28991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28991 raw28991Labels = mixedMoment B node2551 node2551Labels := by
  calc
    _ = mixedMoment B node2551 node2551Labels := by rfl

theorem canonical28996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28996 raw28996Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw28996 raw28996Labels = mixedMoment B raw28996step0 raw28996step0Labels := by
      have ha : raw28996step0 = (fun i j => raw28996 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28996step0 raw28996; decide +kernel
      have hl : raw28996step0Labels = raw28996Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28996 raw28996Labels permutation682 permutation2
    mixedMoment B raw28996step0 raw28996step0Labels = mixedMoment B raw28996step1 raw28996step1Labels := by
      have ha : raw28996step1 = -raw28996step0 := by apply Matrix.ext; change ∀ i j, raw28996step1 i j = -(raw28996step0 i j); unfold raw28996step1 raw28996step0; decide +kernel
      have hl : raw28996step1Labels = raw28996step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3459 node3459Labels := by rfl

theorem canonical28997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28997 raw28997Labels = mixedMoment B node2550 node2550Labels := by
  calc
    mixedMoment B raw28997 raw28997Labels = mixedMoment B raw28997step0 raw28997step0Labels := by
      have ha : raw28997step0 = (fun i j => raw28997 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28997step0 raw28997; decide +kernel
      have hl : raw28997step0Labels = raw28997Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28997 raw28997Labels permutation158 permutation2
    _ = mixedMoment B node2550 node2550Labels := by rfl

theorem canonical28998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28998 raw28998Labels = mixedMoment B node2550 node2550Labels := by
  calc
    _ = mixedMoment B node2550 node2550Labels := by rfl

theorem canonical28999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28999 raw28999Labels = mixedMoment B node2540 node2540Labels := by
  calc
    _ = mixedMoment B node2540 node2540Labels := by rfl

theorem canonical29005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29005 raw29005Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw29005 raw29005Labels = mixedMoment B raw29005step0 raw29005step0Labels := by
      have hz : ∀ j, raw29005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29005step0 = (fun i j => raw29005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29005step0 raw29005; decide +kernel
      have hl : raw29005step0Labels = raw29005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29005 raw29005Labels permutation434 hz
    mixedMoment B raw29005step0 raw29005step0Labels = mixedMoment B raw29005step1 raw29005step1Labels := by
      have ha : raw29005step1 = (fun i j => raw29005step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29005step1 raw29005step0; decide +kernel
      have hl : raw29005step1Labels = raw29005step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29005step0 raw29005step0Labels permutation151 permutation2
    mixedMoment B raw29005step1 raw29005step1Labels = mixedMoment B raw29005step2 raw29005step2Labels := by
      have ha : raw29005step2 = -raw29005step1 := by apply Matrix.ext; change ∀ i j, raw29005step2 i j = -(raw29005step1 i j); unfold raw29005step2 raw29005step1; decide +kernel
      have hl : raw29005step2Labels = raw29005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2079 node2079Labels := by rfl

theorem canonical29006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29006 raw29006Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw29006 raw29006Labels = mixedMoment B raw29006step0 raw29006step0Labels := by
      have hz : ∀ j, raw29006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29006step0 = (fun i j => raw29006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29006step0 raw29006; decide +kernel
      have hl : raw29006step0Labels = raw29006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29006 raw29006Labels permutation434 hz
    mixedMoment B raw29006step0 raw29006step0Labels = mixedMoment B raw29006step1 raw29006step1Labels := by
      have ha : raw29006step1 = (fun i j => raw29006step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29006step1 raw29006step0; decide +kernel
      have hl : raw29006step1Labels = raw29006step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29006step0 raw29006step0Labels permutation151 permutation2
    mixedMoment B raw29006step1 raw29006step1Labels = mixedMoment B raw29006step2 raw29006step2Labels := by
      have ha : raw29006step2 = -raw29006step1 := by apply Matrix.ext; change ∀ i j, raw29006step2 i j = -(raw29006step1 i j); unfold raw29006step2 raw29006step1; decide +kernel
      have hl : raw29006step2Labels = raw29006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2082 node2082Labels := by rfl

theorem canonical29007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29007 raw29007Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw29007 raw29007Labels = mixedMoment B raw29007step0 raw29007step0Labels := by
      have hz : ∀ j, raw29007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29007step0 = (fun i j => raw29007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29007step0 raw29007; decide +kernel
      have hl : raw29007step0Labels = raw29007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29007 raw29007Labels permutation434 hz
    mixedMoment B raw29007step0 raw29007step0Labels = mixedMoment B raw29007step1 raw29007step1Labels := by
      have ha : raw29007step1 = (fun i j => raw29007step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29007step1 raw29007step0; decide +kernel
      have hl : raw29007step1Labels = raw29007step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29007step0 raw29007step0Labels permutation151 permutation2
    mixedMoment B raw29007step1 raw29007step1Labels = mixedMoment B raw29007step2 raw29007step2Labels := by
      have ha : raw29007step2 = -raw29007step1 := by apply Matrix.ext; change ∀ i j, raw29007step2 i j = -(raw29007step1 i j); unfold raw29007step2 raw29007step1; decide +kernel
      have hl : raw29007step2Labels = raw29007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2101 node2101Labels := by rfl

theorem canonical29008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29008 raw29008Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw29008 raw29008Labels = mixedMoment B raw29008step0 raw29008step0Labels := by
      have ha : raw29008step0 = (fun i j => raw29008 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29008step0 raw29008; decide +kernel
      have hl : raw29008step0Labels = raw29008Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29008 raw29008Labels permutation682 permutation2
    mixedMoment B raw29008step0 raw29008step0Labels = mixedMoment B raw29008step1 raw29008step1Labels := by
      have ha : raw29008step1 = -raw29008step0 := by apply Matrix.ext; change ∀ i j, raw29008step1 i j = -(raw29008step0 i j); unfold raw29008step1 raw29008step0; decide +kernel
      have hl : raw29008step1Labels = raw29008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2075 node2075Labels := by rfl

theorem canonical29009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29009 raw29009Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw29009 raw29009Labels = mixedMoment B raw29009step0 raw29009step0Labels := by
      have hz : ∀ j, raw29009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29009step0 = (fun i j => raw29009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29009step0 raw29009; decide +kernel
      have hl : raw29009step0Labels = raw29009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29009 raw29009Labels permutation434 hz
    mixedMoment B raw29009step0 raw29009step0Labels = mixedMoment B raw29009step1 raw29009step1Labels := by
      have ha : raw29009step1 = (fun i j => raw29009step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29009step1 raw29009step0; decide +kernel
      have hl : raw29009step1Labels = raw29009step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29009step0 raw29009step0Labels permutation145 permutation2
    mixedMoment B raw29009step1 raw29009step1Labels = mixedMoment B raw29009step2 raw29009step2Labels := by
      have ha : raw29009step2 = -raw29009step1 := by apply Matrix.ext; change ∀ i j, raw29009step2 i j = -(raw29009step1 i j); unfold raw29009step2 raw29009step1; decide +kernel
      have hl : raw29009step2Labels = raw29009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical29010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29010 raw29010Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw29010 raw29010Labels = mixedMoment B raw29010step0 raw29010step0Labels := by
      have hz : ∀ j, raw29010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29010step0 = (fun i j => raw29010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29010step0 raw29010; decide +kernel
      have hl : raw29010step0Labels = raw29010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29010 raw29010Labels permutation434 hz
    mixedMoment B raw29010step0 raw29010step0Labels = mixedMoment B raw29010step1 raw29010step1Labels := by
      have ha : raw29010step1 = (fun i j => raw29010step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29010step1 raw29010step0; decide +kernel
      have hl : raw29010step1Labels = raw29010step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29010step0 raw29010step0Labels permutation151 permutation2
    mixedMoment B raw29010step1 raw29010step1Labels = mixedMoment B raw29010step2 raw29010step2Labels := by
      have ha : raw29010step2 = -raw29010step1 := by apply Matrix.ext; change ∀ i j, raw29010step2 i j = -(raw29010step1 i j); unfold raw29010step2 raw29010step1; decide +kernel
      have hl : raw29010step2Labels = raw29010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical29011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29011 raw29011Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw29011 raw29011Labels = mixedMoment B raw29011step0 raw29011step0Labels := by
      have hz : ∀ j, raw29011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29011step0 = (fun i j => raw29011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29011step0 raw29011; decide +kernel
      have hl : raw29011step0Labels = raw29011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29011 raw29011Labels permutation434 hz
    mixedMoment B raw29011step0 raw29011step0Labels = mixedMoment B raw29011step1 raw29011step1Labels := by
      have ha : raw29011step1 = (fun i j => raw29011step0 (permutation143 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29011step1 raw29011step0; decide +kernel
      have hl : raw29011step1Labels = raw29011step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29011step0 raw29011step0Labels permutation143 permutation0
    mixedMoment B raw29011step1 raw29011step1Labels = mixedMoment B raw29011step2 raw29011step2Labels := by
      have ha : raw29011step2 = -raw29011step1 := by apply Matrix.ext; change ∀ i j, raw29011step2 i j = -(raw29011step1 i j); unfold raw29011step2 raw29011step1; decide +kernel
      have hl : raw29011step2Labels = raw29011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical29012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29012 raw29012Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw29012 raw29012Labels = mixedMoment B raw29012step0 raw29012step0Labels := by
      have hz : ∀ j, raw29012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29012step0 = (fun i j => raw29012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29012step0 raw29012; decide +kernel
      have hl : raw29012step0Labels = raw29012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29012 raw29012Labels permutation434 hz
    mixedMoment B raw29012step0 raw29012step0Labels = mixedMoment B raw29012step1 raw29012step1Labels := by
      have ha : raw29012step1 = (fun i j => raw29012step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29012step1 raw29012step0; decide +kernel
      have hl : raw29012step1Labels = raw29012step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29012step0 raw29012step0Labels permutation34 permutation2
    _ = mixedMoment B node1123 node1123Labels := by rfl

theorem canonical29013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29013 raw29013Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw29013 raw29013Labels = mixedMoment B raw29013step0 raw29013step0Labels := by
      have hz : ∀ j, raw29013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29013step0 = (fun i j => raw29013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29013step0 raw29013; decide +kernel
      have hl : raw29013step0Labels = raw29013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29013 raw29013Labels permutation434 hz
    mixedMoment B raw29013step0 raw29013step0Labels = mixedMoment B raw29013step1 raw29013step1Labels := by
      have ha : raw29013step1 = (fun i j => raw29013step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29013step1 raw29013step0; decide +kernel
      have hl : raw29013step1Labels = raw29013step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29013step0 raw29013step0Labels permutation145 permutation2
    mixedMoment B raw29013step1 raw29013step1Labels = mixedMoment B raw29013step2 raw29013step2Labels := by
      have ha : raw29013step2 = -raw29013step1 := by apply Matrix.ext; change ∀ i j, raw29013step2 i j = -(raw29013step1 i j); unfold raw29013step2 raw29013step1; decide +kernel
      have hl : raw29013step2Labels = raw29013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1880 node1880Labels := by rfl

theorem canonical29014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29014 raw29014Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw29014 raw29014Labels = mixedMoment B raw29014step0 raw29014step0Labels := by
      have ha : raw29014step0 = (fun i j => raw29014 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29014step0 raw29014; decide +kernel
      have hl : raw29014step0Labels = raw29014Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29014 raw29014Labels permutation646 permutation2
    mixedMoment B raw29014step0 raw29014step0Labels = mixedMoment B raw29014step1 raw29014step1Labels := by
      have ha : raw29014step1 = -raw29014step0 := by apply Matrix.ext; change ∀ i j, raw29014step1 i j = -(raw29014step0 i j); unfold raw29014step1 raw29014step0; decide +kernel
      have hl : raw29014step1Labels = raw29014step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1875 node1875Labels := by rfl

theorem canonical29015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29015 raw29015Labels = mixedMoment B node1914 node1914Labels := by
  calc
    mixedMoment B raw29015 raw29015Labels = mixedMoment B raw29015step0 raw29015step0Labels := by
      have hz : ∀ j, raw29015 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29015step0 = (fun i j => raw29015 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29015step0 raw29015; decide +kernel
      have hl : raw29015step0Labels = raw29015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29015 raw29015Labels permutation434 hz
    mixedMoment B raw29015step0 raw29015step0Labels = mixedMoment B raw29015step1 raw29015step1Labels := by
      have ha : raw29015step1 = (fun i j => raw29015step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29015step1 raw29015step0; decide +kernel
      have hl : raw29015step1Labels = raw29015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29015step0 raw29015step0Labels permutation145 permutation2
    mixedMoment B raw29015step1 raw29015step1Labels = mixedMoment B raw29015step2 raw29015step2Labels := by
      have ha : raw29015step2 = -raw29015step1 := by apply Matrix.ext; change ∀ i j, raw29015step2 i j = -(raw29015step1 i j); unfold raw29015step2 raw29015step1; decide +kernel
      have hl : raw29015step2Labels = raw29015step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1914 node1914Labels := by rfl

theorem canonical29016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29016 raw29016Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw29016 raw29016Labels = mixedMoment B raw29016step0 raw29016step0Labels := by
      have hz : ∀ j, raw29016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29016step0 = (fun i j => raw29016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29016step0 raw29016; decide +kernel
      have hl : raw29016step0Labels = raw29016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29016 raw29016Labels permutation434 hz
    mixedMoment B raw29016step0 raw29016step0Labels = mixedMoment B raw29016step1 raw29016step1Labels := by
      have ha : raw29016step1 = (fun i j => raw29016step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29016step1 raw29016step0; decide +kernel
      have hl : raw29016step1Labels = raw29016step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29016step0 raw29016step0Labels permutation34 permutation2
    _ = mixedMoment B node2504 node2504Labels := by rfl

theorem canonical29020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29020 raw29020Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw29020 raw29020Labels = mixedMoment B raw29020step0 raw29020step0Labels := by
      have hz : ∀ j, raw29020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29020step0 = (fun i j => raw29020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29020step0 raw29020; decide +kernel
      have hl : raw29020step0Labels = raw29020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29020 raw29020Labels permutation434 hz
    mixedMoment B raw29020step0 raw29020step0Labels = mixedMoment B raw29020step1 raw29020step1Labels := by
      have ha : raw29020step1 = (fun i j => raw29020step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29020step1 raw29020step0; decide +kernel
      have hl : raw29020step1Labels = raw29020step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29020step0 raw29020step0Labels permutation145 permutation4
    _ = mixedMoment B node2047 node2047Labels := by rfl

theorem canonical29021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29021 raw29021Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw29021 raw29021Labels = mixedMoment B raw29021step0 raw29021step0Labels := by
      have hz : ∀ j, raw29021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29021step0 = (fun i j => raw29021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29021step0 raw29021; decide +kernel
      have hl : raw29021step0Labels = raw29021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29021 raw29021Labels permutation434 hz
    mixedMoment B raw29021step0 raw29021step0Labels = mixedMoment B raw29021step1 raw29021step1Labels := by
      have ha : raw29021step1 = (fun i j => raw29021step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29021step1 raw29021step0; decide +kernel
      have hl : raw29021step1Labels = raw29021step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29021step0 raw29021step0Labels permutation143 permutation4
    _ = mixedMoment B node2018 node2018Labels := by rfl

theorem canonical29022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29022 raw29022Labels = mixedMoment B node1799 node1799Labels := by
  calc
    mixedMoment B raw29022 raw29022Labels = mixedMoment B raw29022step0 raw29022step0Labels := by
      have hz : ∀ j, raw29022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29022step0 = (fun i j => raw29022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29022step0 raw29022; decide +kernel
      have hl : raw29022step0Labels = raw29022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29022 raw29022Labels permutation434 hz
    mixedMoment B raw29022step0 raw29022step0Labels = mixedMoment B raw29022step1 raw29022step1Labels := by
      have ha : raw29022step1 = (fun i j => raw29022step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29022step1 raw29022step0; decide +kernel
      have hl : raw29022step1Labels = raw29022step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29022step0 raw29022step0Labels permutation145 permutation4
    _ = mixedMoment B node1799 node1799Labels := by rfl

theorem canonical29023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29023 raw29023Labels = mixedMoment B node1874 node1874Labels := by
  calc
    mixedMoment B raw29023 raw29023Labels = mixedMoment B raw29023step0 raw29023step0Labels := by
      have ha : raw29023step0 = (fun i j => raw29023 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29023step0 raw29023; decide +kernel
      have hl : raw29023step0Labels = raw29023Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29023 raw29023Labels permutation164 permutation4
    mixedMoment B raw29023step0 raw29023step0Labels = mixedMoment B raw29023step1 raw29023step1Labels := by
      have ha : raw29023step1 = -raw29023step0 := by apply Matrix.ext; change ∀ i j, raw29023step1 i j = -(raw29023step0 i j); unfold raw29023step1 raw29023step0; decide +kernel
      have hl : raw29023step1Labels = raw29023step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1874 node1874Labels := by rfl

theorem canonical29024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29024 raw29024Labels = mixedMoment B node1911 node1911Labels := by
  calc
    mixedMoment B raw29024 raw29024Labels = mixedMoment B raw29024step0 raw29024step0Labels := by
      have hz : ∀ j, raw29024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29024step0 = (fun i j => raw29024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29024step0 raw29024; decide +kernel
      have hl : raw29024step0Labels = raw29024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29024 raw29024Labels permutation434 hz
    mixedMoment B raw29024step0 raw29024step0Labels = mixedMoment B raw29024step1 raw29024step1Labels := by
      have ha : raw29024step1 = (fun i j => raw29024step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29024step1 raw29024step0; decide +kernel
      have hl : raw29024step1Labels = raw29024step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29024step0 raw29024step0Labels permutation34 permutation4
    mixedMoment B raw29024step1 raw29024step1Labels = mixedMoment B raw29024step2 raw29024step2Labels := by
      have ha : raw29024step2 = -raw29024step1 := by apply Matrix.ext; change ∀ i j, raw29024step2 i j = -(raw29024step1 i j); unfold raw29024step2 raw29024step1; decide +kernel
      have hl : raw29024step2Labels = raw29024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1911 node1911Labels := by rfl

theorem canonical29025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29025 raw29025Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw29025 raw29025Labels = mixedMoment B raw29025step0 raw29025step0Labels := by
      have hz : ∀ j, raw29025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29025step0 = (fun i j => raw29025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29025step0 raw29025; decide +kernel
      have hl : raw29025step0Labels = raw29025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29025 raw29025Labels permutation434 hz
    mixedMoment B raw29025step0 raw29025step0Labels = mixedMoment B raw29025step1 raw29025step1Labels := by
      have ha : raw29025step1 = (fun i j => raw29025step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29025step1 raw29025step0; decide +kernel
      have hl : raw29025step1Labels = raw29025step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29025step0 raw29025step0Labels permutation145 permutation4
    _ = mixedMoment B node916 node916Labels := by rfl

theorem canonical29026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29026 raw29026Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw29026 raw29026Labels = mixedMoment B raw29026step0 raw29026step0Labels := by
      have ha : raw29026step0 = (fun i j => raw29026 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29026step0 raw29026; decide +kernel
      have hl : raw29026step0Labels = raw29026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29026 raw29026Labels permutation158 permutation2
    _ = mixedMoment B node2449 node2449Labels := by rfl

theorem canonical29027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29027 raw29027Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw29027 raw29027Labels = mixedMoment B raw29027step0 raw29027step0Labels := by
      have ha : raw29027step0 = (fun i j => raw29027 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29027step0 raw29027; decide +kernel
      have hl : raw29027step0Labels = raw29027Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29027 raw29027Labels permutation682 permutation2
    mixedMoment B raw29027step0 raw29027step0Labels = mixedMoment B raw29027step1 raw29027step1Labels := by
      have ha : raw29027step1 = -raw29027step0 := by apply Matrix.ext; change ∀ i j, raw29027step1 i j = -(raw29027step0 i j); unfold raw29027step1 raw29027step0; decide +kernel
      have hl : raw29027step1Labels = raw29027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2452 node2452Labels := by rfl

theorem canonical29028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29028 raw29028Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw29028 raw29028Labels = mixedMoment B raw29028step0 raw29028step0Labels := by
      have ha : raw29028step0 = (fun i j => raw29028 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29028step0 raw29028; decide +kernel
      have hl : raw29028step0Labels = raw29028Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29028 raw29028Labels permutation688 permutation2
    mixedMoment B raw29028step0 raw29028step0Labels = mixedMoment B raw29028step1 raw29028step1Labels := by
      have ha : raw29028step1 = -raw29028step0 := by apply Matrix.ext; change ∀ i j, raw29028step1 i j = -(raw29028step0 i j); unfold raw29028step1 raw29028step0; decide +kernel
      have hl : raw29028step1Labels = raw29028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2477 node2477Labels := by rfl

theorem canonical29029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29029 raw29029Labels = mixedMoment B node2461 node2461Labels := by
  calc
    mixedMoment B raw29029 raw29029Labels = mixedMoment B raw29029step0 raw29029step0Labels := by
      have ha : raw29029step0 = (fun i j => raw29029 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29029step0 raw29029; decide +kernel
      have hl : raw29029step0Labels = raw29029Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29029 raw29029Labels permutation680 permutation2
    mixedMoment B raw29029step0 raw29029step0Labels = mixedMoment B raw29029step1 raw29029step1Labels := by
      have ha : raw29029step1 = -raw29029step0 := by apply Matrix.ext; change ∀ i j, raw29029step1 i j = -(raw29029step0 i j); unfold raw29029step1 raw29029step0; decide +kernel
      have hl : raw29029step1Labels = raw29029step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2461 node2461Labels := by rfl

theorem canonical29030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29030 raw29030Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw29030 raw29030Labels = mixedMoment B raw29030step0 raw29030step0Labels := by
      have ha : raw29030step0 = (fun i j => raw29030 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29030step0 raw29030; decide +kernel
      have hl : raw29030step0Labels = raw29030Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29030 raw29030Labels permutation646 permutation2
    mixedMoment B raw29030step0 raw29030step0Labels = mixedMoment B raw29030step1 raw29030step1Labels := by
      have ha : raw29030step1 = -raw29030step0 := by apply Matrix.ext; change ∀ i j, raw29030step1 i j = -(raw29030step0 i j); unfold raw29030step1 raw29030step0; decide +kernel
      have hl : raw29030step1Labels = raw29030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical29031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29031 raw29031Labels = mixedMoment B node3793 node3793Labels := by
  calc
    mixedMoment B raw29031 raw29031Labels = mixedMoment B raw29031step0 raw29031step0Labels := by
      have ha : raw29031step0 = (fun i j => raw29031 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29031step0 raw29031; decide +kernel
      have hl : raw29031step0Labels = raw29031Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29031 raw29031Labels permutation158 permutation2
    _ = mixedMoment B node3793 node3793Labels := by rfl

theorem canonical29032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29032 raw29032Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw29032 raw29032Labels = mixedMoment B raw29032step0 raw29032step0Labels := by
      have ha : raw29032step0 = (fun i j => raw29032 (permutation158 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29032step0 raw29032; decide +kernel
      have hl : raw29032step0Labels = raw29032Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29032 raw29032Labels permutation158 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29093 raw29093Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw29093 raw29093Labels = mixedMoment B raw29093step0 raw29093step0Labels := by
      have hz : ∀ j, raw29093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29093step0 = (fun i j => raw29093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29093step0 raw29093; decide +kernel
      have hl : raw29093step0Labels = raw29093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29093 raw29093Labels permutation434 hz
    mixedMoment B raw29093step0 raw29093step0Labels = mixedMoment B raw29093step1 raw29093step1Labels := by
      have hz : ∀ j, raw29093step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29093step1 = (fun i j => raw29093step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29093step1 raw29093step0; decide +kernel
      have hl : raw29093step1Labels = raw29093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29093step0 raw29093step0Labels permutation80 hz
    mixedMoment B raw29093step1 raw29093step1Labels = mixedMoment B raw29093step2 raw29093step2Labels := by
      have ha : raw29093step2 = (fun i j => raw29093step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29093step2 raw29093step1; decide +kernel
      have hl : raw29093step2Labels = raw29093step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29093step1 raw29093step1Labels permutation31 permutation7
    mixedMoment B raw29093step2 raw29093step2Labels = mixedMoment B raw29093step3 raw29093step3Labels := by
      have ha : raw29093step3 = raw29093step2 := by apply Matrix.ext; unfold raw29093step3 raw29093step2; decide +kernel
      have hl : raw29093step2Labels = labelEmbedding1 ∘ raw29093step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29093step2 raw29093step2Labels raw29093step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical29094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29094 raw29094Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw29094 raw29094Labels = mixedMoment B raw29094step0 raw29094step0Labels := by
      have hz : ∀ j, raw29094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29094step0 = (fun i j => raw29094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29094step0 raw29094; decide +kernel
      have hl : raw29094step0Labels = raw29094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29094 raw29094Labels permutation434 hz
    mixedMoment B raw29094step0 raw29094step0Labels = mixedMoment B raw29094step1 raw29094step1Labels := by
      have ha : raw29094step1 = (fun i j => raw29094step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29094step1 raw29094step0; decide +kernel
      have hl : raw29094step1Labels = raw29094step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29094step0 raw29094step0Labels permutation151 permutation7
    mixedMoment B raw29094step1 raw29094step1Labels = mixedMoment B raw29094step2 raw29094step2Labels := by
      have ha : raw29094step2 = raw29094step1 := by apply Matrix.ext; unfold raw29094step2 raw29094step1; decide +kernel
      have hl : raw29094step1Labels = labelEmbedding1 ∘ raw29094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29094step1 raw29094step1Labels raw29094step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical29095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29095 raw29095Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw29095 raw29095Labels = mixedMoment B raw29095step0 raw29095step0Labels := by
      have hz : ∀ j, raw29095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29095step0 = (fun i j => raw29095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29095step0 raw29095; decide +kernel
      have hl : raw29095step0Labels = raw29095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29095 raw29095Labels permutation346 hz
    mixedMoment B raw29095step0 raw29095step0Labels = mixedMoment B raw29095step1 raw29095step1Labels := by
      have ha : raw29095step1 = (fun i j => raw29095step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29095step1 raw29095step0; decide +kernel
      have hl : raw29095step1Labels = raw29095step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29095step0 raw29095step0Labels permutation151 permutation7
    mixedMoment B raw29095step1 raw29095step1Labels = mixedMoment B raw29095step2 raw29095step2Labels := by
      have ha : raw29095step2 = raw29095step1 := by apply Matrix.ext; unfold raw29095step2 raw29095step1; decide +kernel
      have hl : raw29095step1Labels = labelEmbedding1 ∘ raw29095step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29095step1 raw29095step1Labels raw29095step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical29096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29096 raw29096Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw29096 raw29096Labels = mixedMoment B raw29096step0 raw29096step0Labels := by
      have hz : ∀ j, raw29096 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29096step0 = (fun i j => raw29096 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29096step0 raw29096; decide +kernel
      have hl : raw29096step0Labels = raw29096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29096 raw29096Labels permutation520 hz
    mixedMoment B raw29096step0 raw29096step0Labels = mixedMoment B raw29096step1 raw29096step1Labels := by
      have hz : ∀ j, raw29096step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29096step1 = (fun i j => raw29096step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29096step1 raw29096step0; decide +kernel
      have hl : raw29096step1Labels = raw29096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29096step0 raw29096step0Labels permutation104 hz
    mixedMoment B raw29096step1 raw29096step1Labels = mixedMoment B raw29096step2 raw29096step2Labels := by
      have hz : ∀ j, raw29096step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29096step2 = (fun i j => raw29096step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29096step2 raw29096step1; decide +kernel
      have hl : raw29096step2Labels = raw29096step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29096step1 raw29096step1Labels permutation20 hz
    mixedMoment B raw29096step2 raw29096step2Labels = mixedMoment B raw29096step3 raw29096step3Labels := by
      have hz : ∀ i, raw29096step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw29096step3 = (fun i j => raw29096step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw29096step3 raw29096step2; decide +kernel
      have hl : raw29096step3Labels = (fun j => raw29096step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29096step2 raw29096step2Labels permutation4 hz
    mixedMoment B raw29096step3 raw29096step3Labels = mixedMoment B raw29096step4 raw29096step4Labels := by
      have ha : raw29096step4 = (fun i j => raw29096step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29096step4 raw29096step3; decide +kernel
      have hl : raw29096step4Labels = raw29096step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29096step3 raw29096step3Labels permutation7 permutation0
    mixedMoment B raw29096step4 raw29096step4Labels = mixedMoment B raw29096step5 raw29096step5Labels := by
      have ha : raw29096step5 = -raw29096step4 := by apply Matrix.ext; change ∀ i j, raw29096step5 i j = -(raw29096step4 i j); unfold raw29096step5 raw29096step4; decide +kernel
      have hl : raw29096step5Labels = raw29096step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical29097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29097 raw29097Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw29097 raw29097Labels = mixedMoment B raw29097step0 raw29097step0Labels := by
      have hz : ∀ j, raw29097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29097step0 = (fun i j => raw29097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29097step0 raw29097; decide +kernel
      have hl : raw29097step0Labels = raw29097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29097 raw29097Labels permutation434 hz
    mixedMoment B raw29097step0 raw29097step0Labels = mixedMoment B raw29097step1 raw29097step1Labels := by
      have hz : ∀ j, raw29097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29097step1 = (fun i j => raw29097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29097step1 raw29097step0; decide +kernel
      have hl : raw29097step1Labels = raw29097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29097step0 raw29097step0Labels permutation80 hz
    mixedMoment B raw29097step1 raw29097step1Labels = mixedMoment B raw29097step2 raw29097step2Labels := by
      have ha : raw29097step2 = (fun i j => raw29097step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29097step2 raw29097step1; decide +kernel
      have hl : raw29097step2Labels = raw29097step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29097step1 raw29097step1Labels permutation31 permutation7
    mixedMoment B raw29097step2 raw29097step2Labels = mixedMoment B raw29097step3 raw29097step3Labels := by
      have ha : raw29097step3 = raw29097step2 := by apply Matrix.ext; unfold raw29097step3 raw29097step2; decide +kernel
      have hl : raw29097step2Labels = labelEmbedding1 ∘ raw29097step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29097step2 raw29097step2Labels raw29097step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical29098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29098 raw29098Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw29098 raw29098Labels = mixedMoment B raw29098step0 raw29098step0Labels := by
      have hz : ∀ j, raw29098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29098step0 = (fun i j => raw29098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29098step0 raw29098; decide +kernel
      have hl : raw29098step0Labels = raw29098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29098 raw29098Labels permutation434 hz
    mixedMoment B raw29098step0 raw29098step0Labels = mixedMoment B raw29098step1 raw29098step1Labels := by
      have hz : ∀ j, raw29098step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29098step1 = (fun i j => raw29098step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29098step1 raw29098step0; decide +kernel
      have hl : raw29098step1Labels = raw29098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29098step0 raw29098step0Labels permutation80 hz
    mixedMoment B raw29098step1 raw29098step1Labels = mixedMoment B raw29098step2 raw29098step2Labels := by
      have ha : raw29098step2 = (fun i j => raw29098step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29098step2 raw29098step1; decide +kernel
      have hl : raw29098step2Labels = raw29098step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29098step1 raw29098step1Labels permutation31 permutation7
    mixedMoment B raw29098step2 raw29098step2Labels = mixedMoment B raw29098step3 raw29098step3Labels := by
      have ha : raw29098step3 = raw29098step2 := by apply Matrix.ext; unfold raw29098step3 raw29098step2; decide +kernel
      have hl : raw29098step2Labels = labelEmbedding1 ∘ raw29098step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29098step2 raw29098step2Labels raw29098step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical29099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29099 raw29099Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw29099 raw29099Labels = mixedMoment B raw29099step0 raw29099step0Labels := by
      have hz : ∀ j, raw29099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29099step0 = (fun i j => raw29099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29099step0 raw29099; decide +kernel
      have hl : raw29099step0Labels = raw29099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29099 raw29099Labels permutation434 hz
    mixedMoment B raw29099step0 raw29099step0Labels = mixedMoment B raw29099step1 raw29099step1Labels := by
      have ha : raw29099step1 = (fun i j => raw29099step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29099step1 raw29099step0; decide +kernel
      have hl : raw29099step1Labels = raw29099step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29099step0 raw29099step0Labels permutation151 permutation7
    mixedMoment B raw29099step1 raw29099step1Labels = mixedMoment B raw29099step2 raw29099step2Labels := by
      have ha : raw29099step2 = raw29099step1 := by apply Matrix.ext; unfold raw29099step2 raw29099step1; decide +kernel
      have hl : raw29099step1Labels = labelEmbedding1 ∘ raw29099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29099step1 raw29099step1Labels raw29099step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical29100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29100 raw29100Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw29100 raw29100Labels = mixedMoment B raw29100step0 raw29100step0Labels := by
      have hz : ∀ j, raw29100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29100step0 = (fun i j => raw29100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29100step0 raw29100; decide +kernel
      have hl : raw29100step0Labels = raw29100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29100 raw29100Labels permutation346 hz
    mixedMoment B raw29100step0 raw29100step0Labels = mixedMoment B raw29100step1 raw29100step1Labels := by
      have ha : raw29100step1 = (fun i j => raw29100step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29100step1 raw29100step0; decide +kernel
      have hl : raw29100step1Labels = raw29100step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29100step0 raw29100step0Labels permutation151 permutation7
    mixedMoment B raw29100step1 raw29100step1Labels = mixedMoment B raw29100step2 raw29100step2Labels := by
      have ha : raw29100step2 = raw29100step1 := by apply Matrix.ext; unfold raw29100step2 raw29100step1; decide +kernel
      have hl : raw29100step1Labels = labelEmbedding1 ∘ raw29100step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29100step1 raw29100step1Labels raw29100step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical29101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29101 raw29101Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw29101 raw29101Labels = mixedMoment B raw29101step0 raw29101step0Labels := by
      have hz : ∀ j, raw29101 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29101step0 = (fun i j => raw29101 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29101step0 raw29101; decide +kernel
      have hl : raw29101step0Labels = raw29101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29101 raw29101Labels permutation520 hz
    mixedMoment B raw29101step0 raw29101step0Labels = mixedMoment B raw29101step1 raw29101step1Labels := by
      have hz : ∀ j, raw29101step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29101step1 = (fun i j => raw29101step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29101step1 raw29101step0; decide +kernel
      have hl : raw29101step1Labels = raw29101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29101step0 raw29101step0Labels permutation104 hz
    mixedMoment B raw29101step1 raw29101step1Labels = mixedMoment B raw29101step2 raw29101step2Labels := by
      have hz : ∀ j, raw29101step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29101step2 = (fun i j => raw29101step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29101step2 raw29101step1; decide +kernel
      have hl : raw29101step2Labels = raw29101step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29101step1 raw29101step1Labels permutation20 hz
    mixedMoment B raw29101step2 raw29101step2Labels = mixedMoment B raw29101step3 raw29101step3Labels := by
      have ha : raw29101step3 = (fun i j => raw29101step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29101step3 raw29101step2; decide +kernel
      have hl : raw29101step3Labels = raw29101step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29101step2 raw29101step2Labels permutation7 permutation7
    mixedMoment B raw29101step3 raw29101step3Labels = mixedMoment B raw29101step4 raw29101step4Labels := by
      have ha : raw29101step4 = raw29101step3 := by apply Matrix.ext; unfold raw29101step4 raw29101step3; decide +kernel
      have hl : raw29101step3Labels = labelEmbedding1 ∘ raw29101step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29101step3 raw29101step3Labels raw29101step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

theorem canonical29102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29102 raw29102Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw29102 raw29102Labels = mixedMoment B raw29102step0 raw29102step0Labels := by
      have hz : ∀ j, raw29102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29102step0 = (fun i j => raw29102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29102step0 raw29102; decide +kernel
      have hl : raw29102step0Labels = raw29102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29102 raw29102Labels permutation434 hz
    mixedMoment B raw29102step0 raw29102step0Labels = mixedMoment B raw29102step1 raw29102step1Labels := by
      have hz : ∀ j, raw29102step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29102step1 = (fun i j => raw29102step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29102step1 raw29102step0; decide +kernel
      have hl : raw29102step1Labels = raw29102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29102step0 raw29102step0Labels permutation80 hz
    mixedMoment B raw29102step1 raw29102step1Labels = mixedMoment B raw29102step2 raw29102step2Labels := by
      have ha : raw29102step2 = (fun i j => raw29102step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29102step2 raw29102step1; decide +kernel
      have hl : raw29102step2Labels = raw29102step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29102step1 raw29102step1Labels permutation31 permutation7
    mixedMoment B raw29102step2 raw29102step2Labels = mixedMoment B raw29102step3 raw29102step3Labels := by
      have ha : raw29102step3 = raw29102step2 := by apply Matrix.ext; unfold raw29102step3 raw29102step2; decide +kernel
      have hl : raw29102step2Labels = labelEmbedding1 ∘ raw29102step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29102step2 raw29102step2Labels raw29102step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical29103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29103 raw29103Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw29103 raw29103Labels = mixedMoment B raw29103step0 raw29103step0Labels := by
      have hz : ∀ j, raw29103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29103step0 = (fun i j => raw29103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29103step0 raw29103; decide +kernel
      have hl : raw29103step0Labels = raw29103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29103 raw29103Labels permutation434 hz
    mixedMoment B raw29103step0 raw29103step0Labels = mixedMoment B raw29103step1 raw29103step1Labels := by
      have ha : raw29103step1 = (fun i j => raw29103step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29103step1 raw29103step0; decide +kernel
      have hl : raw29103step1Labels = raw29103step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29103step0 raw29103step0Labels permutation145 permutation7
    mixedMoment B raw29103step1 raw29103step1Labels = mixedMoment B raw29103step2 raw29103step2Labels := by
      have ha : raw29103step2 = raw29103step1 := by apply Matrix.ext; unfold raw29103step2 raw29103step1; decide +kernel
      have hl : raw29103step1Labels = labelEmbedding1 ∘ raw29103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29103step1 raw29103step1Labels raw29103step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

theorem canonical29104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29104 raw29104Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw29104 raw29104Labels = mixedMoment B raw29104step0 raw29104step0Labels := by
      have hz : ∀ j, raw29104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29104step0 = (fun i j => raw29104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29104step0 raw29104; decide +kernel
      have hl : raw29104step0Labels = raw29104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29104 raw29104Labels permutation434 hz
    mixedMoment B raw29104step0 raw29104step0Labels = mixedMoment B raw29104step1 raw29104step1Labels := by
      have ha : raw29104step1 = (fun i j => raw29104step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29104step1 raw29104step0; decide +kernel
      have hl : raw29104step1Labels = raw29104step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29104step0 raw29104step0Labels permutation145 permutation7
    mixedMoment B raw29104step1 raw29104step1Labels = mixedMoment B raw29104step2 raw29104step2Labels := by
      have ha : raw29104step2 = raw29104step1 := by apply Matrix.ext; unfold raw29104step2 raw29104step1; decide +kernel
      have hl : raw29104step1Labels = labelEmbedding1 ∘ raw29104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29104step1 raw29104step1Labels raw29104step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical29105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29105 raw29105Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw29105 raw29105Labels = mixedMoment B raw29105step0 raw29105step0Labels := by
      have ha : raw29105step0 = (fun i j => raw29105 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29105step0 raw29105; decide +kernel
      have hl : raw29105step0Labels = raw29105Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29105 raw29105Labels permutation646 permutation7
    mixedMoment B raw29105step0 raw29105step0Labels = mixedMoment B raw29105step1 raw29105step1Labels := by
      have ha : raw29105step1 = raw29105step0 := by apply Matrix.ext; unfold raw29105step1 raw29105step0; decide +kernel
      have hl : raw29105step0Labels = labelEmbedding1 ∘ raw29105step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29105step0 raw29105step0Labels raw29105step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

theorem canonical29106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29106 raw29106Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw29106 raw29106Labels = mixedMoment B raw29106step0 raw29106step0Labels := by
      have hz : ∀ j, raw29106 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29106step0 = (fun i j => raw29106 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29106step0 raw29106; decide +kernel
      have hl : raw29106step0Labels = raw29106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29106 raw29106Labels permutation520 hz
    mixedMoment B raw29106step0 raw29106step0Labels = mixedMoment B raw29106step1 raw29106step1Labels := by
      have hz : ∀ j, raw29106step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29106step1 = (fun i j => raw29106step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29106step1 raw29106step0; decide +kernel
      have hl : raw29106step1Labels = raw29106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29106step0 raw29106step0Labels permutation104 hz
    mixedMoment B raw29106step1 raw29106step1Labels = mixedMoment B raw29106step2 raw29106step2Labels := by
      have ha : raw29106step2 = (fun i j => raw29106step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29106step2 raw29106step1; decide +kernel
      have hl : raw29106step2Labels = raw29106step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29106step1 raw29106step1Labels permutation31 permutation7
    mixedMoment B raw29106step2 raw29106step2Labels = mixedMoment B raw29106step3 raw29106step3Labels := by
      have ha : raw29106step3 = raw29106step2 := by apply Matrix.ext; unfold raw29106step3 raw29106step2; decide +kernel
      have hl : raw29106step2Labels = labelEmbedding1 ∘ raw29106step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29106step2 raw29106step2Labels raw29106step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical29107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29107 raw29107Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw29107 raw29107Labels = mixedMoment B raw29107step0 raw29107step0Labels := by
      have hz : ∀ j, raw29107 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29107step0 = (fun i j => raw29107 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29107step0 raw29107; decide +kernel
      have hl : raw29107step0Labels = raw29107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29107 raw29107Labels permutation434 hz
    mixedMoment B raw29107step0 raw29107step0Labels = mixedMoment B raw29107step1 raw29107step1Labels := by
      have ha : raw29107step1 = (fun i j => raw29107step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29107step1 raw29107step0; decide +kernel
      have hl : raw29107step1Labels = raw29107step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29107step0 raw29107step0Labels permutation145 permutation7
    mixedMoment B raw29107step1 raw29107step1Labels = mixedMoment B raw29107step2 raw29107step2Labels := by
      have ha : raw29107step2 = raw29107step1 := by apply Matrix.ext; unfold raw29107step2 raw29107step1; decide +kernel
      have hl : raw29107step1Labels = labelEmbedding1 ∘ raw29107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29107step1 raw29107step1Labels raw29107step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical29108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29108 raw29108Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw29108 raw29108Labels = mixedMoment B raw29108step0 raw29108step0Labels := by
      have hz : ∀ j, raw29108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29108step0 = (fun i j => raw29108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29108step0 raw29108; decide +kernel
      have hl : raw29108step0Labels = raw29108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29108 raw29108Labels permutation346 hz
    mixedMoment B raw29108step0 raw29108step0Labels = mixedMoment B raw29108step1 raw29108step1Labels := by
      have ha : raw29108step1 = (fun i j => raw29108step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29108step1 raw29108step0; decide +kernel
      have hl : raw29108step1Labels = raw29108step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29108step0 raw29108step0Labels permutation145 permutation7
    mixedMoment B raw29108step1 raw29108step1Labels = mixedMoment B raw29108step2 raw29108step2Labels := by
      have ha : raw29108step2 = raw29108step1 := by apply Matrix.ext; unfold raw29108step2 raw29108step1; decide +kernel
      have hl : raw29108step1Labels = labelEmbedding1 ∘ raw29108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29108step1 raw29108step1Labels raw29108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

theorem canonical29109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29109 raw29109Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw29109 raw29109Labels = mixedMoment B raw29109step0 raw29109step0Labels := by
      have hz : ∀ j, raw29109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29109step0 = (fun i j => raw29109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29109step0 raw29109; decide +kernel
      have hl : raw29109step0Labels = raw29109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29109 raw29109Labels permutation346 hz
    mixedMoment B raw29109step0 raw29109step0Labels = mixedMoment B raw29109step1 raw29109step1Labels := by
      have ha : raw29109step1 = (fun i j => raw29109step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29109step1 raw29109step0; decide +kernel
      have hl : raw29109step1Labels = raw29109step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29109step0 raw29109step0Labels permutation145 permutation7
    mixedMoment B raw29109step1 raw29109step1Labels = mixedMoment B raw29109step2 raw29109step2Labels := by
      have ha : raw29109step2 = raw29109step1 := by apply Matrix.ext; unfold raw29109step2 raw29109step1; decide +kernel
      have hl : raw29109step1Labels = labelEmbedding1 ∘ raw29109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29109step1 raw29109step1Labels raw29109step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical29110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29110 raw29110Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw29110 raw29110Labels = mixedMoment B raw29110step0 raw29110step0Labels := by
      have ha : raw29110step0 = (fun i j => raw29110 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29110step0 raw29110; decide +kernel
      have hl : raw29110step0Labels = raw29110Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29110 raw29110Labels permutation664 permutation7
    mixedMoment B raw29110step0 raw29110step0Labels = mixedMoment B raw29110step1 raw29110step1Labels := by
      have ha : raw29110step1 = raw29110step0 := by apply Matrix.ext; unfold raw29110step1 raw29110step0; decide +kernel
      have hl : raw29110step0Labels = labelEmbedding1 ∘ raw29110step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29110step0 raw29110step0Labels raw29110step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

theorem canonical29111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29111 raw29111Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw29111 raw29111Labels = mixedMoment B raw29111step0 raw29111step0Labels := by
      have hz : ∀ j, raw29111 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29111step0 = (fun i j => raw29111 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29111step0 raw29111; decide +kernel
      have hl : raw29111step0Labels = raw29111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29111 raw29111Labels permutation520 hz
    mixedMoment B raw29111step0 raw29111step0Labels = mixedMoment B raw29111step1 raw29111step1Labels := by
      have hz : ∀ j, raw29111step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29111step1 = (fun i j => raw29111step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29111step1 raw29111step0; decide +kernel
      have hl : raw29111step1Labels = raw29111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29111step0 raw29111step0Labels permutation80 hz
    mixedMoment B raw29111step1 raw29111step1Labels = mixedMoment B raw29111step2 raw29111step2Labels := by
      have ha : raw29111step2 = (fun i j => raw29111step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29111step2 raw29111step1; decide +kernel
      have hl : raw29111step2Labels = raw29111step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29111step1 raw29111step1Labels permutation31 permutation7
    mixedMoment B raw29111step2 raw29111step2Labels = mixedMoment B raw29111step3 raw29111step3Labels := by
      have ha : raw29111step3 = raw29111step2 := by apply Matrix.ext; unfold raw29111step3 raw29111step2; decide +kernel
      have hl : raw29111step2Labels = labelEmbedding1 ∘ raw29111step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29111step2 raw29111step2Labels raw29111step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical29112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29112 raw29112Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw29112 raw29112Labels = mixedMoment B raw29112step0 raw29112step0Labels := by
      have hz : ∀ j, raw29112 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29112step0 = (fun i j => raw29112 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29112step0 raw29112; decide +kernel
      have hl : raw29112step0Labels = raw29112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29112 raw29112Labels permutation346 hz
    mixedMoment B raw29112step0 raw29112step0Labels = mixedMoment B raw29112step1 raw29112step1Labels := by
      have ha : raw29112step1 = (fun i j => raw29112step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29112step1 raw29112step0; decide +kernel
      have hl : raw29112step1Labels = raw29112step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29112step0 raw29112step0Labels permutation145 permutation7
    mixedMoment B raw29112step1 raw29112step1Labels = mixedMoment B raw29112step2 raw29112step2Labels := by
      have ha : raw29112step2 = raw29112step1 := by apply Matrix.ext; unfold raw29112step2 raw29112step1; decide +kernel
      have hl : raw29112step1Labels = labelEmbedding1 ∘ raw29112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29112step1 raw29112step1Labels raw29112step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical29113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29113 raw29113Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw29113 raw29113Labels = mixedMoment B raw29113step0 raw29113step0Labels := by
      have hz : ∀ j, raw29113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29113step0 = (fun i j => raw29113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29113step0 raw29113; decide +kernel
      have hl : raw29113step0Labels = raw29113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29113 raw29113Labels permutation434 hz
    mixedMoment B raw29113step0 raw29113step0Labels = mixedMoment B raw29113step1 raw29113step1Labels := by
      have hz : ∀ j, raw29113step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29113step1 = (fun i j => raw29113step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29113step1 raw29113step0; decide +kernel
      have hl : raw29113step1Labels = raw29113step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29113step0 raw29113step0Labels permutation80 hz
    mixedMoment B raw29113step1 raw29113step1Labels = mixedMoment B raw29113step2 raw29113step2Labels := by
      have ha : raw29113step2 = (fun i j => raw29113step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29113step2 raw29113step1; decide +kernel
      have hl : raw29113step2Labels = raw29113step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29113step1 raw29113step1Labels permutation31 permutation7
    mixedMoment B raw29113step2 raw29113step2Labels = mixedMoment B raw29113step3 raw29113step3Labels := by
      have ha : raw29113step3 = raw29113step2 := by apply Matrix.ext; unfold raw29113step3 raw29113step2; decide +kernel
      have hl : raw29113step2Labels = labelEmbedding1 ∘ raw29113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29113step2 raw29113step2Labels raw29113step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2167 node2167Labels := by rfl

theorem canonical29114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29114 raw29114Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw29114 raw29114Labels = mixedMoment B raw29114step0 raw29114step0Labels := by
      have hz : ∀ j, raw29114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29114step0 = (fun i j => raw29114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29114step0 raw29114; decide +kernel
      have hl : raw29114step0Labels = raw29114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29114 raw29114Labels permutation434 hz
    mixedMoment B raw29114step0 raw29114step0Labels = mixedMoment B raw29114step1 raw29114step1Labels := by
      have hz : ∀ j, raw29114step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29114step1 = (fun i j => raw29114step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29114step1 raw29114step0; decide +kernel
      have hl : raw29114step1Labels = raw29114step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29114step0 raw29114step0Labels permutation80 hz
    mixedMoment B raw29114step1 raw29114step1Labels = mixedMoment B raw29114step2 raw29114step2Labels := by
      have ha : raw29114step2 = (fun i j => raw29114step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29114step2 raw29114step1; decide +kernel
      have hl : raw29114step2Labels = raw29114step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29114step1 raw29114step1Labels permutation31 permutation7
    mixedMoment B raw29114step2 raw29114step2Labels = mixedMoment B raw29114step3 raw29114step3Labels := by
      have ha : raw29114step3 = raw29114step2 := by apply Matrix.ext; unfold raw29114step3 raw29114step2; decide +kernel
      have hl : raw29114step2Labels = labelEmbedding1 ∘ raw29114step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29114step2 raw29114step2Labels raw29114step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

theorem canonical29115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29115 raw29115Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw29115 raw29115Labels = mixedMoment B raw29115step0 raw29115step0Labels := by
      have hz : ∀ j, raw29115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29115step0 = (fun i j => raw29115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29115step0 raw29115; decide +kernel
      have hl : raw29115step0Labels = raw29115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29115 raw29115Labels permutation434 hz
    mixedMoment B raw29115step0 raw29115step0Labels = mixedMoment B raw29115step1 raw29115step1Labels := by
      have ha : raw29115step1 = (fun i j => raw29115step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29115step1 raw29115step0; decide +kernel
      have hl : raw29115step1Labels = raw29115step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29115step0 raw29115step0Labels permutation151 permutation7
    mixedMoment B raw29115step1 raw29115step1Labels = mixedMoment B raw29115step2 raw29115step2Labels := by
      have ha : raw29115step2 = raw29115step1 := by apply Matrix.ext; unfold raw29115step2 raw29115step1; decide +kernel
      have hl : raw29115step1Labels = labelEmbedding1 ∘ raw29115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29115step1 raw29115step1Labels raw29115step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

theorem canonical29116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29116 raw29116Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw29116 raw29116Labels = mixedMoment B raw29116step0 raw29116step0Labels := by
      have hz : ∀ j, raw29116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29116step0 = (fun i j => raw29116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29116step0 raw29116; decide +kernel
      have hl : raw29116step0Labels = raw29116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29116 raw29116Labels permutation346 hz
    mixedMoment B raw29116step0 raw29116step0Labels = mixedMoment B raw29116step1 raw29116step1Labels := by
      have ha : raw29116step1 = (fun i j => raw29116step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29116step1 raw29116step0; decide +kernel
      have hl : raw29116step1Labels = raw29116step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29116step0 raw29116step0Labels permutation151 permutation7
    mixedMoment B raw29116step1 raw29116step1Labels = mixedMoment B raw29116step2 raw29116step2Labels := by
      have ha : raw29116step2 = raw29116step1 := by apply Matrix.ext; unfold raw29116step2 raw29116step1; decide +kernel
      have hl : raw29116step1Labels = labelEmbedding1 ∘ raw29116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29116step1 raw29116step1Labels raw29116step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

theorem canonical29117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29117 raw29117Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw29117 raw29117Labels = mixedMoment B raw29117step0 raw29117step0Labels := by
      have hz : ∀ j, raw29117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29117step0 = (fun i j => raw29117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29117step0 raw29117; decide +kernel
      have hl : raw29117step0Labels = raw29117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29117 raw29117Labels permutation434 hz
    mixedMoment B raw29117step0 raw29117step0Labels = mixedMoment B raw29117step1 raw29117step1Labels := by
      have hz : ∀ j, raw29117step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29117step1 = (fun i j => raw29117step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29117step1 raw29117step0; decide +kernel
      have hl : raw29117step1Labels = raw29117step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29117step0 raw29117step0Labels permutation80 hz
    mixedMoment B raw29117step1 raw29117step1Labels = mixedMoment B raw29117step2 raw29117step2Labels := by
      have ha : raw29117step2 = (fun i j => raw29117step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29117step2 raw29117step1; decide +kernel
      have hl : raw29117step2Labels = raw29117step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29117step1 raw29117step1Labels permutation31 permutation7
    mixedMoment B raw29117step2 raw29117step2Labels = mixedMoment B raw29117step3 raw29117step3Labels := by
      have ha : raw29117step3 = raw29117step2 := by apply Matrix.ext; unfold raw29117step3 raw29117step2; decide +kernel
      have hl : raw29117step2Labels = labelEmbedding1 ∘ raw29117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29117step2 raw29117step2Labels raw29117step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

theorem canonical29118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29118 raw29118Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw29118 raw29118Labels = mixedMoment B raw29118step0 raw29118step0Labels := by
      have hz : ∀ j, raw29118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29118step0 = (fun i j => raw29118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29118step0 raw29118; decide +kernel
      have hl : raw29118step0Labels = raw29118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29118 raw29118Labels permutation434 hz
    mixedMoment B raw29118step0 raw29118step0Labels = mixedMoment B raw29118step1 raw29118step1Labels := by
      have hz : ∀ j, raw29118step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29118step1 = (fun i j => raw29118step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29118step1 raw29118step0; decide +kernel
      have hl : raw29118step1Labels = raw29118step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29118step0 raw29118step0Labels permutation80 hz
    mixedMoment B raw29118step1 raw29118step1Labels = mixedMoment B raw29118step2 raw29118step2Labels := by
      have ha : raw29118step2 = (fun i j => raw29118step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29118step2 raw29118step1; decide +kernel
      have hl : raw29118step2Labels = raw29118step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29118step1 raw29118step1Labels permutation31 permutation7
    mixedMoment B raw29118step2 raw29118step2Labels = mixedMoment B raw29118step3 raw29118step3Labels := by
      have ha : raw29118step3 = raw29118step2 := by apply Matrix.ext; unfold raw29118step3 raw29118step2; decide +kernel
      have hl : raw29118step2Labels = labelEmbedding1 ∘ raw29118step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29118step2 raw29118step2Labels raw29118step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical29119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29119 raw29119Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw29119 raw29119Labels = mixedMoment B raw29119step0 raw29119step0Labels := by
      have hz : ∀ j, raw29119 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29119step0 = (fun i j => raw29119 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29119step0 raw29119; decide +kernel
      have hl : raw29119step0Labels = raw29119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29119 raw29119Labels permutation434 hz
    mixedMoment B raw29119step0 raw29119step0Labels = mixedMoment B raw29119step1 raw29119step1Labels := by
      have hz : ∀ j, raw29119step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29119step1 = (fun i j => raw29119step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29119step1 raw29119step0; decide +kernel
      have hl : raw29119step1Labels = raw29119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29119step0 raw29119step0Labels permutation80 hz
    mixedMoment B raw29119step1 raw29119step1Labels = mixedMoment B raw29119step2 raw29119step2Labels := by
      have ha : raw29119step2 = (fun i j => raw29119step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29119step2 raw29119step1; decide +kernel
      have hl : raw29119step2Labels = raw29119step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29119step1 raw29119step1Labels permutation31 permutation7
    mixedMoment B raw29119step2 raw29119step2Labels = mixedMoment B raw29119step3 raw29119step3Labels := by
      have ha : raw29119step3 = raw29119step2 := by apply Matrix.ext; unfold raw29119step3 raw29119step2; decide +kernel
      have hl : raw29119step2Labels = labelEmbedding1 ∘ raw29119step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29119step2 raw29119step2Labels raw29119step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

theorem canonical29120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29120 raw29120Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw29120 raw29120Labels = mixedMoment B raw29120step0 raw29120step0Labels := by
      have hz : ∀ j, raw29120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29120step0 = (fun i j => raw29120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29120step0 raw29120; decide +kernel
      have hl : raw29120step0Labels = raw29120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29120 raw29120Labels permutation434 hz
    mixedMoment B raw29120step0 raw29120step0Labels = mixedMoment B raw29120step1 raw29120step1Labels := by
      have ha : raw29120step1 = (fun i j => raw29120step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29120step1 raw29120step0; decide +kernel
      have hl : raw29120step1Labels = raw29120step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29120step0 raw29120step0Labels permutation151 permutation7
    mixedMoment B raw29120step1 raw29120step1Labels = mixedMoment B raw29120step2 raw29120step2Labels := by
      have ha : raw29120step2 = raw29120step1 := by apply Matrix.ext; unfold raw29120step2 raw29120step1; decide +kernel
      have hl : raw29120step1Labels = labelEmbedding1 ∘ raw29120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29120step1 raw29120step1Labels raw29120step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

theorem canonical29121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29121 raw29121Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw29121 raw29121Labels = mixedMoment B raw29121step0 raw29121step0Labels := by
      have hz : ∀ j, raw29121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29121step0 = (fun i j => raw29121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29121step0 raw29121; decide +kernel
      have hl : raw29121step0Labels = raw29121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29121 raw29121Labels permutation346 hz
    mixedMoment B raw29121step0 raw29121step0Labels = mixedMoment B raw29121step1 raw29121step1Labels := by
      have ha : raw29121step1 = (fun i j => raw29121step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29121step1 raw29121step0; decide +kernel
      have hl : raw29121step1Labels = raw29121step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29121step0 raw29121step0Labels permutation151 permutation7
    mixedMoment B raw29121step1 raw29121step1Labels = mixedMoment B raw29121step2 raw29121step2Labels := by
      have ha : raw29121step2 = raw29121step1 := by apply Matrix.ext; unfold raw29121step2 raw29121step1; decide +kernel
      have hl : raw29121step1Labels = labelEmbedding1 ∘ raw29121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29121step1 raw29121step1Labels raw29121step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

theorem canonical29122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29122 raw29122Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw29122 raw29122Labels = mixedMoment B raw29122step0 raw29122step0Labels := by
      have hz : ∀ j, raw29122 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29122step0 = (fun i j => raw29122 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29122step0 raw29122; decide +kernel
      have hl : raw29122step0Labels = raw29122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29122 raw29122Labels permutation520 hz
    mixedMoment B raw29122step0 raw29122step0Labels = mixedMoment B raw29122step1 raw29122step1Labels := by
      have hz : ∀ j, raw29122step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29122step1 = (fun i j => raw29122step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29122step1 raw29122step0; decide +kernel
      have hl : raw29122step1Labels = raw29122step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29122step0 raw29122step0Labels permutation104 hz
    mixedMoment B raw29122step1 raw29122step1Labels = mixedMoment B raw29122step2 raw29122step2Labels := by
      have hz : ∀ j, raw29122step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29122step2 = (fun i j => raw29122step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29122step2 raw29122step1; decide +kernel
      have hl : raw29122step2Labels = raw29122step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29122step1 raw29122step1Labels permutation20 hz
    mixedMoment B raw29122step2 raw29122step2Labels = mixedMoment B raw29122step3 raw29122step3Labels := by
      have ha : raw29122step3 = (fun i j => raw29122step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29122step3 raw29122step2; decide +kernel
      have hl : raw29122step3Labels = raw29122step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29122step2 raw29122step2Labels permutation7 permutation7
    mixedMoment B raw29122step3 raw29122step3Labels = mixedMoment B raw29122step4 raw29122step4Labels := by
      have ha : raw29122step4 = raw29122step3 := by apply Matrix.ext; unfold raw29122step4 raw29122step3; decide +kernel
      have hl : raw29122step3Labels = labelEmbedding1 ∘ raw29122step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29122step3 raw29122step3Labels raw29122step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1754 node1754Labels := by rfl

theorem canonical29123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29123 raw29123Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw29123 raw29123Labels = mixedMoment B raw29123step0 raw29123step0Labels := by
      have hz : ∀ j, raw29123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29123step0 = (fun i j => raw29123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29123step0 raw29123; decide +kernel
      have hl : raw29123step0Labels = raw29123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29123 raw29123Labels permutation346 hz
    mixedMoment B raw29123step0 raw29123step0Labels = mixedMoment B raw29123step1 raw29123step1Labels := by
      have ha : raw29123step1 = (fun i j => raw29123step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29123step1 raw29123step0; decide +kernel
      have hl : raw29123step1Labels = raw29123step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29123step0 raw29123step0Labels permutation151 permutation2
    mixedMoment B raw29123step1 raw29123step1Labels = mixedMoment B raw29123step2 raw29123step2Labels := by
      have ha : raw29123step2 = -raw29123step1 := by apply Matrix.ext; change ∀ i j, raw29123step2 i j = -(raw29123step1 i j); unfold raw29123step2 raw29123step1; decide +kernel
      have hl : raw29123step2Labels = raw29123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2385 node2385Labels := by rfl

theorem canonical29124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29124 raw29124Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw29124 raw29124Labels = mixedMoment B raw29124step0 raw29124step0Labels := by
      have hz : ∀ j, raw29124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29124step0 = (fun i j => raw29124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29124step0 raw29124; decide +kernel
      have hl : raw29124step0Labels = raw29124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29124 raw29124Labels permutation346 hz
    mixedMoment B raw29124step0 raw29124step0Labels = mixedMoment B raw29124step1 raw29124step1Labels := by
      have ha : raw29124step1 = (fun i j => raw29124step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29124step1 raw29124step0; decide +kernel
      have hl : raw29124step1Labels = raw29124step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29124step0 raw29124step0Labels permutation151 permutation2
    mixedMoment B raw29124step1 raw29124step1Labels = mixedMoment B raw29124step2 raw29124step2Labels := by
      have ha : raw29124step2 = -raw29124step1 := by apply Matrix.ext; change ∀ i j, raw29124step2 i j = -(raw29124step1 i j); unfold raw29124step2 raw29124step1; decide +kernel
      have hl : raw29124step2Labels = raw29124step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2388 node2388Labels := by rfl

theorem canonical29125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29125 raw29125Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw29125 raw29125Labels = mixedMoment B raw29125step0 raw29125step0Labels := by
      have ha : raw29125step0 = (fun i j => raw29125 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29125step0 raw29125; decide +kernel
      have hl : raw29125step0Labels = raw29125Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29125 raw29125Labels permutation688 permutation2
    mixedMoment B raw29125step0 raw29125step0Labels = mixedMoment B raw29125step1 raw29125step1Labels := by
      have ha : raw29125step1 = -raw29125step0 := by apply Matrix.ext; change ∀ i j, raw29125step1 i j = -(raw29125step0 i j); unfold raw29125step1 raw29125step0; decide +kernel
      have hl : raw29125step1Labels = raw29125step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2382 node2382Labels := by rfl

theorem canonical29126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29126 raw29126Labels = mixedMoment B node2403 node2403Labels := by
  calc
    mixedMoment B raw29126 raw29126Labels = mixedMoment B raw29126step0 raw29126step0Labels := by
      have hz : ∀ j, raw29126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29126step0 = (fun i j => raw29126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29126step0 raw29126; decide +kernel
      have hl : raw29126step0Labels = raw29126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29126 raw29126Labels permutation346 hz
    mixedMoment B raw29126step0 raw29126step0Labels = mixedMoment B raw29126step1 raw29126step1Labels := by
      have ha : raw29126step1 = (fun i j => raw29126step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29126step1 raw29126step0; decide +kernel
      have hl : raw29126step1Labels = raw29126step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29126step0 raw29126step0Labels permutation149 permutation2
    mixedMoment B raw29126step1 raw29126step1Labels = mixedMoment B raw29126step2 raw29126step2Labels := by
      have ha : raw29126step2 = -raw29126step1 := by apply Matrix.ext; change ∀ i j, raw29126step2 i j = -(raw29126step1 i j); unfold raw29126step2 raw29126step1; decide +kernel
      have hl : raw29126step2Labels = raw29126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2403 node2403Labels := by rfl

theorem canonical29127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29127 raw29127Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw29127 raw29127Labels = mixedMoment B raw29127step0 raw29127step0Labels := by
      have hz : ∀ j, raw29127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29127step0 = (fun i j => raw29127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29127step0 raw29127; decide +kernel
      have hl : raw29127step0Labels = raw29127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29127 raw29127Labels permutation346 hz
    mixedMoment B raw29127step0 raw29127step0Labels = mixedMoment B raw29127step1 raw29127step1Labels := by
      have ha : raw29127step1 = (fun i j => raw29127step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29127step1 raw29127step0; decide +kernel
      have hl : raw29127step1Labels = raw29127step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29127step0 raw29127step0Labels permutation151 permutation2
    mixedMoment B raw29127step1 raw29127step1Labels = mixedMoment B raw29127step2 raw29127step2Labels := by
      have ha : raw29127step2 = -raw29127step1 := by apply Matrix.ext; change ∀ i j, raw29127step2 i j = -(raw29127step1 i j); unfold raw29127step2 raw29127step1; decide +kernel
      have hl : raw29127step2Labels = raw29127step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical29128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29128 raw29128Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw29128 raw29128Labels = mixedMoment B raw29128step0 raw29128step0Labels := by
      have hz : ∀ j, raw29128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29128step0 = (fun i j => raw29128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29128step0 raw29128; decide +kernel
      have hl : raw29128step0Labels = raw29128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29128 raw29128Labels permutation346 hz
    mixedMoment B raw29128step0 raw29128step0Labels = mixedMoment B raw29128step1 raw29128step1Labels := by
      have ha : raw29128step1 = (fun i j => raw29128step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29128step1 raw29128step0; decide +kernel
      have hl : raw29128step1Labels = raw29128step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29128step0 raw29128step0Labels permutation151 permutation2
    mixedMoment B raw29128step1 raw29128step1Labels = mixedMoment B raw29128step2 raw29128step2Labels := by
      have ha : raw29128step2 = -raw29128step1 := by apply Matrix.ext; change ∀ i j, raw29128step2 i j = -(raw29128step1 i j); unfold raw29128step2 raw29128step1; decide +kernel
      have hl : raw29128step2Labels = raw29128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical29129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29129 raw29129Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw29129 raw29129Labels = mixedMoment B raw29129step0 raw29129step0Labels := by
      have hz : ∀ j, raw29129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29129step0 = (fun i j => raw29129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29129step0 raw29129; decide +kernel
      have hl : raw29129step0Labels = raw29129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29129 raw29129Labels permutation346 hz
    mixedMoment B raw29129step0 raw29129step0Labels = mixedMoment B raw29129step1 raw29129step1Labels := by
      have ha : raw29129step1 = (fun i j => raw29129step0 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29129step1 raw29129step0; decide +kernel
      have hl : raw29129step1Labels = raw29129step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29129step0 raw29129step0Labels permutation125 permutation0
    mixedMoment B raw29129step1 raw29129step1Labels = mixedMoment B raw29129step2 raw29129step2Labels := by
      have ha : raw29129step2 = -raw29129step1 := by apply Matrix.ext; change ∀ i j, raw29129step2 i j = -(raw29129step1 i j); unfold raw29129step2 raw29129step1; decide +kernel
      have hl : raw29129step2Labels = raw29129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical29137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29137 raw29137Labels = mixedMoment B node2468 node2468Labels := by
  calc
    mixedMoment B raw29137 raw29137Labels = mixedMoment B raw29137step0 raw29137step0Labels := by
      have hz : ∀ j, raw29137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29137step0 = (fun i j => raw29137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29137step0 raw29137; decide +kernel
      have hl : raw29137step0Labels = raw29137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29137 raw29137Labels permutation346 hz
    _ = mixedMoment B node2468 node2468Labels := by rfl

theorem canonical29138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29138 raw29138Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw29138 raw29138Labels = mixedMoment B raw29138step0 raw29138step0Labels := by
      have hz : ∀ j, raw29138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29138step0 = (fun i j => raw29138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29138step0 raw29138; decide +kernel
      have hl : raw29138step0Labels = raw29138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29138 raw29138Labels permutation346 hz
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical29139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29139 raw29139Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw29139 raw29139Labels = mixedMoment B raw29139step0 raw29139step0Labels := by
      have ha : raw29139step0 = (fun i j => raw29139 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29139step0 raw29139; decide +kernel
      have hl : raw29139step0Labels = raw29139Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29139 raw29139Labels permutation158 permutation2
    _ = mixedMoment B node2459 node2459Labels := by rfl

theorem canonical29140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29140 raw29140Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw29140 raw29140Labels = mixedMoment B raw29140step0 raw29140step0Labels := by
      have hz : ∀ j, raw29140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29140step0 = (fun i j => raw29140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29140step0 raw29140; decide +kernel
      have hl : raw29140step0Labels = raw29140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29140 raw29140Labels permutation346 hz
    _ = mixedMoment B node2505 node2505Labels := by rfl

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

theorem canonical29248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29248 raw29248Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw29248 raw29248Labels = mixedMoment B raw29248step0 raw29248step0Labels := by
      have hz : ∀ j, raw29248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29248step0 = (fun i j => raw29248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29248step0 raw29248; decide +kernel
      have hl : raw29248step0Labels = raw29248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29248 raw29248Labels permutation434 hz
    mixedMoment B raw29248step0 raw29248step0Labels = mixedMoment B raw29248step1 raw29248step1Labels := by
      have hz : ∀ j, raw29248step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29248step1 = (fun i j => raw29248step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29248step1 raw29248step0; decide +kernel
      have hl : raw29248step1Labels = raw29248step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29248step0 raw29248step0Labels permutation80 hz
    mixedMoment B raw29248step1 raw29248step1Labels = mixedMoment B raw29248step2 raw29248step2Labels := by
      have ha : raw29248step2 = (fun i j => raw29248step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29248step2 raw29248step1; decide +kernel
      have hl : raw29248step2Labels = raw29248step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29248step1 raw29248step1Labels permutation31 permutation7
    mixedMoment B raw29248step2 raw29248step2Labels = mixedMoment B raw29248step3 raw29248step3Labels := by
      have ha : raw29248step3 = raw29248step2 := by apply Matrix.ext; unfold raw29248step3 raw29248step2; decide +kernel
      have hl : raw29248step2Labels = labelEmbedding1 ∘ raw29248step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29248step2 raw29248step2Labels raw29248step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical29249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29249 raw29249Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw29249 raw29249Labels = mixedMoment B raw29249step0 raw29249step0Labels := by
      have hz : ∀ j, raw29249 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29249step0 = (fun i j => raw29249 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29249step0 raw29249; decide +kernel
      have hl : raw29249step0Labels = raw29249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29249 raw29249Labels permutation434 hz
    mixedMoment B raw29249step0 raw29249step0Labels = mixedMoment B raw29249step1 raw29249step1Labels := by
      have ha : raw29249step1 = (fun i j => raw29249step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29249step1 raw29249step0; decide +kernel
      have hl : raw29249step1Labels = raw29249step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29249step0 raw29249step0Labels permutation149 permutation7
    mixedMoment B raw29249step1 raw29249step1Labels = mixedMoment B raw29249step2 raw29249step2Labels := by
      have ha : raw29249step2 = raw29249step1 := by apply Matrix.ext; unfold raw29249step2 raw29249step1; decide +kernel
      have hl : raw29249step1Labels = labelEmbedding1 ∘ raw29249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29249step1 raw29249step1Labels raw29249step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical29250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29250 raw29250Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw29250 raw29250Labels = mixedMoment B raw29250step0 raw29250step0Labels := by
      have hz : ∀ j, raw29250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29250step0 = (fun i j => raw29250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29250step0 raw29250; decide +kernel
      have hl : raw29250step0Labels = raw29250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29250 raw29250Labels permutation346 hz
    mixedMoment B raw29250step0 raw29250step0Labels = mixedMoment B raw29250step1 raw29250step1Labels := by
      have ha : raw29250step1 = (fun i j => raw29250step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29250step1 raw29250step0; decide +kernel
      have hl : raw29250step1Labels = raw29250step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29250step0 raw29250step0Labels permutation149 permutation7
    mixedMoment B raw29250step1 raw29250step1Labels = mixedMoment B raw29250step2 raw29250step2Labels := by
      have ha : raw29250step2 = raw29250step1 := by apply Matrix.ext; unfold raw29250step2 raw29250step1; decide +kernel
      have hl : raw29250step1Labels = labelEmbedding1 ∘ raw29250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29250step1 raw29250step1Labels raw29250step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical29251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29251 raw29251Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw29251 raw29251Labels = mixedMoment B raw29251step0 raw29251step0Labels := by
      have hz : ∀ j, raw29251 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29251step0 = (fun i j => raw29251 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29251step0 raw29251; decide +kernel
      have hl : raw29251step0Labels = raw29251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29251 raw29251Labels permutation520 hz
    mixedMoment B raw29251step0 raw29251step0Labels = mixedMoment B raw29251step1 raw29251step1Labels := by
      have hz : ∀ j, raw29251step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29251step1 = (fun i j => raw29251step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29251step1 raw29251step0; decide +kernel
      have hl : raw29251step1Labels = raw29251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29251step0 raw29251step0Labels permutation104 hz
    mixedMoment B raw29251step1 raw29251step1Labels = mixedMoment B raw29251step2 raw29251step2Labels := by
      have hz : ∀ j, raw29251step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29251step2 = (fun i j => raw29251step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29251step2 raw29251step1; decide +kernel
      have hl : raw29251step2Labels = raw29251step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29251step1 raw29251step1Labels permutation20 hz
    mixedMoment B raw29251step2 raw29251step2Labels = mixedMoment B raw29251step3 raw29251step3Labels := by
      have ha : raw29251step3 = (fun i j => raw29251step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29251step3 raw29251step2; decide +kernel
      have hl : raw29251step3Labels = raw29251step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29251step2 raw29251step2Labels permutation7 permutation7
    mixedMoment B raw29251step3 raw29251step3Labels = mixedMoment B raw29251step4 raw29251step4Labels := by
      have ha : raw29251step4 = raw29251step3 := by apply Matrix.ext; unfold raw29251step4 raw29251step3; decide +kernel
      have hl : raw29251step3Labels = labelEmbedding1 ∘ raw29251step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29251step3 raw29251step3Labels raw29251step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2268 node2268Labels := by rfl

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

theorem canonical29253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29253 raw29253Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw29253 raw29253Labels = mixedMoment B raw29253step0 raw29253step0Labels := by
      have hz : ∀ j, raw29253 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29253step0 = (fun i j => raw29253 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29253step0 raw29253; decide +kernel
      have hl : raw29253step0Labels = raw29253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29253 raw29253Labels permutation434 hz
    mixedMoment B raw29253step0 raw29253step0Labels = mixedMoment B raw29253step1 raw29253step1Labels := by
      have ha : raw29253step1 = (fun i j => raw29253step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29253step1 raw29253step0; decide +kernel
      have hl : raw29253step1Labels = raw29253step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29253step0 raw29253step0Labels permutation32 permutation7
    mixedMoment B raw29253step1 raw29253step1Labels = mixedMoment B raw29253step2 raw29253step2Labels := by
      have ha : raw29253step2 = -raw29253step1 := by apply Matrix.ext; change ∀ i j, raw29253step2 i j = -(raw29253step1 i j); unfold raw29253step2 raw29253step1; decide +kernel
      have hl : raw29253step2Labels = raw29253step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29253step2 raw29253step2Labels = mixedMoment B raw29253step3 raw29253step3Labels := by
      have ha : raw29253step3 = raw29253step2 := by apply Matrix.ext; unfold raw29253step3 raw29253step2; decide +kernel
      have hl : raw29253step2Labels = labelEmbedding1 ∘ raw29253step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29253step2 raw29253step2Labels raw29253step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

theorem canonical29254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29254 raw29254Labels = mixedMoment B node2170 node2170Labels := by
  calc
    mixedMoment B raw29254 raw29254Labels = mixedMoment B raw29254step0 raw29254step0Labels := by
      have ha : raw29254step0 = (fun i j => raw29254 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29254step0 raw29254; decide +kernel
      have hl : raw29254step0Labels = raw29254Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29254 raw29254Labels permutation644 permutation7
    mixedMoment B raw29254step0 raw29254step0Labels = mixedMoment B raw29254step1 raw29254step1Labels := by
      have ha : raw29254step1 = raw29254step0 := by apply Matrix.ext; unfold raw29254step1 raw29254step0; decide +kernel
      have hl : raw29254step0Labels = labelEmbedding1 ∘ raw29254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29254step0 raw29254step0Labels raw29254step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2170 node2170Labels := by rfl

theorem canonical29255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29255 raw29255Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw29255 raw29255Labels = mixedMoment B raw29255step0 raw29255step0Labels := by
      have hz : ∀ j, raw29255 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29255step0 = (fun i j => raw29255 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29255step0 raw29255; decide +kernel
      have hl : raw29255step0Labels = raw29255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29255 raw29255Labels permutation520 hz
    mixedMoment B raw29255step0 raw29255step0Labels = mixedMoment B raw29255step1 raw29255step1Labels := by
      have hz : ∀ j, raw29255step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29255step1 = (fun i j => raw29255step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29255step1 raw29255step0; decide +kernel
      have hl : raw29255step1Labels = raw29255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29255step0 raw29255step0Labels permutation104 hz
    mixedMoment B raw29255step1 raw29255step1Labels = mixedMoment B raw29255step2 raw29255step2Labels := by
      have ha : raw29255step2 = (fun i j => raw29255step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29255step2 raw29255step1; decide +kernel
      have hl : raw29255step2Labels = raw29255step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29255step1 raw29255step1Labels permutation31 permutation7
    mixedMoment B raw29255step2 raw29255step2Labels = mixedMoment B raw29255step3 raw29255step3Labels := by
      have ha : raw29255step3 = raw29255step2 := by apply Matrix.ext; unfold raw29255step3 raw29255step2; decide +kernel
      have hl : raw29255step2Labels = labelEmbedding1 ∘ raw29255step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29255step2 raw29255step2Labels raw29255step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

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

theorem canonical29260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29260 raw29260Labels = mixedMoment B node2159 node2159Labels := by
  calc
    mixedMoment B raw29260 raw29260Labels = mixedMoment B raw29260step0 raw29260step0Labels := by
      have hz : ∀ j, raw29260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29260step0 = (fun i j => raw29260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29260step0 raw29260; decide +kernel
      have hl : raw29260step0Labels = raw29260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29260 raw29260Labels permutation434 hz
    mixedMoment B raw29260step0 raw29260step0Labels = mixedMoment B raw29260step1 raw29260step1Labels := by
      have hz : ∀ j, raw29260step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29260step1 = (fun i j => raw29260step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29260step1 raw29260step0; decide +kernel
      have hl : raw29260step1Labels = raw29260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29260step0 raw29260step0Labels permutation80 hz
    mixedMoment B raw29260step1 raw29260step1Labels = mixedMoment B raw29260step2 raw29260step2Labels := by
      have ha : raw29260step2 = (fun i j => raw29260step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29260step2 raw29260step1; decide +kernel
      have hl : raw29260step2Labels = raw29260step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29260step1 raw29260step1Labels permutation31 permutation7
    mixedMoment B raw29260step2 raw29260step2Labels = mixedMoment B raw29260step3 raw29260step3Labels := by
      have ha : raw29260step3 = raw29260step2 := by apply Matrix.ext; unfold raw29260step3 raw29260step2; decide +kernel
      have hl : raw29260step2Labels = labelEmbedding1 ∘ raw29260step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29260step2 raw29260step2Labels raw29260step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2159 node2159Labels := by rfl

theorem canonical29261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29261 raw29261Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw29261 raw29261Labels = mixedMoment B raw29261step0 raw29261step0Labels := by
      have hz : ∀ j, raw29261 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29261step0 = (fun i j => raw29261 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29261step0 raw29261; decide +kernel
      have hl : raw29261step0Labels = raw29261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29261 raw29261Labels permutation434 hz
    mixedMoment B raw29261step0 raw29261step0Labels = mixedMoment B raw29261step1 raw29261step1Labels := by
      have ha : raw29261step1 = (fun i j => raw29261step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29261step1 raw29261step0; decide +kernel
      have hl : raw29261step1Labels = raw29261step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29261step0 raw29261step0Labels permutation149 permutation7
    mixedMoment B raw29261step1 raw29261step1Labels = mixedMoment B raw29261step2 raw29261step2Labels := by
      have ha : raw29261step2 = raw29261step1 := by apply Matrix.ext; unfold raw29261step2 raw29261step1; decide +kernel
      have hl : raw29261step1Labels = labelEmbedding1 ∘ raw29261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29261step1 raw29261step1Labels raw29261step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

theorem canonical29262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29262 raw29262Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw29262 raw29262Labels = mixedMoment B raw29262step0 raw29262step0Labels := by
      have hz : ∀ j, raw29262 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29262step0 = (fun i j => raw29262 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29262step0 raw29262; decide +kernel
      have hl : raw29262step0Labels = raw29262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29262 raw29262Labels permutation346 hz
    mixedMoment B raw29262step0 raw29262step0Labels = mixedMoment B raw29262step1 raw29262step1Labels := by
      have ha : raw29262step1 = (fun i j => raw29262step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29262step1 raw29262step0; decide +kernel
      have hl : raw29262step1Labels = raw29262step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29262step0 raw29262step0Labels permutation149 permutation7
    mixedMoment B raw29262step1 raw29262step1Labels = mixedMoment B raw29262step2 raw29262step2Labels := by
      have ha : raw29262step2 = raw29262step1 := by apply Matrix.ext; unfold raw29262step2 raw29262step1; decide +kernel
      have hl : raw29262step1Labels = labelEmbedding1 ∘ raw29262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29262step1 raw29262step1Labels raw29262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

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

theorem canonical29264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29264 raw29264Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw29264 raw29264Labels = mixedMoment B raw29264step0 raw29264step0Labels := by
      have hz : ∀ j, raw29264 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29264step0 = (fun i j => raw29264 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29264step0 raw29264; decide +kernel
      have hl : raw29264step0Labels = raw29264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29264 raw29264Labels permutation434 hz
    mixedMoment B raw29264step0 raw29264step0Labels = mixedMoment B raw29264step1 raw29264step1Labels := by
      have hz : ∀ j, raw29264step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29264step1 = (fun i j => raw29264step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29264step1 raw29264step0; decide +kernel
      have hl : raw29264step1Labels = raw29264step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29264step0 raw29264step0Labels permutation80 hz
    mixedMoment B raw29264step1 raw29264step1Labels = mixedMoment B raw29264step2 raw29264step2Labels := by
      have ha : raw29264step2 = (fun i j => raw29264step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29264step2 raw29264step1; decide +kernel
      have hl : raw29264step2Labels = raw29264step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29264step1 raw29264step1Labels permutation31 permutation7
    mixedMoment B raw29264step2 raw29264step2Labels = mixedMoment B raw29264step3 raw29264step3Labels := by
      have ha : raw29264step3 = raw29264step2 := by apply Matrix.ext; unfold raw29264step3 raw29264step2; decide +kernel
      have hl : raw29264step2Labels = labelEmbedding1 ∘ raw29264step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29264step2 raw29264step2Labels raw29264step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

theorem canonical29265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29265 raw29265Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw29265 raw29265Labels = mixedMoment B raw29265step0 raw29265step0Labels := by
      have hz : ∀ j, raw29265 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29265step0 = (fun i j => raw29265 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29265step0 raw29265; decide +kernel
      have hl : raw29265step0Labels = raw29265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29265 raw29265Labels permutation434 hz
    mixedMoment B raw29265step0 raw29265step0Labels = mixedMoment B raw29265step1 raw29265step1Labels := by
      have ha : raw29265step1 = (fun i j => raw29265step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29265step1 raw29265step0; decide +kernel
      have hl : raw29265step1Labels = raw29265step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29265step0 raw29265step0Labels permutation149 permutation7
    mixedMoment B raw29265step1 raw29265step1Labels = mixedMoment B raw29265step2 raw29265step2Labels := by
      have ha : raw29265step2 = raw29265step1 := by apply Matrix.ext; unfold raw29265step2 raw29265step1; decide +kernel
      have hl : raw29265step1Labels = labelEmbedding1 ∘ raw29265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29265step1 raw29265step1Labels raw29265step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

theorem canonical29266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29266 raw29266Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw29266 raw29266Labels = mixedMoment B raw29266step0 raw29266step0Labels := by
      have hz : ∀ j, raw29266 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29266step0 = (fun i j => raw29266 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29266step0 raw29266; decide +kernel
      have hl : raw29266step0Labels = raw29266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29266 raw29266Labels permutation346 hz
    mixedMoment B raw29266step0 raw29266step0Labels = mixedMoment B raw29266step1 raw29266step1Labels := by
      have ha : raw29266step1 = (fun i j => raw29266step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29266step1 raw29266step0; decide +kernel
      have hl : raw29266step1Labels = raw29266step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29266step0 raw29266step0Labels permutation149 permutation7
    mixedMoment B raw29266step1 raw29266step1Labels = mixedMoment B raw29266step2 raw29266step2Labels := by
      have ha : raw29266step2 = raw29266step1 := by apply Matrix.ext; unfold raw29266step2 raw29266step1; decide +kernel
      have hl : raw29266step1Labels = labelEmbedding1 ∘ raw29266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29266step1 raw29266step1Labels raw29266step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

theorem canonical29267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29267 raw29267Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw29267 raw29267Labels = mixedMoment B raw29267step0 raw29267step0Labels := by
      have hz : ∀ j, raw29267 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29267step0 = (fun i j => raw29267 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29267step0 raw29267; decide +kernel
      have hl : raw29267step0Labels = raw29267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29267 raw29267Labels permutation434 hz
    mixedMoment B raw29267step0 raw29267step0Labels = mixedMoment B raw29267step1 raw29267step1Labels := by
      have hz : ∀ j, raw29267step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29267step1 = (fun i j => raw29267step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29267step1 raw29267step0; decide +kernel
      have hl : raw29267step1Labels = raw29267step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29267step0 raw29267step0Labels permutation80 hz
    mixedMoment B raw29267step1 raw29267step1Labels = mixedMoment B raw29267step2 raw29267step2Labels := by
      have ha : raw29267step2 = (fun i j => raw29267step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29267step2 raw29267step1; decide +kernel
      have hl : raw29267step2Labels = raw29267step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29267step1 raw29267step1Labels permutation31 permutation2
    mixedMoment B raw29267step2 raw29267step2Labels = mixedMoment B raw29267step3 raw29267step3Labels := by
      have ha : raw29267step3 = -raw29267step2 := by apply Matrix.ext; change ∀ i j, raw29267step3 i j = -(raw29267step2 i j); unfold raw29267step3 raw29267step2; decide +kernel
      have hl : raw29267step3Labels = raw29267step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2065 node2065Labels := by rfl

theorem canonical29268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29268 raw29268Labels = mixedMoment B node2056 node2056Labels := by
  calc
    mixedMoment B raw29268 raw29268Labels = mixedMoment B raw29268step0 raw29268step0Labels := by
      have hz : ∀ j, raw29268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29268step0 = (fun i j => raw29268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29268step0 raw29268; decide +kernel
      have hl : raw29268step0Labels = raw29268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29268 raw29268Labels permutation434 hz
    mixedMoment B raw29268step0 raw29268step0Labels = mixedMoment B raw29268step1 raw29268step1Labels := by
      have hz : ∀ j, raw29268step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29268step1 = (fun i j => raw29268step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29268step1 raw29268step0; decide +kernel
      have hl : raw29268step1Labels = raw29268step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29268step0 raw29268step0Labels permutation80 hz
    _ = mixedMoment B node2056 node2056Labels := by rfl

theorem canonical29269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29269 raw29269Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw29269 raw29269Labels = mixedMoment B raw29269step0 raw29269step0Labels := by
      have hz : ∀ j, raw29269 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29269step0 = (fun i j => raw29269 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29269step0 raw29269; decide +kernel
      have hl : raw29269step0Labels = raw29269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29269 raw29269Labels permutation434 hz
    _ = mixedMoment B node1804 node1804Labels := by rfl

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

theorem canonical29271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29271 raw29271Labels = mixedMoment B node1817 node1817Labels := by
  calc
    mixedMoment B raw29271 raw29271Labels = mixedMoment B raw29271step0 raw29271step0Labels := by
      have hz : ∀ j, raw29271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29271step0 = (fun i j => raw29271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29271step0 raw29271; decide +kernel
      have hl : raw29271step0Labels = raw29271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29271 raw29271Labels permutation434 hz
    mixedMoment B raw29271step0 raw29271step0Labels = mixedMoment B raw29271step1 raw29271step1Labels := by
      have hz : ∀ j, raw29271step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29271step1 = (fun i j => raw29271step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29271step1 raw29271step0; decide +kernel
      have hl : raw29271step1Labels = raw29271step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29271step0 raw29271step0Labels permutation80 hz
    _ = mixedMoment B node1817 node1817Labels := by rfl

theorem canonical29272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29272 raw29272Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw29272 raw29272Labels = mixedMoment B raw29272step0 raw29272step0Labels := by
      have hz : ∀ j, raw29272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29272step0 = (fun i j => raw29272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29272step0 raw29272; decide +kernel
      have hl : raw29272step0Labels = raw29272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29272 raw29272Labels permutation434 hz
    mixedMoment B raw29272step0 raw29272step0Labels = mixedMoment B raw29272step1 raw29272step1Labels := by
      have hz : ∀ j, raw29272step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29272step1 = (fun i j => raw29272step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29272step1 raw29272step0; decide +kernel
      have hl : raw29272step1Labels = raw29272step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29272step0 raw29272step0Labels permutation80 hz
    mixedMoment B raw29272step1 raw29272step1Labels = mixedMoment B raw29272step2 raw29272step2Labels := by
      have ha : raw29272step2 = (fun i j => raw29272step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29272step2 raw29272step1; decide +kernel
      have hl : raw29272step2Labels = raw29272step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29272step1 raw29272step1Labels permutation31 permutation2
    mixedMoment B raw29272step2 raw29272step2Labels = mixedMoment B raw29272step3 raw29272step3Labels := by
      have ha : raw29272step3 = -raw29272step2 := by apply Matrix.ext; change ∀ i j, raw29272step3 i j = -(raw29272step2 i j); unfold raw29272step3 raw29272step2; decide +kernel
      have hl : raw29272step3Labels = raw29272step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node937 node937Labels := by rfl

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

theorem sound916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node916 node916Labels = Sparse.eval nodeValue916 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 916) = mixedMoment B node916 node916Labels := rfl
  simpa [nodeValue916, Sparse.eval] using hc.symm

theorem sound937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node937 node937Labels = Sparse.eval nodeValue937 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 937) = mixedMoment B node937 node937Labels := rfl
  simpa [nodeValue937, Sparse.eval] using hc.symm

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

theorem sound1123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1123 node1123Labels = Sparse.eval nodeValue1123 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1123) = mixedMoment B node1123 node1123Labels := rfl
  simpa [nodeValue1123, Sparse.eval] using hc.symm

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

theorem sound1666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1666 node1666Labels = Sparse.eval nodeValue1666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1666) = mixedMoment B node1666 node1666Labels := rfl
  simpa [nodeValue1666, Sparse.eval] using hc.symm

theorem sound1674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1674 node1674Labels = Sparse.eval nodeValue1674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1674) = mixedMoment B node1674 node1674Labels := rfl
  simpa [nodeValue1674, Sparse.eval] using hc.symm

theorem sound1677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1677 node1677Labels = Sparse.eval nodeValue1677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1677) = mixedMoment B node1677 node1677Labels := rfl
  simpa [nodeValue1677, Sparse.eval] using hc.symm

theorem sound1683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1683 node1683Labels = Sparse.eval nodeValue1683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1683) = mixedMoment B node1683 node1683Labels := rfl
  simpa [nodeValue1683, Sparse.eval] using hc.symm

theorem sound1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1692 node1692Labels = Sparse.eval nodeValue1692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1692) = mixedMoment B node1692 node1692Labels := rfl
  simpa [nodeValue1692, Sparse.eval] using hc.symm

theorem sound1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1693 node1693Labels = Sparse.eval nodeValue1693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1693) = mixedMoment B node1693 node1693Labels := rfl
  simpa [nodeValue1693, Sparse.eval] using hc.symm

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

theorem zero1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1754 node1754Labels = 0 := by
  exact mixedMoment_order_one B hB node1754 node1754Labels 1
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

theorem sound1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1754 node1754Labels = Sparse.eval nodeValue1754 (mixedVector B) := by
  simpa only [nodeValue1754, Sparse.eval_nil] using zero1754 B _hB _hF

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

theorem sound1799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1799 node1799Labels = Sparse.eval nodeValue1799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1799) = mixedMoment B node1799 node1799Labels := rfl
  simpa [nodeValue1799, Sparse.eval] using hc.symm

theorem sound1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1804 node1804Labels = Sparse.eval nodeValue1804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1804) = mixedMoment B node1804 node1804Labels := rfl
  simpa [nodeValue1804, Sparse.eval] using hc.symm

theorem sound1817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1817 node1817Labels = Sparse.eval nodeValue1817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1817) = mixedMoment B node1817 node1817Labels := rfl
  simpa [nodeValue1817, Sparse.eval] using hc.symm

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

theorem zero1911 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1911 node1911Labels = 0 := by
  exact mixedMoment_order_one B hB node1911 node1911Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1874 node1874Labels = Sparse.eval nodeValue1874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1874) = mixedMoment B node1874 node1874Labels := rfl
  simpa [nodeValue1874, Sparse.eval] using hc.symm

theorem sound1875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1875 node1875Labels = Sparse.eval nodeValue1875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1875) = mixedMoment B node1875 node1875Labels := rfl
  simpa [nodeValue1875, Sparse.eval] using hc.symm

theorem sound1880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1880 node1880Labels = Sparse.eval nodeValue1880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1880) = mixedMoment B node1880 node1880Labels := rfl
  simpa [nodeValue1880, Sparse.eval] using hc.symm

theorem sound1897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1897 node1897Labels = Sparse.eval nodeValue1897 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1897) = mixedMoment B node1897 node1897Labels := rfl
  simpa [nodeValue1897, Sparse.eval] using hc.symm

theorem sound1911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1911 node1911Labels = Sparse.eval nodeValue1911 (mixedVector B) := by
  simpa only [nodeValue1911, Sparse.eval_nil] using zero1911 B _hB _hF

theorem sound1914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1914 node1914Labels = Sparse.eval nodeValue1914 (mixedVector B) := by
  simpa only [nodeValue1914, Sparse.eval_nil] using zero1914 B _hB _hF

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

theorem sound2018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2018 node2018Labels = Sparse.eval nodeValue2018 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2018) = mixedMoment B node2018 node2018Labels := rfl
  simpa [nodeValue2018, Sparse.eval] using hc.symm

theorem sound2047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2047 node2047Labels = Sparse.eval nodeValue2047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2047) = mixedMoment B node2047 node2047Labels := rfl
  simpa [nodeValue2047, Sparse.eval] using hc.symm

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

theorem zero2056 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2056 node2056Labels = 0 := by
  exact mixedMoment_order_one B hB node2056 node2056Labels 1
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

theorem sound2056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2056 node2056Labels = Sparse.eval nodeValue2056 (mixedVector B) := by
  simpa only [nodeValue2056, Sparse.eval_nil] using zero2056 B _hB _hF

theorem sound2065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2065 node2065Labels = Sparse.eval nodeValue2065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2065) = mixedMoment B node2065 node2065Labels := rfl
  simpa [nodeValue2065, Sparse.eval] using hc.symm

theorem sound2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2075 node2075Labels = Sparse.eval nodeValue2075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2075) = mixedMoment B node2075 node2075Labels := rfl
  simpa [nodeValue2075, Sparse.eval] using hc.symm

theorem sound2079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2079 node2079Labels = Sparse.eval nodeValue2079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2079) = mixedMoment B node2079 node2079Labels := rfl
  simpa [nodeValue2079, Sparse.eval] using hc.symm

theorem sound2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2082 node2082Labels = Sparse.eval nodeValue2082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2082) = mixedMoment B node2082 node2082Labels := rfl
  simpa [nodeValue2082, Sparse.eval] using hc.symm

theorem sound2101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2101 node2101Labels = Sparse.eval nodeValue2101 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2101) = mixedMoment B node2101 node2101Labels := rfl
  simpa [nodeValue2101, Sparse.eval] using hc.symm

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

theorem sound2151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2151 node2151Labels = Sparse.eval nodeValue2151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2151) = mixedMoment B node2151 node2151Labels := rfl
  simpa [nodeValue2151, Sparse.eval] using hc.symm

theorem sound2159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2159 node2159Labels = Sparse.eval nodeValue2159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2159) = mixedMoment B node2159 node2159Labels := rfl
  simpa [nodeValue2159, Sparse.eval] using hc.symm

theorem sound2167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2167 node2167Labels = Sparse.eval nodeValue2167 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2167) = mixedMoment B node2167 node2167Labels := rfl
  simpa [nodeValue2167, Sparse.eval] using hc.symm

theorem sound2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2168 node2168Labels = Sparse.eval nodeValue2168 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2168) = mixedMoment B node2168 node2168Labels := rfl
  simpa [nodeValue2168, Sparse.eval] using hc.symm

theorem sound2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2170 node2170Labels = Sparse.eval nodeValue2170 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2170) = mixedMoment B node2170 node2170Labels := rfl
  simpa [nodeValue2170, Sparse.eval] using hc.symm

theorem sound2173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2173 node2173Labels = Sparse.eval nodeValue2173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2173) = mixedMoment B node2173 node2173Labels := rfl
  simpa [nodeValue2173, Sparse.eval] using hc.symm

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

theorem sound2184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2184 node2184Labels = Sparse.eval nodeValue2184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2184) = mixedMoment B node2184 node2184Labels := rfl
  simpa [nodeValue2184, Sparse.eval] using hc.symm

theorem sound2185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2185 node2185Labels = Sparse.eval nodeValue2185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2185) = mixedMoment B node2185 node2185Labels := rfl
  simpa [nodeValue2185, Sparse.eval] using hc.symm

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = Sparse.eval nodeValue2205 (mixedVector B) := by
  simpa only [nodeValue2205, Sparse.eval_nil] using zero2205 B _hB _hF

theorem sound2208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2208 node2208Labels = Sparse.eval nodeValue2208 (mixedVector B) := by
  simpa only [nodeValue2208, Sparse.eval_nil] using zero2208 B _hB _hF

theorem sound2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2218 node2218Labels = Sparse.eval nodeValue2218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2218) = mixedMoment B node2218 node2218Labels := rfl
  simpa [nodeValue2218, Sparse.eval] using hc.symm

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

theorem sound2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = Sparse.eval nodeValue2228 (mixedVector B) := by
  simpa only [nodeValue2228, Sparse.eval_nil] using zero2228 B _hB _hF

theorem sound2229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2229 node2229Labels = Sparse.eval nodeValue2229 (mixedVector B) := by
  simpa only [nodeValue2229, Sparse.eval_nil] using zero2229 B _hB _hF

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

theorem sound2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2268 node2268Labels = Sparse.eval nodeValue2268 (mixedVector B) := by
  simpa only [nodeValue2268, Sparse.eval_nil] using zero2268 B _hB _hF

theorem sound2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = Sparse.eval nodeValue2292 (mixedVector B) := by
  simpa only [nodeValue2292, Sparse.eval_nil] using zero2292 B _hB _hF

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

theorem sound2377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2377 node2377Labels = Sparse.eval nodeValue2377 (mixedVector B) := by
  simpa only [nodeValue2377, Sparse.eval_nil] using zero2377 B _hB _hF

theorem sound2382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2382 node2382Labels = Sparse.eval nodeValue2382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2382) = mixedMoment B node2382 node2382Labels := rfl
  simpa [nodeValue2382, Sparse.eval] using hc.symm

theorem sound2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2385 node2385Labels = Sparse.eval nodeValue2385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2385) = mixedMoment B node2385 node2385Labels := rfl
  simpa [nodeValue2385, Sparse.eval] using hc.symm

theorem sound2388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2388 node2388Labels = Sparse.eval nodeValue2388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2388) = mixedMoment B node2388 node2388Labels := rfl
  simpa [nodeValue2388, Sparse.eval] using hc.symm

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

theorem zero2468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2468 node2468Labels = 0 := by
  exact mixedMoment_order_one B hB node2468 node2468Labels 1
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

theorem sound2449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2449 node2449Labels = Sparse.eval nodeValue2449 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2449) = mixedMoment B node2449 node2449Labels := rfl
  simpa [nodeValue2449, Sparse.eval] using hc.symm

theorem sound2452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2452 node2452Labels = Sparse.eval nodeValue2452 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2452) = mixedMoment B node2452 node2452Labels := rfl
  simpa [nodeValue2452, Sparse.eval] using hc.symm

theorem sound2459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2459 node2459Labels = Sparse.eval nodeValue2459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2459) = mixedMoment B node2459 node2459Labels := rfl
  simpa [nodeValue2459, Sparse.eval] using hc.symm

theorem sound2461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2461 node2461Labels = Sparse.eval nodeValue2461 (mixedVector B) := by
  simpa only [nodeValue2461, Sparse.eval_nil] using zero2461 B _hB _hF

theorem sound2468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2468 node2468Labels = Sparse.eval nodeValue2468 (mixedVector B) := by
  simpa only [nodeValue2468, Sparse.eval_nil] using zero2468 B _hB _hF

theorem sound2477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2477 node2477Labels = Sparse.eval nodeValue2477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2477) = mixedMoment B node2477 node2477Labels := rfl
  simpa [nodeValue2477, Sparse.eval] using hc.symm

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

theorem zero2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2540 node2540Labels = 0 := by
  exact mixedMoment_alpha B hF node2540 node2540Labels 1 permutation161
    (by decide +kernel)

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

theorem sound2505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2505 node2505Labels = Sparse.eval nodeValue2505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2505) = mixedMoment B node2505 node2505Labels := rfl
  simpa [nodeValue2505, Sparse.eval] using hc.symm

theorem sound2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2540 node2540Labels = Sparse.eval nodeValue2540 (mixedVector B) := by
  simpa only [nodeValue2540, Sparse.eval_nil] using zero2540 B _hB _hF

theorem sound2541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2541 node2541Labels = Sparse.eval nodeValue2541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2541) = mixedMoment B node2541 node2541Labels := rfl
  simpa [nodeValue2541, Sparse.eval] using hc.symm

theorem sound2550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2550 node2550Labels = Sparse.eval nodeValue2550 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2550) = mixedMoment B node2550 node2550Labels := rfl
  simpa [nodeValue2550, Sparse.eval] using hc.symm

theorem sound2551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2551 node2551Labels = Sparse.eval nodeValue2551 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2551) = mixedMoment B node2551 node2551Labels := rfl
  simpa [nodeValue2551, Sparse.eval] using hc.symm

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

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

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

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

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

theorem sound2726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2726 node2726Labels = Sparse.eval nodeValue2726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2726) = mixedMoment B node2726 node2726Labels := rfl
  simpa [nodeValue2726, Sparse.eval] using hc.symm

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

theorem sound2742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = Sparse.eval nodeValue2742 (mixedVector B) := by
  simpa only [nodeValue2742, Sparse.eval_nil] using zero2742 B _hB _hF

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

theorem sound3459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3459 node3459Labels = Sparse.eval nodeValue3459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3459) = mixedMoment B node3459 node3459Labels := rfl
  simpa [nodeValue3459, Sparse.eval] using hc.symm

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

theorem sound3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3564 node3564Labels = Sparse.eval nodeValue3564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3564) = mixedMoment B node3564 node3564Labels := rfl
  simpa [nodeValue3564, Sparse.eval] using hc.symm

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

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

theorem sound3766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3766 node3766Labels = Sparse.eval nodeValue3766 (mixedVector B) := by
  simpa only [nodeValue3766, Sparse.eval_nil] using zero3766 B _hB _hF

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

theorem zero3793 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3793 node3793Labels = 0 := by
  exact mixedMoment_order_one B hB node3793 node3793Labels 1
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

theorem sound3793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3793 node3793Labels = Sparse.eval nodeValue3793 (mixedVector B) := by
  simpa only [nodeValue3793, Sparse.eval_nil] using zero3793 B _hB _hF

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

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources64
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2057 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2057 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2057 + difference 0 5) (sourceB2057 + difference 5 0) sourceC2057) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2057 + difference 0 5) (sourceB2057 + difference 5 0) sourceC2057) = raw28989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2057 sourceB2057 sourceC2057 difference raw28989; decide +kernel
    rw [ha]
    exact (canonical28989 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2057 + difference 1 5) (sourceB2057 + difference 5 1) sourceC2057) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2057 + difference 1 5) (sourceB2057 + difference 5 1) sourceC2057) = raw21045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2057 sourceB2057 sourceC2057 difference raw21045; decide +kernel
    rw [ha]
    exact (canonical21045 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2057 + difference 2 5) (sourceB2057 + difference 5 2) sourceC2057) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2551) := by
    have ha : (tripleCharges (sourceA2057 + difference 2 5) (sourceB2057 + difference 5 2) sourceC2057) = raw28990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2057 sourceB2057 sourceC2057 difference raw28990; decide +kernel
    rw [ha]
    exact (canonical28990 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2057 + difference 3 5) (sourceB2057 + difference 5 3) sourceC2057) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2551) := by
    have ha : (tripleCharges (sourceA2057 + difference 3 5) (sourceB2057 + difference 5 3) sourceC2057) = raw28991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2057 sourceB2057 sourceC2057 difference raw28991; decide +kernel
    rw [ha]
    exact (canonical28991 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2057 + difference 4 5) (sourceB2057 + difference 5 4) sourceC2057) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2541) := by
    have ha : (tripleCharges (sourceA2057 + difference 4 5) (sourceB2057 + difference 5 4) sourceC2057) = raw22871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2057 sourceB2057 sourceC2057 difference raw22871; decide +kernel
    rw [ha]
    exact (canonical22871 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2057 + difference 5 5) (sourceB2057 + difference 5 5) sourceC2057) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2377) := by
    have ha : (tripleCharges (sourceA2057 + difference 5 5) (sourceB2057 + difference 5 5) sourceC2057) = raw21041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2057 sourceB2057 sourceC2057 difference raw21041; decide +kernel
    rw [ha]
    exact (canonical21041 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2057 + sourceB2057) sourceC2057) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2057 + sourceB2057) sourceC2057) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA2057 sourceB2057 sourceC2057 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2057 sourceB2057 sourceC2057
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2057, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2059 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2059 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2059 + difference 0 5) (sourceB2059 + difference 5 0) sourceC2059) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA2059 + difference 0 5) (sourceB2059 + difference 5 0) sourceC2059) = raw28996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2059 sourceB2059 sourceC2059 difference raw28996; decide +kernel
    rw [ha]
    exact (canonical28996 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2059 + difference 1 5) (sourceB2059 + difference 5 1) sourceC2059) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2059 + difference 1 5) (sourceB2059 + difference 5 1) sourceC2059) = raw21056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2059 sourceB2059 sourceC2059 difference raw21056; decide +kernel
    rw [ha]
    exact (canonical21056 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2059 + difference 2 5) (sourceB2059 + difference 5 2) sourceC2059) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2550) := by
    have ha : (tripleCharges (sourceA2059 + difference 2 5) (sourceB2059 + difference 5 2) sourceC2059) = raw28997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2059 sourceB2059 sourceC2059 difference raw28997; decide +kernel
    rw [ha]
    exact (canonical28997 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2059 + difference 3 5) (sourceB2059 + difference 5 3) sourceC2059) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2550) := by
    have ha : (tripleCharges (sourceA2059 + difference 3 5) (sourceB2059 + difference 5 3) sourceC2059) = raw28998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2059 sourceB2059 sourceC2059 difference raw28998; decide +kernel
    rw [ha]
    exact (canonical28998 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2059 + difference 4 5) (sourceB2059 + difference 5 4) sourceC2059) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2540) := by
    have ha : (tripleCharges (sourceA2059 + difference 4 5) (sourceB2059 + difference 5 4) sourceC2059) = raw28999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2059 sourceB2059 sourceC2059 difference raw28999; decide +kernel
    rw [ha]
    exact (canonical28999 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2059 + difference 5 5) (sourceB2059 + difference 5 5) sourceC2059) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1897) := by
    have ha : (tripleCharges (sourceA2059 + difference 5 5) (sourceB2059 + difference 5 5) sourceC2059) = raw21052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2059 sourceB2059 sourceC2059 difference raw21052; decide +kernel
    rw [ha]
    exact (canonical21052 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2059 + sourceB2059) sourceC2059) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2059 + sourceB2059) sourceC2059) = raw21057 := by
      apply Matrix.ext; unfold doubleCharges sourceA2059 sourceB2059 sourceC2059 raw21057; decide +kernel
    rw [ha]
    exact (canonical21057 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2059 sourceB2059 sourceC2059
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2059, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2061 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2061 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2061 + difference 0 0) (sourceB2061 + difference 0 0) sourceC2061) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA2061 + difference 0 0) (sourceB2061 + difference 0 0) sourceC2061) = raw29005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2061 sourceB2061 sourceC2061 difference raw29005; decide +kernel
    rw [ha]
    exact (canonical29005 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2061 + difference 0 1) (sourceB2061 + difference 1 0) sourceC2061) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2061 + difference 0 1) (sourceB2061 + difference 1 0) sourceC2061) = raw29006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2061 sourceB2061 sourceC2061 difference raw29006; decide +kernel
    rw [ha]
    exact (canonical29006 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2061 + difference 0 2) (sourceB2061 + difference 2 0) sourceC2061) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2101) := by
    have ha : (tripleCharges (sourceA2061 + difference 0 2) (sourceB2061 + difference 2 0) sourceC2061) = raw29007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2061 sourceB2061 sourceC2061 difference raw29007; decide +kernel
    rw [ha]
    exact (canonical29007 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2061 + difference 0 3) (sourceB2061 + difference 3 0) sourceC2061) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2075) := by
    have ha : (tripleCharges (sourceA2061 + difference 0 3) (sourceB2061 + difference 3 0) sourceC2061) = raw29008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2061 sourceB2061 sourceC2061 difference raw29008; decide +kernel
    rw [ha]
    exact (canonical29008 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2061 + difference 0 4) (sourceB2061 + difference 4 0) sourceC2061) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2061 + difference 0 4) (sourceB2061 + difference 4 0) sourceC2061) = raw29009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2061 sourceB2061 sourceC2061 difference raw29009; decide +kernel
    rw [ha]
    exact (canonical29009 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2061 + difference 0 5) (sourceB2061 + difference 5 0) sourceC2061) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2061 + difference 0 5) (sourceB2061 + difference 5 0) sourceC2061) = raw29010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2061 sourceB2061 sourceC2061 difference raw29010; decide +kernel
    rw [ha]
    exact (canonical29010 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2061 + sourceB2061) sourceC2061) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2061 + sourceB2061) sourceC2061) = raw29011 := by
      apply Matrix.ext; unfold doubleCharges sourceA2061 sourceB2061 sourceC2061 raw29011; decide +kernel
    rw [ha]
    exact (canonical29011 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2061 sourceB2061 sourceC2061
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2061, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2062 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2062 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2062 + difference 2 0) (sourceB2062 + difference 0 2) sourceC2062) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA2062 + difference 2 0) (sourceB2062 + difference 0 2) sourceC2062) = raw29012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2062 sourceB2062 sourceC2062 difference raw29012; decide +kernel
    rw [ha]
    exact (canonical29012 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2062 + difference 2 1) (sourceB2062 + difference 1 2) sourceC2062) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2062 + difference 2 1) (sourceB2062 + difference 1 2) sourceC2062) = raw29013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2062 sourceB2062 sourceC2062 difference raw29013; decide +kernel
    rw [ha]
    exact (canonical29013 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2062 + difference 2 2) (sourceB2062 + difference 2 2) sourceC2062) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA2062 + difference 2 2) (sourceB2062 + difference 2 2) sourceC2062) = raw29005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2062 sourceB2062 sourceC2062 difference raw29005; decide +kernel
    rw [ha]
    exact (canonical29005 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2062 + difference 2 3) (sourceB2062 + difference 3 2) sourceC2062) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1875) := by
    have ha : (tripleCharges (sourceA2062 + difference 2 3) (sourceB2062 + difference 3 2) sourceC2062) = raw29014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2062 sourceB2062 sourceC2062 difference raw29014; decide +kernel
    rw [ha]
    exact (canonical29014 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2062 + difference 2 4) (sourceB2062 + difference 4 2) sourceC2062) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA2062 + difference 2 4) (sourceB2062 + difference 4 2) sourceC2062) = raw29015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2062 sourceB2062 sourceC2062 difference raw29015; decide +kernel
    rw [ha]
    exact (canonical29015 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2062 + difference 2 5) (sourceB2062 + difference 5 2) sourceC2062) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2504) := by
    have ha : (tripleCharges (sourceA2062 + difference 2 5) (sourceB2062 + difference 5 2) sourceC2062) = raw29016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2062 sourceB2062 sourceC2062 difference raw29016; decide +kernel
    rw [ha]
    exact (canonical29016 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2062 + sourceB2062) sourceC2062) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2062 + sourceB2062) sourceC2062) = raw29011 := by
      apply Matrix.ext; unfold doubleCharges sourceA2062 sourceB2062 sourceC2062 raw29011; decide +kernel
    rw [ha]
    exact (canonical29011 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2062 sourceB2062 sourceC2062
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2062, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2064 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2064 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2064 + difference 0 0) (sourceB2064 + difference 0 0) sourceC2064) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2047) := by
    have ha : (tripleCharges (sourceA2064 + difference 0 0) (sourceB2064 + difference 0 0) sourceC2064) = raw29020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2064 sourceB2064 sourceC2064 difference raw29020; decide +kernel
    rw [ha]
    exact (canonical29020 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2064 + difference 1 0) (sourceB2064 + difference 0 1) sourceC2064) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA2064 + difference 1 0) (sourceB2064 + difference 0 1) sourceC2064) = raw29021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2064 sourceB2064 sourceC2064 difference raw29021; decide +kernel
    rw [ha]
    exact (canonical29021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2064 + difference 2 0) (sourceB2064 + difference 0 2) sourceC2064) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1799) := by
    have ha : (tripleCharges (sourceA2064 + difference 2 0) (sourceB2064 + difference 0 2) sourceC2064) = raw29022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2064 sourceB2064 sourceC2064 difference raw29022; decide +kernel
    rw [ha]
    exact (canonical29022 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2064 + difference 3 0) (sourceB2064 + difference 0 3) sourceC2064) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1874) := by
    have ha : (tripleCharges (sourceA2064 + difference 3 0) (sourceB2064 + difference 0 3) sourceC2064) = raw29023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2064 sourceB2064 sourceC2064 difference raw29023; decide +kernel
    rw [ha]
    exact (canonical29023 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2064 + difference 4 0) (sourceB2064 + difference 0 4) sourceC2064) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA2064 + difference 4 0) (sourceB2064 + difference 0 4) sourceC2064) = raw29024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2064 sourceB2064 sourceC2064 difference raw29024; decide +kernel
    rw [ha]
    exact (canonical29024 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2064 + difference 5 0) (sourceB2064 + difference 0 5) sourceC2064) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 916) := by
    have ha : (tripleCharges (sourceA2064 + difference 5 0) (sourceB2064 + difference 0 5) sourceC2064) = raw29025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2064 sourceB2064 sourceC2064 difference raw29025; decide +kernel
    rw [ha]
    exact (canonical29025 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2064 + sourceB2064) sourceC2064) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA2064 + sourceB2064) sourceC2064) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2064 sourceB2064 sourceC2064 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2064 sourceB2064 sourceC2064
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2064, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2065 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2065 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2065 + difference 0 0) (sourceB2065 + difference 0 0) sourceC2065) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA2065 + difference 0 0) (sourceB2065 + difference 0 0) sourceC2065) = raw29026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2065 sourceB2065 sourceC2065 difference raw29026; decide +kernel
    rw [ha]
    exact (canonical29026 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2065 + difference 0 1) (sourceB2065 + difference 1 0) sourceC2065) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2065 + difference 0 1) (sourceB2065 + difference 1 0) sourceC2065) = raw29027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2065 sourceB2065 sourceC2065 difference raw29027; decide +kernel
    rw [ha]
    exact (canonical29027 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2065 + difference 0 2) (sourceB2065 + difference 2 0) sourceC2065) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA2065 + difference 0 2) (sourceB2065 + difference 2 0) sourceC2065) = raw29028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2065 sourceB2065 sourceC2065 difference raw29028; decide +kernel
    rw [ha]
    exact (canonical29028 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2065 + difference 0 3) (sourceB2065 + difference 3 0) sourceC2065) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2461) := by
    have ha : (tripleCharges (sourceA2065 + difference 0 3) (sourceB2065 + difference 3 0) sourceC2065) = raw29029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2065 sourceB2065 sourceC2065 difference raw29029; decide +kernel
    rw [ha]
    exact (canonical29029 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2065 + difference 0 4) (sourceB2065 + difference 4 0) sourceC2065) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA2065 + difference 0 4) (sourceB2065 + difference 4 0) sourceC2065) = raw29030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2065 sourceB2065 sourceC2065 difference raw29030; decide +kernel
    rw [ha]
    exact (canonical29030 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2065 + difference 0 5) (sourceB2065 + difference 5 0) sourceC2065) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3793) := by
    have ha : (tripleCharges (sourceA2065 + difference 0 5) (sourceB2065 + difference 5 0) sourceC2065) = raw29031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2065 sourceB2065 sourceC2065 difference raw29031; decide +kernel
    rw [ha]
    exact (canonical29031 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2065 + sourceB2065) sourceC2065) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2065 + sourceB2065) sourceC2065) = raw29032 := by
      apply Matrix.ext; unfold doubleCharges sourceA2065 sourceB2065 sourceC2065 raw29032; decide +kernel
    rw [ha]
    exact (canonical29032 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2065 sourceB2065 sourceC2065
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2065, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2073 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2073 + difference 0 1) (sourceB2073 + difference 1 0) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2073 + difference 0 1) (sourceB2073 + difference 1 0) sourceC2073) = raw29093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29093; decide +kernel
    rw [ha]
    exact (canonical29093 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2073 + difference 0 2) (sourceB2073 + difference 2 0) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2073 + difference 0 2) (sourceB2073 + difference 2 0) sourceC2073) = raw29094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29094; decide +kernel
    rw [ha]
    exact (canonical29094 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2073 + difference 0 3) (sourceB2073 + difference 3 0) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2073 + difference 0 3) (sourceB2073 + difference 3 0) sourceC2073) = raw29095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29095; decide +kernel
    rw [ha]
    exact (canonical29095 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2073 + difference 0 4) (sourceB2073 + difference 4 0) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2073 + difference 0 4) (sourceB2073 + difference 4 0) sourceC2073) = raw29096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29096; decide +kernel
    rw [ha]
    exact (canonical29096 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2073 + difference 0 5) (sourceB2073 + difference 5 0) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2073 + difference 0 5) (sourceB2073 + difference 5 0) sourceC2073) = raw29097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29097; decide +kernel
    rw [ha]
    exact (canonical29097 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2073 + difference 1 0) (sourceB2073 + difference 0 1) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA2073 + difference 1 0) (sourceB2073 + difference 0 1) sourceC2073) = raw29098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29098; decide +kernel
    rw [ha]
    exact (canonical29098 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2073 + difference 1 2) (sourceB2073 + difference 2 1) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2073 + difference 1 2) (sourceB2073 + difference 2 1) sourceC2073) = raw29099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29099; decide +kernel
    rw [ha]
    exact (canonical29099 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2073 + difference 1 3) (sourceB2073 + difference 3 1) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2073 + difference 1 3) (sourceB2073 + difference 3 1) sourceC2073) = raw29100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29100; decide +kernel
    rw [ha]
    exact (canonical29100 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2073 + difference 1 4) (sourceB2073 + difference 4 1) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA2073 + difference 1 4) (sourceB2073 + difference 4 1) sourceC2073) = raw29101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29101; decide +kernel
    rw [ha]
    exact (canonical29101 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2073 + difference 1 5) (sourceB2073 + difference 5 1) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA2073 + difference 1 5) (sourceB2073 + difference 5 1) sourceC2073) = raw29102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29102; decide +kernel
    rw [ha]
    exact (canonical29102 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2073 + difference 2 0) (sourceB2073 + difference 0 2) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA2073 + difference 2 0) (sourceB2073 + difference 0 2) sourceC2073) = raw29103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29103; decide +kernel
    rw [ha]
    exact (canonical29103 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2073 + difference 2 1) (sourceB2073 + difference 1 2) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2073 + difference 2 1) (sourceB2073 + difference 1 2) sourceC2073) = raw29104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29104; decide +kernel
    rw [ha]
    exact (canonical29104 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2073 + difference 2 3) (sourceB2073 + difference 3 2) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2173) := by
    have ha : (tripleCharges (sourceA2073 + difference 2 3) (sourceB2073 + difference 3 2) sourceC2073) = raw29105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29105; decide +kernel
    rw [ha]
    exact (canonical29105 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2073 + difference 2 4) (sourceB2073 + difference 4 2) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2073 + difference 2 4) (sourceB2073 + difference 4 2) sourceC2073) = raw29106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29106; decide +kernel
    rw [ha]
    exact (canonical29106 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2073 + difference 2 5) (sourceB2073 + difference 5 2) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2073 + difference 2 5) (sourceB2073 + difference 5 2) sourceC2073) = raw29107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29107; decide +kernel
    rw [ha]
    exact (canonical29107 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2073 + difference 3 0) (sourceB2073 + difference 0 3) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA2073 + difference 3 0) (sourceB2073 + difference 0 3) sourceC2073) = raw29108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29108; decide +kernel
    rw [ha]
    exact (canonical29108 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2073 + difference 3 1) (sourceB2073 + difference 1 3) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2073 + difference 3 1) (sourceB2073 + difference 1 3) sourceC2073) = raw29109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29109; decide +kernel
    rw [ha]
    exact (canonical29109 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2073 + difference 3 2) (sourceB2073 + difference 2 3) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2173) := by
    have ha : (tripleCharges (sourceA2073 + difference 3 2) (sourceB2073 + difference 2 3) sourceC2073) = raw29110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29110; decide +kernel
    rw [ha]
    exact (canonical29110 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2073 + difference 3 4) (sourceB2073 + difference 4 3) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2073 + difference 3 4) (sourceB2073 + difference 4 3) sourceC2073) = raw29111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29111; decide +kernel
    rw [ha]
    exact (canonical29111 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2073 + difference 3 5) (sourceB2073 + difference 5 3) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2073 + difference 3 5) (sourceB2073 + difference 5 3) sourceC2073) = raw29112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29112; decide +kernel
    rw [ha]
    exact (canonical29112 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2073 + difference 4 0) (sourceB2073 + difference 0 4) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2073 + difference 4 0) (sourceB2073 + difference 0 4) sourceC2073) = raw29113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29113; decide +kernel
    rw [ha]
    exact (canonical29113 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2073 + difference 4 1) (sourceB2073 + difference 1 4) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2073 + difference 4 1) (sourceB2073 + difference 1 4) sourceC2073) = raw29114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29114; decide +kernel
    rw [ha]
    exact (canonical29114 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2073 + difference 4 2) (sourceB2073 + difference 2 4) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2073 + difference 4 2) (sourceB2073 + difference 2 4) sourceC2073) = raw29115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29115; decide +kernel
    rw [ha]
    exact (canonical29115 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2073 + difference 4 3) (sourceB2073 + difference 3 4) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2073 + difference 4 3) (sourceB2073 + difference 3 4) sourceC2073) = raw29116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29116; decide +kernel
    rw [ha]
    exact (canonical29116 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2073 + difference 4 5) (sourceB2073 + difference 5 4) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA2073 + difference 4 5) (sourceB2073 + difference 5 4) sourceC2073) = raw29117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29117; decide +kernel
    rw [ha]
    exact (canonical29117 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2073 + difference 5 0) (sourceB2073 + difference 0 5) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA2073 + difference 5 0) (sourceB2073 + difference 0 5) sourceC2073) = raw29118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29118; decide +kernel
    rw [ha]
    exact (canonical29118 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2073 + difference 5 1) (sourceB2073 + difference 1 5) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2073 + difference 5 1) (sourceB2073 + difference 1 5) sourceC2073) = raw29119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29119; decide +kernel
    rw [ha]
    exact (canonical29119 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2073 + difference 5 2) (sourceB2073 + difference 2 5) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA2073 + difference 5 2) (sourceB2073 + difference 2 5) sourceC2073) = raw29120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29120; decide +kernel
    rw [ha]
    exact (canonical29120 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2073 + difference 5 3) (sourceB2073 + difference 3 5) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA2073 + difference 5 3) (sourceB2073 + difference 3 5) sourceC2073) = raw29121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29121; decide +kernel
    rw [ha]
    exact (canonical29121 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2073 + difference 5 4) (sourceB2073 + difference 4 5) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA2073 + difference 5 4) (sourceB2073 + difference 4 5) sourceC2073) = raw29122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29122; decide +kernel
    rw [ha]
    exact (canonical29122 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2073 sourceB2073 sourceC2073
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2073, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2074 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2074 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2074 + difference 0 0) (sourceB2074 + difference 0 0) sourceC2074) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA2074 + difference 0 0) (sourceB2074 + difference 0 0) sourceC2074) = raw29123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2074 sourceB2074 sourceC2074 difference raw29123; decide +kernel
    rw [ha]
    exact (canonical29123 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2074 + difference 0 1) (sourceB2074 + difference 1 0) sourceC2074) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA2074 + difference 0 1) (sourceB2074 + difference 1 0) sourceC2074) = raw29124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2074 sourceB2074 sourceC2074 difference raw29124; decide +kernel
    rw [ha]
    exact (canonical29124 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2074 + difference 0 2) (sourceB2074 + difference 2 0) sourceC2074) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2382) := by
    have ha : (tripleCharges (sourceA2074 + difference 0 2) (sourceB2074 + difference 2 0) sourceC2074) = raw29125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2074 sourceB2074 sourceC2074 difference raw29125; decide +kernel
    rw [ha]
    exact (canonical29125 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2074 + difference 0 3) (sourceB2074 + difference 3 0) sourceC2074) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2403) := by
    have ha : (tripleCharges (sourceA2074 + difference 0 3) (sourceB2074 + difference 3 0) sourceC2074) = raw29126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2074 sourceB2074 sourceC2074 difference raw29126; decide +kernel
    rw [ha]
    exact (canonical29126 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2074 + difference 0 4) (sourceB2074 + difference 4 0) sourceC2074) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2074 + difference 0 4) (sourceB2074 + difference 4 0) sourceC2074) = raw29127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2074 sourceB2074 sourceC2074 difference raw29127; decide +kernel
    rw [ha]
    exact (canonical29127 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2074 + difference 0 5) (sourceB2074 + difference 5 0) sourceC2074) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2074 + difference 0 5) (sourceB2074 + difference 5 0) sourceC2074) = raw29128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2074 sourceB2074 sourceC2074 difference raw29128; decide +kernel
    rw [ha]
    exact (canonical29128 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2074 + sourceB2074) sourceC2074) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2074 + sourceB2074) sourceC2074) = raw29129 := by
      apply Matrix.ext; unfold doubleCharges sourceA2074 sourceB2074 sourceC2074 raw29129; decide +kernel
    rw [ha]
    exact (canonical29129 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2074 sourceB2074 sourceC2074
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2074, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2077 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2077 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2077 + difference 0 5) (sourceB2077 + difference 5 0) sourceC2077) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2077 + difference 0 5) (sourceB2077 + difference 5 0) sourceC2077) = raw29128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2077 sourceB2077 sourceC2077 difference raw29128; decide +kernel
    rw [ha]
    exact (canonical29128 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2077 + difference 1 5) (sourceB2077 + difference 5 1) sourceC2077) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2077 + difference 1 5) (sourceB2077 + difference 5 1) sourceC2077) = raw29138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2077 sourceB2077 sourceC2077 difference raw29138; decide +kernel
    rw [ha]
    exact (canonical29138 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2077 + difference 2 5) (sourceB2077 + difference 5 2) sourceC2077) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA2077 + difference 2 5) (sourceB2077 + difference 5 2) sourceC2077) = raw29139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2077 sourceB2077 sourceC2077 difference raw29139; decide +kernel
    rw [ha]
    exact (canonical29139 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2077 + difference 3 5) (sourceB2077 + difference 5 3) sourceC2077) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA2077 + difference 3 5) (sourceB2077 + difference 5 3) sourceC2077) = raw29140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2077 sourceB2077 sourceC2077 difference raw29140; decide +kernel
    rw [ha]
    exact (canonical29140 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2077 + difference 4 5) (sourceB2077 + difference 5 4) sourceC2077) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2468) := by
    have ha : (tripleCharges (sourceA2077 + difference 4 5) (sourceB2077 + difference 5 4) sourceC2077) = raw29137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2077 sourceB2077 sourceC2077 difference raw29137; decide +kernel
    rw [ha]
    exact (canonical29137 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2077 + difference 5 5) (sourceB2077 + difference 5 5) sourceC2077) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA2077 + difference 5 5) (sourceB2077 + difference 5 5) sourceC2077) = raw29123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2077 sourceB2077 sourceC2077 difference raw29123; decide +kernel
    rw [ha]
    exact (canonical29123 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2077 + sourceB2077) sourceC2077) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2077 + sourceB2077) sourceC2077) = raw29129 := by
      apply Matrix.ext; unfold doubleCharges sourceA2077 sourceB2077 sourceC2077 raw29129; decide +kernel
    rw [ha]
    exact (canonical29129 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2077 sourceB2077 sourceC2077
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2077, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources65
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2086 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2086 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2086 + difference 0 1) (sourceB2086 + difference 1 0) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2086 + difference 0 1) (sourceB2086 + difference 1 0) sourceC2086) = raw29248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29248; decide +kernel
    rw [ha]
    exact (canonical29248 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2086 + difference 0 2) (sourceB2086 + difference 2 0) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2086 + difference 0 2) (sourceB2086 + difference 2 0) sourceC2086) = raw29249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29249; decide +kernel
    rw [ha]
    exact (canonical29249 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2086 + difference 0 3) (sourceB2086 + difference 3 0) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2086 + difference 0 3) (sourceB2086 + difference 3 0) sourceC2086) = raw29250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29250; decide +kernel
    rw [ha]
    exact (canonical29250 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2086 + difference 0 4) (sourceB2086 + difference 4 0) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA2086 + difference 0 4) (sourceB2086 + difference 4 0) sourceC2086) = raw29251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29251; decide +kernel
    rw [ha]
    exact (canonical29251 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2086 + difference 0 5) (sourceB2086 + difference 5 0) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA2086 + difference 0 5) (sourceB2086 + difference 5 0) sourceC2086) = raw29252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29252; decide +kernel
    rw [ha]
    exact (canonical29252 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2086 + difference 1 0) (sourceB2086 + difference 0 1) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA2086 + difference 1 0) (sourceB2086 + difference 0 1) sourceC2086) = raw19941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw19941; decide +kernel
    rw [ha]
    exact (canonical19941 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2086 + difference 1 2) (sourceB2086 + difference 2 1) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2086 + difference 1 2) (sourceB2086 + difference 2 1) sourceC2086) = raw21854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw21854; decide +kernel
    rw [ha]
    exact (canonical21854 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2086 + difference 1 3) (sourceB2086 + difference 3 1) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2086 + difference 1 3) (sourceB2086 + difference 3 1) sourceC2086) = raw21855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw21855; decide +kernel
    rw [ha]
    exact (canonical21855 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2086 + difference 1 4) (sourceB2086 + difference 4 1) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA2086 + difference 1 4) (sourceB2086 + difference 4 1) sourceC2086) = raw19921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw19921; decide +kernel
    rw [ha]
    exact (canonical19921 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2086 + difference 1 5) (sourceB2086 + difference 5 1) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA2086 + difference 1 5) (sourceB2086 + difference 5 1) sourceC2086) = raw21856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw21856; decide +kernel
    rw [ha]
    exact (canonical21856 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2086 + difference 2 0) (sourceB2086 + difference 0 2) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA2086 + difference 2 0) (sourceB2086 + difference 0 2) sourceC2086) = raw21862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw21862; decide +kernel
    rw [ha]
    exact (canonical21862 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2086 + difference 2 1) (sourceB2086 + difference 1 2) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2086 + difference 2 1) (sourceB2086 + difference 1 2) sourceC2086) = raw29253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29253; decide +kernel
    rw [ha]
    exact (canonical29253 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2086 + difference 2 3) (sourceB2086 + difference 3 2) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2170) := by
    have ha : (tripleCharges (sourceA2086 + difference 2 3) (sourceB2086 + difference 3 2) sourceC2086) = raw29254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29254; decide +kernel
    rw [ha]
    exact (canonical29254 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2086 + difference 2 4) (sourceB2086 + difference 4 2) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2086 + difference 2 4) (sourceB2086 + difference 4 2) sourceC2086) = raw29255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29255; decide +kernel
    rw [ha]
    exact (canonical29255 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2086 + difference 2 5) (sourceB2086 + difference 5 2) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2086 + difference 2 5) (sourceB2086 + difference 5 2) sourceC2086) = raw29256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29256; decide +kernel
    rw [ha]
    exact (canonical29256 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2086 + difference 3 0) (sourceB2086 + difference 0 3) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA2086 + difference 3 0) (sourceB2086 + difference 0 3) sourceC2086) = raw21866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw21866; decide +kernel
    rw [ha]
    exact (canonical21866 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2086 + difference 3 1) (sourceB2086 + difference 1 3) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2086 + difference 3 1) (sourceB2086 + difference 1 3) sourceC2086) = raw29257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29257; decide +kernel
    rw [ha]
    exact (canonical29257 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2086 + difference 3 2) (sourceB2086 + difference 2 3) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2170) := by
    have ha : (tripleCharges (sourceA2086 + difference 3 2) (sourceB2086 + difference 2 3) sourceC2086) = raw29258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29258; decide +kernel
    rw [ha]
    exact (canonical29258 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2086 + difference 3 4) (sourceB2086 + difference 4 3) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2086 + difference 3 4) (sourceB2086 + difference 4 3) sourceC2086) = raw29259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29259; decide +kernel
    rw [ha]
    exact (canonical29259 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2086 + difference 3 5) (sourceB2086 + difference 5 3) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2086 + difference 3 5) (sourceB2086 + difference 5 3) sourceC2086) = raw25973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw25973; decide +kernel
    rw [ha]
    exact (canonical25973 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2086 + difference 4 0) (sourceB2086 + difference 0 4) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2086 + difference 4 0) (sourceB2086 + difference 0 4) sourceC2086) = raw21870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw21870; decide +kernel
    rw [ha]
    exact (canonical21870 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2086 + difference 4 1) (sourceB2086 + difference 1 4) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2159) := by
    have ha : (tripleCharges (sourceA2086 + difference 4 1) (sourceB2086 + difference 1 4) sourceC2086) = raw29260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29260; decide +kernel
    rw [ha]
    exact (canonical29260 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2086 + difference 4 2) (sourceB2086 + difference 2 4) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2086 + difference 4 2) (sourceB2086 + difference 2 4) sourceC2086) = raw29261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29261; decide +kernel
    rw [ha]
    exact (canonical29261 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2086 + difference 4 3) (sourceB2086 + difference 3 4) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2086 + difference 4 3) (sourceB2086 + difference 3 4) sourceC2086) = raw29262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29262; decide +kernel
    rw [ha]
    exact (canonical29262 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2086 + difference 4 5) (sourceB2086 + difference 5 4) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2086 + difference 4 5) (sourceB2086 + difference 5 4) sourceC2086) = raw29263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29263; decide +kernel
    rw [ha]
    exact (canonical29263 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2086 + difference 5 0) (sourceB2086 + difference 0 5) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA2086 + difference 5 0) (sourceB2086 + difference 0 5) sourceC2086) = raw19938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw19938; decide +kernel
    rw [ha]
    exact (canonical19938 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2086 + difference 5 1) (sourceB2086 + difference 1 5) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2086 + difference 5 1) (sourceB2086 + difference 1 5) sourceC2086) = raw29264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29264; decide +kernel
    rw [ha]
    exact (canonical29264 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2086 + difference 5 2) (sourceB2086 + difference 2 5) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA2086 + difference 5 2) (sourceB2086 + difference 2 5) sourceC2086) = raw29265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29265; decide +kernel
    rw [ha]
    exact (canonical29265 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2086 + difference 5 3) (sourceB2086 + difference 3 5) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA2086 + difference 5 3) (sourceB2086 + difference 3 5) sourceC2086) = raw29266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29266; decide +kernel
    rw [ha]
    exact (canonical29266 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2086 + difference 5 4) (sourceB2086 + difference 4 5) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA2086 + difference 5 4) (sourceB2086 + difference 4 5) sourceC2086) = raw19917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw19917; decide +kernel
    rw [ha]
    exact (canonical19917 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2086 sourceB2086 sourceC2086
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2086, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2087 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2087 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2087 + difference 0 1) (sourceB2087 + difference 1 0) sourceC2087) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA2087 + difference 0 1) (sourceB2087 + difference 1 0) sourceC2087) = raw29267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2087 sourceB2087 sourceC2087 difference raw29267; decide +kernel
    rw [ha]
    exact (canonical29267 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2087 + difference 1 1) (sourceB2087 + difference 1 1) sourceC2087) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2056) := by
    have ha : (tripleCharges (sourceA2087 + difference 1 1) (sourceB2087 + difference 1 1) sourceC2087) = raw29268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2087 sourceB2087 sourceC2087 difference raw29268; decide +kernel
    rw [ha]
    exact (canonical29268 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2087 + difference 2 1) (sourceB2087 + difference 1 2) sourceC2087) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1804) := by
    have ha : (tripleCharges (sourceA2087 + difference 2 1) (sourceB2087 + difference 1 2) sourceC2087) = raw29269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2087 sourceB2087 sourceC2087 difference raw29269; decide +kernel
    rw [ha]
    exact (canonical29269 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2087 + difference 3 1) (sourceB2087 + difference 1 3) sourceC2087) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1804) := by
    have ha : (tripleCharges (sourceA2087 + difference 3 1) (sourceB2087 + difference 1 3) sourceC2087) = raw29270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2087 sourceB2087 sourceC2087 difference raw29270; decide +kernel
    rw [ha]
    exact (canonical29270 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2087 + difference 4 1) (sourceB2087 + difference 1 4) sourceC2087) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1817) := by
    have ha : (tripleCharges (sourceA2087 + difference 4 1) (sourceB2087 + difference 1 4) sourceC2087) = raw29271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2087 sourceB2087 sourceC2087 difference raw29271; decide +kernel
    rw [ha]
    exact (canonical29271 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2087 + difference 5 1) (sourceB2087 + difference 1 5) sourceC2087) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 937) := by
    have ha : (tripleCharges (sourceA2087 + difference 5 1) (sourceB2087 + difference 1 5) sourceC2087) = raw29272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2087 sourceB2087 sourceC2087 difference raw29272; decide +kernel
    rw [ha]
    exact (canonical29272 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2087 + sourceB2087) sourceC2087) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA2087 + sourceB2087) sourceC2087) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA2087 sourceB2087 sourceC2087 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2087 sourceB2087 sourceC2087
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2087, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1728 : Integer.Sparse.reindex keyMap MixedData.row1728 = numericRow1728 := by decide +kernel

theorem numericCheck1728 (x : Master → ℝ) : Integer.Sparse.eval numericRow1728 x =
    (1 : ℝ) * reducedSource1728 x := by
  norm_num [numericRow1728, reducedSource1728, Integer.Sparse.eval, Sparse.eval, nodeValue2377, nodeValue2541, nodeValue2551, nodeValue2705, nodeValue3757, nodeValue4088]

theorem reindexCheck1729 : Integer.Sparse.reindex keyMap MixedData.row1729 = numericRow1729 := by decide +kernel

theorem numericCheck1729 (x : Master → ℝ) : Integer.Sparse.eval numericRow1729 x =
    (1 : ℝ) * reducedSource1729 x := by
  norm_num [numericRow1729, reducedSource1729, Integer.Sparse.eval, Sparse.eval, nodeValue1897, nodeValue2540, nodeValue2550, nodeValue2704, nodeValue3459, nodeValue4080]

theorem reindexCheck1730 : Integer.Sparse.reindex keyMap MixedData.row1730 = numericRow1730 := by decide +kernel

theorem numericCheck1730 (x : Master → ℝ) : Integer.Sparse.eval numericRow1730 x =
    (1 : ℝ) * reducedSource1730 x := by
  norm_num [numericRow1730, reducedSource1730, Integer.Sparse.eval, Sparse.eval, nodeValue2075, nodeValue2079, nodeValue2082, nodeValue2101, nodeValue2205, nodeValue3564, nodeValue4080]

theorem reindexCheck1731 : Integer.Sparse.reindex keyMap MixedData.row1731 = numericRow1731 := by decide +kernel

theorem numericCheck1731 (x : Master → ℝ) : Integer.Sparse.eval numericRow1731 x =
    (1 : ℝ) * reducedSource1731 x := by
  norm_num [numericRow1731, reducedSource1731, Integer.Sparse.eval, Sparse.eval, nodeValue1123, nodeValue1875, nodeValue1880, nodeValue1914, nodeValue2079, nodeValue2504, nodeValue4080]

theorem reindexCheck1732 : Integer.Sparse.reindex keyMap MixedData.row1732 = numericRow1732 := by decide +kernel

theorem numericCheck1732 (x : Master → ℝ) : Integer.Sparse.eval numericRow1732 x =
    (1 : ℝ) * reducedSource1732 x := by
  norm_num [numericRow1732, reducedSource1732, Integer.Sparse.eval, Sparse.eval, nodeValue916, nodeValue1799, nodeValue1874, nodeValue1911, nodeValue2018, nodeValue2047, nodeValue4081]

theorem reindexCheck1733 : Integer.Sparse.reindex keyMap MixedData.row1733 = numericRow1733 := by decide +kernel

theorem numericCheck1733 (x : Master → ℝ) : Integer.Sparse.eval numericRow1733 x =
    (1 : ℝ) * reducedSource1733 x := by
  norm_num [numericRow1733, reducedSource1733, Integer.Sparse.eval, Sparse.eval, nodeValue2449, nodeValue2452, nodeValue2461, nodeValue2477, nodeValue2694, nodeValue3793, nodeValue4090]

theorem reindexCheck1735 : Integer.Sparse.reindex keyMap MixedData.row1735 = numericRow1735 := by decide +kernel

theorem numericCheck1735 (x : Master → ℝ) : Integer.Sparse.eval numericRow1735 x =
    (1 : ℝ) * reducedSource1735 x := by
  norm_num [numericRow1735, reducedSource1735, Integer.Sparse.eval, Sparse.eval, nodeValue1674, nodeValue1692, nodeValue1693, nodeValue1754, nodeValue2151, nodeValue2167, nodeValue2168, nodeValue2173, nodeValue2184, nodeValue2185, nodeValue2203, nodeValue2205, nodeValue2226, nodeValue2228, nodeValue2229, nodeValue2292, nodeValue2685, nodeValue2704, nodeValue2740, nodeValue2742, nodeValue4084]

theorem reindexCheck1736 : Integer.Sparse.reindex keyMap MixedData.row1736 = numericRow1736 := by decide +kernel

theorem numericCheck1736 (x : Master → ℝ) : Integer.Sparse.eval numericRow1736 x =
    (1 : ℝ) * reducedSource1736 x := by
  norm_num [numericRow1736, reducedSource1736, Integer.Sparse.eval, Sparse.eval, nodeValue2382, nodeValue2385, nodeValue2388, nodeValue2403, nodeValue2672, nodeValue3766, nodeValue4088]

theorem reindexCheck1737 : Integer.Sparse.reindex keyMap MixedData.row1737 = numericRow1737 := by decide +kernel

theorem numericCheck1737 (x : Master → ℝ) : Integer.Sparse.eval numericRow1737 x =
    (1 : ℝ) * reducedSource1737 x := by
  norm_num [numericRow1737, reducedSource1737, Integer.Sparse.eval, Sparse.eval, nodeValue2385, nodeValue2459, nodeValue2468, nodeValue2505, nodeValue2705, nodeValue3766, nodeValue4088]

theorem reindexCheck1741 : Integer.Sparse.reindex keyMap MixedData.row1741 = numericRow1741 := by decide +kernel

theorem numericCheck1741 (x : Master → ℝ) : Integer.Sparse.eval numericRow1741 x =
    (1 : ℝ) * reducedSource1741 x := by
  norm_num [numericRow1741, reducedSource1741, Integer.Sparse.eval, Sparse.eval, nodeValue1666, nodeValue1677, nodeValue1683, nodeValue1730, nodeValue2143, nodeValue2159, nodeValue2170, nodeValue2193, nodeValue2208, nodeValue2218, nodeValue2268, nodeValue2726, nodeValue4085]

theorem reindexCheck1742 : Integer.Sparse.reindex keyMap MixedData.row1742 = numericRow1742 := by decide +kernel

theorem numericCheck1742 (x : Master → ℝ) : Integer.Sparse.eval numericRow1742 x =
    (1 : ℝ) * reducedSource1742 x := by
  norm_num [numericRow1742, reducedSource1742, Integer.Sparse.eval, Sparse.eval, nodeValue937, nodeValue1804, nodeValue1817, nodeValue2056, nodeValue2065, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1728 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1728 (mixedVector B) = 0 := by
  have h2377 : mixedVector B (Sum.inr 2377) = Sparse.eval nodeValue2377 (mixedVector B) := by
    change mixedMoment B node2377 node2377Labels = _
    exact sound2377 B hB hF
  have h2541 : mixedVector B (Sum.inr 2541) = Sparse.eval nodeValue2541 (mixedVector B) := by
    change mixedMoment B node2541 node2541Labels = _
    exact sound2541 B hB hF
  have h2551 : mixedVector B (Sum.inr 2551) = Sparse.eval nodeValue2551 (mixedVector B) := by
    change mixedMoment B node2551 node2551Labels = _
    exact sound2551 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2057, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2377, h2541, h2551, h2705, h3757, h4088, reducedSource1728] using sourceEq2057 B hB

theorem rowSound1728 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1728 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1728, numericCheck1728, reducedZero1728 B hB hF, mul_zero]

theorem reducedZero1729 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1729 (mixedVector B) = 0 := by
  have h1897 : mixedVector B (Sum.inr 1897) = Sparse.eval nodeValue1897 (mixedVector B) := by
    change mixedMoment B node1897 node1897Labels = _
    exact sound1897 B hB hF
  have h2540 : mixedVector B (Sum.inr 2540) = Sparse.eval nodeValue2540 (mixedVector B) := by
    change mixedMoment B node2540 node2540Labels = _
    exact sound2540 B hB hF
  have h2550 : mixedVector B (Sum.inr 2550) = Sparse.eval nodeValue2550 (mixedVector B) := by
    change mixedMoment B node2550 node2550Labels = _
    exact sound2550 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h3459 : mixedVector B (Sum.inr 3459) = Sparse.eval nodeValue3459 (mixedVector B) := by
    change mixedMoment B node3459 node3459Labels = _
    exact sound3459 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2059, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1897, h2540, h2550, h2704, h3459, h4080, reducedSource1729] using sourceEq2059 B hB

theorem rowSound1729 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1729 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1729, numericCheck1729, reducedZero1729 B hB hF, mul_zero]

theorem reducedZero1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1730 (mixedVector B) = 0 := by
  have h2075 : mixedVector B (Sum.inr 2075) = Sparse.eval nodeValue2075 (mixedVector B) := by
    change mixedMoment B node2075 node2075Labels = _
    exact sound2075 B hB hF
  have h2079 : mixedVector B (Sum.inr 2079) = Sparse.eval nodeValue2079 (mixedVector B) := by
    change mixedMoment B node2079 node2079Labels = _
    exact sound2079 B hB hF
  have h2082 : mixedVector B (Sum.inr 2082) = Sparse.eval nodeValue2082 (mixedVector B) := by
    change mixedMoment B node2082 node2082Labels = _
    exact sound2082 B hB hF
  have h2101 : mixedVector B (Sum.inr 2101) = Sparse.eval nodeValue2101 (mixedVector B) := by
    change mixedMoment B node2101 node2101Labels = _
    exact sound2101 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2061, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2075, h2079, h2082, h2101, h2205, h3564, h4080, reducedSource1730] using sourceEq2061 B hB

theorem rowSound1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1730 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1730, numericCheck1730, reducedZero1730 B hB hF, mul_zero]

theorem reducedZero1731 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1731 (mixedVector B) = 0 := by
  have h1123 : mixedVector B (Sum.inr 1123) = Sparse.eval nodeValue1123 (mixedVector B) := by
    change mixedMoment B node1123 node1123Labels = _
    exact sound1123 B hB hF
  have h1875 : mixedVector B (Sum.inr 1875) = Sparse.eval nodeValue1875 (mixedVector B) := by
    change mixedMoment B node1875 node1875Labels = _
    exact sound1875 B hB hF
  have h1880 : mixedVector B (Sum.inr 1880) = Sparse.eval nodeValue1880 (mixedVector B) := by
    change mixedMoment B node1880 node1880Labels = _
    exact sound1880 B hB hF
  have h1914 : mixedVector B (Sum.inr 1914) = Sparse.eval nodeValue1914 (mixedVector B) := by
    change mixedMoment B node1914 node1914Labels = _
    exact sound1914 B hB hF
  have h2079 : mixedVector B (Sum.inr 2079) = Sparse.eval nodeValue2079 (mixedVector B) := by
    change mixedMoment B node2079 node2079Labels = _
    exact sound2079 B hB hF
  have h2504 : mixedVector B (Sum.inr 2504) = Sparse.eval nodeValue2504 (mixedVector B) := by
    change mixedMoment B node2504 node2504Labels = _
    exact sound2504 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2062, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1123, h1875, h1880, h1914, h2079, h2504, h4080, reducedSource1731] using sourceEq2062 B hB

theorem rowSound1731 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1731 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1731, numericCheck1731, reducedZero1731 B hB hF, mul_zero]

theorem reducedZero1732 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1732 (mixedVector B) = 0 := by
  have h916 : mixedVector B (Sum.inr 916) = Sparse.eval nodeValue916 (mixedVector B) := by
    change mixedMoment B node916 node916Labels = _
    exact sound916 B hB hF
  have h1799 : mixedVector B (Sum.inr 1799) = Sparse.eval nodeValue1799 (mixedVector B) := by
    change mixedMoment B node1799 node1799Labels = _
    exact sound1799 B hB hF
  have h1874 : mixedVector B (Sum.inr 1874) = Sparse.eval nodeValue1874 (mixedVector B) := by
    change mixedMoment B node1874 node1874Labels = _
    exact sound1874 B hB hF
  have h1911 : mixedVector B (Sum.inr 1911) = Sparse.eval nodeValue1911 (mixedVector B) := by
    change mixedMoment B node1911 node1911Labels = _
    exact sound1911 B hB hF
  have h2018 : mixedVector B (Sum.inr 2018) = Sparse.eval nodeValue2018 (mixedVector B) := by
    change mixedMoment B node2018 node2018Labels = _
    exact sound2018 B hB hF
  have h2047 : mixedVector B (Sum.inr 2047) = Sparse.eval nodeValue2047 (mixedVector B) := by
    change mixedMoment B node2047 node2047Labels = _
    exact sound2047 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm2064, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h916, h1799, h1874, h1911, h2018, h2047, h4081, reducedSource1732] using sourceEq2064 B hB

theorem rowSound1732 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1732 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1732, numericCheck1732, reducedZero1732 B hB hF, mul_zero]

theorem reducedZero1733 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1733 (mixedVector B) = 0 := by
  have h2449 : mixedVector B (Sum.inr 2449) = Sparse.eval nodeValue2449 (mixedVector B) := by
    change mixedMoment B node2449 node2449Labels = _
    exact sound2449 B hB hF
  have h2452 : mixedVector B (Sum.inr 2452) = Sparse.eval nodeValue2452 (mixedVector B) := by
    change mixedMoment B node2452 node2452Labels = _
    exact sound2452 B hB hF
  have h2461 : mixedVector B (Sum.inr 2461) = Sparse.eval nodeValue2461 (mixedVector B) := by
    change mixedMoment B node2461 node2461Labels = _
    exact sound2461 B hB hF
  have h2477 : mixedVector B (Sum.inr 2477) = Sparse.eval nodeValue2477 (mixedVector B) := by
    change mixedMoment B node2477 node2477Labels = _
    exact sound2477 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h3793 : mixedVector B (Sum.inr 3793) = Sparse.eval nodeValue3793 (mixedVector B) := by
    change mixedMoment B node3793 node3793Labels = _
    exact sound3793 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm2065, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2449, h2452, h2461, h2477, h2694, h3793, h4090, reducedSource1733] using sourceEq2065 B hB

theorem rowSound1733 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1733 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1733, numericCheck1733, reducedZero1733 B hB hF, mul_zero]

theorem reducedZero1735 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1735 (mixedVector B) = 0 := by
  have h1674 : mixedVector B (Sum.inr 1674) = Sparse.eval nodeValue1674 (mixedVector B) := by
    change mixedMoment B node1674 node1674Labels = _
    exact sound1674 B hB hF
  have h1692 : mixedVector B (Sum.inr 1692) = Sparse.eval nodeValue1692 (mixedVector B) := by
    change mixedMoment B node1692 node1692Labels = _
    exact sound1692 B hB hF
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h2151 : mixedVector B (Sum.inr 2151) = Sparse.eval nodeValue2151 (mixedVector B) := by
    change mixedMoment B node2151 node2151Labels = _
    exact sound2151 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h2173 : mixedVector B (Sum.inr 2173) = Sparse.eval nodeValue2173 (mixedVector B) := by
    change mixedMoment B node2173 node2173Labels = _
    exact sound2173 B hB hF
  have h2184 : mixedVector B (Sum.inr 2184) = Sparse.eval nodeValue2184 (mixedVector B) := by
    change mixedMoment B node2184 node2184Labels = _
    exact sound2184 B hB hF
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2073, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1674, h1692, h1693, h1754, h2151, h2167, h2168, h2173, h2184, h2185, h2203, h2205, h2226, h2228, h2229, h2292, h2685, h2704, h2740, h2742, h4084, reducedSource1735] using sourceEq2073 B hB

theorem rowSound1735 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1735 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1735, numericCheck1735, reducedZero1735 B hB hF, mul_zero]

theorem reducedZero1736 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1736 (mixedVector B) = 0 := by
  have h2382 : mixedVector B (Sum.inr 2382) = Sparse.eval nodeValue2382 (mixedVector B) := by
    change mixedMoment B node2382 node2382Labels = _
    exact sound2382 B hB hF
  have h2385 : mixedVector B (Sum.inr 2385) = Sparse.eval nodeValue2385 (mixedVector B) := by
    change mixedMoment B node2385 node2385Labels = _
    exact sound2385 B hB hF
  have h2388 : mixedVector B (Sum.inr 2388) = Sparse.eval nodeValue2388 (mixedVector B) := by
    change mixedMoment B node2388 node2388Labels = _
    exact sound2388 B hB hF
  have h2403 : mixedVector B (Sum.inr 2403) = Sparse.eval nodeValue2403 (mixedVector B) := by
    change mixedMoment B node2403 node2403Labels = _
    exact sound2403 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2074, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2382, h2385, h2388, h2403, h2672, h3766, h4088, reducedSource1736] using sourceEq2074 B hB

theorem rowSound1736 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1736 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1736, numericCheck1736, reducedZero1736 B hB hF, mul_zero]

theorem reducedZero1737 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1737 (mixedVector B) = 0 := by
  have h2385 : mixedVector B (Sum.inr 2385) = Sparse.eval nodeValue2385 (mixedVector B) := by
    change mixedMoment B node2385 node2385Labels = _
    exact sound2385 B hB hF
  have h2459 : mixedVector B (Sum.inr 2459) = Sparse.eval nodeValue2459 (mixedVector B) := by
    change mixedMoment B node2459 node2459Labels = _
    exact sound2459 B hB hF
  have h2468 : mixedVector B (Sum.inr 2468) = Sparse.eval nodeValue2468 (mixedVector B) := by
    change mixedMoment B node2468 node2468Labels = _
    exact sound2468 B hB hF
  have h2505 : mixedVector B (Sum.inr 2505) = Sparse.eval nodeValue2505 (mixedVector B) := by
    change mixedMoment B node2505 node2505Labels = _
    exact sound2505 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2077, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2385, h2459, h2468, h2505, h2705, h3766, h4088, reducedSource1737] using sourceEq2077 B hB

theorem rowSound1737 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1737 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1737, numericCheck1737, reducedZero1737 B hB hF, mul_zero]

theorem reducedZero1741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1741 (mixedVector B) = 0 := by
  have h1666 : mixedVector B (Sum.inr 1666) = Sparse.eval nodeValue1666 (mixedVector B) := by
    change mixedMoment B node1666 node1666Labels = _
    exact sound1666 B hB hF
  have h1677 : mixedVector B (Sum.inr 1677) = Sparse.eval nodeValue1677 (mixedVector B) := by
    change mixedMoment B node1677 node1677Labels = _
    exact sound1677 B hB hF
  have h1683 : mixedVector B (Sum.inr 1683) = Sparse.eval nodeValue1683 (mixedVector B) := by
    change mixedMoment B node1683 node1683Labels = _
    exact sound1683 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h2143 : mixedVector B (Sum.inr 2143) = Sparse.eval nodeValue2143 (mixedVector B) := by
    change mixedMoment B node2143 node2143Labels = _
    exact sound2143 B hB hF
  have h2159 : mixedVector B (Sum.inr 2159) = Sparse.eval nodeValue2159 (mixedVector B) := by
    change mixedMoment B node2159 node2159Labels = _
    exact sound2159 B hB hF
  have h2170 : mixedVector B (Sum.inr 2170) = Sparse.eval nodeValue2170 (mixedVector B) := by
    change mixedMoment B node2170 node2170Labels = _
    exact sound2170 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm2086, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1666, h1677, h1683, h1730, h2143, h2159, h2170, h2193, h2208, h2218, h2268, h2726, h4085, reducedSource1741] using sourceEq2086 B hB

theorem rowSound1741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1741 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1741, numericCheck1741, reducedZero1741 B hB hF, mul_zero]

theorem reducedZero1742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1742 (mixedVector B) = 0 := by
  have h937 : mixedVector B (Sum.inr 937) = Sparse.eval nodeValue937 (mixedVector B) := by
    change mixedMoment B node937 node937Labels = _
    exact sound937 B hB hF
  have h1804 : mixedVector B (Sum.inr 1804) = Sparse.eval nodeValue1804 (mixedVector B) := by
    change mixedMoment B node1804 node1804Labels = _
    exact sound1804 B hB hF
  have h1817 : mixedVector B (Sum.inr 1817) = Sparse.eval nodeValue1817 (mixedVector B) := by
    change mixedMoment B node1817 node1817Labels = _
    exact sound1817 B hB hF
  have h2056 : mixedVector B (Sum.inr 2056) = Sparse.eval nodeValue2056 (mixedVector B) := by
    change mixedMoment B node2056 node2056Labels = _
    exact sound2056 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm2087, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h937, h1804, h1817, h2056, h2065, h4085, reducedSource1742] using sourceEq2087 B hB

theorem rowSound1742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1742 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1742, numericCheck1742, reducedZero1742 B hB hF, mul_zero]

theorem sourceRowsAt1728 : MixedData.sourceRows (1728 : Fin 2425) =
    MixedData.row1728 := by decide +kernel

theorem sourceRowsAt1729 : MixedData.sourceRows (1729 : Fin 2425) =
    MixedData.row1729 := by decide +kernel

theorem sourceRowsAt1730 : MixedData.sourceRows (1730 : Fin 2425) =
    MixedData.row1730 := by decide +kernel

theorem sourceRowsAt1731 : MixedData.sourceRows (1731 : Fin 2425) =
    MixedData.row1731 := by decide +kernel

theorem sourceRowsAt1732 : MixedData.sourceRows (1732 : Fin 2425) =
    MixedData.row1732 := by decide +kernel

theorem sourceRowsAt1733 : MixedData.sourceRows (1733 : Fin 2425) =
    MixedData.row1733 := by decide +kernel

theorem sourceRowsAt1734 : MixedData.sourceRows (1734 : Fin 2425) =
    MixedData.row1734 := by decide +kernel

theorem sourceRowsAt1735 : MixedData.sourceRows (1735 : Fin 2425) =
    MixedData.row1735 := by decide +kernel

theorem sourceRowsAt1736 : MixedData.sourceRows (1736 : Fin 2425) =
    MixedData.row1736 := by decide +kernel

theorem sourceRowsAt1737 : MixedData.sourceRows (1737 : Fin 2425) =
    MixedData.row1737 := by decide +kernel

theorem sourceRowsAt1738 : MixedData.sourceRows (1738 : Fin 2425) =
    MixedData.row1738 := by decide +kernel

theorem sourceRowsAt1739 : MixedData.sourceRows (1739 : Fin 2425) =
    MixedData.row1739 := by decide +kernel

theorem sourceRowsAt1740 : MixedData.sourceRows (1740 : Fin 2425) =
    MixedData.row1740 := by decide +kernel

theorem sourceRowsAt1741 : MixedData.sourceRows (1741 : Fin 2425) =
    MixedData.row1741 := by decide +kernel

theorem sourceRowsAt1742 : MixedData.sourceRows (1742 : Fin 2425) =
    MixedData.row1742 := by decide +kernel

theorem sourceRowsAt1743 : MixedData.sourceRows (1743 : Fin 2425) =
    MixedData.row1743 := by decide +kernel

theorem chunkSound108_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 108) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1728 ∨ k.val = 1729 ∨ k.val = 1730 ∨ k.val = 1731 ∨ k.val = 1732 ∨ k.val = 1733 ∨ k.val = 1734 ∨ k.val = 1735 ∨ k.val = 1736 ∨ k.val = 1737 ∨ k.val = 1738 ∨ k.val = 1739 ∨ k.val = 1740 ∨ k.val = 1741 ∨ k.val = 1742 ∨ k.val = 1743 := by omega
  rcases heq with h1728 | h1729 | h1730 | h1731 | h1732 | h1733 | h1734 | h1735 | h1736 | h1737 | h1738 | h1739 | h1740 | h1741 | h1742 | h1743
  · have he : k = (1728 : Fin 2425) := Fin.ext h1728
    subst k
    rw [sourceRowsAt1728]
    exact rowSound1728 B hB hF
  · have he : k = (1729 : Fin 2425) := Fin.ext h1729
    subst k
    rw [sourceRowsAt1729]
    exact rowSound1729 B hB hF
  · have he : k = (1730 : Fin 2425) := Fin.ext h1730
    subst k
    rw [sourceRowsAt1730]
    exact rowSound1730 B hB hF
  · have he : k = (1731 : Fin 2425) := Fin.ext h1731
    subst k
    rw [sourceRowsAt1731]
    exact rowSound1731 B hB hF
  · have he : k = (1732 : Fin 2425) := Fin.ext h1732
    subst k
    rw [sourceRowsAt1732]
    exact rowSound1732 B hB hF
  · have he : k = (1733 : Fin 2425) := Fin.ext h1733
    subst k
    rw [sourceRowsAt1733]
    exact rowSound1733 B hB hF
  · have he : k = (1734 : Fin 2425) := Fin.ext h1734
    subst k
    rw [sourceRowsAt1734]
    exact rowSound1734_e B hB hF
  · have he : k = (1735 : Fin 2425) := Fin.ext h1735
    subst k
    rw [sourceRowsAt1735]
    exact rowSound1735 B hB hF
  · have he : k = (1736 : Fin 2425) := Fin.ext h1736
    subst k
    rw [sourceRowsAt1736]
    exact rowSound1736 B hB hF
  · have he : k = (1737 : Fin 2425) := Fin.ext h1737
    subst k
    rw [sourceRowsAt1737]
    exact rowSound1737 B hB hF
  · have he : k = (1738 : Fin 2425) := Fin.ext h1738
    subst k
    rw [sourceRowsAt1738]
    exact rowSound1738_e B hB hF
  · have he : k = (1739 : Fin 2425) := Fin.ext h1739
    subst k
    rw [sourceRowsAt1739]
    exact rowSound1739_e B hB hF
  · have he : k = (1740 : Fin 2425) := Fin.ext h1740
    subst k
    rw [sourceRowsAt1740]
    exact rowSound1740_e B hB hF
  · have he : k = (1741 : Fin 2425) := Fin.ext h1741
    subst k
    rw [sourceRowsAt1741]
    exact rowSound1741 B hB hF
  · have he : k = (1742 : Fin 2425) := Fin.ext h1742
    subst k
    rw [sourceRowsAt1742]
    exact rowSound1742 B hB hF
  · have he : k = (1743 : Fin 2425) := Fin.ext h1743
    subst k
    rw [sourceRowsAt1743]
    exact rowSound1743_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e_oai
