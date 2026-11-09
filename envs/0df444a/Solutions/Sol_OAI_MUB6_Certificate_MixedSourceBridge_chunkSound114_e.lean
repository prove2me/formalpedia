-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:39:41.44165+00:00
-- url     : https://prove2.me/submissions/604b8d44-0d2f-4ace-a6c2-147b9a46a0f3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1825_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1826_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1828_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1831_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1833_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1835_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1838_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1839_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24045 raw24045Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw24045 raw24045Labels = mixedMoment B raw24045step0 raw24045step0Labels := by
      have hz : ∀ j, raw24045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24045step0 = (fun i j => raw24045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24045step0 raw24045; decide +kernel
      have hl : raw24045step0Labels = raw24045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24045 raw24045Labels permutation434 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical236
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30218 raw30218Labels = mixedMoment B node2456 node2456Labels := by
  calc
    mixedMoment B raw30218 raw30218Labels = mixedMoment B raw30218step0 raw30218step0Labels := by
      have ha : raw30218step0 = (fun i j => raw30218 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30218step0 raw30218; decide +kernel
      have hl : raw30218step0Labels = raw30218Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30218 raw30218Labels permutation158 permutation2
    _ = mixedMoment B node2456 node2456Labels := by rfl

theorem canonical30219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30219 raw30219Labels = mixedMoment B node3680 node3680Labels := by
  calc
    mixedMoment B raw30219 raw30219Labels = mixedMoment B raw30219step0 raw30219step0Labels := by
      have ha : raw30219step0 = (fun i j => raw30219 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30219step0 raw30219; decide +kernel
      have hl : raw30219step0Labels = raw30219Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30219 raw30219Labels permutation158 permutation2
    _ = mixedMoment B node3680 node3680Labels := by rfl

theorem canonical30220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30220 raw30220Labels = mixedMoment B node2756 node2756Labels := by
  calc
    mixedMoment B raw30220 raw30220Labels = mixedMoment B raw30220step0 raw30220step0Labels := by
      have ha : raw30220step0 = (fun i j => raw30220 (permutation369 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30220step0 raw30220; decide +kernel
      have hl : raw30220step0Labels = raw30220Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30220 raw30220Labels permutation369 permutation4
    mixedMoment B raw30220step0 raw30220step0Labels = mixedMoment B raw30220step1 raw30220step1Labels := by
      have ha : raw30220step1 = -raw30220step0 := by apply Matrix.ext; change ∀ i j, raw30220step1 i j = -(raw30220step0 i j); unfold raw30220step1 raw30220step0; decide +kernel
      have hl : raw30220step1Labels = raw30220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2756 node2756Labels := by rfl

theorem canonical30221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30221 raw30221Labels = mixedMoment B node3776 node3776Labels := by
  calc
    mixedMoment B raw30221 raw30221Labels = mixedMoment B raw30221step0 raw30221step0Labels := by
      have ha : raw30221step0 = (fun i j => raw30221 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30221step0 raw30221; decide +kernel
      have hl : raw30221step0Labels = raw30221Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30221 raw30221Labels permutation158 permutation2
    _ = mixedMoment B node3776 node3776Labels := by rfl

theorem canonical30222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30222 raw30222Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw30222 raw30222Labels = mixedMoment B raw30222step0 raw30222step0Labels := by
      have ha : raw30222step0 = (fun i j => raw30222 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30222step0 raw30222; decide +kernel
      have hl : raw30222step0Labels = raw30222Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30222 raw30222Labels permutation158 permutation2
    _ = mixedMoment B node3796 node3796Labels := by rfl

theorem canonical30223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30223 raw30223Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw30223 raw30223Labels = mixedMoment B raw30223step0 raw30223step0Labels := by
      have ha : raw30223step0 = (fun i j => raw30223 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30223step0 raw30223; decide +kernel
      have hl : raw30223step0Labels = raw30223Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30223 raw30223Labels permutation159 permutation2
    _ = mixedMoment B node3796 node3796Labels := by rfl

theorem canonical30224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30224 raw30224Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw30224 raw30224Labels = mixedMoment B raw30224step0 raw30224step0Labels := by
      have ha : raw30224step0 = (fun i j => raw30224 (permutation161 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30224step0 raw30224; decide +kernel
      have hl : raw30224step0Labels = raw30224Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30224 raw30224Labels permutation161 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical30299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30299 raw30299Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw30299 raw30299Labels = mixedMoment B raw30299step0 raw30299step0Labels := by
      have hz : ∀ j, raw30299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30299step0 = (fun i j => raw30299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30299step0 raw30299; decide +kernel
      have hl : raw30299step0Labels = raw30299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30299 raw30299Labels permutation434 hz
    mixedMoment B raw30299step0 raw30299step0Labels = mixedMoment B raw30299step1 raw30299step1Labels := by
      have ha : raw30299step1 = (fun i j => raw30299step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30299step1 raw30299step0; decide +kernel
      have hl : raw30299step1Labels = raw30299step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30299step0 raw30299step0Labels permutation33 permutation2
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical30300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30300 raw30300Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw30300 raw30300Labels = mixedMoment B raw30300step0 raw30300step0Labels := by
      have hz : ∀ j, raw30300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30300step0 = (fun i j => raw30300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30300step0 raw30300; decide +kernel
      have hl : raw30300step0Labels = raw30300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30300 raw30300Labels permutation434 hz
    mixedMoment B raw30300step0 raw30300step0Labels = mixedMoment B raw30300step1 raw30300step1Labels := by
      have ha : raw30300step1 = (fun i j => raw30300step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30300step1 raw30300step0; decide +kernel
      have hl : raw30300step1Labels = raw30300step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30300step0 raw30300step0Labels permutation33 permutation2
    _ = mixedMoment B node2488 node2488Labels := by rfl

theorem canonical30301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30301 raw30301Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw30301 raw30301Labels = mixedMoment B raw30301step0 raw30301step0Labels := by
      have hz : ∀ j, raw30301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30301step0 = (fun i j => raw30301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30301step0 raw30301; decide +kernel
      have hl : raw30301step0Labels = raw30301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30301 raw30301Labels permutation434 hz
    mixedMoment B raw30301step0 raw30301step0Labels = mixedMoment B raw30301step1 raw30301step1Labels := by
      have ha : raw30301step1 = (fun i j => raw30301step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30301step1 raw30301step0; decide +kernel
      have hl : raw30301step1Labels = raw30301step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30301step0 raw30301step0Labels permutation33 permutation2
    _ = mixedMoment B node2341 node2341Labels := by rfl

theorem canonical30302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30302 raw30302Labels = mixedMoment B node2321 node2321Labels := by
  calc
    mixedMoment B raw30302 raw30302Labels = mixedMoment B raw30302step0 raw30302step0Labels := by
      have ha : raw30302step0 = (fun i j => raw30302 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30302step0 raw30302; decide +kernel
      have hl : raw30302step0Labels = raw30302Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30302 raw30302Labels permutation153 permutation2
    _ = mixedMoment B node2321 node2321Labels := by rfl

theorem canonical30303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30303 raw30303Labels = mixedMoment B node2325 node2325Labels := by
  calc
    mixedMoment B raw30303 raw30303Labels = mixedMoment B raw30303step0 raw30303step0Labels := by
      have hz : ∀ j, raw30303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30303step0 = (fun i j => raw30303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30303step0 raw30303; decide +kernel
      have hl : raw30303step0Labels = raw30303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30303 raw30303Labels permutation434 hz
    mixedMoment B raw30303step0 raw30303step0Labels = mixedMoment B raw30303step1 raw30303step1Labels := by
      have ha : raw30303step1 = (fun i j => raw30303step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30303step1 raw30303step0; decide +kernel
      have hl : raw30303step1Labels = raw30303step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30303step0 raw30303step0Labels permutation33 permutation2
    _ = mixedMoment B node2325 node2325Labels := by rfl

theorem canonical30304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30304 raw30304Labels = mixedMoment B node2327 node2327Labels := by
  calc
    mixedMoment B raw30304 raw30304Labels = mixedMoment B raw30304step0 raw30304step0Labels := by
      have hz : ∀ j, raw30304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30304step0 = (fun i j => raw30304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30304step0 raw30304; decide +kernel
      have hl : raw30304step0Labels = raw30304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30304 raw30304Labels permutation434 hz
    _ = mixedMoment B node2327 node2327Labels := by rfl

theorem canonical30305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30305 raw30305Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw30305 raw30305Labels = mixedMoment B raw30305step0 raw30305step0Labels := by
      have hz : ∀ j, raw30305 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw30305step0 = (fun i j => raw30305 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw30305step0 raw30305; decide +kernel
      have hl : raw30305step0Labels = raw30305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30305 raw30305Labels permutation590 hz
    mixedMoment B raw30305step0 raw30305step0Labels = mixedMoment B raw30305step1 raw30305step1Labels := by
      have hz : ∀ j, raw30305step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw30305step1 = (fun i j => raw30305step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw30305step1 raw30305step0; decide +kernel
      have hl : raw30305step1Labels = raw30305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30305step0 raw30305step0Labels permutation104 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical237
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30442 raw30442Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw30442 raw30442Labels = mixedMoment B raw30442step0 raw30442step0Labels := by
      have hz : ∀ j, raw30442 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30442step0 = (fun i j => raw30442 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30442step0 raw30442; decide +kernel
      have hl : raw30442step0Labels = raw30442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30442 raw30442Labels permutation434 hz
    mixedMoment B raw30442step0 raw30442step0Labels = mixedMoment B raw30442step1 raw30442step1Labels := by
      have ha : raw30442step1 = (fun i j => raw30442step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30442step1 raw30442step0; decide +kernel
      have hl : raw30442step1Labels = raw30442step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30442step0 raw30442step0Labels permutation32 permutation7
    mixedMoment B raw30442step1 raw30442step1Labels = mixedMoment B raw30442step2 raw30442step2Labels := by
      have ha : raw30442step2 = -raw30442step1 := by apply Matrix.ext; change ∀ i j, raw30442step2 i j = -(raw30442step1 i j); unfold raw30442step2 raw30442step1; decide +kernel
      have hl : raw30442step2Labels = raw30442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30442step2 raw30442step2Labels = mixedMoment B raw30442step3 raw30442step3Labels := by
      have ha : raw30442step3 = raw30442step2 := by apply Matrix.ext; unfold raw30442step3 raw30442step2; decide +kernel
      have hl : raw30442step2Labels = labelEmbedding1 ∘ raw30442step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30442step2 raw30442step2Labels raw30442step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

theorem canonical30443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30443 raw30443Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw30443 raw30443Labels = mixedMoment B raw30443step0 raw30443step0Labels := by
      have hz : ∀ j, raw30443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30443step0 = (fun i j => raw30443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30443step0 raw30443; decide +kernel
      have hl : raw30443step0Labels = raw30443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30443 raw30443Labels permutation434 hz
    mixedMoment B raw30443step0 raw30443step0Labels = mixedMoment B raw30443step1 raw30443step1Labels := by
      have ha : raw30443step1 = (fun i j => raw30443step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30443step1 raw30443step0; decide +kernel
      have hl : raw30443step1Labels = raw30443step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30443step0 raw30443step0Labels permutation32 permutation7
    mixedMoment B raw30443step1 raw30443step1Labels = mixedMoment B raw30443step2 raw30443step2Labels := by
      have ha : raw30443step2 = -raw30443step1 := by apply Matrix.ext; change ∀ i j, raw30443step2 i j = -(raw30443step1 i j); unfold raw30443step2 raw30443step1; decide +kernel
      have hl : raw30443step2Labels = raw30443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30443step2 raw30443step2Labels = mixedMoment B raw30443step3 raw30443step3Labels := by
      have ha : raw30443step3 = raw30443step2 := by apply Matrix.ext; unfold raw30443step3 raw30443step2; decide +kernel
      have hl : raw30443step2Labels = labelEmbedding1 ∘ raw30443step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30443step2 raw30443step2Labels raw30443step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

theorem canonical30444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30444 raw30444Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw30444 raw30444Labels = mixedMoment B raw30444step0 raw30444step0Labels := by
      have ha : raw30444step0 = (fun i j => raw30444 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30444step0 raw30444; decide +kernel
      have hl : raw30444step0Labels = raw30444Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30444 raw30444Labels permutation158 permutation7
    mixedMoment B raw30444step0 raw30444step0Labels = mixedMoment B raw30444step1 raw30444step1Labels := by
      have ha : raw30444step1 = -raw30444step0 := by apply Matrix.ext; change ∀ i j, raw30444step1 i j = -(raw30444step0 i j); unfold raw30444step1 raw30444step0; decide +kernel
      have hl : raw30444step1Labels = raw30444step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30444step1 raw30444step1Labels = mixedMoment B raw30444step2 raw30444step2Labels := by
      have ha : raw30444step2 = raw30444step1 := by apply Matrix.ext; unfold raw30444step2 raw30444step1; decide +kernel
      have hl : raw30444step1Labels = labelEmbedding1 ∘ raw30444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30444step1 raw30444step1Labels raw30444step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

theorem canonical30445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30445 raw30445Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw30445 raw30445Labels = mixedMoment B raw30445step0 raw30445step0Labels := by
      have hz : ∀ j, raw30445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30445step0 = (fun i j => raw30445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30445step0 raw30445; decide +kernel
      have hl : raw30445step0Labels = raw30445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30445 raw30445Labels permutation434 hz
    mixedMoment B raw30445step0 raw30445step0Labels = mixedMoment B raw30445step1 raw30445step1Labels := by
      have ha : raw30445step1 = (fun i j => raw30445step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30445step1 raw30445step0; decide +kernel
      have hl : raw30445step1Labels = raw30445step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30445step0 raw30445step0Labels permutation32 permutation7
    mixedMoment B raw30445step1 raw30445step1Labels = mixedMoment B raw30445step2 raw30445step2Labels := by
      have ha : raw30445step2 = -raw30445step1 := by apply Matrix.ext; change ∀ i j, raw30445step2 i j = -(raw30445step1 i j); unfold raw30445step2 raw30445step1; decide +kernel
      have hl : raw30445step2Labels = raw30445step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30445step2 raw30445step2Labels = mixedMoment B raw30445step3 raw30445step3Labels := by
      have ha : raw30445step3 = raw30445step2 := by apply Matrix.ext; unfold raw30445step3 raw30445step2; decide +kernel
      have hl : raw30445step2Labels = labelEmbedding1 ∘ raw30445step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30445step2 raw30445step2Labels raw30445step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical30446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30446 raw30446Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw30446 raw30446Labels = mixedMoment B raw30446step0 raw30446step0Labels := by
      have hz : ∀ j, raw30446 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30446step0 = (fun i j => raw30446 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30446step0 raw30446; decide +kernel
      have hl : raw30446step0Labels = raw30446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30446 raw30446Labels permutation434 hz
    mixedMoment B raw30446step0 raw30446step0Labels = mixedMoment B raw30446step1 raw30446step1Labels := by
      have ha : raw30446step1 = (fun i j => raw30446step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30446step1 raw30446step0; decide +kernel
      have hl : raw30446step1Labels = raw30446step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30446step0 raw30446step0Labels permutation33 permutation7
    mixedMoment B raw30446step1 raw30446step1Labels = mixedMoment B raw30446step2 raw30446step2Labels := by
      have ha : raw30446step2 = -raw30446step1 := by apply Matrix.ext; change ∀ i j, raw30446step2 i j = -(raw30446step1 i j); unfold raw30446step2 raw30446step1; decide +kernel
      have hl : raw30446step2Labels = raw30446step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30446step2 raw30446step2Labels = mixedMoment B raw30446step3 raw30446step3Labels := by
      have ha : raw30446step3 = raw30446step2 := by apply Matrix.ext; unfold raw30446step3 raw30446step2; decide +kernel
      have hl : raw30446step2Labels = labelEmbedding1 ∘ raw30446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30446step2 raw30446step2Labels raw30446step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical30447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30447 raw30447Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw30447 raw30447Labels = mixedMoment B raw30447step0 raw30447step0Labels := by
      have hz : ∀ j, raw30447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30447step0 = (fun i j => raw30447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30447step0 raw30447; decide +kernel
      have hl : raw30447step0Labels = raw30447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30447 raw30447Labels permutation434 hz
    mixedMoment B raw30447step0 raw30447step0Labels = mixedMoment B raw30447step1 raw30447step1Labels := by
      have ha : raw30447step1 = (fun i j => raw30447step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30447step1 raw30447step0; decide +kernel
      have hl : raw30447step1Labels = raw30447step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30447step0 raw30447step0Labels permutation38 permutation5
    mixedMoment B raw30447step1 raw30447step1Labels = mixedMoment B raw30447step2 raw30447step2Labels := by
      have ha : raw30447step2 = -raw30447step1 := by apply Matrix.ext; change ∀ i j, raw30447step2 i j = -(raw30447step1 i j); unfold raw30447step2 raw30447step1; decide +kernel
      have hl : raw30447step2Labels = raw30447step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30447step2 raw30447step2Labels = mixedMoment B raw30447step3 raw30447step3Labels := by
      have ha : raw30447step3 = raw30447step2 := by apply Matrix.ext; unfold raw30447step3 raw30447step2; decide +kernel
      have hl : raw30447step2Labels = labelEmbedding1 ∘ raw30447step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30447step2 raw30447step2Labels raw30447step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3297 node3297Labels := by rfl

theorem canonical30448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30448 raw30448Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw30448 raw30448Labels = mixedMoment B raw30448step0 raw30448step0Labels := by
      have hz : ∀ j, raw30448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30448step0 = (fun i j => raw30448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30448step0 raw30448; decide +kernel
      have hl : raw30448step0Labels = raw30448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30448 raw30448Labels permutation434 hz
    mixedMoment B raw30448step0 raw30448step0Labels = mixedMoment B raw30448step1 raw30448step1Labels := by
      have ha : raw30448step1 = (fun i j => raw30448step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30448step1 raw30448step0; decide +kernel
      have hl : raw30448step1Labels = raw30448step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30448step0 raw30448step0Labels permutation32 permutation7
    mixedMoment B raw30448step1 raw30448step1Labels = mixedMoment B raw30448step2 raw30448step2Labels := by
      have ha : raw30448step2 = -raw30448step1 := by apply Matrix.ext; change ∀ i j, raw30448step2 i j = -(raw30448step1 i j); unfold raw30448step2 raw30448step1; decide +kernel
      have hl : raw30448step2Labels = raw30448step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30448step2 raw30448step2Labels = mixedMoment B raw30448step3 raw30448step3Labels := by
      have ha : raw30448step3 = raw30448step2 := by apply Matrix.ext; unfold raw30448step3 raw30448step2; decide +kernel
      have hl : raw30448step2Labels = labelEmbedding1 ∘ raw30448step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30448step2 raw30448step2Labels raw30448step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

theorem canonical30449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30449 raw30449Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw30449 raw30449Labels = mixedMoment B raw30449step0 raw30449step0Labels := by
      have ha : raw30449step0 = (fun i j => raw30449 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30449step0 raw30449; decide +kernel
      have hl : raw30449step0Labels = raw30449Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30449 raw30449Labels permutation158 permutation7
    mixedMoment B raw30449step0 raw30449step0Labels = mixedMoment B raw30449step1 raw30449step1Labels := by
      have ha : raw30449step1 = -raw30449step0 := by apply Matrix.ext; change ∀ i j, raw30449step1 i j = -(raw30449step0 i j); unfold raw30449step1 raw30449step0; decide +kernel
      have hl : raw30449step1Labels = raw30449step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30449step1 raw30449step1Labels = mixedMoment B raw30449step2 raw30449step2Labels := by
      have ha : raw30449step2 = raw30449step1 := by apply Matrix.ext; unfold raw30449step2 raw30449step1; decide +kernel
      have hl : raw30449step1Labels = labelEmbedding1 ∘ raw30449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30449step1 raw30449step1Labels raw30449step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3520 node3520Labels := by rfl

theorem canonical30450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30450 raw30450Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw30450 raw30450Labels = mixedMoment B raw30450step0 raw30450step0Labels := by
      have hz : ∀ j, raw30450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30450step0 = (fun i j => raw30450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30450step0 raw30450; decide +kernel
      have hl : raw30450step0Labels = raw30450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30450 raw30450Labels permutation434 hz
    mixedMoment B raw30450step0 raw30450step0Labels = mixedMoment B raw30450step1 raw30450step1Labels := by
      have ha : raw30450step1 = (fun i j => raw30450step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30450step1 raw30450step0; decide +kernel
      have hl : raw30450step1Labels = raw30450step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30450step0 raw30450step0Labels permutation32 permutation7
    mixedMoment B raw30450step1 raw30450step1Labels = mixedMoment B raw30450step2 raw30450step2Labels := by
      have ha : raw30450step2 = -raw30450step1 := by apply Matrix.ext; change ∀ i j, raw30450step2 i j = -(raw30450step1 i j); unfold raw30450step2 raw30450step1; decide +kernel
      have hl : raw30450step2Labels = raw30450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30450step2 raw30450step2Labels = mixedMoment B raw30450step3 raw30450step3Labels := by
      have ha : raw30450step3 = raw30450step2 := by apply Matrix.ext; unfold raw30450step3 raw30450step2; decide +kernel
      have hl : raw30450step2Labels = labelEmbedding1 ∘ raw30450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30450step2 raw30450step2Labels raw30450step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical30451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30451 raw30451Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw30451 raw30451Labels = mixedMoment B raw30451step0 raw30451step0Labels := by
      have hz : ∀ j, raw30451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30451step0 = (fun i j => raw30451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30451step0 raw30451; decide +kernel
      have hl : raw30451step0Labels = raw30451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30451 raw30451Labels permutation434 hz
    mixedMoment B raw30451step0 raw30451step0Labels = mixedMoment B raw30451step1 raw30451step1Labels := by
      have ha : raw30451step1 = (fun i j => raw30451step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30451step1 raw30451step0; decide +kernel
      have hl : raw30451step1Labels = raw30451step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30451step0 raw30451step0Labels permutation33 permutation7
    mixedMoment B raw30451step1 raw30451step1Labels = mixedMoment B raw30451step2 raw30451step2Labels := by
      have ha : raw30451step2 = -raw30451step1 := by apply Matrix.ext; change ∀ i j, raw30451step2 i j = -(raw30451step1 i j); unfold raw30451step2 raw30451step1; decide +kernel
      have hl : raw30451step2Labels = raw30451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30451step2 raw30451step2Labels = mixedMoment B raw30451step3 raw30451step3Labels := by
      have ha : raw30451step3 = raw30451step2 := by apply Matrix.ext; unfold raw30451step3 raw30451step2; decide +kernel
      have hl : raw30451step2Labels = labelEmbedding1 ∘ raw30451step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30451step2 raw30451step2Labels raw30451step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical30452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30452 raw30452Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw30452 raw30452Labels = mixedMoment B raw30452step0 raw30452step0Labels := by
      have hz : ∀ j, raw30452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30452step0 = (fun i j => raw30452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30452step0 raw30452; decide +kernel
      have hl : raw30452step0Labels = raw30452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30452 raw30452Labels permutation434 hz
    mixedMoment B raw30452step0 raw30452step0Labels = mixedMoment B raw30452step1 raw30452step1Labels := by
      have ha : raw30452step1 = (fun i j => raw30452step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30452step1 raw30452step0; decide +kernel
      have hl : raw30452step1Labels = raw30452step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30452step0 raw30452step0Labels permutation32 permutation7
    mixedMoment B raw30452step1 raw30452step1Labels = mixedMoment B raw30452step2 raw30452step2Labels := by
      have ha : raw30452step2 = -raw30452step1 := by apply Matrix.ext; change ∀ i j, raw30452step2 i j = -(raw30452step1 i j); unfold raw30452step2 raw30452step1; decide +kernel
      have hl : raw30452step2Labels = raw30452step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30452step2 raw30452step2Labels = mixedMoment B raw30452step3 raw30452step3Labels := by
      have ha : raw30452step3 = raw30452step2 := by apply Matrix.ext; unfold raw30452step3 raw30452step2; decide +kernel
      have hl : raw30452step2Labels = labelEmbedding1 ∘ raw30452step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30452step2 raw30452step2Labels raw30452step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3274 node3274Labels := by rfl

theorem canonical30453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30453 raw30453Labels = mixedMoment B node3421 node3421Labels := by
  calc
    mixedMoment B raw30453 raw30453Labels = mixedMoment B raw30453step0 raw30453step0Labels := by
      have hz : ∀ j, raw30453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30453step0 = (fun i j => raw30453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30453step0 raw30453; decide +kernel
      have hl : raw30453step0Labels = raw30453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30453 raw30453Labels permutation434 hz
    mixedMoment B raw30453step0 raw30453step0Labels = mixedMoment B raw30453step1 raw30453step1Labels := by
      have ha : raw30453step1 = (fun i j => raw30453step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30453step1 raw30453step0; decide +kernel
      have hl : raw30453step1Labels = raw30453step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30453step0 raw30453step0Labels permutation32 permutation7
    mixedMoment B raw30453step1 raw30453step1Labels = mixedMoment B raw30453step2 raw30453step2Labels := by
      have ha : raw30453step2 = -raw30453step1 := by apply Matrix.ext; change ∀ i j, raw30453step2 i j = -(raw30453step1 i j); unfold raw30453step2 raw30453step1; decide +kernel
      have hl : raw30453step2Labels = raw30453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30453step2 raw30453step2Labels = mixedMoment B raw30453step3 raw30453step3Labels := by
      have ha : raw30453step3 = raw30453step2 := by apply Matrix.ext; unfold raw30453step3 raw30453step2; decide +kernel
      have hl : raw30453step2Labels = labelEmbedding1 ∘ raw30453step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30453step2 raw30453step2Labels raw30453step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3421 node3421Labels := by rfl

theorem canonical30454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30454 raw30454Labels = mixedMoment B node3456 node3456Labels := by
  calc
    mixedMoment B raw30454 raw30454Labels = mixedMoment B raw30454step0 raw30454step0Labels := by
      have ha : raw30454step0 = (fun i j => raw30454 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30454step0 raw30454; decide +kernel
      have hl : raw30454step0Labels = raw30454Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30454 raw30454Labels permutation158 permutation7
    mixedMoment B raw30454step0 raw30454step0Labels = mixedMoment B raw30454step1 raw30454step1Labels := by
      have ha : raw30454step1 = -raw30454step0 := by apply Matrix.ext; change ∀ i j, raw30454step1 i j = -(raw30454step0 i j); unfold raw30454step1 raw30454step0; decide +kernel
      have hl : raw30454step1Labels = raw30454step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30454step1 raw30454step1Labels = mixedMoment B raw30454step2 raw30454step2Labels := by
      have ha : raw30454step2 = raw30454step1 := by apply Matrix.ext; unfold raw30454step2 raw30454step1; decide +kernel
      have hl : raw30454step1Labels = labelEmbedding1 ∘ raw30454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30454step1 raw30454step1Labels raw30454step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3456 node3456Labels := by rfl

theorem canonical30455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30455 raw30455Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw30455 raw30455Labels = mixedMoment B raw30455step0 raw30455step0Labels := by
      have hz : ∀ j, raw30455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30455step0 = (fun i j => raw30455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30455step0 raw30455; decide +kernel
      have hl : raw30455step0Labels = raw30455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30455 raw30455Labels permutation434 hz
    mixedMoment B raw30455step0 raw30455step0Labels = mixedMoment B raw30455step1 raw30455step1Labels := by
      have ha : raw30455step1 = (fun i j => raw30455step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30455step1 raw30455step0; decide +kernel
      have hl : raw30455step1Labels = raw30455step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30455step0 raw30455step0Labels permutation32 permutation7
    mixedMoment B raw30455step1 raw30455step1Labels = mixedMoment B raw30455step2 raw30455step2Labels := by
      have ha : raw30455step2 = -raw30455step1 := by apply Matrix.ext; change ∀ i j, raw30455step2 i j = -(raw30455step1 i j); unfold raw30455step2 raw30455step1; decide +kernel
      have hl : raw30455step2Labels = raw30455step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30455step2 raw30455step2Labels = mixedMoment B raw30455step3 raw30455step3Labels := by
      have ha : raw30455step3 = raw30455step2 := by apply Matrix.ext; unfold raw30455step3 raw30455step2; decide +kernel
      have hl : raw30455step2Labels = labelEmbedding1 ∘ raw30455step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30455step2 raw30455step2Labels raw30455step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

theorem canonical30456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30456 raw30456Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw30456 raw30456Labels = mixedMoment B raw30456step0 raw30456step0Labels := by
      have hz : ∀ j, raw30456 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30456step0 = (fun i j => raw30456 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30456step0 raw30456; decide +kernel
      have hl : raw30456step0Labels = raw30456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30456 raw30456Labels permutation434 hz
    mixedMoment B raw30456step0 raw30456step0Labels = mixedMoment B raw30456step1 raw30456step1Labels := by
      have ha : raw30456step1 = (fun i j => raw30456step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30456step1 raw30456step0; decide +kernel
      have hl : raw30456step1Labels = raw30456step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30456step0 raw30456step0Labels permutation33 permutation7
    mixedMoment B raw30456step1 raw30456step1Labels = mixedMoment B raw30456step2 raw30456step2Labels := by
      have ha : raw30456step2 = -raw30456step1 := by apply Matrix.ext; change ∀ i j, raw30456step2 i j = -(raw30456step1 i j); unfold raw30456step2 raw30456step1; decide +kernel
      have hl : raw30456step2Labels = raw30456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30456step2 raw30456step2Labels = mixedMoment B raw30456step3 raw30456step3Labels := by
      have ha : raw30456step3 = raw30456step2 := by apply Matrix.ext; unfold raw30456step3 raw30456step2; decide +kernel
      have hl : raw30456step2Labels = labelEmbedding1 ∘ raw30456step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30456step2 raw30456step2Labels raw30456step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

theorem canonical30457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30457 raw30457Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw30457 raw30457Labels = mixedMoment B raw30457step0 raw30457step0Labels := by
      have ha : raw30457step0 = (fun i j => raw30457 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30457step0 raw30457; decide +kernel
      have hl : raw30457step0Labels = raw30457Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30457 raw30457Labels permutation158 permutation7
    mixedMoment B raw30457step0 raw30457step0Labels = mixedMoment B raw30457step1 raw30457step1Labels := by
      have ha : raw30457step1 = -raw30457step0 := by apply Matrix.ext; change ∀ i j, raw30457step1 i j = -(raw30457step0 i j); unfold raw30457step1 raw30457step0; decide +kernel
      have hl : raw30457step1Labels = raw30457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30457step1 raw30457step1Labels = mixedMoment B raw30457step2 raw30457step2Labels := by
      have ha : raw30457step2 = raw30457step1 := by apply Matrix.ext; unfold raw30457step2 raw30457step1; decide +kernel
      have hl : raw30457step1Labels = labelEmbedding1 ∘ raw30457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30457step1 raw30457step1Labels raw30457step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

theorem canonical30458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30458 raw30458Labels = mixedMoment B node3409 node3409Labels := by
  calc
    mixedMoment B raw30458 raw30458Labels = mixedMoment B raw30458step0 raw30458step0Labels := by
      have ha : raw30458step0 = (fun i j => raw30458 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30458step0 raw30458; decide +kernel
      have hl : raw30458step0Labels = raw30458Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30458 raw30458Labels permutation158 permutation7
    mixedMoment B raw30458step0 raw30458step0Labels = mixedMoment B raw30458step1 raw30458step1Labels := by
      have ha : raw30458step1 = -raw30458step0 := by apply Matrix.ext; change ∀ i j, raw30458step1 i j = -(raw30458step0 i j); unfold raw30458step1 raw30458step0; decide +kernel
      have hl : raw30458step1Labels = raw30458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30458step1 raw30458step1Labels = mixedMoment B raw30458step2 raw30458step2Labels := by
      have ha : raw30458step2 = raw30458step1 := by apply Matrix.ext; unfold raw30458step2 raw30458step1; decide +kernel
      have hl : raw30458step1Labels = labelEmbedding1 ∘ raw30458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30458step1 raw30458step1Labels raw30458step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3409 node3409Labels := by rfl

theorem canonical30459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30459 raw30459Labels = mixedMoment B node3465 node3465Labels := by
  calc
    mixedMoment B raw30459 raw30459Labels = mixedMoment B raw30459step0 raw30459step0Labels := by
      have ha : raw30459step0 = (fun i j => raw30459 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30459step0 raw30459; decide +kernel
      have hl : raw30459step0Labels = raw30459Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30459 raw30459Labels permutation158 permutation7
    mixedMoment B raw30459step0 raw30459step0Labels = mixedMoment B raw30459step1 raw30459step1Labels := by
      have ha : raw30459step1 = -raw30459step0 := by apply Matrix.ext; change ∀ i j, raw30459step1 i j = -(raw30459step0 i j); unfold raw30459step1 raw30459step0; decide +kernel
      have hl : raw30459step1Labels = raw30459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30459step1 raw30459step1Labels = mixedMoment B raw30459step2 raw30459step2Labels := by
      have ha : raw30459step2 = raw30459step1 := by apply Matrix.ext; unfold raw30459step2 raw30459step1; decide +kernel
      have hl : raw30459step1Labels = labelEmbedding1 ∘ raw30459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30459step1 raw30459step1Labels raw30459step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3465 node3465Labels := by rfl

theorem canonical30460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30460 raw30460Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw30460 raw30460Labels = mixedMoment B raw30460step0 raw30460step0Labels := by
      have ha : raw30460step0 = (fun i j => raw30460 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30460step0 raw30460; decide +kernel
      have hl : raw30460step0Labels = raw30460Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30460 raw30460Labels permutation158 permutation7
    mixedMoment B raw30460step0 raw30460step0Labels = mixedMoment B raw30460step1 raw30460step1Labels := by
      have ha : raw30460step1 = -raw30460step0 := by apply Matrix.ext; change ∀ i j, raw30460step1 i j = -(raw30460step0 i j); unfold raw30460step1 raw30460step0; decide +kernel
      have hl : raw30460step1Labels = raw30460step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30460step1 raw30460step1Labels = mixedMoment B raw30460step2 raw30460step2Labels := by
      have ha : raw30460step2 = raw30460step1 := by apply Matrix.ext; unfold raw30460step2 raw30460step1; decide +kernel
      have hl : raw30460step1Labels = labelEmbedding1 ∘ raw30460step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30460step1 raw30460step1Labels raw30460step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

theorem canonical30461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30461 raw30461Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw30461 raw30461Labels = mixedMoment B raw30461step0 raw30461step0Labels := by
      have ha : raw30461step0 = (fun i j => raw30461 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30461step0 raw30461; decide +kernel
      have hl : raw30461step0Labels = raw30461Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30461 raw30461Labels permutation159 permutation7
    mixedMoment B raw30461step0 raw30461step0Labels = mixedMoment B raw30461step1 raw30461step1Labels := by
      have ha : raw30461step1 = -raw30461step0 := by apply Matrix.ext; change ∀ i j, raw30461step1 i j = -(raw30461step0 i j); unfold raw30461step1 raw30461step0; decide +kernel
      have hl : raw30461step1Labels = raw30461step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30461step1 raw30461step1Labels = mixedMoment B raw30461step2 raw30461step2Labels := by
      have ha : raw30461step2 = raw30461step1 := by apply Matrix.ext; unfold raw30461step2 raw30461step1; decide +kernel
      have hl : raw30461step1Labels = labelEmbedding1 ∘ raw30461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30461step1 raw30461step1Labels raw30461step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

theorem canonical30462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30462 raw30462Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw30462 raw30462Labels = mixedMoment B raw30462step0 raw30462step0Labels := by
      have hz : ∀ j, raw30462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30462step0 = (fun i j => raw30462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30462step0 raw30462; decide +kernel
      have hl : raw30462step0Labels = raw30462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30462 raw30462Labels permutation434 hz
    mixedMoment B raw30462step0 raw30462step0Labels = mixedMoment B raw30462step1 raw30462step1Labels := by
      have ha : raw30462step1 = (fun i j => raw30462step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30462step1 raw30462step0; decide +kernel
      have hl : raw30462step1Labels = raw30462step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30462step0 raw30462step0Labels permutation33 permutation7
    mixedMoment B raw30462step1 raw30462step1Labels = mixedMoment B raw30462step2 raw30462step2Labels := by
      have ha : raw30462step2 = -raw30462step1 := by apply Matrix.ext; change ∀ i j, raw30462step2 i j = -(raw30462step1 i j); unfold raw30462step2 raw30462step1; decide +kernel
      have hl : raw30462step2Labels = raw30462step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30462step2 raw30462step2Labels = mixedMoment B raw30462step3 raw30462step3Labels := by
      have ha : raw30462step3 = raw30462step2 := by apply Matrix.ext; unfold raw30462step3 raw30462step2; decide +kernel
      have hl : raw30462step2Labels = labelEmbedding1 ∘ raw30462step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30462step2 raw30462step2Labels raw30462step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

theorem canonical30463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30463 raw30463Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw30463 raw30463Labels = mixedMoment B raw30463step0 raw30463step0Labels := by
      have hz : ∀ j, raw30463 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30463step0 = (fun i j => raw30463 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30463step0 raw30463; decide +kernel
      have hl : raw30463step0Labels = raw30463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30463 raw30463Labels permutation434 hz
    mixedMoment B raw30463step0 raw30463step0Labels = mixedMoment B raw30463step1 raw30463step1Labels := by
      have ha : raw30463step1 = (fun i j => raw30463step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30463step1 raw30463step0; decide +kernel
      have hl : raw30463step1Labels = raw30463step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30463step0 raw30463step0Labels permutation127 permutation5
    mixedMoment B raw30463step1 raw30463step1Labels = mixedMoment B raw30463step2 raw30463step2Labels := by
      have ha : raw30463step2 = raw30463step1 := by apply Matrix.ext; unfold raw30463step2 raw30463step1; decide +kernel
      have hl : raw30463step1Labels = labelEmbedding1 ∘ raw30463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30463step1 raw30463step1Labels raw30463step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30464 raw30464Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw30464 raw30464Labels = mixedMoment B raw30464step0 raw30464step0Labels := by
      have hz : ∀ j, raw30464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30464step0 = (fun i j => raw30464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30464step0 raw30464; decide +kernel
      have hl : raw30464step0Labels = raw30464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30464 raw30464Labels permutation434 hz
    mixedMoment B raw30464step0 raw30464step0Labels = mixedMoment B raw30464step1 raw30464step1Labels := by
      have ha : raw30464step1 = (fun i j => raw30464step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30464step1 raw30464step0; decide +kernel
      have hl : raw30464step1Labels = raw30464step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30464step0 raw30464step0Labels permutation124 permutation5
    mixedMoment B raw30464step1 raw30464step1Labels = mixedMoment B raw30464step2 raw30464step2Labels := by
      have ha : raw30464step2 = raw30464step1 := by apply Matrix.ext; unfold raw30464step2 raw30464step1; decide +kernel
      have hl : raw30464step1Labels = labelEmbedding1 ∘ raw30464step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30464step1 raw30464step1Labels raw30464step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

theorem canonical30465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30465 raw30465Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw30465 raw30465Labels = mixedMoment B raw30465step0 raw30465step0Labels := by
      have ha : raw30465step0 = (fun i j => raw30465 (permutation577 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30465step0 raw30465; decide +kernel
      have hl : raw30465step0Labels = raw30465Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30465 raw30465Labels permutation577 permutation5
    mixedMoment B raw30465step0 raw30465step0Labels = mixedMoment B raw30465step1 raw30465step1Labels := by
      have ha : raw30465step1 = raw30465step0 := by apply Matrix.ext; unfold raw30465step1 raw30465step0; decide +kernel
      have hl : raw30465step0Labels = labelEmbedding1 ∘ raw30465step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30465step0 raw30465step0Labels raw30465step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

theorem canonical30466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30466 raw30466Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw30466 raw30466Labels = mixedMoment B raw30466step0 raw30466step0Labels := by
      have hz : ∀ j, raw30466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30466step0 = (fun i j => raw30466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30466step0 raw30466; decide +kernel
      have hl : raw30466step0Labels = raw30466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30466 raw30466Labels permutation434 hz
    mixedMoment B raw30466step0 raw30466step0Labels = mixedMoment B raw30466step1 raw30466step1Labels := by
      have ha : raw30466step1 = (fun i j => raw30466step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30466step1 raw30466step0; decide +kernel
      have hl : raw30466step1Labels = raw30466step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30466step0 raw30466step0Labels permutation33 permutation7
    mixedMoment B raw30466step1 raw30466step1Labels = mixedMoment B raw30466step2 raw30466step2Labels := by
      have ha : raw30466step2 = -raw30466step1 := by apply Matrix.ext; change ∀ i j, raw30466step2 i j = -(raw30466step1 i j); unfold raw30466step2 raw30466step1; decide +kernel
      have hl : raw30466step2Labels = raw30466step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30466step2 raw30466step2Labels = mixedMoment B raw30466step3 raw30466step3Labels := by
      have ha : raw30466step3 = raw30466step2 := by apply Matrix.ext; unfold raw30466step3 raw30466step2; decide +kernel
      have hl : raw30466step2Labels = labelEmbedding1 ∘ raw30466step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30466step2 raw30466step2Labels raw30466step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical30467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30467 raw30467Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw30467 raw30467Labels = mixedMoment B raw30467step0 raw30467step0Labels := by
      have hz : ∀ j, raw30467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30467step0 = (fun i j => raw30467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30467step0 raw30467; decide +kernel
      have hl : raw30467step0Labels = raw30467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30467 raw30467Labels permutation434 hz
    mixedMoment B raw30467step0 raw30467step0Labels = mixedMoment B raw30467step1 raw30467step1Labels := by
      have ha : raw30467step1 = (fun i j => raw30467step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30467step1 raw30467step0; decide +kernel
      have hl : raw30467step1Labels = raw30467step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30467step0 raw30467step0Labels permutation32 permutation7
    mixedMoment B raw30467step1 raw30467step1Labels = mixedMoment B raw30467step2 raw30467step2Labels := by
      have ha : raw30467step2 = -raw30467step1 := by apply Matrix.ext; change ∀ i j, raw30467step2 i j = -(raw30467step1 i j); unfold raw30467step2 raw30467step1; decide +kernel
      have hl : raw30467step2Labels = raw30467step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30467step2 raw30467step2Labels = mixedMoment B raw30467step3 raw30467step3Labels := by
      have ha : raw30467step3 = raw30467step2 := by apply Matrix.ext; unfold raw30467step3 raw30467step2; decide +kernel
      have hl : raw30467step2Labels = labelEmbedding1 ∘ raw30467step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30467step2 raw30467step2Labels raw30467step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

theorem canonical30468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30468 raw30468Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw30468 raw30468Labels = mixedMoment B raw30468step0 raw30468step0Labels := by
      have hz : ∀ j, raw30468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30468step0 = (fun i j => raw30468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30468step0 raw30468; decide +kernel
      have hl : raw30468step0Labels = raw30468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30468 raw30468Labels permutation434 hz
    mixedMoment B raw30468step0 raw30468step0Labels = mixedMoment B raw30468step1 raw30468step1Labels := by
      have ha : raw30468step1 = (fun i j => raw30468step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30468step1 raw30468step0; decide +kernel
      have hl : raw30468step1Labels = raw30468step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30468step0 raw30468step0Labels permutation151 permutation5
    mixedMoment B raw30468step1 raw30468step1Labels = mixedMoment B raw30468step2 raw30468step2Labels := by
      have ha : raw30468step2 = raw30468step1 := by apply Matrix.ext; unfold raw30468step2 raw30468step1; decide +kernel
      have hl : raw30468step1Labels = labelEmbedding1 ∘ raw30468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30468step1 raw30468step1Labels raw30468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

theorem canonical30469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30469 raw30469Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw30469 raw30469Labels = mixedMoment B raw30469step0 raw30469step0Labels := by
      have hz : ∀ j, raw30469 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30469step0 = (fun i j => raw30469 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30469step0 raw30469; decide +kernel
      have hl : raw30469step0Labels = raw30469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30469 raw30469Labels permutation434 hz
    mixedMoment B raw30469step0 raw30469step0Labels = mixedMoment B raw30469step1 raw30469step1Labels := by
      have ha : raw30469step1 = (fun i j => raw30469step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30469step1 raw30469step0; decide +kernel
      have hl : raw30469step1Labels = raw30469step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30469step0 raw30469step0Labels permutation148 permutation5
    mixedMoment B raw30469step1 raw30469step1Labels = mixedMoment B raw30469step2 raw30469step2Labels := by
      have ha : raw30469step2 = raw30469step1 := by apply Matrix.ext; unfold raw30469step2 raw30469step1; decide +kernel
      have hl : raw30469step1Labels = labelEmbedding1 ∘ raw30469step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30469step1 raw30469step1Labels raw30469step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

theorem canonical30470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30470 raw30470Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw30470 raw30470Labels = mixedMoment B raw30470step0 raw30470step0Labels := by
      have ha : raw30470step0 = (fun i j => raw30470 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30470step0 raw30470; decide +kernel
      have hl : raw30470step0Labels = raw30470Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30470 raw30470Labels permutation674 permutation5
    mixedMoment B raw30470step0 raw30470step0Labels = mixedMoment B raw30470step1 raw30470step1Labels := by
      have ha : raw30470step1 = raw30470step0 := by apply Matrix.ext; unfold raw30470step1 raw30470step0; decide +kernel
      have hl : raw30470step0Labels = labelEmbedding1 ∘ raw30470step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30470step0 raw30470step0Labels raw30470step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

theorem canonical30471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30471 raw30471Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw30471 raw30471Labels = mixedMoment B raw30471step0 raw30471step0Labels := by
      have hz : ∀ j, raw30471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30471step0 = (fun i j => raw30471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30471step0 raw30471; decide +kernel
      have hl : raw30471step0Labels = raw30471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30471 raw30471Labels permutation434 hz
    mixedMoment B raw30471step0 raw30471step0Labels = mixedMoment B raw30471step1 raw30471step1Labels := by
      have ha : raw30471step1 = (fun i j => raw30471step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30471step1 raw30471step0; decide +kernel
      have hl : raw30471step1Labels = raw30471step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30471step0 raw30471step0Labels permutation32 permutation7
    mixedMoment B raw30471step1 raw30471step1Labels = mixedMoment B raw30471step2 raw30471step2Labels := by
      have ha : raw30471step2 = -raw30471step1 := by apply Matrix.ext; change ∀ i j, raw30471step2 i j = -(raw30471step1 i j); unfold raw30471step2 raw30471step1; decide +kernel
      have hl : raw30471step2Labels = raw30471step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30471step2 raw30471step2Labels = mixedMoment B raw30471step3 raw30471step3Labels := by
      have ha : raw30471step3 = raw30471step2 := by apply Matrix.ext; unfold raw30471step3 raw30471step2; decide +kernel
      have hl : raw30471step2Labels = labelEmbedding1 ∘ raw30471step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30471step2 raw30471step2Labels raw30471step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical30472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30472 raw30472Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw30472 raw30472Labels = mixedMoment B raw30472step0 raw30472step0Labels := by
      have hz : ∀ j, raw30472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30472step0 = (fun i j => raw30472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30472step0 raw30472; decide +kernel
      have hl : raw30472step0Labels = raw30472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30472 raw30472Labels permutation434 hz
    _ = mixedMoment B node3694 node3694Labels := by rfl

theorem canonical30473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30473 raw30473Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw30473 raw30473Labels = mixedMoment B raw30473step0 raw30473step0Labels := by
      have hz : ∀ j, raw30473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30473step0 = (fun i j => raw30473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30473step0 raw30473; decide +kernel
      have hl : raw30473step0Labels = raw30473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30473 raw30473Labels permutation434 hz
    _ = mixedMoment B node2489 node2489Labels := by rfl

theorem canonical30474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30474 raw30474Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw30474 raw30474Labels = mixedMoment B raw30474step0 raw30474step0Labels := by
      have hz : ∀ j, raw30474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30474step0 = (fun i j => raw30474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30474step0 raw30474; decide +kernel
      have hl : raw30474step0Labels = raw30474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30474 raw30474Labels permutation434 hz
    _ = mixedMoment B node2342 node2342Labels := by rfl

theorem canonical30475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30475 raw30475Labels = mixedMoment B node2322 node2322Labels := by
  calc
    _ = mixedMoment B node2322 node2322Labels := by rfl

theorem canonical30476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30476 raw30476Labels = mixedMoment B node2326 node2326Labels := by
  calc
    mixedMoment B raw30476 raw30476Labels = mixedMoment B raw30476step0 raw30476step0Labels := by
      have hz : ∀ j, raw30476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30476step0 = (fun i j => raw30476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30476step0 raw30476; decide +kernel
      have hl : raw30476step0Labels = raw30476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30476 raw30476Labels permutation434 hz
    mixedMoment B raw30476step0 raw30476step0Labels = mixedMoment B raw30476step1 raw30476step1Labels := by
      have ha : raw30476step1 = (fun i j => raw30476step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30476step1 raw30476step0; decide +kernel
      have hl : raw30476step1Labels = raw30476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30476step0 raw30476step0Labels permutation33 permutation2
    _ = mixedMoment B node2326 node2326Labels := by rfl

theorem canonical30477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30477 raw30477Labels = mixedMoment B node2326 node2326Labels := by
  calc
    mixedMoment B raw30477 raw30477Labels = mixedMoment B raw30477step0 raw30477step0Labels := by
      have hz : ∀ j, raw30477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30477step0 = (fun i j => raw30477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30477step0 raw30477; decide +kernel
      have hl : raw30477step0Labels = raw30477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30477 raw30477Labels permutation434 hz
    _ = mixedMoment B node2326 node2326Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30623 raw30623Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw30623 raw30623Labels = mixedMoment B raw30623step0 raw30623step0Labels := by
      have hz : ∀ j, raw30623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30623step0 = (fun i j => raw30623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30623step0 raw30623; decide +kernel
      have hl : raw30623step0Labels = raw30623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30623 raw30623Labels permutation434 hz
    mixedMoment B raw30623step0 raw30623step0Labels = mixedMoment B raw30623step1 raw30623step1Labels := by
      have hz : ∀ j, raw30623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30623step1 = (fun i j => raw30623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30623step1 raw30623step0; decide +kernel
      have hl : raw30623step1Labels = raw30623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30623step0 raw30623step0Labels permutation80 hz
    mixedMoment B raw30623step1 raw30623step1Labels = mixedMoment B raw30623step2 raw30623step2Labels := by
      have ha : raw30623step2 = (fun i j => raw30623step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30623step2 raw30623step1; decide +kernel
      have hl : raw30623step2Labels = raw30623step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30623step1 raw30623step1Labels permutation25 permutation7
    mixedMoment B raw30623step2 raw30623step2Labels = mixedMoment B raw30623step3 raw30623step3Labels := by
      have ha : raw30623step3 = raw30623step2 := by apply Matrix.ext; unfold raw30623step3 raw30623step2; decide +kernel
      have hl : raw30623step2Labels = labelEmbedding1 ∘ raw30623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30623step2 raw30623step2Labels raw30623step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical30624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30624 raw30624Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw30624 raw30624Labels = mixedMoment B raw30624step0 raw30624step0Labels := by
      have hz : ∀ j, raw30624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30624step0 = (fun i j => raw30624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30624step0 raw30624; decide +kernel
      have hl : raw30624step0Labels = raw30624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30624 raw30624Labels permutation434 hz
    mixedMoment B raw30624step0 raw30624step0Labels = mixedMoment B raw30624step1 raw30624step1Labels := by
      have ha : raw30624step1 = (fun i j => raw30624step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30624step1 raw30624step0; decide +kernel
      have hl : raw30624step1Labels = raw30624step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30624step0 raw30624step0Labels permutation127 permutation7
    mixedMoment B raw30624step1 raw30624step1Labels = mixedMoment B raw30624step2 raw30624step2Labels := by
      have ha : raw30624step2 = raw30624step1 := by apply Matrix.ext; unfold raw30624step2 raw30624step1; decide +kernel
      have hl : raw30624step1Labels = labelEmbedding1 ∘ raw30624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30624step1 raw30624step1Labels raw30624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical30625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30625 raw30625Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw30625 raw30625Labels = mixedMoment B raw30625step0 raw30625step0Labels := by
      have hz : ∀ j, raw30625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30625step0 = (fun i j => raw30625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30625step0 raw30625; decide +kernel
      have hl : raw30625step0Labels = raw30625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30625 raw30625Labels permutation346 hz
    mixedMoment B raw30625step0 raw30625step0Labels = mixedMoment B raw30625step1 raw30625step1Labels := by
      have ha : raw30625step1 = (fun i j => raw30625step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30625step1 raw30625step0; decide +kernel
      have hl : raw30625step1Labels = raw30625step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30625step0 raw30625step0Labels permutation127 permutation7
    mixedMoment B raw30625step1 raw30625step1Labels = mixedMoment B raw30625step2 raw30625step2Labels := by
      have ha : raw30625step2 = raw30625step1 := by apply Matrix.ext; unfold raw30625step2 raw30625step1; decide +kernel
      have hl : raw30625step1Labels = labelEmbedding1 ∘ raw30625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30625step1 raw30625step1Labels raw30625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical30626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30626 raw30626Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw30626 raw30626Labels = mixedMoment B raw30626step0 raw30626step0Labels := by
      have hz : ∀ j, raw30626 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30626step0 = (fun i j => raw30626 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30626step0 raw30626; decide +kernel
      have hl : raw30626step0Labels = raw30626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30626 raw30626Labels permutation434 hz
    mixedMoment B raw30626step0 raw30626step0Labels = mixedMoment B raw30626step1 raw30626step1Labels := by
      have hz : ∀ j, raw30626step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30626step1 = (fun i j => raw30626step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30626step1 raw30626step0; decide +kernel
      have hl : raw30626step1Labels = raw30626step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30626step0 raw30626step0Labels permutation80 hz
    mixedMoment B raw30626step1 raw30626step1Labels = mixedMoment B raw30626step2 raw30626step2Labels := by
      have ha : raw30626step2 = (fun i j => raw30626step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30626step2 raw30626step1; decide +kernel
      have hl : raw30626step2Labels = raw30626step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30626step1 raw30626step1Labels permutation25 permutation7
    mixedMoment B raw30626step2 raw30626step2Labels = mixedMoment B raw30626step3 raw30626step3Labels := by
      have ha : raw30626step3 = raw30626step2 := by apply Matrix.ext; unfold raw30626step3 raw30626step2; decide +kernel
      have hl : raw30626step2Labels = labelEmbedding1 ∘ raw30626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30626step2 raw30626step2Labels raw30626step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical30627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30627 raw30627Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw30627 raw30627Labels = mixedMoment B raw30627step0 raw30627step0Labels := by
      have hz : ∀ j, raw30627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30627step0 = (fun i j => raw30627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30627step0 raw30627; decide +kernel
      have hl : raw30627step0Labels = raw30627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30627 raw30627Labels permutation434 hz
    mixedMoment B raw30627step0 raw30627step0Labels = mixedMoment B raw30627step1 raw30627step1Labels := by
      have hz : ∀ j, raw30627step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30627step1 = (fun i j => raw30627step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30627step1 raw30627step0; decide +kernel
      have hl : raw30627step1Labels = raw30627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30627step0 raw30627step0Labels permutation80 hz
    mixedMoment B raw30627step1 raw30627step1Labels = mixedMoment B raw30627step2 raw30627step2Labels := by
      have ha : raw30627step2 = (fun i j => raw30627step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30627step2 raw30627step1; decide +kernel
      have hl : raw30627step2Labels = raw30627step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30627step1 raw30627step1Labels permutation25 permutation7
    mixedMoment B raw30627step2 raw30627step2Labels = mixedMoment B raw30627step3 raw30627step3Labels := by
      have ha : raw30627step3 = raw30627step2 := by apply Matrix.ext; unfold raw30627step3 raw30627step2; decide +kernel
      have hl : raw30627step2Labels = labelEmbedding1 ∘ raw30627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30627step2 raw30627step2Labels raw30627step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

theorem canonical30628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30628 raw30628Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw30628 raw30628Labels = mixedMoment B raw30628step0 raw30628step0Labels := by
      have hz : ∀ j, raw30628 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30628step0 = (fun i j => raw30628 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30628step0 raw30628; decide +kernel
      have hl : raw30628step0Labels = raw30628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30628 raw30628Labels permutation434 hz
    mixedMoment B raw30628step0 raw30628step0Labels = mixedMoment B raw30628step1 raw30628step1Labels := by
      have ha : raw30628step1 = (fun i j => raw30628step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30628step1 raw30628step0; decide +kernel
      have hl : raw30628step1Labels = raw30628step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30628step0 raw30628step0Labels permutation127 permutation7
    mixedMoment B raw30628step1 raw30628step1Labels = mixedMoment B raw30628step2 raw30628step2Labels := by
      have ha : raw30628step2 = raw30628step1 := by apply Matrix.ext; unfold raw30628step2 raw30628step1; decide +kernel
      have hl : raw30628step1Labels = labelEmbedding1 ∘ raw30628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30628step1 raw30628step1Labels raw30628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

theorem canonical30629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30629 raw30629Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw30629 raw30629Labels = mixedMoment B raw30629step0 raw30629step0Labels := by
      have hz : ∀ j, raw30629 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30629step0 = (fun i j => raw30629 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30629step0 raw30629; decide +kernel
      have hl : raw30629step0Labels = raw30629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30629 raw30629Labels permutation434 hz
    mixedMoment B raw30629step0 raw30629step0Labels = mixedMoment B raw30629step1 raw30629step1Labels := by
      have ha : raw30629step1 = (fun i j => raw30629step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30629step1 raw30629step0; decide +kernel
      have hl : raw30629step1Labels = raw30629step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30629step0 raw30629step0Labels permutation127 permutation7
    mixedMoment B raw30629step1 raw30629step1Labels = mixedMoment B raw30629step2 raw30629step2Labels := by
      have ha : raw30629step2 = raw30629step1 := by apply Matrix.ext; unfold raw30629step2 raw30629step1; decide +kernel
      have hl : raw30629step1Labels = labelEmbedding1 ∘ raw30629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30629step1 raw30629step1Labels raw30629step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical30630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30630 raw30630Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw30630 raw30630Labels = mixedMoment B raw30630step0 raw30630step0Labels := by
      have ha : raw30630step0 = (fun i j => raw30630 (permutation584 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30630step0 raw30630; decide +kernel
      have hl : raw30630step0Labels = raw30630Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30630 raw30630Labels permutation584 permutation7
    mixedMoment B raw30630step0 raw30630step0Labels = mixedMoment B raw30630step1 raw30630step1Labels := by
      have ha : raw30630step1 = raw30630step0 := by apply Matrix.ext; unfold raw30630step1 raw30630step0; decide +kernel
      have hl : raw30630step0Labels = labelEmbedding1 ∘ raw30630step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30630step0 raw30630step0Labels raw30630step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

theorem canonical30631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30631 raw30631Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw30631 raw30631Labels = mixedMoment B raw30631step0 raw30631step0Labels := by
      have hz : ∀ j, raw30631 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30631step0 = (fun i j => raw30631 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30631step0 raw30631; decide +kernel
      have hl : raw30631step0Labels = raw30631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30631 raw30631Labels permutation434 hz
    mixedMoment B raw30631step0 raw30631step0Labels = mixedMoment B raw30631step1 raw30631step1Labels := by
      have ha : raw30631step1 = (fun i j => raw30631step0 (permutation121 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30631step1 raw30631step0; decide +kernel
      have hl : raw30631step1Labels = raw30631step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30631step0 raw30631step0Labels permutation121 permutation7
    mixedMoment B raw30631step1 raw30631step1Labels = mixedMoment B raw30631step2 raw30631step2Labels := by
      have ha : raw30631step2 = raw30631step1 := by apply Matrix.ext; unfold raw30631step2 raw30631step1; decide +kernel
      have hl : raw30631step1Labels = labelEmbedding1 ∘ raw30631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30631step1 raw30631step1Labels raw30631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical30632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30632 raw30632Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw30632 raw30632Labels = mixedMoment B raw30632step0 raw30632step0Labels := by
      have hz : ∀ j, raw30632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30632step0 = (fun i j => raw30632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30632step0 raw30632; decide +kernel
      have hl : raw30632step0Labels = raw30632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30632 raw30632Labels permutation346 hz
    mixedMoment B raw30632step0 raw30632step0Labels = mixedMoment B raw30632step1 raw30632step1Labels := by
      have ha : raw30632step1 = (fun i j => raw30632step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30632step1 raw30632step0; decide +kernel
      have hl : raw30632step1Labels = raw30632step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30632step0 raw30632step0Labels permutation127 permutation7
    mixedMoment B raw30632step1 raw30632step1Labels = mixedMoment B raw30632step2 raw30632step2Labels := by
      have ha : raw30632step2 = raw30632step1 := by apply Matrix.ext; unfold raw30632step2 raw30632step1; decide +kernel
      have hl : raw30632step1Labels = labelEmbedding1 ∘ raw30632step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30632step1 raw30632step1Labels raw30632step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

theorem canonical30633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30633 raw30633Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw30633 raw30633Labels = mixedMoment B raw30633step0 raw30633step0Labels := by
      have hz : ∀ j, raw30633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30633step0 = (fun i j => raw30633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30633step0 raw30633; decide +kernel
      have hl : raw30633step0Labels = raw30633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30633 raw30633Labels permutation346 hz
    mixedMoment B raw30633step0 raw30633step0Labels = mixedMoment B raw30633step1 raw30633step1Labels := by
      have ha : raw30633step1 = (fun i j => raw30633step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30633step1 raw30633step0; decide +kernel
      have hl : raw30633step1Labels = raw30633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30633step0 raw30633step0Labels permutation127 permutation7
    mixedMoment B raw30633step1 raw30633step1Labels = mixedMoment B raw30633step2 raw30633step2Labels := by
      have ha : raw30633step2 = raw30633step1 := by apply Matrix.ext; unfold raw30633step2 raw30633step1; decide +kernel
      have hl : raw30633step1Labels = labelEmbedding1 ∘ raw30633step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30633step1 raw30633step1Labels raw30633step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical30634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30634 raw30634Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw30634 raw30634Labels = mixedMoment B raw30634step0 raw30634step0Labels := by
      have ha : raw30634step0 = (fun i j => raw30634 (permutation589 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30634step0 raw30634; decide +kernel
      have hl : raw30634step0Labels = raw30634Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30634 raw30634Labels permutation589 permutation7
    mixedMoment B raw30634step0 raw30634step0Labels = mixedMoment B raw30634step1 raw30634step1Labels := by
      have ha : raw30634step1 = raw30634step0 := by apply Matrix.ext; unfold raw30634step1 raw30634step0; decide +kernel
      have hl : raw30634step0Labels = labelEmbedding1 ∘ raw30634step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30634step0 raw30634step0Labels raw30634step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

theorem canonical30635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30635 raw30635Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw30635 raw30635Labels = mixedMoment B raw30635step0 raw30635step0Labels := by
      have hz : ∀ j, raw30635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30635step0 = (fun i j => raw30635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30635step0 raw30635; decide +kernel
      have hl : raw30635step0Labels = raw30635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30635 raw30635Labels permutation346 hz
    mixedMoment B raw30635step0 raw30635step0Labels = mixedMoment B raw30635step1 raw30635step1Labels := by
      have ha : raw30635step1 = (fun i j => raw30635step0 (permutation121 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30635step1 raw30635step0; decide +kernel
      have hl : raw30635step1Labels = raw30635step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30635step0 raw30635step0Labels permutation121 permutation7
    mixedMoment B raw30635step1 raw30635step1Labels = mixedMoment B raw30635step2 raw30635step2Labels := by
      have ha : raw30635step2 = raw30635step1 := by apply Matrix.ext; unfold raw30635step2 raw30635step1; decide +kernel
      have hl : raw30635step1Labels = labelEmbedding1 ∘ raw30635step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30635step1 raw30635step1Labels raw30635step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical30636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30636 raw30636Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw30636 raw30636Labels = mixedMoment B raw30636step0 raw30636step0Labels := by
      have hz : ∀ j, raw30636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30636step0 = (fun i j => raw30636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30636step0 raw30636; decide +kernel
      have hl : raw30636step0Labels = raw30636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30636 raw30636Labels permutation434 hz
    mixedMoment B raw30636step0 raw30636step0Labels = mixedMoment B raw30636step1 raw30636step1Labels := by
      have hz : ∀ j, raw30636step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30636step1 = (fun i j => raw30636step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30636step1 raw30636step0; decide +kernel
      have hl : raw30636step1Labels = raw30636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30636step0 raw30636step0Labels permutation80 hz
    mixedMoment B raw30636step1 raw30636step1Labels = mixedMoment B raw30636step2 raw30636step2Labels := by
      have ha : raw30636step2 = (fun i j => raw30636step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30636step2 raw30636step1; decide +kernel
      have hl : raw30636step2Labels = raw30636step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30636step1 raw30636step1Labels permutation25 permutation7
    mixedMoment B raw30636step2 raw30636step2Labels = mixedMoment B raw30636step3 raw30636step3Labels := by
      have ha : raw30636step3 = raw30636step2 := by apply Matrix.ext; unfold raw30636step3 raw30636step2; decide +kernel
      have hl : raw30636step2Labels = labelEmbedding1 ∘ raw30636step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30636step2 raw30636step2Labels raw30636step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2167 node2167Labels := by rfl

theorem canonical30637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30637 raw30637Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw30637 raw30637Labels = mixedMoment B raw30637step0 raw30637step0Labels := by
      have hz : ∀ j, raw30637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30637step0 = (fun i j => raw30637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30637step0 raw30637; decide +kernel
      have hl : raw30637step0Labels = raw30637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30637 raw30637Labels permutation434 hz
    mixedMoment B raw30637step0 raw30637step0Labels = mixedMoment B raw30637step1 raw30637step1Labels := by
      have hz : ∀ j, raw30637step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30637step1 = (fun i j => raw30637step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30637step1 raw30637step0; decide +kernel
      have hl : raw30637step1Labels = raw30637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30637step0 raw30637step0Labels permutation80 hz
    mixedMoment B raw30637step1 raw30637step1Labels = mixedMoment B raw30637step2 raw30637step2Labels := by
      have ha : raw30637step2 = (fun i j => raw30637step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30637step2 raw30637step1; decide +kernel
      have hl : raw30637step2Labels = raw30637step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30637step1 raw30637step1Labels permutation25 permutation7
    mixedMoment B raw30637step2 raw30637step2Labels = mixedMoment B raw30637step3 raw30637step3Labels := by
      have ha : raw30637step3 = raw30637step2 := by apply Matrix.ext; unfold raw30637step3 raw30637step2; decide +kernel
      have hl : raw30637step2Labels = labelEmbedding1 ∘ raw30637step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30637step2 raw30637step2Labels raw30637step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

theorem canonical30638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30638 raw30638Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw30638 raw30638Labels = mixedMoment B raw30638step0 raw30638step0Labels := by
      have hz : ∀ j, raw30638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30638step0 = (fun i j => raw30638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30638step0 raw30638; decide +kernel
      have hl : raw30638step0Labels = raw30638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30638 raw30638Labels permutation434 hz
    mixedMoment B raw30638step0 raw30638step0Labels = mixedMoment B raw30638step1 raw30638step1Labels := by
      have ha : raw30638step1 = (fun i j => raw30638step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30638step1 raw30638step0; decide +kernel
      have hl : raw30638step1Labels = raw30638step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30638step0 raw30638step0Labels permutation127 permutation7
    mixedMoment B raw30638step1 raw30638step1Labels = mixedMoment B raw30638step2 raw30638step2Labels := by
      have ha : raw30638step2 = raw30638step1 := by apply Matrix.ext; unfold raw30638step2 raw30638step1; decide +kernel
      have hl : raw30638step1Labels = labelEmbedding1 ∘ raw30638step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30638step1 raw30638step1Labels raw30638step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

theorem canonical30639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30639 raw30639Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw30639 raw30639Labels = mixedMoment B raw30639step0 raw30639step0Labels := by
      have hz : ∀ j, raw30639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30639step0 = (fun i j => raw30639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30639step0 raw30639; decide +kernel
      have hl : raw30639step0Labels = raw30639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30639 raw30639Labels permutation346 hz
    mixedMoment B raw30639step0 raw30639step0Labels = mixedMoment B raw30639step1 raw30639step1Labels := by
      have ha : raw30639step1 = (fun i j => raw30639step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30639step1 raw30639step0; decide +kernel
      have hl : raw30639step1Labels = raw30639step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30639step0 raw30639step0Labels permutation127 permutation7
    mixedMoment B raw30639step1 raw30639step1Labels = mixedMoment B raw30639step2 raw30639step2Labels := by
      have ha : raw30639step2 = raw30639step1 := by apply Matrix.ext; unfold raw30639step2 raw30639step1; decide +kernel
      have hl : raw30639step1Labels = labelEmbedding1 ∘ raw30639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30639step1 raw30639step1Labels raw30639step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

theorem canonical30640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30640 raw30640Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw30640 raw30640Labels = mixedMoment B raw30640step0 raw30640step0Labels := by
      have hz : ∀ j, raw30640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30640step0 = (fun i j => raw30640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30640step0 raw30640; decide +kernel
      have hl : raw30640step0Labels = raw30640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30640 raw30640Labels permutation434 hz
    mixedMoment B raw30640step0 raw30640step0Labels = mixedMoment B raw30640step1 raw30640step1Labels := by
      have hz : ∀ j, raw30640step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30640step1 = (fun i j => raw30640step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30640step1 raw30640step0; decide +kernel
      have hl : raw30640step1Labels = raw30640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30640step0 raw30640step0Labels permutation80 hz
    mixedMoment B raw30640step1 raw30640step1Labels = mixedMoment B raw30640step2 raw30640step2Labels := by
      have ha : raw30640step2 = (fun i j => raw30640step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30640step2 raw30640step1; decide +kernel
      have hl : raw30640step2Labels = raw30640step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30640step1 raw30640step1Labels permutation25 permutation7
    mixedMoment B raw30640step2 raw30640step2Labels = mixedMoment B raw30640step3 raw30640step3Labels := by
      have ha : raw30640step3 = raw30640step2 := by apply Matrix.ext; unfold raw30640step3 raw30640step2; decide +kernel
      have hl : raw30640step2Labels = labelEmbedding1 ∘ raw30640step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30640step2 raw30640step2Labels raw30640step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical30641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30641 raw30641Labels = mixedMoment B node2258 node2258Labels := by
  calc
    mixedMoment B raw30641 raw30641Labels = mixedMoment B raw30641step0 raw30641step0Labels := by
      have hz : ∀ j, raw30641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30641step0 = (fun i j => raw30641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30641step0 raw30641; decide +kernel
      have hl : raw30641step0Labels = raw30641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30641 raw30641Labels permutation434 hz
    mixedMoment B raw30641step0 raw30641step0Labels = mixedMoment B raw30641step1 raw30641step1Labels := by
      have hz : ∀ j, raw30641step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30641step1 = (fun i j => raw30641step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30641step1 raw30641step0; decide +kernel
      have hl : raw30641step1Labels = raw30641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30641step0 raw30641step0Labels permutation80 hz
    mixedMoment B raw30641step1 raw30641step1Labels = mixedMoment B raw30641step2 raw30641step2Labels := by
      have ha : raw30641step2 = (fun i j => raw30641step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30641step2 raw30641step1; decide +kernel
      have hl : raw30641step2Labels = raw30641step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30641step1 raw30641step1Labels permutation29 permutation5
    mixedMoment B raw30641step2 raw30641step2Labels = mixedMoment B raw30641step3 raw30641step3Labels := by
      have ha : raw30641step3 = raw30641step2 := by apply Matrix.ext; unfold raw30641step3 raw30641step2; decide +kernel
      have hl : raw30641step2Labels = labelEmbedding1 ∘ raw30641step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30641step2 raw30641step2Labels raw30641step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2258 node2258Labels := by rfl

theorem canonical30642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30642 raw30642Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw30642 raw30642Labels = mixedMoment B raw30642step0 raw30642step0Labels := by
      have hz : ∀ j, raw30642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30642step0 = (fun i j => raw30642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30642step0 raw30642; decide +kernel
      have hl : raw30642step0Labels = raw30642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30642 raw30642Labels permutation434 hz
    mixedMoment B raw30642step0 raw30642step0Labels = mixedMoment B raw30642step1 raw30642step1Labels := by
      have hz : ∀ j, raw30642step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30642step1 = (fun i j => raw30642step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30642step1 raw30642step0; decide +kernel
      have hl : raw30642step1Labels = raw30642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30642step0 raw30642step0Labels permutation80 hz
    mixedMoment B raw30642step1 raw30642step1Labels = mixedMoment B raw30642step2 raw30642step2Labels := by
      have ha : raw30642step2 = (fun i j => raw30642step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30642step2 raw30642step1; decide +kernel
      have hl : raw30642step2Labels = raw30642step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30642step1 raw30642step1Labels permutation31 permutation5
    mixedMoment B raw30642step2 raw30642step2Labels = mixedMoment B raw30642step3 raw30642step3Labels := by
      have ha : raw30642step3 = raw30642step2 := by apply Matrix.ext; unfold raw30642step3 raw30642step2; decide +kernel
      have hl : raw30642step2Labels = labelEmbedding1 ∘ raw30642step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30642step2 raw30642step2Labels raw30642step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2286 node2286Labels := by rfl

theorem canonical30643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30643 raw30643Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw30643 raw30643Labels = mixedMoment B raw30643step0 raw30643step0Labels := by
      have hz : ∀ j, raw30643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30643step0 = (fun i j => raw30643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30643step0 raw30643; decide +kernel
      have hl : raw30643step0Labels = raw30643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30643 raw30643Labels permutation434 hz
    mixedMoment B raw30643step0 raw30643step0Labels = mixedMoment B raw30643step1 raw30643step1Labels := by
      have ha : raw30643step1 = (fun i j => raw30643step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30643step1 raw30643step0; decide +kernel
      have hl : raw30643step1Labels = raw30643step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30643step0 raw30643step0Labels permutation139 permutation5
    mixedMoment B raw30643step1 raw30643step1Labels = mixedMoment B raw30643step2 raw30643step2Labels := by
      have ha : raw30643step2 = raw30643step1 := by apply Matrix.ext; unfold raw30643step2 raw30643step1; decide +kernel
      have hl : raw30643step1Labels = labelEmbedding1 ∘ raw30643step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30643step1 raw30643step1Labels raw30643step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

theorem canonical30644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30644 raw30644Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw30644 raw30644Labels = mixedMoment B raw30644step0 raw30644step0Labels := by
      have hz : ∀ j, raw30644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30644step0 = (fun i j => raw30644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30644step0 raw30644; decide +kernel
      have hl : raw30644step0Labels = raw30644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30644 raw30644Labels permutation346 hz
    mixedMoment B raw30644step0 raw30644step0Labels = mixedMoment B raw30644step1 raw30644step1Labels := by
      have ha : raw30644step1 = (fun i j => raw30644step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30644step1 raw30644step0; decide +kernel
      have hl : raw30644step1Labels = raw30644step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30644step0 raw30644step0Labels permutation139 permutation5
    mixedMoment B raw30644step1 raw30644step1Labels = mixedMoment B raw30644step2 raw30644step2Labels := by
      have ha : raw30644step2 = raw30644step1 := by apply Matrix.ext; unfold raw30644step2 raw30644step1; decide +kernel
      have hl : raw30644step1Labels = labelEmbedding1 ∘ raw30644step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30644step1 raw30644step1Labels raw30644step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30730 raw30730Labels = mixedMoment B node3775 node3775Labels := by
  calc
    mixedMoment B raw30730 raw30730Labels = mixedMoment B raw30730step0 raw30730step0Labels := by
      have hz : ∀ j, raw30730 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30730step0 = (fun i j => raw30730 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30730step0 raw30730; decide +kernel
      have hl : raw30730step0Labels = raw30730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30730 raw30730Labels permutation434 hz
    mixedMoment B raw30730step0 raw30730step0Labels = mixedMoment B raw30730step1 raw30730step1Labels := by
      have hz : ∀ j, raw30730step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30730step1 = (fun i j => raw30730step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30730step1 raw30730step0; decide +kernel
      have hl : raw30730step1Labels = raw30730step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30730step0 raw30730step0Labels permutation80 hz
    mixedMoment B raw30730step1 raw30730step1Labels = mixedMoment B raw30730step2 raw30730step2Labels := by
      have ha : raw30730step2 = (fun i j => raw30730step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30730step2 raw30730step1; decide +kernel
      have hl : raw30730step2Labels = raw30730step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30730step1 raw30730step1Labels permutation25 permutation7
    mixedMoment B raw30730step2 raw30730step2Labels = mixedMoment B raw30730step3 raw30730step3Labels := by
      have ha : raw30730step3 = raw30730step2 := by apply Matrix.ext; unfold raw30730step3 raw30730step2; decide +kernel
      have hl : raw30730step2Labels = labelEmbedding1 ∘ raw30730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30730step2 raw30730step2Labels raw30730step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3775 node3775Labels := by rfl

theorem canonical30731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30731 raw30731Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw30731 raw30731Labels = mixedMoment B raw30731step0 raw30731step0Labels := by
      have hz : ∀ j, raw30731 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30731step0 = (fun i j => raw30731 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30731step0 raw30731; decide +kernel
      have hl : raw30731step0Labels = raw30731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30731 raw30731Labels permutation434 hz
    mixedMoment B raw30731step0 raw30731step0Labels = mixedMoment B raw30731step1 raw30731step1Labels := by
      have ha : raw30731step1 = (fun i j => raw30731step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30731step1 raw30731step0; decide +kernel
      have hl : raw30731step1Labels = raw30731step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30731step0 raw30731step0Labels permutation127 permutation7
    mixedMoment B raw30731step1 raw30731step1Labels = mixedMoment B raw30731step2 raw30731step2Labels := by
      have ha : raw30731step2 = raw30731step1 := by apply Matrix.ext; unfold raw30731step2 raw30731step1; decide +kernel
      have hl : raw30731step1Labels = labelEmbedding1 ∘ raw30731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30731step1 raw30731step1Labels raw30731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical30732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30732 raw30732Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw30732 raw30732Labels = mixedMoment B raw30732step0 raw30732step0Labels := by
      have hz : ∀ j, raw30732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30732step0 = (fun i j => raw30732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30732step0 raw30732; decide +kernel
      have hl : raw30732step0Labels = raw30732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30732 raw30732Labels permutation346 hz
    mixedMoment B raw30732step0 raw30732step0Labels = mixedMoment B raw30732step1 raw30732step1Labels := by
      have ha : raw30732step1 = (fun i j => raw30732step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30732step1 raw30732step0; decide +kernel
      have hl : raw30732step1Labels = raw30732step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30732step0 raw30732step0Labels permutation127 permutation7
    mixedMoment B raw30732step1 raw30732step1Labels = mixedMoment B raw30732step2 raw30732step2Labels := by
      have ha : raw30732step2 = raw30732step1 := by apply Matrix.ext; unfold raw30732step2 raw30732step1; decide +kernel
      have hl : raw30732step1Labels = labelEmbedding1 ∘ raw30732step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30732step1 raw30732step1Labels raw30732step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical30733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30733 raw30733Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw30733 raw30733Labels = mixedMoment B raw30733step0 raw30733step0Labels := by
      have hz : ∀ j, raw30733 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30733step0 = (fun i j => raw30733 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30733step0 raw30733; decide +kernel
      have hl : raw30733step0Labels = raw30733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30733 raw30733Labels permutation434 hz
    mixedMoment B raw30733step0 raw30733step0Labels = mixedMoment B raw30733step1 raw30733step1Labels := by
      have hz : ∀ j, raw30733step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30733step1 = (fun i j => raw30733step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30733step1 raw30733step0; decide +kernel
      have hl : raw30733step1Labels = raw30733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30733step0 raw30733step0Labels permutation80 hz
    mixedMoment B raw30733step1 raw30733step1Labels = mixedMoment B raw30733step2 raw30733step2Labels := by
      have ha : raw30733step2 = (fun i j => raw30733step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30733step2 raw30733step1; decide +kernel
      have hl : raw30733step2Labels = raw30733step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30733step1 raw30733step1Labels permutation9 permutation7
    mixedMoment B raw30733step2 raw30733step2Labels = mixedMoment B raw30733step3 raw30733step3Labels := by
      have ha : raw30733step3 = -raw30733step2 := by apply Matrix.ext; change ∀ i j, raw30733step3 i j = -(raw30733step2 i j); unfold raw30733step3 raw30733step2; decide +kernel
      have hl : raw30733step3Labels = raw30733step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30733step3 raw30733step3Labels = mixedMoment B raw30733step4 raw30733step4Labels := by
      have ha : raw30733step4 = raw30733step3 := by apply Matrix.ext; unfold raw30733step4 raw30733step3; decide +kernel
      have hl : raw30733step3Labels = labelEmbedding1 ∘ raw30733step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30733step3 raw30733step3Labels raw30733step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

theorem canonical30734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30734 raw30734Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw30734 raw30734Labels = mixedMoment B raw30734step0 raw30734step0Labels := by
      have hz : ∀ j, raw30734 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30734step0 = (fun i j => raw30734 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30734step0 raw30734; decide +kernel
      have hl : raw30734step0Labels = raw30734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30734 raw30734Labels permutation434 hz
    mixedMoment B raw30734step0 raw30734step0Labels = mixedMoment B raw30734step1 raw30734step1Labels := by
      have hz : ∀ j, raw30734step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30734step1 = (fun i j => raw30734step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30734step1 raw30734step0; decide +kernel
      have hl : raw30734step1Labels = raw30734step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30734step0 raw30734step0Labels permutation80 hz
    mixedMoment B raw30734step1 raw30734step1Labels = mixedMoment B raw30734step2 raw30734step2Labels := by
      have hz : ∀ i, raw30734step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw30734step2 = (fun i j => raw30734step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw30734step2 raw30734step1; decide +kernel
      have hl : raw30734step2Labels = (fun j => raw30734step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw30734step1 raw30734step1Labels permutation4 hz
    mixedMoment B raw30734step2 raw30734step2Labels = mixedMoment B raw30734step3 raw30734step3Labels := by
      have ha : raw30734step3 = (fun i j => raw30734step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30734step3 raw30734step2; decide +kernel
      have hl : raw30734step3Labels = raw30734step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30734step2 raw30734step2Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical30735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30735 raw30735Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw30735 raw30735Labels = mixedMoment B raw30735step0 raw30735step0Labels := by
      have hz : ∀ j, raw30735 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30735step0 = (fun i j => raw30735 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30735step0 raw30735; decide +kernel
      have hl : raw30735step0Labels = raw30735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30735 raw30735Labels permutation434 hz
    mixedMoment B raw30735step0 raw30735step0Labels = mixedMoment B raw30735step1 raw30735step1Labels := by
      have hz : ∀ j, raw30735step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30735step1 = (fun i j => raw30735step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30735step1 raw30735step0; decide +kernel
      have hl : raw30735step1Labels = raw30735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30735step0 raw30735step0Labels permutation80 hz
    mixedMoment B raw30735step1 raw30735step1Labels = mixedMoment B raw30735step2 raw30735step2Labels := by
      have ha : raw30735step2 = (fun i j => raw30735step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30735step2 raw30735step1; decide +kernel
      have hl : raw30735step2Labels = raw30735step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30735step1 raw30735step1Labels permutation9 permutation7
    mixedMoment B raw30735step2 raw30735step2Labels = mixedMoment B raw30735step3 raw30735step3Labels := by
      have ha : raw30735step3 = -raw30735step2 := by apply Matrix.ext; change ∀ i j, raw30735step3 i j = -(raw30735step2 i j); unfold raw30735step3 raw30735step2; decide +kernel
      have hl : raw30735step3Labels = raw30735step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30735step3 raw30735step3Labels = mixedMoment B raw30735step4 raw30735step4Labels := by
      have ha : raw30735step4 = raw30735step3 := by apply Matrix.ext; unfold raw30735step4 raw30735step3; decide +kernel
      have hl : raw30735step3Labels = labelEmbedding1 ∘ raw30735step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30735step3 raw30735step3Labels raw30735step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical30736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30736 raw30736Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw30736 raw30736Labels = mixedMoment B raw30736step0 raw30736step0Labels := by
      have hz : ∀ j, raw30736 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30736step0 = (fun i j => raw30736 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30736step0 raw30736; decide +kernel
      have hl : raw30736step0Labels = raw30736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30736 raw30736Labels permutation434 hz
    mixedMoment B raw30736step0 raw30736step0Labels = mixedMoment B raw30736step1 raw30736step1Labels := by
      have ha : raw30736step1 = (fun i j => raw30736step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30736step1 raw30736step0; decide +kernel
      have hl : raw30736step1Labels = raw30736step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30736step0 raw30736step0Labels permutation33 permutation7
    mixedMoment B raw30736step1 raw30736step1Labels = mixedMoment B raw30736step2 raw30736step2Labels := by
      have ha : raw30736step2 = -raw30736step1 := by apply Matrix.ext; change ∀ i j, raw30736step2 i j = -(raw30736step1 i j); unfold raw30736step2 raw30736step1; decide +kernel
      have hl : raw30736step2Labels = raw30736step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30736step2 raw30736step2Labels = mixedMoment B raw30736step3 raw30736step3Labels := by
      have ha : raw30736step3 = raw30736step2 := by apply Matrix.ext; unfold raw30736step3 raw30736step2; decide +kernel
      have hl : raw30736step2Labels = labelEmbedding1 ∘ raw30736step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30736step2 raw30736step2Labels raw30736step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical30737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30737 raw30737Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw30737 raw30737Labels = mixedMoment B raw30737step0 raw30737step0Labels := by
      have hz : ∀ j, raw30737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30737step0 = (fun i j => raw30737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30737step0 raw30737; decide +kernel
      have hl : raw30737step0Labels = raw30737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30737 raw30737Labels permutation346 hz
    mixedMoment B raw30737step0 raw30737step0Labels = mixedMoment B raw30737step1 raw30737step1Labels := by
      have ha : raw30737step1 = (fun i j => raw30737step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30737step1 raw30737step0; decide +kernel
      have hl : raw30737step1Labels = raw30737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30737step0 raw30737step0Labels permutation33 permutation7
    mixedMoment B raw30737step1 raw30737step1Labels = mixedMoment B raw30737step2 raw30737step2Labels := by
      have ha : raw30737step2 = -raw30737step1 := by apply Matrix.ext; change ∀ i j, raw30737step2 i j = -(raw30737step1 i j); unfold raw30737step2 raw30737step1; decide +kernel
      have hl : raw30737step2Labels = raw30737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30737step2 raw30737step2Labels = mixedMoment B raw30737step3 raw30737step3Labels := by
      have ha : raw30737step3 = raw30737step2 := by apply Matrix.ext; unfold raw30737step3 raw30737step2; decide +kernel
      have hl : raw30737step2Labels = labelEmbedding1 ∘ raw30737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30737step2 raw30737step2Labels raw30737step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical30738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30738 raw30738Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw30738 raw30738Labels = mixedMoment B raw30738step0 raw30738step0Labels := by
      have hz : ∀ j, raw30738 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30738step0 = (fun i j => raw30738 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30738step0 raw30738; decide +kernel
      have hl : raw30738step0Labels = raw30738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30738 raw30738Labels permutation434 hz
    mixedMoment B raw30738step0 raw30738step0Labels = mixedMoment B raw30738step1 raw30738step1Labels := by
      have hz : ∀ j, raw30738step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30738step1 = (fun i j => raw30738step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30738step1 raw30738step0; decide +kernel
      have hl : raw30738step1Labels = raw30738step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30738step0 raw30738step0Labels permutation80 hz
    mixedMoment B raw30738step1 raw30738step1Labels = mixedMoment B raw30738step2 raw30738step2Labels := by
      have ha : raw30738step2 = (fun i j => raw30738step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30738step2 raw30738step1; decide +kernel
      have hl : raw30738step2Labels = raw30738step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30738step1 raw30738step1Labels permutation9 permutation7
    mixedMoment B raw30738step2 raw30738step2Labels = mixedMoment B raw30738step3 raw30738step3Labels := by
      have ha : raw30738step3 = -raw30738step2 := by apply Matrix.ext; change ∀ i j, raw30738step3 i j = -(raw30738step2 i j); unfold raw30738step3 raw30738step2; decide +kernel
      have hl : raw30738step3Labels = raw30738step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30738step3 raw30738step3Labels = mixedMoment B raw30738step4 raw30738step4Labels := by
      have ha : raw30738step4 = raw30738step3 := by apply Matrix.ext; unfold raw30738step4 raw30738step3; decide +kernel
      have hl : raw30738step3Labels = labelEmbedding1 ∘ raw30738step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30738step3 raw30738step3Labels raw30738step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical30739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30739 raw30739Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw30739 raw30739Labels = mixedMoment B raw30739step0 raw30739step0Labels := by
      have hz : ∀ j, raw30739 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30739step0 = (fun i j => raw30739 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30739step0 raw30739; decide +kernel
      have hl : raw30739step0Labels = raw30739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30739 raw30739Labels permutation434 hz
    mixedMoment B raw30739step0 raw30739step0Labels = mixedMoment B raw30739step1 raw30739step1Labels := by
      have ha : raw30739step1 = (fun i j => raw30739step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30739step1 raw30739step0; decide +kernel
      have hl : raw30739step1Labels = raw30739step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30739step0 raw30739step0Labels permutation33 permutation7
    mixedMoment B raw30739step1 raw30739step1Labels = mixedMoment B raw30739step2 raw30739step2Labels := by
      have ha : raw30739step2 = -raw30739step1 := by apply Matrix.ext; change ∀ i j, raw30739step2 i j = -(raw30739step1 i j); unfold raw30739step2 raw30739step1; decide +kernel
      have hl : raw30739step2Labels = raw30739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30739step2 raw30739step2Labels = mixedMoment B raw30739step3 raw30739step3Labels := by
      have ha : raw30739step3 = raw30739step2 := by apply Matrix.ext; unfold raw30739step3 raw30739step2; decide +kernel
      have hl : raw30739step2Labels = labelEmbedding1 ∘ raw30739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30739step2 raw30739step2Labels raw30739step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

theorem canonical30740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30740 raw30740Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw30740 raw30740Labels = mixedMoment B raw30740step0 raw30740step0Labels := by
      have hz : ∀ j, raw30740 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30740step0 = (fun i j => raw30740 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30740step0 raw30740; decide +kernel
      have hl : raw30740step0Labels = raw30740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30740 raw30740Labels permutation434 hz
    mixedMoment B raw30740step0 raw30740step0Labels = mixedMoment B raw30740step1 raw30740step1Labels := by
      have ha : raw30740step1 = (fun i j => raw30740step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30740step1 raw30740step0; decide +kernel
      have hl : raw30740step1Labels = raw30740step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30740step0 raw30740step0Labels permutation33 permutation7
    mixedMoment B raw30740step1 raw30740step1Labels = mixedMoment B raw30740step2 raw30740step2Labels := by
      have ha : raw30740step2 = -raw30740step1 := by apply Matrix.ext; change ∀ i j, raw30740step2 i j = -(raw30740step1 i j); unfold raw30740step2 raw30740step1; decide +kernel
      have hl : raw30740step2Labels = raw30740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30740step2 raw30740step2Labels = mixedMoment B raw30740step3 raw30740step3Labels := by
      have ha : raw30740step3 = raw30740step2 := by apply Matrix.ext; unfold raw30740step3 raw30740step2; decide +kernel
      have hl : raw30740step2Labels = labelEmbedding1 ∘ raw30740step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30740step2 raw30740step2Labels raw30740step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

theorem canonical30741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30741 raw30741Labels = mixedMoment B node3450 node3450Labels := by
  calc
    mixedMoment B raw30741 raw30741Labels = mixedMoment B raw30741step0 raw30741step0Labels := by
      have ha : raw30741step0 = (fun i j => raw30741 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30741step0 raw30741; decide +kernel
      have hl : raw30741step0Labels = raw30741Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30741 raw30741Labels permutation159 permutation7
    mixedMoment B raw30741step0 raw30741step0Labels = mixedMoment B raw30741step1 raw30741step1Labels := by
      have ha : raw30741step1 = -raw30741step0 := by apply Matrix.ext; change ∀ i j, raw30741step1 i j = -(raw30741step0 i j); unfold raw30741step1 raw30741step0; decide +kernel
      have hl : raw30741step1Labels = raw30741step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30741step1 raw30741step1Labels = mixedMoment B raw30741step2 raw30741step2Labels := by
      have ha : raw30741step2 = raw30741step1 := by apply Matrix.ext; unfold raw30741step2 raw30741step1; decide +kernel
      have hl : raw30741step1Labels = labelEmbedding1 ∘ raw30741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30741step1 raw30741step1Labels raw30741step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3450 node3450Labels := by rfl

theorem canonical30742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30742 raw30742Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw30742 raw30742Labels = mixedMoment B raw30742step0 raw30742step0Labels := by
      have hz : ∀ j, raw30742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30742step0 = (fun i j => raw30742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30742step0 raw30742; decide +kernel
      have hl : raw30742step0Labels = raw30742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30742 raw30742Labels permutation434 hz
    mixedMoment B raw30742step0 raw30742step0Labels = mixedMoment B raw30742step1 raw30742step1Labels := by
      have ha : raw30742step1 = (fun i j => raw30742step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30742step1 raw30742step0; decide +kernel
      have hl : raw30742step1Labels = raw30742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30742step0 raw30742step0Labels permutation33 permutation7
    mixedMoment B raw30742step1 raw30742step1Labels = mixedMoment B raw30742step2 raw30742step2Labels := by
      have ha : raw30742step2 = -raw30742step1 := by apply Matrix.ext; change ∀ i j, raw30742step2 i j = -(raw30742step1 i j); unfold raw30742step2 raw30742step1; decide +kernel
      have hl : raw30742step2Labels = raw30742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30742step2 raw30742step2Labels = mixedMoment B raw30742step3 raw30742step3Labels := by
      have ha : raw30742step3 = raw30742step2 := by apply Matrix.ext; unfold raw30742step3 raw30742step2; decide +kernel
      have hl : raw30742step2Labels = labelEmbedding1 ∘ raw30742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30742step2 raw30742step2Labels raw30742step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

theorem canonical30743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30743 raw30743Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw30743 raw30743Labels = mixedMoment B raw30743step0 raw30743step0Labels := by
      have hz : ∀ j, raw30743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30743step0 = (fun i j => raw30743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30743step0 raw30743; decide +kernel
      have hl : raw30743step0Labels = raw30743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30743 raw30743Labels permutation434 hz
    mixedMoment B raw30743step0 raw30743step0Labels = mixedMoment B raw30743step1 raw30743step1Labels := by
      have ha : raw30743step1 = (fun i j => raw30743step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30743step1 raw30743step0; decide +kernel
      have hl : raw30743step1Labels = raw30743step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30743step0 raw30743step0Labels permutation33 permutation7
    mixedMoment B raw30743step1 raw30743step1Labels = mixedMoment B raw30743step2 raw30743step2Labels := by
      have ha : raw30743step2 = -raw30743step1 := by apply Matrix.ext; change ∀ i j, raw30743step2 i j = -(raw30743step1 i j); unfold raw30743step2 raw30743step1; decide +kernel
      have hl : raw30743step2Labels = raw30743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30743step2 raw30743step2Labels = mixedMoment B raw30743step3 raw30743step3Labels := by
      have ha : raw30743step3 = raw30743step2 := by apply Matrix.ext; unfold raw30743step3 raw30743step2; decide +kernel
      have hl : raw30743step2Labels = labelEmbedding1 ∘ raw30743step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30743step2 raw30743step2Labels raw30743step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

theorem canonical30744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30744 raw30744Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw30744 raw30744Labels = mixedMoment B raw30744step0 raw30744step0Labels := by
      have hz : ∀ j, raw30744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30744step0 = (fun i j => raw30744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30744step0 raw30744; decide +kernel
      have hl : raw30744step0Labels = raw30744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30744 raw30744Labels permutation346 hz
    mixedMoment B raw30744step0 raw30744step0Labels = mixedMoment B raw30744step1 raw30744step1Labels := by
      have ha : raw30744step1 = (fun i j => raw30744step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30744step1 raw30744step0; decide +kernel
      have hl : raw30744step1Labels = raw30744step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30744step0 raw30744step0Labels permutation33 permutation7
    mixedMoment B raw30744step1 raw30744step1Labels = mixedMoment B raw30744step2 raw30744step2Labels := by
      have ha : raw30744step2 = -raw30744step1 := by apply Matrix.ext; change ∀ i j, raw30744step2 i j = -(raw30744step1 i j); unfold raw30744step2 raw30744step1; decide +kernel
      have hl : raw30744step2Labels = raw30744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30744step2 raw30744step2Labels = mixedMoment B raw30744step3 raw30744step3Labels := by
      have ha : raw30744step3 = raw30744step2 := by apply Matrix.ext; unfold raw30744step3 raw30744step2; decide +kernel
      have hl : raw30744step2Labels = labelEmbedding1 ∘ raw30744step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30744step2 raw30744step2Labels raw30744step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

theorem canonical30745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30745 raw30745Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw30745 raw30745Labels = mixedMoment B raw30745step0 raw30745step0Labels := by
      have hz : ∀ j, raw30745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30745step0 = (fun i j => raw30745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30745step0 raw30745; decide +kernel
      have hl : raw30745step0Labels = raw30745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30745 raw30745Labels permutation346 hz
    mixedMoment B raw30745step0 raw30745step0Labels = mixedMoment B raw30745step1 raw30745step1Labels := by
      have ha : raw30745step1 = (fun i j => raw30745step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30745step1 raw30745step0; decide +kernel
      have hl : raw30745step1Labels = raw30745step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30745step0 raw30745step0Labels permutation33 permutation7
    mixedMoment B raw30745step1 raw30745step1Labels = mixedMoment B raw30745step2 raw30745step2Labels := by
      have ha : raw30745step2 = -raw30745step1 := by apply Matrix.ext; change ∀ i j, raw30745step2 i j = -(raw30745step1 i j); unfold raw30745step2 raw30745step1; decide +kernel
      have hl : raw30745step2Labels = raw30745step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30745step2 raw30745step2Labels = mixedMoment B raw30745step3 raw30745step3Labels := by
      have ha : raw30745step3 = raw30745step2 := by apply Matrix.ext; unfold raw30745step3 raw30745step2; decide +kernel
      have hl : raw30745step2Labels = labelEmbedding1 ∘ raw30745step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30745step2 raw30745step2Labels raw30745step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

theorem canonical30746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30746 raw30746Labels = mixedMoment B node3450 node3450Labels := by
  calc
    mixedMoment B raw30746 raw30746Labels = mixedMoment B raw30746step0 raw30746step0Labels := by
      have ha : raw30746step0 = (fun i j => raw30746 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30746step0 raw30746; decide +kernel
      have hl : raw30746step0Labels = raw30746Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30746 raw30746Labels permutation153 permutation7
    mixedMoment B raw30746step0 raw30746step0Labels = mixedMoment B raw30746step1 raw30746step1Labels := by
      have ha : raw30746step1 = -raw30746step0 := by apply Matrix.ext; change ∀ i j, raw30746step1 i j = -(raw30746step0 i j); unfold raw30746step1 raw30746step0; decide +kernel
      have hl : raw30746step1Labels = raw30746step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30746step1 raw30746step1Labels = mixedMoment B raw30746step2 raw30746step2Labels := by
      have ha : raw30746step2 = raw30746step1 := by apply Matrix.ext; unfold raw30746step2 raw30746step1; decide +kernel
      have hl : raw30746step1Labels = labelEmbedding1 ∘ raw30746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30746step1 raw30746step1Labels raw30746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3450 node3450Labels := by rfl

theorem canonical30747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30747 raw30747Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw30747 raw30747Labels = mixedMoment B raw30747step0 raw30747step0Labels := by
      have hz : ∀ j, raw30747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30747step0 = (fun i j => raw30747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30747step0 raw30747; decide +kernel
      have hl : raw30747step0Labels = raw30747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30747 raw30747Labels permutation346 hz
    mixedMoment B raw30747step0 raw30747step0Labels = mixedMoment B raw30747step1 raw30747step1Labels := by
      have ha : raw30747step1 = (fun i j => raw30747step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30747step1 raw30747step0; decide +kernel
      have hl : raw30747step1Labels = raw30747step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30747step0 raw30747step0Labels permutation33 permutation7
    mixedMoment B raw30747step1 raw30747step1Labels = mixedMoment B raw30747step2 raw30747step2Labels := by
      have ha : raw30747step2 = -raw30747step1 := by apply Matrix.ext; change ∀ i j, raw30747step2 i j = -(raw30747step1 i j); unfold raw30747step2 raw30747step1; decide +kernel
      have hl : raw30747step2Labels = raw30747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30747step2 raw30747step2Labels = mixedMoment B raw30747step3 raw30747step3Labels := by
      have ha : raw30747step3 = raw30747step2 := by apply Matrix.ext; unfold raw30747step3 raw30747step2; decide +kernel
      have hl : raw30747step2Labels = labelEmbedding1 ∘ raw30747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30747step2 raw30747step2Labels raw30747step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

theorem canonical30748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30748 raw30748Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw30748 raw30748Labels = mixedMoment B raw30748step0 raw30748step0Labels := by
      have hz : ∀ j, raw30748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30748step0 = (fun i j => raw30748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30748step0 raw30748; decide +kernel
      have hl : raw30748step0Labels = raw30748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30748 raw30748Labels permutation346 hz
    mixedMoment B raw30748step0 raw30748step0Labels = mixedMoment B raw30748step1 raw30748step1Labels := by
      have ha : raw30748step1 = (fun i j => raw30748step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30748step1 raw30748step0; decide +kernel
      have hl : raw30748step1Labels = raw30748step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30748step0 raw30748step0Labels permutation33 permutation7
    mixedMoment B raw30748step1 raw30748step1Labels = mixedMoment B raw30748step2 raw30748step2Labels := by
      have ha : raw30748step2 = -raw30748step1 := by apply Matrix.ext; change ∀ i j, raw30748step2 i j = -(raw30748step1 i j); unfold raw30748step2 raw30748step1; decide +kernel
      have hl : raw30748step2Labels = raw30748step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30748step2 raw30748step2Labels = mixedMoment B raw30748step3 raw30748step3Labels := by
      have ha : raw30748step3 = raw30748step2 := by apply Matrix.ext; unfold raw30748step3 raw30748step2; decide +kernel
      have hl : raw30748step2Labels = labelEmbedding1 ∘ raw30748step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30748step2 raw30748step2Labels raw30748step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

theorem canonical30749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30749 raw30749Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw30749 raw30749Labels = mixedMoment B raw30749step0 raw30749step0Labels := by
      have hz : ∀ j, raw30749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30749step0 = (fun i j => raw30749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30749step0 raw30749; decide +kernel
      have hl : raw30749step0Labels = raw30749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30749 raw30749Labels permutation434 hz
    mixedMoment B raw30749step0 raw30749step0Labels = mixedMoment B raw30749step1 raw30749step1Labels := by
      have hz : ∀ j, raw30749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30749step1 = (fun i j => raw30749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30749step1 raw30749step0; decide +kernel
      have hl : raw30749step1Labels = raw30749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30749step0 raw30749step0Labels permutation80 hz
    mixedMoment B raw30749step1 raw30749step1Labels = mixedMoment B raw30749step2 raw30749step2Labels := by
      have ha : raw30749step2 = (fun i j => raw30749step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30749step2 raw30749step1; decide +kernel
      have hl : raw30749step2Labels = raw30749step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30749step1 raw30749step1Labels permutation9 permutation7
    mixedMoment B raw30749step2 raw30749step2Labels = mixedMoment B raw30749step3 raw30749step3Labels := by
      have ha : raw30749step3 = -raw30749step2 := by apply Matrix.ext; change ∀ i j, raw30749step3 i j = -(raw30749step2 i j); unfold raw30749step3 raw30749step2; decide +kernel
      have hl : raw30749step3Labels = raw30749step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30749step3 raw30749step3Labels = mixedMoment B raw30749step4 raw30749step4Labels := by
      have ha : raw30749step4 = raw30749step3 := by apply Matrix.ext; unfold raw30749step4 raw30749step3; decide +kernel
      have hl : raw30749step3Labels = labelEmbedding1 ∘ raw30749step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30749step3 raw30749step3Labels raw30749step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3276 node3276Labels := by rfl

theorem canonical30750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30750 raw30750Labels = mixedMoment B node3422 node3422Labels := by
  calc
    mixedMoment B raw30750 raw30750Labels = mixedMoment B raw30750step0 raw30750step0Labels := by
      have hz : ∀ j, raw30750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30750step0 = (fun i j => raw30750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30750step0 raw30750; decide +kernel
      have hl : raw30750step0Labels = raw30750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30750 raw30750Labels permutation434 hz
    mixedMoment B raw30750step0 raw30750step0Labels = mixedMoment B raw30750step1 raw30750step1Labels := by
      have hz : ∀ j, raw30750step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30750step1 = (fun i j => raw30750step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30750step1 raw30750step0; decide +kernel
      have hl : raw30750step1Labels = raw30750step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30750step0 raw30750step0Labels permutation80 hz
    mixedMoment B raw30750step1 raw30750step1Labels = mixedMoment B raw30750step2 raw30750step2Labels := by
      have ha : raw30750step2 = (fun i j => raw30750step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30750step2 raw30750step1; decide +kernel
      have hl : raw30750step2Labels = raw30750step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30750step1 raw30750step1Labels permutation25 permutation7
    mixedMoment B raw30750step2 raw30750step2Labels = mixedMoment B raw30750step3 raw30750step3Labels := by
      have ha : raw30750step3 = raw30750step2 := by apply Matrix.ext; unfold raw30750step3 raw30750step2; decide +kernel
      have hl : raw30750step2Labels = labelEmbedding1 ∘ raw30750step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30750step2 raw30750step2Labels raw30750step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3422 node3422Labels := by rfl

theorem canonical30751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30751 raw30751Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw30751 raw30751Labels = mixedMoment B raw30751step0 raw30751step0Labels := by
      have hz : ∀ j, raw30751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30751step0 = (fun i j => raw30751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30751step0 raw30751; decide +kernel
      have hl : raw30751step0Labels = raw30751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30751 raw30751Labels permutation434 hz
    mixedMoment B raw30751step0 raw30751step0Labels = mixedMoment B raw30751step1 raw30751step1Labels := by
      have ha : raw30751step1 = (fun i j => raw30751step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30751step1 raw30751step0; decide +kernel
      have hl : raw30751step1Labels = raw30751step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30751step0 raw30751step0Labels permutation127 permutation7
    mixedMoment B raw30751step1 raw30751step1Labels = mixedMoment B raw30751step2 raw30751step2Labels := by
      have ha : raw30751step2 = raw30751step1 := by apply Matrix.ext; unfold raw30751step2 raw30751step1; decide +kernel
      have hl : raw30751step1Labels = labelEmbedding1 ∘ raw30751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30751step1 raw30751step1Labels raw30751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

theorem canonical30752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30752 raw30752Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw30752 raw30752Labels = mixedMoment B raw30752step0 raw30752step0Labels := by
      have hz : ∀ j, raw30752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30752step0 = (fun i j => raw30752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30752step0 raw30752; decide +kernel
      have hl : raw30752step0Labels = raw30752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30752 raw30752Labels permutation346 hz
    mixedMoment B raw30752step0 raw30752step0Labels = mixedMoment B raw30752step1 raw30752step1Labels := by
      have ha : raw30752step1 = (fun i j => raw30752step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30752step1 raw30752step0; decide +kernel
      have hl : raw30752step1Labels = raw30752step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30752step0 raw30752step0Labels permutation127 permutation7
    mixedMoment B raw30752step1 raw30752step1Labels = mixedMoment B raw30752step2 raw30752step2Labels := by
      have ha : raw30752step2 = raw30752step1 := by apply Matrix.ext; unfold raw30752step2 raw30752step1; decide +kernel
      have hl : raw30752step1Labels = labelEmbedding1 ∘ raw30752step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30752step1 raw30752step1Labels raw30752step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

theorem canonical30753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30753 raw30753Labels = mixedMoment B node3484 node3484Labels := by
  calc
    mixedMoment B raw30753 raw30753Labels = mixedMoment B raw30753step0 raw30753step0Labels := by
      have hz : ∀ j, raw30753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30753step0 = (fun i j => raw30753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30753step0 raw30753; decide +kernel
      have hl : raw30753step0Labels = raw30753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30753 raw30753Labels permutation434 hz
    mixedMoment B raw30753step0 raw30753step0Labels = mixedMoment B raw30753step1 raw30753step1Labels := by
      have hz : ∀ j, raw30753step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30753step1 = (fun i j => raw30753step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30753step1 raw30753step0; decide +kernel
      have hl : raw30753step1Labels = raw30753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30753step0 raw30753step0Labels permutation80 hz
    mixedMoment B raw30753step1 raw30753step1Labels = mixedMoment B raw30753step2 raw30753step2Labels := by
      have ha : raw30753step2 = (fun i j => raw30753step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30753step2 raw30753step1; decide +kernel
      have hl : raw30753step2Labels = raw30753step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30753step1 raw30753step1Labels permutation25 permutation7
    mixedMoment B raw30753step2 raw30753step2Labels = mixedMoment B raw30753step3 raw30753step3Labels := by
      have ha : raw30753step3 = raw30753step2 := by apply Matrix.ext; unfold raw30753step3 raw30753step2; decide +kernel
      have hl : raw30753step2Labels = labelEmbedding1 ∘ raw30753step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30753step2 raw30753step2Labels raw30753step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3484 node3484Labels := by rfl

theorem canonical30754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30754 raw30754Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw30754 raw30754Labels = mixedMoment B raw30754step0 raw30754step0Labels := by
      have hz : ∀ j, raw30754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30754step0 = (fun i j => raw30754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30754step0 raw30754; decide +kernel
      have hl : raw30754step0Labels = raw30754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30754 raw30754Labels permutation434 hz
    mixedMoment B raw30754step0 raw30754step0Labels = mixedMoment B raw30754step1 raw30754step1Labels := by
      have hz : ∀ j, raw30754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30754step1 = (fun i j => raw30754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30754step1 raw30754step0; decide +kernel
      have hl : raw30754step1Labels = raw30754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30754step0 raw30754step0Labels permutation80 hz
    mixedMoment B raw30754step1 raw30754step1Labels = mixedMoment B raw30754step2 raw30754step2Labels := by
      have ha : raw30754step2 = (fun i j => raw30754step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30754step2 raw30754step1; decide +kernel
      have hl : raw30754step2Labels = raw30754step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30754step1 raw30754step1Labels permutation9 permutation7
    mixedMoment B raw30754step2 raw30754step2Labels = mixedMoment B raw30754step3 raw30754step3Labels := by
      have ha : raw30754step3 = -raw30754step2 := by apply Matrix.ext; change ∀ i j, raw30754step3 i j = -(raw30754step2 i j); unfold raw30754step3 raw30754step2; decide +kernel
      have hl : raw30754step3Labels = raw30754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30754step3 raw30754step3Labels = mixedMoment B raw30754step4 raw30754step4Labels := by
      have ha : raw30754step4 = raw30754step3 := by apply Matrix.ext; unfold raw30754step4 raw30754step3; decide +kernel
      have hl : raw30754step3Labels = labelEmbedding1 ∘ raw30754step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30754step3 raw30754step3Labels raw30754step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3277 node3277Labels := by rfl

theorem canonical30755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30755 raw30755Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw30755 raw30755Labels = mixedMoment B raw30755step0 raw30755step0Labels := by
      have hz : ∀ j, raw30755 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30755step0 = (fun i j => raw30755 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30755step0 raw30755; decide +kernel
      have hl : raw30755step0Labels = raw30755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30755 raw30755Labels permutation434 hz
    mixedMoment B raw30755step0 raw30755step0Labels = mixedMoment B raw30755step1 raw30755step1Labels := by
      have hz : ∀ j, raw30755step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30755step1 = (fun i j => raw30755step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30755step1 raw30755step0; decide +kernel
      have hl : raw30755step1Labels = raw30755step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30755step0 raw30755step0Labels permutation80 hz
    mixedMoment B raw30755step1 raw30755step1Labels = mixedMoment B raw30755step2 raw30755step2Labels := by
      have ha : raw30755step2 = (fun i j => raw30755step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30755step2 raw30755step1; decide +kernel
      have hl : raw30755step2Labels = raw30755step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30755step1 raw30755step1Labels permutation9 permutation7
    mixedMoment B raw30755step2 raw30755step2Labels = mixedMoment B raw30755step3 raw30755step3Labels := by
      have ha : raw30755step3 = -raw30755step2 := by apply Matrix.ext; change ∀ i j, raw30755step3 i j = -(raw30755step2 i j); unfold raw30755step3 raw30755step2; decide +kernel
      have hl : raw30755step3Labels = raw30755step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30755step3 raw30755step3Labels = mixedMoment B raw30755step4 raw30755step4Labels := by
      have ha : raw30755step4 = raw30755step3 := by apply Matrix.ext; unfold raw30755step4 raw30755step3; decide +kernel
      have hl : raw30755step3Labels = labelEmbedding1 ∘ raw30755step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30755step3 raw30755step3Labels raw30755step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3423 node3423Labels := by rfl

theorem canonical30756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30756 raw30756Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw30756 raw30756Labels = mixedMoment B raw30756step0 raw30756step0Labels := by
      have hz : ∀ j, raw30756 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30756step0 = (fun i j => raw30756 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30756step0 raw30756; decide +kernel
      have hl : raw30756step0Labels = raw30756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30756 raw30756Labels permutation434 hz
    mixedMoment B raw30756step0 raw30756step0Labels = mixedMoment B raw30756step1 raw30756step1Labels := by
      have ha : raw30756step1 = (fun i j => raw30756step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30756step1 raw30756step0; decide +kernel
      have hl : raw30756step1Labels = raw30756step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30756step0 raw30756step0Labels permutation33 permutation7
    mixedMoment B raw30756step1 raw30756step1Labels = mixedMoment B raw30756step2 raw30756step2Labels := by
      have ha : raw30756step2 = -raw30756step1 := by apply Matrix.ext; change ∀ i j, raw30756step2 i j = -(raw30756step1 i j); unfold raw30756step2 raw30756step1; decide +kernel
      have hl : raw30756step2Labels = raw30756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30756step2 raw30756step2Labels = mixedMoment B raw30756step3 raw30756step3Labels := by
      have ha : raw30756step3 = raw30756step2 := by apply Matrix.ext; unfold raw30756step3 raw30756step2; decide +kernel
      have hl : raw30756step2Labels = labelEmbedding1 ∘ raw30756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30756step2 raw30756step2Labels raw30756step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

theorem canonical30757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30757 raw30757Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw30757 raw30757Labels = mixedMoment B raw30757step0 raw30757step0Labels := by
      have hz : ∀ j, raw30757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30757step0 = (fun i j => raw30757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30757step0 raw30757; decide +kernel
      have hl : raw30757step0Labels = raw30757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30757 raw30757Labels permutation346 hz
    mixedMoment B raw30757step0 raw30757step0Labels = mixedMoment B raw30757step1 raw30757step1Labels := by
      have ha : raw30757step1 = (fun i j => raw30757step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30757step1 raw30757step0; decide +kernel
      have hl : raw30757step1Labels = raw30757step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30757step0 raw30757step0Labels permutation33 permutation7
    mixedMoment B raw30757step1 raw30757step1Labels = mixedMoment B raw30757step2 raw30757step2Labels := by
      have ha : raw30757step2 = -raw30757step1 := by apply Matrix.ext; change ∀ i j, raw30757step2 i j = -(raw30757step1 i j); unfold raw30757step2 raw30757step1; decide +kernel
      have hl : raw30757step2Labels = raw30757step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30757step2 raw30757step2Labels = mixedMoment B raw30757step3 raw30757step3Labels := by
      have ha : raw30757step3 = raw30757step2 := by apply Matrix.ext; unfold raw30757step3 raw30757step2; decide +kernel
      have hl : raw30757step2Labels = labelEmbedding1 ∘ raw30757step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30757step2 raw30757step2Labels raw30757step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30862 raw30862Labels = mixedMoment B node2379 node2379Labels := by
  calc
    mixedMoment B raw30862 raw30862Labels = mixedMoment B raw30862step0 raw30862step0Labels := by
      have ha : raw30862step0 = (fun i j => raw30862 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30862step0 raw30862; decide +kernel
      have hl : raw30862step0Labels = raw30862Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30862 raw30862Labels permutation153 permutation2
    _ = mixedMoment B node2379 node2379Labels := by rfl

theorem canonical30863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30863 raw30863Labels = mixedMoment B node3646 node3646Labels := by
  calc
    mixedMoment B raw30863 raw30863Labels = mixedMoment B raw30863step0 raw30863step0Labels := by
      have ha : raw30863step0 = (fun i j => raw30863 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30863step0 raw30863; decide +kernel
      have hl : raw30863step0Labels = raw30863Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30863 raw30863Labels permutation153 permutation2
    _ = mixedMoment B node3646 node3646Labels := by rfl

theorem canonical30864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30864 raw30864Labels = mixedMoment B node3718 node3718Labels := by
  calc
    mixedMoment B raw30864 raw30864Labels = mixedMoment B raw30864step0 raw30864step0Labels := by
      have ha : raw30864step0 = (fun i j => raw30864 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30864step0 raw30864; decide +kernel
      have hl : raw30864step0Labels = raw30864Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30864 raw30864Labels permutation589 permutation2
    mixedMoment B raw30864step0 raw30864step0Labels = mixedMoment B raw30864step1 raw30864step1Labels := by
      have ha : raw30864step1 = -raw30864step0 := by apply Matrix.ext; change ∀ i j, raw30864step1 i j = -(raw30864step0 i j); unfold raw30864step1 raw30864step0; decide +kernel
      have hl : raw30864step1Labels = raw30864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3718 node3718Labels := by rfl

theorem canonical30865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30865 raw30865Labels = mixedMoment B node3718 node3718Labels := by
  calc
    mixedMoment B raw30865 raw30865Labels = mixedMoment B raw30865step0 raw30865step0Labels := by
      have ha : raw30865step0 = (fun i j => raw30865 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30865step0 raw30865; decide +kernel
      have hl : raw30865step0Labels = raw30865Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30865 raw30865Labels permutation584 permutation2
    mixedMoment B raw30865step0 raw30865step0Labels = mixedMoment B raw30865step1 raw30865step1Labels := by
      have ha : raw30865step1 = -raw30865step0 := by apply Matrix.ext; change ∀ i j, raw30865step1 i j = -(raw30865step0 i j); unfold raw30865step1 raw30865step0; decide +kernel
      have hl : raw30865step1Labels = raw30865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3718 node3718Labels := by rfl

theorem canonical30866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30866 raw30866Labels = mixedMoment B node3759 node3759Labels := by
  calc
    _ = mixedMoment B node3759 node3759Labels := by rfl

theorem canonical30867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30867 raw30867Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw30867 raw30867Labels = mixedMoment B raw30867step0 raw30867step0Labels := by
      have ha : raw30867step0 = (fun i j => raw30867 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30867step0 raw30867; decide +kernel
      have hl : raw30867step0Labels = raw30867Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30867 raw30867Labels permutation153 permutation2
    _ = mixedMoment B node3757 node3757Labels := by rfl

theorem canonical30868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30868 raw30868Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw30868 raw30868Labels = mixedMoment B raw30868step0 raw30868step0Labels := by
      have hz : ∀ j, raw30868 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw30868step0 = (fun i j => raw30868 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw30868step0 raw30868; decide +kernel
      have hl : raw30868step0Labels = raw30868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30868 raw30868Labels permutation590 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical30869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30869 raw30869Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw30869 raw30869Labels = mixedMoment B raw30869step0 raw30869step0Labels := by
      have hz : ∀ j, raw30869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30869step0 = (fun i j => raw30869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30869step0 raw30869; decide +kernel
      have hl : raw30869step0Labels = raw30869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30869 raw30869Labels permutation434 hz
    mixedMoment B raw30869step0 raw30869step0Labels = mixedMoment B raw30869step1 raw30869step1Labels := by
      have ha : raw30869step1 = (fun i j => raw30869step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30869step1 raw30869step0; decide +kernel
      have hl : raw30869step1Labels = raw30869step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30869step0 raw30869step0Labels permutation33 permutation2
    _ = mixedMoment B node2388 node2388Labels := by rfl

theorem canonical30870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30870 raw30870Labels = mixedMoment B node3654 node3654Labels := by
  calc
    mixedMoment B raw30870 raw30870Labels = mixedMoment B raw30870step0 raw30870step0Labels := by
      have hz : ∀ j, raw30870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30870step0 = (fun i j => raw30870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30870step0 raw30870; decide +kernel
      have hl : raw30870step0Labels = raw30870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30870 raw30870Labels permutation434 hz
    mixedMoment B raw30870step0 raw30870step0Labels = mixedMoment B raw30870step1 raw30870step1Labels := by
      have ha : raw30870step1 = (fun i j => raw30870step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30870step1 raw30870step0; decide +kernel
      have hl : raw30870step1Labels = raw30870step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30870step0 raw30870step0Labels permutation33 permutation2
    _ = mixedMoment B node3654 node3654Labels := by rfl

theorem canonical30871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30871 raw30871Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw30871 raw30871Labels = mixedMoment B raw30871step0 raw30871step0Labels := by
      have hz : ∀ j, raw30871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30871step0 = (fun i j => raw30871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30871step0 raw30871; decide +kernel
      have hl : raw30871step0Labels = raw30871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30871 raw30871Labels permutation434 hz
    mixedMoment B raw30871step0 raw30871step0Labels = mixedMoment B raw30871step1 raw30871step1Labels := by
      have ha : raw30871step1 = (fun i j => raw30871step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30871step1 raw30871step0; decide +kernel
      have hl : raw30871step1Labels = raw30871step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30871step0 raw30871step0Labels permutation127 permutation2
    mixedMoment B raw30871step1 raw30871step1Labels = mixedMoment B raw30871step2 raw30871step2Labels := by
      have ha : raw30871step2 = -raw30871step1 := by apply Matrix.ext; change ∀ i j, raw30871step2 i j = -(raw30871step1 i j); unfold raw30871step2 raw30871step1; decide +kernel
      have hl : raw30871step2Labels = raw30871step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3702 node3702Labels := by rfl

theorem canonical30872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30872 raw30872Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw30872 raw30872Labels = mixedMoment B raw30872step0 raw30872step0Labels := by
      have ha : raw30872step0 = (fun i j => raw30872 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30872step0 raw30872; decide +kernel
      have hl : raw30872step0Labels = raw30872Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30872 raw30872Labels permutation584 permutation2
    mixedMoment B raw30872step0 raw30872step0Labels = mixedMoment B raw30872step1 raw30872step1Labels := by
      have ha : raw30872step1 = -raw30872step0 := by apply Matrix.ext; change ∀ i j, raw30872step1 i j = -(raw30872step0 i j); unfold raw30872step1 raw30872step0; decide +kernel
      have hl : raw30872step1Labels = raw30872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3681 node3681Labels := by rfl

theorem canonical30873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30873 raw30873Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw30873 raw30873Labels = mixedMoment B raw30873step0 raw30873step0Labels := by
      have hz : ∀ j, raw30873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30873step0 = (fun i j => raw30873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30873step0 raw30873; decide +kernel
      have hl : raw30873step0Labels = raw30873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30873 raw30873Labels permutation434 hz
    _ = mixedMoment B node3767 node3767Labels := by rfl

theorem canonical30874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30874 raw30874Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw30874 raw30874Labels = mixedMoment B raw30874step0 raw30874step0Labels := by
      have hz : ∀ j, raw30874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30874step0 = (fun i j => raw30874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30874step0 raw30874; decide +kernel
      have hl : raw30874step0Labels = raw30874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30874 raw30874Labels permutation434 hz
    mixedMoment B raw30874step0 raw30874step0Labels = mixedMoment B raw30874step1 raw30874step1Labels := by
      have ha : raw30874step1 = (fun i j => raw30874step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30874step1 raw30874step0; decide +kernel
      have hl : raw30874step1Labels = raw30874step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30874step0 raw30874step0Labels permutation33 permutation2
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical30875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30875 raw30875Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw30875 raw30875Labels = mixedMoment B raw30875step0 raw30875step0Labels := by
      have hz : ∀ j, raw30875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30875step0 = (fun i j => raw30875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30875step0 raw30875; decide +kernel
      have hl : raw30875step0Labels = raw30875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30875 raw30875Labels permutation434 hz
    mixedMoment B raw30875step0 raw30875step0Labels = mixedMoment B raw30875step1 raw30875step1Labels := by
      have ha : raw30875step1 = (fun i j => raw30875step0 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30875step1 raw30875step0; decide +kernel
      have hl : raw30875step1Labels = raw30875step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30875step0 raw30875step0Labels permutation33 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3993 raw3993Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw3993 raw3993Labels = mixedMoment B raw3993step0 raw3993step0Labels := by
      have hz : ∀ j, raw3993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3993step0 = (fun i j => raw3993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3993step0 raw3993; decide +kernel
      have hl : raw3993step0Labels = raw3993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3993 raw3993Labels permutation434 hz
    mixedMoment B raw3993step0 raw3993step0Labels = mixedMoment B raw3993step1 raw3993step1Labels := by
      have hz : ∀ j, raw3993step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3993step1 = (fun i j => raw3993step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3993step1 raw3993step0; decide +kernel
      have hl : raw3993step1Labels = raw3993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3993step0 raw3993step0Labels permutation80 hz
    mixedMoment B raw3993step1 raw3993step1Labels = mixedMoment B raw3993step2 raw3993step2Labels := by
      have ha : raw3993step2 = (fun i j => raw3993step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3993step2 raw3993step1; decide +kernel
      have hl : raw3993step2Labels = raw3993step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3993step1 raw3993step1Labels permutation9 permutation7
    mixedMoment B raw3993step2 raw3993step2Labels = mixedMoment B raw3993step3 raw3993step3Labels := by
      have ha : raw3993step3 = -raw3993step2 := by apply Matrix.ext; change ∀ i j, raw3993step3 i j = -(raw3993step2 i j); unfold raw3993step3 raw3993step2; decide +kernel
      have hl : raw3993step3Labels = raw3993step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3993step3 raw3993step3Labels = mixedMoment B raw3993step4 raw3993step4Labels := by
      have ha : raw3993step4 = raw3993step3 := by apply Matrix.ext; unfold raw3993step4 raw3993step3; decide +kernel
      have hl : raw3993step3Labels = labelEmbedding1 ∘ raw3993step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3993step3 raw3993step3Labels raw3993step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

theorem canonical3996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3996 raw3996Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw3996 raw3996Labels = mixedMoment B raw3996step0 raw3996step0Labels := by
      have hz : ∀ j, raw3996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3996step0 = (fun i j => raw3996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3996step0 raw3996; decide +kernel
      have hl : raw3996step0Labels = raw3996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3996 raw3996Labels permutation434 hz
    mixedMoment B raw3996step0 raw3996step0Labels = mixedMoment B raw3996step1 raw3996step1Labels := by
      have hz : ∀ j, raw3996step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3996step1 = (fun i j => raw3996step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3996step1 raw3996step0; decide +kernel
      have hl : raw3996step1Labels = raw3996step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3996step0 raw3996step0Labels permutation80 hz
    mixedMoment B raw3996step1 raw3996step1Labels = mixedMoment B raw3996step2 raw3996step2Labels := by
      have ha : raw3996step2 = (fun i j => raw3996step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3996step2 raw3996step1; decide +kernel
      have hl : raw3996step2Labels = raw3996step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3996step1 raw3996step1Labels permutation9 permutation7
    mixedMoment B raw3996step2 raw3996step2Labels = mixedMoment B raw3996step3 raw3996step3Labels := by
      have ha : raw3996step3 = -raw3996step2 := by apply Matrix.ext; change ∀ i j, raw3996step3 i j = -(raw3996step2 i j); unfold raw3996step3 raw3996step2; decide +kernel
      have hl : raw3996step3Labels = raw3996step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3996step3 raw3996step3Labels = mixedMoment B raw3996step4 raw3996step4Labels := by
      have ha : raw3996step4 = raw3996step3 := by apply Matrix.ext; unfold raw3996step4 raw3996step3; decide +kernel
      have hl : raw3996step3Labels = labelEmbedding1 ∘ raw3996step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3996step3 raw3996step3Labels raw3996step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5831 raw5831Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw5831 raw5831Labels = mixedMoment B raw5831step0 raw5831step0Labels := by
      have hz : ∀ j, raw5831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5831step0 = (fun i j => raw5831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5831step0 raw5831; decide +kernel
      have hl : raw5831step0Labels = raw5831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5831 raw5831Labels permutation434 hz
    mixedMoment B raw5831step0 raw5831step0Labels = mixedMoment B raw5831step1 raw5831step1Labels := by
      have hz : ∀ j, raw5831step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5831step1 = (fun i j => raw5831step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5831step1 raw5831step0; decide +kernel
      have hl : raw5831step1Labels = raw5831step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5831step0 raw5831step0Labels permutation80 hz
    mixedMoment B raw5831step1 raw5831step1Labels = mixedMoment B raw5831step2 raw5831step2Labels := by
      have ha : raw5831step2 = (fun i j => raw5831step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5831step2 raw5831step1; decide +kernel
      have hl : raw5831step2Labels = raw5831step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5831step1 raw5831step1Labels permutation25 permutation7
    mixedMoment B raw5831step2 raw5831step2Labels = mixedMoment B raw5831step3 raw5831step3Labels := by
      have ha : raw5831step3 = raw5831step2 := by apply Matrix.ext; unfold raw5831step3 raw5831step2; decide +kernel
      have hl : raw5831step2Labels = labelEmbedding1 ∘ raw5831step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5831step2 raw5831step2Labels raw5831step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical5842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5842 raw5842Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw5842 raw5842Labels = mixedMoment B raw5842step0 raw5842step0Labels := by
      have hz : ∀ j, raw5842 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5842step0 = (fun i j => raw5842 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5842step0 raw5842; decide +kernel
      have hl : raw5842step0Labels = raw5842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5842 raw5842Labels permutation434 hz
    mixedMoment B raw5842step0 raw5842step0Labels = mixedMoment B raw5842step1 raw5842step1Labels := by
      have ha : raw5842step1 = (fun i j => raw5842step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5842step1 raw5842step0; decide +kernel
      have hl : raw5842step1Labels = raw5842step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5842step0 raw5842step0Labels permutation127 permutation7
    mixedMoment B raw5842step1 raw5842step1Labels = mixedMoment B raw5842step2 raw5842step2Labels := by
      have ha : raw5842step2 = raw5842step1 := by apply Matrix.ext; unfold raw5842step2 raw5842step1; decide +kernel
      have hl : raw5842step1Labels = labelEmbedding1 ∘ raw5842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5842step1 raw5842step1Labels raw5842step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

theorem canonical5847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5847 raw5847Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw5847 raw5847Labels = mixedMoment B raw5847step0 raw5847step0Labels := by
      have hz : ∀ j, raw5847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5847step0 = (fun i j => raw5847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5847step0 raw5847; decide +kernel
      have hl : raw5847step0Labels = raw5847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5847 raw5847Labels permutation346 hz
    mixedMoment B raw5847step0 raw5847step0Labels = mixedMoment B raw5847step1 raw5847step1Labels := by
      have ha : raw5847step1 = (fun i j => raw5847step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5847step1 raw5847step0; decide +kernel
      have hl : raw5847step1Labels = raw5847step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5847step0 raw5847step0Labels permutation127 permutation7
    mixedMoment B raw5847step1 raw5847step1Labels = mixedMoment B raw5847step2 raw5847step2Labels := by
      have ha : raw5847step2 = raw5847step1 := by apply Matrix.ext; unfold raw5847step2 raw5847step1; decide +kernel
      have hl : raw5847step1Labels = labelEmbedding1 ∘ raw5847step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5847step1 raw5847step1Labels raw5847step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

theorem canonical5851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5851 raw5851Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw5851 raw5851Labels = mixedMoment B raw5851step0 raw5851step0Labels := by
      have hz : ∀ j, raw5851 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5851step0 = (fun i j => raw5851 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5851step0 raw5851; decide +kernel
      have hl : raw5851step0Labels = raw5851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5851 raw5851Labels permutation434 hz
    mixedMoment B raw5851step0 raw5851step0Labels = mixedMoment B raw5851step1 raw5851step1Labels := by
      have hz : ∀ j, raw5851step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5851step1 = (fun i j => raw5851step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5851step1 raw5851step0; decide +kernel
      have hl : raw5851step1Labels = raw5851step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5851step0 raw5851step0Labels permutation80 hz
    mixedMoment B raw5851step1 raw5851step1Labels = mixedMoment B raw5851step2 raw5851step2Labels := by
      have ha : raw5851step2 = (fun i j => raw5851step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5851step2 raw5851step1; decide +kernel
      have hl : raw5851step2Labels = raw5851step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5851step1 raw5851step1Labels permutation25 permutation7
    mixedMoment B raw5851step2 raw5851step2Labels = mixedMoment B raw5851step3 raw5851step3Labels := by
      have ha : raw5851step3 = raw5851step2 := by apply Matrix.ext; unfold raw5851step3 raw5851step2; decide +kernel
      have hl : raw5851step2Labels = labelEmbedding1 ∘ raw5851step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5851step2 raw5851step2Labels raw5851step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical5853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5853 raw5853Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw5853 raw5853Labels = mixedMoment B raw5853step0 raw5853step0Labels := by
      have hz : ∀ j, raw5853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5853step0 = (fun i j => raw5853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5853step0 raw5853; decide +kernel
      have hl : raw5853step0Labels = raw5853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5853 raw5853Labels permutation434 hz
    mixedMoment B raw5853step0 raw5853step0Labels = mixedMoment B raw5853step1 raw5853step1Labels := by
      have ha : raw5853step1 = (fun i j => raw5853step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5853step1 raw5853step0; decide +kernel
      have hl : raw5853step1Labels = raw5853step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5853step0 raw5853step0Labels permutation127 permutation7
    mixedMoment B raw5853step1 raw5853step1Labels = mixedMoment B raw5853step2 raw5853step2Labels := by
      have ha : raw5853step2 = raw5853step1 := by apply Matrix.ext; unfold raw5853step2 raw5853step1; decide +kernel
      have hl : raw5853step1Labels = labelEmbedding1 ∘ raw5853step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5853step1 raw5853step1Labels raw5853step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical5854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5854 raw5854Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw5854 raw5854Labels = mixedMoment B raw5854step0 raw5854step0Labels := by
      have hz : ∀ j, raw5854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5854step0 = (fun i j => raw5854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5854step0 raw5854; decide +kernel
      have hl : raw5854step0Labels = raw5854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5854 raw5854Labels permutation346 hz
    mixedMoment B raw5854step0 raw5854step0Labels = mixedMoment B raw5854step1 raw5854step1Labels := by
      have ha : raw5854step1 = (fun i j => raw5854step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5854step1 raw5854step0; decide +kernel
      have hl : raw5854step1Labels = raw5854step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5854step0 raw5854step0Labels permutation127 permutation7
    mixedMoment B raw5854step1 raw5854step1Labels = mixedMoment B raw5854step2 raw5854step2Labels := by
      have ha : raw5854step2 = raw5854step1 := by apply Matrix.ext; unfold raw5854step2 raw5854step1; decide +kernel
      have hl : raw5854step1Labels = labelEmbedding1 ∘ raw5854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5854step1 raw5854step1Labels raw5854step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical5855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5855 raw5855Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5855 raw5855Labels = mixedMoment B raw5855step0 raw5855step0Labels := by
      have hz : ∀ j, raw5855 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5855step0 = (fun i j => raw5855 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5855step0 raw5855; decide +kernel
      have hl : raw5855step0Labels = raw5855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5855 raw5855Labels permutation434 hz
    mixedMoment B raw5855step0 raw5855step0Labels = mixedMoment B raw5855step1 raw5855step1Labels := by
      have hz : ∀ j, raw5855step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5855step1 = (fun i j => raw5855step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5855step1 raw5855step0; decide +kernel
      have hl : raw5855step1Labels = raw5855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5855step0 raw5855step0Labels permutation80 hz
    mixedMoment B raw5855step1 raw5855step1Labels = mixedMoment B raw5855step2 raw5855step2Labels := by
      have ha : raw5855step2 = (fun i j => raw5855step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5855step2 raw5855step1; decide +kernel
      have hl : raw5855step2Labels = raw5855step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5855step1 raw5855step1Labels permutation25 permutation7
    mixedMoment B raw5855step2 raw5855step2Labels = mixedMoment B raw5855step3 raw5855step3Labels := by
      have ha : raw5855step3 = raw5855step2 := by apply Matrix.ext; unfold raw5855step3 raw5855step2; decide +kernel
      have hl : raw5855step2Labels = labelEmbedding1 ∘ raw5855step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5855step2 raw5855step2Labels raw5855step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical5857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5857 raw5857Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw5857 raw5857Labels = mixedMoment B raw5857step0 raw5857step0Labels := by
      have hz : ∀ j, raw5857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5857step0 = (fun i j => raw5857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5857step0 raw5857; decide +kernel
      have hl : raw5857step0Labels = raw5857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5857 raw5857Labels permutation434 hz
    mixedMoment B raw5857step0 raw5857step0Labels = mixedMoment B raw5857step1 raw5857step1Labels := by
      have hz : ∀ j, raw5857step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5857step1 = (fun i j => raw5857step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5857step1 raw5857step0; decide +kernel
      have hl : raw5857step1Labels = raw5857step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5857step0 raw5857step0Labels permutation80 hz
    mixedMoment B raw5857step1 raw5857step1Labels = mixedMoment B raw5857step2 raw5857step2Labels := by
      have ha : raw5857step2 = (fun i j => raw5857step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5857step2 raw5857step1; decide +kernel
      have hl : raw5857step2Labels = raw5857step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5857step1 raw5857step1Labels permutation28 permutation5
    mixedMoment B raw5857step2 raw5857step2Labels = mixedMoment B raw5857step3 raw5857step3Labels := by
      have ha : raw5857step3 = raw5857step2 := by apply Matrix.ext; unfold raw5857step3 raw5857step2; decide +kernel
      have hl : raw5857step2Labels = labelEmbedding1 ∘ raw5857step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5857step2 raw5857step2Labels raw5857step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2267 node2267Labels := by rfl

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

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

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

theorem sound2151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2151 node2151Labels = Sparse.eval nodeValue2151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2151) = mixedMoment B node2151 node2151Labels := rfl
  simpa [nodeValue2151, Sparse.eval] using hc.symm

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

theorem zero2228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = 0 := by
  exact mixedMoment_order_one B hB node2228 node2228Labels 1
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

theorem sound2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = Sparse.eval nodeValue2228 (mixedVector B) := by
  simpa only [nodeValue2228, Sparse.eval_nil] using zero2228 B _hB _hF

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

theorem sound2256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2256 node2256Labels = Sparse.eval nodeValue2256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2256) = mixedMoment B node2256 node2256Labels := rfl
  simpa [nodeValue2256, Sparse.eval] using hc.symm

theorem sound2258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2258 node2258Labels = Sparse.eval nodeValue2258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2258) = mixedMoment B node2258 node2258Labels := rfl
  simpa [nodeValue2258, Sparse.eval] using hc.symm

theorem sound2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2267 node2267Labels = Sparse.eval nodeValue2267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2267) = mixedMoment B node2267 node2267Labels := rfl
  simpa [nodeValue2267, Sparse.eval] using hc.symm

theorem sound2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2286 node2286Labels = Sparse.eval nodeValue2286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2286) = mixedMoment B node2286 node2286Labels := rfl
  simpa [nodeValue2286, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

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

theorem sound2321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2321 node2321Labels = Sparse.eval nodeValue2321 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2321) = mixedMoment B node2321 node2321Labels := rfl
  simpa [nodeValue2321, Sparse.eval] using hc.symm

theorem sound2322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2322 node2322Labels = Sparse.eval nodeValue2322 (mixedVector B) := by
  simpa only [nodeValue2322, Sparse.eval_nil] using zero2322 B _hB _hF

theorem sound2325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2325 node2325Labels = Sparse.eval nodeValue2325 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2325) = mixedMoment B node2325 node2325Labels := rfl
  simpa [nodeValue2325, Sparse.eval] using hc.symm

theorem sound2326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2326 node2326Labels = Sparse.eval nodeValue2326 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2326) = mixedMoment B node2326 node2326Labels := rfl
  simpa [nodeValue2326, Sparse.eval] using hc.symm

theorem sound2327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2327 node2327Labels = Sparse.eval nodeValue2327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2327) = mixedMoment B node2327 node2327Labels := rfl
  simpa [nodeValue2327, Sparse.eval] using hc.symm

theorem sound2341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2341 node2341Labels = Sparse.eval nodeValue2341 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2341) = mixedMoment B node2341 node2341Labels := rfl
  simpa [nodeValue2341, Sparse.eval] using hc.symm

theorem sound2342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2342 node2342Labels = Sparse.eval nodeValue2342 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2342) = mixedMoment B node2342 node2342Labels := rfl
  simpa [nodeValue2342, Sparse.eval] using hc.symm

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

theorem sound2379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2379 node2379Labels = Sparse.eval nodeValue2379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2379) = mixedMoment B node2379 node2379Labels := rfl
  simpa [nodeValue2379, Sparse.eval] using hc.symm

theorem sound2388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2388 node2388Labels = Sparse.eval nodeValue2388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2388) = mixedMoment B node2388 node2388Labels := rfl
  simpa [nodeValue2388, Sparse.eval] using hc.symm

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

theorem sound2456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2456 node2456Labels = Sparse.eval nodeValue2456 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2456) = mixedMoment B node2456 node2456Labels := rfl
  simpa [nodeValue2456, Sparse.eval] using hc.symm

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

theorem sound2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2489 node2489Labels = Sparse.eval nodeValue2489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2489) = mixedMoment B node2489 node2489Labels := rfl
  simpa [nodeValue2489, Sparse.eval] using hc.symm

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

theorem sound2652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2652 node2652Labels = Sparse.eval nodeValue2652 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2652) = mixedMoment B node2652 node2652Labels := rfl
  simpa [nodeValue2652, Sparse.eval] using hc.symm

theorem sound2657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2657 node2657Labels = Sparse.eval nodeValue2657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2657) = mixedMoment B node2657 node2657Labels := rfl
  simpa [nodeValue2657, Sparse.eval] using hc.symm

theorem sound2658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2658 node2658Labels = Sparse.eval nodeValue2658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2658) = mixedMoment B node2658 node2658Labels := rfl
  simpa [nodeValue2658, Sparse.eval] using hc.symm

theorem sound2670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2670 node2670Labels = Sparse.eval nodeValue2670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2670) = mixedMoment B node2670 node2670Labels := rfl
  simpa [nodeValue2670, Sparse.eval] using hc.symm

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

theorem sound2683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2683 node2683Labels = Sparse.eval nodeValue2683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2683) = mixedMoment B node2683 node2683Labels := rfl
  simpa [nodeValue2683, Sparse.eval] using hc.symm

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

theorem sound2704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2704 node2704Labels = Sparse.eval nodeValue2704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2704) = mixedMoment B node2704 node2704Labels := rfl
  simpa [nodeValue2704, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2756 node2756Labels = Sparse.eval nodeValue2756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2756) = mixedMoment B node2756 node2756Labels := rfl
  simpa [nodeValue2756, Sparse.eval] using hc.symm

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

theorem sound3024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3024 node3024Labels = Sparse.eval nodeValue3024 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3024) = mixedMoment B node3024 node3024Labels := rfl
  simpa [nodeValue3024, Sparse.eval] using hc.symm

theorem sound3052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3052 node3052Labels = Sparse.eval nodeValue3052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3052) = mixedMoment B node3052 node3052Labels := rfl
  simpa [nodeValue3052, Sparse.eval] using hc.symm

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

theorem sound3261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3261 node3261Labels = Sparse.eval nodeValue3261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3261) = mixedMoment B node3261 node3261Labels := rfl
  simpa [nodeValue3261, Sparse.eval] using hc.symm

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

theorem sound3265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3265 node3265Labels = Sparse.eval nodeValue3265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3265) = mixedMoment B node3265 node3265Labels := rfl
  simpa [nodeValue3265, Sparse.eval] using hc.symm

theorem sound3272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3272 node3272Labels = Sparse.eval nodeValue3272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3272) = mixedMoment B node3272 node3272Labels := rfl
  simpa [nodeValue3272, Sparse.eval] using hc.symm

theorem sound3274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3274 node3274Labels = Sparse.eval nodeValue3274 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3274) = mixedMoment B node3274 node3274Labels := rfl
  simpa [nodeValue3274, Sparse.eval] using hc.symm

theorem sound3276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3276 node3276Labels = Sparse.eval nodeValue3276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3276) = mixedMoment B node3276 node3276Labels := rfl
  simpa [nodeValue3276, Sparse.eval] using hc.symm

theorem sound3277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3277 node3277Labels = Sparse.eval nodeValue3277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3277) = mixedMoment B node3277 node3277Labels := rfl
  simpa [nodeValue3277, Sparse.eval] using hc.symm

theorem sound3297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3297 node3297Labels = Sparse.eval nodeValue3297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3297) = mixedMoment B node3297 node3297Labels := rfl
  simpa [nodeValue3297, Sparse.eval] using hc.symm

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

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

theorem sound3408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3408 node3408Labels = Sparse.eval nodeValue3408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3408) = mixedMoment B node3408 node3408Labels := rfl
  simpa [nodeValue3408, Sparse.eval] using hc.symm

theorem sound3409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3409 node3409Labels = Sparse.eval nodeValue3409 (mixedVector B) := by
  simpa only [nodeValue3409, Sparse.eval_nil] using zero3409 B _hB _hF

theorem sound3411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3411 node3411Labels = Sparse.eval nodeValue3411 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3411) = mixedMoment B node3411 node3411Labels := rfl
  simpa [nodeValue3411, Sparse.eval] using hc.symm

theorem sound3412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3412 node3412Labels = Sparse.eval nodeValue3412 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3412) = mixedMoment B node3412 node3412Labels := rfl
  simpa [nodeValue3412, Sparse.eval] using hc.symm

theorem sound3413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3413 node3413Labels = Sparse.eval nodeValue3413 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3413) = mixedMoment B node3413 node3413Labels := rfl
  simpa [nodeValue3413, Sparse.eval] using hc.symm

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

theorem sound3450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3450 node3450Labels = Sparse.eval nodeValue3450 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3450) = mixedMoment B node3450 node3450Labels := rfl
  simpa [nodeValue3450, Sparse.eval] using hc.symm

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

theorem zero3483 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3483 node3483Labels = 0 := by
  exact mixedMoment_order_one B hB node3483 node3483Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3456 node3456Labels = Sparse.eval nodeValue3456 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3456) = mixedMoment B node3456 node3456Labels := rfl
  simpa [nodeValue3456, Sparse.eval] using hc.symm

theorem sound3457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3457 node3457Labels = Sparse.eval nodeValue3457 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3457) = mixedMoment B node3457 node3457Labels := rfl
  simpa [nodeValue3457, Sparse.eval] using hc.symm

theorem sound3465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3465 node3465Labels = Sparse.eval nodeValue3465 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3465) = mixedMoment B node3465 node3465Labels := rfl
  simpa [nodeValue3465, Sparse.eval] using hc.symm

theorem sound3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3467 node3467Labels = Sparse.eval nodeValue3467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3467) = mixedMoment B node3467 node3467Labels := rfl
  simpa [nodeValue3467, Sparse.eval] using hc.symm

theorem sound3470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3470 node3470Labels = Sparse.eval nodeValue3470 (mixedVector B) := by
  simpa only [nodeValue3470, Sparse.eval_nil] using zero3470 B _hB _hF

theorem sound3471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3471 node3471Labels = Sparse.eval nodeValue3471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3471) = mixedMoment B node3471 node3471Labels := rfl
  simpa [nodeValue3471, Sparse.eval] using hc.symm

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

theorem sound3483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3483 node3483Labels = Sparse.eval nodeValue3483 (mixedVector B) := by
  simpa only [nodeValue3483, Sparse.eval_nil] using zero3483 B _hB _hF

theorem sound3484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3484 node3484Labels = Sparse.eval nodeValue3484 (mixedVector B) := by
  simpa only [nodeValue3484, Sparse.eval_nil] using zero3484 B _hB _hF

theorem sound3486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3486 node3486Labels = Sparse.eval nodeValue3486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3486) = mixedMoment B node3486 node3486Labels := rfl
  simpa [nodeValue3486, Sparse.eval] using hc.symm

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

theorem sound3520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3520 node3520Labels = Sparse.eval nodeValue3520 (mixedVector B) := by
  simpa only [nodeValue3520, Sparse.eval_nil] using zero3520 B _hB _hF

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

theorem sound3542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3542 node3542Labels = Sparse.eval nodeValue3542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3542) = mixedMoment B node3542 node3542Labels := rfl
  simpa [nodeValue3542, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

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

theorem sound3646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3646 node3646Labels = Sparse.eval nodeValue3646 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3646) = mixedMoment B node3646 node3646Labels := rfl
  simpa [nodeValue3646, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3654 node3654Labels = 0 := by
  exact mixedMoment_order_one B hB node3654 node3654Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3654 node3654Labels = Sparse.eval nodeValue3654 (mixedVector B) := by
  simpa only [nodeValue3654, Sparse.eval_nil] using zero3654 B _hB _hF

theorem sound3680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3680 node3680Labels = Sparse.eval nodeValue3680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3680) = mixedMoment B node3680 node3680Labels := rfl
  simpa [nodeValue3680, Sparse.eval] using hc.symm

theorem sound3681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3681 node3681Labels = Sparse.eval nodeValue3681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3681) = mixedMoment B node3681 node3681Labels := rfl
  simpa [nodeValue3681, Sparse.eval] using hc.symm

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

theorem sound3694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3694 node3694Labels = Sparse.eval nodeValue3694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3694) = mixedMoment B node3694 node3694Labels := rfl
  simpa [nodeValue3694, Sparse.eval] using hc.symm

theorem sound3702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3702 node3702Labels = Sparse.eval nodeValue3702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3702) = mixedMoment B node3702 node3702Labels := rfl
  simpa [nodeValue3702, Sparse.eval] using hc.symm

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

theorem zero3775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3775 node3775Labels = 0 := by
  exact mixedMoment_order_one B hB node3775 node3775Labels 1
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

theorem sound3718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3718 node3718Labels = Sparse.eval nodeValue3718 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3718) = mixedMoment B node3718 node3718Labels := rfl
  simpa [nodeValue3718, Sparse.eval] using hc.symm

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

theorem sound3759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3759 node3759Labels = Sparse.eval nodeValue3759 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3759) = mixedMoment B node3759 node3759Labels := rfl
  simpa [nodeValue3759, Sparse.eval] using hc.symm

theorem sound3766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3766 node3766Labels = Sparse.eval nodeValue3766 (mixedVector B) := by
  simpa only [nodeValue3766, Sparse.eval_nil] using zero3766 B _hB _hF

theorem sound3767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3767 node3767Labels = Sparse.eval nodeValue3767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3767) = mixedMoment B node3767 node3767Labels := rfl
  simpa [nodeValue3767, Sparse.eval] using hc.symm

theorem sound3773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3773 node3773Labels = Sparse.eval nodeValue3773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3773) = mixedMoment B node3773 node3773Labels := rfl
  simpa [nodeValue3773, Sparse.eval] using hc.symm

theorem sound3775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3775 node3775Labels = Sparse.eval nodeValue3775 (mixedVector B) := by
  simpa only [nodeValue3775, Sparse.eval_nil] using zero3775 B _hB _hF

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

theorem sound3776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3776 node3776Labels = Sparse.eval nodeValue3776 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3776) = mixedMoment B node3776 node3776Labels := rfl
  simpa [nodeValue3776, Sparse.eval] using hc.symm

theorem sound3796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3796 node3796Labels = Sparse.eval nodeValue3796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3796) = mixedMoment B node3796 node3796Labels := rfl
  simpa [nodeValue3796, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources68
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2207 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2207 + difference 0 0) (sourceB2207 + difference 0 0) sourceC2207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2456) := by
    have ha : (tripleCharges (sourceA2207 + difference 0 0) (sourceB2207 + difference 0 0) sourceC2207) = raw30218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2207 sourceB2207 sourceC2207 difference raw30218; decide +kernel
    rw [ha]
    exact (canonical30218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2207 + difference 0 1) (sourceB2207 + difference 1 0) sourceC2207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3680) := by
    have ha : (tripleCharges (sourceA2207 + difference 0 1) (sourceB2207 + difference 1 0) sourceC2207) = raw30219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2207 sourceB2207 sourceC2207 difference raw30219; decide +kernel
    rw [ha]
    exact (canonical30219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2207 + difference 0 2) (sourceB2207 + difference 2 0) sourceC2207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2756) := by
    have ha : (tripleCharges (sourceA2207 + difference 0 2) (sourceB2207 + difference 2 0) sourceC2207) = raw30220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2207 sourceB2207 sourceC2207 difference raw30220; decide +kernel
    rw [ha]
    exact (canonical30220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2207 + difference 0 3) (sourceB2207 + difference 3 0) sourceC2207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3776) := by
    have ha : (tripleCharges (sourceA2207 + difference 0 3) (sourceB2207 + difference 3 0) sourceC2207) = raw30221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2207 sourceB2207 sourceC2207 difference raw30221; decide +kernel
    rw [ha]
    exact (canonical30221 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2207 + difference 0 4) (sourceB2207 + difference 4 0) sourceC2207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA2207 + difference 0 4) (sourceB2207 + difference 4 0) sourceC2207) = raw30222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2207 sourceB2207 sourceC2207 difference raw30222; decide +kernel
    rw [ha]
    exact (canonical30222 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2207 + difference 0 5) (sourceB2207 + difference 5 0) sourceC2207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA2207 + difference 0 5) (sourceB2207 + difference 5 0) sourceC2207) = raw30223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2207 sourceB2207 sourceC2207 difference raw30223; decide +kernel
    rw [ha]
    exact (canonical30223 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2207 + sourceB2207) sourceC2207) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2207 + sourceB2207) sourceC2207) = raw30224 := by
      apply Matrix.ext; unfold doubleCharges sourceA2207 sourceB2207 sourceC2207 raw30224; decide +kernel
    rw [ha]
    exact (canonical30224 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2207 sourceB2207 sourceC2207
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2207, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources69
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2212 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2212 + difference 0 1) (sourceB2212 + difference 1 0) sourceC2212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2212 + difference 0 1) (sourceB2212 + difference 1 0) sourceC2212) = raw30299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2212 sourceB2212 sourceC2212 difference raw30299; decide +kernel
    rw [ha]
    exact (canonical30299 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2212 + difference 1 1) (sourceB2212 + difference 1 1) sourceC2212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2212 + difference 1 1) (sourceB2212 + difference 1 1) sourceC2212) = raw30300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2212 sourceB2212 sourceC2212 difference raw30300; decide +kernel
    rw [ha]
    exact (canonical30300 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2212 + difference 2 1) (sourceB2212 + difference 1 2) sourceC2212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2212 + difference 2 1) (sourceB2212 + difference 1 2) sourceC2212) = raw30301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2212 sourceB2212 sourceC2212 difference raw30301; decide +kernel
    rw [ha]
    exact (canonical30301 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2212 + difference 3 1) (sourceB2212 + difference 1 3) sourceC2212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2321) := by
    have ha : (tripleCharges (sourceA2212 + difference 3 1) (sourceB2212 + difference 1 3) sourceC2212) = raw30302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2212 sourceB2212 sourceC2212 difference raw30302; decide +kernel
    rw [ha]
    exact (canonical30302 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2212 + difference 4 1) (sourceB2212 + difference 1 4) sourceC2212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2325) := by
    have ha : (tripleCharges (sourceA2212 + difference 4 1) (sourceB2212 + difference 1 4) sourceC2212) = raw30303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2212 sourceB2212 sourceC2212 difference raw30303; decide +kernel
    rw [ha]
    exact (canonical30303 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2212 + difference 5 1) (sourceB2212 + difference 1 5) sourceC2212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2327) := by
    have ha : (tripleCharges (sourceA2212 + difference 5 1) (sourceB2212 + difference 1 5) sourceC2212) = raw30304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2212 sourceB2212 sourceC2212 difference raw30304; decide +kernel
    rw [ha]
    exact (canonical30304 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2212 + sourceB2212) sourceC2212) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2212 + sourceB2212) sourceC2212) = raw30305 := by
      apply Matrix.ext; unfold doubleCharges sourceA2212 sourceB2212 sourceC2212 raw30305; decide +kernel
    rw [ha]
    exact (canonical30305 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2212 sourceB2212 sourceC2212
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2212, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2218 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2218 + difference 0 1) (sourceB2218 + difference 1 0) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3773) := by
    have ha : (tripleCharges (sourceA2218 + difference 0 1) (sourceB2218 + difference 1 0) sourceC2218) = raw30442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30442; decide +kernel
    rw [ha]
    exact (canonical30442 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2218 + difference 0 2) (sourceB2218 + difference 2 0) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3815) := by
    have ha : (tripleCharges (sourceA2218 + difference 0 2) (sourceB2218 + difference 2 0) sourceC2218) = raw30443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30443; decide +kernel
    rw [ha]
    exact (canonical30443 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2218 + difference 0 3) (sourceB2218 + difference 3 0) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3797) := by
    have ha : (tripleCharges (sourceA2218 + difference 0 3) (sourceB2218 + difference 3 0) sourceC2218) = raw30444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30444; decide +kernel
    rw [ha]
    exact (canonical30444 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2218 + difference 0 4) (sourceB2218 + difference 4 0) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2218 + difference 0 4) (sourceB2218 + difference 4 0) sourceC2218) = raw30445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30445; decide +kernel
    rw [ha]
    exact (canonical30445 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2218 + difference 0 5) (sourceB2218 + difference 5 0) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2218 + difference 0 5) (sourceB2218 + difference 5 0) sourceC2218) = raw30446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30446; decide +kernel
    rw [ha]
    exact (canonical30446 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2218 + difference 1 0) (sourceB2218 + difference 0 1) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA2218 + difference 1 0) (sourceB2218 + difference 0 1) sourceC2218) = raw30447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30447; decide +kernel
    rw [ha]
    exact (canonical30447 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2218 + difference 1 2) (sourceB2218 + difference 2 1) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2218 + difference 1 2) (sourceB2218 + difference 2 1) sourceC2218) = raw30448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30448; decide +kernel
    rw [ha]
    exact (canonical30448 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2218 + difference 1 3) (sourceB2218 + difference 3 1) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2218 + difference 1 3) (sourceB2218 + difference 3 1) sourceC2218) = raw30449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30449; decide +kernel
    rw [ha]
    exact (canonical30449 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2218 + difference 1 4) (sourceB2218 + difference 4 1) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA2218 + difference 1 4) (sourceB2218 + difference 4 1) sourceC2218) = raw30450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30450; decide +kernel
    rw [ha]
    exact (canonical30450 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2218 + difference 1 5) (sourceB2218 + difference 5 1) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA2218 + difference 1 5) (sourceB2218 + difference 5 1) sourceC2218) = raw30451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30451; decide +kernel
    rw [ha]
    exact (canonical30451 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2218 + difference 2 0) (sourceB2218 + difference 0 2) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3274) := by
    have ha : (tripleCharges (sourceA2218 + difference 2 0) (sourceB2218 + difference 0 2) sourceC2218) = raw30452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30452; decide +kernel
    rw [ha]
    exact (canonical30452 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2218 + difference 2 1) (sourceB2218 + difference 1 2) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3421) := by
    have ha : (tripleCharges (sourceA2218 + difference 2 1) (sourceB2218 + difference 1 2) sourceC2218) = raw30453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30453; decide +kernel
    rw [ha]
    exact (canonical30453 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2218 + difference 2 3) (sourceB2218 + difference 3 2) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3456) := by
    have ha : (tripleCharges (sourceA2218 + difference 2 3) (sourceB2218 + difference 3 2) sourceC2218) = raw30454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30454; decide +kernel
    rw [ha]
    exact (canonical30454 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2218 + difference 2 4) (sourceB2218 + difference 4 2) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA2218 + difference 2 4) (sourceB2218 + difference 4 2) sourceC2218) = raw30455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30455; decide +kernel
    rw [ha]
    exact (canonical30455 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2218 + difference 2 5) (sourceB2218 + difference 5 2) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA2218 + difference 2 5) (sourceB2218 + difference 5 2) sourceC2218) = raw30456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30456; decide +kernel
    rw [ha]
    exact (canonical30456 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2218 + difference 3 0) (sourceB2218 + difference 0 3) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA2218 + difference 3 0) (sourceB2218 + difference 0 3) sourceC2218) = raw30457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30457; decide +kernel
    rw [ha]
    exact (canonical30457 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2218 + difference 3 1) (sourceB2218 + difference 1 3) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3409) := by
    have ha : (tripleCharges (sourceA2218 + difference 3 1) (sourceB2218 + difference 1 3) sourceC2218) = raw30458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30458; decide +kernel
    rw [ha]
    exact (canonical30458 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2218 + difference 3 2) (sourceB2218 + difference 2 3) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3465) := by
    have ha : (tripleCharges (sourceA2218 + difference 3 2) (sourceB2218 + difference 2 3) sourceC2218) = raw30459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30459; decide +kernel
    rw [ha]
    exact (canonical30459 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2218 + difference 3 4) (sourceB2218 + difference 4 3) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA2218 + difference 3 4) (sourceB2218 + difference 4 3) sourceC2218) = raw30460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30460; decide +kernel
    rw [ha]
    exact (canonical30460 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2218 + difference 3 5) (sourceB2218 + difference 5 3) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA2218 + difference 3 5) (sourceB2218 + difference 5 3) sourceC2218) = raw30461 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30461; decide +kernel
    rw [ha]
    exact (canonical30461 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2218 + difference 4 0) (sourceB2218 + difference 0 4) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA2218 + difference 4 0) (sourceB2218 + difference 0 4) sourceC2218) = raw30462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30462; decide +kernel
    rw [ha]
    exact (canonical30462 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2218 + difference 4 1) (sourceB2218 + difference 1 4) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2218 + difference 4 1) (sourceB2218 + difference 1 4) sourceC2218) = raw30463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30463; decide +kernel
    rw [ha]
    exact (canonical30463 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2218 + difference 4 2) (sourceB2218 + difference 2 4) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2218 + difference 4 2) (sourceB2218 + difference 2 4) sourceC2218) = raw30464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30464; decide +kernel
    rw [ha]
    exact (canonical30464 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2218 + difference 4 3) (sourceB2218 + difference 3 4) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2218 + difference 4 3) (sourceB2218 + difference 3 4) sourceC2218) = raw30465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30465; decide +kernel
    rw [ha]
    exact (canonical30465 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2218 + difference 4 5) (sourceB2218 + difference 5 4) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA2218 + difference 4 5) (sourceB2218 + difference 5 4) sourceC2218) = raw30466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30466; decide +kernel
    rw [ha]
    exact (canonical30466 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2218 + difference 5 0) (sourceB2218 + difference 0 5) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA2218 + difference 5 0) (sourceB2218 + difference 0 5) sourceC2218) = raw30467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30467; decide +kernel
    rw [ha]
    exact (canonical30467 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2218 + difference 5 1) (sourceB2218 + difference 1 5) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2218 + difference 5 1) (sourceB2218 + difference 1 5) sourceC2218) = raw30468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30468; decide +kernel
    rw [ha]
    exact (canonical30468 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2218 + difference 5 2) (sourceB2218 + difference 2 5) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2218 + difference 5 2) (sourceB2218 + difference 2 5) sourceC2218) = raw30469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30469; decide +kernel
    rw [ha]
    exact (canonical30469 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2218 + difference 5 3) (sourceB2218 + difference 3 5) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2218 + difference 5 3) (sourceB2218 + difference 3 5) sourceC2218) = raw30470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30470; decide +kernel
    rw [ha]
    exact (canonical30470 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2218 + difference 5 4) (sourceB2218 + difference 4 5) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA2218 + difference 5 4) (sourceB2218 + difference 4 5) sourceC2218) = raw30471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30471; decide +kernel
    rw [ha]
    exact (canonical30471 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2218 sourceB2218 sourceC2218
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2218, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2219 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2219 + difference 0 1) (sourceB2219 + difference 1 0) sourceC2219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2219 + difference 0 1) (sourceB2219 + difference 1 0) sourceC2219) = raw30472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2219 sourceB2219 sourceC2219 difference raw30472; decide +kernel
    rw [ha]
    exact (canonical30472 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2219 + difference 1 1) (sourceB2219 + difference 1 1) sourceC2219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2219 + difference 1 1) (sourceB2219 + difference 1 1) sourceC2219) = raw30473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2219 sourceB2219 sourceC2219 difference raw30473; decide +kernel
    rw [ha]
    exact (canonical30473 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2219 + difference 2 1) (sourceB2219 + difference 1 2) sourceC2219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2219 + difference 2 1) (sourceB2219 + difference 1 2) sourceC2219) = raw30474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2219 sourceB2219 sourceC2219 difference raw30474; decide +kernel
    rw [ha]
    exact (canonical30474 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2219 + difference 3 1) (sourceB2219 + difference 1 3) sourceC2219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2322) := by
    have ha : (tripleCharges (sourceA2219 + difference 3 1) (sourceB2219 + difference 1 3) sourceC2219) = raw30475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2219 sourceB2219 sourceC2219 difference raw30475; decide +kernel
    rw [ha]
    exact (canonical30475 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2219 + difference 4 1) (sourceB2219 + difference 1 4) sourceC2219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2326) := by
    have ha : (tripleCharges (sourceA2219 + difference 4 1) (sourceB2219 + difference 1 4) sourceC2219) = raw30476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2219 sourceB2219 sourceC2219 difference raw30476; decide +kernel
    rw [ha]
    exact (canonical30476 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2219 + difference 5 1) (sourceB2219 + difference 1 5) sourceC2219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2326) := by
    have ha : (tripleCharges (sourceA2219 + difference 5 1) (sourceB2219 + difference 1 5) sourceC2219) = raw30477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2219 sourceB2219 sourceC2219 difference raw30477; decide +kernel
    rw [ha]
    exact (canonical30477 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2219 + sourceB2219) sourceC2219) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2219 + sourceB2219) sourceC2219) = raw24045 := by
      apply Matrix.ext; unfold doubleCharges sourceA2219 sourceB2219 sourceC2219 raw24045; decide +kernel
    rw [ha]
    exact (canonical24045 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2219 sourceB2219 sourceC2219
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2219, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2230 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2230 + difference 0 1) (sourceB2230 + difference 1 0) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA2230 + difference 0 1) (sourceB2230 + difference 1 0) sourceC2230) = raw30623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30623; decide +kernel
    rw [ha]
    exact (canonical30623 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2230 + difference 0 2) (sourceB2230 + difference 2 0) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2230 + difference 0 2) (sourceB2230 + difference 2 0) sourceC2230) = raw30624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30624; decide +kernel
    rw [ha]
    exact (canonical30624 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2230 + difference 0 3) (sourceB2230 + difference 3 0) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2230 + difference 0 3) (sourceB2230 + difference 3 0) sourceC2230) = raw30625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30625; decide +kernel
    rw [ha]
    exact (canonical30625 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2230 + difference 0 4) (sourceB2230 + difference 4 0) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA2230 + difference 0 4) (sourceB2230 + difference 4 0) sourceC2230) = raw5831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5831; decide +kernel
    rw [ha]
    exact (canonical5831 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2230 + difference 0 5) (sourceB2230 + difference 5 0) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2230 + difference 0 5) (sourceB2230 + difference 5 0) sourceC2230) = raw30626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30626; decide +kernel
    rw [ha]
    exact (canonical30626 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2230 + difference 1 0) (sourceB2230 + difference 0 1) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA2230 + difference 1 0) (sourceB2230 + difference 0 1) sourceC2230) = raw5851 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5851; decide +kernel
    rw [ha]
    exact (canonical5851 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2230 + difference 1 2) (sourceB2230 + difference 2 1) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2230 + difference 1 2) (sourceB2230 + difference 2 1) sourceC2230) = raw5853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5853; decide +kernel
    rw [ha]
    exact (canonical5853 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2230 + difference 1 3) (sourceB2230 + difference 3 1) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2230 + difference 1 3) (sourceB2230 + difference 3 1) sourceC2230) = raw5854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5854; decide +kernel
    rw [ha]
    exact (canonical5854 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2230 + difference 1 4) (sourceB2230 + difference 4 1) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA2230 + difference 1 4) (sourceB2230 + difference 4 1) sourceC2230) = raw30627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30627; decide +kernel
    rw [ha]
    exact (canonical30627 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2230 + difference 1 5) (sourceB2230 + difference 5 1) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA2230 + difference 1 5) (sourceB2230 + difference 5 1) sourceC2230) = raw5855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5855; decide +kernel
    rw [ha]
    exact (canonical5855 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2230 + difference 2 0) (sourceB2230 + difference 0 2) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA2230 + difference 2 0) (sourceB2230 + difference 0 2) sourceC2230) = raw30628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30628; decide +kernel
    rw [ha]
    exact (canonical30628 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2230 + difference 2 1) (sourceB2230 + difference 1 2) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2230 + difference 2 1) (sourceB2230 + difference 1 2) sourceC2230) = raw30629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30629; decide +kernel
    rw [ha]
    exact (canonical30629 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2230 + difference 2 3) (sourceB2230 + difference 3 2) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2652) := by
    have ha : (tripleCharges (sourceA2230 + difference 2 3) (sourceB2230 + difference 3 2) sourceC2230) = raw30630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30630; decide +kernel
    rw [ha]
    exact (canonical30630 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2230 + difference 2 4) (sourceB2230 + difference 4 2) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA2230 + difference 2 4) (sourceB2230 + difference 4 2) sourceC2230) = raw5842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5842; decide +kernel
    rw [ha]
    exact (canonical5842 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2230 + difference 2 5) (sourceB2230 + difference 5 2) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2230 + difference 2 5) (sourceB2230 + difference 5 2) sourceC2230) = raw30631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30631; decide +kernel
    rw [ha]
    exact (canonical30631 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2230 + difference 3 0) (sourceB2230 + difference 0 3) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA2230 + difference 3 0) (sourceB2230 + difference 0 3) sourceC2230) = raw30632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30632; decide +kernel
    rw [ha]
    exact (canonical30632 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2230 + difference 3 1) (sourceB2230 + difference 1 3) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2230 + difference 3 1) (sourceB2230 + difference 1 3) sourceC2230) = raw30633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30633; decide +kernel
    rw [ha]
    exact (canonical30633 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2230 + difference 3 2) (sourceB2230 + difference 2 3) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2652) := by
    have ha : (tripleCharges (sourceA2230 + difference 3 2) (sourceB2230 + difference 2 3) sourceC2230) = raw30634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30634; decide +kernel
    rw [ha]
    exact (canonical30634 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2230 + difference 3 4) (sourceB2230 + difference 4 3) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA2230 + difference 3 4) (sourceB2230 + difference 4 3) sourceC2230) = raw5847 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5847; decide +kernel
    rw [ha]
    exact (canonical5847 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2230 + difference 3 5) (sourceB2230 + difference 5 3) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2230 + difference 3 5) (sourceB2230 + difference 5 3) sourceC2230) = raw30635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30635; decide +kernel
    rw [ha]
    exact (canonical30635 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2230 + difference 4 0) (sourceB2230 + difference 0 4) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2230 + difference 4 0) (sourceB2230 + difference 0 4) sourceC2230) = raw30636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30636; decide +kernel
    rw [ha]
    exact (canonical30636 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2230 + difference 4 1) (sourceB2230 + difference 1 4) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2230 + difference 4 1) (sourceB2230 + difference 1 4) sourceC2230) = raw30637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30637; decide +kernel
    rw [ha]
    exact (canonical30637 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2230 + difference 4 2) (sourceB2230 + difference 2 4) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2230 + difference 4 2) (sourceB2230 + difference 2 4) sourceC2230) = raw30638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30638; decide +kernel
    rw [ha]
    exact (canonical30638 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2230 + difference 4 3) (sourceB2230 + difference 3 4) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2230 + difference 4 3) (sourceB2230 + difference 3 4) sourceC2230) = raw30639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30639; decide +kernel
    rw [ha]
    exact (canonical30639 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2230 + difference 4 5) (sourceB2230 + difference 5 4) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2230 + difference 4 5) (sourceB2230 + difference 5 4) sourceC2230) = raw30640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30640; decide +kernel
    rw [ha]
    exact (canonical30640 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2230 + difference 5 0) (sourceB2230 + difference 0 5) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2258) := by
    have ha : (tripleCharges (sourceA2230 + difference 5 0) (sourceB2230 + difference 0 5) sourceC2230) = raw30641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30641; decide +kernel
    rw [ha]
    exact (canonical30641 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2230 + difference 5 1) (sourceB2230 + difference 1 5) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2286) := by
    have ha : (tripleCharges (sourceA2230 + difference 5 1) (sourceB2230 + difference 1 5) sourceC2230) = raw30642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30642; decide +kernel
    rw [ha]
    exact (canonical30642 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2230 + difference 5 2) (sourceB2230 + difference 2 5) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA2230 + difference 5 2) (sourceB2230 + difference 2 5) sourceC2230) = raw30643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30643; decide +kernel
    rw [ha]
    exact (canonical30643 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2230 + difference 5 3) (sourceB2230 + difference 3 5) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA2230 + difference 5 3) (sourceB2230 + difference 3 5) sourceC2230) = raw30644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30644; decide +kernel
    rw [ha]
    exact (canonical30644 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2230 + difference 5 4) (sourceB2230 + difference 4 5) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA2230 + difference 5 4) (sourceB2230 + difference 4 5) sourceC2230) = raw5857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5857; decide +kernel
    rw [ha]
    exact (canonical5857 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2230 sourceB2230 sourceC2230
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2230, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2236 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2236 + difference 0 1) (sourceB2236 + difference 1 0) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3775) := by
    have ha : (tripleCharges (sourceA2236 + difference 0 1) (sourceB2236 + difference 1 0) sourceC2236) = raw30730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30730; decide +kernel
    rw [ha]
    exact (canonical30730 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2236 + difference 0 2) (sourceB2236 + difference 2 0) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2236 + difference 0 2) (sourceB2236 + difference 2 0) sourceC2236) = raw30731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30731; decide +kernel
    rw [ha]
    exact (canonical30731 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2236 + difference 0 3) (sourceB2236 + difference 3 0) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2236 + difference 0 3) (sourceB2236 + difference 3 0) sourceC2236) = raw30732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30732; decide +kernel
    rw [ha]
    exact (canonical30732 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2236 + difference 0 4) (sourceB2236 + difference 4 0) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA2236 + difference 0 4) (sourceB2236 + difference 4 0) sourceC2236) = raw30733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30733; decide +kernel
    rw [ha]
    exact (canonical30733 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2236 + difference 0 5) (sourceB2236 + difference 5 0) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2236 + difference 0 5) (sourceB2236 + difference 5 0) sourceC2236) = raw30734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30734; decide +kernel
    rw [ha]
    exact (canonical30734 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2236 + difference 1 0) (sourceB2236 + difference 0 1) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA2236 + difference 1 0) (sourceB2236 + difference 0 1) sourceC2236) = raw30735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30735; decide +kernel
    rw [ha]
    exact (canonical30735 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2236 + difference 1 2) (sourceB2236 + difference 2 1) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2236 + difference 1 2) (sourceB2236 + difference 2 1) sourceC2236) = raw30736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30736; decide +kernel
    rw [ha]
    exact (canonical30736 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2236 + difference 1 3) (sourceB2236 + difference 3 1) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2236 + difference 1 3) (sourceB2236 + difference 3 1) sourceC2236) = raw30737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30737; decide +kernel
    rw [ha]
    exact (canonical30737 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2236 + difference 1 4) (sourceB2236 + difference 4 1) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA2236 + difference 1 4) (sourceB2236 + difference 4 1) sourceC2236) = raw3996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw3996; decide +kernel
    rw [ha]
    exact (canonical3996 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2236 + difference 1 5) (sourceB2236 + difference 5 1) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA2236 + difference 1 5) (sourceB2236 + difference 5 1) sourceC2236) = raw30738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30738; decide +kernel
    rw [ha]
    exact (canonical30738 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2236 + difference 2 0) (sourceB2236 + difference 0 2) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA2236 + difference 2 0) (sourceB2236 + difference 0 2) sourceC2236) = raw30739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30739; decide +kernel
    rw [ha]
    exact (canonical30739 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2236 + difference 2 1) (sourceB2236 + difference 1 2) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2236 + difference 2 1) (sourceB2236 + difference 1 2) sourceC2236) = raw30740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30740; decide +kernel
    rw [ha]
    exact (canonical30740 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2236 + difference 2 3) (sourceB2236 + difference 3 2) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3450) := by
    have ha : (tripleCharges (sourceA2236 + difference 2 3) (sourceB2236 + difference 3 2) sourceC2236) = raw30741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30741; decide +kernel
    rw [ha]
    exact (canonical30741 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2236 + difference 2 4) (sourceB2236 + difference 4 2) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA2236 + difference 2 4) (sourceB2236 + difference 4 2) sourceC2236) = raw30742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30742; decide +kernel
    rw [ha]
    exact (canonical30742 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2236 + difference 2 5) (sourceB2236 + difference 5 2) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2236 + difference 2 5) (sourceB2236 + difference 5 2) sourceC2236) = raw30743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30743; decide +kernel
    rw [ha]
    exact (canonical30743 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2236 + difference 3 0) (sourceB2236 + difference 0 3) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA2236 + difference 3 0) (sourceB2236 + difference 0 3) sourceC2236) = raw30744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30744; decide +kernel
    rw [ha]
    exact (canonical30744 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2236 + difference 3 1) (sourceB2236 + difference 1 3) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2236 + difference 3 1) (sourceB2236 + difference 1 3) sourceC2236) = raw30745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30745; decide +kernel
    rw [ha]
    exact (canonical30745 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2236 + difference 3 2) (sourceB2236 + difference 2 3) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3450) := by
    have ha : (tripleCharges (sourceA2236 + difference 3 2) (sourceB2236 + difference 2 3) sourceC2236) = raw30746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30746; decide +kernel
    rw [ha]
    exact (canonical30746 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2236 + difference 3 4) (sourceB2236 + difference 4 3) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA2236 + difference 3 4) (sourceB2236 + difference 4 3) sourceC2236) = raw30747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30747; decide +kernel
    rw [ha]
    exact (canonical30747 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2236 + difference 3 5) (sourceB2236 + difference 5 3) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2236 + difference 3 5) (sourceB2236 + difference 5 3) sourceC2236) = raw30748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30748; decide +kernel
    rw [ha]
    exact (canonical30748 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2236 + difference 4 0) (sourceB2236 + difference 0 4) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2236 + difference 4 0) (sourceB2236 + difference 0 4) sourceC2236) = raw30749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30749; decide +kernel
    rw [ha]
    exact (canonical30749 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2236 + difference 4 1) (sourceB2236 + difference 1 4) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3422) := by
    have ha : (tripleCharges (sourceA2236 + difference 4 1) (sourceB2236 + difference 1 4) sourceC2236) = raw30750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30750; decide +kernel
    rw [ha]
    exact (canonical30750 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2236 + difference 4 2) (sourceB2236 + difference 2 4) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2236 + difference 4 2) (sourceB2236 + difference 2 4) sourceC2236) = raw30751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30751; decide +kernel
    rw [ha]
    exact (canonical30751 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2236 + difference 4 3) (sourceB2236 + difference 3 4) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2236 + difference 4 3) (sourceB2236 + difference 3 4) sourceC2236) = raw30752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30752; decide +kernel
    rw [ha]
    exact (canonical30752 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2236 + difference 4 5) (sourceB2236 + difference 5 4) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3484) := by
    have ha : (tripleCharges (sourceA2236 + difference 4 5) (sourceB2236 + difference 5 4) sourceC2236) = raw30753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30753; decide +kernel
    rw [ha]
    exact (canonical30753 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2236 + difference 5 0) (sourceB2236 + difference 0 5) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2236 + difference 5 0) (sourceB2236 + difference 0 5) sourceC2236) = raw30754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30754; decide +kernel
    rw [ha]
    exact (canonical30754 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2236 + difference 5 1) (sourceB2236 + difference 1 5) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2236 + difference 5 1) (sourceB2236 + difference 1 5) sourceC2236) = raw30755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30755; decide +kernel
    rw [ha]
    exact (canonical30755 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2236 + difference 5 2) (sourceB2236 + difference 2 5) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2236 + difference 5 2) (sourceB2236 + difference 2 5) sourceC2236) = raw30756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30756; decide +kernel
    rw [ha]
    exact (canonical30756 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2236 + difference 5 3) (sourceB2236 + difference 3 5) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2236 + difference 5 3) (sourceB2236 + difference 3 5) sourceC2236) = raw30757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30757; decide +kernel
    rw [ha]
    exact (canonical30757 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2236 + difference 5 4) (sourceB2236 + difference 4 5) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA2236 + difference 5 4) (sourceB2236 + difference 4 5) sourceC2236) = raw3993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw3993; decide +kernel
    rw [ha]
    exact (canonical3993 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2236 sourceB2236 sourceC2236
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2236, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources70
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2244 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2244 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2244 + difference 0 0) (sourceB2244 + difference 0 0) sourceC2244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2379) := by
    have ha : (tripleCharges (sourceA2244 + difference 0 0) (sourceB2244 + difference 0 0) sourceC2244) = raw30862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2244 sourceB2244 sourceC2244 difference raw30862; decide +kernel
    rw [ha]
    exact (canonical30862 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2244 + difference 0 1) (sourceB2244 + difference 1 0) sourceC2244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3646) := by
    have ha : (tripleCharges (sourceA2244 + difference 0 1) (sourceB2244 + difference 1 0) sourceC2244) = raw30863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2244 sourceB2244 sourceC2244 difference raw30863; decide +kernel
    rw [ha]
    exact (canonical30863 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2244 + difference 0 2) (sourceB2244 + difference 2 0) sourceC2244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3718) := by
    have ha : (tripleCharges (sourceA2244 + difference 0 2) (sourceB2244 + difference 2 0) sourceC2244) = raw30864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2244 sourceB2244 sourceC2244 difference raw30864; decide +kernel
    rw [ha]
    exact (canonical30864 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2244 + difference 0 3) (sourceB2244 + difference 3 0) sourceC2244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3718) := by
    have ha : (tripleCharges (sourceA2244 + difference 0 3) (sourceB2244 + difference 3 0) sourceC2244) = raw30865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2244 sourceB2244 sourceC2244 difference raw30865; decide +kernel
    rw [ha]
    exact (canonical30865 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2244 + difference 0 4) (sourceB2244 + difference 4 0) sourceC2244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA2244 + difference 0 4) (sourceB2244 + difference 4 0) sourceC2244) = raw30866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2244 sourceB2244 sourceC2244 difference raw30866; decide +kernel
    rw [ha]
    exact (canonical30866 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2244 + difference 0 5) (sourceB2244 + difference 5 0) sourceC2244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2244 + difference 0 5) (sourceB2244 + difference 5 0) sourceC2244) = raw30867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2244 sourceB2244 sourceC2244 difference raw30867; decide +kernel
    rw [ha]
    exact (canonical30867 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2244 + sourceB2244) sourceC2244) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2244 + sourceB2244) sourceC2244) = raw30868 := by
      apply Matrix.ext; unfold doubleCharges sourceA2244 sourceB2244 sourceC2244 raw30868; decide +kernel
    rw [ha]
    exact (canonical30868 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2244 sourceB2244 sourceC2244
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2244, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2245 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2245 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2245 + difference 0 0) (sourceB2245 + difference 0 0) sourceC2245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA2245 + difference 0 0) (sourceB2245 + difference 0 0) sourceC2245) = raw30869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2245 sourceB2245 sourceC2245 difference raw30869; decide +kernel
    rw [ha]
    exact (canonical30869 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2245 + difference 0 1) (sourceB2245 + difference 1 0) sourceC2245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3654) := by
    have ha : (tripleCharges (sourceA2245 + difference 0 1) (sourceB2245 + difference 1 0) sourceC2245) = raw30870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2245 sourceB2245 sourceC2245 difference raw30870; decide +kernel
    rw [ha]
    exact (canonical30870 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2245 + difference 0 2) (sourceB2245 + difference 2 0) sourceC2245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3702) := by
    have ha : (tripleCharges (sourceA2245 + difference 0 2) (sourceB2245 + difference 2 0) sourceC2245) = raw30871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2245 sourceB2245 sourceC2245 difference raw30871; decide +kernel
    rw [ha]
    exact (canonical30871 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2245 + difference 0 3) (sourceB2245 + difference 3 0) sourceC2245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3681) := by
    have ha : (tripleCharges (sourceA2245 + difference 0 3) (sourceB2245 + difference 3 0) sourceC2245) = raw30872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2245 sourceB2245 sourceC2245 difference raw30872; decide +kernel
    rw [ha]
    exact (canonical30872 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2245 + difference 0 4) (sourceB2245 + difference 4 0) sourceC2245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2245 + difference 0 4) (sourceB2245 + difference 4 0) sourceC2245) = raw30873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2245 sourceB2245 sourceC2245 difference raw30873; decide +kernel
    rw [ha]
    exact (canonical30873 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2245 + difference 0 5) (sourceB2245 + difference 5 0) sourceC2245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2245 + difference 0 5) (sourceB2245 + difference 5 0) sourceC2245) = raw30874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2245 sourceB2245 sourceC2245 difference raw30874; decide +kernel
    rw [ha]
    exact (canonical30874 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2245 + sourceB2245) sourceC2245) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2245 + sourceB2245) sourceC2245) = raw30875 := by
      apply Matrix.ext; unfold doubleCharges sourceA2245 sourceB2245 sourceC2245 raw30875; decide +kernel
    rw [ha]
    exact (canonical30875 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2245 sourceB2245 sourceC2245
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2245, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1824 : Integer.Sparse.reindex keyMap MixedData.row1824 = numericRow1824 := by decide +kernel

theorem numericCheck1824 (x : Master → ℝ) : Integer.Sparse.eval numericRow1824 x =
    (1 : ℝ) * reducedSource1824 x := by
  norm_num [numericRow1824, reducedSource1824, Integer.Sparse.eval, Sparse.eval, nodeValue2456, nodeValue2756, nodeValue3680, nodeValue3776, nodeValue3796, nodeValue4090]

theorem reindexCheck1827 : Integer.Sparse.reindex keyMap MixedData.row1827 = numericRow1827 := by decide +kernel

theorem numericCheck1827 (x : Master → ℝ) : Integer.Sparse.eval numericRow1827 x =
    (1 : ℝ) * reducedSource1827 x := by
  norm_num [numericRow1827, reducedSource1827, Integer.Sparse.eval, Sparse.eval, nodeValue2321, nodeValue2325, nodeValue2327, nodeValue2341, nodeValue2488, nodeValue3693, nodeValue4092]

theorem reindexCheck1829 : Integer.Sparse.reindex keyMap MixedData.row1829 = numericRow1829 := by decide +kernel

theorem numericCheck1829 (x : Master → ℝ) : Integer.Sparse.eval numericRow1829 x =
    (1 : ℝ) * reducedSource1829 x := by
  norm_num [numericRow1829, reducedSource1829, Integer.Sparse.eval, Sparse.eval, nodeValue3261, nodeValue3272, nodeValue3274, nodeValue3297, nodeValue3408, nodeValue3409, nodeValue3413, nodeValue3419, nodeValue3421, nodeValue3456, nodeValue3465, nodeValue3467, nodeValue3481, nodeValue3483, nodeValue3520, nodeValue3542, nodeValue3544, nodeValue3773, nodeValue3797, nodeValue3815, nodeValue3816]

theorem reindexCheck1830 : Integer.Sparse.reindex keyMap MixedData.row1830 = numericRow1830 := by decide +kernel

theorem numericCheck1830 (x : Master → ℝ) : Integer.Sparse.eval numericRow1830 x =
    (1 : ℝ) * reducedSource1830 x := by
  norm_num [numericRow1830, reducedSource1830, Integer.Sparse.eval, Sparse.eval, nodeValue2322, nodeValue2326, nodeValue2342, nodeValue2489, nodeValue3694, nodeValue4091]

theorem reindexCheck1832 : Integer.Sparse.reindex keyMap MixedData.row1832 = numericRow1832 := by decide +kernel

theorem numericCheck1832 (x : Master → ℝ) : Integer.Sparse.eval numericRow1832 x =
    (1 : ℝ) * reducedSource1832 x := by
  norm_num [numericRow1832, reducedSource1832, Integer.Sparse.eval, Sparse.eval, nodeValue2151, nodeValue2167, nodeValue2168, nodeValue2228, nodeValue2256, nodeValue2258, nodeValue2267, nodeValue2286, nodeValue2652, nodeValue2657, nodeValue2658, nodeValue2670, nodeValue2672, nodeValue2683, nodeValue2686, nodeValue2704, nodeValue2740, nodeValue2742, nodeValue3024, nodeValue3052, nodeValue3054]

theorem reindexCheck1834 : Integer.Sparse.reindex keyMap MixedData.row1834 = numericRow1834 := by decide +kernel

theorem numericCheck1834 (x : Master → ℝ) : Integer.Sparse.eval numericRow1834 x =
    (1 : ℝ) * reducedSource1834 x := by
  norm_num [numericRow1834, reducedSource1834, Integer.Sparse.eval, Sparse.eval, nodeValue3265, nodeValue3276, nodeValue3277, nodeValue3301, nodeValue3411, nodeValue3412, nodeValue3422, nodeValue3423, nodeValue3450, nodeValue3457, nodeValue3470, nodeValue3471, nodeValue3484, nodeValue3486, nodeValue3522, nodeValue3547, nodeValue3548, nodeValue3766, nodeValue3775, nodeValue3817, nodeValue4092]

theorem reindexCheck1836 : Integer.Sparse.reindex keyMap MixedData.row1836 = numericRow1836 := by decide +kernel

theorem numericCheck1836 (x : Master → ℝ) : Integer.Sparse.eval numericRow1836 x =
    (1 : ℝ) * reducedSource1836 x := by
  norm_num [numericRow1836, reducedSource1836, Integer.Sparse.eval, Sparse.eval, nodeValue2379, nodeValue3646, nodeValue3718, nodeValue3757, nodeValue3759, nodeValue4088]

theorem reindexCheck1837 : Integer.Sparse.reindex keyMap MixedData.row1837 = numericRow1837 := by decide +kernel

theorem numericCheck1837 (x : Master → ℝ) : Integer.Sparse.eval numericRow1837 x =
    (1 : ℝ) * reducedSource1837 x := by
  norm_num [numericRow1837, reducedSource1837, Integer.Sparse.eval, Sparse.eval, nodeValue2388, nodeValue3654, nodeValue3681, nodeValue3702, nodeValue3766, nodeValue3767, nodeValue4088]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1824 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1824 (mixedVector B) = 0 := by
  have h2456 : mixedVector B (Sum.inr 2456) = Sparse.eval nodeValue2456 (mixedVector B) := by
    change mixedMoment B node2456 node2456Labels = _
    exact sound2456 B hB hF
  have h2756 : mixedVector B (Sum.inr 2756) = Sparse.eval nodeValue2756 (mixedVector B) := by
    change mixedMoment B node2756 node2756Labels = _
    exact sound2756 B hB hF
  have h3680 : mixedVector B (Sum.inr 3680) = Sparse.eval nodeValue3680 (mixedVector B) := by
    change mixedMoment B node3680 node3680Labels = _
    exact sound3680 B hB hF
  have h3776 : mixedVector B (Sum.inr 3776) = Sparse.eval nodeValue3776 (mixedVector B) := by
    change mixedMoment B node3776 node3776Labels = _
    exact sound3776 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm2207, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2456, h2756, h3680, h3776, h3796, h4090, reducedSource1824] using sourceEq2207 B hB

theorem rowSound1824 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1824 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1824, numericCheck1824, reducedZero1824 B hB hF, mul_zero]

theorem reducedZero1827 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1827 (mixedVector B) = 0 := by
  have h2321 : mixedVector B (Sum.inr 2321) = Sparse.eval nodeValue2321 (mixedVector B) := by
    change mixedMoment B node2321 node2321Labels = _
    exact sound2321 B hB hF
  have h2325 : mixedVector B (Sum.inr 2325) = Sparse.eval nodeValue2325 (mixedVector B) := by
    change mixedMoment B node2325 node2325Labels = _
    exact sound2325 B hB hF
  have h2327 : mixedVector B (Sum.inr 2327) = Sparse.eval nodeValue2327 (mixedVector B) := by
    change mixedMoment B node2327 node2327Labels = _
    exact sound2327 B hB hF
  have h2341 : mixedVector B (Sum.inr 2341) = Sparse.eval nodeValue2341 (mixedVector B) := by
    change mixedMoment B node2341 node2341Labels = _
    exact sound2341 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2212, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2321, h2325, h2327, h2341, h2488, h3693, h4092, reducedSource1827] using sourceEq2212 B hB

theorem rowSound1827 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1827 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1827, numericCheck1827, reducedZero1827 B hB hF, mul_zero]

theorem reducedZero1829 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1829 (mixedVector B) = 0 := by
  have h3261 : mixedVector B (Sum.inr 3261) = Sparse.eval nodeValue3261 (mixedVector B) := by
    change mixedMoment B node3261 node3261Labels = _
    exact sound3261 B hB hF
  have h3272 : mixedVector B (Sum.inr 3272) = Sparse.eval nodeValue3272 (mixedVector B) := by
    change mixedMoment B node3272 node3272Labels = _
    exact sound3272 B hB hF
  have h3274 : mixedVector B (Sum.inr 3274) = Sparse.eval nodeValue3274 (mixedVector B) := by
    change mixedMoment B node3274 node3274Labels = _
    exact sound3274 B hB hF
  have h3297 : mixedVector B (Sum.inr 3297) = Sparse.eval nodeValue3297 (mixedVector B) := by
    change mixedMoment B node3297 node3297Labels = _
    exact sound3297 B hB hF
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3409 : mixedVector B (Sum.inr 3409) = Sparse.eval nodeValue3409 (mixedVector B) := by
    change mixedMoment B node3409 node3409Labels = _
    exact sound3409 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3419 : mixedVector B (Sum.inr 3419) = Sparse.eval nodeValue3419 (mixedVector B) := by
    change mixedMoment B node3419 node3419Labels = _
    exact sound3419 B hB hF
  have h3421 : mixedVector B (Sum.inr 3421) = Sparse.eval nodeValue3421 (mixedVector B) := by
    change mixedMoment B node3421 node3421Labels = _
    exact sound3421 B hB hF
  have h3456 : mixedVector B (Sum.inr 3456) = Sparse.eval nodeValue3456 (mixedVector B) := by
    change mixedMoment B node3456 node3456Labels = _
    exact sound3456 B hB hF
  have h3465 : mixedVector B (Sum.inr 3465) = Sparse.eval nodeValue3465 (mixedVector B) := by
    change mixedMoment B node3465 node3465Labels = _
    exact sound3465 B hB hF
  have h3467 : mixedVector B (Sum.inr 3467) = Sparse.eval nodeValue3467 (mixedVector B) := by
    change mixedMoment B node3467 node3467Labels = _
    exact sound3467 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3483 : mixedVector B (Sum.inr 3483) = Sparse.eval nodeValue3483 (mixedVector B) := by
    change mixedMoment B node3483 node3483Labels = _
    exact sound3483 B hB hF
  have h3520 : mixedVector B (Sum.inr 3520) = Sparse.eval nodeValue3520 (mixedVector B) := by
    change mixedMoment B node3520 node3520Labels = _
    exact sound3520 B hB hF
  have h3542 : mixedVector B (Sum.inr 3542) = Sparse.eval nodeValue3542 (mixedVector B) := by
    change mixedMoment B node3542 node3542Labels = _
    exact sound3542 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3773 : mixedVector B (Sum.inr 3773) = Sparse.eval nodeValue3773 (mixedVector B) := by
    change mixedMoment B node3773 node3773Labels = _
    exact sound3773 B hB hF
  have h3797 : mixedVector B (Sum.inr 3797) = Sparse.eval nodeValue3797 (mixedVector B) := by
    change mixedMoment B node3797 node3797Labels = _
    exact sound3797 B hB hF
  have h3815 : mixedVector B (Sum.inr 3815) = Sparse.eval nodeValue3815 (mixedVector B) := by
    change mixedMoment B node3815 node3815Labels = _
    exact sound3815 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  simpa only [sourceForm2218, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3261, h3272, h3274, h3297, h3408, h3409, h3413, h3419, h3421, h3456, h3465, h3467, h3481, h3483, h3520, h3542, h3544, h3773, h3797, h3815, h3816, reducedSource1829] using sourceEq2218 B hB

theorem rowSound1829 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1829 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1829, numericCheck1829, reducedZero1829 B hB hF, mul_zero]

theorem reducedZero1830 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1830 (mixedVector B) = 0 := by
  have h2322 : mixedVector B (Sum.inr 2322) = Sparse.eval nodeValue2322 (mixedVector B) := by
    change mixedMoment B node2322 node2322Labels = _
    exact sound2322 B hB hF
  have h2326 : mixedVector B (Sum.inr 2326) = Sparse.eval nodeValue2326 (mixedVector B) := by
    change mixedMoment B node2326 node2326Labels = _
    exact sound2326 B hB hF
  have h2342 : mixedVector B (Sum.inr 2342) = Sparse.eval nodeValue2342 (mixedVector B) := by
    change mixedMoment B node2342 node2342Labels = _
    exact sound2342 B hB hF
  have h2489 : mixedVector B (Sum.inr 2489) = Sparse.eval nodeValue2489 (mixedVector B) := by
    change mixedMoment B node2489 node2489Labels = _
    exact sound2489 B hB hF
  have h3694 : mixedVector B (Sum.inr 3694) = Sparse.eval nodeValue3694 (mixedVector B) := by
    change mixedMoment B node3694 node3694Labels = _
    exact sound3694 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2219, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2322, h2326, h2342, h2489, h3694, h4091, reducedSource1830] using sourceEq2219 B hB

theorem rowSound1830 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1830 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1830, numericCheck1830, reducedZero1830 B hB hF, mul_zero]

theorem reducedZero1832 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1832 (mixedVector B) = 0 := by
  have h2151 : mixedVector B (Sum.inr 2151) = Sparse.eval nodeValue2151 (mixedVector B) := by
    change mixedMoment B node2151 node2151Labels = _
    exact sound2151 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2256 : mixedVector B (Sum.inr 2256) = Sparse.eval nodeValue2256 (mixedVector B) := by
    change mixedMoment B node2256 node2256Labels = _
    exact sound2256 B hB hF
  have h2258 : mixedVector B (Sum.inr 2258) = Sparse.eval nodeValue2258 (mixedVector B) := by
    change mixedMoment B node2258 node2258Labels = _
    exact sound2258 B hB hF
  have h2267 : mixedVector B (Sum.inr 2267) = Sparse.eval nodeValue2267 (mixedVector B) := by
    change mixedMoment B node2267 node2267Labels = _
    exact sound2267 B hB hF
  have h2286 : mixedVector B (Sum.inr 2286) = Sparse.eval nodeValue2286 (mixedVector B) := by
    change mixedMoment B node2286 node2286Labels = _
    exact sound2286 B hB hF
  have h2652 : mixedVector B (Sum.inr 2652) = Sparse.eval nodeValue2652 (mixedVector B) := by
    change mixedMoment B node2652 node2652Labels = _
    exact sound2652 B hB hF
  have h2657 : mixedVector B (Sum.inr 2657) = Sparse.eval nodeValue2657 (mixedVector B) := by
    change mixedMoment B node2657 node2657Labels = _
    exact sound2657 B hB hF
  have h2658 : mixedVector B (Sum.inr 2658) = Sparse.eval nodeValue2658 (mixedVector B) := by
    change mixedMoment B node2658 node2658Labels = _
    exact sound2658 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h3024 : mixedVector B (Sum.inr 3024) = Sparse.eval nodeValue3024 (mixedVector B) := by
    change mixedMoment B node3024 node3024Labels = _
    exact sound3024 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  simpa only [sourceForm2230, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2151, h2167, h2168, h2228, h2256, h2258, h2267, h2286, h2652, h2657, h2658, h2670, h2672, h2683, h2686, h2704, h2740, h2742, h3024, h3052, h3054, reducedSource1832] using sourceEq2230 B hB

theorem rowSound1832 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1832 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1832, numericCheck1832, reducedZero1832 B hB hF, mul_zero]

theorem reducedZero1834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1834 (mixedVector B) = 0 := by
  have h3265 : mixedVector B (Sum.inr 3265) = Sparse.eval nodeValue3265 (mixedVector B) := by
    change mixedMoment B node3265 node3265Labels = _
    exact sound3265 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3411 : mixedVector B (Sum.inr 3411) = Sparse.eval nodeValue3411 (mixedVector B) := by
    change mixedMoment B node3411 node3411Labels = _
    exact sound3411 B hB hF
  have h3412 : mixedVector B (Sum.inr 3412) = Sparse.eval nodeValue3412 (mixedVector B) := by
    change mixedMoment B node3412 node3412Labels = _
    exact sound3412 B hB hF
  have h3422 : mixedVector B (Sum.inr 3422) = Sparse.eval nodeValue3422 (mixedVector B) := by
    change mixedMoment B node3422 node3422Labels = _
    exact sound3422 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h3450 : mixedVector B (Sum.inr 3450) = Sparse.eval nodeValue3450 (mixedVector B) := by
    change mixedMoment B node3450 node3450Labels = _
    exact sound3450 B hB hF
  have h3457 : mixedVector B (Sum.inr 3457) = Sparse.eval nodeValue3457 (mixedVector B) := by
    change mixedMoment B node3457 node3457Labels = _
    exact sound3457 B hB hF
  have h3470 : mixedVector B (Sum.inr 3470) = Sparse.eval nodeValue3470 (mixedVector B) := by
    change mixedMoment B node3470 node3470Labels = _
    exact sound3470 B hB hF
  have h3471 : mixedVector B (Sum.inr 3471) = Sparse.eval nodeValue3471 (mixedVector B) := by
    change mixedMoment B node3471 node3471Labels = _
    exact sound3471 B hB hF
  have h3484 : mixedVector B (Sum.inr 3484) = Sparse.eval nodeValue3484 (mixedVector B) := by
    change mixedMoment B node3484 node3484Labels = _
    exact sound3484 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3775 : mixedVector B (Sum.inr 3775) = Sparse.eval nodeValue3775 (mixedVector B) := by
    change mixedMoment B node3775 node3775Labels = _
    exact sound3775 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2236, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3265, h3276, h3277, h3301, h3411, h3412, h3422, h3423, h3450, h3457, h3470, h3471, h3484, h3486, h3522, h3547, h3548, h3766, h3775, h3817, h4092, reducedSource1834] using sourceEq2236 B hB

theorem rowSound1834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1834 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1834, numericCheck1834, reducedZero1834 B hB hF, mul_zero]

theorem reducedZero1836 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1836 (mixedVector B) = 0 := by
  have h2379 : mixedVector B (Sum.inr 2379) = Sparse.eval nodeValue2379 (mixedVector B) := by
    change mixedMoment B node2379 node2379Labels = _
    exact sound2379 B hB hF
  have h3646 : mixedVector B (Sum.inr 3646) = Sparse.eval nodeValue3646 (mixedVector B) := by
    change mixedMoment B node3646 node3646Labels = _
    exact sound3646 B hB hF
  have h3718 : mixedVector B (Sum.inr 3718) = Sparse.eval nodeValue3718 (mixedVector B) := by
    change mixedMoment B node3718 node3718Labels = _
    exact sound3718 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h3759 : mixedVector B (Sum.inr 3759) = Sparse.eval nodeValue3759 (mixedVector B) := by
    change mixedMoment B node3759 node3759Labels = _
    exact sound3759 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2244, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2379, h3646, h3718, h3757, h3759, h4088, reducedSource1836] using sourceEq2244 B hB

theorem rowSound1836 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1836 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1836, numericCheck1836, reducedZero1836 B hB hF, mul_zero]

theorem reducedZero1837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1837 (mixedVector B) = 0 := by
  have h2388 : mixedVector B (Sum.inr 2388) = Sparse.eval nodeValue2388 (mixedVector B) := by
    change mixedMoment B node2388 node2388Labels = _
    exact sound2388 B hB hF
  have h3654 : mixedVector B (Sum.inr 3654) = Sparse.eval nodeValue3654 (mixedVector B) := by
    change mixedMoment B node3654 node3654Labels = _
    exact sound3654 B hB hF
  have h3681 : mixedVector B (Sum.inr 3681) = Sparse.eval nodeValue3681 (mixedVector B) := by
    change mixedMoment B node3681 node3681Labels = _
    exact sound3681 B hB hF
  have h3702 : mixedVector B (Sum.inr 3702) = Sparse.eval nodeValue3702 (mixedVector B) := by
    change mixedMoment B node3702 node3702Labels = _
    exact sound3702 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3767 : mixedVector B (Sum.inr 3767) = Sparse.eval nodeValue3767 (mixedVector B) := by
    change mixedMoment B node3767 node3767Labels = _
    exact sound3767 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2245, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2388, h3654, h3681, h3702, h3766, h3767, h4088, reducedSource1837] using sourceEq2245 B hB

theorem rowSound1837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1837 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1837, numericCheck1837, reducedZero1837 B hB hF, mul_zero]

theorem sourceRowsAt1824 : MixedData.sourceRows (1824 : Fin 2425) =
    MixedData.row1824 := by decide +kernel

theorem sourceRowsAt1825 : MixedData.sourceRows (1825 : Fin 2425) =
    MixedData.row1825 := by decide +kernel

theorem sourceRowsAt1826 : MixedData.sourceRows (1826 : Fin 2425) =
    MixedData.row1826 := by decide +kernel

theorem sourceRowsAt1827 : MixedData.sourceRows (1827 : Fin 2425) =
    MixedData.row1827 := by decide +kernel

theorem sourceRowsAt1828 : MixedData.sourceRows (1828 : Fin 2425) =
    MixedData.row1828 := by decide +kernel

theorem sourceRowsAt1829 : MixedData.sourceRows (1829 : Fin 2425) =
    MixedData.row1829 := by decide +kernel

theorem sourceRowsAt1830 : MixedData.sourceRows (1830 : Fin 2425) =
    MixedData.row1830 := by decide +kernel

theorem sourceRowsAt1831 : MixedData.sourceRows (1831 : Fin 2425) =
    MixedData.row1831 := by decide +kernel

theorem sourceRowsAt1832 : MixedData.sourceRows (1832 : Fin 2425) =
    MixedData.row1832 := by decide +kernel

theorem sourceRowsAt1833 : MixedData.sourceRows (1833 : Fin 2425) =
    MixedData.row1833 := by decide +kernel

theorem sourceRowsAt1834 : MixedData.sourceRows (1834 : Fin 2425) =
    MixedData.row1834 := by decide +kernel

theorem sourceRowsAt1835 : MixedData.sourceRows (1835 : Fin 2425) =
    MixedData.row1835 := by decide +kernel

theorem sourceRowsAt1836 : MixedData.sourceRows (1836 : Fin 2425) =
    MixedData.row1836 := by decide +kernel

theorem sourceRowsAt1837 : MixedData.sourceRows (1837 : Fin 2425) =
    MixedData.row1837 := by decide +kernel

theorem sourceRowsAt1838 : MixedData.sourceRows (1838 : Fin 2425) =
    MixedData.row1838 := by decide +kernel

theorem sourceRowsAt1839 : MixedData.sourceRows (1839 : Fin 2425) =
    MixedData.row1839 := by decide +kernel

theorem chunkSound114_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 114) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1824 ∨ k.val = 1825 ∨ k.val = 1826 ∨ k.val = 1827 ∨ k.val = 1828 ∨ k.val = 1829 ∨ k.val = 1830 ∨ k.val = 1831 ∨ k.val = 1832 ∨ k.val = 1833 ∨ k.val = 1834 ∨ k.val = 1835 ∨ k.val = 1836 ∨ k.val = 1837 ∨ k.val = 1838 ∨ k.val = 1839 := by omega
  rcases heq with h1824 | h1825 | h1826 | h1827 | h1828 | h1829 | h1830 | h1831 | h1832 | h1833 | h1834 | h1835 | h1836 | h1837 | h1838 | h1839
  · have he : k = (1824 : Fin 2425) := Fin.ext h1824
    subst k
    rw [sourceRowsAt1824]
    exact rowSound1824 B hB hF
  · have he : k = (1825 : Fin 2425) := Fin.ext h1825
    subst k
    rw [sourceRowsAt1825]
    exact rowSound1825_e B hB hF
  · have he : k = (1826 : Fin 2425) := Fin.ext h1826
    subst k
    rw [sourceRowsAt1826]
    exact rowSound1826_e B hB hF
  · have he : k = (1827 : Fin 2425) := Fin.ext h1827
    subst k
    rw [sourceRowsAt1827]
    exact rowSound1827 B hB hF
  · have he : k = (1828 : Fin 2425) := Fin.ext h1828
    subst k
    rw [sourceRowsAt1828]
    exact rowSound1828_e B hB hF
  · have he : k = (1829 : Fin 2425) := Fin.ext h1829
    subst k
    rw [sourceRowsAt1829]
    exact rowSound1829 B hB hF
  · have he : k = (1830 : Fin 2425) := Fin.ext h1830
    subst k
    rw [sourceRowsAt1830]
    exact rowSound1830 B hB hF
  · have he : k = (1831 : Fin 2425) := Fin.ext h1831
    subst k
    rw [sourceRowsAt1831]
    exact rowSound1831_e B hB hF
  · have he : k = (1832 : Fin 2425) := Fin.ext h1832
    subst k
    rw [sourceRowsAt1832]
    exact rowSound1832 B hB hF
  · have he : k = (1833 : Fin 2425) := Fin.ext h1833
    subst k
    rw [sourceRowsAt1833]
    exact rowSound1833_e B hB hF
  · have he : k = (1834 : Fin 2425) := Fin.ext h1834
    subst k
    rw [sourceRowsAt1834]
    exact rowSound1834 B hB hF
  · have he : k = (1835 : Fin 2425) := Fin.ext h1835
    subst k
    rw [sourceRowsAt1835]
    exact rowSound1835_e B hB hF
  · have he : k = (1836 : Fin 2425) := Fin.ext h1836
    subst k
    rw [sourceRowsAt1836]
    exact rowSound1836 B hB hF
  · have he : k = (1837 : Fin 2425) := Fin.ext h1837
    subst k
    rw [sourceRowsAt1837]
    exact rowSound1837 B hB hF
  · have he : k = (1838 : Fin 2425) := Fin.ext h1838
    subst k
    rw [sourceRowsAt1838]
    exact rowSound1838_e B hB hF
  · have he : k = (1839 : Fin 2425) := Fin.ext h1839
    subst k
    rw [sourceRowsAt1839]
    exact rowSound1839_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114_e_oai
