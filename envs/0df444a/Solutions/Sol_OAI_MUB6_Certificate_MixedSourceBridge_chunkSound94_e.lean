-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:41:46.404687+00:00
-- url     : https://prove2.me/submissions/96fbe60c-04d5-4fd8-86cf-67d59943fbd7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1505_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1507_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1508_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1510_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1511_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1513_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1514_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1516_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1517_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19936 raw19936Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19936 raw19936Labels = mixedMoment B raw19936step0 raw19936step0Labels := by
      have hz : ∀ j, raw19936 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19936step0 = (fun i j => raw19936 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19936step0 raw19936; decide +kernel
      have hl : raw19936step0Labels = raw19936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19936 raw19936Labels permutation520 hz
    mixedMoment B raw19936step0 raw19936step0Labels = mixedMoment B raw19936step1 raw19936step1Labels := by
      have hz : ∀ j, raw19936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19936step1 = (fun i j => raw19936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19936step1 raw19936step0; decide +kernel
      have hl : raw19936step1Labels = raw19936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19936step0 raw19936step0Labels permutation80 hz
    mixedMoment B raw19936step1 raw19936step1Labels = mixedMoment B raw19936step2 raw19936step2Labels := by
      have hz : ∀ j, raw19936step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19936step2 = (fun i j => raw19936step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19936step2 raw19936step1; decide +kernel
      have hl : raw19936step2Labels = raw19936step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19936step1 raw19936step1Labels permutation14 hz
    mixedMoment B raw19936step2 raw19936step2Labels = mixedMoment B raw19936step3 raw19936step3Labels := by
      have ha : raw19936step3 = (fun i j => raw19936step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19936step3 raw19936step2; decide +kernel
      have hl : raw19936step3Labels = raw19936step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19936step2 raw19936step2Labels permutation2 permutation7
    mixedMoment B raw19936step3 raw19936step3Labels = mixedMoment B raw19936step4 raw19936step4Labels := by
      have ha : raw19936step4 = -raw19936step3 := by apply Matrix.ext; change ∀ i j, raw19936step4 i j = -(raw19936step3 i j); unfold raw19936step4 raw19936step3; decide +kernel
      have hl : raw19936step4Labels = raw19936step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19936step4 raw19936step4Labels = mixedMoment B raw19936step5 raw19936step5Labels := by
      have ha : raw19936step5 = raw19936step4 := by apply Matrix.ext; unfold raw19936step5 raw19936step4; decide +kernel
      have hl : raw19936step4Labels = labelEmbedding1 ∘ raw19936step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19936step4 raw19936step4Labels raw19936step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical21860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21860 raw21860Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw21860 raw21860Labels = mixedMoment B raw21860step0 raw21860step0Labels := by
      have hz : ∀ j, raw21860 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21860step0 = (fun i j => raw21860 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21860step0 raw21860; decide +kernel
      have hl : raw21860step0Labels = raw21860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21860 raw21860Labels permutation434 hz
    mixedMoment B raw21860step0 raw21860step0Labels = mixedMoment B raw21860step1 raw21860step1Labels := by
      have hz : ∀ j, raw21860step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21860step1 = (fun i j => raw21860step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21860step1 raw21860step0; decide +kernel
      have hl : raw21860step1Labels = raw21860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21860step0 raw21860step0Labels permutation80 hz
    mixedMoment B raw21860step1 raw21860step1Labels = mixedMoment B raw21860step2 raw21860step2Labels := by
      have ha : raw21860step2 = (fun i j => raw21860step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21860step2 raw21860step1; decide +kernel
      have hl : raw21860step2Labels = raw21860step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21860step1 raw21860step1Labels permutation8 permutation7
    mixedMoment B raw21860step2 raw21860step2Labels = mixedMoment B raw21860step3 raw21860step3Labels := by
      have ha : raw21860step3 = -raw21860step2 := by apply Matrix.ext; change ∀ i j, raw21860step3 i j = -(raw21860step2 i j); unfold raw21860step3 raw21860step2; decide +kernel
      have hl : raw21860step3Labels = raw21860step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21860step3 raw21860step3Labels = mixedMoment B raw21860step4 raw21860step4Labels := by
      have ha : raw21860step4 = raw21860step3 := by apply Matrix.ext; unfold raw21860step4 raw21860step3; decide +kernel
      have hl : raw21860step3Labels = labelEmbedding1 ∘ raw21860step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21860step3 raw21860step3Labels raw21860step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical21864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21864 raw21864Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw21864 raw21864Labels = mixedMoment B raw21864step0 raw21864step0Labels := by
      have hz : ∀ j, raw21864 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21864step0 = (fun i j => raw21864 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21864step0 raw21864; decide +kernel
      have hl : raw21864step0Labels = raw21864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21864 raw21864Labels permutation434 hz
    mixedMoment B raw21864step0 raw21864step0Labels = mixedMoment B raw21864step1 raw21864step1Labels := by
      have hz : ∀ j, raw21864step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21864step1 = (fun i j => raw21864step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21864step1 raw21864step0; decide +kernel
      have hl : raw21864step1Labels = raw21864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21864step0 raw21864step0Labels permutation56 hz
    mixedMoment B raw21864step1 raw21864step1Labels = mixedMoment B raw21864step2 raw21864step2Labels := by
      have ha : raw21864step2 = (fun i j => raw21864step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21864step2 raw21864step1; decide +kernel
      have hl : raw21864step2Labels = raw21864step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21864step1 raw21864step1Labels permutation8 permutation7
    mixedMoment B raw21864step2 raw21864step2Labels = mixedMoment B raw21864step3 raw21864step3Labels := by
      have ha : raw21864step3 = -raw21864step2 := by apply Matrix.ext; change ∀ i j, raw21864step3 i j = -(raw21864step2 i j); unfold raw21864step3 raw21864step2; decide +kernel
      have hl : raw21864step3Labels = raw21864step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21864step3 raw21864step3Labels = mixedMoment B raw21864step4 raw21864step4Labels := by
      have ha : raw21864step4 = raw21864step3 := by apply Matrix.ext; unfold raw21864step4 raw21864step3; decide +kernel
      have hl : raw21864step3Labels = labelEmbedding1 ∘ raw21864step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21864step3 raw21864step3Labels raw21864step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical21865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21865 raw21865Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw21865 raw21865Labels = mixedMoment B raw21865step0 raw21865step0Labels := by
      have hz : ∀ j, raw21865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21865step0 = (fun i j => raw21865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21865step0 raw21865; decide +kernel
      have hl : raw21865step0Labels = raw21865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21865 raw21865Labels permutation346 hz
    mixedMoment B raw21865step0 raw21865step0Labels = mixedMoment B raw21865step1 raw21865step1Labels := by
      have hz : ∀ j, raw21865step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21865step1 = (fun i j => raw21865step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21865step1 raw21865step0; decide +kernel
      have hl : raw21865step1Labels = raw21865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21865step0 raw21865step0Labels permutation56 hz
    mixedMoment B raw21865step1 raw21865step1Labels = mixedMoment B raw21865step2 raw21865step2Labels := by
      have ha : raw21865step2 = (fun i j => raw21865step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21865step2 raw21865step1; decide +kernel
      have hl : raw21865step2Labels = raw21865step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21865step1 raw21865step1Labels permutation8 permutation7
    mixedMoment B raw21865step2 raw21865step2Labels = mixedMoment B raw21865step3 raw21865step3Labels := by
      have ha : raw21865step3 = -raw21865step2 := by apply Matrix.ext; change ∀ i j, raw21865step3 i j = -(raw21865step2 i j); unfold raw21865step3 raw21865step2; decide +kernel
      have hl : raw21865step3Labels = raw21865step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21865step3 raw21865step3Labels = mixedMoment B raw21865step4 raw21865step4Labels := by
      have ha : raw21865step4 = raw21865step3 := by apply Matrix.ext; unfold raw21865step4 raw21865step3; decide +kernel
      have hl : raw21865step3Labels = labelEmbedding1 ∘ raw21865step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21865step3 raw21865step3Labels raw21865step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1509 node1509Labels := by rfl

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

theorem canonical21867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21867 raw21867Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21867 raw21867Labels = mixedMoment B raw21867step0 raw21867step0Labels := by
      have hz : ∀ j, raw21867 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21867step0 = (fun i j => raw21867 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21867step0 raw21867; decide +kernel
      have hl : raw21867step0Labels = raw21867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21867 raw21867Labels permutation265 hz
    mixedMoment B raw21867step0 raw21867step0Labels = mixedMoment B raw21867step1 raw21867step1Labels := by
      have ha : raw21867step1 = (fun i j => raw21867step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21867step1 raw21867step0; decide +kernel
      have hl : raw21867step1Labels = raw21867step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21867step0 raw21867step0Labels permutation32 permutation7
    mixedMoment B raw21867step1 raw21867step1Labels = mixedMoment B raw21867step2 raw21867step2Labels := by
      have ha : raw21867step2 = -raw21867step1 := by apply Matrix.ext; change ∀ i j, raw21867step2 i j = -(raw21867step1 i j); unfold raw21867step2 raw21867step1; decide +kernel
      have hl : raw21867step2Labels = raw21867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21867step2 raw21867step2Labels = mixedMoment B raw21867step3 raw21867step3Labels := by
      have ha : raw21867step3 = raw21867step2 := by apply Matrix.ext; unfold raw21867step3 raw21867step2; decide +kernel
      have hl : raw21867step2Labels = labelEmbedding1 ∘ raw21867step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21867step2 raw21867step2Labels raw21867step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

theorem canonical21873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21873 raw21873Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw21873 raw21873Labels = mixedMoment B raw21873step0 raw21873step0Labels := by
      have hz : ∀ j, raw21873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21873step0 = (fun i j => raw21873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21873step0 raw21873; decide +kernel
      have hl : raw21873step0Labels = raw21873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21873 raw21873Labels permutation434 hz
    mixedMoment B raw21873step0 raw21873step0Labels = mixedMoment B raw21873step1 raw21873step1Labels := by
      have hz : ∀ j, raw21873step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21873step1 = (fun i j => raw21873step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21873step1 raw21873step0; decide +kernel
      have hl : raw21873step1Labels = raw21873step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21873step0 raw21873step0Labels permutation80 hz
    mixedMoment B raw21873step1 raw21873step1Labels = mixedMoment B raw21873step2 raw21873step2Labels := by
      have hz : ∀ j, raw21873step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21873step2 = (fun i j => raw21873step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21873step2 raw21873step1; decide +kernel
      have hl : raw21873step2Labels = raw21873step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21873step1 raw21873step1Labels permutation14 hz
    mixedMoment B raw21873step2 raw21873step2Labels = mixedMoment B raw21873step3 raw21873step3Labels := by
      have ha : raw21873step3 = (fun i j => raw21873step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21873step3 raw21873step2; decide +kernel
      have hl : raw21873step3Labels = raw21873step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21873step2 raw21873step2Labels permutation2 permutation7
    mixedMoment B raw21873step3 raw21873step3Labels = mixedMoment B raw21873step4 raw21873step4Labels := by
      have ha : raw21873step4 = -raw21873step3 := by apply Matrix.ext; change ∀ i j, raw21873step4 i j = -(raw21873step3 i j); unfold raw21873step4 raw21873step3; decide +kernel
      have hl : raw21873step4Labels = raw21873step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21873step4 raw21873step4Labels = mixedMoment B raw21873step5 raw21873step5Labels := by
      have ha : raw21873step5 = raw21873step4 := by apply Matrix.ext; unfold raw21873step5 raw21873step4; decide +kernel
      have hl : raw21873step4Labels = labelEmbedding1 ∘ raw21873step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21873step4 raw21873step4Labels raw21873step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1741 node1741Labels := by rfl

theorem canonical21878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21878 raw21878Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw21878 raw21878Labels = mixedMoment B raw21878step0 raw21878step0Labels := by
      have hz : ∀ j, raw21878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21878step0 = (fun i j => raw21878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21878step0 raw21878; decide +kernel
      have hl : raw21878step0Labels = raw21878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21878 raw21878Labels permutation346 hz
    mixedMoment B raw21878step0 raw21878step0Labels = mixedMoment B raw21878step1 raw21878step1Labels := by
      have hz : ∀ j, raw21878step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21878step1 = (fun i j => raw21878step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21878step1 raw21878step0; decide +kernel
      have hl : raw21878step1Labels = raw21878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21878step0 raw21878step0Labels permutation56 hz
    _ = mixedMoment B node602 node602Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical199
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25585 raw25585Labels = mixedMoment B node1076 node1076Labels := by
  calc
    mixedMoment B raw25585 raw25585Labels = mixedMoment B raw25585step0 raw25585step0Labels := by
      have hz : ∀ j, raw25585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25585step0 = (fun i j => raw25585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25585step0 raw25585; decide +kernel
      have hl : raw25585step0Labels = raw25585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25585 raw25585Labels permutation346 hz
    mixedMoment B raw25585step0 raw25585step0Labels = mixedMoment B raw25585step1 raw25585step1Labels := by
      have hz : ∀ j, raw25585step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25585step1 = (fun i j => raw25585step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25585step1 raw25585step0; decide +kernel
      have hl : raw25585step1Labels = raw25585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25585step0 raw25585step0Labels permutation56 hz
    mixedMoment B raw25585step1 raw25585step1Labels = mixedMoment B raw25585step2 raw25585step2Labels := by
      have ha : raw25585step2 = (fun i j => raw25585step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25585step2 raw25585step1; decide +kernel
      have hl : raw25585step2Labels = raw25585step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25585step1 raw25585step1Labels permutation10 permutation2
    _ = mixedMoment B node1076 node1076Labels := by rfl

theorem canonical25586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25586 raw25586Labels = mixedMoment B node2049 node2049Labels := by
  calc
    mixedMoment B raw25586 raw25586Labels = mixedMoment B raw25586step0 raw25586step0Labels := by
      have hz : ∀ j, raw25586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25586step0 = (fun i j => raw25586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25586step0 raw25586; decide +kernel
      have hl : raw25586step0Labels = raw25586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25586 raw25586Labels permutation346 hz
    mixedMoment B raw25586step0 raw25586step0Labels = mixedMoment B raw25586step1 raw25586step1Labels := by
      have ha : raw25586step1 = (fun i j => raw25586step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25586step1 raw25586step0; decide +kernel
      have hl : raw25586step1Labels = raw25586step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25586step0 raw25586step0Labels permutation34 permutation2
    _ = mixedMoment B node2049 node2049Labels := by rfl

theorem canonical25587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25587 raw25587Labels = mixedMoment B node2049 node2049Labels := by
  calc
    mixedMoment B raw25587 raw25587Labels = mixedMoment B raw25587step0 raw25587step0Labels := by
      have hz : ∀ j, raw25587 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25587step0 = (fun i j => raw25587 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25587step0 raw25587; decide +kernel
      have hl : raw25587step0Labels = raw25587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25587 raw25587Labels permutation265 hz
    mixedMoment B raw25587step0 raw25587step0Labels = mixedMoment B raw25587step1 raw25587step1Labels := by
      have ha : raw25587step1 = (fun i j => raw25587step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25587step1 raw25587step0; decide +kernel
      have hl : raw25587step1Labels = raw25587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25587step0 raw25587step0Labels permutation34 permutation2
    _ = mixedMoment B node2049 node2049Labels := by rfl

theorem canonical25588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25588 raw25588Labels = mixedMoment B node2282 node2282Labels := by
  calc
    mixedMoment B raw25588 raw25588Labels = mixedMoment B raw25588step0 raw25588step0Labels := by
      have hz : ∀ j, raw25588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25588step0 = (fun i j => raw25588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25588step0 raw25588; decide +kernel
      have hl : raw25588step0Labels = raw25588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25588 raw25588Labels permutation346 hz
    mixedMoment B raw25588step0 raw25588step0Labels = mixedMoment B raw25588step1 raw25588step1Labels := by
      have hz : ∀ j, raw25588step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25588step1 = (fun i j => raw25588step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25588step1 raw25588step0; decide +kernel
      have hl : raw25588step1Labels = raw25588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25588step0 raw25588step0Labels permutation56 hz
    _ = mixedMoment B node2282 node2282Labels := by rfl

theorem canonical25589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25589 raw25589Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw25589 raw25589Labels = mixedMoment B raw25589step0 raw25589step0Labels := by
      have hz : ∀ j, raw25589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25589step0 = (fun i j => raw25589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25589step0 raw25589; decide +kernel
      have hl : raw25589step0Labels = raw25589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25589 raw25589Labels permutation346 hz
    mixedMoment B raw25589step0 raw25589step0Labels = mixedMoment B raw25589step1 raw25589step1Labels := by
      have hz : ∀ j, raw25589step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25589step1 = (fun i j => raw25589step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25589step1 raw25589step0; decide +kernel
      have hl : raw25589step1Labels = raw25589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25589step0 raw25589step0Labels permutation56 hz
    mixedMoment B raw25589step1 raw25589step1Labels = mixedMoment B raw25589step2 raw25589step2Labels := by
      have ha : raw25589step2 = (fun i j => raw25589step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25589step2 raw25589step1; decide +kernel
      have hl : raw25589step2Labels = raw25589step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25589step1 raw25589step1Labels permutation10 permutation2
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical25590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25590 raw25590Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw25590 raw25590Labels = mixedMoment B raw25590step0 raw25590step0Labels := by
      have hz : ∀ j, raw25590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25590step0 = (fun i j => raw25590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25590step0 raw25590; decide +kernel
      have hl : raw25590step0Labels = raw25590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25590 raw25590Labels permutation346 hz
    mixedMoment B raw25590step0 raw25590step0Labels = mixedMoment B raw25590step1 raw25590step1Labels := by
      have hz : ∀ j, raw25590step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25590step1 = (fun i j => raw25590step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25590step1 raw25590step0; decide +kernel
      have hl : raw25590step1Labels = raw25590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25590step0 raw25590step0Labels permutation56 hz
    mixedMoment B raw25590step1 raw25590step1Labels = mixedMoment B raw25590step2 raw25590step2Labels := by
      have ha : raw25590step2 = (fun i j => raw25590step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25590step2 raw25590step1; decide +kernel
      have hl : raw25590step2Labels = raw25590step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25590step1 raw25590step1Labels permutation11 permutation2
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical25591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25591 raw25591Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw25591 raw25591Labels = mixedMoment B raw25591step0 raw25591step0Labels := by
      have hz : ∀ j, raw25591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25591step0 = (fun i j => raw25591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25591step0 raw25591; decide +kernel
      have hl : raw25591step0Labels = raw25591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25591 raw25591Labels permutation346 hz
    mixedMoment B raw25591step0 raw25591step0Labels = mixedMoment B raw25591step1 raw25591step1Labels := by
      have hz : ∀ j, raw25591step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25591step1 = (fun i j => raw25591step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25591step1 raw25591step0; decide +kernel
      have hl : raw25591step1Labels = raw25591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25591step0 raw25591step0Labels permutation56 hz
    mixedMoment B raw25591step1 raw25591step1Labels = mixedMoment B raw25591step2 raw25591step2Labels := by
      have ha : raw25591step2 = (fun i j => raw25591step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25591step2 raw25591step1; decide +kernel
      have hl : raw25591step2Labels = raw25591step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25591step1 raw25591step1Labels permutation11 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical200
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25633 raw25633Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw25633 raw25633Labels = mixedMoment B raw25633step0 raw25633step0Labels := by
      have hz : ∀ j, raw25633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25633step0 = (fun i j => raw25633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25633step0 raw25633; decide +kernel
      have hl : raw25633step0Labels = raw25633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25633 raw25633Labels permutation346 hz
    mixedMoment B raw25633step0 raw25633step0Labels = mixedMoment B raw25633step1 raw25633step1Labels := by
      have ha : raw25633step1 = (fun i j => raw25633step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25633step1 raw25633step0; decide +kernel
      have hl : raw25633step1Labels = raw25633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25633step0 raw25633step0Labels permutation37 permutation7
    mixedMoment B raw25633step1 raw25633step1Labels = mixedMoment B raw25633step2 raw25633step2Labels := by
      have ha : raw25633step2 = -raw25633step1 := by apply Matrix.ext; change ∀ i j, raw25633step2 i j = -(raw25633step1 i j); unfold raw25633step2 raw25633step1; decide +kernel
      have hl : raw25633step2Labels = raw25633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25633step2 raw25633step2Labels = mixedMoment B raw25633step3 raw25633step3Labels := by
      have ha : raw25633step3 = raw25633step2 := by apply Matrix.ext; unfold raw25633step3 raw25633step2; decide +kernel
      have hl : raw25633step2Labels = labelEmbedding1 ∘ raw25633step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25633step2 raw25633step2Labels raw25633step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical25634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25634 raw25634Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw25634 raw25634Labels = mixedMoment B raw25634step0 raw25634step0Labels := by
      have hz : ∀ j, raw25634 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25634step0 = (fun i j => raw25634 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25634step0 raw25634; decide +kernel
      have hl : raw25634step0Labels = raw25634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25634 raw25634Labels permutation265 hz
    mixedMoment B raw25634step0 raw25634step0Labels = mixedMoment B raw25634step1 raw25634step1Labels := by
      have ha : raw25634step1 = (fun i j => raw25634step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25634step1 raw25634step0; decide +kernel
      have hl : raw25634step1Labels = raw25634step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25634step0 raw25634step0Labels permutation37 permutation7
    mixedMoment B raw25634step1 raw25634step1Labels = mixedMoment B raw25634step2 raw25634step2Labels := by
      have ha : raw25634step2 = -raw25634step1 := by apply Matrix.ext; change ∀ i j, raw25634step2 i j = -(raw25634step1 i j); unfold raw25634step2 raw25634step1; decide +kernel
      have hl : raw25634step2Labels = raw25634step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25634step2 raw25634step2Labels = mixedMoment B raw25634step3 raw25634step3Labels := by
      have ha : raw25634step3 = raw25634step2 := by apply Matrix.ext; unfold raw25634step3 raw25634step2; decide +kernel
      have hl : raw25634step2Labels = labelEmbedding1 ∘ raw25634step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25634step2 raw25634step2Labels raw25634step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical25635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25635 raw25635Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw25635 raw25635Labels = mixedMoment B raw25635step0 raw25635step0Labels := by
      have hz : ∀ j, raw25635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25635step0 = (fun i j => raw25635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25635step0 raw25635; decide +kernel
      have hl : raw25635step0Labels = raw25635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25635 raw25635Labels permutation346 hz
    mixedMoment B raw25635step0 raw25635step0Labels = mixedMoment B raw25635step1 raw25635step1Labels := by
      have hz : ∀ j, raw25635step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25635step1 = (fun i j => raw25635step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25635step1 raw25635step0; decide +kernel
      have hl : raw25635step1Labels = raw25635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25635step0 raw25635step0Labels permutation56 hz
    mixedMoment B raw25635step1 raw25635step1Labels = mixedMoment B raw25635step2 raw25635step2Labels := by
      have ha : raw25635step2 = (fun i j => raw25635step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25635step2 raw25635step1; decide +kernel
      have hl : raw25635step2Labels = raw25635step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25635step1 raw25635step1Labels permutation13 permutation7
    mixedMoment B raw25635step2 raw25635step2Labels = mixedMoment B raw25635step3 raw25635step3Labels := by
      have ha : raw25635step3 = -raw25635step2 := by apply Matrix.ext; change ∀ i j, raw25635step3 i j = -(raw25635step2 i j); unfold raw25635step3 raw25635step2; decide +kernel
      have hl : raw25635step3Labels = raw25635step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25635step3 raw25635step3Labels = mixedMoment B raw25635step4 raw25635step4Labels := by
      have ha : raw25635step4 = raw25635step3 := by apply Matrix.ext; unfold raw25635step4 raw25635step3; decide +kernel
      have hl : raw25635step3Labels = labelEmbedding1 ∘ raw25635step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25635step3 raw25635step3Labels raw25635step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical25636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25636 raw25636Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw25636 raw25636Labels = mixedMoment B raw25636step0 raw25636step0Labels := by
      have hz : ∀ j, raw25636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25636step0 = (fun i j => raw25636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25636step0 raw25636; decide +kernel
      have hl : raw25636step0Labels = raw25636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25636 raw25636Labels permutation346 hz
    mixedMoment B raw25636step0 raw25636step0Labels = mixedMoment B raw25636step1 raw25636step1Labels := by
      have hz : ∀ j, raw25636step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25636step1 = (fun i j => raw25636step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25636step1 raw25636step0; decide +kernel
      have hl : raw25636step1Labels = raw25636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25636step0 raw25636step0Labels permutation56 hz
    mixedMoment B raw25636step1 raw25636step1Labels = mixedMoment B raw25636step2 raw25636step2Labels := by
      have ha : raw25636step2 = (fun i j => raw25636step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25636step2 raw25636step1; decide +kernel
      have hl : raw25636step2Labels = raw25636step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25636step1 raw25636step1Labels permutation13 permutation7
    mixedMoment B raw25636step2 raw25636step2Labels = mixedMoment B raw25636step3 raw25636step3Labels := by
      have ha : raw25636step3 = -raw25636step2 := by apply Matrix.ext; change ∀ i j, raw25636step3 i j = -(raw25636step2 i j); unfold raw25636step3 raw25636step2; decide +kernel
      have hl : raw25636step3Labels = raw25636step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25636step3 raw25636step3Labels = mixedMoment B raw25636step4 raw25636step4Labels := by
      have ha : raw25636step4 = raw25636step3 := by apply Matrix.ext; unfold raw25636step4 raw25636step3; decide +kernel
      have hl : raw25636step3Labels = labelEmbedding1 ∘ raw25636step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25636step3 raw25636step3Labels raw25636step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical25637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25637 raw25637Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw25637 raw25637Labels = mixedMoment B raw25637step0 raw25637step0Labels := by
      have hz : ∀ j, raw25637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25637step0 = (fun i j => raw25637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25637step0 raw25637; decide +kernel
      have hl : raw25637step0Labels = raw25637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25637 raw25637Labels permutation346 hz
    mixedMoment B raw25637step0 raw25637step0Labels = mixedMoment B raw25637step1 raw25637step1Labels := by
      have hz : ∀ j, raw25637step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25637step1 = (fun i j => raw25637step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25637step1 raw25637step0; decide +kernel
      have hl : raw25637step1Labels = raw25637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25637step0 raw25637step0Labels permutation56 hz
    mixedMoment B raw25637step1 raw25637step1Labels = mixedMoment B raw25637step2 raw25637step2Labels := by
      have ha : raw25637step2 = (fun i j => raw25637step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25637step2 raw25637step1; decide +kernel
      have hl : raw25637step2Labels = raw25637step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25637step1 raw25637step1Labels permutation13 permutation7
    mixedMoment B raw25637step2 raw25637step2Labels = mixedMoment B raw25637step3 raw25637step3Labels := by
      have ha : raw25637step3 = -raw25637step2 := by apply Matrix.ext; change ∀ i j, raw25637step3 i j = -(raw25637step2 i j); unfold raw25637step3 raw25637step2; decide +kernel
      have hl : raw25637step3Labels = raw25637step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25637step3 raw25637step3Labels = mixedMoment B raw25637step4 raw25637step4Labels := by
      have ha : raw25637step4 = raw25637step3 := by apply Matrix.ext; unfold raw25637step4 raw25637step3; decide +kernel
      have hl : raw25637step3Labels = labelEmbedding1 ∘ raw25637step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25637step3 raw25637step3Labels raw25637step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2265 node2265Labels := by rfl

theorem canonical25638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25638 raw25638Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw25638 raw25638Labels = mixedMoment B raw25638step0 raw25638step0Labels := by
      have hz : ∀ j, raw25638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25638step0 = (fun i j => raw25638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25638step0 raw25638; decide +kernel
      have hl : raw25638step0Labels = raw25638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25638 raw25638Labels permutation346 hz
    mixedMoment B raw25638step0 raw25638step0Labels = mixedMoment B raw25638step1 raw25638step1Labels := by
      have ha : raw25638step1 = (fun i j => raw25638step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25638step1 raw25638step0; decide +kernel
      have hl : raw25638step1Labels = raw25638step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25638step0 raw25638step0Labels permutation37 permutation7
    mixedMoment B raw25638step1 raw25638step1Labels = mixedMoment B raw25638step2 raw25638step2Labels := by
      have ha : raw25638step2 = -raw25638step1 := by apply Matrix.ext; change ∀ i j, raw25638step2 i j = -(raw25638step1 i j); unfold raw25638step2 raw25638step1; decide +kernel
      have hl : raw25638step2Labels = raw25638step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25638step2 raw25638step2Labels = mixedMoment B raw25638step3 raw25638step3Labels := by
      have ha : raw25638step3 = raw25638step2 := by apply Matrix.ext; unfold raw25638step3 raw25638step2; decide +kernel
      have hl : raw25638step2Labels = labelEmbedding1 ∘ raw25638step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25638step2 raw25638step2Labels raw25638step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

theorem canonical25639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25639 raw25639Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw25639 raw25639Labels = mixedMoment B raw25639step0 raw25639step0Labels := by
      have ha : raw25639step0 = (fun i j => raw25639 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25639step0 raw25639; decide +kernel
      have hl : raw25639step0Labels = raw25639Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25639 raw25639Labels permutation181 permutation7
    mixedMoment B raw25639step0 raw25639step0Labels = mixedMoment B raw25639step1 raw25639step1Labels := by
      have ha : raw25639step1 = -raw25639step0 := by apply Matrix.ext; change ∀ i j, raw25639step1 i j = -(raw25639step0 i j); unfold raw25639step1 raw25639step0; decide +kernel
      have hl : raw25639step1Labels = raw25639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25639step1 raw25639step1Labels = mixedMoment B raw25639step2 raw25639step2Labels := by
      have ha : raw25639step2 = raw25639step1 := by apply Matrix.ext; unfold raw25639step2 raw25639step1; decide +kernel
      have hl : raw25639step1Labels = labelEmbedding1 ∘ raw25639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25639step1 raw25639step1Labels raw25639step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

theorem canonical25640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25640 raw25640Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw25640 raw25640Labels = mixedMoment B raw25640step0 raw25640step0Labels := by
      have hz : ∀ j, raw25640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25640step0 = (fun i j => raw25640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25640step0 raw25640; decide +kernel
      have hl : raw25640step0Labels = raw25640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25640 raw25640Labels permutation346 hz
    mixedMoment B raw25640step0 raw25640step0Labels = mixedMoment B raw25640step1 raw25640step1Labels := by
      have ha : raw25640step1 = (fun i j => raw25640step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25640step1 raw25640step0; decide +kernel
      have hl : raw25640step1Labels = raw25640step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25640step0 raw25640step0Labels permutation37 permutation7
    mixedMoment B raw25640step1 raw25640step1Labels = mixedMoment B raw25640step2 raw25640step2Labels := by
      have ha : raw25640step2 = -raw25640step1 := by apply Matrix.ext; change ∀ i j, raw25640step2 i j = -(raw25640step1 i j); unfold raw25640step2 raw25640step1; decide +kernel
      have hl : raw25640step2Labels = raw25640step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25640step2 raw25640step2Labels = mixedMoment B raw25640step3 raw25640step3Labels := by
      have ha : raw25640step3 = raw25640step2 := by apply Matrix.ext; unfold raw25640step3 raw25640step2; decide +kernel
      have hl : raw25640step2Labels = labelEmbedding1 ∘ raw25640step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25640step2 raw25640step2Labels raw25640step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

theorem canonical25641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25641 raw25641Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw25641 raw25641Labels = mixedMoment B raw25641step0 raw25641step0Labels := by
      have hz : ∀ j, raw25641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25641step0 = (fun i j => raw25641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25641step0 raw25641; decide +kernel
      have hl : raw25641step0Labels = raw25641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25641 raw25641Labels permutation346 hz
    mixedMoment B raw25641step0 raw25641step0Labels = mixedMoment B raw25641step1 raw25641step1Labels := by
      have ha : raw25641step1 = (fun i j => raw25641step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25641step1 raw25641step0; decide +kernel
      have hl : raw25641step1Labels = raw25641step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25641step0 raw25641step0Labels permutation37 permutation7
    mixedMoment B raw25641step1 raw25641step1Labels = mixedMoment B raw25641step2 raw25641step2Labels := by
      have ha : raw25641step2 = -raw25641step1 := by apply Matrix.ext; change ∀ i j, raw25641step2 i j = -(raw25641step1 i j); unfold raw25641step2 raw25641step1; decide +kernel
      have hl : raw25641step2Labels = raw25641step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25641step2 raw25641step2Labels = mixedMoment B raw25641step3 raw25641step3Labels := by
      have ha : raw25641step3 = raw25641step2 := by apply Matrix.ext; unfold raw25641step3 raw25641step2; decide +kernel
      have hl : raw25641step2Labels = labelEmbedding1 ∘ raw25641step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25641step2 raw25641step2Labels raw25641step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical25642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25642 raw25642Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw25642 raw25642Labels = mixedMoment B raw25642step0 raw25642step0Labels := by
      have hz : ∀ j, raw25642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25642step0 = (fun i j => raw25642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25642step0 raw25642; decide +kernel
      have hl : raw25642step0Labels = raw25642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25642 raw25642Labels permutation346 hz
    mixedMoment B raw25642step0 raw25642step0Labels = mixedMoment B raw25642step1 raw25642step1Labels := by
      have ha : raw25642step1 = (fun i j => raw25642step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25642step1 raw25642step0; decide +kernel
      have hl : raw25642step1Labels = raw25642step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25642step0 raw25642step0Labels permutation37 permutation7
    mixedMoment B raw25642step1 raw25642step1Labels = mixedMoment B raw25642step2 raw25642step2Labels := by
      have ha : raw25642step2 = -raw25642step1 := by apply Matrix.ext; change ∀ i j, raw25642step2 i j = -(raw25642step1 i j); unfold raw25642step2 raw25642step1; decide +kernel
      have hl : raw25642step2Labels = raw25642step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25642step2 raw25642step2Labels = mixedMoment B raw25642step3 raw25642step3Labels := by
      have ha : raw25642step3 = raw25642step2 := by apply Matrix.ext; unfold raw25642step3 raw25642step2; decide +kernel
      have hl : raw25642step2Labels = labelEmbedding1 ∘ raw25642step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25642step2 raw25642step2Labels raw25642step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical25643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25643 raw25643Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw25643 raw25643Labels = mixedMoment B raw25643step0 raw25643step0Labels := by
      have hz : ∀ j, raw25643 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25643step0 = (fun i j => raw25643 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25643step0 raw25643; decide +kernel
      have hl : raw25643step0Labels = raw25643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25643 raw25643Labels permutation265 hz
    mixedMoment B raw25643step0 raw25643step0Labels = mixedMoment B raw25643step1 raw25643step1Labels := by
      have ha : raw25643step1 = (fun i j => raw25643step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25643step1 raw25643step0; decide +kernel
      have hl : raw25643step1Labels = raw25643step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25643step0 raw25643step0Labels permutation37 permutation7
    mixedMoment B raw25643step1 raw25643step1Labels = mixedMoment B raw25643step2 raw25643step2Labels := by
      have ha : raw25643step2 = -raw25643step1 := by apply Matrix.ext; change ∀ i j, raw25643step2 i j = -(raw25643step1 i j); unfold raw25643step2 raw25643step1; decide +kernel
      have hl : raw25643step2Labels = raw25643step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25643step2 raw25643step2Labels = mixedMoment B raw25643step3 raw25643step3Labels := by
      have ha : raw25643step3 = raw25643step2 := by apply Matrix.ext; unfold raw25643step3 raw25643step2; decide +kernel
      have hl : raw25643step2Labels = labelEmbedding1 ∘ raw25643step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25643step2 raw25643step2Labels raw25643step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

theorem canonical25644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25644 raw25644Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw25644 raw25644Labels = mixedMoment B raw25644step0 raw25644step0Labels := by
      have ha : raw25644step0 = (fun i j => raw25644 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25644step0 raw25644; decide +kernel
      have hl : raw25644step0Labels = raw25644Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25644 raw25644Labels permutation157 permutation7
    mixedMoment B raw25644step0 raw25644step0Labels = mixedMoment B raw25644step1 raw25644step1Labels := by
      have ha : raw25644step1 = -raw25644step0 := by apply Matrix.ext; change ∀ i j, raw25644step1 i j = -(raw25644step0 i j); unfold raw25644step1 raw25644step0; decide +kernel
      have hl : raw25644step1Labels = raw25644step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25644step1 raw25644step1Labels = mixedMoment B raw25644step2 raw25644step2Labels := by
      have ha : raw25644step2 = raw25644step1 := by apply Matrix.ext; unfold raw25644step2 raw25644step1; decide +kernel
      have hl : raw25644step1Labels = labelEmbedding1 ∘ raw25644step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25644step1 raw25644step1Labels raw25644step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

theorem canonical25645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25645 raw25645Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw25645 raw25645Labels = mixedMoment B raw25645step0 raw25645step0Labels := by
      have hz : ∀ j, raw25645 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25645step0 = (fun i j => raw25645 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25645step0 raw25645; decide +kernel
      have hl : raw25645step0Labels = raw25645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25645 raw25645Labels permutation265 hz
    mixedMoment B raw25645step0 raw25645step0Labels = mixedMoment B raw25645step1 raw25645step1Labels := by
      have ha : raw25645step1 = (fun i j => raw25645step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25645step1 raw25645step0; decide +kernel
      have hl : raw25645step1Labels = raw25645step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25645step0 raw25645step0Labels permutation37 permutation7
    mixedMoment B raw25645step1 raw25645step1Labels = mixedMoment B raw25645step2 raw25645step2Labels := by
      have ha : raw25645step2 = -raw25645step1 := by apply Matrix.ext; change ∀ i j, raw25645step2 i j = -(raw25645step1 i j); unfold raw25645step2 raw25645step1; decide +kernel
      have hl : raw25645step2Labels = raw25645step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25645step2 raw25645step2Labels = mixedMoment B raw25645step3 raw25645step3Labels := by
      have ha : raw25645step3 = raw25645step2 := by apply Matrix.ext; unfold raw25645step3 raw25645step2; decide +kernel
      have hl : raw25645step2Labels = labelEmbedding1 ∘ raw25645step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25645step2 raw25645step2Labels raw25645step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

theorem canonical25646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25646 raw25646Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw25646 raw25646Labels = mixedMoment B raw25646step0 raw25646step0Labels := by
      have hz : ∀ j, raw25646 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25646step0 = (fun i j => raw25646 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25646step0 raw25646; decide +kernel
      have hl : raw25646step0Labels = raw25646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25646 raw25646Labels permutation265 hz
    mixedMoment B raw25646step0 raw25646step0Labels = mixedMoment B raw25646step1 raw25646step1Labels := by
      have ha : raw25646step1 = (fun i j => raw25646step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25646step1 raw25646step0; decide +kernel
      have hl : raw25646step1Labels = raw25646step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25646step0 raw25646step0Labels permutation37 permutation7
    mixedMoment B raw25646step1 raw25646step1Labels = mixedMoment B raw25646step2 raw25646step2Labels := by
      have ha : raw25646step2 = -raw25646step1 := by apply Matrix.ext; change ∀ i j, raw25646step2 i j = -(raw25646step1 i j); unfold raw25646step2 raw25646step1; decide +kernel
      have hl : raw25646step2Labels = raw25646step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25646step2 raw25646step2Labels = mixedMoment B raw25646step3 raw25646step3Labels := by
      have ha : raw25646step3 = raw25646step2 := by apply Matrix.ext; unfold raw25646step3 raw25646step2; decide +kernel
      have hl : raw25646step2Labels = labelEmbedding1 ∘ raw25646step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25646step2 raw25646step2Labels raw25646step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical25647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25647 raw25647Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw25647 raw25647Labels = mixedMoment B raw25647step0 raw25647step0Labels := by
      have hz : ∀ j, raw25647 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25647step0 = (fun i j => raw25647 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25647step0 raw25647; decide +kernel
      have hl : raw25647step0Labels = raw25647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25647 raw25647Labels permutation265 hz
    mixedMoment B raw25647step0 raw25647step0Labels = mixedMoment B raw25647step1 raw25647step1Labels := by
      have ha : raw25647step1 = (fun i j => raw25647step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25647step1 raw25647step0; decide +kernel
      have hl : raw25647step1Labels = raw25647step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25647step0 raw25647step0Labels permutation37 permutation7
    mixedMoment B raw25647step1 raw25647step1Labels = mixedMoment B raw25647step2 raw25647step2Labels := by
      have ha : raw25647step2 = -raw25647step1 := by apply Matrix.ext; change ∀ i j, raw25647step2 i j = -(raw25647step1 i j); unfold raw25647step2 raw25647step1; decide +kernel
      have hl : raw25647step2Labels = raw25647step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25647step2 raw25647step2Labels = mixedMoment B raw25647step3 raw25647step3Labels := by
      have ha : raw25647step3 = raw25647step2 := by apply Matrix.ext; unfold raw25647step3 raw25647step2; decide +kernel
      have hl : raw25647step2Labels = labelEmbedding1 ∘ raw25647step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25647step2 raw25647step2Labels raw25647step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical25648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25648 raw25648Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw25648 raw25648Labels = mixedMoment B raw25648step0 raw25648step0Labels := by
      have hz : ∀ j, raw25648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25648step0 = (fun i j => raw25648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25648step0 raw25648; decide +kernel
      have hl : raw25648step0Labels = raw25648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25648 raw25648Labels permutation346 hz
    mixedMoment B raw25648step0 raw25648step0Labels = mixedMoment B raw25648step1 raw25648step1Labels := by
      have hz : ∀ j, raw25648step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25648step1 = (fun i j => raw25648step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25648step1 raw25648step0; decide +kernel
      have hl : raw25648step1Labels = raw25648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25648step0 raw25648step0Labels permutation56 hz
    mixedMoment B raw25648step1 raw25648step1Labels = mixedMoment B raw25648step2 raw25648step2Labels := by
      have ha : raw25648step2 = (fun i j => raw25648step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25648step2 raw25648step1; decide +kernel
      have hl : raw25648step2Labels = raw25648step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25648step1 raw25648step1Labels permutation13 permutation7
    mixedMoment B raw25648step2 raw25648step2Labels = mixedMoment B raw25648step3 raw25648step3Labels := by
      have ha : raw25648step3 = -raw25648step2 := by apply Matrix.ext; change ∀ i j, raw25648step3 i j = -(raw25648step2 i j); unfold raw25648step3 raw25648step2; decide +kernel
      have hl : raw25648step3Labels = raw25648step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25648step3 raw25648step3Labels = mixedMoment B raw25648step4 raw25648step4Labels := by
      have ha : raw25648step4 = raw25648step3 := by apply Matrix.ext; unfold raw25648step4 raw25648step3; decide +kernel
      have hl : raw25648step3Labels = labelEmbedding1 ∘ raw25648step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25648step3 raw25648step3Labels raw25648step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1525 node1525Labels := by rfl

theorem canonical25649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25649 raw25649Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw25649 raw25649Labels = mixedMoment B raw25649step0 raw25649step0Labels := by
      have hz : ∀ j, raw25649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25649step0 = (fun i j => raw25649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25649step0 raw25649; decide +kernel
      have hl : raw25649step0Labels = raw25649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25649 raw25649Labels permutation346 hz
    mixedMoment B raw25649step0 raw25649step0Labels = mixedMoment B raw25649step1 raw25649step1Labels := by
      have ha : raw25649step1 = (fun i j => raw25649step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25649step1 raw25649step0; decide +kernel
      have hl : raw25649step1Labels = raw25649step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25649step0 raw25649step0Labels permutation37 permutation7
    mixedMoment B raw25649step1 raw25649step1Labels = mixedMoment B raw25649step2 raw25649step2Labels := by
      have ha : raw25649step2 = -raw25649step1 := by apply Matrix.ext; change ∀ i j, raw25649step2 i j = -(raw25649step1 i j); unfold raw25649step2 raw25649step1; decide +kernel
      have hl : raw25649step2Labels = raw25649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25649step2 raw25649step2Labels = mixedMoment B raw25649step3 raw25649step3Labels := by
      have ha : raw25649step3 = raw25649step2 := by apply Matrix.ext; unfold raw25649step3 raw25649step2; decide +kernel
      have hl : raw25649step2Labels = labelEmbedding1 ∘ raw25649step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25649step2 raw25649step2Labels raw25649step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

theorem canonical25650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25650 raw25650Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw25650 raw25650Labels = mixedMoment B raw25650step0 raw25650step0Labels := by
      have hz : ∀ j, raw25650 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25650step0 = (fun i j => raw25650 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25650step0 raw25650; decide +kernel
      have hl : raw25650step0Labels = raw25650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25650 raw25650Labels permutation265 hz
    mixedMoment B raw25650step0 raw25650step0Labels = mixedMoment B raw25650step1 raw25650step1Labels := by
      have ha : raw25650step1 = (fun i j => raw25650step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25650step1 raw25650step0; decide +kernel
      have hl : raw25650step1Labels = raw25650step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25650step0 raw25650step0Labels permutation37 permutation7
    mixedMoment B raw25650step1 raw25650step1Labels = mixedMoment B raw25650step2 raw25650step2Labels := by
      have ha : raw25650step2 = -raw25650step1 := by apply Matrix.ext; change ∀ i j, raw25650step2 i j = -(raw25650step1 i j); unfold raw25650step2 raw25650step1; decide +kernel
      have hl : raw25650step2Labels = raw25650step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25650step2 raw25650step2Labels = mixedMoment B raw25650step3 raw25650step3Labels := by
      have ha : raw25650step3 = raw25650step2 := by apply Matrix.ext; unfold raw25650step3 raw25650step2; decide +kernel
      have hl : raw25650step2Labels = labelEmbedding1 ∘ raw25650step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25650step2 raw25650step2Labels raw25650step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

theorem canonical25651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25651 raw25651Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw25651 raw25651Labels = mixedMoment B raw25651step0 raw25651step0Labels := by
      have hz : ∀ j, raw25651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25651step0 = (fun i j => raw25651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25651step0 raw25651; decide +kernel
      have hl : raw25651step0Labels = raw25651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25651 raw25651Labels permutation346 hz
    mixedMoment B raw25651step0 raw25651step0Labels = mixedMoment B raw25651step1 raw25651step1Labels := by
      have hz : ∀ j, raw25651step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25651step1 = (fun i j => raw25651step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25651step1 raw25651step0; decide +kernel
      have hl : raw25651step1Labels = raw25651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25651step0 raw25651step0Labels permutation56 hz
    mixedMoment B raw25651step1 raw25651step1Labels = mixedMoment B raw25651step2 raw25651step2Labels := by
      have ha : raw25651step2 = (fun i j => raw25651step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25651step2 raw25651step1; decide +kernel
      have hl : raw25651step2Labels = raw25651step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25651step1 raw25651step1Labels permutation13 permutation7
    mixedMoment B raw25651step2 raw25651step2Labels = mixedMoment B raw25651step3 raw25651step3Labels := by
      have ha : raw25651step3 = -raw25651step2 := by apply Matrix.ext; change ∀ i j, raw25651step3 i j = -(raw25651step2 i j); unfold raw25651step3 raw25651step2; decide +kernel
      have hl : raw25651step3Labels = raw25651step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25651step3 raw25651step3Labels = mixedMoment B raw25651step4 raw25651step4Labels := by
      have ha : raw25651step4 = raw25651step3 := by apply Matrix.ext; unfold raw25651step4 raw25651step3; decide +kernel
      have hl : raw25651step3Labels = labelEmbedding1 ∘ raw25651step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25651step3 raw25651step3Labels raw25651step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

theorem canonical25652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25652 raw25652Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw25652 raw25652Labels = mixedMoment B raw25652step0 raw25652step0Labels := by
      have hz : ∀ j, raw25652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25652step0 = (fun i j => raw25652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25652step0 raw25652; decide +kernel
      have hl : raw25652step0Labels = raw25652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25652 raw25652Labels permutation346 hz
    mixedMoment B raw25652step0 raw25652step0Labels = mixedMoment B raw25652step1 raw25652step1Labels := by
      have hz : ∀ j, raw25652step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25652step1 = (fun i j => raw25652step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25652step1 raw25652step0; decide +kernel
      have hl : raw25652step1Labels = raw25652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25652step0 raw25652step0Labels permutation56 hz
    mixedMoment B raw25652step1 raw25652step1Labels = mixedMoment B raw25652step2 raw25652step2Labels := by
      have ha : raw25652step2 = (fun i j => raw25652step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25652step2 raw25652step1; decide +kernel
      have hl : raw25652step2Labels = raw25652step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25652step1 raw25652step1Labels permutation13 permutation7
    mixedMoment B raw25652step2 raw25652step2Labels = mixedMoment B raw25652step3 raw25652step3Labels := by
      have ha : raw25652step3 = -raw25652step2 := by apply Matrix.ext; change ∀ i j, raw25652step3 i j = -(raw25652step2 i j); unfold raw25652step3 raw25652step2; decide +kernel
      have hl : raw25652step3Labels = raw25652step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25652step3 raw25652step3Labels = mixedMoment B raw25652step4 raw25652step4Labels := by
      have ha : raw25652step4 = raw25652step3 := by apply Matrix.ext; unfold raw25652step4 raw25652step3; decide +kernel
      have hl : raw25652step3Labels = labelEmbedding1 ∘ raw25652step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25652step3 raw25652step3Labels raw25652step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical25653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25653 raw25653Labels = mixedMoment B node1526 node1526Labels := by
  calc
    mixedMoment B raw25653 raw25653Labels = mixedMoment B raw25653step0 raw25653step0Labels := by
      have hz : ∀ j, raw25653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25653step0 = (fun i j => raw25653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25653step0 raw25653; decide +kernel
      have hl : raw25653step0Labels = raw25653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25653 raw25653Labels permutation346 hz
    mixedMoment B raw25653step0 raw25653step0Labels = mixedMoment B raw25653step1 raw25653step1Labels := by
      have hz : ∀ j, raw25653step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25653step1 = (fun i j => raw25653step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25653step1 raw25653step0; decide +kernel
      have hl : raw25653step1Labels = raw25653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25653step0 raw25653step0Labels permutation56 hz
    mixedMoment B raw25653step1 raw25653step1Labels = mixedMoment B raw25653step2 raw25653step2Labels := by
      have ha : raw25653step2 = (fun i j => raw25653step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25653step2 raw25653step1; decide +kernel
      have hl : raw25653step2Labels = raw25653step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25653step1 raw25653step1Labels permutation13 permutation7
    mixedMoment B raw25653step2 raw25653step2Labels = mixedMoment B raw25653step3 raw25653step3Labels := by
      have ha : raw25653step3 = -raw25653step2 := by apply Matrix.ext; change ∀ i j, raw25653step3 i j = -(raw25653step2 i j); unfold raw25653step3 raw25653step2; decide +kernel
      have hl : raw25653step3Labels = raw25653step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25653step3 raw25653step3Labels = mixedMoment B raw25653step4 raw25653step4Labels := by
      have ha : raw25653step4 = raw25653step3 := by apply Matrix.ext; unfold raw25653step4 raw25653step3; decide +kernel
      have hl : raw25653step3Labels = labelEmbedding1 ∘ raw25653step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25653step3 raw25653step3Labels raw25653step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1526 node1526Labels := by rfl

theorem canonical25654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25654 raw25654Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw25654 raw25654Labels = mixedMoment B raw25654step0 raw25654step0Labels := by
      have hz : ∀ j, raw25654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25654step0 = (fun i j => raw25654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25654step0 raw25654; decide +kernel
      have hl : raw25654step0Labels = raw25654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25654 raw25654Labels permutation346 hz
    mixedMoment B raw25654step0 raw25654step0Labels = mixedMoment B raw25654step1 raw25654step1Labels := by
      have ha : raw25654step1 = (fun i j => raw25654step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25654step1 raw25654step0; decide +kernel
      have hl : raw25654step1Labels = raw25654step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25654step0 raw25654step0Labels permutation37 permutation7
    mixedMoment B raw25654step1 raw25654step1Labels = mixedMoment B raw25654step2 raw25654step2Labels := by
      have ha : raw25654step2 = -raw25654step1 := by apply Matrix.ext; change ∀ i j, raw25654step2 i j = -(raw25654step1 i j); unfold raw25654step2 raw25654step1; decide +kernel
      have hl : raw25654step2Labels = raw25654step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25654step2 raw25654step2Labels = mixedMoment B raw25654step3 raw25654step3Labels := by
      have ha : raw25654step3 = raw25654step2 := by apply Matrix.ext; unfold raw25654step3 raw25654step2; decide +kernel
      have hl : raw25654step2Labels = labelEmbedding1 ∘ raw25654step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25654step2 raw25654step2Labels raw25654step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

theorem canonical25655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25655 raw25655Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw25655 raw25655Labels = mixedMoment B raw25655step0 raw25655step0Labels := by
      have hz : ∀ j, raw25655 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25655step0 = (fun i j => raw25655 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25655step0 raw25655; decide +kernel
      have hl : raw25655step0Labels = raw25655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25655 raw25655Labels permutation265 hz
    mixedMoment B raw25655step0 raw25655step0Labels = mixedMoment B raw25655step1 raw25655step1Labels := by
      have ha : raw25655step1 = (fun i j => raw25655step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25655step1 raw25655step0; decide +kernel
      have hl : raw25655step1Labels = raw25655step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25655step0 raw25655step0Labels permutation37 permutation7
    mixedMoment B raw25655step1 raw25655step1Labels = mixedMoment B raw25655step2 raw25655step2Labels := by
      have ha : raw25655step2 = -raw25655step1 := by apply Matrix.ext; change ∀ i j, raw25655step2 i j = -(raw25655step1 i j); unfold raw25655step2 raw25655step1; decide +kernel
      have hl : raw25655step2Labels = raw25655step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25655step2 raw25655step2Labels = mixedMoment B raw25655step3 raw25655step3Labels := by
      have ha : raw25655step3 = raw25655step2 := by apply Matrix.ext; unfold raw25655step3 raw25655step2; decide +kernel
      have hl : raw25655step2Labels = labelEmbedding1 ∘ raw25655step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25655step2 raw25655step2Labels raw25655step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

theorem canonical25656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25656 raw25656Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw25656 raw25656Labels = mixedMoment B raw25656step0 raw25656step0Labels := by
      have hz : ∀ j, raw25656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25656step0 = (fun i j => raw25656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25656step0 raw25656; decide +kernel
      have hl : raw25656step0Labels = raw25656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25656 raw25656Labels permutation346 hz
    mixedMoment B raw25656step0 raw25656step0Labels = mixedMoment B raw25656step1 raw25656step1Labels := by
      have hz : ∀ j, raw25656step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25656step1 = (fun i j => raw25656step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25656step1 raw25656step0; decide +kernel
      have hl : raw25656step1Labels = raw25656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25656step0 raw25656step0Labels permutation56 hz
    mixedMoment B raw25656step1 raw25656step1Labels = mixedMoment B raw25656step2 raw25656step2Labels := by
      have ha : raw25656step2 = (fun i j => raw25656step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25656step2 raw25656step1; decide +kernel
      have hl : raw25656step2Labels = raw25656step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25656step1 raw25656step1Labels permutation13 permutation7
    mixedMoment B raw25656step2 raw25656step2Labels = mixedMoment B raw25656step3 raw25656step3Labels := by
      have ha : raw25656step3 = -raw25656step2 := by apply Matrix.ext; change ∀ i j, raw25656step3 i j = -(raw25656step2 i j); unfold raw25656step3 raw25656step2; decide +kernel
      have hl : raw25656step3Labels = raw25656step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25656step3 raw25656step3Labels = mixedMoment B raw25656step4 raw25656step4Labels := by
      have ha : raw25656step4 = raw25656step3 := by apply Matrix.ext; unfold raw25656step4 raw25656step3; decide +kernel
      have hl : raw25656step3Labels = labelEmbedding1 ∘ raw25656step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25656step3 raw25656step3Labels raw25656step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

theorem canonical25657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25657 raw25657Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw25657 raw25657Labels = mixedMoment B raw25657step0 raw25657step0Labels := by
      have hz : ∀ j, raw25657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25657step0 = (fun i j => raw25657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25657step0 raw25657; decide +kernel
      have hl : raw25657step0Labels = raw25657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25657 raw25657Labels permutation346 hz
    mixedMoment B raw25657step0 raw25657step0Labels = mixedMoment B raw25657step1 raw25657step1Labels := by
      have hz : ∀ j, raw25657step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25657step1 = (fun i j => raw25657step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25657step1 raw25657step0; decide +kernel
      have hl : raw25657step1Labels = raw25657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25657step0 raw25657step0Labels permutation56 hz
    mixedMoment B raw25657step1 raw25657step1Labels = mixedMoment B raw25657step2 raw25657step2Labels := by
      have ha : raw25657step2 = (fun i j => raw25657step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25657step2 raw25657step1; decide +kernel
      have hl : raw25657step2Labels = raw25657step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25657step1 raw25657step1Labels permutation13 permutation7
    mixedMoment B raw25657step2 raw25657step2Labels = mixedMoment B raw25657step3 raw25657step3Labels := by
      have ha : raw25657step3 = -raw25657step2 := by apply Matrix.ext; change ∀ i j, raw25657step3 i j = -(raw25657step2 i j); unfold raw25657step3 raw25657step2; decide +kernel
      have hl : raw25657step3Labels = raw25657step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25657step3 raw25657step3Labels = mixedMoment B raw25657step4 raw25657step4Labels := by
      have ha : raw25657step4 = raw25657step3 := by apply Matrix.ext; unfold raw25657step4 raw25657step3; decide +kernel
      have hl : raw25657step3Labels = labelEmbedding1 ∘ raw25657step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25657step3 raw25657step3Labels raw25657step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical25658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25658 raw25658Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw25658 raw25658Labels = mixedMoment B raw25658step0 raw25658step0Labels := by
      have hz : ∀ j, raw25658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25658step0 = (fun i j => raw25658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25658step0 raw25658; decide +kernel
      have hl : raw25658step0Labels = raw25658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25658 raw25658Labels permutation346 hz
    mixedMoment B raw25658step0 raw25658step0Labels = mixedMoment B raw25658step1 raw25658step1Labels := by
      have hz : ∀ j, raw25658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25658step1 = (fun i j => raw25658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25658step1 raw25658step0; decide +kernel
      have hl : raw25658step1Labels = raw25658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25658step0 raw25658step0Labels permutation56 hz
    mixedMoment B raw25658step1 raw25658step1Labels = mixedMoment B raw25658step2 raw25658step2Labels := by
      have ha : raw25658step2 = (fun i j => raw25658step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25658step2 raw25658step1; decide +kernel
      have hl : raw25658step2Labels = raw25658step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25658step1 raw25658step1Labels permutation13 permutation7
    mixedMoment B raw25658step2 raw25658step2Labels = mixedMoment B raw25658step3 raw25658step3Labels := by
      have ha : raw25658step3 = -raw25658step2 := by apply Matrix.ext; change ∀ i j, raw25658step3 i j = -(raw25658step2 i j); unfold raw25658step3 raw25658step2; decide +kernel
      have hl : raw25658step3Labels = raw25658step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25658step3 raw25658step3Labels = mixedMoment B raw25658step4 raw25658step4Labels := by
      have ha : raw25658step4 = raw25658step3 := by apply Matrix.ext; unfold raw25658step4 raw25658step3; decide +kernel
      have hl : raw25658step3Labels = labelEmbedding1 ∘ raw25658step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25658step3 raw25658step3Labels raw25658step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1530 node1530Labels := by rfl

theorem canonical25659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25659 raw25659Labels = mixedMoment B node1686 node1686Labels := by
  calc
    mixedMoment B raw25659 raw25659Labels = mixedMoment B raw25659step0 raw25659step0Labels := by
      have hz : ∀ j, raw25659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25659step0 = (fun i j => raw25659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25659step0 raw25659; decide +kernel
      have hl : raw25659step0Labels = raw25659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25659 raw25659Labels permutation346 hz
    mixedMoment B raw25659step0 raw25659step0Labels = mixedMoment B raw25659step1 raw25659step1Labels := by
      have ha : raw25659step1 = (fun i j => raw25659step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25659step1 raw25659step0; decide +kernel
      have hl : raw25659step1Labels = raw25659step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25659step0 raw25659step0Labels permutation37 permutation7
    mixedMoment B raw25659step1 raw25659step1Labels = mixedMoment B raw25659step2 raw25659step2Labels := by
      have ha : raw25659step2 = -raw25659step1 := by apply Matrix.ext; change ∀ i j, raw25659step2 i j = -(raw25659step1 i j); unfold raw25659step2 raw25659step1; decide +kernel
      have hl : raw25659step2Labels = raw25659step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25659step2 raw25659step2Labels = mixedMoment B raw25659step3 raw25659step3Labels := by
      have ha : raw25659step3 = raw25659step2 := by apply Matrix.ext; unfold raw25659step3 raw25659step2; decide +kernel
      have hl : raw25659step2Labels = labelEmbedding1 ∘ raw25659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25659step2 raw25659step2Labels raw25659step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1686 node1686Labels := by rfl

theorem canonical25660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25660 raw25660Labels = mixedMoment B node1686 node1686Labels := by
  calc
    mixedMoment B raw25660 raw25660Labels = mixedMoment B raw25660step0 raw25660step0Labels := by
      have hz : ∀ j, raw25660 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25660step0 = (fun i j => raw25660 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25660step0 raw25660; decide +kernel
      have hl : raw25660step0Labels = raw25660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25660 raw25660Labels permutation265 hz
    mixedMoment B raw25660step0 raw25660step0Labels = mixedMoment B raw25660step1 raw25660step1Labels := by
      have ha : raw25660step1 = (fun i j => raw25660step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25660step1 raw25660step0; decide +kernel
      have hl : raw25660step1Labels = raw25660step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25660step0 raw25660step0Labels permutation37 permutation7
    mixedMoment B raw25660step1 raw25660step1Labels = mixedMoment B raw25660step2 raw25660step2Labels := by
      have ha : raw25660step2 = -raw25660step1 := by apply Matrix.ext; change ∀ i j, raw25660step2 i j = -(raw25660step1 i j); unfold raw25660step2 raw25660step1; decide +kernel
      have hl : raw25660step2Labels = raw25660step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25660step2 raw25660step2Labels = mixedMoment B raw25660step3 raw25660step3Labels := by
      have ha : raw25660step3 = raw25660step2 := by apply Matrix.ext; unfold raw25660step3 raw25660step2; decide +kernel
      have hl : raw25660step2Labels = labelEmbedding1 ∘ raw25660step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25660step2 raw25660step2Labels raw25660step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1686 node1686Labels := by rfl

theorem canonical25661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25661 raw25661Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw25661 raw25661Labels = mixedMoment B raw25661step0 raw25661step0Labels := by
      have hz : ∀ j, raw25661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25661step0 = (fun i j => raw25661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25661step0 raw25661; decide +kernel
      have hl : raw25661step0Labels = raw25661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25661 raw25661Labels permutation346 hz
    mixedMoment B raw25661step0 raw25661step0Labels = mixedMoment B raw25661step1 raw25661step1Labels := by
      have hz : ∀ j, raw25661step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25661step1 = (fun i j => raw25661step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25661step1 raw25661step0; decide +kernel
      have hl : raw25661step1Labels = raw25661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25661step0 raw25661step0Labels permutation56 hz
    mixedMoment B raw25661step1 raw25661step1Labels = mixedMoment B raw25661step2 raw25661step2Labels := by
      have ha : raw25661step2 = (fun i j => raw25661step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25661step2 raw25661step1; decide +kernel
      have hl : raw25661step2Labels = raw25661step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25661step1 raw25661step1Labels permutation13 permutation7
    mixedMoment B raw25661step2 raw25661step2Labels = mixedMoment B raw25661step3 raw25661step3Labels := by
      have ha : raw25661step3 = -raw25661step2 := by apply Matrix.ext; change ∀ i j, raw25661step3 i j = -(raw25661step2 i j); unfold raw25661step3 raw25661step2; decide +kernel
      have hl : raw25661step3Labels = raw25661step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25661step3 raw25661step3Labels = mixedMoment B raw25661step4 raw25661step4Labels := by
      have ha : raw25661step4 = raw25661step3 := by apply Matrix.ext; unfold raw25661step4 raw25661step3; decide +kernel
      have hl : raw25661step3Labels = labelEmbedding1 ∘ raw25661step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25661step3 raw25661step3Labels raw25661step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

theorem canonical25662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25662 raw25662Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw25662 raw25662Labels = mixedMoment B raw25662step0 raw25662step0Labels := by
      have hz : ∀ j, raw25662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25662step0 = (fun i j => raw25662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25662step0 raw25662; decide +kernel
      have hl : raw25662step0Labels = raw25662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25662 raw25662Labels permutation346 hz
    mixedMoment B raw25662step0 raw25662step0Labels = mixedMoment B raw25662step1 raw25662step1Labels := by
      have hz : ∀ j, raw25662step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25662step1 = (fun i j => raw25662step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25662step1 raw25662step0; decide +kernel
      have hl : raw25662step1Labels = raw25662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25662step0 raw25662step0Labels permutation56 hz
    mixedMoment B raw25662step1 raw25662step1Labels = mixedMoment B raw25662step2 raw25662step2Labels := by
      have ha : raw25662step2 = (fun i j => raw25662step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25662step2 raw25662step1; decide +kernel
      have hl : raw25662step2Labels = raw25662step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25662step1 raw25662step1Labels permutation13 permutation7
    mixedMoment B raw25662step2 raw25662step2Labels = mixedMoment B raw25662step3 raw25662step3Labels := by
      have ha : raw25662step3 = -raw25662step2 := by apply Matrix.ext; change ∀ i j, raw25662step3 i j = -(raw25662step2 i j); unfold raw25662step3 raw25662step2; decide +kernel
      have hl : raw25662step3Labels = raw25662step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25662step3 raw25662step3Labels = mixedMoment B raw25662step4 raw25662step4Labels := by
      have ha : raw25662step4 = raw25662step3 := by apply Matrix.ext; unfold raw25662step4 raw25662step3; decide +kernel
      have hl : raw25662step3Labels = labelEmbedding1 ∘ raw25662step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25662step3 raw25662step3Labels raw25662step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

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

theorem canonical25763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25763 raw25763Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw25763 raw25763Labels = mixedMoment B raw25763step0 raw25763step0Labels := by
      have hz : ∀ j, raw25763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25763step0 = (fun i j => raw25763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25763step0 raw25763; decide +kernel
      have hl : raw25763step0Labels = raw25763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25763 raw25763Labels permutation346 hz
    mixedMoment B raw25763step0 raw25763step0Labels = mixedMoment B raw25763step1 raw25763step1Labels := by
      have ha : raw25763step1 = (fun i j => raw25763step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25763step1 raw25763step0; decide +kernel
      have hl : raw25763step1Labels = raw25763step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25763step0 raw25763step0Labels permutation35 permutation7
    mixedMoment B raw25763step1 raw25763step1Labels = mixedMoment B raw25763step2 raw25763step2Labels := by
      have ha : raw25763step2 = -raw25763step1 := by apply Matrix.ext; change ∀ i j, raw25763step2 i j = -(raw25763step1 i j); unfold raw25763step2 raw25763step1; decide +kernel
      have hl : raw25763step2Labels = raw25763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25763step2 raw25763step2Labels = mixedMoment B raw25763step3 raw25763step3Labels := by
      have ha : raw25763step3 = raw25763step2 := by apply Matrix.ext; unfold raw25763step3 raw25763step2; decide +kernel
      have hl : raw25763step2Labels = labelEmbedding1 ∘ raw25763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25763step2 raw25763step2Labels raw25763step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

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

theorem canonical25768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25768 raw25768Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw25768 raw25768Labels = mixedMoment B raw25768step0 raw25768step0Labels := by
      have hz : ∀ j, raw25768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25768step0 = (fun i j => raw25768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25768step0 raw25768; decide +kernel
      have hl : raw25768step0Labels = raw25768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25768 raw25768Labels permutation346 hz
    mixedMoment B raw25768step0 raw25768step0Labels = mixedMoment B raw25768step1 raw25768step1Labels := by
      have ha : raw25768step1 = (fun i j => raw25768step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25768step1 raw25768step0; decide +kernel
      have hl : raw25768step1Labels = raw25768step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25768step0 raw25768step0Labels permutation35 permutation7
    mixedMoment B raw25768step1 raw25768step1Labels = mixedMoment B raw25768step2 raw25768step2Labels := by
      have ha : raw25768step2 = -raw25768step1 := by apply Matrix.ext; change ∀ i j, raw25768step2 i j = -(raw25768step1 i j); unfold raw25768step2 raw25768step1; decide +kernel
      have hl : raw25768step2Labels = raw25768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25768step2 raw25768step2Labels = mixedMoment B raw25768step3 raw25768step3Labels := by
      have ha : raw25768step3 = raw25768step2 := by apply Matrix.ext; unfold raw25768step3 raw25768step2; decide +kernel
      have hl : raw25768step2Labels = labelEmbedding1 ∘ raw25768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25768step2 raw25768step2Labels raw25768step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

theorem canonical25769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25769 raw25769Labels = mixedMoment B node1665 node1665Labels := by
  calc
    mixedMoment B raw25769 raw25769Labels = mixedMoment B raw25769step0 raw25769step0Labels := by
      have ha : raw25769step0 = (fun i j => raw25769 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25769step0 raw25769; decide +kernel
      have hl : raw25769step0Labels = raw25769Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25769 raw25769Labels permutation179 permutation7
    mixedMoment B raw25769step0 raw25769step0Labels = mixedMoment B raw25769step1 raw25769step1Labels := by
      have ha : raw25769step1 = -raw25769step0 := by apply Matrix.ext; change ∀ i j, raw25769step1 i j = -(raw25769step0 i j); unfold raw25769step1 raw25769step0; decide +kernel
      have hl : raw25769step1Labels = raw25769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25769step1 raw25769step1Labels = mixedMoment B raw25769step2 raw25769step2Labels := by
      have ha : raw25769step2 = raw25769step1 := by apply Matrix.ext; unfold raw25769step2 raw25769step1; decide +kernel
      have hl : raw25769step1Labels = labelEmbedding1 ∘ raw25769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25769step1 raw25769step1Labels raw25769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1665 node1665Labels := by rfl

theorem canonical25770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25770 raw25770Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw25770 raw25770Labels = mixedMoment B raw25770step0 raw25770step0Labels := by
      have hz : ∀ j, raw25770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25770step0 = (fun i j => raw25770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25770step0 raw25770; decide +kernel
      have hl : raw25770step0Labels = raw25770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25770 raw25770Labels permutation346 hz
    mixedMoment B raw25770step0 raw25770step0Labels = mixedMoment B raw25770step1 raw25770step1Labels := by
      have ha : raw25770step1 = (fun i j => raw25770step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25770step1 raw25770step0; decide +kernel
      have hl : raw25770step1Labels = raw25770step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25770step0 raw25770step0Labels permutation35 permutation7
    mixedMoment B raw25770step1 raw25770step1Labels = mixedMoment B raw25770step2 raw25770step2Labels := by
      have ha : raw25770step2 = -raw25770step1 := by apply Matrix.ext; change ∀ i j, raw25770step2 i j = -(raw25770step1 i j); unfold raw25770step2 raw25770step1; decide +kernel
      have hl : raw25770step2Labels = raw25770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25770step2 raw25770step2Labels = mixedMoment B raw25770step3 raw25770step3Labels := by
      have ha : raw25770step3 = raw25770step2 := by apply Matrix.ext; unfold raw25770step3 raw25770step2; decide +kernel
      have hl : raw25770step2Labels = labelEmbedding1 ∘ raw25770step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25770step2 raw25770step2Labels raw25770step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

theorem canonical25771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25771 raw25771Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw25771 raw25771Labels = mixedMoment B raw25771step0 raw25771step0Labels := by
      have hz : ∀ j, raw25771 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25771step0 = (fun i j => raw25771 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25771step0 raw25771; decide +kernel
      have hl : raw25771step0Labels = raw25771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25771 raw25771Labels permutation520 hz
    mixedMoment B raw25771step0 raw25771step0Labels = mixedMoment B raw25771step1 raw25771step1Labels := by
      have hz : ∀ j, raw25771step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25771step1 = (fun i j => raw25771step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25771step1 raw25771step0; decide +kernel
      have hl : raw25771step1Labels = raw25771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25771step0 raw25771step0Labels permutation80 hz
    mixedMoment B raw25771step1 raw25771step1Labels = mixedMoment B raw25771step2 raw25771step2Labels := by
      have ha : raw25771step2 = (fun i j => raw25771step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25771step2 raw25771step1; decide +kernel
      have hl : raw25771step2Labels = raw25771step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25771step1 raw25771step1Labels permutation9 permutation7
    mixedMoment B raw25771step2 raw25771step2Labels = mixedMoment B raw25771step3 raw25771step3Labels := by
      have ha : raw25771step3 = -raw25771step2 := by apply Matrix.ext; change ∀ i j, raw25771step3 i j = -(raw25771step2 i j); unfold raw25771step3 raw25771step2; decide +kernel
      have hl : raw25771step3Labels = raw25771step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25771step3 raw25771step3Labels = mixedMoment B raw25771step4 raw25771step4Labels := by
      have ha : raw25771step4 = raw25771step3 := by apply Matrix.ext; unfold raw25771step4 raw25771step3; decide +kernel
      have hl : raw25771step3Labels = labelEmbedding1 ∘ raw25771step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25771step3 raw25771step3Labels raw25771step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical25772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25772 raw25772Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw25772 raw25772Labels = mixedMoment B raw25772step0 raw25772step0Labels := by
      have hz : ∀ j, raw25772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25772step0 = (fun i j => raw25772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25772step0 raw25772; decide +kernel
      have hl : raw25772step0Labels = raw25772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25772 raw25772Labels permutation346 hz
    mixedMoment B raw25772step0 raw25772step0Labels = mixedMoment B raw25772step1 raw25772step1Labels := by
      have ha : raw25772step1 = (fun i j => raw25772step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25772step1 raw25772step0; decide +kernel
      have hl : raw25772step1Labels = raw25772step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25772step0 raw25772step0Labels permutation35 permutation7
    mixedMoment B raw25772step1 raw25772step1Labels = mixedMoment B raw25772step2 raw25772step2Labels := by
      have ha : raw25772step2 = -raw25772step1 := by apply Matrix.ext; change ∀ i j, raw25772step2 i j = -(raw25772step1 i j); unfold raw25772step2 raw25772step1; decide +kernel
      have hl : raw25772step2Labels = raw25772step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25772step2 raw25772step2Labels = mixedMoment B raw25772step3 raw25772step3Labels := by
      have ha : raw25772step3 = raw25772step2 := by apply Matrix.ext; unfold raw25772step3 raw25772step2; decide +kernel
      have hl : raw25772step2Labels = labelEmbedding1 ∘ raw25772step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25772step2 raw25772step2Labels raw25772step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical25773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25773 raw25773Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw25773 raw25773Labels = mixedMoment B raw25773step0 raw25773step0Labels := by
      have hz : ∀ j, raw25773 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25773step0 = (fun i j => raw25773 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25773step0 raw25773; decide +kernel
      have hl : raw25773step0Labels = raw25773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25773 raw25773Labels permutation265 hz
    mixedMoment B raw25773step0 raw25773step0Labels = mixedMoment B raw25773step1 raw25773step1Labels := by
      have ha : raw25773step1 = (fun i j => raw25773step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25773step1 raw25773step0; decide +kernel
      have hl : raw25773step1Labels = raw25773step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25773step0 raw25773step0Labels permutation35 permutation7
    mixedMoment B raw25773step1 raw25773step1Labels = mixedMoment B raw25773step2 raw25773step2Labels := by
      have ha : raw25773step2 = -raw25773step1 := by apply Matrix.ext; change ∀ i j, raw25773step2 i j = -(raw25773step1 i j); unfold raw25773step2 raw25773step1; decide +kernel
      have hl : raw25773step2Labels = raw25773step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25773step2 raw25773step2Labels = mixedMoment B raw25773step3 raw25773step3Labels := by
      have ha : raw25773step3 = raw25773step2 := by apply Matrix.ext; unfold raw25773step3 raw25773step2; decide +kernel
      have hl : raw25773step2Labels = labelEmbedding1 ∘ raw25773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25773step2 raw25773step2Labels raw25773step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

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

theorem canonical25775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25775 raw25775Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw25775 raw25775Labels = mixedMoment B raw25775step0 raw25775step0Labels := by
      have hz : ∀ j, raw25775 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25775step0 = (fun i j => raw25775 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25775step0 raw25775; decide +kernel
      have hl : raw25775step0Labels = raw25775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25775 raw25775Labels permutation265 hz
    mixedMoment B raw25775step0 raw25775step0Labels = mixedMoment B raw25775step1 raw25775step1Labels := by
      have ha : raw25775step1 = (fun i j => raw25775step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25775step1 raw25775step0; decide +kernel
      have hl : raw25775step1Labels = raw25775step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25775step0 raw25775step0Labels permutation35 permutation7
    mixedMoment B raw25775step1 raw25775step1Labels = mixedMoment B raw25775step2 raw25775step2Labels := by
      have ha : raw25775step2 = -raw25775step1 := by apply Matrix.ext; change ∀ i j, raw25775step2 i j = -(raw25775step1 i j); unfold raw25775step2 raw25775step1; decide +kernel
      have hl : raw25775step2Labels = raw25775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25775step2 raw25775step2Labels = mixedMoment B raw25775step3 raw25775step3Labels := by
      have ha : raw25775step3 = raw25775step2 := by apply Matrix.ext; unfold raw25775step3 raw25775step2; decide +kernel
      have hl : raw25775step2Labels = labelEmbedding1 ∘ raw25775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25775step2 raw25775step2Labels raw25775step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

theorem canonical25776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25776 raw25776Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw25776 raw25776Labels = mixedMoment B raw25776step0 raw25776step0Labels := by
      have hz : ∀ j, raw25776 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25776step0 = (fun i j => raw25776 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25776step0 raw25776; decide +kernel
      have hl : raw25776step0Labels = raw25776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25776 raw25776Labels permutation520 hz
    mixedMoment B raw25776step0 raw25776step0Labels = mixedMoment B raw25776step1 raw25776step1Labels := by
      have hz : ∀ j, raw25776step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25776step1 = (fun i j => raw25776step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25776step1 raw25776step0; decide +kernel
      have hl : raw25776step1Labels = raw25776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25776step0 raw25776step0Labels permutation56 hz
    mixedMoment B raw25776step1 raw25776step1Labels = mixedMoment B raw25776step2 raw25776step2Labels := by
      have ha : raw25776step2 = (fun i j => raw25776step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25776step2 raw25776step1; decide +kernel
      have hl : raw25776step2Labels = raw25776step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25776step1 raw25776step1Labels permutation9 permutation7
    mixedMoment B raw25776step2 raw25776step2Labels = mixedMoment B raw25776step3 raw25776step3Labels := by
      have ha : raw25776step3 = -raw25776step2 := by apply Matrix.ext; change ∀ i j, raw25776step3 i j = -(raw25776step2 i j); unfold raw25776step3 raw25776step2; decide +kernel
      have hl : raw25776step3Labels = raw25776step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25776step3 raw25776step3Labels = mixedMoment B raw25776step4 raw25776step4Labels := by
      have ha : raw25776step4 = raw25776step3 := by apply Matrix.ext; unfold raw25776step4 raw25776step3; decide +kernel
      have hl : raw25776step3Labels = labelEmbedding1 ∘ raw25776step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25776step3 raw25776step3Labels raw25776step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical25777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25777 raw25777Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw25777 raw25777Labels = mixedMoment B raw25777step0 raw25777step0Labels := by
      have hz : ∀ j, raw25777 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25777step0 = (fun i j => raw25777 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25777step0 raw25777; decide +kernel
      have hl : raw25777step0Labels = raw25777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25777 raw25777Labels permutation265 hz
    mixedMoment B raw25777step0 raw25777step0Labels = mixedMoment B raw25777step1 raw25777step1Labels := by
      have ha : raw25777step1 = (fun i j => raw25777step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25777step1 raw25777step0; decide +kernel
      have hl : raw25777step1Labels = raw25777step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25777step0 raw25777step0Labels permutation35 permutation7
    mixedMoment B raw25777step1 raw25777step1Labels = mixedMoment B raw25777step2 raw25777step2Labels := by
      have ha : raw25777step2 = -raw25777step1 := by apply Matrix.ext; change ∀ i j, raw25777step2 i j = -(raw25777step1 i j); unfold raw25777step2 raw25777step1; decide +kernel
      have hl : raw25777step2Labels = raw25777step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25777step2 raw25777step2Labels = mixedMoment B raw25777step3 raw25777step3Labels := by
      have ha : raw25777step3 = raw25777step2 := by apply Matrix.ext; unfold raw25777step3 raw25777step2; decide +kernel
      have hl : raw25777step2Labels = labelEmbedding1 ∘ raw25777step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25777step2 raw25777step2Labels raw25777step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical25778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25778 raw25778Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw25778 raw25778Labels = mixedMoment B raw25778step0 raw25778step0Labels := by
      have hz : ∀ j, raw25778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25778step0 = (fun i j => raw25778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25778step0 raw25778; decide +kernel
      have hl : raw25778step0Labels = raw25778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25778 raw25778Labels permutation346 hz
    mixedMoment B raw25778step0 raw25778step0Labels = mixedMoment B raw25778step1 raw25778step1Labels := by
      have hz : ∀ j, raw25778step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25778step1 = (fun i j => raw25778step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25778step1 raw25778step0; decide +kernel
      have hl : raw25778step1Labels = raw25778step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25778step0 raw25778step0Labels permutation56 hz
    mixedMoment B raw25778step1 raw25778step1Labels = mixedMoment B raw25778step2 raw25778step2Labels := by
      have ha : raw25778step2 = (fun i j => raw25778step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25778step2 raw25778step1; decide +kernel
      have hl : raw25778step2Labels = raw25778step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25778step1 raw25778step1Labels permutation11 permutation7
    mixedMoment B raw25778step2 raw25778step2Labels = mixedMoment B raw25778step3 raw25778step3Labels := by
      have ha : raw25778step3 = -raw25778step2 := by apply Matrix.ext; change ∀ i j, raw25778step3 i j = -(raw25778step2 i j); unfold raw25778step3 raw25778step2; decide +kernel
      have hl : raw25778step3Labels = raw25778step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25778step3 raw25778step3Labels = mixedMoment B raw25778step4 raw25778step4Labels := by
      have ha : raw25778step4 = raw25778step3 := by apply Matrix.ext; unfold raw25778step4 raw25778step3; decide +kernel
      have hl : raw25778step3Labels = labelEmbedding1 ∘ raw25778step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25778step3 raw25778step3Labels raw25778step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1519 node1519Labels := by rfl

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

theorem canonical25780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25780 raw25780Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw25780 raw25780Labels = mixedMoment B raw25780step0 raw25780step0Labels := by
      have hz : ∀ j, raw25780 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25780step0 = (fun i j => raw25780 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25780step0 raw25780; decide +kernel
      have hl : raw25780step0Labels = raw25780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25780 raw25780Labels permutation265 hz
    mixedMoment B raw25780step0 raw25780step0Labels = mixedMoment B raw25780step1 raw25780step1Labels := by
      have ha : raw25780step1 = (fun i j => raw25780step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25780step1 raw25780step0; decide +kernel
      have hl : raw25780step1Labels = raw25780step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25780step0 raw25780step0Labels permutation35 permutation7
    mixedMoment B raw25780step1 raw25780step1Labels = mixedMoment B raw25780step2 raw25780step2Labels := by
      have ha : raw25780step2 = -raw25780step1 := by apply Matrix.ext; change ∀ i j, raw25780step2 i j = -(raw25780step1 i j); unfold raw25780step2 raw25780step1; decide +kernel
      have hl : raw25780step2Labels = raw25780step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25780step2 raw25780step2Labels = mixedMoment B raw25780step3 raw25780step3Labels := by
      have ha : raw25780step3 = raw25780step2 := by apply Matrix.ext; unfold raw25780step3 raw25780step2; decide +kernel
      have hl : raw25780step2Labels = labelEmbedding1 ∘ raw25780step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25780step2 raw25780step2Labels raw25780step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

theorem canonical25781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25781 raw25781Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw25781 raw25781Labels = mixedMoment B raw25781step0 raw25781step0Labels := by
      have hz : ∀ j, raw25781 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25781step0 = (fun i j => raw25781 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25781step0 raw25781; decide +kernel
      have hl : raw25781step0Labels = raw25781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25781 raw25781Labels permutation520 hz
    mixedMoment B raw25781step0 raw25781step0Labels = mixedMoment B raw25781step1 raw25781step1Labels := by
      have hz : ∀ j, raw25781step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25781step1 = (fun i j => raw25781step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25781step1 raw25781step0; decide +kernel
      have hl : raw25781step1Labels = raw25781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25781step0 raw25781step0Labels permutation80 hz
    mixedMoment B raw25781step1 raw25781step1Labels = mixedMoment B raw25781step2 raw25781step2Labels := by
      have hz : ∀ j, raw25781step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25781step2 = (fun i j => raw25781step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25781step2 raw25781step1; decide +kernel
      have hl : raw25781step2Labels = raw25781step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25781step1 raw25781step1Labels permutation14 hz
    mixedMoment B raw25781step2 raw25781step2Labels = mixedMoment B raw25781step3 raw25781step3Labels := by
      have ha : raw25781step3 = (fun i j => raw25781step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25781step3 raw25781step2; decide +kernel
      have hl : raw25781step3Labels = raw25781step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25781step2 raw25781step2Labels permutation3 permutation7
    mixedMoment B raw25781step3 raw25781step3Labels = mixedMoment B raw25781step4 raw25781step4Labels := by
      have ha : raw25781step4 = -raw25781step3 := by apply Matrix.ext; change ∀ i j, raw25781step4 i j = -(raw25781step3 i j); unfold raw25781step4 raw25781step3; decide +kernel
      have hl : raw25781step4Labels = raw25781step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25781step4 raw25781step4Labels = mixedMoment B raw25781step5 raw25781step5Labels := by
      have ha : raw25781step5 = raw25781step4 := by apply Matrix.ext; unfold raw25781step5 raw25781step4; decide +kernel
      have hl : raw25781step4Labels = labelEmbedding1 ∘ raw25781step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25781step4 raw25781step4Labels raw25781step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1755 node1755Labels := by rfl

theorem canonical25782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25782 raw25782Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw25782 raw25782Labels = mixedMoment B raw25782step0 raw25782step0Labels := by
      have hz : ∀ j, raw25782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25782step0 = (fun i j => raw25782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25782step0 raw25782; decide +kernel
      have hl : raw25782step0Labels = raw25782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25782 raw25782Labels permutation346 hz
    mixedMoment B raw25782step0 raw25782step0Labels = mixedMoment B raw25782step1 raw25782step1Labels := by
      have hz : ∀ j, raw25782step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25782step1 = (fun i j => raw25782step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25782step1 raw25782step0; decide +kernel
      have hl : raw25782step1Labels = raw25782step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25782step0 raw25782step0Labels permutation56 hz
    mixedMoment B raw25782step1 raw25782step1Labels = mixedMoment B raw25782step2 raw25782step2Labels := by
      have ha : raw25782step2 = (fun i j => raw25782step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25782step2 raw25782step1; decide +kernel
      have hl : raw25782step2Labels = raw25782step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25782step1 raw25782step1Labels permutation11 permutation7
    mixedMoment B raw25782step2 raw25782step2Labels = mixedMoment B raw25782step3 raw25782step3Labels := by
      have ha : raw25782step3 = -raw25782step2 := by apply Matrix.ext; change ∀ i j, raw25782step3 i j = -(raw25782step2 i j); unfold raw25782step3 raw25782step2; decide +kernel
      have hl : raw25782step3Labels = raw25782step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25782step3 raw25782step3Labels = mixedMoment B raw25782step4 raw25782step4Labels := by
      have ha : raw25782step4 = raw25782step3 := by apply Matrix.ext; unfold raw25782step4 raw25782step3; decide +kernel
      have hl : raw25782step3Labels = labelEmbedding1 ∘ raw25782step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25782step3 raw25782step3Labels raw25782step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical25783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25783 raw25783Labels = mixedMoment B node1526 node1526Labels := by
  calc
    mixedMoment B raw25783 raw25783Labels = mixedMoment B raw25783step0 raw25783step0Labels := by
      have hz : ∀ j, raw25783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25783step0 = (fun i j => raw25783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25783step0 raw25783; decide +kernel
      have hl : raw25783step0Labels = raw25783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25783 raw25783Labels permutation346 hz
    mixedMoment B raw25783step0 raw25783step0Labels = mixedMoment B raw25783step1 raw25783step1Labels := by
      have hz : ∀ j, raw25783step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25783step1 = (fun i j => raw25783step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25783step1 raw25783step0; decide +kernel
      have hl : raw25783step1Labels = raw25783step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25783step0 raw25783step0Labels permutation56 hz
    mixedMoment B raw25783step1 raw25783step1Labels = mixedMoment B raw25783step2 raw25783step2Labels := by
      have ha : raw25783step2 = (fun i j => raw25783step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25783step2 raw25783step1; decide +kernel
      have hl : raw25783step2Labels = raw25783step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25783step1 raw25783step1Labels permutation11 permutation7
    mixedMoment B raw25783step2 raw25783step2Labels = mixedMoment B raw25783step3 raw25783step3Labels := by
      have ha : raw25783step3 = -raw25783step2 := by apply Matrix.ext; change ∀ i j, raw25783step3 i j = -(raw25783step2 i j); unfold raw25783step3 raw25783step2; decide +kernel
      have hl : raw25783step3Labels = raw25783step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25783step3 raw25783step3Labels = mixedMoment B raw25783step4 raw25783step4Labels := by
      have ha : raw25783step4 = raw25783step3 := by apply Matrix.ext; unfold raw25783step4 raw25783step3; decide +kernel
      have hl : raw25783step3Labels = labelEmbedding1 ∘ raw25783step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25783step3 raw25783step3Labels raw25783step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1526 node1526Labels := by rfl

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

theorem canonical25785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25785 raw25785Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw25785 raw25785Labels = mixedMoment B raw25785step0 raw25785step0Labels := by
      have hz : ∀ j, raw25785 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25785step0 = (fun i j => raw25785 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25785step0 raw25785; decide +kernel
      have hl : raw25785step0Labels = raw25785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25785 raw25785Labels permutation265 hz
    mixedMoment B raw25785step0 raw25785step0Labels = mixedMoment B raw25785step1 raw25785step1Labels := by
      have ha : raw25785step1 = (fun i j => raw25785step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25785step1 raw25785step0; decide +kernel
      have hl : raw25785step1Labels = raw25785step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25785step0 raw25785step0Labels permutation35 permutation7
    mixedMoment B raw25785step1 raw25785step1Labels = mixedMoment B raw25785step2 raw25785step2Labels := by
      have ha : raw25785step2 = -raw25785step1 := by apply Matrix.ext; change ∀ i j, raw25785step2 i j = -(raw25785step1 i j); unfold raw25785step2 raw25785step1; decide +kernel
      have hl : raw25785step2Labels = raw25785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25785step2 raw25785step2Labels = mixedMoment B raw25785step3 raw25785step3Labels := by
      have ha : raw25785step3 = raw25785step2 := by apply Matrix.ext; unfold raw25785step3 raw25785step2; decide +kernel
      have hl : raw25785step2Labels = labelEmbedding1 ∘ raw25785step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25785step2 raw25785step2Labels raw25785step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

theorem canonical25786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25786 raw25786Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw25786 raw25786Labels = mixedMoment B raw25786step0 raw25786step0Labels := by
      have hz : ∀ j, raw25786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25786step0 = (fun i j => raw25786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25786step0 raw25786; decide +kernel
      have hl : raw25786step0Labels = raw25786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25786 raw25786Labels permutation346 hz
    mixedMoment B raw25786step0 raw25786step0Labels = mixedMoment B raw25786step1 raw25786step1Labels := by
      have hz : ∀ j, raw25786step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25786step1 = (fun i j => raw25786step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25786step1 raw25786step0; decide +kernel
      have hl : raw25786step1Labels = raw25786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25786step0 raw25786step0Labels permutation56 hz
    mixedMoment B raw25786step1 raw25786step1Labels = mixedMoment B raw25786step2 raw25786step2Labels := by
      have ha : raw25786step2 = (fun i j => raw25786step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25786step2 raw25786step1; decide +kernel
      have hl : raw25786step2Labels = raw25786step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25786step1 raw25786step1Labels permutation11 permutation7
    mixedMoment B raw25786step2 raw25786step2Labels = mixedMoment B raw25786step3 raw25786step3Labels := by
      have ha : raw25786step3 = -raw25786step2 := by apply Matrix.ext; change ∀ i j, raw25786step3 i j = -(raw25786step2 i j); unfold raw25786step3 raw25786step2; decide +kernel
      have hl : raw25786step3Labels = raw25786step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25786step3 raw25786step3Labels = mixedMoment B raw25786step4 raw25786step4Labels := by
      have ha : raw25786step4 = raw25786step3 := by apply Matrix.ext; unfold raw25786step4 raw25786step3; decide +kernel
      have hl : raw25786step3Labels = labelEmbedding1 ∘ raw25786step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25786step3 raw25786step3Labels raw25786step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

theorem canonical25787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25787 raw25787Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw25787 raw25787Labels = mixedMoment B raw25787step0 raw25787step0Labels := by
      have hz : ∀ j, raw25787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25787step0 = (fun i j => raw25787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25787step0 raw25787; decide +kernel
      have hl : raw25787step0Labels = raw25787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25787 raw25787Labels permutation346 hz
    mixedMoment B raw25787step0 raw25787step0Labels = mixedMoment B raw25787step1 raw25787step1Labels := by
      have hz : ∀ j, raw25787step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25787step1 = (fun i j => raw25787step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25787step1 raw25787step0; decide +kernel
      have hl : raw25787step1Labels = raw25787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25787step0 raw25787step0Labels permutation56 hz
    mixedMoment B raw25787step1 raw25787step1Labels = mixedMoment B raw25787step2 raw25787step2Labels := by
      have ha : raw25787step2 = (fun i j => raw25787step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25787step2 raw25787step1; decide +kernel
      have hl : raw25787step2Labels = raw25787step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25787step1 raw25787step1Labels permutation11 permutation7
    mixedMoment B raw25787step2 raw25787step2Labels = mixedMoment B raw25787step3 raw25787step3Labels := by
      have ha : raw25787step3 = -raw25787step2 := by apply Matrix.ext; change ∀ i j, raw25787step3 i j = -(raw25787step2 i j); unfold raw25787step3 raw25787step2; decide +kernel
      have hl : raw25787step3Labels = raw25787step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25787step3 raw25787step3Labels = mixedMoment B raw25787step4 raw25787step4Labels := by
      have ha : raw25787step4 = raw25787step3 := by apply Matrix.ext; unfold raw25787step4 raw25787step3; decide +kernel
      have hl : raw25787step3Labels = labelEmbedding1 ∘ raw25787step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25787step3 raw25787step3Labels raw25787step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical25788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25788 raw25788Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw25788 raw25788Labels = mixedMoment B raw25788step0 raw25788step0Labels := by
      have hz : ∀ j, raw25788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25788step0 = (fun i j => raw25788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25788step0 raw25788; decide +kernel
      have hl : raw25788step0Labels = raw25788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25788 raw25788Labels permutation346 hz
    mixedMoment B raw25788step0 raw25788step0Labels = mixedMoment B raw25788step1 raw25788step1Labels := by
      have hz : ∀ j, raw25788step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25788step1 = (fun i j => raw25788step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25788step1 raw25788step0; decide +kernel
      have hl : raw25788step1Labels = raw25788step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25788step0 raw25788step0Labels permutation56 hz
    mixedMoment B raw25788step1 raw25788step1Labels = mixedMoment B raw25788step2 raw25788step2Labels := by
      have ha : raw25788step2 = (fun i j => raw25788step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25788step2 raw25788step1; decide +kernel
      have hl : raw25788step2Labels = raw25788step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25788step1 raw25788step1Labels permutation11 permutation7
    mixedMoment B raw25788step2 raw25788step2Labels = mixedMoment B raw25788step3 raw25788step3Labels := by
      have ha : raw25788step3 = -raw25788step2 := by apply Matrix.ext; change ∀ i j, raw25788step3 i j = -(raw25788step2 i j); unfold raw25788step3 raw25788step2; decide +kernel
      have hl : raw25788step3Labels = raw25788step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25788step3 raw25788step3Labels = mixedMoment B raw25788step4 raw25788step4Labels := by
      have ha : raw25788step4 = raw25788step3 := by apply Matrix.ext; unfold raw25788step4 raw25788step3; decide +kernel
      have hl : raw25788step3Labels = labelEmbedding1 ∘ raw25788step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25788step3 raw25788step3Labels raw25788step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

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

theorem canonical25790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25790 raw25790Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw25790 raw25790Labels = mixedMoment B raw25790step0 raw25790step0Labels := by
      have hz : ∀ j, raw25790 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25790step0 = (fun i j => raw25790 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25790step0 raw25790; decide +kernel
      have hl : raw25790step0Labels = raw25790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25790 raw25790Labels permutation265 hz
    mixedMoment B raw25790step0 raw25790step0Labels = mixedMoment B raw25790step1 raw25790step1Labels := by
      have ha : raw25790step1 = (fun i j => raw25790step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25790step1 raw25790step0; decide +kernel
      have hl : raw25790step1Labels = raw25790step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25790step0 raw25790step0Labels permutation35 permutation7
    mixedMoment B raw25790step1 raw25790step1Labels = mixedMoment B raw25790step2 raw25790step2Labels := by
      have ha : raw25790step2 = -raw25790step1 := by apply Matrix.ext; change ∀ i j, raw25790step2 i j = -(raw25790step1 i j); unfold raw25790step2 raw25790step1; decide +kernel
      have hl : raw25790step2Labels = raw25790step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25790step2 raw25790step2Labels = mixedMoment B raw25790step3 raw25790step3Labels := by
      have ha : raw25790step3 = raw25790step2 := by apply Matrix.ext; unfold raw25790step3 raw25790step2; decide +kernel
      have hl : raw25790step2Labels = labelEmbedding1 ∘ raw25790step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25790step2 raw25790step2Labels raw25790step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

theorem canonical25791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25791 raw25791Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw25791 raw25791Labels = mixedMoment B raw25791step0 raw25791step0Labels := by
      have hz : ∀ j, raw25791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25791step0 = (fun i j => raw25791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25791step0 raw25791; decide +kernel
      have hl : raw25791step0Labels = raw25791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25791 raw25791Labels permutation346 hz
    mixedMoment B raw25791step0 raw25791step0Labels = mixedMoment B raw25791step1 raw25791step1Labels := by
      have hz : ∀ j, raw25791step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25791step1 = (fun i j => raw25791step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25791step1 raw25791step0; decide +kernel
      have hl : raw25791step1Labels = raw25791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25791step0 raw25791step0Labels permutation56 hz
    mixedMoment B raw25791step1 raw25791step1Labels = mixedMoment B raw25791step2 raw25791step2Labels := by
      have ha : raw25791step2 = (fun i j => raw25791step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25791step2 raw25791step1; decide +kernel
      have hl : raw25791step2Labels = raw25791step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25791step1 raw25791step1Labels permutation11 permutation7
    mixedMoment B raw25791step2 raw25791step2Labels = mixedMoment B raw25791step3 raw25791step3Labels := by
      have ha : raw25791step3 = -raw25791step2 := by apply Matrix.ext; change ∀ i j, raw25791step3 i j = -(raw25791step2 i j); unfold raw25791step3 raw25791step2; decide +kernel
      have hl : raw25791step3Labels = raw25791step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25791step3 raw25791step3Labels = mixedMoment B raw25791step4 raw25791step4Labels := by
      have ha : raw25791step4 = raw25791step3 := by apply Matrix.ext; unfold raw25791step4 raw25791step3; decide +kernel
      have hl : raw25791step3Labels = labelEmbedding1 ∘ raw25791step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25791step3 raw25791step3Labels raw25791step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

theorem canonical25792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25792 raw25792Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw25792 raw25792Labels = mixedMoment B raw25792step0 raw25792step0Labels := by
      have hz : ∀ j, raw25792 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25792step0 = (fun i j => raw25792 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25792step0 raw25792; decide +kernel
      have hl : raw25792step0Labels = raw25792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25792 raw25792Labels permutation520 hz
    mixedMoment B raw25792step0 raw25792step0Labels = mixedMoment B raw25792step1 raw25792step1Labels := by
      have hz : ∀ j, raw25792step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25792step1 = (fun i j => raw25792step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25792step1 raw25792step0; decide +kernel
      have hl : raw25792step1Labels = raw25792step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25792step0 raw25792step0Labels permutation80 hz
    mixedMoment B raw25792step1 raw25792step1Labels = mixedMoment B raw25792step2 raw25792step2Labels := by
      have hz : ∀ j, raw25792step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25792step2 = (fun i j => raw25792step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25792step2 raw25792step1; decide +kernel
      have hl : raw25792step2Labels = raw25792step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25792step1 raw25792step1Labels permutation14 hz
    mixedMoment B raw25792step2 raw25792step2Labels = mixedMoment B raw25792step3 raw25792step3Labels := by
      have ha : raw25792step3 = (fun i j => raw25792step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25792step3 raw25792step2; decide +kernel
      have hl : raw25792step3Labels = raw25792step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25792step2 raw25792step2Labels permutation3 permutation7
    mixedMoment B raw25792step3 raw25792step3Labels = mixedMoment B raw25792step4 raw25792step4Labels := by
      have ha : raw25792step4 = -raw25792step3 := by apply Matrix.ext; change ∀ i j, raw25792step4 i j = -(raw25792step3 i j); unfold raw25792step4 raw25792step3; decide +kernel
      have hl : raw25792step4Labels = raw25792step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25792step4 raw25792step4Labels = mixedMoment B raw25792step5 raw25792step5Labels := by
      have ha : raw25792step5 = raw25792step4 := by apply Matrix.ext; unfold raw25792step5 raw25792step4; decide +kernel
      have hl : raw25792step4Labels = labelEmbedding1 ∘ raw25792step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25792step4 raw25792step4Labels raw25792step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

theorem canonical25848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25848 raw25848Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw25848 raw25848Labels = mixedMoment B raw25848step0 raw25848step0Labels := by
      have hz : ∀ j, raw25848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25848step0 = (fun i j => raw25848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25848step0 raw25848; decide +kernel
      have hl : raw25848step0Labels = raw25848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25848 raw25848Labels permutation346 hz
    mixedMoment B raw25848step0 raw25848step0Labels = mixedMoment B raw25848step1 raw25848step1Labels := by
      have hz : ∀ j, raw25848step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25848step1 = (fun i j => raw25848step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25848step1 raw25848step0; decide +kernel
      have hl : raw25848step1Labels = raw25848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25848step0 raw25848step0Labels permutation56 hz
    mixedMoment B raw25848step1 raw25848step1Labels = mixedMoment B raw25848step2 raw25848step2Labels := by
      have ha : raw25848step2 = (fun i j => raw25848step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25848step2 raw25848step1; decide +kernel
      have hl : raw25848step2Labels = raw25848step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25848step1 raw25848step1Labels permutation10 permutation2
    _ = mixedMoment B node1075 node1075Labels := by rfl

theorem canonical25849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25849 raw25849Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw25849 raw25849Labels = mixedMoment B raw25849step0 raw25849step0Labels := by
      have hz : ∀ j, raw25849 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25849step0 = (fun i j => raw25849 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25849step0 raw25849; decide +kernel
      have hl : raw25849step0Labels = raw25849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25849 raw25849Labels permutation346 hz
    mixedMoment B raw25849step0 raw25849step0Labels = mixedMoment B raw25849step1 raw25849step1Labels := by
      have ha : raw25849step1 = (fun i j => raw25849step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25849step1 raw25849step0; decide +kernel
      have hl : raw25849step1Labels = raw25849step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25849step0 raw25849step0Labels permutation34 permutation2
    _ = mixedMoment B node2048 node2048Labels := by rfl

theorem canonical25850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25850 raw25850Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw25850 raw25850Labels = mixedMoment B raw25850step0 raw25850step0Labels := by
      have hz : ∀ j, raw25850 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25850step0 = (fun i j => raw25850 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25850step0 raw25850; decide +kernel
      have hl : raw25850step0Labels = raw25850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25850 raw25850Labels permutation265 hz
    mixedMoment B raw25850step0 raw25850step0Labels = mixedMoment B raw25850step1 raw25850step1Labels := by
      have ha : raw25850step1 = (fun i j => raw25850step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25850step1 raw25850step0; decide +kernel
      have hl : raw25850step1Labels = raw25850step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25850step0 raw25850step0Labels permutation34 permutation2
    _ = mixedMoment B node2048 node2048Labels := by rfl

theorem canonical25851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25851 raw25851Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw25851 raw25851Labels = mixedMoment B raw25851step0 raw25851step0Labels := by
      have hz : ∀ j, raw25851 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25851step0 = (fun i j => raw25851 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25851step0 raw25851; decide +kernel
      have hl : raw25851step0Labels = raw25851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25851 raw25851Labels permutation346 hz
    mixedMoment B raw25851step0 raw25851step0Labels = mixedMoment B raw25851step1 raw25851step1Labels := by
      have hz : ∀ j, raw25851step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25851step1 = (fun i j => raw25851step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25851step1 raw25851step0; decide +kernel
      have hl : raw25851step1Labels = raw25851step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25851step0 raw25851step0Labels permutation56 hz
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical25852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25852 raw25852Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw25852 raw25852Labels = mixedMoment B raw25852step0 raw25852step0Labels := by
      have hz : ∀ j, raw25852 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25852step0 = (fun i j => raw25852 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25852step0 raw25852; decide +kernel
      have hl : raw25852step0Labels = raw25852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25852 raw25852Labels permutation346 hz
    mixedMoment B raw25852step0 raw25852step0Labels = mixedMoment B raw25852step1 raw25852step1Labels := by
      have hz : ∀ j, raw25852step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25852step1 = (fun i j => raw25852step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25852step1 raw25852step0; decide +kernel
      have hl : raw25852step1Labels = raw25852step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25852step0 raw25852step0Labels permutation56 hz
    mixedMoment B raw25852step1 raw25852step1Labels = mixedMoment B raw25852step2 raw25852step2Labels := by
      have ha : raw25852step2 = (fun i j => raw25852step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25852step2 raw25852step1; decide +kernel
      have hl : raw25852step2Labels = raw25852step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25852step1 raw25852step1Labels permutation10 permutation2
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical25853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25853 raw25853Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw25853 raw25853Labels = mixedMoment B raw25853step0 raw25853step0Labels := by
      have hz : ∀ j, raw25853 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25853step0 = (fun i j => raw25853 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25853step0 raw25853; decide +kernel
      have hl : raw25853step0Labels = raw25853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25853 raw25853Labels permutation346 hz
    mixedMoment B raw25853step0 raw25853step0Labels = mixedMoment B raw25853step1 raw25853step1Labels := by
      have hz : ∀ j, raw25853step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25853step1 = (fun i j => raw25853step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25853step1 raw25853step0; decide +kernel
      have hl : raw25853step1Labels = raw25853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25853step0 raw25853step0Labels permutation56 hz
    mixedMoment B raw25853step1 raw25853step1Labels = mixedMoment B raw25853step2 raw25853step2Labels := by
      have ha : raw25853step2 = (fun i j => raw25853step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25853step2 raw25853step1; decide +kernel
      have hl : raw25853step2Labels = raw25853step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25853step1 raw25853step1Labels permutation10 permutation2
    _ = mixedMoment B node2288 node2288Labels := by rfl

theorem canonical25854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25854 raw25854Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw25854 raw25854Labels = mixedMoment B raw25854step0 raw25854step0Labels := by
      have hz : ∀ j, raw25854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25854step0 = (fun i j => raw25854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25854step0 raw25854; decide +kernel
      have hl : raw25854step0Labels = raw25854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25854 raw25854Labels permutation346 hz
    mixedMoment B raw25854step0 raw25854step0Labels = mixedMoment B raw25854step1 raw25854step1Labels := by
      have hz : ∀ j, raw25854step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25854step1 = (fun i j => raw25854step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25854step1 raw25854step0; decide +kernel
      have hl : raw25854step1Labels = raw25854step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25854step0 raw25854step0Labels permutation56 hz
    mixedMoment B raw25854step1 raw25854step1Labels = mixedMoment B raw25854step2 raw25854step2Labels := by
      have ha : raw25854step2 = (fun i j => raw25854step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25854step2 raw25854step1; decide +kernel
      have hl : raw25854step2Labels = raw25854step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25854step1 raw25854step1Labels permutation10 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

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

theorem canonical25915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25915 raw25915Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw25915 raw25915Labels = mixedMoment B raw25915step0 raw25915step0Labels := by
      have hz : ∀ j, raw25915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25915step0 = (fun i j => raw25915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25915step0 raw25915; decide +kernel
      have hl : raw25915step0Labels = raw25915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25915 raw25915Labels permutation346 hz
    mixedMoment B raw25915step0 raw25915step0Labels = mixedMoment B raw25915step1 raw25915step1Labels := by
      have hz : ∀ j, raw25915step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25915step1 = (fun i j => raw25915step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25915step1 raw25915step0; decide +kernel
      have hl : raw25915step1Labels = raw25915step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25915step0 raw25915step0Labels permutation56 hz
    mixedMoment B raw25915step1 raw25915step1Labels = mixedMoment B raw25915step2 raw25915step2Labels := by
      have ha : raw25915step2 = (fun i j => raw25915step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25915step2 raw25915step1; decide +kernel
      have hl : raw25915step2Labels = raw25915step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25915step1 raw25915step1Labels permutation10 permutation2
    _ = mixedMoment B node1074 node1074Labels := by rfl

theorem canonical25916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25916 raw25916Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw25916 raw25916Labels = mixedMoment B raw25916step0 raw25916step0Labels := by
      have hz : ∀ j, raw25916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25916step0 = (fun i j => raw25916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25916step0 raw25916; decide +kernel
      have hl : raw25916step0Labels = raw25916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25916 raw25916Labels permutation346 hz
    mixedMoment B raw25916step0 raw25916step0Labels = mixedMoment B raw25916step1 raw25916step1Labels := by
      have ha : raw25916step1 = (fun i j => raw25916step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25916step1 raw25916step0; decide +kernel
      have hl : raw25916step1Labels = raw25916step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25916step0 raw25916step0Labels permutation34 permutation2
    _ = mixedMoment B node2047 node2047Labels := by rfl

theorem canonical25917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25917 raw25917Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw25917 raw25917Labels = mixedMoment B raw25917step0 raw25917step0Labels := by
      have hz : ∀ j, raw25917 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25917step0 = (fun i j => raw25917 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25917step0 raw25917; decide +kernel
      have hl : raw25917step0Labels = raw25917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25917 raw25917Labels permutation265 hz
    mixedMoment B raw25917step0 raw25917step0Labels = mixedMoment B raw25917step1 raw25917step1Labels := by
      have ha : raw25917step1 = (fun i j => raw25917step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25917step1 raw25917step0; decide +kernel
      have hl : raw25917step1Labels = raw25917step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25917step0 raw25917step0Labels permutation34 permutation2
    _ = mixedMoment B node2047 node2047Labels := by rfl

theorem canonical25918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25918 raw25918Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw25918 raw25918Labels = mixedMoment B raw25918step0 raw25918step0Labels := by
      have hz : ∀ j, raw25918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25918step0 = (fun i j => raw25918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25918step0 raw25918; decide +kernel
      have hl : raw25918step0Labels = raw25918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25918 raw25918Labels permutation346 hz
    mixedMoment B raw25918step0 raw25918step0Labels = mixedMoment B raw25918step1 raw25918step1Labels := by
      have hz : ∀ j, raw25918step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25918step1 = (fun i j => raw25918step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25918step1 raw25918step0; decide +kernel
      have hl : raw25918step1Labels = raw25918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25918step0 raw25918step0Labels permutation56 hz
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical25919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25919 raw25919Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw25919 raw25919Labels = mixedMoment B raw25919step0 raw25919step0Labels := by
      have hz : ∀ j, raw25919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25919step0 = (fun i j => raw25919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25919step0 raw25919; decide +kernel
      have hl : raw25919step0Labels = raw25919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25919 raw25919Labels permutation346 hz
    mixedMoment B raw25919step0 raw25919step0Labels = mixedMoment B raw25919step1 raw25919step1Labels := by
      have hz : ∀ j, raw25919step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25919step1 = (fun i j => raw25919step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25919step1 raw25919step0; decide +kernel
      have hl : raw25919step1Labels = raw25919step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25919step0 raw25919step0Labels permutation56 hz
    mixedMoment B raw25919step1 raw25919step1Labels = mixedMoment B raw25919step2 raw25919step2Labels := by
      have ha : raw25919step2 = (fun i j => raw25919step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25919step2 raw25919step1; decide +kernel
      have hl : raw25919step2Labels = raw25919step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25919step1 raw25919step1Labels permutation10 permutation2
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical25920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25920 raw25920Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw25920 raw25920Labels = mixedMoment B raw25920step0 raw25920step0Labels := by
      have hz : ∀ j, raw25920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25920step0 = (fun i j => raw25920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25920step0 raw25920; decide +kernel
      have hl : raw25920step0Labels = raw25920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25920 raw25920Labels permutation346 hz
    mixedMoment B raw25920step0 raw25920step0Labels = mixedMoment B raw25920step1 raw25920step1Labels := by
      have hz : ∀ j, raw25920step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25920step1 = (fun i j => raw25920step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25920step1 raw25920step0; decide +kernel
      have hl : raw25920step1Labels = raw25920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25920step0 raw25920step0Labels permutation56 hz
    mixedMoment B raw25920step1 raw25920step1Labels = mixedMoment B raw25920step2 raw25920step2Labels := by
      have ha : raw25920step2 = (fun i j => raw25920step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25920step2 raw25920step1; decide +kernel
      have hl : raw25920step2Labels = raw25920step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25920step1 raw25920step1Labels permutation10 permutation2
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical25921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25921 raw25921Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw25921 raw25921Labels = mixedMoment B raw25921step0 raw25921step0Labels := by
      have hz : ∀ j, raw25921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25921step0 = (fun i j => raw25921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25921step0 raw25921; decide +kernel
      have hl : raw25921step0Labels = raw25921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25921 raw25921Labels permutation346 hz
    mixedMoment B raw25921step0 raw25921step0Labels = mixedMoment B raw25921step1 raw25921step1Labels := by
      have hz : ∀ j, raw25921step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25921step1 = (fun i j => raw25921step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25921step1 raw25921step0; decide +kernel
      have hl : raw25921step1Labels = raw25921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25921step0 raw25921step0Labels permutation56 hz
    mixedMoment B raw25921step1 raw25921step1Labels = mixedMoment B raw25921step2 raw25921step2Labels := by
      have ha : raw25921step2 = (fun i j => raw25921step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25921step2 raw25921step1; decide +kernel
      have hl : raw25921step2Labels = raw25921step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25921step1 raw25921step1Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

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

theorem canonical25977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25977 raw25977Labels = mixedMoment B node1503 node1503Labels := by
  calc
    mixedMoment B raw25977 raw25977Labels = mixedMoment B raw25977step0 raw25977step0Labels := by
      have hz : ∀ j, raw25977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25977step0 = (fun i j => raw25977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25977step0 raw25977; decide +kernel
      have hl : raw25977step0Labels = raw25977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25977 raw25977Labels permutation346 hz
    mixedMoment B raw25977step0 raw25977step0Labels = mixedMoment B raw25977step1 raw25977step1Labels := by
      have ha : raw25977step1 = (fun i j => raw25977step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25977step1 raw25977step0; decide +kernel
      have hl : raw25977step1Labels = raw25977step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25977step0 raw25977step0Labels permutation32 permutation7
    mixedMoment B raw25977step1 raw25977step1Labels = mixedMoment B raw25977step2 raw25977step2Labels := by
      have ha : raw25977step2 = -raw25977step1 := by apply Matrix.ext; change ∀ i j, raw25977step2 i j = -(raw25977step1 i j); unfold raw25977step2 raw25977step1; decide +kernel
      have hl : raw25977step2Labels = raw25977step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25977step2 raw25977step2Labels = mixedMoment B raw25977step3 raw25977step3Labels := by
      have ha : raw25977step3 = raw25977step2 := by apply Matrix.ext; unfold raw25977step3 raw25977step2; decide +kernel
      have hl : raw25977step2Labels = labelEmbedding1 ∘ raw25977step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25977step2 raw25977step2Labels raw25977step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1503 node1503Labels := by rfl

theorem canonical25978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25978 raw25978Labels = mixedMoment B node1662 node1662Labels := by
  calc
    mixedMoment B raw25978 raw25978Labels = mixedMoment B raw25978step0 raw25978step0Labels := by
      have ha : raw25978step0 = (fun i j => raw25978 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25978step0 raw25978; decide +kernel
      have hl : raw25978step0Labels = raw25978Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25978 raw25978Labels permutation176 permutation7
    mixedMoment B raw25978step0 raw25978step0Labels = mixedMoment B raw25978step1 raw25978step1Labels := by
      have ha : raw25978step1 = -raw25978step0 := by apply Matrix.ext; change ∀ i j, raw25978step1 i j = -(raw25978step0 i j); unfold raw25978step1 raw25978step0; decide +kernel
      have hl : raw25978step1Labels = raw25978step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25978step1 raw25978step1Labels = mixedMoment B raw25978step2 raw25978step2Labels := by
      have ha : raw25978step2 = raw25978step1 := by apply Matrix.ext; unfold raw25978step2 raw25978step1; decide +kernel
      have hl : raw25978step1Labels = labelEmbedding1 ∘ raw25978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25978step1 raw25978step1Labels raw25978step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1662 node1662Labels := by rfl

theorem canonical25979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25979 raw25979Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw25979 raw25979Labels = mixedMoment B raw25979step0 raw25979step0Labels := by
      have hz : ∀ j, raw25979 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25979step0 = (fun i j => raw25979 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25979step0 raw25979; decide +kernel
      have hl : raw25979step0Labels = raw25979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25979 raw25979Labels permutation520 hz
    mixedMoment B raw25979step0 raw25979step0Labels = mixedMoment B raw25979step1 raw25979step1Labels := by
      have hz : ∀ j, raw25979step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25979step1 = (fun i j => raw25979step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25979step1 raw25979step0; decide +kernel
      have hl : raw25979step1Labels = raw25979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25979step0 raw25979step0Labels permutation80 hz
    mixedMoment B raw25979step1 raw25979step1Labels = mixedMoment B raw25979step2 raw25979step2Labels := by
      have ha : raw25979step2 = (fun i j => raw25979step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25979step2 raw25979step1; decide +kernel
      have hl : raw25979step2Labels = raw25979step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25979step1 raw25979step1Labels permutation8 permutation7
    mixedMoment B raw25979step2 raw25979step2Labels = mixedMoment B raw25979step3 raw25979step3Labels := by
      have ha : raw25979step3 = -raw25979step2 := by apply Matrix.ext; change ∀ i j, raw25979step3 i j = -(raw25979step2 i j); unfold raw25979step3 raw25979step2; decide +kernel
      have hl : raw25979step3Labels = raw25979step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25979step3 raw25979step3Labels = mixedMoment B raw25979step4 raw25979step4Labels := by
      have ha : raw25979step4 = raw25979step3 := by apply Matrix.ext; unfold raw25979step4 raw25979step3; decide +kernel
      have hl : raw25979step3Labels = labelEmbedding1 ∘ raw25979step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25979step3 raw25979step3Labels raw25979step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical25980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25980 raw25980Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw25980 raw25980Labels = mixedMoment B raw25980step0 raw25980step0Labels := by
      have hz : ∀ j, raw25980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25980step0 = (fun i j => raw25980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25980step0 raw25980; decide +kernel
      have hl : raw25980step0Labels = raw25980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25980 raw25980Labels permutation346 hz
    mixedMoment B raw25980step0 raw25980step0Labels = mixedMoment B raw25980step1 raw25980step1Labels := by
      have ha : raw25980step1 = (fun i j => raw25980step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25980step1 raw25980step0; decide +kernel
      have hl : raw25980step1Labels = raw25980step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25980step0 raw25980step0Labels permutation32 permutation7
    mixedMoment B raw25980step1 raw25980step1Labels = mixedMoment B raw25980step2 raw25980step2Labels := by
      have ha : raw25980step2 = -raw25980step1 := by apply Matrix.ext; change ∀ i j, raw25980step2 i j = -(raw25980step1 i j); unfold raw25980step2 raw25980step1; decide +kernel
      have hl : raw25980step2Labels = raw25980step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25980step2 raw25980step2Labels = mixedMoment B raw25980step3 raw25980step3Labels := by
      have ha : raw25980step3 = raw25980step2 := by apply Matrix.ext; unfold raw25980step3 raw25980step2; decide +kernel
      have hl : raw25980step2Labels = labelEmbedding1 ∘ raw25980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25980step2 raw25980step2Labels raw25980step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1700 node1700Labels := by rfl

theorem canonical25981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25981 raw25981Labels = mixedMoment B node1503 node1503Labels := by
  calc
    mixedMoment B raw25981 raw25981Labels = mixedMoment B raw25981step0 raw25981step0Labels := by
      have hz : ∀ j, raw25981 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25981step0 = (fun i j => raw25981 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25981step0 raw25981; decide +kernel
      have hl : raw25981step0Labels = raw25981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25981 raw25981Labels permutation265 hz
    mixedMoment B raw25981step0 raw25981step0Labels = mixedMoment B raw25981step1 raw25981step1Labels := by
      have ha : raw25981step1 = (fun i j => raw25981step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25981step1 raw25981step0; decide +kernel
      have hl : raw25981step1Labels = raw25981step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25981step0 raw25981step0Labels permutation32 permutation7
    mixedMoment B raw25981step1 raw25981step1Labels = mixedMoment B raw25981step2 raw25981step2Labels := by
      have ha : raw25981step2 = -raw25981step1 := by apply Matrix.ext; change ∀ i j, raw25981step2 i j = -(raw25981step1 i j); unfold raw25981step2 raw25981step1; decide +kernel
      have hl : raw25981step2Labels = raw25981step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25981step2 raw25981step2Labels = mixedMoment B raw25981step3 raw25981step3Labels := by
      have ha : raw25981step3 = raw25981step2 := by apply Matrix.ext; unfold raw25981step3 raw25981step2; decide +kernel
      have hl : raw25981step2Labels = labelEmbedding1 ∘ raw25981step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25981step2 raw25981step2Labels raw25981step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1503 node1503Labels := by rfl

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

theorem canonical25983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25983 raw25983Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw25983 raw25983Labels = mixedMoment B raw25983step0 raw25983step0Labels := by
      have hz : ∀ j, raw25983 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25983step0 = (fun i j => raw25983 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25983step0 raw25983; decide +kernel
      have hl : raw25983step0Labels = raw25983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25983 raw25983Labels permutation520 hz
    mixedMoment B raw25983step0 raw25983step0Labels = mixedMoment B raw25983step1 raw25983step1Labels := by
      have hz : ∀ j, raw25983step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25983step1 = (fun i j => raw25983step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25983step1 raw25983step0; decide +kernel
      have hl : raw25983step1Labels = raw25983step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25983step0 raw25983step0Labels permutation56 hz
    mixedMoment B raw25983step1 raw25983step1Labels = mixedMoment B raw25983step2 raw25983step2Labels := by
      have ha : raw25983step2 = (fun i j => raw25983step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25983step2 raw25983step1; decide +kernel
      have hl : raw25983step2Labels = raw25983step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25983step1 raw25983step1Labels permutation8 permutation7
    mixedMoment B raw25983step2 raw25983step2Labels = mixedMoment B raw25983step3 raw25983step3Labels := by
      have ha : raw25983step3 = -raw25983step2 := by apply Matrix.ext; change ∀ i j, raw25983step3 i j = -(raw25983step2 i j); unfold raw25983step3 raw25983step2; decide +kernel
      have hl : raw25983step3Labels = raw25983step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25983step3 raw25983step3Labels = mixedMoment B raw25983step4 raw25983step4Labels := by
      have ha : raw25983step4 = raw25983step3 := by apply Matrix.ext; unfold raw25983step4 raw25983step3; decide +kernel
      have hl : raw25983step3Labels = labelEmbedding1 ∘ raw25983step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25983step3 raw25983step3Labels raw25983step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

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

theorem canonical25984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25984 raw25984Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw25984 raw25984Labels = mixedMoment B raw25984step0 raw25984step0Labels := by
      have hz : ∀ j, raw25984 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25984step0 = (fun i j => raw25984 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25984step0 raw25984; decide +kernel
      have hl : raw25984step0Labels = raw25984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25984 raw25984Labels permutation265 hz
    mixedMoment B raw25984step0 raw25984step0Labels = mixedMoment B raw25984step1 raw25984step1Labels := by
      have ha : raw25984step1 = (fun i j => raw25984step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25984step1 raw25984step0; decide +kernel
      have hl : raw25984step1Labels = raw25984step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25984step0 raw25984step0Labels permutation32 permutation7
    mixedMoment B raw25984step1 raw25984step1Labels = mixedMoment B raw25984step2 raw25984step2Labels := by
      have ha : raw25984step2 = -raw25984step1 := by apply Matrix.ext; change ∀ i j, raw25984step2 i j = -(raw25984step1 i j); unfold raw25984step2 raw25984step1; decide +kernel
      have hl : raw25984step2Labels = raw25984step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25984step2 raw25984step2Labels = mixedMoment B raw25984step3 raw25984step3Labels := by
      have ha : raw25984step3 = raw25984step2 := by apply Matrix.ext; unfold raw25984step3 raw25984step2; decide +kernel
      have hl : raw25984step2Labels = labelEmbedding1 ∘ raw25984step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25984step2 raw25984step2Labels raw25984step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1700 node1700Labels := by rfl

theorem canonical25985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25985 raw25985Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw25985 raw25985Labels = mixedMoment B raw25985step0 raw25985step0Labels := by
      have hz : ∀ j, raw25985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25985step0 = (fun i j => raw25985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25985step0 raw25985; decide +kernel
      have hl : raw25985step0Labels = raw25985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25985 raw25985Labels permutation346 hz
    mixedMoment B raw25985step0 raw25985step0Labels = mixedMoment B raw25985step1 raw25985step1Labels := by
      have hz : ∀ j, raw25985step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25985step1 = (fun i j => raw25985step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25985step1 raw25985step0; decide +kernel
      have hl : raw25985step1Labels = raw25985step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25985step0 raw25985step0Labels permutation56 hz
    mixedMoment B raw25985step1 raw25985step1Labels = mixedMoment B raw25985step2 raw25985step2Labels := by
      have ha : raw25985step2 = (fun i j => raw25985step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25985step2 raw25985step1; decide +kernel
      have hl : raw25985step2Labels = raw25985step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25985step1 raw25985step1Labels permutation10 permutation7
    mixedMoment B raw25985step2 raw25985step2Labels = mixedMoment B raw25985step3 raw25985step3Labels := by
      have ha : raw25985step3 = -raw25985step2 := by apply Matrix.ext; change ∀ i j, raw25985step3 i j = -(raw25985step2 i j); unfold raw25985step3 raw25985step2; decide +kernel
      have hl : raw25985step3Labels = raw25985step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25985step3 raw25985step3Labels = mixedMoment B raw25985step4 raw25985step4Labels := by
      have ha : raw25985step4 = raw25985step3 := by apply Matrix.ext; unfold raw25985step4 raw25985step3; decide +kernel
      have hl : raw25985step3Labels = labelEmbedding1 ∘ raw25985step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25985step3 raw25985step3Labels raw25985step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

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

theorem canonical25987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25987 raw25987Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw25987 raw25987Labels = mixedMoment B raw25987step0 raw25987step0Labels := by
      have hz : ∀ j, raw25987 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25987step0 = (fun i j => raw25987 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25987step0 raw25987; decide +kernel
      have hl : raw25987step0Labels = raw25987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25987 raw25987Labels permutation265 hz
    mixedMoment B raw25987step0 raw25987step0Labels = mixedMoment B raw25987step1 raw25987step1Labels := by
      have ha : raw25987step1 = (fun i j => raw25987step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25987step1 raw25987step0; decide +kernel
      have hl : raw25987step1Labels = raw25987step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25987step0 raw25987step0Labels permutation34 permutation7
    mixedMoment B raw25987step1 raw25987step1Labels = mixedMoment B raw25987step2 raw25987step2Labels := by
      have ha : raw25987step2 = -raw25987step1 := by apply Matrix.ext; change ∀ i j, raw25987step2 i j = -(raw25987step1 i j); unfold raw25987step2 raw25987step1; decide +kernel
      have hl : raw25987step2Labels = raw25987step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25987step2 raw25987step2Labels = mixedMoment B raw25987step3 raw25987step3Labels := by
      have ha : raw25987step3 = raw25987step2 := by apply Matrix.ext; unfold raw25987step3 raw25987step2; decide +kernel
      have hl : raw25987step2Labels = labelEmbedding1 ∘ raw25987step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25987step2 raw25987step2Labels raw25987step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

theorem canonical25988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25988 raw25988Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw25988 raw25988Labels = mixedMoment B raw25988step0 raw25988step0Labels := by
      have hz : ∀ j, raw25988 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25988step0 = (fun i j => raw25988 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25988step0 raw25988; decide +kernel
      have hl : raw25988step0Labels = raw25988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25988 raw25988Labels permutation520 hz
    mixedMoment B raw25988step0 raw25988step0Labels = mixedMoment B raw25988step1 raw25988step1Labels := by
      have hz : ∀ j, raw25988step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25988step1 = (fun i j => raw25988step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25988step1 raw25988step0; decide +kernel
      have hl : raw25988step1Labels = raw25988step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25988step0 raw25988step0Labels permutation80 hz
    mixedMoment B raw25988step1 raw25988step1Labels = mixedMoment B raw25988step2 raw25988step2Labels := by
      have hz : ∀ j, raw25988step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25988step2 = (fun i j => raw25988step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25988step2 raw25988step1; decide +kernel
      have hl : raw25988step2Labels = raw25988step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25988step1 raw25988step1Labels permutation14 hz
    mixedMoment B raw25988step2 raw25988step2Labels = mixedMoment B raw25988step3 raw25988step3Labels := by
      have ha : raw25988step3 = (fun i j => raw25988step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25988step3 raw25988step2; decide +kernel
      have hl : raw25988step3Labels = raw25988step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25988step2 raw25988step2Labels permutation2 permutation7
    mixedMoment B raw25988step3 raw25988step3Labels = mixedMoment B raw25988step4 raw25988step4Labels := by
      have ha : raw25988step4 = -raw25988step3 := by apply Matrix.ext; change ∀ i j, raw25988step4 i j = -(raw25988step3 i j); unfold raw25988step4 raw25988step3; decide +kernel
      have hl : raw25988step4Labels = raw25988step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25988step4 raw25988step4Labels = mixedMoment B raw25988step5 raw25988step5Labels := by
      have ha : raw25988step5 = raw25988step4 := by apply Matrix.ext; unfold raw25988step5 raw25988step4; decide +kernel
      have hl : raw25988step4Labels = labelEmbedding1 ∘ raw25988step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25988step4 raw25988step4Labels raw25988step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1741 node1741Labels := by rfl

theorem canonical25989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25989 raw25989Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw25989 raw25989Labels = mixedMoment B raw25989step0 raw25989step0Labels := by
      have hz : ∀ j, raw25989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25989step0 = (fun i j => raw25989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25989step0 raw25989; decide +kernel
      have hl : raw25989step0Labels = raw25989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25989 raw25989Labels permutation346 hz
    mixedMoment B raw25989step0 raw25989step0Labels = mixedMoment B raw25989step1 raw25989step1Labels := by
      have hz : ∀ j, raw25989step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25989step1 = (fun i j => raw25989step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25989step1 raw25989step0; decide +kernel
      have hl : raw25989step1Labels = raw25989step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25989step0 raw25989step0Labels permutation56 hz
    mixedMoment B raw25989step1 raw25989step1Labels = mixedMoment B raw25989step2 raw25989step2Labels := by
      have ha : raw25989step2 = (fun i j => raw25989step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25989step2 raw25989step1; decide +kernel
      have hl : raw25989step2Labels = raw25989step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25989step1 raw25989step1Labels permutation10 permutation7
    mixedMoment B raw25989step2 raw25989step2Labels = mixedMoment B raw25989step3 raw25989step3Labels := by
      have ha : raw25989step3 = -raw25989step2 := by apply Matrix.ext; change ∀ i j, raw25989step3 i j = -(raw25989step2 i j); unfold raw25989step3 raw25989step2; decide +kernel
      have hl : raw25989step3Labels = raw25989step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25989step3 raw25989step3Labels = mixedMoment B raw25989step4 raw25989step4Labels := by
      have ha : raw25989step4 = raw25989step3 := by apply Matrix.ext; unfold raw25989step4 raw25989step3; decide +kernel
      have hl : raw25989step3Labels = labelEmbedding1 ∘ raw25989step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25989step3 raw25989step3Labels raw25989step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

theorem canonical25990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25990 raw25990Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw25990 raw25990Labels = mixedMoment B raw25990step0 raw25990step0Labels := by
      have hz : ∀ j, raw25990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25990step0 = (fun i j => raw25990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25990step0 raw25990; decide +kernel
      have hl : raw25990step0Labels = raw25990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25990 raw25990Labels permutation346 hz
    mixedMoment B raw25990step0 raw25990step0Labels = mixedMoment B raw25990step1 raw25990step1Labels := by
      have hz : ∀ j, raw25990step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25990step1 = (fun i j => raw25990step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25990step1 raw25990step0; decide +kernel
      have hl : raw25990step1Labels = raw25990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25990step0 raw25990step0Labels permutation56 hz
    mixedMoment B raw25990step1 raw25990step1Labels = mixedMoment B raw25990step2 raw25990step2Labels := by
      have ha : raw25990step2 = (fun i j => raw25990step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25990step2 raw25990step1; decide +kernel
      have hl : raw25990step2Labels = raw25990step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25990step1 raw25990step1Labels permutation8 permutation7
    mixedMoment B raw25990step2 raw25990step2Labels = mixedMoment B raw25990step3 raw25990step3Labels := by
      have ha : raw25990step3 = -raw25990step2 := by apply Matrix.ext; change ∀ i j, raw25990step3 i j = -(raw25990step2 i j); unfold raw25990step3 raw25990step2; decide +kernel
      have hl : raw25990step3Labels = raw25990step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25990step3 raw25990step3Labels = mixedMoment B raw25990step4 raw25990step4Labels := by
      have ha : raw25990step4 = raw25990step3 := by apply Matrix.ext; unfold raw25990step4 raw25990step3; decide +kernel
      have hl : raw25990step3Labels = labelEmbedding1 ∘ raw25990step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25990step3 raw25990step3Labels raw25990step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

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

theorem canonical25992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25992 raw25992Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw25992 raw25992Labels = mixedMoment B raw25992step0 raw25992step0Labels := by
      have hz : ∀ j, raw25992 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25992step0 = (fun i j => raw25992 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25992step0 raw25992; decide +kernel
      have hl : raw25992step0Labels = raw25992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25992 raw25992Labels permutation265 hz
    mixedMoment B raw25992step0 raw25992step0Labels = mixedMoment B raw25992step1 raw25992step1Labels := by
      have ha : raw25992step1 = (fun i j => raw25992step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25992step1 raw25992step0; decide +kernel
      have hl : raw25992step1Labels = raw25992step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25992step0 raw25992step0Labels permutation32 permutation7
    mixedMoment B raw25992step1 raw25992step1Labels = mixedMoment B raw25992step2 raw25992step2Labels := by
      have ha : raw25992step2 = -raw25992step1 := by apply Matrix.ext; change ∀ i j, raw25992step2 i j = -(raw25992step1 i j); unfold raw25992step2 raw25992step1; decide +kernel
      have hl : raw25992step2Labels = raw25992step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25992step2 raw25992step2Labels = mixedMoment B raw25992step3 raw25992step3Labels := by
      have ha : raw25992step3 = raw25992step2 := by apply Matrix.ext; unfold raw25992step3 raw25992step2; decide +kernel
      have hl : raw25992step2Labels = labelEmbedding1 ∘ raw25992step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25992step2 raw25992step2Labels raw25992step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

theorem canonical25993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25993 raw25993Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw25993 raw25993Labels = mixedMoment B raw25993step0 raw25993step0Labels := by
      have hz : ∀ j, raw25993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25993step0 = (fun i j => raw25993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25993step0 raw25993; decide +kernel
      have hl : raw25993step0Labels = raw25993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25993 raw25993Labels permutation346 hz
    mixedMoment B raw25993step0 raw25993step0Labels = mixedMoment B raw25993step1 raw25993step1Labels := by
      have hz : ∀ j, raw25993step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25993step1 = (fun i j => raw25993step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25993step1 raw25993step0; decide +kernel
      have hl : raw25993step1Labels = raw25993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25993step0 raw25993step0Labels permutation56 hz
    mixedMoment B raw25993step1 raw25993step1Labels = mixedMoment B raw25993step2 raw25993step2Labels := by
      have ha : raw25993step2 = (fun i j => raw25993step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25993step2 raw25993step1; decide +kernel
      have hl : raw25993step2Labels = raw25993step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25993step1 raw25993step1Labels permutation8 permutation7
    mixedMoment B raw25993step2 raw25993step2Labels = mixedMoment B raw25993step3 raw25993step3Labels := by
      have ha : raw25993step3 = -raw25993step2 := by apply Matrix.ext; change ∀ i j, raw25993step3 i j = -(raw25993step2 i j); unfold raw25993step3 raw25993step2; decide +kernel
      have hl : raw25993step3Labels = raw25993step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25993step3 raw25993step3Labels = mixedMoment B raw25993step4 raw25993step4Labels := by
      have ha : raw25993step4 = raw25993step3 := by apply Matrix.ext; unfold raw25993step4 raw25993step3; decide +kernel
      have hl : raw25993step3Labels = labelEmbedding1 ∘ raw25993step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25993step3 raw25993step3Labels raw25993step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

theorem canonical25994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25994 raw25994Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw25994 raw25994Labels = mixedMoment B raw25994step0 raw25994step0Labels := by
      have hz : ∀ j, raw25994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25994step0 = (fun i j => raw25994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25994step0 raw25994; decide +kernel
      have hl : raw25994step0Labels = raw25994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25994 raw25994Labels permutation346 hz
    mixedMoment B raw25994step0 raw25994step0Labels = mixedMoment B raw25994step1 raw25994step1Labels := by
      have hz : ∀ j, raw25994step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25994step1 = (fun i j => raw25994step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25994step1 raw25994step0; decide +kernel
      have hl : raw25994step1Labels = raw25994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25994step0 raw25994step0Labels permutation56 hz
    _ = mixedMoment B node1080 node1080Labels := by rfl

theorem canonical25995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25995 raw25995Labels = mixedMoment B node598 node598Labels := by
  calc
    mixedMoment B raw25995 raw25995Labels = mixedMoment B raw25995step0 raw25995step0Labels := by
      have hz : ∀ j, raw25995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25995step0 = (fun i j => raw25995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25995step0 raw25995; decide +kernel
      have hl : raw25995step0Labels = raw25995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25995 raw25995Labels permutation346 hz
    _ = mixedMoment B node598 node598Labels := by rfl

theorem canonical25996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25996 raw25996Labels = mixedMoment B node598 node598Labels := by
  calc
    mixedMoment B raw25996 raw25996Labels = mixedMoment B raw25996step0 raw25996step0Labels := by
      have hz : ∀ j, raw25996 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25996step0 = (fun i j => raw25996 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25996step0 raw25996; decide +kernel
      have hl : raw25996step0Labels = raw25996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25996 raw25996Labels permutation265 hz
    _ = mixedMoment B node598 node598Labels := by rfl

theorem canonical25997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25997 raw25997Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw25997 raw25997Labels = mixedMoment B raw25997step0 raw25997step0Labels := by
      have hz : ∀ j, raw25997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25997step0 = (fun i j => raw25997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25997step0 raw25997; decide +kernel
      have hl : raw25997step0Labels = raw25997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25997 raw25997Labels permutation346 hz
    mixedMoment B raw25997step0 raw25997step0Labels = mixedMoment B raw25997step1 raw25997step1Labels := by
      have hz : ∀ j, raw25997step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25997step1 = (fun i j => raw25997step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25997step1 raw25997step0; decide +kernel
      have hl : raw25997step1Labels = raw25997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25997step0 raw25997step0Labels permutation56 hz
    mixedMoment B raw25997step1 raw25997step1Labels = mixedMoment B raw25997step2 raw25997step2Labels := by
      have ha : raw25997step2 = (fun i j => raw25997step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25997step2 raw25997step1; decide +kernel
      have hl : raw25997step2Labels = raw25997step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25997step1 raw25997step1Labels permutation10 permutation2
    _ = mixedMoment B node607 node607Labels := by rfl

theorem canonical25998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25998 raw25998Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw25998 raw25998Labels = mixedMoment B raw25998step0 raw25998step0Labels := by
      have hz : ∀ j, raw25998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25998step0 = (fun i j => raw25998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25998step0 raw25998; decide +kernel
      have hl : raw25998step0Labels = raw25998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25998 raw25998Labels permutation346 hz
    mixedMoment B raw25998step0 raw25998step0Labels = mixedMoment B raw25998step1 raw25998step1Labels := by
      have hz : ∀ j, raw25998step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25998step1 = (fun i j => raw25998step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25998step1 raw25998step0; decide +kernel
      have hl : raw25998step1Labels = raw25998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25998step0 raw25998step0Labels permutation56 hz
    _ = mixedMoment B node607 node607Labels := by rfl

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

theorem sound2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2279 node2279Labels = Sparse.eval nodeValue2279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2279) = mixedMoment B node2279 node2279Labels := rfl
  simpa [nodeValue2279, Sparse.eval] using hc.symm

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

theorem sound1074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1074 node1074Labels = Sparse.eval nodeValue1074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1074) = mixedMoment B node1074 node1074Labels := rfl
  simpa [nodeValue1074, Sparse.eval] using hc.symm

theorem sound1075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1075 node1075Labels = Sparse.eval nodeValue1075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1075) = mixedMoment B node1075 node1075Labels := rfl
  simpa [nodeValue1075, Sparse.eval] using hc.symm

theorem sound1076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1076 node1076Labels = Sparse.eval nodeValue1076 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1076) = mixedMoment B node1076 node1076Labels := rfl
  simpa [nodeValue1076, Sparse.eval] using hc.symm

theorem sound1080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1080 node1080Labels = Sparse.eval nodeValue1080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1080) = mixedMoment B node1080 node1080Labels := rfl
  simpa [nodeValue1080, Sparse.eval] using hc.symm

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

theorem sound1503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1503 node1503Labels = Sparse.eval nodeValue1503 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1503) = mixedMoment B node1503 node1503Labels := rfl
  simpa [nodeValue1503, Sparse.eval] using hc.symm

theorem sound1508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1508 node1508Labels = Sparse.eval nodeValue1508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1508) = mixedMoment B node1508 node1508Labels := rfl
  simpa [nodeValue1508, Sparse.eval] using hc.symm

theorem sound1509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1509 node1509Labels = Sparse.eval nodeValue1509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1509) = mixedMoment B node1509 node1509Labels := rfl
  simpa [nodeValue1509, Sparse.eval] using hc.symm

theorem sound1512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1512 node1512Labels = Sparse.eval nodeValue1512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1512) = mixedMoment B node1512 node1512Labels := rfl
  simpa [nodeValue1512, Sparse.eval] using hc.symm

theorem sound1513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1513 node1513Labels = Sparse.eval nodeValue1513 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1513) = mixedMoment B node1513 node1513Labels := rfl
  simpa [nodeValue1513, Sparse.eval] using hc.symm

theorem sound1519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1519 node1519Labels = Sparse.eval nodeValue1519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1519) = mixedMoment B node1519 node1519Labels := rfl
  simpa [nodeValue1519, Sparse.eval] using hc.symm

theorem sound1520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1520 node1520Labels = Sparse.eval nodeValue1520 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1520) = mixedMoment B node1520 node1520Labels := rfl
  simpa [nodeValue1520, Sparse.eval] using hc.symm

theorem sound1525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1525 node1525Labels = Sparse.eval nodeValue1525 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1525) = mixedMoment B node1525 node1525Labels := rfl
  simpa [nodeValue1525, Sparse.eval] using hc.symm

theorem sound1526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1526 node1526Labels = Sparse.eval nodeValue1526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1526) = mixedMoment B node1526 node1526Labels := rfl
  simpa [nodeValue1526, Sparse.eval] using hc.symm

theorem sound1530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1530 node1530Labels = Sparse.eval nodeValue1530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1530) = mixedMoment B node1530 node1530Labels := rfl
  simpa [nodeValue1530, Sparse.eval] using hc.symm

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

theorem zero1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = 0 := by
  exact mixedMoment_order_one B hB node1727 node1727Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1668 node1668Labels = Sparse.eval nodeValue1668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1668) = mixedMoment B node1668 node1668Labels := rfl
  simpa [nodeValue1668, Sparse.eval] using hc.symm

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

theorem sound1681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1681 node1681Labels = Sparse.eval nodeValue1681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1681) = mixedMoment B node1681 node1681Labels := rfl
  simpa [nodeValue1681, Sparse.eval] using hc.symm

theorem sound1682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1682 node1682Labels = Sparse.eval nodeValue1682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1682) = mixedMoment B node1682 node1682Labels := rfl
  simpa [nodeValue1682, Sparse.eval] using hc.symm

theorem sound1686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1686 node1686Labels = Sparse.eval nodeValue1686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1686) = mixedMoment B node1686 node1686Labels := rfl
  simpa [nodeValue1686, Sparse.eval] using hc.symm

theorem sound1700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1700 node1700Labels = Sparse.eval nodeValue1700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1700) = mixedMoment B node1700 node1700Labels := rfl
  simpa [nodeValue1700, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

theorem sound1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1709 node1709Labels = Sparse.eval nodeValue1709 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1709) = mixedMoment B node1709 node1709Labels := rfl
  simpa [nodeValue1709, Sparse.eval] using hc.symm

theorem sound1710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1710 node1710Labels = Sparse.eval nodeValue1710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1710) = mixedMoment B node1710 node1710Labels := rfl
  simpa [nodeValue1710, Sparse.eval] using hc.symm

theorem sound1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1714 node1714Labels = Sparse.eval nodeValue1714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1714) = mixedMoment B node1714 node1714Labels := rfl
  simpa [nodeValue1714, Sparse.eval] using hc.symm

theorem sound1715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1715 node1715Labels = Sparse.eval nodeValue1715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1715) = mixedMoment B node1715 node1715Labels := rfl
  simpa [nodeValue1715, Sparse.eval] using hc.symm

theorem sound1716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1716 node1716Labels = Sparse.eval nodeValue1716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1716) = mixedMoment B node1716 node1716Labels := rfl
  simpa [nodeValue1716, Sparse.eval] using hc.symm

theorem sound1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = Sparse.eval nodeValue1727 (mixedVector B) := by
  simpa only [nodeValue1727, Sparse.eval_nil] using zero1727 B _hB _hF

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

theorem sound1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1728 node1728Labels = Sparse.eval nodeValue1728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1728) = mixedMoment B node1728 node1728Labels := rfl
  simpa [nodeValue1728, Sparse.eval] using hc.symm

theorem sound1729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1729 node1729Labels = Sparse.eval nodeValue1729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1729) = mixedMoment B node1729 node1729Labels := rfl
  simpa [nodeValue1729, Sparse.eval] using hc.symm

theorem sound1730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1730 node1730Labels = Sparse.eval nodeValue1730 (mixedVector B) := by
  simpa only [nodeValue1730, Sparse.eval_nil] using zero1730 B _hB _hF

theorem sound1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1738 node1738Labels = Sparse.eval nodeValue1738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1738) = mixedMoment B node1738 node1738Labels := rfl
  simpa [nodeValue1738, Sparse.eval] using hc.symm

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

theorem sound1740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1740 node1740Labels = Sparse.eval nodeValue1740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1740) = mixedMoment B node1740 node1740Labels := rfl
  simpa [nodeValue1740, Sparse.eval] using hc.symm

theorem sound1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1741 node1741Labels = Sparse.eval nodeValue1741 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1741) = mixedMoment B node1741 node1741Labels := rfl
  simpa [nodeValue1741, Sparse.eval] using hc.symm

theorem sound1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1745 node1745Labels = Sparse.eval nodeValue1745 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1745) = mixedMoment B node1745 node1745Labels := rfl
  simpa [nodeValue1745, Sparse.eval] using hc.symm

theorem sound1746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1746 node1746Labels = Sparse.eval nodeValue1746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1746) = mixedMoment B node1746 node1746Labels := rfl
  simpa [nodeValue1746, Sparse.eval] using hc.symm

theorem sound1755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1755 node1755Labels = Sparse.eval nodeValue1755 (mixedVector B) := by
  simpa only [nodeValue1755, Sparse.eval_nil] using zero1755 B _hB _hF

theorem sound1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1756 node1756Labels = Sparse.eval nodeValue1756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1756) = mixedMoment B node1756 node1756Labels := rfl
  simpa [nodeValue1756, Sparse.eval] using hc.symm

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

theorem sound2047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2047 node2047Labels = Sparse.eval nodeValue2047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2047) = mixedMoment B node2047 node2047Labels := rfl
  simpa [nodeValue2047, Sparse.eval] using hc.symm

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

theorem sound2048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2048 node2048Labels = Sparse.eval nodeValue2048 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2048) = mixedMoment B node2048 node2048Labels := rfl
  simpa [nodeValue2048, Sparse.eval] using hc.symm

theorem sound2049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2049 node2049Labels = Sparse.eval nodeValue2049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2049) = mixedMoment B node2049 node2049Labels := rfl
  simpa [nodeValue2049, Sparse.eval] using hc.symm

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

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

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

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

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

theorem sound2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2276 node2276Labels = Sparse.eval nodeValue2276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2276) = mixedMoment B node2276 node2276Labels := rfl
  simpa [nodeValue2276, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

theorem sound2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2282 node2282Labels = Sparse.eval nodeValue2282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2282) = mixedMoment B node2282 node2282Labels := rfl
  simpa [nodeValue2282, Sparse.eval] using hc.symm

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

theorem sound2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2288 node2288Labels = Sparse.eval nodeValue2288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2288) = mixedMoment B node2288 node2288Labels := rfl
  simpa [nodeValue2288, Sparse.eval] using hc.symm

theorem sound2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = Sparse.eval nodeValue2293 (mixedVector B) := by
  simpa only [nodeValue2293, Sparse.eval_nil] using zero2293 B _hB _hF

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

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

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

theorem sound598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node598 node598Labels = Sparse.eval nodeValue598 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 598) = mixedMoment B node598 node598Labels := rfl
  simpa [nodeValue598, Sparse.eval] using hc.symm

theorem sound602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node602 node602Labels = Sparse.eval nodeValue602 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 602) = mixedMoment B node602 node602Labels := rfl
  simpa [nodeValue602, Sparse.eval] using hc.symm

theorem sound607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node607 node607Labels = Sparse.eval nodeValue607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 607) = mixedMoment B node607 node607Labels := rfl
  simpa [nodeValue607, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources55
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1766 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1766 + difference 0 0) (sourceB1766 + difference 0 0) sourceC1766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1076) := by
    have ha : (tripleCharges (sourceA1766 + difference 0 0) (sourceB1766 + difference 0 0) sourceC1766) = raw25585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1766 sourceB1766 sourceC1766 difference raw25585; decide +kernel
    rw [ha]
    exact (canonical25585 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1766 + difference 0 1) (sourceB1766 + difference 1 0) sourceC1766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2049) := by
    have ha : (tripleCharges (sourceA1766 + difference 0 1) (sourceB1766 + difference 1 0) sourceC1766) = raw25586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1766 sourceB1766 sourceC1766 difference raw25586; decide +kernel
    rw [ha]
    exact (canonical25586 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1766 + difference 0 2) (sourceB1766 + difference 2 0) sourceC1766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2049) := by
    have ha : (tripleCharges (sourceA1766 + difference 0 2) (sourceB1766 + difference 2 0) sourceC1766) = raw25587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1766 sourceB1766 sourceC1766 difference raw25587; decide +kernel
    rw [ha]
    exact (canonical25587 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1766 + difference 0 3) (sourceB1766 + difference 3 0) sourceC1766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2282) := by
    have ha : (tripleCharges (sourceA1766 + difference 0 3) (sourceB1766 + difference 3 0) sourceC1766) = raw25588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1766 sourceB1766 sourceC1766 difference raw25588; decide +kernel
    rw [ha]
    exact (canonical25588 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1766 + difference 0 4) (sourceB1766 + difference 4 0) sourceC1766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1766 + difference 0 4) (sourceB1766 + difference 4 0) sourceC1766) = raw25589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1766 sourceB1766 sourceC1766 difference raw25589; decide +kernel
    rw [ha]
    exact (canonical25589 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1766 + difference 0 5) (sourceB1766 + difference 5 0) sourceC1766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1766 + difference 0 5) (sourceB1766 + difference 5 0) sourceC1766) = raw25590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1766 sourceB1766 sourceC1766 difference raw25590; decide +kernel
    rw [ha]
    exact (canonical25590 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1766 + sourceB1766) sourceC1766) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1766 + sourceB1766) sourceC1766) = raw25591 := by
      apply Matrix.ext; unfold doubleCharges sourceA1766 sourceB1766 sourceC1766 raw25591; decide +kernel
    rw [ha]
    exact (canonical25591 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1766 sourceB1766 sourceC1766
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1766, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1770 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1770 + difference 0 1) (sourceB1770 + difference 1 0) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1770 + difference 0 1) (sourceB1770 + difference 1 0) sourceC1770) = raw25633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25633; decide +kernel
    rw [ha]
    exact (canonical25633 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1770 + difference 0 2) (sourceB1770 + difference 2 0) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1770 + difference 0 2) (sourceB1770 + difference 2 0) sourceC1770) = raw25634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25634; decide +kernel
    rw [ha]
    exact (canonical25634 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1770 + difference 0 3) (sourceB1770 + difference 3 0) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA1770 + difference 0 3) (sourceB1770 + difference 3 0) sourceC1770) = raw25635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25635; decide +kernel
    rw [ha]
    exact (canonical25635 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1770 + difference 0 4) (sourceB1770 + difference 4 0) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA1770 + difference 0 4) (sourceB1770 + difference 4 0) sourceC1770) = raw25636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25636; decide +kernel
    rw [ha]
    exact (canonical25636 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1770 + difference 0 5) (sourceB1770 + difference 5 0) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA1770 + difference 0 5) (sourceB1770 + difference 5 0) sourceC1770) = raw25637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25637; decide +kernel
    rw [ha]
    exact (canonical25637 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1770 + difference 1 0) (sourceB1770 + difference 0 1) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1770 + difference 1 0) (sourceB1770 + difference 0 1) sourceC1770) = raw25638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25638; decide +kernel
    rw [ha]
    exact (canonical25638 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1770 + difference 1 2) (sourceB1770 + difference 2 1) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA1770 + difference 1 2) (sourceB1770 + difference 2 1) sourceC1770) = raw25639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25639; decide +kernel
    rw [ha]
    exact (canonical25639 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1770 + difference 1 3) (sourceB1770 + difference 3 1) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1770 + difference 1 3) (sourceB1770 + difference 3 1) sourceC1770) = raw25640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25640; decide +kernel
    rw [ha]
    exact (canonical25640 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1770 + difference 1 4) (sourceB1770 + difference 4 1) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1770 + difference 1 4) (sourceB1770 + difference 4 1) sourceC1770) = raw25641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25641; decide +kernel
    rw [ha]
    exact (canonical25641 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1770 + difference 1 5) (sourceB1770 + difference 5 1) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1770 + difference 1 5) (sourceB1770 + difference 5 1) sourceC1770) = raw25642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25642; decide +kernel
    rw [ha]
    exact (canonical25642 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1770 + difference 2 0) (sourceB1770 + difference 0 2) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1770 + difference 2 0) (sourceB1770 + difference 0 2) sourceC1770) = raw25643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25643; decide +kernel
    rw [ha]
    exact (canonical25643 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1770 + difference 2 1) (sourceB1770 + difference 1 2) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA1770 + difference 2 1) (sourceB1770 + difference 1 2) sourceC1770) = raw25644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25644; decide +kernel
    rw [ha]
    exact (canonical25644 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1770 + difference 2 3) (sourceB1770 + difference 3 2) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1770 + difference 2 3) (sourceB1770 + difference 3 2) sourceC1770) = raw25645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25645; decide +kernel
    rw [ha]
    exact (canonical25645 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1770 + difference 2 4) (sourceB1770 + difference 4 2) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1770 + difference 2 4) (sourceB1770 + difference 4 2) sourceC1770) = raw25646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25646; decide +kernel
    rw [ha]
    exact (canonical25646 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1770 + difference 2 5) (sourceB1770 + difference 5 2) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1770 + difference 2 5) (sourceB1770 + difference 5 2) sourceC1770) = raw25647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25647; decide +kernel
    rw [ha]
    exact (canonical25647 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1770 + difference 3 0) (sourceB1770 + difference 0 3) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1525) := by
    have ha : (tripleCharges (sourceA1770 + difference 3 0) (sourceB1770 + difference 0 3) sourceC1770) = raw25648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25648; decide +kernel
    rw [ha]
    exact (canonical25648 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1770 + difference 3 1) (sourceB1770 + difference 1 3) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA1770 + difference 3 1) (sourceB1770 + difference 1 3) sourceC1770) = raw25649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25649; decide +kernel
    rw [ha]
    exact (canonical25649 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1770 + difference 3 2) (sourceB1770 + difference 2 3) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA1770 + difference 3 2) (sourceB1770 + difference 2 3) sourceC1770) = raw25650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25650; decide +kernel
    rw [ha]
    exact (canonical25650 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1770 + difference 3 4) (sourceB1770 + difference 4 3) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1770 + difference 3 4) (sourceB1770 + difference 4 3) sourceC1770) = raw25651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25651; decide +kernel
    rw [ha]
    exact (canonical25651 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1770 + difference 3 5) (sourceB1770 + difference 5 3) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1770 + difference 3 5) (sourceB1770 + difference 5 3) sourceC1770) = raw25652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25652; decide +kernel
    rw [ha]
    exact (canonical25652 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1770 + difference 4 0) (sourceB1770 + difference 0 4) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1526) := by
    have ha : (tripleCharges (sourceA1770 + difference 4 0) (sourceB1770 + difference 0 4) sourceC1770) = raw25653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25653; decide +kernel
    rw [ha]
    exact (canonical25653 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1770 + difference 4 1) (sourceB1770 + difference 1 4) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA1770 + difference 4 1) (sourceB1770 + difference 1 4) sourceC1770) = raw25654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25654; decide +kernel
    rw [ha]
    exact (canonical25654 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1770 + difference 4 2) (sourceB1770 + difference 2 4) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA1770 + difference 4 2) (sourceB1770 + difference 2 4) sourceC1770) = raw25655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25655; decide +kernel
    rw [ha]
    exact (canonical25655 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1770 + difference 4 3) (sourceB1770 + difference 3 4) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1770 + difference 4 3) (sourceB1770 + difference 3 4) sourceC1770) = raw25656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25656; decide +kernel
    rw [ha]
    exact (canonical25656 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1770 + difference 4 5) (sourceB1770 + difference 5 4) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1770 + difference 4 5) (sourceB1770 + difference 5 4) sourceC1770) = raw25657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25657; decide +kernel
    rw [ha]
    exact (canonical25657 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1770 + difference 5 0) (sourceB1770 + difference 0 5) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA1770 + difference 5 0) (sourceB1770 + difference 0 5) sourceC1770) = raw25658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25658; decide +kernel
    rw [ha]
    exact (canonical25658 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1770 + difference 5 1) (sourceB1770 + difference 1 5) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1686) := by
    have ha : (tripleCharges (sourceA1770 + difference 5 1) (sourceB1770 + difference 1 5) sourceC1770) = raw25659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25659; decide +kernel
    rw [ha]
    exact (canonical25659 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1770 + difference 5 2) (sourceB1770 + difference 2 5) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1686) := by
    have ha : (tripleCharges (sourceA1770 + difference 5 2) (sourceB1770 + difference 2 5) sourceC1770) = raw25660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25660; decide +kernel
    rw [ha]
    exact (canonical25660 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1770 + difference 5 3) (sourceB1770 + difference 3 5) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA1770 + difference 5 3) (sourceB1770 + difference 3 5) sourceC1770) = raw25661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25661; decide +kernel
    rw [ha]
    exact (canonical25661 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1770 + difference 5 4) (sourceB1770 + difference 4 5) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1770 + difference 5 4) (sourceB1770 + difference 4 5) sourceC1770) = raw25662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25662; decide +kernel
    rw [ha]
    exact (canonical25662 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1770 sourceB1770 sourceC1770
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1770, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1776 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1776 + difference 0 1) (sourceB1776 + difference 1 0) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1776 + difference 0 1) (sourceB1776 + difference 1 0) sourceC1776) = raw25763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25763; decide +kernel
    rw [ha]
    exact (canonical25763 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1776 + difference 0 2) (sourceB1776 + difference 2 0) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1776 + difference 0 2) (sourceB1776 + difference 2 0) sourceC1776) = raw25764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25764; decide +kernel
    rw [ha]
    exact (canonical25764 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1776 + difference 0 3) (sourceB1776 + difference 3 0) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA1776 + difference 0 3) (sourceB1776 + difference 3 0) sourceC1776) = raw25765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25765; decide +kernel
    rw [ha]
    exact (canonical25765 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1776 + difference 0 4) (sourceB1776 + difference 4 0) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA1776 + difference 0 4) (sourceB1776 + difference 4 0) sourceC1776) = raw25766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25766; decide +kernel
    rw [ha]
    exact (canonical25766 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1776 + difference 0 5) (sourceB1776 + difference 5 0) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA1776 + difference 0 5) (sourceB1776 + difference 5 0) sourceC1776) = raw25767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25767; decide +kernel
    rw [ha]
    exact (canonical25767 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1776 + difference 1 0) (sourceB1776 + difference 0 1) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1776 + difference 1 0) (sourceB1776 + difference 0 1) sourceC1776) = raw25768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25768; decide +kernel
    rw [ha]
    exact (canonical25768 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1776 + difference 1 2) (sourceB1776 + difference 2 1) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1665) := by
    have ha : (tripleCharges (sourceA1776 + difference 1 2) (sourceB1776 + difference 2 1) sourceC1776) = raw25769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25769; decide +kernel
    rw [ha]
    exact (canonical25769 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1776 + difference 1 3) (sourceB1776 + difference 3 1) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1776 + difference 1 3) (sourceB1776 + difference 3 1) sourceC1776) = raw25770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25770; decide +kernel
    rw [ha]
    exact (canonical25770 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1776 + difference 1 4) (sourceB1776 + difference 4 1) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1776 + difference 1 4) (sourceB1776 + difference 4 1) sourceC1776) = raw25771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25771; decide +kernel
    rw [ha]
    exact (canonical25771 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1776 + difference 1 5) (sourceB1776 + difference 5 1) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1776 + difference 1 5) (sourceB1776 + difference 5 1) sourceC1776) = raw25772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25772; decide +kernel
    rw [ha]
    exact (canonical25772 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1776 + difference 2 0) (sourceB1776 + difference 0 2) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1776 + difference 2 0) (sourceB1776 + difference 0 2) sourceC1776) = raw25773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25773; decide +kernel
    rw [ha]
    exact (canonical25773 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1776 + difference 2 1) (sourceB1776 + difference 1 2) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1665) := by
    have ha : (tripleCharges (sourceA1776 + difference 2 1) (sourceB1776 + difference 1 2) sourceC1776) = raw25774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25774; decide +kernel
    rw [ha]
    exact (canonical25774 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1776 + difference 2 3) (sourceB1776 + difference 3 2) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1776 + difference 2 3) (sourceB1776 + difference 3 2) sourceC1776) = raw25775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25775; decide +kernel
    rw [ha]
    exact (canonical25775 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1776 + difference 2 4) (sourceB1776 + difference 4 2) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1776 + difference 2 4) (sourceB1776 + difference 4 2) sourceC1776) = raw25776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25776; decide +kernel
    rw [ha]
    exact (canonical25776 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1776 + difference 2 5) (sourceB1776 + difference 5 2) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1776 + difference 2 5) (sourceB1776 + difference 5 2) sourceC1776) = raw25777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25777; decide +kernel
    rw [ha]
    exact (canonical25777 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1776 + difference 3 0) (sourceB1776 + difference 0 3) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA1776 + difference 3 0) (sourceB1776 + difference 0 3) sourceC1776) = raw25778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25778; decide +kernel
    rw [ha]
    exact (canonical25778 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1776 + difference 3 1) (sourceB1776 + difference 1 3) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1776 + difference 3 1) (sourceB1776 + difference 1 3) sourceC1776) = raw25779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25779; decide +kernel
    rw [ha]
    exact (canonical25779 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1776 + difference 3 2) (sourceB1776 + difference 2 3) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1776 + difference 3 2) (sourceB1776 + difference 2 3) sourceC1776) = raw25780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25780; decide +kernel
    rw [ha]
    exact (canonical25780 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1776 + difference 3 4) (sourceB1776 + difference 4 3) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1776 + difference 3 4) (sourceB1776 + difference 4 3) sourceC1776) = raw25781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25781; decide +kernel
    rw [ha]
    exact (canonical25781 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1776 + difference 3 5) (sourceB1776 + difference 5 3) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1776 + difference 3 5) (sourceB1776 + difference 5 3) sourceC1776) = raw25782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25782; decide +kernel
    rw [ha]
    exact (canonical25782 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1776 + difference 4 0) (sourceB1776 + difference 0 4) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1526) := by
    have ha : (tripleCharges (sourceA1776 + difference 4 0) (sourceB1776 + difference 0 4) sourceC1776) = raw25783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25783; decide +kernel
    rw [ha]
    exact (canonical25783 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1776 + difference 4 1) (sourceB1776 + difference 1 4) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA1776 + difference 4 1) (sourceB1776 + difference 1 4) sourceC1776) = raw25784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25784; decide +kernel
    rw [ha]
    exact (canonical25784 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1776 + difference 4 2) (sourceB1776 + difference 2 4) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA1776 + difference 4 2) (sourceB1776 + difference 2 4) sourceC1776) = raw25785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25785; decide +kernel
    rw [ha]
    exact (canonical25785 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1776 + difference 4 3) (sourceB1776 + difference 3 4) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1776 + difference 4 3) (sourceB1776 + difference 3 4) sourceC1776) = raw25786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25786; decide +kernel
    rw [ha]
    exact (canonical25786 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1776 + difference 4 5) (sourceB1776 + difference 5 4) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1776 + difference 4 5) (sourceB1776 + difference 5 4) sourceC1776) = raw25787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25787; decide +kernel
    rw [ha]
    exact (canonical25787 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1776 + difference 5 0) (sourceB1776 + difference 0 5) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA1776 + difference 5 0) (sourceB1776 + difference 0 5) sourceC1776) = raw25788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25788; decide +kernel
    rw [ha]
    exact (canonical25788 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1776 + difference 5 1) (sourceB1776 + difference 1 5) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1776 + difference 5 1) (sourceB1776 + difference 1 5) sourceC1776) = raw25789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25789; decide +kernel
    rw [ha]
    exact (canonical25789 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1776 + difference 5 2) (sourceB1776 + difference 2 5) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1776 + difference 5 2) (sourceB1776 + difference 2 5) sourceC1776) = raw25790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25790; decide +kernel
    rw [ha]
    exact (canonical25790 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1776 + difference 5 3) (sourceB1776 + difference 3 5) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1776 + difference 5 3) (sourceB1776 + difference 3 5) sourceC1776) = raw25791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25791; decide +kernel
    rw [ha]
    exact (canonical25791 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1776 + difference 5 4) (sourceB1776 + difference 4 5) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1776 + difference 5 4) (sourceB1776 + difference 4 5) sourceC1776) = raw25792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25792; decide +kernel
    rw [ha]
    exact (canonical25792 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1776 sourceB1776 sourceC1776
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1776, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1780 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1780 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1780 + difference 0 0) (sourceB1780 + difference 0 0) sourceC1780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1780 + difference 0 0) (sourceB1780 + difference 0 0) sourceC1780) = raw25848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1780 sourceB1780 sourceC1780 difference raw25848; decide +kernel
    rw [ha]
    exact (canonical25848 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1780 + difference 0 1) (sourceB1780 + difference 1 0) sourceC1780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2048) := by
    have ha : (tripleCharges (sourceA1780 + difference 0 1) (sourceB1780 + difference 1 0) sourceC1780) = raw25849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1780 sourceB1780 sourceC1780 difference raw25849; decide +kernel
    rw [ha]
    exact (canonical25849 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1780 + difference 0 2) (sourceB1780 + difference 2 0) sourceC1780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2048) := by
    have ha : (tripleCharges (sourceA1780 + difference 0 2) (sourceB1780 + difference 2 0) sourceC1780) = raw25850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1780 sourceB1780 sourceC1780 difference raw25850; decide +kernel
    rw [ha]
    exact (canonical25850 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1780 + difference 0 3) (sourceB1780 + difference 3 0) sourceC1780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA1780 + difference 0 3) (sourceB1780 + difference 3 0) sourceC1780) = raw25851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1780 sourceB1780 sourceC1780 difference raw25851; decide +kernel
    rw [ha]
    exact (canonical25851 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1780 + difference 0 4) (sourceB1780 + difference 4 0) sourceC1780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1780 + difference 0 4) (sourceB1780 + difference 4 0) sourceC1780) = raw25852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1780 sourceB1780 sourceC1780 difference raw25852; decide +kernel
    rw [ha]
    exact (canonical25852 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1780 + difference 0 5) (sourceB1780 + difference 5 0) sourceC1780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA1780 + difference 0 5) (sourceB1780 + difference 5 0) sourceC1780) = raw25853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1780 sourceB1780 sourceC1780 difference raw25853; decide +kernel
    rw [ha]
    exact (canonical25853 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1780 + sourceB1780) sourceC1780) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1780 + sourceB1780) sourceC1780) = raw25854 := by
      apply Matrix.ext; unfold doubleCharges sourceA1780 sourceB1780 sourceC1780 raw25854; decide +kernel
    rw [ha]
    exact (canonical25854 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1780 sourceB1780 sourceC1780
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1780, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1783 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1783 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1783 + difference 0 0) (sourceB1783 + difference 0 0) sourceC1783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1783 + difference 0 0) (sourceB1783 + difference 0 0) sourceC1783) = raw25915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1783 sourceB1783 sourceC1783 difference raw25915; decide +kernel
    rw [ha]
    exact (canonical25915 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1783 + difference 0 1) (sourceB1783 + difference 1 0) sourceC1783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2047) := by
    have ha : (tripleCharges (sourceA1783 + difference 0 1) (sourceB1783 + difference 1 0) sourceC1783) = raw25916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1783 sourceB1783 sourceC1783 difference raw25916; decide +kernel
    rw [ha]
    exact (canonical25916 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1783 + difference 0 2) (sourceB1783 + difference 2 0) sourceC1783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2047) := by
    have ha : (tripleCharges (sourceA1783 + difference 0 2) (sourceB1783 + difference 2 0) sourceC1783) = raw25917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1783 sourceB1783 sourceC1783 difference raw25917; decide +kernel
    rw [ha]
    exact (canonical25917 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1783 + difference 0 3) (sourceB1783 + difference 3 0) sourceC1783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1783 + difference 0 3) (sourceB1783 + difference 3 0) sourceC1783) = raw25918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1783 sourceB1783 sourceC1783 difference raw25918; decide +kernel
    rw [ha]
    exact (canonical25918 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1783 + difference 0 4) (sourceB1783 + difference 4 0) sourceC1783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1783 + difference 0 4) (sourceB1783 + difference 4 0) sourceC1783) = raw25919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1783 sourceB1783 sourceC1783 difference raw25919; decide +kernel
    rw [ha]
    exact (canonical25919 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1783 + difference 0 5) (sourceB1783 + difference 5 0) sourceC1783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1783 + difference 0 5) (sourceB1783 + difference 5 0) sourceC1783) = raw25920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1783 sourceB1783 sourceC1783 difference raw25920; decide +kernel
    rw [ha]
    exact (canonical25920 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1783 + sourceB1783) sourceC1783) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1783 + sourceB1783) sourceC1783) = raw25921 := by
      apply Matrix.ext; unfold doubleCharges sourceA1783 sourceB1783 sourceC1783 raw25921; decide +kernel
    rw [ha]
    exact (canonical25921 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1783 sourceB1783 sourceC1783
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1783, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1786 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1786 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1786 + difference 0 1) (sourceB1786 + difference 1 0) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1786 + difference 0 1) (sourceB1786 + difference 1 0) sourceC1786) = raw25973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25973; decide +kernel
    rw [ha]
    exact (canonical25973 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1786 + difference 0 2) (sourceB1786 + difference 2 0) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1786 + difference 0 2) (sourceB1786 + difference 2 0) sourceC1786) = raw25974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25974; decide +kernel
    rw [ha]
    exact (canonical25974 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1786 + difference 0 3) (sourceB1786 + difference 3 0) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA1786 + difference 0 3) (sourceB1786 + difference 3 0) sourceC1786) = raw21856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21856; decide +kernel
    rw [ha]
    exact (canonical21856 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1786 + difference 0 4) (sourceB1786 + difference 4 0) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA1786 + difference 0 4) (sourceB1786 + difference 4 0) sourceC1786) = raw25975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25975; decide +kernel
    rw [ha]
    exact (canonical25975 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1786 + difference 0 5) (sourceB1786 + difference 5 0) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA1786 + difference 0 5) (sourceB1786 + difference 5 0) sourceC1786) = raw25976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25976; decide +kernel
    rw [ha]
    exact (canonical25976 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1786 + difference 1 0) (sourceB1786 + difference 0 1) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1503) := by
    have ha : (tripleCharges (sourceA1786 + difference 1 0) (sourceB1786 + difference 0 1) sourceC1786) = raw25977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25977; decide +kernel
    rw [ha]
    exact (canonical25977 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1786 + difference 1 2) (sourceB1786 + difference 2 1) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1662) := by
    have ha : (tripleCharges (sourceA1786 + difference 1 2) (sourceB1786 + difference 2 1) sourceC1786) = raw25978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25978; decide +kernel
    rw [ha]
    exact (canonical25978 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1786 + difference 1 3) (sourceB1786 + difference 3 1) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1786 + difference 1 3) (sourceB1786 + difference 3 1) sourceC1786) = raw21860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21860; decide +kernel
    rw [ha]
    exact (canonical21860 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1786 + difference 1 4) (sourceB1786 + difference 4 1) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1786 + difference 1 4) (sourceB1786 + difference 4 1) sourceC1786) = raw25979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25979; decide +kernel
    rw [ha]
    exact (canonical25979 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1786 + difference 1 5) (sourceB1786 + difference 5 1) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA1786 + difference 1 5) (sourceB1786 + difference 5 1) sourceC1786) = raw25980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25980; decide +kernel
    rw [ha]
    exact (canonical25980 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1786 + difference 2 0) (sourceB1786 + difference 0 2) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1503) := by
    have ha : (tripleCharges (sourceA1786 + difference 2 0) (sourceB1786 + difference 0 2) sourceC1786) = raw25981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25981; decide +kernel
    rw [ha]
    exact (canonical25981 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1786 + difference 2 1) (sourceB1786 + difference 1 2) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1662) := by
    have ha : (tripleCharges (sourceA1786 + difference 2 1) (sourceB1786 + difference 1 2) sourceC1786) = raw25982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25982; decide +kernel
    rw [ha]
    exact (canonical25982 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1786 + difference 2 3) (sourceB1786 + difference 3 2) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1786 + difference 2 3) (sourceB1786 + difference 3 2) sourceC1786) = raw21864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21864; decide +kernel
    rw [ha]
    exact (canonical21864 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1786 + difference 2 4) (sourceB1786 + difference 4 2) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1786 + difference 2 4) (sourceB1786 + difference 4 2) sourceC1786) = raw25983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25983; decide +kernel
    rw [ha]
    exact (canonical25983 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1786 + difference 2 5) (sourceB1786 + difference 5 2) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA1786 + difference 2 5) (sourceB1786 + difference 5 2) sourceC1786) = raw25984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25984; decide +kernel
    rw [ha]
    exact (canonical25984 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1786 + difference 3 0) (sourceB1786 + difference 0 3) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA1786 + difference 3 0) (sourceB1786 + difference 0 3) sourceC1786) = raw25985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25985; decide +kernel
    rw [ha]
    exact (canonical25985 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1786 + difference 3 1) (sourceB1786 + difference 1 3) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1786 + difference 3 1) (sourceB1786 + difference 1 3) sourceC1786) = raw25986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25986; decide +kernel
    rw [ha]
    exact (canonical25986 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1786 + difference 3 2) (sourceB1786 + difference 2 3) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1786 + difference 3 2) (sourceB1786 + difference 2 3) sourceC1786) = raw25987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25987; decide +kernel
    rw [ha]
    exact (canonical25987 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1786 + difference 3 4) (sourceB1786 + difference 4 3) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1786 + difference 3 4) (sourceB1786 + difference 4 3) sourceC1786) = raw25988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25988; decide +kernel
    rw [ha]
    exact (canonical25988 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1786 + difference 3 5) (sourceB1786 + difference 5 3) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1786 + difference 3 5) (sourceB1786 + difference 5 3) sourceC1786) = raw25989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25989; decide +kernel
    rw [ha]
    exact (canonical25989 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1786 + difference 4 0) (sourceB1786 + difference 0 4) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA1786 + difference 4 0) (sourceB1786 + difference 0 4) sourceC1786) = raw25990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25990; decide +kernel
    rw [ha]
    exact (canonical25990 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1786 + difference 4 1) (sourceB1786 + difference 1 4) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1786 + difference 4 1) (sourceB1786 + difference 1 4) sourceC1786) = raw25991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25991; decide +kernel
    rw [ha]
    exact (canonical25991 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1786 + difference 4 2) (sourceB1786 + difference 2 4) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1786 + difference 4 2) (sourceB1786 + difference 2 4) sourceC1786) = raw25992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25992; decide +kernel
    rw [ha]
    exact (canonical25992 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1786 + difference 4 3) (sourceB1786 + difference 3 4) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1786 + difference 4 3) (sourceB1786 + difference 3 4) sourceC1786) = raw21873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21873; decide +kernel
    rw [ha]
    exact (canonical21873 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1786 + difference 4 5) (sourceB1786 + difference 5 4) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1786 + difference 4 5) (sourceB1786 + difference 5 4) sourceC1786) = raw25993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25993; decide +kernel
    rw [ha]
    exact (canonical25993 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1786 + difference 5 0) (sourceB1786 + difference 0 5) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA1786 + difference 5 0) (sourceB1786 + difference 0 5) sourceC1786) = raw21865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21865; decide +kernel
    rw [ha]
    exact (canonical21865 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1786 + difference 5 1) (sourceB1786 + difference 1 5) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1786 + difference 5 1) (sourceB1786 + difference 1 5) sourceC1786) = raw21866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21866; decide +kernel
    rw [ha]
    exact (canonical21866 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1786 + difference 5 2) (sourceB1786 + difference 2 5) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1786 + difference 5 2) (sourceB1786 + difference 2 5) sourceC1786) = raw21867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21867; decide +kernel
    rw [ha]
    exact (canonical21867 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1786 + difference 5 3) (sourceB1786 + difference 3 5) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1786 + difference 5 3) (sourceB1786 + difference 3 5) sourceC1786) = raw19941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw19941; decide +kernel
    rw [ha]
    exact (canonical19941 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1786 + difference 5 4) (sourceB1786 + difference 4 5) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1786 + difference 5 4) (sourceB1786 + difference 4 5) sourceC1786) = raw19936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw19936; decide +kernel
    rw [ha]
    exact (canonical19936 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1786 sourceB1786 sourceC1786
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1786, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1787 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1787 + difference 0 0) (sourceB1787 + difference 0 0) sourceC1787) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1787 + difference 0 0) (sourceB1787 + difference 0 0) sourceC1787) = raw25994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1787 sourceB1787 sourceC1787 difference raw25994; decide +kernel
    rw [ha]
    exact (canonical25994 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1787 + difference 1 0) (sourceB1787 + difference 0 1) sourceC1787) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 598) := by
    have ha : (tripleCharges (sourceA1787 + difference 1 0) (sourceB1787 + difference 0 1) sourceC1787) = raw25995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1787 sourceB1787 sourceC1787 difference raw25995; decide +kernel
    rw [ha]
    exact (canonical25995 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1787 + difference 2 0) (sourceB1787 + difference 0 2) sourceC1787) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 598) := by
    have ha : (tripleCharges (sourceA1787 + difference 2 0) (sourceB1787 + difference 0 2) sourceC1787) = raw25996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1787 sourceB1787 sourceC1787 difference raw25996; decide +kernel
    rw [ha]
    exact (canonical25996 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1787 + difference 3 0) (sourceB1787 + difference 0 3) sourceC1787) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 607) := by
    have ha : (tripleCharges (sourceA1787 + difference 3 0) (sourceB1787 + difference 0 3) sourceC1787) = raw25997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1787 sourceB1787 sourceC1787 difference raw25997; decide +kernel
    rw [ha]
    exact (canonical25997 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1787 + difference 4 0) (sourceB1787 + difference 0 4) sourceC1787) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 607) := by
    have ha : (tripleCharges (sourceA1787 + difference 4 0) (sourceB1787 + difference 0 4) sourceC1787) = raw25998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1787 sourceB1787 sourceC1787 difference raw25998; decide +kernel
    rw [ha]
    exact (canonical25998 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1787 + difference 5 0) (sourceB1787 + difference 0 5) sourceC1787) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 602) := by
    have ha : (tripleCharges (sourceA1787 + difference 5 0) (sourceB1787 + difference 0 5) sourceC1787) = raw21878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1787 sourceB1787 sourceC1787 difference raw21878; decide +kernel
    rw [ha]
    exact (canonical21878 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1787 + sourceB1787) sourceC1787) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1787 + sourceB1787) sourceC1787) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA1787 sourceB1787 sourceC1787 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1787 sourceB1787 sourceC1787
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1787, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1504 : Integer.Sparse.reindex keyMap MixedData.row1504 = numericRow1504 := by decide +kernel

theorem numericCheck1504 (x : Master → ℝ) : Integer.Sparse.eval numericRow1504 x =
    (1 : ℝ) * reducedSource1504 x := by
  norm_num [numericRow1504, reducedSource1504, Integer.Sparse.eval, Sparse.eval, nodeValue1076, nodeValue2049, nodeValue2230, nodeValue2282, nodeValue2287, nodeValue4081]

theorem reindexCheck1506 : Integer.Sparse.reindex keyMap MixedData.row1506 = numericRow1506 := by decide +kernel

theorem numericCheck1506 (x : Master → ℝ) : Integer.Sparse.eval numericRow1506 x =
    (1 : ℝ) * reducedSource1506 x := by
  norm_num [numericRow1506, reducedSource1506, Integer.Sparse.eval, Sparse.eval, nodeValue1512, nodeValue1525, nodeValue1526, nodeValue1530, nodeValue1668, nodeValue1681, nodeValue1682, nodeValue1686, nodeValue1708, nodeValue1714, nodeValue1715, nodeValue1727, nodeValue1728, nodeValue1738, nodeValue1740, nodeValue1745, nodeValue1746, nodeValue2216, nodeValue2265, nodeValue2278, nodeValue2279]

theorem reindexCheck1509 : Integer.Sparse.reindex keyMap MixedData.row1509 = numericRow1509 := by decide +kernel

theorem numericCheck1509 (x : Master → ℝ) : Integer.Sparse.eval numericRow1509 x =
    (1 : ℝ) * reducedSource1509 x := by
  norm_num [numericRow1509, reducedSource1509, Integer.Sparse.eval, Sparse.eval, nodeValue1508, nodeValue1519, nodeValue1520, nodeValue1526, nodeValue1665, nodeValue1675, nodeValue1676, nodeValue1682, nodeValue1708, nodeValue1709, nodeValue1727, nodeValue1728, nodeValue1729, nodeValue1739, nodeValue1740, nodeValue1755, nodeValue1756, nodeValue2206, nodeValue2265, nodeValue2266, nodeValue2293]

theorem reindexCheck1512 : Integer.Sparse.reindex keyMap MixedData.row1512 = numericRow1512 := by decide +kernel

theorem numericCheck1512 (x : Master → ℝ) : Integer.Sparse.eval numericRow1512 x =
    (1 : ℝ) * reducedSource1512 x := by
  norm_num [numericRow1512, reducedSource1512, Integer.Sparse.eval, Sparse.eval, nodeValue1075, nodeValue2048, nodeValue2229, nodeValue2276, nodeValue2288, nodeValue4082]

theorem reindexCheck1515 : Integer.Sparse.reindex keyMap MixedData.row1515 = numericRow1515 := by decide +kernel

theorem numericCheck1515 (x : Master → ℝ) : Integer.Sparse.eval numericRow1515 x =
    (1 : ℝ) * reducedSource1515 x := by
  norm_num [numericRow1515, reducedSource1515, Integer.Sparse.eval, Sparse.eval, nodeValue1074, nodeValue2047, nodeValue2228, nodeValue2261, nodeValue2287, nodeValue4081]

theorem reindexCheck1518 : Integer.Sparse.reindex keyMap MixedData.row1518 = numericRow1518 := by decide +kernel

theorem numericCheck1518 (x : Master → ℝ) : Integer.Sparse.eval numericRow1518 x =
    (1 : ℝ) * reducedSource1518 x := by
  norm_num [numericRow1518, reducedSource1518, Integer.Sparse.eval, Sparse.eval, nodeValue1503, nodeValue1509, nodeValue1513, nodeValue1662, nodeValue1666, nodeValue1669, nodeValue1700, nodeValue1710, nodeValue1716, nodeValue1730, nodeValue1741, nodeValue2193, nodeValue2247, nodeValue2268]

theorem reindexCheck1519 : Integer.Sparse.reindex keyMap MixedData.row1519 = numericRow1519 := by decide +kernel

theorem numericCheck1519 (x : Master → ℝ) : Integer.Sparse.eval numericRow1519 x =
    (1 : ℝ) * reducedSource1519 x := by
  norm_num [numericRow1519, reducedSource1519, Integer.Sparse.eval, Sparse.eval, nodeValue598, nodeValue602, nodeValue607, nodeValue1080, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1504 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1504 (mixedVector B) = 0 := by
  have h1076 : mixedVector B (Sum.inr 1076) = Sparse.eval nodeValue1076 (mixedVector B) := by
    change mixedMoment B node1076 node1076Labels = _
    exact sound1076 B hB hF
  have h2049 : mixedVector B (Sum.inr 2049) = Sparse.eval nodeValue2049 (mixedVector B) := by
    change mixedMoment B node2049 node2049Labels = _
    exact sound2049 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2282 : mixedVector B (Sum.inr 2282) = Sparse.eval nodeValue2282 (mixedVector B) := by
    change mixedMoment B node2282 node2282Labels = _
    exact sound2282 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1766, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1076, h2049, h2230, h2282, h2287, h4081, reducedSource1504] using sourceEq1766 B hB

theorem rowSound1504 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1504 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1504, numericCheck1504, reducedZero1504 B hB hF, mul_zero]

theorem reducedZero1506 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1506 (mixedVector B) = 0 := by
  have h1512 : mixedVector B (Sum.inr 1512) = Sparse.eval nodeValue1512 (mixedVector B) := by
    change mixedMoment B node1512 node1512Labels = _
    exact sound1512 B hB hF
  have h1525 : mixedVector B (Sum.inr 1525) = Sparse.eval nodeValue1525 (mixedVector B) := by
    change mixedMoment B node1525 node1525Labels = _
    exact sound1525 B hB hF
  have h1526 : mixedVector B (Sum.inr 1526) = Sparse.eval nodeValue1526 (mixedVector B) := by
    change mixedMoment B node1526 node1526Labels = _
    exact sound1526 B hB hF
  have h1530 : mixedVector B (Sum.inr 1530) = Sparse.eval nodeValue1530 (mixedVector B) := by
    change mixedMoment B node1530 node1530Labels = _
    exact sound1530 B hB hF
  have h1668 : mixedVector B (Sum.inr 1668) = Sparse.eval nodeValue1668 (mixedVector B) := by
    change mixedMoment B node1668 node1668Labels = _
    exact sound1668 B hB hF
  have h1681 : mixedVector B (Sum.inr 1681) = Sparse.eval nodeValue1681 (mixedVector B) := by
    change mixedMoment B node1681 node1681Labels = _
    exact sound1681 B hB hF
  have h1682 : mixedVector B (Sum.inr 1682) = Sparse.eval nodeValue1682 (mixedVector B) := by
    change mixedMoment B node1682 node1682Labels = _
    exact sound1682 B hB hF
  have h1686 : mixedVector B (Sum.inr 1686) = Sparse.eval nodeValue1686 (mixedVector B) := by
    change mixedMoment B node1686 node1686Labels = _
    exact sound1686 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h1746 : mixedVector B (Sum.inr 1746) = Sparse.eval nodeValue1746 (mixedVector B) := by
    change mixedMoment B node1746 node1746Labels = _
    exact sound1746 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  simpa only [sourceForm1770, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1512, h1525, h1526, h1530, h1668, h1681, h1682, h1686, h1708, h1714, h1715, h1727, h1728, h1738, h1740, h1745, h1746, h2216, h2265, h2278, h2279, reducedSource1506] using sourceEq1770 B hB

theorem rowSound1506 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1506 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1506, numericCheck1506, reducedZero1506 B hB hF, mul_zero]

theorem reducedZero1509 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1509 (mixedVector B) = 0 := by
  have h1508 : mixedVector B (Sum.inr 1508) = Sparse.eval nodeValue1508 (mixedVector B) := by
    change mixedMoment B node1508 node1508Labels = _
    exact sound1508 B hB hF
  have h1519 : mixedVector B (Sum.inr 1519) = Sparse.eval nodeValue1519 (mixedVector B) := by
    change mixedMoment B node1519 node1519Labels = _
    exact sound1519 B hB hF
  have h1520 : mixedVector B (Sum.inr 1520) = Sparse.eval nodeValue1520 (mixedVector B) := by
    change mixedMoment B node1520 node1520Labels = _
    exact sound1520 B hB hF
  have h1526 : mixedVector B (Sum.inr 1526) = Sparse.eval nodeValue1526 (mixedVector B) := by
    change mixedMoment B node1526 node1526Labels = _
    exact sound1526 B hB hF
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
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h1755 : mixedVector B (Sum.inr 1755) = Sparse.eval nodeValue1755 (mixedVector B) := by
    change mixedMoment B node1755 node1755Labels = _
    exact sound1755 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  simpa only [sourceForm1776, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1508, h1519, h1520, h1526, h1665, h1675, h1676, h1682, h1708, h1709, h1727, h1728, h1729, h1739, h1740, h1755, h1756, h2206, h2265, h2266, h2293, reducedSource1509] using sourceEq1776 B hB

theorem rowSound1509 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1509 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1509, numericCheck1509, reducedZero1509 B hB hF, mul_zero]

theorem reducedZero1512 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1512 (mixedVector B) = 0 := by
  have h1075 : mixedVector B (Sum.inr 1075) = Sparse.eval nodeValue1075 (mixedVector B) := by
    change mixedMoment B node1075 node1075Labels = _
    exact sound1075 B hB hF
  have h2048 : mixedVector B (Sum.inr 2048) = Sparse.eval nodeValue2048 (mixedVector B) := by
    change mixedMoment B node2048 node2048Labels = _
    exact sound2048 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2288 : mixedVector B (Sum.inr 2288) = Sparse.eval nodeValue2288 (mixedVector B) := by
    change mixedMoment B node2288 node2288Labels = _
    exact sound2288 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1780, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1075, h2048, h2229, h2276, h2288, h4082, reducedSource1512] using sourceEq1780 B hB

theorem rowSound1512 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1512 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1512, numericCheck1512, reducedZero1512 B hB hF, mul_zero]

theorem reducedZero1515 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1515 (mixedVector B) = 0 := by
  have h1074 : mixedVector B (Sum.inr 1074) = Sparse.eval nodeValue1074 (mixedVector B) := by
    change mixedMoment B node1074 node1074Labels = _
    exact sound1074 B hB hF
  have h2047 : mixedVector B (Sum.inr 2047) = Sparse.eval nodeValue2047 (mixedVector B) := by
    change mixedMoment B node2047 node2047Labels = _
    exact sound2047 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1783, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1074, h2047, h2228, h2261, h2287, h4081, reducedSource1515] using sourceEq1783 B hB

theorem rowSound1515 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1515 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1515, numericCheck1515, reducedZero1515 B hB hF, mul_zero]

theorem reducedZero1518 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1518 (mixedVector B) = 0 := by
  have h1503 : mixedVector B (Sum.inr 1503) = Sparse.eval nodeValue1503 (mixedVector B) := by
    change mixedMoment B node1503 node1503Labels = _
    exact sound1503 B hB hF
  have h1509 : mixedVector B (Sum.inr 1509) = Sparse.eval nodeValue1509 (mixedVector B) := by
    change mixedMoment B node1509 node1509Labels = _
    exact sound1509 B hB hF
  have h1513 : mixedVector B (Sum.inr 1513) = Sparse.eval nodeValue1513 (mixedVector B) := by
    change mixedMoment B node1513 node1513Labels = _
    exact sound1513 B hB hF
  have h1662 : mixedVector B (Sum.inr 1662) = Sparse.eval nodeValue1662 (mixedVector B) := by
    change mixedMoment B node1662 node1662Labels = _
    exact sound1662 B hB hF
  have h1666 : mixedVector B (Sum.inr 1666) = Sparse.eval nodeValue1666 (mixedVector B) := by
    change mixedMoment B node1666 node1666Labels = _
    exact sound1666 B hB hF
  have h1669 : mixedVector B (Sum.inr 1669) = Sparse.eval nodeValue1669 (mixedVector B) := by
    change mixedMoment B node1669 node1669Labels = _
    exact sound1669 B hB hF
  have h1700 : mixedVector B (Sum.inr 1700) = Sparse.eval nodeValue1700 (mixedVector B) := by
    change mixedMoment B node1700 node1700Labels = _
    exact sound1700 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  simpa only [sourceForm1786, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1503, h1509, h1513, h1662, h1666, h1669, h1700, h1710, h1716, h1730, h1741, h2193, h2247, h2268, reducedSource1518] using sourceEq1786 B hB

theorem rowSound1518 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1518 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1518, numericCheck1518, reducedZero1518 B hB hF, mul_zero]

theorem reducedZero1519 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1519 (mixedVector B) = 0 := by
  have h598 : mixedVector B (Sum.inr 598) = Sparse.eval nodeValue598 (mixedVector B) := by
    change mixedMoment B node598 node598Labels = _
    exact sound598 B hB hF
  have h602 : mixedVector B (Sum.inr 602) = Sparse.eval nodeValue602 (mixedVector B) := by
    change mixedMoment B node602 node602Labels = _
    exact sound602 B hB hF
  have h607 : mixedVector B (Sum.inr 607) = Sparse.eval nodeValue607 (mixedVector B) := by
    change mixedMoment B node607 node607Labels = _
    exact sound607 B hB hF
  have h1080 : mixedVector B (Sum.inr 1080) = Sparse.eval nodeValue1080 (mixedVector B) := by
    change mixedMoment B node1080 node1080Labels = _
    exact sound1080 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1787, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h598, h602, h607, h1080, h4085, reducedSource1519] using sourceEq1787 B hB

theorem rowSound1519 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1519 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1519, numericCheck1519, reducedZero1519 B hB hF, mul_zero]

theorem sourceRowsAt1504 : MixedData.sourceRows (1504 : Fin 2425) =
    MixedData.row1504 := by decide +kernel

theorem sourceRowsAt1505 : MixedData.sourceRows (1505 : Fin 2425) =
    MixedData.row1505 := by decide +kernel

theorem sourceRowsAt1506 : MixedData.sourceRows (1506 : Fin 2425) =
    MixedData.row1506 := by decide +kernel

theorem sourceRowsAt1507 : MixedData.sourceRows (1507 : Fin 2425) =
    MixedData.row1507 := by decide +kernel

theorem sourceRowsAt1508 : MixedData.sourceRows (1508 : Fin 2425) =
    MixedData.row1508 := by decide +kernel

theorem sourceRowsAt1509 : MixedData.sourceRows (1509 : Fin 2425) =
    MixedData.row1509 := by decide +kernel

theorem sourceRowsAt1510 : MixedData.sourceRows (1510 : Fin 2425) =
    MixedData.row1510 := by decide +kernel

theorem sourceRowsAt1511 : MixedData.sourceRows (1511 : Fin 2425) =
    MixedData.row1511 := by decide +kernel

theorem sourceRowsAt1512 : MixedData.sourceRows (1512 : Fin 2425) =
    MixedData.row1512 := by decide +kernel

theorem sourceRowsAt1513 : MixedData.sourceRows (1513 : Fin 2425) =
    MixedData.row1513 := by decide +kernel

theorem sourceRowsAt1514 : MixedData.sourceRows (1514 : Fin 2425) =
    MixedData.row1514 := by decide +kernel

theorem sourceRowsAt1515 : MixedData.sourceRows (1515 : Fin 2425) =
    MixedData.row1515 := by decide +kernel

theorem sourceRowsAt1516 : MixedData.sourceRows (1516 : Fin 2425) =
    MixedData.row1516 := by decide +kernel

theorem sourceRowsAt1517 : MixedData.sourceRows (1517 : Fin 2425) =
    MixedData.row1517 := by decide +kernel

theorem sourceRowsAt1518 : MixedData.sourceRows (1518 : Fin 2425) =
    MixedData.row1518 := by decide +kernel

theorem sourceRowsAt1519 : MixedData.sourceRows (1519 : Fin 2425) =
    MixedData.row1519 := by decide +kernel

theorem chunkSound94_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 94) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1504 ∨ k.val = 1505 ∨ k.val = 1506 ∨ k.val = 1507 ∨ k.val = 1508 ∨ k.val = 1509 ∨ k.val = 1510 ∨ k.val = 1511 ∨ k.val = 1512 ∨ k.val = 1513 ∨ k.val = 1514 ∨ k.val = 1515 ∨ k.val = 1516 ∨ k.val = 1517 ∨ k.val = 1518 ∨ k.val = 1519 := by omega
  rcases heq with h1504 | h1505 | h1506 | h1507 | h1508 | h1509 | h1510 | h1511 | h1512 | h1513 | h1514 | h1515 | h1516 | h1517 | h1518 | h1519
  · have he : k = (1504 : Fin 2425) := Fin.ext h1504
    subst k
    rw [sourceRowsAt1504]
    exact rowSound1504 B hB hF
  · have he : k = (1505 : Fin 2425) := Fin.ext h1505
    subst k
    rw [sourceRowsAt1505]
    exact rowSound1505_e B hB hF
  · have he : k = (1506 : Fin 2425) := Fin.ext h1506
    subst k
    rw [sourceRowsAt1506]
    exact rowSound1506 B hB hF
  · have he : k = (1507 : Fin 2425) := Fin.ext h1507
    subst k
    rw [sourceRowsAt1507]
    exact rowSound1507_e B hB hF
  · have he : k = (1508 : Fin 2425) := Fin.ext h1508
    subst k
    rw [sourceRowsAt1508]
    exact rowSound1508_e B hB hF
  · have he : k = (1509 : Fin 2425) := Fin.ext h1509
    subst k
    rw [sourceRowsAt1509]
    exact rowSound1509 B hB hF
  · have he : k = (1510 : Fin 2425) := Fin.ext h1510
    subst k
    rw [sourceRowsAt1510]
    exact rowSound1510_e B hB hF
  · have he : k = (1511 : Fin 2425) := Fin.ext h1511
    subst k
    rw [sourceRowsAt1511]
    exact rowSound1511_e B hB hF
  · have he : k = (1512 : Fin 2425) := Fin.ext h1512
    subst k
    rw [sourceRowsAt1512]
    exact rowSound1512 B hB hF
  · have he : k = (1513 : Fin 2425) := Fin.ext h1513
    subst k
    rw [sourceRowsAt1513]
    exact rowSound1513_e B hB hF
  · have he : k = (1514 : Fin 2425) := Fin.ext h1514
    subst k
    rw [sourceRowsAt1514]
    exact rowSound1514_e B hB hF
  · have he : k = (1515 : Fin 2425) := Fin.ext h1515
    subst k
    rw [sourceRowsAt1515]
    exact rowSound1515 B hB hF
  · have he : k = (1516 : Fin 2425) := Fin.ext h1516
    subst k
    rw [sourceRowsAt1516]
    exact rowSound1516_e B hB hF
  · have he : k = (1517 : Fin 2425) := Fin.ext h1517
    subst k
    rw [sourceRowsAt1517]
    exact rowSound1517_e B hB hF
  · have he : k = (1518 : Fin 2425) := Fin.ext h1518
    subst k
    rw [sourceRowsAt1518]
    exact rowSound1518 B hB hF
  · have he : k = (1519 : Fin 2425) := Fin.ext h1519
    subst k
    rw [sourceRowsAt1519]
    exact rowSound1519 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94_e_oai
