-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:17:10.291285+00:00
-- url     : https://prove2.me/submissions/0a3c31b4-09d6-499b-a874-e30b9f43bc76

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1811_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1815_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1816_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1822_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18013 raw18013Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw18013 raw18013Labels = mixedMoment B raw18013step0 raw18013step0Labels := by
      have hz : ∀ j, raw18013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18013step0 = (fun i j => raw18013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18013step0 raw18013; decide +kernel
      have hl : raw18013step0Labels = raw18013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18013 raw18013Labels permutation434 hz
    mixedMoment B raw18013step0 raw18013step0Labels = mixedMoment B raw18013step1 raw18013step1Labels := by
      have hz : ∀ j, raw18013step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18013step1 = (fun i j => raw18013step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18013step1 raw18013step0; decide +kernel
      have hl : raw18013step1Labels = raw18013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18013step0 raw18013step0Labels permutation80 hz
    mixedMoment B raw18013step1 raw18013step1Labels = mixedMoment B raw18013step2 raw18013step2Labels := by
      have ha : raw18013step2 = (fun i j => raw18013step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18013step2 raw18013step1; decide +kernel
      have hl : raw18013step2Labels = raw18013step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18013step1 raw18013step1Labels permutation11 permutation5
    mixedMoment B raw18013step2 raw18013step2Labels = mixedMoment B raw18013step3 raw18013step3Labels := by
      have ha : raw18013step3 = -raw18013step2 := by apply Matrix.ext; change ∀ i j, raw18013step3 i j = -(raw18013step2 i j); unfold raw18013step3 raw18013step2; decide +kernel
      have hl : raw18013step3Labels = raw18013step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18013step3 raw18013step3Labels = mixedMoment B raw18013step4 raw18013step4Labels := by
      have ha : raw18013step4 = raw18013step3 := by apply Matrix.ext; unfold raw18013step4 raw18013step3; decide +kernel
      have hl : raw18013step3Labels = labelEmbedding1 ∘ raw18013step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18013step3 raw18013step3Labels raw18013step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical18018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18018 raw18018Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw18018 raw18018Labels = mixedMoment B raw18018step0 raw18018step0Labels := by
      have hz : ∀ j, raw18018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18018step0 = (fun i j => raw18018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18018step0 raw18018; decide +kernel
      have hl : raw18018step0Labels = raw18018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18018 raw18018Labels permutation434 hz
    mixedMoment B raw18018step0 raw18018step0Labels = mixedMoment B raw18018step1 raw18018step1Labels := by
      have ha : raw18018step1 = (fun i j => raw18018step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18018step1 raw18018step0; decide +kernel
      have hl : raw18018step1Labels = raw18018step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18018step0 raw18018step0Labels permutation44 permutation5
    mixedMoment B raw18018step1 raw18018step1Labels = mixedMoment B raw18018step2 raw18018step2Labels := by
      have ha : raw18018step2 = -raw18018step1 := by apply Matrix.ext; change ∀ i j, raw18018step2 i j = -(raw18018step1 i j); unfold raw18018step2 raw18018step1; decide +kernel
      have hl : raw18018step2Labels = raw18018step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18018step2 raw18018step2Labels = mixedMoment B raw18018step3 raw18018step3Labels := by
      have ha : raw18018step3 = raw18018step2 := by apply Matrix.ext; unfold raw18018step3 raw18018step2; decide +kernel
      have hl : raw18018step2Labels = labelEmbedding1 ∘ raw18018step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18018step2 raw18018step2Labels raw18018step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

theorem canonical18023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18023 raw18023Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw18023 raw18023Labels = mixedMoment B raw18023step0 raw18023step0Labels := by
      have hz : ∀ j, raw18023 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18023step0 = (fun i j => raw18023 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18023step0 raw18023; decide +kernel
      have hl : raw18023step0Labels = raw18023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18023 raw18023Labels permutation346 hz
    mixedMoment B raw18023step0 raw18023step0Labels = mixedMoment B raw18023step1 raw18023step1Labels := by
      have ha : raw18023step1 = (fun i j => raw18023step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18023step1 raw18023step0; decide +kernel
      have hl : raw18023step1Labels = raw18023step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18023step0 raw18023step0Labels permutation44 permutation5
    mixedMoment B raw18023step1 raw18023step1Labels = mixedMoment B raw18023step2 raw18023step2Labels := by
      have ha : raw18023step2 = -raw18023step1 := by apply Matrix.ext; change ∀ i j, raw18023step2 i j = -(raw18023step1 i j); unfold raw18023step2 raw18023step1; decide +kernel
      have hl : raw18023step2Labels = raw18023step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18023step2 raw18023step2Labels = mixedMoment B raw18023step3 raw18023step3Labels := by
      have ha : raw18023step3 = raw18023step2 := by apply Matrix.ext; unfold raw18023step3 raw18023step2; decide +kernel
      have hl : raw18023step2Labels = labelEmbedding1 ∘ raw18023step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18023step2 raw18023step2Labels raw18023step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

theorem canonical18029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18029 raw18029Labels = mixedMoment B node3775 node3775Labels := by
  calc
    mixedMoment B raw18029 raw18029Labels = mixedMoment B raw18029step0 raw18029step0Labels := by
      have hz : ∀ j, raw18029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18029step0 = (fun i j => raw18029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18029step0 raw18029; decide +kernel
      have hl : raw18029step0Labels = raw18029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18029 raw18029Labels permutation434 hz
    mixedMoment B raw18029step0 raw18029step0Labels = mixedMoment B raw18029step1 raw18029step1Labels := by
      have hz : ∀ j, raw18029step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18029step1 = (fun i j => raw18029step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18029step1 raw18029step0; decide +kernel
      have hl : raw18029step1Labels = raw18029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18029step0 raw18029step0Labels permutation80 hz
    mixedMoment B raw18029step1 raw18029step1Labels = mixedMoment B raw18029step2 raw18029step2Labels := by
      have ha : raw18029step2 = (fun i j => raw18029step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18029step2 raw18029step1; decide +kernel
      have hl : raw18029step2Labels = raw18029step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18029step1 raw18029step1Labels permutation24 permutation7
    mixedMoment B raw18029step2 raw18029step2Labels = mixedMoment B raw18029step3 raw18029step3Labels := by
      have ha : raw18029step3 = raw18029step2 := by apply Matrix.ext; unfold raw18029step3 raw18029step2; decide +kernel
      have hl : raw18029step2Labels = labelEmbedding1 ∘ raw18029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18029step2 raw18029step2Labels raw18029step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3775 node3775Labels := by rfl

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

theorem canonical18033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18033 raw18033Labels = mixedMoment B node3579 node3579Labels := by
  calc
    mixedMoment B raw18033 raw18033Labels = mixedMoment B raw18033step0 raw18033step0Labels := by
      have hz : ∀ j, raw18033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18033step0 = (fun i j => raw18033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18033step0 raw18033; decide +kernel
      have hl : raw18033step0Labels = raw18033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18033 raw18033Labels permutation434 hz
    mixedMoment B raw18033step0 raw18033step0Labels = mixedMoment B raw18033step1 raw18033step1Labels := by
      have hz : ∀ j, raw18033step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18033step1 = (fun i j => raw18033step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18033step1 raw18033step0; decide +kernel
      have hl : raw18033step1Labels = raw18033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18033step0 raw18033step0Labels permutation80 hz
    mixedMoment B raw18033step1 raw18033step1Labels = mixedMoment B raw18033step2 raw18033step2Labels := by
      have ha : raw18033step2 = (fun i j => raw18033step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18033step2 raw18033step1; decide +kernel
      have hl : raw18033step2Labels = raw18033step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18033step1 raw18033step1Labels permutation29 permutation5
    mixedMoment B raw18033step2 raw18033step2Labels = mixedMoment B raw18033step3 raw18033step3Labels := by
      have ha : raw18033step3 = raw18033step2 := by apply Matrix.ext; unfold raw18033step3 raw18033step2; decide +kernel
      have hl : raw18033step2Labels = labelEmbedding1 ∘ raw18033step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18033step2 raw18033step2Labels raw18033step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3579 node3579Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22699 raw22699Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw22699 raw22699Labels = mixedMoment B raw22699step0 raw22699step0Labels := by
      have hz : ∀ j, raw22699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22699step0 = (fun i j => raw22699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22699step0 raw22699; decide +kernel
      have hl : raw22699step0Labels = raw22699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22699 raw22699Labels permutation346 hz
    mixedMoment B raw22699step0 raw22699step0Labels = mixedMoment B raw22699step1 raw22699step1Labels := by
      have hz : ∀ j, raw22699step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22699step1 = (fun i j => raw22699step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22699step1 raw22699step0; decide +kernel
      have hl : raw22699step1Labels = raw22699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22699step0 raw22699step0Labels permutation56 hz
    mixedMoment B raw22699step1 raw22699step1Labels = mixedMoment B raw22699step2 raw22699step2Labels := by
      have ha : raw22699step2 = (fun i j => raw22699step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22699step2 raw22699step1; decide +kernel
      have hl : raw22699step2Labels = raw22699step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22699step1 raw22699step1Labels permutation9 permutation7
    mixedMoment B raw22699step2 raw22699step2Labels = mixedMoment B raw22699step3 raw22699step3Labels := by
      have ha : raw22699step3 = -raw22699step2 := by apply Matrix.ext; change ∀ i j, raw22699step3 i j = -(raw22699step2 i j); unfold raw22699step3 raw22699step2; decide +kernel
      have hl : raw22699step3Labels = raw22699step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22699step3 raw22699step3Labels = mixedMoment B raw22699step4 raw22699step4Labels := by
      have ha : raw22699step4 = raw22699step3 := by apply Matrix.ext; unfold raw22699step4 raw22699step3; decide +kernel
      have hl : raw22699step3Labels = labelEmbedding1 ∘ raw22699step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22699step3 raw22699step3Labels raw22699step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical22705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22705 raw22705Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw22705 raw22705Labels = mixedMoment B raw22705step0 raw22705step0Labels := by
      have ha : raw22705step0 = (fun i j => raw22705 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22705step0 raw22705; decide +kernel
      have hl : raw22705step0Labels = raw22705Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22705 raw22705Labels permutation166 permutation5
    mixedMoment B raw22705step0 raw22705step0Labels = mixedMoment B raw22705step1 raw22705step1Labels := by
      have ha : raw22705step1 = -raw22705step0 := by apply Matrix.ext; change ∀ i j, raw22705step1 i j = -(raw22705step0 i j); unfold raw22705step1 raw22705step0; decide +kernel
      have hl : raw22705step1Labels = raw22705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22705step1 raw22705step1Labels = mixedMoment B raw22705step2 raw22705step2Labels := by
      have ha : raw22705step2 = raw22705step1 := by apply Matrix.ext; unfold raw22705step2 raw22705step1; decide +kernel
      have hl : raw22705step1Labels = labelEmbedding1 ∘ raw22705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22705step1 raw22705step1Labels raw22705step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

theorem canonical22709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22709 raw22709Labels = mixedMoment B node3271 node3271Labels := by
  calc
    mixedMoment B raw22709 raw22709Labels = mixedMoment B raw22709step0 raw22709step0Labels := by
      have hz : ∀ j, raw22709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22709step0 = (fun i j => raw22709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22709step0 raw22709; decide +kernel
      have hl : raw22709step0Labels = raw22709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22709 raw22709Labels permutation346 hz
    mixedMoment B raw22709step0 raw22709step0Labels = mixedMoment B raw22709step1 raw22709step1Labels := by
      have ha : raw22709step1 = (fun i j => raw22709step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22709step1 raw22709step0; decide +kernel
      have hl : raw22709step1Labels = raw22709step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22709step0 raw22709step0Labels permutation35 permutation5
    mixedMoment B raw22709step1 raw22709step1Labels = mixedMoment B raw22709step2 raw22709step2Labels := by
      have ha : raw22709step2 = -raw22709step1 := by apply Matrix.ext; change ∀ i j, raw22709step2 i j = -(raw22709step1 i j); unfold raw22709step2 raw22709step1; decide +kernel
      have hl : raw22709step2Labels = raw22709step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22709step2 raw22709step2Labels = mixedMoment B raw22709step3 raw22709step3Labels := by
      have ha : raw22709step3 = raw22709step2 := by apply Matrix.ext; unfold raw22709step3 raw22709step2; decide +kernel
      have hl : raw22709step2Labels = labelEmbedding1 ∘ raw22709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22709step2 raw22709step2Labels raw22709step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3271 node3271Labels := by rfl

theorem canonical22713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22713 raw22713Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw22713 raw22713Labels = mixedMoment B raw22713step0 raw22713step0Labels := by
      have hz : ∀ j, raw22713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22713step0 = (fun i j => raw22713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22713step0 raw22713; decide +kernel
      have hl : raw22713step0Labels = raw22713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22713 raw22713Labels permutation346 hz
    mixedMoment B raw22713step0 raw22713step0Labels = mixedMoment B raw22713step1 raw22713step1Labels := by
      have ha : raw22713step1 = (fun i j => raw22713step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22713step1 raw22713step0; decide +kernel
      have hl : raw22713step1Labels = raw22713step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22713step0 raw22713step0Labels permutation33 permutation5
    mixedMoment B raw22713step1 raw22713step1Labels = mixedMoment B raw22713step2 raw22713step2Labels := by
      have ha : raw22713step2 = -raw22713step1 := by apply Matrix.ext; change ∀ i j, raw22713step2 i j = -(raw22713step1 i j); unfold raw22713step2 raw22713step1; decide +kernel
      have hl : raw22713step2Labels = raw22713step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22713step2 raw22713step2Labels = mixedMoment B raw22713step3 raw22713step3Labels := by
      have ha : raw22713step3 = raw22713step2 := by apply Matrix.ext; unfold raw22713step3 raw22713step2; decide +kernel
      have hl : raw22713step2Labels = labelEmbedding1 ∘ raw22713step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22713step2 raw22713step2Labels raw22713step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

theorem canonical22718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22718 raw22718Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw22718 raw22718Labels = mixedMoment B raw22718step0 raw22718step0Labels := by
      have hz : ∀ j, raw22718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22718step0 = (fun i j => raw22718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22718step0 raw22718; decide +kernel
      have hl : raw22718step0Labels = raw22718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22718 raw22718Labels permutation346 hz
    mixedMoment B raw22718step0 raw22718step0Labels = mixedMoment B raw22718step1 raw22718step1Labels := by
      have ha : raw22718step1 = (fun i j => raw22718step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22718step1 raw22718step0; decide +kernel
      have hl : raw22718step1Labels = raw22718step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22718step0 raw22718step0Labels permutation34 permutation5
    mixedMoment B raw22718step1 raw22718step1Labels = mixedMoment B raw22718step2 raw22718step2Labels := by
      have ha : raw22718step2 = -raw22718step1 := by apply Matrix.ext; change ∀ i j, raw22718step2 i j = -(raw22718step1 i j); unfold raw22718step2 raw22718step1; decide +kernel
      have hl : raw22718step2Labels = raw22718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22718step2 raw22718step2Labels = mixedMoment B raw22718step3 raw22718step3Labels := by
      have ha : raw22718step3 = raw22718step2 := by apply Matrix.ext; unfold raw22718step3 raw22718step2; decide +kernel
      have hl : raw22718step2Labels = labelEmbedding1 ∘ raw22718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22718step2 raw22718step2Labels raw22718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

theorem canonical22730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22730 raw22730Labels = mixedMoment B node1149 node1149Labels := by
  calc
    mixedMoment B raw22730 raw22730Labels = mixedMoment B raw22730step0 raw22730step0Labels := by
      have ha : raw22730step0 = (fun i j => raw22730 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22730step0 raw22730; decide +kernel
      have hl : raw22730step0Labels = raw22730Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22730 raw22730Labels permutation159 permutation2
    _ = mixedMoment B node1149 node1149Labels := by rfl

theorem canonical22731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22731 raw22731Labels = mixedMoment B node1160 node1160Labels := by
  calc
    mixedMoment B raw22731 raw22731Labels = mixedMoment B raw22731step0 raw22731step0Labels := by
      have hz : ∀ j, raw22731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22731step0 = (fun i j => raw22731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22731step0 raw22731; decide +kernel
      have hl : raw22731step0Labels = raw22731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22731 raw22731Labels permutation346 hz
    mixedMoment B raw22731step0 raw22731step0Labels = mixedMoment B raw22731step1 raw22731step1Labels := by
      have ha : raw22731step1 = (fun i j => raw22731step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22731step1 raw22731step0; decide +kernel
      have hl : raw22731step1Labels = raw22731step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22731step0 raw22731step0Labels permutation33 permutation2
    _ = mixedMoment B node1160 node1160Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical220
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28230 raw28230Labels = mixedMoment B node2820 node2820Labels := by
  calc
    mixedMoment B raw28230 raw28230Labels = mixedMoment B raw28230step0 raw28230step0Labels := by
      have hz : ∀ j, raw28230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28230step0 = (fun i j => raw28230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28230step0 raw28230; decide +kernel
      have hl : raw28230step0Labels = raw28230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28230 raw28230Labels permutation434 hz
    mixedMoment B raw28230step0 raw28230step0Labels = mixedMoment B raw28230step1 raw28230step1Labels := by
      have hz : ∀ j, raw28230step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28230step1 = (fun i j => raw28230step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28230step1 raw28230step0; decide +kernel
      have hl : raw28230step1Labels = raw28230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28230step0 raw28230step0Labels permutation80 hz
    _ = mixedMoment B node2820 node2820Labels := by rfl

theorem canonical28232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28232 raw28232Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw28232 raw28232Labels = mixedMoment B raw28232step0 raw28232step0Labels := by
      have hz : ∀ j, raw28232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28232step0 = (fun i j => raw28232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28232step0 raw28232; decide +kernel
      have hl : raw28232step0Labels = raw28232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28232 raw28232Labels permutation434 hz
    mixedMoment B raw28232step0 raw28232step0Labels = mixedMoment B raw28232step1 raw28232step1Labels := by
      have hz : ∀ j, raw28232step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28232step1 = (fun i j => raw28232step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28232step1 raw28232step0; decide +kernel
      have hl : raw28232step1Labels = raw28232step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28232step0 raw28232step0Labels permutation80 hz
    mixedMoment B raw28232step1 raw28232step1Labels = mixedMoment B raw28232step2 raw28232step2Labels := by
      have ha : raw28232step2 = (fun i j => raw28232step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28232step2 raw28232step1; decide +kernel
      have hl : raw28232step2Labels = raw28232step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28232step1 raw28232step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical233
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29927 raw29927Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw29927 raw29927Labels = mixedMoment B raw29927step0 raw29927step0Labels := by
      have hz : ∀ j, raw29927 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29927step0 = (fun i j => raw29927 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29927step0 raw29927; decide +kernel
      have hl : raw29927step0Labels = raw29927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29927 raw29927Labels permutation434 hz
    mixedMoment B raw29927step0 raw29927step0Labels = mixedMoment B raw29927step1 raw29927step1Labels := by
      have ha : raw29927step1 = (fun i j => raw29927step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29927step1 raw29927step0; decide +kernel
      have hl : raw29927step1Labels = raw29927step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29927step0 raw29927step0Labels permutation56 permutation2
    _ = mixedMoment B node3694 node3694Labels := by rfl

theorem canonical29928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29928 raw29928Labels = mixedMoment B node2868 node2868Labels := by
  calc
    mixedMoment B raw29928 raw29928Labels = mixedMoment B raw29928step0 raw29928step0Labels := by
      have hz : ∀ j, raw29928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29928step0 = (fun i j => raw29928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29928step0 raw29928; decide +kernel
      have hl : raw29928step0Labels = raw29928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29928 raw29928Labels permutation434 hz
    _ = mixedMoment B node2868 node2868Labels := by rfl

theorem canonical29929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29929 raw29929Labels = mixedMoment B node2818 node2818Labels := by
  calc
    mixedMoment B raw29929 raw29929Labels = mixedMoment B raw29929step0 raw29929step0Labels := by
      have hz : ∀ j, raw29929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29929step0 = (fun i j => raw29929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29929step0 raw29929; decide +kernel
      have hl : raw29929step0Labels = raw29929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29929 raw29929Labels permutation434 hz
    _ = mixedMoment B node2818 node2818Labels := by rfl

theorem canonical29930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29930 raw29930Labels = mixedMoment B node2799 node2799Labels := by
  calc
    _ = mixedMoment B node2799 node2799Labels := by rfl

theorem canonical29931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29931 raw29931Labels = mixedMoment B node2802 node2802Labels := by
  calc
    mixedMoment B raw29931 raw29931Labels = mixedMoment B raw29931step0 raw29931step0Labels := by
      have hz : ∀ j, raw29931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29931step0 = (fun i j => raw29931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29931step0 raw29931; decide +kernel
      have hl : raw29931step0Labels = raw29931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29931 raw29931Labels permutation434 hz
    mixedMoment B raw29931step0 raw29931step0Labels = mixedMoment B raw29931step1 raw29931step1Labels := by
      have ha : raw29931step1 = (fun i j => raw29931step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29931step1 raw29931step0; decide +kernel
      have hl : raw29931step1Labels = raw29931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29931step0 raw29931step0Labels permutation33 permutation2
    _ = mixedMoment B node2802 node2802Labels := by rfl

theorem canonical29932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29932 raw29932Labels = mixedMoment B node2802 node2802Labels := by
  calc
    mixedMoment B raw29932 raw29932Labels = mixedMoment B raw29932step0 raw29932step0Labels := by
      have hz : ∀ j, raw29932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29932step0 = (fun i j => raw29932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29932step0 raw29932; decide +kernel
      have hl : raw29932step0Labels = raw29932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29932 raw29932Labels permutation434 hz
    _ = mixedMoment B node2802 node2802Labels := by rfl

theorem canonical29933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29933 raw29933Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw29933 raw29933Labels = mixedMoment B raw29933step0 raw29933step0Labels := by
      have hz : ∀ j, raw29933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29933step0 = (fun i j => raw29933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29933step0 raw29933; decide +kernel
      have hl : raw29933step0Labels = raw29933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29933 raw29933Labels permutation434 hz
    mixedMoment B raw29933step0 raw29933step0Labels = mixedMoment B raw29933step1 raw29933step1Labels := by
      have ha : raw29933step1 = (fun i j => raw29933step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29933step1 raw29933step0; decide +kernel
      have hl : raw29933step1Labels = raw29933step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29933step0 raw29933step0Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical29934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29934 raw29934Labels = mixedMoment B node1322 node1322Labels := by
  calc
    mixedMoment B raw29934 raw29934Labels = mixedMoment B raw29934step0 raw29934step0Labels := by
      have hz : ∀ j, raw29934 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29934step0 = (fun i j => raw29934 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29934step0 raw29934; decide +kernel
      have hl : raw29934step0Labels = raw29934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29934 raw29934Labels permutation434 hz
    _ = mixedMoment B node1322 node1322Labels := by rfl

theorem canonical29935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29935 raw29935Labels = mixedMoment B node2849 node2849Labels := by
  calc
    mixedMoment B raw29935 raw29935Labels = mixedMoment B raw29935step0 raw29935step0Labels := by
      have ha : raw29935step0 = (fun i j => raw29935 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29935step0 raw29935; decide +kernel
      have hl : raw29935step0Labels = raw29935Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29935 raw29935Labels permutation158 permutation2
    _ = mixedMoment B node2849 node2849Labels := by rfl

theorem canonical29936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29936 raw29936Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw29936 raw29936Labels = mixedMoment B raw29936step0 raw29936step0Labels := by
      have hz : ∀ j, raw29936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29936step0 = (fun i j => raw29936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29936step0 raw29936; decide +kernel
      have hl : raw29936step0Labels = raw29936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29936 raw29936Labels permutation434 hz
    _ = mixedMoment B node2884 node2884Labels := by rfl

theorem canonical29937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29937 raw29937Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw29937 raw29937Labels = mixedMoment B raw29937step0 raw29937step0Labels := by
      have hz : ∀ j, raw29937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29937step0 = (fun i j => raw29937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29937step0 raw29937; decide +kernel
      have hl : raw29937step0Labels = raw29937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29937 raw29937Labels permutation434 hz
    mixedMoment B raw29937step0 raw29937step0Labels = mixedMoment B raw29937step1 raw29937step1Labels := by
      have ha : raw29937step1 = (fun i j => raw29937step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29937step1 raw29937step0; decide +kernel
      have hl : raw29937step1Labels = raw29937step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29937step0 raw29937step0Labels permutation33 permutation2
    _ = mixedMoment B node2884 node2884Labels := by rfl

theorem canonical29938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29938 raw29938Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw29938 raw29938Labels = mixedMoment B raw29938step0 raw29938step0Labels := by
      have hz : ∀ j, raw29938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29938step0 = (fun i j => raw29938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29938step0 raw29938; decide +kernel
      have hl : raw29938step0Labels = raw29938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29938 raw29938Labels permutation434 hz
    mixedMoment B raw29938step0 raw29938step0Labels = mixedMoment B raw29938step1 raw29938step1Labels := by
      have hz : ∀ j, raw29938step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29938step1 = (fun i j => raw29938step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29938step1 raw29938step0; decide +kernel
      have hl : raw29938step1Labels = raw29938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29938step0 raw29938step0Labels permutation80 hz
    mixedMoment B raw29938step1 raw29938step1Labels = mixedMoment B raw29938step2 raw29938step2Labels := by
      have ha : raw29938step2 = (fun i j => raw29938step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29938step2 raw29938step1; decide +kernel
      have hl : raw29938step2Labels = raw29938step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29938step1 raw29938step1Labels permutation24 permutation2
    mixedMoment B raw29938step2 raw29938step2Labels = mixedMoment B raw29938step3 raw29938step3Labels := by
      have ha : raw29938step3 = -raw29938step2 := by apply Matrix.ext; change ∀ i j, raw29938step3 i j = -(raw29938step2 i j); unfold raw29938step3 raw29938step2; decide +kernel
      have hl : raw29938step3Labels = raw29938step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3397 node3397Labels := by rfl

theorem canonical29939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29939 raw29939Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw29939 raw29939Labels = mixedMoment B raw29939step0 raw29939step0Labels := by
      have hz : ∀ j, raw29939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29939step0 = (fun i j => raw29939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29939step0 raw29939; decide +kernel
      have hl : raw29939step0Labels = raw29939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29939 raw29939Labels permutation434 hz
    mixedMoment B raw29939step0 raw29939step0Labels = mixedMoment B raw29939step1 raw29939step1Labels := by
      have hz : ∀ j, raw29939step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29939step1 = (fun i j => raw29939step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29939step1 raw29939step0; decide +kernel
      have hl : raw29939step1Labels = raw29939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29939step0 raw29939step0Labels permutation80 hz
    mixedMoment B raw29939step1 raw29939step1Labels = mixedMoment B raw29939step2 raw29939step2Labels := by
      have ha : raw29939step2 = (fun i j => raw29939step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29939step2 raw29939step1; decide +kernel
      have hl : raw29939step2Labels = raw29939step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29939step1 raw29939step1Labels permutation9 permutation2
    _ = mixedMoment B node2888 node2888Labels := by rfl

theorem canonical29940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29940 raw29940Labels = mixedMoment B node2812 node2812Labels := by
  calc
    mixedMoment B raw29940 raw29940Labels = mixedMoment B raw29940step0 raw29940step0Labels := by
      have hz : ∀ j, raw29940 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29940step0 = (fun i j => raw29940 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29940step0 raw29940; decide +kernel
      have hl : raw29940step0Labels = raw29940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29940 raw29940Labels permutation434 hz
    mixedMoment B raw29940step0 raw29940step0Labels = mixedMoment B raw29940step1 raw29940step1Labels := by
      have ha : raw29940step1 = (fun i j => raw29940step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29940step1 raw29940step0; decide +kernel
      have hl : raw29940step1Labels = raw29940step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29940step0 raw29940step0Labels permutation33 permutation2
    _ = mixedMoment B node2812 node2812Labels := by rfl

theorem canonical29941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29941 raw29941Labels = mixedMoment B node2812 node2812Labels := by
  calc
    mixedMoment B raw29941 raw29941Labels = mixedMoment B raw29941step0 raw29941step0Labels := by
      have hz : ∀ j, raw29941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29941step0 = (fun i j => raw29941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29941step0 raw29941; decide +kernel
      have hl : raw29941step0Labels = raw29941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29941 raw29941Labels permutation346 hz
    mixedMoment B raw29941step0 raw29941step0Labels = mixedMoment B raw29941step1 raw29941step1Labels := by
      have ha : raw29941step1 = (fun i j => raw29941step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29941step1 raw29941step0; decide +kernel
      have hl : raw29941step1Labels = raw29941step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29941step0 raw29941step0Labels permutation33 permutation2
    _ = mixedMoment B node2812 node2812Labels := by rfl

theorem canonical29942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29942 raw29942Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw29942 raw29942Labels = mixedMoment B raw29942step0 raw29942step0Labels := by
      have hz : ∀ j, raw29942 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29942step0 = (fun i j => raw29942 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29942step0 raw29942; decide +kernel
      have hl : raw29942step0Labels = raw29942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29942 raw29942Labels permutation434 hz
    mixedMoment B raw29942step0 raw29942step0Labels = mixedMoment B raw29942step1 raw29942step1Labels := by
      have hz : ∀ j, raw29942step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29942step1 = (fun i j => raw29942step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29942step1 raw29942step0; decide +kernel
      have hl : raw29942step1Labels = raw29942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29942step0 raw29942step0Labels permutation80 hz
    mixedMoment B raw29942step1 raw29942step1Labels = mixedMoment B raw29942step2 raw29942step2Labels := by
      have ha : raw29942step2 = (fun i j => raw29942step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29942step2 raw29942step1; decide +kernel
      have hl : raw29942step2Labels = raw29942step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29942step1 raw29942step1Labels permutation25 permutation2
    mixedMoment B raw29942step2 raw29942step2Labels = mixedMoment B raw29942step3 raw29942step3Labels := by
      have ha : raw29942step3 = -raw29942step2 := by apply Matrix.ext; change ∀ i j, raw29942step3 i j = -(raw29942step2 i j); unfold raw29942step3 raw29942step2; decide +kernel
      have hl : raw29942step3Labels = raw29942step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1819 node1819Labels := by rfl

theorem canonical29943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29943 raw29943Labels = mixedMoment B node2821 node2821Labels := by
  calc
    mixedMoment B raw29943 raw29943Labels = mixedMoment B raw29943step0 raw29943step0Labels := by
      have hz : ∀ j, raw29943 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29943step0 = (fun i j => raw29943 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29943step0 raw29943; decide +kernel
      have hl : raw29943step0Labels = raw29943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29943 raw29943Labels permutation434 hz
    mixedMoment B raw29943step0 raw29943step0Labels = mixedMoment B raw29943step1 raw29943step1Labels := by
      have hz : ∀ j, raw29943step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29943step1 = (fun i j => raw29943step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29943step1 raw29943step0; decide +kernel
      have hl : raw29943step1Labels = raw29943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29943step0 raw29943step0Labels permutation80 hz
    _ = mixedMoment B node2821 node2821Labels := by rfl

theorem canonical29944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29944 raw29944Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw29944 raw29944Labels = mixedMoment B raw29944step0 raw29944step0Labels := by
      have hz : ∀ j, raw29944 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw29944step0 = (fun i j => raw29944 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw29944step0 raw29944; decide +kernel
      have hl : raw29944step0Labels = raw29944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29944 raw29944Labels permutation590 hz
    mixedMoment B raw29944step0 raw29944step0Labels = mixedMoment B raw29944step1 raw29944step1Labels := by
      have hz : ∀ j, raw29944step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29944step1 = (fun i j => raw29944step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29944step1 raw29944step0; decide +kernel
      have hl : raw29944step1Labels = raw29944step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29944step0 raw29944step0Labels permutation104 hz
    mixedMoment B raw29944step1 raw29944step1Labels = mixedMoment B raw29944step2 raw29944step2Labels := by
      have hz : ∀ j, raw29944step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29944step2 = (fun i j => raw29944step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29944step2 raw29944step1; decide +kernel
      have hl : raw29944step2Labels = raw29944step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29944step1 raw29944step1Labels permutation20 hz
    mixedMoment B raw29944step2 raw29944step2Labels = mixedMoment B raw29944step3 raw29944step3Labels := by
      have ha : raw29944step3 = (fun i j => raw29944step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29944step3 raw29944step2; decide +kernel
      have hl : raw29944step3Labels = raw29944step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29944step2 raw29944step2Labels permutation6 permutation0
    mixedMoment B raw29944step3 raw29944step3Labels = mixedMoment B raw29944step4 raw29944step4Labels := by
      have ha : raw29944step4 = -raw29944step3 := by apply Matrix.ext; change ∀ i j, raw29944step4 i j = -(raw29944step3 i j); unfold raw29944step4 raw29944step3; decide +kernel
      have hl : raw29944step4Labels = raw29944step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

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

theorem canonical30002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30002 raw30002Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw30002 raw30002Labels = mixedMoment B raw30002step0 raw30002step0Labels := by
      have hz : ∀ j, raw30002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30002step0 = (fun i j => raw30002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30002step0 raw30002; decide +kernel
      have hl : raw30002step0Labels = raw30002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30002 raw30002Labels permutation434 hz
    mixedMoment B raw30002step0 raw30002step0Labels = mixedMoment B raw30002step1 raw30002step1Labels := by
      have hz : ∀ j, raw30002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30002step1 = (fun i j => raw30002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30002step1 raw30002step0; decide +kernel
      have hl : raw30002step1Labels = raw30002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30002step0 raw30002step0Labels permutation80 hz
    mixedMoment B raw30002step1 raw30002step1Labels = mixedMoment B raw30002step2 raw30002step2Labels := by
      have ha : raw30002step2 = (fun i j => raw30002step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30002step2 raw30002step1; decide +kernel
      have hl : raw30002step2Labels = raw30002step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30002step1 raw30002step1Labels permutation11 permutation5
    mixedMoment B raw30002step2 raw30002step2Labels = mixedMoment B raw30002step3 raw30002step3Labels := by
      have ha : raw30002step3 = -raw30002step2 := by apply Matrix.ext; change ∀ i j, raw30002step3 i j = -(raw30002step2 i j); unfold raw30002step3 raw30002step2; decide +kernel
      have hl : raw30002step3Labels = raw30002step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30002step3 raw30002step3Labels = mixedMoment B raw30002step4 raw30002step4Labels := by
      have ha : raw30002step4 = raw30002step3 := by apply Matrix.ext; unfold raw30002step4 raw30002step3; decide +kernel
      have hl : raw30002step3Labels = labelEmbedding1 ∘ raw30002step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30002step3 raw30002step3Labels raw30002step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

theorem canonical30003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30003 raw30003Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw30003 raw30003Labels = mixedMoment B raw30003step0 raw30003step0Labels := by
      have hz : ∀ j, raw30003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30003step0 = (fun i j => raw30003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30003step0 raw30003; decide +kernel
      have hl : raw30003step0Labels = raw30003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30003 raw30003Labels permutation434 hz
    mixedMoment B raw30003step0 raw30003step0Labels = mixedMoment B raw30003step1 raw30003step1Labels := by
      have ha : raw30003step1 = (fun i j => raw30003step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30003step1 raw30003step0; decide +kernel
      have hl : raw30003step1Labels = raw30003step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30003step0 raw30003step0Labels permutation41 permutation5
    mixedMoment B raw30003step1 raw30003step1Labels = mixedMoment B raw30003step2 raw30003step2Labels := by
      have ha : raw30003step2 = -raw30003step1 := by apply Matrix.ext; change ∀ i j, raw30003step2 i j = -(raw30003step1 i j); unfold raw30003step2 raw30003step1; decide +kernel
      have hl : raw30003step2Labels = raw30003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30003step2 raw30003step2Labels = mixedMoment B raw30003step3 raw30003step3Labels := by
      have ha : raw30003step3 = raw30003step2 := by apply Matrix.ext; unfold raw30003step3 raw30003step2; decide +kernel
      have hl : raw30003step2Labels = labelEmbedding1 ∘ raw30003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30003step2 raw30003step2Labels raw30003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

theorem canonical30004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30004 raw30004Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw30004 raw30004Labels = mixedMoment B raw30004step0 raw30004step0Labels := by
      have hz : ∀ j, raw30004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30004step0 = (fun i j => raw30004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30004step0 raw30004; decide +kernel
      have hl : raw30004step0Labels = raw30004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30004 raw30004Labels permutation346 hz
    mixedMoment B raw30004step0 raw30004step0Labels = mixedMoment B raw30004step1 raw30004step1Labels := by
      have ha : raw30004step1 = (fun i j => raw30004step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30004step1 raw30004step0; decide +kernel
      have hl : raw30004step1Labels = raw30004step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30004step0 raw30004step0Labels permutation41 permutation5
    mixedMoment B raw30004step1 raw30004step1Labels = mixedMoment B raw30004step2 raw30004step2Labels := by
      have ha : raw30004step2 = -raw30004step1 := by apply Matrix.ext; change ∀ i j, raw30004step2 i j = -(raw30004step1 i j); unfold raw30004step2 raw30004step1; decide +kernel
      have hl : raw30004step2Labels = raw30004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30004step2 raw30004step2Labels = mixedMoment B raw30004step3 raw30004step3Labels := by
      have ha : raw30004step3 = raw30004step2 := by apply Matrix.ext; unfold raw30004step3 raw30004step2; decide +kernel
      have hl : raw30004step2Labels = labelEmbedding1 ∘ raw30004step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30004step2 raw30004step2Labels raw30004step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

theorem canonical30005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30005 raw30005Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw30005 raw30005Labels = mixedMoment B raw30005step0 raw30005step0Labels := by
      have hz : ∀ j, raw30005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30005step0 = (fun i j => raw30005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30005step0 raw30005; decide +kernel
      have hl : raw30005step0Labels = raw30005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30005 raw30005Labels permutation434 hz
    mixedMoment B raw30005step0 raw30005step0Labels = mixedMoment B raw30005step1 raw30005step1Labels := by
      have hz : ∀ j, raw30005step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30005step1 = (fun i j => raw30005step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30005step1 raw30005step0; decide +kernel
      have hl : raw30005step1Labels = raw30005step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30005step0 raw30005step0Labels permutation80 hz
    mixedMoment B raw30005step1 raw30005step1Labels = mixedMoment B raw30005step2 raw30005step2Labels := by
      have ha : raw30005step2 = (fun i j => raw30005step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30005step2 raw30005step1; decide +kernel
      have hl : raw30005step2Labels = raw30005step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30005step1 raw30005step1Labels permutation13 permutation5
    mixedMoment B raw30005step2 raw30005step2Labels = mixedMoment B raw30005step3 raw30005step3Labels := by
      have ha : raw30005step3 = -raw30005step2 := by apply Matrix.ext; change ∀ i j, raw30005step3 i j = -(raw30005step2 i j); unfold raw30005step3 raw30005step2; decide +kernel
      have hl : raw30005step3Labels = raw30005step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30005step3 raw30005step3Labels = mixedMoment B raw30005step4 raw30005step4Labels := by
      have ha : raw30005step4 = raw30005step3 := by apply Matrix.ext; unfold raw30005step4 raw30005step3; decide +kernel
      have hl : raw30005step3Labels = labelEmbedding1 ∘ raw30005step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30005step3 raw30005step3Labels raw30005step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical30006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30006 raw30006Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw30006 raw30006Labels = mixedMoment B raw30006step0 raw30006step0Labels := by
      have hz : ∀ j, raw30006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30006step0 = (fun i j => raw30006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30006step0 raw30006; decide +kernel
      have hl : raw30006step0Labels = raw30006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30006 raw30006Labels permutation434 hz
    mixedMoment B raw30006step0 raw30006step0Labels = mixedMoment B raw30006step1 raw30006step1Labels := by
      have ha : raw30006step1 = (fun i j => raw30006step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30006step1 raw30006step0; decide +kernel
      have hl : raw30006step1Labels = raw30006step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30006step0 raw30006step0Labels permutation44 permutation5
    mixedMoment B raw30006step1 raw30006step1Labels = mixedMoment B raw30006step2 raw30006step2Labels := by
      have ha : raw30006step2 = -raw30006step1 := by apply Matrix.ext; change ∀ i j, raw30006step2 i j = -(raw30006step1 i j); unfold raw30006step2 raw30006step1; decide +kernel
      have hl : raw30006step2Labels = raw30006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30006step2 raw30006step2Labels = mixedMoment B raw30006step3 raw30006step3Labels := by
      have ha : raw30006step3 = raw30006step2 := by apply Matrix.ext; unfold raw30006step3 raw30006step2; decide +kernel
      have hl : raw30006step2Labels = labelEmbedding1 ∘ raw30006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30006step2 raw30006step2Labels raw30006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

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

theorem canonical30008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30008 raw30008Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw30008 raw30008Labels = mixedMoment B raw30008step0 raw30008step0Labels := by
      have ha : raw30008step0 = (fun i j => raw30008 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30008step0 raw30008; decide +kernel
      have hl : raw30008step0Labels = raw30008Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30008 raw30008Labels permutation212 permutation5
    mixedMoment B raw30008step0 raw30008step0Labels = mixedMoment B raw30008step1 raw30008step1Labels := by
      have ha : raw30008step1 = -raw30008step0 := by apply Matrix.ext; change ∀ i j, raw30008step1 i j = -(raw30008step0 i j); unfold raw30008step1 raw30008step0; decide +kernel
      have hl : raw30008step1Labels = raw30008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30008step1 raw30008step1Labels = mixedMoment B raw30008step2 raw30008step2Labels := by
      have ha : raw30008step2 = raw30008step1 := by apply Matrix.ext; unfold raw30008step2 raw30008step1; decide +kernel
      have hl : raw30008step1Labels = labelEmbedding1 ∘ raw30008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30008step1 raw30008step1Labels raw30008step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

theorem canonical30009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30009 raw30009Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw30009 raw30009Labels = mixedMoment B raw30009step0 raw30009step0Labels := by
      have hz : ∀ j, raw30009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30009step0 = (fun i j => raw30009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30009step0 raw30009; decide +kernel
      have hl : raw30009step0Labels = raw30009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30009 raw30009Labels permutation434 hz
    mixedMoment B raw30009step0 raw30009step0Labels = mixedMoment B raw30009step1 raw30009step1Labels := by
      have ha : raw30009step1 = (fun i j => raw30009step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30009step1 raw30009step0; decide +kernel
      have hl : raw30009step1Labels = raw30009step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30009step0 raw30009step0Labels permutation54 permutation5
    mixedMoment B raw30009step1 raw30009step1Labels = mixedMoment B raw30009step2 raw30009step2Labels := by
      have ha : raw30009step2 = -raw30009step1 := by apply Matrix.ext; change ∀ i j, raw30009step2 i j = -(raw30009step1 i j); unfold raw30009step2 raw30009step1; decide +kernel
      have hl : raw30009step2Labels = raw30009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30009step2 raw30009step2Labels = mixedMoment B raw30009step3 raw30009step3Labels := by
      have ha : raw30009step3 = raw30009step2 := by apply Matrix.ext; unfold raw30009step3 raw30009step2; decide +kernel
      have hl : raw30009step2Labels = labelEmbedding1 ∘ raw30009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30009step2 raw30009step2Labels raw30009step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

theorem canonical30010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30010 raw30010Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw30010 raw30010Labels = mixedMoment B raw30010step0 raw30010step0Labels := by
      have hz : ∀ j, raw30010 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30010step0 = (fun i j => raw30010 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30010step0 raw30010; decide +kernel
      have hl : raw30010step0Labels = raw30010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30010 raw30010Labels permutation346 hz
    mixedMoment B raw30010step0 raw30010step0Labels = mixedMoment B raw30010step1 raw30010step1Labels := by
      have ha : raw30010step1 = (fun i j => raw30010step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30010step1 raw30010step0; decide +kernel
      have hl : raw30010step1Labels = raw30010step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30010step0 raw30010step0Labels permutation44 permutation5
    mixedMoment B raw30010step1 raw30010step1Labels = mixedMoment B raw30010step2 raw30010step2Labels := by
      have ha : raw30010step2 = -raw30010step1 := by apply Matrix.ext; change ∀ i j, raw30010step2 i j = -(raw30010step1 i j); unfold raw30010step2 raw30010step1; decide +kernel
      have hl : raw30010step2Labels = raw30010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30010step2 raw30010step2Labels = mixedMoment B raw30010step3 raw30010step3Labels := by
      have ha : raw30010step3 = raw30010step2 := by apply Matrix.ext; unfold raw30010step3 raw30010step2; decide +kernel
      have hl : raw30010step2Labels = labelEmbedding1 ∘ raw30010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30010step2 raw30010step2Labels raw30010step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

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

theorem canonical30012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30012 raw30012Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw30012 raw30012Labels = mixedMoment B raw30012step0 raw30012step0Labels := by
      have ha : raw30012step0 = (fun i j => raw30012 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30012step0 raw30012; decide +kernel
      have hl : raw30012step0Labels = raw30012Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30012 raw30012Labels permutation188 permutation5
    mixedMoment B raw30012step0 raw30012step0Labels = mixedMoment B raw30012step1 raw30012step1Labels := by
      have ha : raw30012step1 = -raw30012step0 := by apply Matrix.ext; change ∀ i j, raw30012step1 i j = -(raw30012step0 i j); unfold raw30012step1 raw30012step0; decide +kernel
      have hl : raw30012step1Labels = raw30012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30012step1 raw30012step1Labels = mixedMoment B raw30012step2 raw30012step2Labels := by
      have ha : raw30012step2 = raw30012step1 := by apply Matrix.ext; unfold raw30012step2 raw30012step1; decide +kernel
      have hl : raw30012step1Labels = labelEmbedding1 ∘ raw30012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30012step1 raw30012step1Labels raw30012step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

theorem canonical30013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30013 raw30013Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw30013 raw30013Labels = mixedMoment B raw30013step0 raw30013step0Labels := by
      have hz : ∀ j, raw30013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30013step0 = (fun i j => raw30013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30013step0 raw30013; decide +kernel
      have hl : raw30013step0Labels = raw30013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30013 raw30013Labels permutation346 hz
    mixedMoment B raw30013step0 raw30013step0Labels = mixedMoment B raw30013step1 raw30013step1Labels := by
      have ha : raw30013step1 = (fun i j => raw30013step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30013step1 raw30013step0; decide +kernel
      have hl : raw30013step1Labels = raw30013step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30013step0 raw30013step0Labels permutation54 permutation5
    mixedMoment B raw30013step1 raw30013step1Labels = mixedMoment B raw30013step2 raw30013step2Labels := by
      have ha : raw30013step2 = -raw30013step1 := by apply Matrix.ext; change ∀ i j, raw30013step2 i j = -(raw30013step1 i j); unfold raw30013step2 raw30013step1; decide +kernel
      have hl : raw30013step2Labels = raw30013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30013step2 raw30013step2Labels = mixedMoment B raw30013step3 raw30013step3Labels := by
      have ha : raw30013step3 = raw30013step2 := by apply Matrix.ext; unfold raw30013step3 raw30013step2; decide +kernel
      have hl : raw30013step2Labels = labelEmbedding1 ∘ raw30013step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30013step2 raw30013step2Labels raw30013step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

theorem canonical30014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30014 raw30014Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw30014 raw30014Labels = mixedMoment B raw30014step0 raw30014step0Labels := by
      have hz : ∀ j, raw30014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30014step0 = (fun i j => raw30014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30014step0 raw30014; decide +kernel
      have hl : raw30014step0Labels = raw30014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30014 raw30014Labels permutation434 hz
    mixedMoment B raw30014step0 raw30014step0Labels = mixedMoment B raw30014step1 raw30014step1Labels := by
      have hz : ∀ j, raw30014step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30014step1 = (fun i j => raw30014step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30014step1 raw30014step0; decide +kernel
      have hl : raw30014step1Labels = raw30014step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30014step0 raw30014step0Labels permutation80 hz
    mixedMoment B raw30014step1 raw30014step1Labels = mixedMoment B raw30014step2 raw30014step2Labels := by
      have ha : raw30014step2 = (fun i j => raw30014step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30014step2 raw30014step1; decide +kernel
      have hl : raw30014step2Labels = raw30014step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30014step1 raw30014step1Labels permutation9 permutation5
    mixedMoment B raw30014step2 raw30014step2Labels = mixedMoment B raw30014step3 raw30014step3Labels := by
      have ha : raw30014step3 = -raw30014step2 := by apply Matrix.ext; change ∀ i j, raw30014step3 i j = -(raw30014step2 i j); unfold raw30014step3 raw30014step2; decide +kernel
      have hl : raw30014step3Labels = raw30014step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30014step3 raw30014step3Labels = mixedMoment B raw30014step4 raw30014step4Labels := by
      have ha : raw30014step4 = raw30014step3 := by apply Matrix.ext; unfold raw30014step4 raw30014step3; decide +kernel
      have hl : raw30014step3Labels = labelEmbedding1 ∘ raw30014step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30014step3 raw30014step3Labels raw30014step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

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

theorem canonical30016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30016 raw30016Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw30016 raw30016Labels = mixedMoment B raw30016step0 raw30016step0Labels := by
      have hz : ∀ j, raw30016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30016step0 = (fun i j => raw30016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30016step0 raw30016; decide +kernel
      have hl : raw30016step0Labels = raw30016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30016 raw30016Labels permutation434 hz
    mixedMoment B raw30016step0 raw30016step0Labels = mixedMoment B raw30016step1 raw30016step1Labels := by
      have ha : raw30016step1 = (fun i j => raw30016step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30016step1 raw30016step0; decide +kernel
      have hl : raw30016step1Labels = raw30016step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30016step0 raw30016step0Labels permutation126 permutation7
    mixedMoment B raw30016step1 raw30016step1Labels = mixedMoment B raw30016step2 raw30016step2Labels := by
      have ha : raw30016step2 = raw30016step1 := by apply Matrix.ext; unfold raw30016step2 raw30016step1; decide +kernel
      have hl : raw30016step1Labels = labelEmbedding1 ∘ raw30016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30016step1 raw30016step1Labels raw30016step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

theorem canonical30017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30017 raw30017Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw30017 raw30017Labels = mixedMoment B raw30017step0 raw30017step0Labels := by
      have hz : ∀ j, raw30017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30017step0 = (fun i j => raw30017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30017step0 raw30017; decide +kernel
      have hl : raw30017step0Labels = raw30017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30017 raw30017Labels permutation346 hz
    mixedMoment B raw30017step0 raw30017step0Labels = mixedMoment B raw30017step1 raw30017step1Labels := by
      have ha : raw30017step1 = (fun i j => raw30017step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30017step1 raw30017step0; decide +kernel
      have hl : raw30017step1Labels = raw30017step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30017step0 raw30017step0Labels permutation126 permutation7
    mixedMoment B raw30017step1 raw30017step1Labels = mixedMoment B raw30017step2 raw30017step2Labels := by
      have ha : raw30017step2 = raw30017step1 := by apply Matrix.ext; unfold raw30017step2 raw30017step1; decide +kernel
      have hl : raw30017step1Labels = labelEmbedding1 ∘ raw30017step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30017step1 raw30017step1Labels raw30017step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

theorem canonical30018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30018 raw30018Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw30018 raw30018Labels = mixedMoment B raw30018step0 raw30018step0Labels := by
      have hz : ∀ j, raw30018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30018step0 = (fun i j => raw30018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30018step0 raw30018; decide +kernel
      have hl : raw30018step0Labels = raw30018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30018 raw30018Labels permutation434 hz
    mixedMoment B raw30018step0 raw30018step0Labels = mixedMoment B raw30018step1 raw30018step1Labels := by
      have hz : ∀ j, raw30018step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30018step1 = (fun i j => raw30018step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30018step1 raw30018step0; decide +kernel
      have hl : raw30018step1Labels = raw30018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30018step0 raw30018step0Labels permutation80 hz
    mixedMoment B raw30018step1 raw30018step1Labels = mixedMoment B raw30018step2 raw30018step2Labels := by
      have ha : raw30018step2 = (fun i j => raw30018step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30018step2 raw30018step1; decide +kernel
      have hl : raw30018step2Labels = raw30018step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30018step1 raw30018step1Labels permutation24 permutation7
    mixedMoment B raw30018step2 raw30018step2Labels = mixedMoment B raw30018step3 raw30018step3Labels := by
      have ha : raw30018step3 = raw30018step2 := by apply Matrix.ext; unfold raw30018step3 raw30018step2; decide +kernel
      have hl : raw30018step2Labels = labelEmbedding1 ∘ raw30018step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30018step2 raw30018step2Labels raw30018step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

theorem canonical30019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30019 raw30019Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw30019 raw30019Labels = mixedMoment B raw30019step0 raw30019step0Labels := by
      have hz : ∀ j, raw30019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30019step0 = (fun i j => raw30019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30019step0 raw30019; decide +kernel
      have hl : raw30019step0Labels = raw30019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30019 raw30019Labels permutation434 hz
    mixedMoment B raw30019step0 raw30019step0Labels = mixedMoment B raw30019step1 raw30019step1Labels := by
      have hz : ∀ j, raw30019step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30019step1 = (fun i j => raw30019step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30019step1 raw30019step0; decide +kernel
      have hl : raw30019step1Labels = raw30019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30019step0 raw30019step0Labels permutation80 hz
    mixedMoment B raw30019step1 raw30019step1Labels = mixedMoment B raw30019step2 raw30019step2Labels := by
      have ha : raw30019step2 = (fun i j => raw30019step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30019step2 raw30019step1; decide +kernel
      have hl : raw30019step2Labels = raw30019step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30019step1 raw30019step1Labels permutation10 permutation5
    mixedMoment B raw30019step2 raw30019step2Labels = mixedMoment B raw30019step3 raw30019step3Labels := by
      have ha : raw30019step3 = -raw30019step2 := by apply Matrix.ext; change ∀ i j, raw30019step3 i j = -(raw30019step2 i j); unfold raw30019step3 raw30019step2; decide +kernel
      have hl : raw30019step3Labels = raw30019step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30019step3 raw30019step3Labels = mixedMoment B raw30019step4 raw30019step4Labels := by
      have ha : raw30019step4 = raw30019step3 := by apply Matrix.ext; unfold raw30019step4 raw30019step3; decide +kernel
      have hl : raw30019step3Labels = labelEmbedding1 ∘ raw30019step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30019step3 raw30019step3Labels raw30019step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1735 node1735Labels := by rfl

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

theorem canonical30021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30021 raw30021Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw30021 raw30021Labels = mixedMoment B raw30021step0 raw30021step0Labels := by
      have hz : ∀ j, raw30021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30021step0 = (fun i j => raw30021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30021step0 raw30021; decide +kernel
      have hl : raw30021step0Labels = raw30021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30021 raw30021Labels permutation434 hz
    mixedMoment B raw30021step0 raw30021step0Labels = mixedMoment B raw30021step1 raw30021step1Labels := by
      have ha : raw30021step1 = (fun i j => raw30021step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30021step1 raw30021step0; decide +kernel
      have hl : raw30021step1Labels = raw30021step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30021step0 raw30021step0Labels permutation40 permutation5
    mixedMoment B raw30021step1 raw30021step1Labels = mixedMoment B raw30021step2 raw30021step2Labels := by
      have ha : raw30021step2 = -raw30021step1 := by apply Matrix.ext; change ∀ i j, raw30021step2 i j = -(raw30021step1 i j); unfold raw30021step2 raw30021step1; decide +kernel
      have hl : raw30021step2Labels = raw30021step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30021step2 raw30021step2Labels = mixedMoment B raw30021step3 raw30021step3Labels := by
      have ha : raw30021step3 = raw30021step2 := by apply Matrix.ext; unfold raw30021step3 raw30021step2; decide +kernel
      have hl : raw30021step2Labels = labelEmbedding1 ∘ raw30021step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30021step2 raw30021step2Labels raw30021step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

theorem canonical30022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30022 raw30022Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw30022 raw30022Labels = mixedMoment B raw30022step0 raw30022step0Labels := by
      have hz : ∀ j, raw30022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30022step0 = (fun i j => raw30022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30022step0 raw30022; decide +kernel
      have hl : raw30022step0Labels = raw30022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30022 raw30022Labels permutation346 hz
    mixedMoment B raw30022step0 raw30022step0Labels = mixedMoment B raw30022step1 raw30022step1Labels := by
      have ha : raw30022step1 = (fun i j => raw30022step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30022step1 raw30022step0; decide +kernel
      have hl : raw30022step1Labels = raw30022step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30022step0 raw30022step0Labels permutation40 permutation5
    mixedMoment B raw30022step1 raw30022step1Labels = mixedMoment B raw30022step2 raw30022step2Labels := by
      have ha : raw30022step2 = -raw30022step1 := by apply Matrix.ext; change ∀ i j, raw30022step2 i j = -(raw30022step1 i j); unfold raw30022step2 raw30022step1; decide +kernel
      have hl : raw30022step2Labels = raw30022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30022step2 raw30022step2Labels = mixedMoment B raw30022step3 raw30022step3Labels := by
      have ha : raw30022step3 = raw30022step2 := by apply Matrix.ext; unfold raw30022step3 raw30022step2; decide +kernel
      have hl : raw30022step2Labels = labelEmbedding1 ∘ raw30022step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30022step2 raw30022step2Labels raw30022step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

theorem canonical30023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30023 raw30023Labels = mixedMoment B node3707 node3707Labels := by
  calc
    mixedMoment B raw30023 raw30023Labels = mixedMoment B raw30023step0 raw30023step0Labels := by
      have hz : ∀ j, raw30023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30023step0 = (fun i j => raw30023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30023step0 raw30023; decide +kernel
      have hl : raw30023step0Labels = raw30023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30023 raw30023Labels permutation434 hz
    mixedMoment B raw30023step0 raw30023step0Labels = mixedMoment B raw30023step1 raw30023step1Labels := by
      have hz : ∀ j, raw30023step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30023step1 = (fun i j => raw30023step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30023step1 raw30023step0; decide +kernel
      have hl : raw30023step1Labels = raw30023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30023step0 raw30023step0Labels permutation80 hz
    mixedMoment B raw30023step1 raw30023step1Labels = mixedMoment B raw30023step2 raw30023step2Labels := by
      have ha : raw30023step2 = (fun i j => raw30023step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30023step2 raw30023step1; decide +kernel
      have hl : raw30023step2Labels = raw30023step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30023step1 raw30023step1Labels permutation15 permutation2
    _ = mixedMoment B node3707 node3707Labels := by rfl

theorem canonical30024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30024 raw30024Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw30024 raw30024Labels = mixedMoment B raw30024step0 raw30024step0Labels := by
      have hz : ∀ j, raw30024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30024step0 = (fun i j => raw30024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30024step0 raw30024; decide +kernel
      have hl : raw30024step0Labels = raw30024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30024 raw30024Labels permutation434 hz
    mixedMoment B raw30024step0 raw30024step0Labels = mixedMoment B raw30024step1 raw30024step1Labels := by
      have hz : ∀ j, raw30024step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30024step1 = (fun i j => raw30024step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30024step1 raw30024step0; decide +kernel
      have hl : raw30024step1Labels = raw30024step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30024step0 raw30024step0Labels permutation80 hz
    mixedMoment B raw30024step1 raw30024step1Labels = mixedMoment B raw30024step2 raw30024step2Labels := by
      have ha : raw30024step2 = (fun i j => raw30024step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30024step2 raw30024step1; decide +kernel
      have hl : raw30024step2Labels = raw30024step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30024step1 raw30024step1Labels permutation9 permutation2
    _ = mixedMoment B node2889 node2889Labels := by rfl

theorem canonical30025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30025 raw30025Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw30025 raw30025Labels = mixedMoment B raw30025step0 raw30025step0Labels := by
      have hz : ∀ j, raw30025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30025step0 = (fun i j => raw30025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30025step0 raw30025; decide +kernel
      have hl : raw30025step0Labels = raw30025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30025 raw30025Labels permutation434 hz
    mixedMoment B raw30025step0 raw30025step0Labels = mixedMoment B raw30025step1 raw30025step1Labels := by
      have ha : raw30025step1 = (fun i j => raw30025step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30025step1 raw30025step0; decide +kernel
      have hl : raw30025step1Labels = raw30025step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30025step0 raw30025step0Labels permutation33 permutation2
    _ = mixedMoment B node2813 node2813Labels := by rfl

theorem canonical30026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30026 raw30026Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw30026 raw30026Labels = mixedMoment B raw30026step0 raw30026step0Labels := by
      have hz : ∀ j, raw30026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30026step0 = (fun i j => raw30026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30026step0 raw30026; decide +kernel
      have hl : raw30026step0Labels = raw30026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30026 raw30026Labels permutation346 hz
    mixedMoment B raw30026step0 raw30026step0Labels = mixedMoment B raw30026step1 raw30026step1Labels := by
      have ha : raw30026step1 = (fun i j => raw30026step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30026step1 raw30026step0; decide +kernel
      have hl : raw30026step1Labels = raw30026step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30026step0 raw30026step0Labels permutation33 permutation2
    _ = mixedMoment B node2813 node2813Labels := by rfl

theorem canonical30027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30027 raw30027Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw30027 raw30027Labels = mixedMoment B raw30027step0 raw30027step0Labels := by
      have hz : ∀ j, raw30027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30027step0 = (fun i j => raw30027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30027step0 raw30027; decide +kernel
      have hl : raw30027step0Labels = raw30027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30027 raw30027Labels permutation434 hz
    mixedMoment B raw30027step0 raw30027step0Labels = mixedMoment B raw30027step1 raw30027step1Labels := by
      have hz : ∀ j, raw30027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30027step1 = (fun i j => raw30027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30027step1 raw30027step0; decide +kernel
      have hl : raw30027step1Labels = raw30027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30027step0 raw30027step0Labels permutation80 hz
    mixedMoment B raw30027step1 raw30027step1Labels = mixedMoment B raw30027step2 raw30027step2Labels := by
      have ha : raw30027step2 = (fun i j => raw30027step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30027step2 raw30027step1; decide +kernel
      have hl : raw30027step2Labels = raw30027step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30027step1 raw30027step1Labels permutation25 permutation2
    mixedMoment B raw30027step2 raw30027step2Labels = mixedMoment B raw30027step3 raw30027step3Labels := by
      have ha : raw30027step3 = -raw30027step2 := by apply Matrix.ext; change ∀ i j, raw30027step3 i j = -(raw30027step2 i j); unfold raw30027step3 raw30027step2; decide +kernel
      have hl : raw30027step3Labels = raw30027step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2345 node2345Labels := by rfl

theorem canonical30069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30069 raw30069Labels = mixedMoment B node2533 node2533Labels := by
  calc
    mixedMoment B raw30069 raw30069Labels = mixedMoment B raw30069step0 raw30069step0Labels := by
      have ha : raw30069step0 = (fun i j => raw30069 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30069step0 raw30069; decide +kernel
      have hl : raw30069step0Labels = raw30069Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30069 raw30069Labels permutation159 permutation2
    _ = mixedMoment B node2533 node2533Labels := by rfl

theorem canonical30070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30070 raw30070Labels = mixedMoment B node3679 node3679Labels := by
  calc
    mixedMoment B raw30070 raw30070Labels = mixedMoment B raw30070step0 raw30070step0Labels := by
      have ha : raw30070step0 = (fun i j => raw30070 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30070step0 raw30070; decide +kernel
      have hl : raw30070step0Labels = raw30070Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30070 raw30070Labels permutation584 permutation2
    mixedMoment B raw30070step0 raw30070step0Labels = mixedMoment B raw30070step1 raw30070step1Labels := by
      have ha : raw30070step1 = -raw30070step0 := by apply Matrix.ext; change ∀ i j, raw30070step1 i j = -(raw30070step0 i j); unfold raw30070step1 raw30070step0; decide +kernel
      have hl : raw30070step1Labels = raw30070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3679 node3679Labels := by rfl

theorem canonical30071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30071 raw30071Labels = mixedMoment B node3695 node3695Labels := by
  calc
    mixedMoment B raw30071 raw30071Labels = mixedMoment B raw30071step0 raw30071step0Labels := by
      have ha : raw30071step0 = (fun i j => raw30071 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30071step0 raw30071; decide +kernel
      have hl : raw30071step0Labels = raw30071Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30071 raw30071Labels permutation589 permutation2
    mixedMoment B raw30071step0 raw30071step0Labels = mixedMoment B raw30071step1 raw30071step1Labels := by
      have ha : raw30071step1 = -raw30071step0 := by apply Matrix.ext; change ∀ i j, raw30071step1 i j = -(raw30071step0 i j); unfold raw30071step1 raw30071step0; decide +kernel
      have hl : raw30071step1Labels = raw30071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3695 node3695Labels := by rfl

theorem canonical30072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30072 raw30072Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw30072 raw30072Labels = mixedMoment B raw30072step0 raw30072step0Labels := by
      have ha : raw30072step0 = (fun i j => raw30072 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30072step0 raw30072; decide +kernel
      have hl : raw30072step0Labels = raw30072Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30072 raw30072Labels permutation582 permutation2
    mixedMoment B raw30072step0 raw30072step0Labels = mixedMoment B raw30072step1 raw30072step1Labels := by
      have ha : raw30072step1 = -raw30072step0 := by apply Matrix.ext; change ∀ i j, raw30072step1 i j = -(raw30072step0 i j); unfold raw30072step1 raw30072step0; decide +kernel
      have hl : raw30072step1Labels = raw30072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3681 node3681Labels := by rfl

theorem canonical30073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30073 raw30073Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw30073 raw30073Labels = mixedMoment B raw30073step0 raw30073step0Labels := by
      have ha : raw30073step0 = (fun i j => raw30073 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30073step0 raw30073; decide +kernel
      have hl : raw30073step0Labels = raw30073Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30073 raw30073Labels permutation158 permutation2
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical30074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30074 raw30074Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw30074 raw30074Labels = mixedMoment B raw30074step0 raw30074step0Labels := by
      have ha : raw30074step0 = (fun i j => raw30074 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30074step0 raw30074; decide +kernel
      have hl : raw30074step0Labels = raw30074Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30074 raw30074Labels permutation584 permutation2
    mixedMoment B raw30074step0 raw30074step0Labels = mixedMoment B raw30074step1 raw30074step1Labels := by
      have ha : raw30074step1 = -raw30074step0 := by apply Matrix.ext; change ∀ i j, raw30074step1 i j = -(raw30074step0 i j); unfold raw30074step1 raw30074step0; decide +kernel
      have hl : raw30074step1Labels = raw30074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical30075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30075 raw30075Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw30075 raw30075Labels = mixedMoment B raw30075step0 raw30075step0Labels := by
      have hz : ∀ j, raw30075 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw30075step0 = (fun i j => raw30075 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw30075step0 raw30075; decide +kernel
      have hl : raw30075step0Labels = raw30075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30075 raw30075Labels permutation265 hz
    mixedMoment B raw30075step0 raw30075step0Labels = mixedMoment B raw30075step1 raw30075step1Labels := by
      have ha : raw30075step1 = (fun i j => raw30075step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30075step1 raw30075step0; decide +kernel
      have hl : raw30075step1Labels = raw30075step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30075step0 raw30075step0Labels permutation39 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical235
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30110 raw30110Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw30110 raw30110Labels = mixedMoment B raw30110step0 raw30110step0Labels := by
      have hz : ∀ j, raw30110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30110step0 = (fun i j => raw30110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30110step0 raw30110; decide +kernel
      have hl : raw30110step0Labels = raw30110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30110 raw30110Labels permutation346 hz
    mixedMoment B raw30110step0 raw30110step0Labels = mixedMoment B raw30110step1 raw30110step1Labels := by
      have ha : raw30110step1 = (fun i j => raw30110step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30110step1 raw30110step0; decide +kernel
      have hl : raw30110step1Labels = raw30110step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30110step0 raw30110step0Labels permutation125 permutation7
    mixedMoment B raw30110step1 raw30110step1Labels = mixedMoment B raw30110step2 raw30110step2Labels := by
      have ha : raw30110step2 = raw30110step1 := by apply Matrix.ext; unfold raw30110step2 raw30110step1; decide +kernel
      have hl : raw30110step1Labels = labelEmbedding1 ∘ raw30110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30110step1 raw30110step1Labels raw30110step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

theorem canonical30111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30111 raw30111Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw30111 raw30111Labels = mixedMoment B raw30111step0 raw30111step0Labels := by
      have ha : raw30111step0 = (fun i j => raw30111 (permutation577 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30111step0 raw30111; decide +kernel
      have hl : raw30111step0Labels = raw30111Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30111 raw30111Labels permutation577 permutation7
    mixedMoment B raw30111step0 raw30111step0Labels = mixedMoment B raw30111step1 raw30111step1Labels := by
      have ha : raw30111step1 = raw30111step0 := by apply Matrix.ext; unfold raw30111step1 raw30111step0; decide +kernel
      have hl : raw30111step0Labels = labelEmbedding1 ∘ raw30111step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30111step0 raw30111step0Labels raw30111step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

theorem canonical30112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30112 raw30112Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw30112 raw30112Labels = mixedMoment B raw30112step0 raw30112step0Labels := by
      have hz : ∀ j, raw30112 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30112step0 = (fun i j => raw30112 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30112step0 raw30112; decide +kernel
      have hl : raw30112step0Labels = raw30112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30112 raw30112Labels permutation346 hz
    mixedMoment B raw30112step0 raw30112step0Labels = mixedMoment B raw30112step1 raw30112step1Labels := by
      have ha : raw30112step1 = (fun i j => raw30112step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30112step1 raw30112step0; decide +kernel
      have hl : raw30112step1Labels = raw30112step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30112step0 raw30112step0Labels permutation125 permutation7
    mixedMoment B raw30112step1 raw30112step1Labels = mixedMoment B raw30112step2 raw30112step2Labels := by
      have ha : raw30112step2 = raw30112step1 := by apply Matrix.ext; unfold raw30112step2 raw30112step1; decide +kernel
      have hl : raw30112step1Labels = labelEmbedding1 ∘ raw30112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30112step1 raw30112step1Labels raw30112step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical30113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30113 raw30113Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw30113 raw30113Labels = mixedMoment B raw30113step0 raw30113step0Labels := by
      have hz : ∀ j, raw30113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30113step0 = (fun i j => raw30113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30113step0 raw30113; decide +kernel
      have hl : raw30113step0Labels = raw30113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30113 raw30113Labels permutation346 hz
    mixedMoment B raw30113step0 raw30113step0Labels = mixedMoment B raw30113step1 raw30113step1Labels := by
      have ha : raw30113step1 = (fun i j => raw30113step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30113step1 raw30113step0; decide +kernel
      have hl : raw30113step1Labels = raw30113step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30113step0 raw30113step0Labels permutation125 permutation7
    mixedMoment B raw30113step1 raw30113step1Labels = mixedMoment B raw30113step2 raw30113step2Labels := by
      have ha : raw30113step2 = raw30113step1 := by apply Matrix.ext; unfold raw30113step2 raw30113step1; decide +kernel
      have hl : raw30113step1Labels = labelEmbedding1 ∘ raw30113step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30113step1 raw30113step1Labels raw30113step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical30114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30114 raw30114Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw30114 raw30114Labels = mixedMoment B raw30114step0 raw30114step0Labels := by
      have ha : raw30114step0 = (fun i j => raw30114 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30114step0 raw30114; decide +kernel
      have hl : raw30114step0Labels = raw30114Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30114 raw30114Labels permutation201 permutation7
    mixedMoment B raw30114step0 raw30114step0Labels = mixedMoment B raw30114step1 raw30114step1Labels := by
      have ha : raw30114step1 = -raw30114step0 := by apply Matrix.ext; change ∀ i j, raw30114step1 i j = -(raw30114step0 i j); unfold raw30114step1 raw30114step0; decide +kernel
      have hl : raw30114step1Labels = raw30114step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30114step1 raw30114step1Labels = mixedMoment B raw30114step2 raw30114step2Labels := by
      have ha : raw30114step2 = raw30114step1 := by apply Matrix.ext; unfold raw30114step2 raw30114step1; decide +kernel
      have hl : raw30114step1Labels = labelEmbedding1 ∘ raw30114step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30114step1 raw30114step1Labels raw30114step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

theorem canonical30115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30115 raw30115Labels = mixedMoment B node3450 node3450Labels := by
  calc
    mixedMoment B raw30115 raw30115Labels = mixedMoment B raw30115step0 raw30115step0Labels := by
      have ha : raw30115step0 = (fun i j => raw30115 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30115step0 raw30115; decide +kernel
      have hl : raw30115step0Labels = raw30115Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30115 raw30115Labels permutation201 permutation7
    mixedMoment B raw30115step0 raw30115step0Labels = mixedMoment B raw30115step1 raw30115step1Labels := by
      have ha : raw30115step1 = -raw30115step0 := by apply Matrix.ext; change ∀ i j, raw30115step1 i j = -(raw30115step0 i j); unfold raw30115step1 raw30115step0; decide +kernel
      have hl : raw30115step1Labels = raw30115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30115step1 raw30115step1Labels = mixedMoment B raw30115step2 raw30115step2Labels := by
      have ha : raw30115step2 = raw30115step1 := by apply Matrix.ext; unfold raw30115step2 raw30115step1; decide +kernel
      have hl : raw30115step1Labels = labelEmbedding1 ∘ raw30115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30115step1 raw30115step1Labels raw30115step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3450 node3450Labels := by rfl

theorem canonical30116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30116 raw30116Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw30116 raw30116Labels = mixedMoment B raw30116step0 raw30116step0Labels := by
      have ha : raw30116step0 = (fun i j => raw30116 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30116step0 raw30116; decide +kernel
      have hl : raw30116step0Labels = raw30116Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30116 raw30116Labels permutation201 permutation7
    mixedMoment B raw30116step0 raw30116step0Labels = mixedMoment B raw30116step1 raw30116step1Labels := by
      have ha : raw30116step1 = -raw30116step0 := by apply Matrix.ext; change ∀ i j, raw30116step1 i j = -(raw30116step0 i j); unfold raw30116step1 raw30116step0; decide +kernel
      have hl : raw30116step1Labels = raw30116step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30116step1 raw30116step1Labels = mixedMoment B raw30116step2 raw30116step2Labels := by
      have ha : raw30116step2 = raw30116step1 := by apply Matrix.ext; unfold raw30116step2 raw30116step1; decide +kernel
      have hl : raw30116step1Labels = labelEmbedding1 ∘ raw30116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30116step1 raw30116step1Labels raw30116step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical30117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30117 raw30117Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw30117 raw30117Labels = mixedMoment B raw30117step0 raw30117step0Labels := by
      have hz : ∀ j, raw30117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30117step0 = (fun i j => raw30117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30117step0 raw30117; decide +kernel
      have hl : raw30117step0Labels = raw30117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30117 raw30117Labels permutation346 hz
    mixedMoment B raw30117step0 raw30117step0Labels = mixedMoment B raw30117step1 raw30117step1Labels := by
      have ha : raw30117step1 = (fun i j => raw30117step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30117step1 raw30117step0; decide +kernel
      have hl : raw30117step1Labels = raw30117step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30117step0 raw30117step0Labels permutation39 permutation7
    mixedMoment B raw30117step1 raw30117step1Labels = mixedMoment B raw30117step2 raw30117step2Labels := by
      have ha : raw30117step2 = -raw30117step1 := by apply Matrix.ext; change ∀ i j, raw30117step2 i j = -(raw30117step1 i j); unfold raw30117step2 raw30117step1; decide +kernel
      have hl : raw30117step2Labels = raw30117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30117step2 raw30117step2Labels = mixedMoment B raw30117step3 raw30117step3Labels := by
      have ha : raw30117step3 = raw30117step2 := by apply Matrix.ext; unfold raw30117step3 raw30117step2; decide +kernel
      have hl : raw30117step2Labels = labelEmbedding1 ∘ raw30117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30117step2 raw30117step2Labels raw30117step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

theorem canonical30118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30118 raw30118Labels = mixedMoment B node3556 node3556Labels := by
  calc
    mixedMoment B raw30118 raw30118Labels = mixedMoment B raw30118step0 raw30118step0Labels := by
      have ha : raw30118step0 = (fun i j => raw30118 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30118step0 raw30118; decide +kernel
      have hl : raw30118step0Labels = raw30118Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30118 raw30118Labels permutation201 permutation7
    mixedMoment B raw30118step0 raw30118step0Labels = mixedMoment B raw30118step1 raw30118step1Labels := by
      have ha : raw30118step1 = -raw30118step0 := by apply Matrix.ext; change ∀ i j, raw30118step1 i j = -(raw30118step0 i j); unfold raw30118step1 raw30118step0; decide +kernel
      have hl : raw30118step1Labels = raw30118step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30118step1 raw30118step1Labels = mixedMoment B raw30118step2 raw30118step2Labels := by
      have ha : raw30118step2 = raw30118step1 := by apply Matrix.ext; unfold raw30118step2 raw30118step1; decide +kernel
      have hl : raw30118step1Labels = labelEmbedding1 ∘ raw30118step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30118step1 raw30118step1Labels raw30118step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3556 node3556Labels := by rfl

theorem canonical30119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30119 raw30119Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw30119 raw30119Labels = mixedMoment B raw30119step0 raw30119step0Labels := by
      have hz : ∀ j, raw30119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30119step0 = (fun i j => raw30119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30119step0 raw30119; decide +kernel
      have hl : raw30119step0Labels = raw30119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30119 raw30119Labels permutation346 hz
    mixedMoment B raw30119step0 raw30119step0Labels = mixedMoment B raw30119step1 raw30119step1Labels := by
      have ha : raw30119step1 = (fun i j => raw30119step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30119step1 raw30119step0; decide +kernel
      have hl : raw30119step1Labels = raw30119step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30119step0 raw30119step0Labels permutation39 permutation7
    mixedMoment B raw30119step1 raw30119step1Labels = mixedMoment B raw30119step2 raw30119step2Labels := by
      have ha : raw30119step2 = -raw30119step1 := by apply Matrix.ext; change ∀ i j, raw30119step2 i j = -(raw30119step1 i j); unfold raw30119step2 raw30119step1; decide +kernel
      have hl : raw30119step2Labels = raw30119step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30119step2 raw30119step2Labels = mixedMoment B raw30119step3 raw30119step3Labels := by
      have ha : raw30119step3 = raw30119step2 := by apply Matrix.ext; unfold raw30119step3 raw30119step2; decide +kernel
      have hl : raw30119step2Labels = labelEmbedding1 ∘ raw30119step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30119step2 raw30119step2Labels raw30119step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical30120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30120 raw30120Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw30120 raw30120Labels = mixedMoment B raw30120step0 raw30120step0Labels := by
      have hz : ∀ j, raw30120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30120step0 = (fun i j => raw30120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30120step0 raw30120; decide +kernel
      have hl : raw30120step0Labels = raw30120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30120 raw30120Labels permutation346 hz
    mixedMoment B raw30120step0 raw30120step0Labels = mixedMoment B raw30120step1 raw30120step1Labels := by
      have ha : raw30120step1 = (fun i j => raw30120step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30120step1 raw30120step0; decide +kernel
      have hl : raw30120step1Labels = raw30120step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30120step0 raw30120step0Labels permutation125 permutation7
    mixedMoment B raw30120step1 raw30120step1Labels = mixedMoment B raw30120step2 raw30120step2Labels := by
      have ha : raw30120step2 = raw30120step1 := by apply Matrix.ext; unfold raw30120step2 raw30120step1; decide +kernel
      have hl : raw30120step1Labels = labelEmbedding1 ∘ raw30120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30120step1 raw30120step1Labels raw30120step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

theorem canonical30121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30121 raw30121Labels = mixedMoment B node3403 node3403Labels := by
  calc
    mixedMoment B raw30121 raw30121Labels = mixedMoment B raw30121step0 raw30121step0Labels := by
      have ha : raw30121step0 = (fun i j => raw30121 (permutation577 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30121step0 raw30121; decide +kernel
      have hl : raw30121step0Labels = raw30121Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30121 raw30121Labels permutation577 permutation7
    mixedMoment B raw30121step0 raw30121step0Labels = mixedMoment B raw30121step1 raw30121step1Labels := by
      have ha : raw30121step1 = raw30121step0 := by apply Matrix.ext; unfold raw30121step1 raw30121step0; decide +kernel
      have hl : raw30121step0Labels = labelEmbedding1 ∘ raw30121step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30121step0 raw30121step0Labels raw30121step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3403 node3403Labels := by rfl

theorem canonical30122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30122 raw30122Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw30122 raw30122Labels = mixedMoment B raw30122step0 raw30122step0Labels := by
      have hz : ∀ j, raw30122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30122step0 = (fun i j => raw30122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30122step0 raw30122; decide +kernel
      have hl : raw30122step0Labels = raw30122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30122 raw30122Labels permutation346 hz
    mixedMoment B raw30122step0 raw30122step0Labels = mixedMoment B raw30122step1 raw30122step1Labels := by
      have ha : raw30122step1 = (fun i j => raw30122step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30122step1 raw30122step0; decide +kernel
      have hl : raw30122step1Labels = raw30122step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30122step0 raw30122step0Labels permutation125 permutation7
    mixedMoment B raw30122step1 raw30122step1Labels = mixedMoment B raw30122step2 raw30122step2Labels := by
      have ha : raw30122step2 = raw30122step1 := by apply Matrix.ext; unfold raw30122step2 raw30122step1; decide +kernel
      have hl : raw30122step1Labels = labelEmbedding1 ∘ raw30122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30122step1 raw30122step1Labels raw30122step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

theorem canonical30123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30123 raw30123Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw30123 raw30123Labels = mixedMoment B raw30123step0 raw30123step0Labels := by
      have hz : ∀ j, raw30123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30123step0 = (fun i j => raw30123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30123step0 raw30123; decide +kernel
      have hl : raw30123step0Labels = raw30123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30123 raw30123Labels permutation346 hz
    mixedMoment B raw30123step0 raw30123step0Labels = mixedMoment B raw30123step1 raw30123step1Labels := by
      have ha : raw30123step1 = (fun i j => raw30123step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30123step1 raw30123step0; decide +kernel
      have hl : raw30123step1Labels = raw30123step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30123step0 raw30123step0Labels permutation125 permutation7
    mixedMoment B raw30123step1 raw30123step1Labels = mixedMoment B raw30123step2 raw30123step2Labels := by
      have ha : raw30123step2 = raw30123step1 := by apply Matrix.ext; unfold raw30123step2 raw30123step1; decide +kernel
      have hl : raw30123step1Labels = labelEmbedding1 ∘ raw30123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30123step1 raw30123step1Labels raw30123step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical30124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30124 raw30124Labels = mixedMoment B node3512 node3512Labels := by
  calc
    mixedMoment B raw30124 raw30124Labels = mixedMoment B raw30124step0 raw30124step0Labels := by
      have hz : ∀ j, raw30124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30124step0 = (fun i j => raw30124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30124step0 raw30124; decide +kernel
      have hl : raw30124step0Labels = raw30124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30124 raw30124Labels permutation346 hz
    mixedMoment B raw30124step0 raw30124step0Labels = mixedMoment B raw30124step1 raw30124step1Labels := by
      have ha : raw30124step1 = (fun i j => raw30124step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30124step1 raw30124step0; decide +kernel
      have hl : raw30124step1Labels = raw30124step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30124step0 raw30124step0Labels permutation144 permutation5
    mixedMoment B raw30124step1 raw30124step1Labels = mixedMoment B raw30124step2 raw30124step2Labels := by
      have ha : raw30124step2 = raw30124step1 := by apply Matrix.ext; unfold raw30124step2 raw30124step1; decide +kernel
      have hl : raw30124step1Labels = labelEmbedding1 ∘ raw30124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30124step1 raw30124step1Labels raw30124step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3512 node3512Labels := by rfl

theorem canonical30125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30125 raw30125Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw30125 raw30125Labels = mixedMoment B raw30125step0 raw30125step0Labels := by
      have ha : raw30125step0 = (fun i j => raw30125 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30125step0 raw30125; decide +kernel
      have hl : raw30125step0Labels = raw30125Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30125 raw30125Labels permutation662 permutation5
    mixedMoment B raw30125step0 raw30125step0Labels = mixedMoment B raw30125step1 raw30125step1Labels := by
      have ha : raw30125step1 = raw30125step0 := by apply Matrix.ext; unfold raw30125step1 raw30125step0; decide +kernel
      have hl : raw30125step0Labels = labelEmbedding1 ∘ raw30125step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30125step0 raw30125step0Labels raw30125step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3510 node3510Labels := by rfl

theorem canonical30126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30126 raw30126Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw30126 raw30126Labels = mixedMoment B raw30126step0 raw30126step0Labels := by
      have hz : ∀ j, raw30126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30126step0 = (fun i j => raw30126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30126step0 raw30126; decide +kernel
      have hl : raw30126step0Labels = raw30126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30126 raw30126Labels permutation346 hz
    mixedMoment B raw30126step0 raw30126step0Labels = mixedMoment B raw30126step1 raw30126step1Labels := by
      have ha : raw30126step1 = (fun i j => raw30126step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30126step1 raw30126step0; decide +kernel
      have hl : raw30126step1Labels = raw30126step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30126step0 raw30126step0Labels permutation39 permutation7
    mixedMoment B raw30126step1 raw30126step1Labels = mixedMoment B raw30126step2 raw30126step2Labels := by
      have ha : raw30126step2 = -raw30126step1 := by apply Matrix.ext; change ∀ i j, raw30126step2 i j = -(raw30126step1 i j); unfold raw30126step2 raw30126step1; decide +kernel
      have hl : raw30126step2Labels = raw30126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30126step2 raw30126step2Labels = mixedMoment B raw30126step3 raw30126step3Labels := by
      have ha : raw30126step3 = raw30126step2 := by apply Matrix.ext; unfold raw30126step3 raw30126step2; decide +kernel
      have hl : raw30126step2Labels = labelEmbedding1 ∘ raw30126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30126step2 raw30126step2Labels raw30126step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

theorem canonical30127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30127 raw30127Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw30127 raw30127Labels = mixedMoment B raw30127step0 raw30127step0Labels := by
      have hz : ∀ j, raw30127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30127step0 = (fun i j => raw30127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30127step0 raw30127; decide +kernel
      have hl : raw30127step0Labels = raw30127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30127 raw30127Labels permutation346 hz
    mixedMoment B raw30127step0 raw30127step0Labels = mixedMoment B raw30127step1 raw30127step1Labels := by
      have ha : raw30127step1 = (fun i j => raw30127step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30127step1 raw30127step0; decide +kernel
      have hl : raw30127step1Labels = raw30127step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30127step0 raw30127step0Labels permutation127 permutation2
    mixedMoment B raw30127step1 raw30127step1Labels = mixedMoment B raw30127step2 raw30127step2Labels := by
      have ha : raw30127step2 = -raw30127step1 := by apply Matrix.ext; change ∀ i j, raw30127step2 i j = -(raw30127step1 i j); unfold raw30127step2 raw30127step1; decide +kernel
      have hl : raw30127step2Labels = raw30127step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical30128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30128 raw30128Labels = mixedMoment B node2348 node2348Labels := by
  calc
    mixedMoment B raw30128 raw30128Labels = mixedMoment B raw30128step0 raw30128step0Labels := by
      have ha : raw30128step0 = (fun i j => raw30128 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30128step0 raw30128; decide +kernel
      have hl : raw30128step0Labels = raw30128Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30128 raw30128Labels permutation159 permutation2
    _ = mixedMoment B node2348 node2348Labels := by rfl

theorem canonical30129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30129 raw30129Labels = mixedMoment B node2356 node2356Labels := by
  calc
    mixedMoment B raw30129 raw30129Labels = mixedMoment B raw30129step0 raw30129step0Labels := by
      have hz : ∀ j, raw30129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30129step0 = (fun i j => raw30129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30129step0 raw30129; decide +kernel
      have hl : raw30129step0Labels = raw30129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30129 raw30129Labels permutation346 hz
    mixedMoment B raw30129step0 raw30129step0Labels = mixedMoment B raw30129step1 raw30129step1Labels := by
      have ha : raw30129step1 = (fun i j => raw30129step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30129step1 raw30129step0; decide +kernel
      have hl : raw30129step1Labels = raw30129step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30129step0 raw30129step0Labels permutation33 permutation2
    _ = mixedMoment B node2356 node2356Labels := by rfl

theorem canonical30130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30130 raw30130Labels = mixedMoment B node2325 node2325Labels := by
  calc
    mixedMoment B raw30130 raw30130Labels = mixedMoment B raw30130step0 raw30130step0Labels := by
      have hz : ∀ j, raw30130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30130step0 = (fun i j => raw30130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30130step0 raw30130; decide +kernel
      have hl : raw30130step0Labels = raw30130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30130 raw30130Labels permutation346 hz
    mixedMoment B raw30130step0 raw30130step0Labels = mixedMoment B raw30130step1 raw30130step1Labels := by
      have ha : raw30130step1 = (fun i j => raw30130step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30130step1 raw30130step0; decide +kernel
      have hl : raw30130step1Labels = raw30130step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30130step0 raw30130step0Labels permutation127 permutation2
    mixedMoment B raw30130step1 raw30130step1Labels = mixedMoment B raw30130step2 raw30130step2Labels := by
      have ha : raw30130step2 = -raw30130step1 := by apply Matrix.ext; change ∀ i j, raw30130step2 i j = -(raw30130step1 i j); unfold raw30130step2 raw30130step1; decide +kernel
      have hl : raw30130step2Labels = raw30130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2325 node2325Labels := by rfl

theorem canonical30131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30131 raw30131Labels = mixedMoment B node2352 node2352Labels := by
  calc
    mixedMoment B raw30131 raw30131Labels = mixedMoment B raw30131step0 raw30131step0Labels := by
      have hz : ∀ j, raw30131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30131step0 = (fun i j => raw30131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30131step0 raw30131; decide +kernel
      have hl : raw30131step0Labels = raw30131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30131 raw30131Labels permutation346 hz
    _ = mixedMoment B node2352 node2352Labels := by rfl

theorem canonical30132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30132 raw30132Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw30132 raw30132Labels = mixedMoment B raw30132step0 raw30132step0Labels := by
      have ha : raw30132step0 = (fun i j => raw30132 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30132step0 raw30132; decide +kernel
      have hl : raw30132step0Labels = raw30132Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30132 raw30132Labels permutation201 permutation2
    _ = mixedMoment B node2428 node2428Labels := by rfl

theorem canonical30133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30133 raw30133Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw30133 raw30133Labels = mixedMoment B raw30133step0 raw30133step0Labels := by
      have ha : raw30133step0 = (fun i j => raw30133 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30133step0 raw30133; decide +kernel
      have hl : raw30133step0Labels = raw30133Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30133 raw30133Labels permutation159 permutation2
    _ = mixedMoment B node2553 node2553Labels := by rfl

theorem canonical30134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30134 raw30134Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw30134 raw30134Labels = mixedMoment B raw30134step0 raw30134step0Labels := by
      have ha : raw30134step0 = (fun i j => raw30134 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30134step0 raw30134; decide +kernel
      have hl : raw30134step0Labels = raw30134Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30134 raw30134Labels permutation587 permutation2
    mixedMoment B raw30134step0 raw30134step0Labels = mixedMoment B raw30134step1 raw30134step1Labels := by
      have ha : raw30134step1 = -raw30134step0 := by apply Matrix.ext; change ∀ i j, raw30134step1 i j = -(raw30134step0 i j); unfold raw30134step1 raw30134step0; decide +kernel
      have hl : raw30134step1Labels = raw30134step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3689 node3689Labels := by rfl

theorem canonical30135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30135 raw30135Labels = mixedMoment B node2525 node2525Labels := by
  calc
    mixedMoment B raw30135 raw30135Labels = mixedMoment B raw30135step0 raw30135step0Labels := by
      have ha : raw30135step0 = (fun i j => raw30135 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30135step0 raw30135; decide +kernel
      have hl : raw30135step0Labels = raw30135Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30135 raw30135Labels permutation153 permutation2
    _ = mixedMoment B node2525 node2525Labels := by rfl

theorem canonical30136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30136 raw30136Labels = mixedMoment B node2319 node2319Labels := by
  calc
    mixedMoment B raw30136 raw30136Labels = mixedMoment B raw30136step0 raw30136step0Labels := by
      have ha : raw30136step0 = (fun i j => raw30136 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30136step0 raw30136; decide +kernel
      have hl : raw30136step0Labels = raw30136Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30136 raw30136Labels permutation587 permutation2
    mixedMoment B raw30136step0 raw30136step0Labels = mixedMoment B raw30136step1 raw30136step1Labels := by
      have ha : raw30136step1 = -raw30136step0 := by apply Matrix.ext; change ∀ i j, raw30136step1 i j = -(raw30136step0 i j); unfold raw30136step1 raw30136step0; decide +kernel
      have hl : raw30136step1Labels = raw30136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2319 node2319Labels := by rfl

theorem canonical30137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30137 raw30137Labels = mixedMoment B node2524 node2524Labels := by
  calc
    _ = mixedMoment B node2524 node2524Labels := by rfl

theorem canonical30138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30138 raw30138Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw30138 raw30138Labels = mixedMoment B raw30138step0 raw30138step0Labels := by
      have hz : ∀ j, raw30138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30138step0 = (fun i j => raw30138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30138step0 raw30138; decide +kernel
      have hl : raw30138step0Labels = raw30138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30138 raw30138Labels permutation346 hz
    mixedMoment B raw30138step0 raw30138step0Labels = mixedMoment B raw30138step1 raw30138step1Labels := by
      have ha : raw30138step1 = (fun i j => raw30138step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30138step1 raw30138step0; decide +kernel
      have hl : raw30138step1Labels = raw30138step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30138step0 raw30138step0Labels permutation33 permutation2
    _ = mixedMoment B node2590 node2590Labels := by rfl

theorem canonical30199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30199 raw30199Labels = mixedMoment B node3646 node3646Labels := by
  calc
    mixedMoment B raw30199 raw30199Labels = mixedMoment B raw30199step0 raw30199step0Labels := by
      have ha : raw30199step0 = (fun i j => raw30199 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30199step0 raw30199; decide +kernel
      have hl : raw30199step0Labels = raw30199Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30199 raw30199Labels permutation584 permutation2
    mixedMoment B raw30199step0 raw30199step0Labels = mixedMoment B raw30199step1 raw30199step1Labels := by
      have ha : raw30199step1 = -raw30199step0 := by apply Matrix.ext; change ∀ i j, raw30199step1 i j = -(raw30199step0 i j); unfold raw30199step1 raw30199step0; decide +kernel
      have hl : raw30199step1Labels = raw30199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3646 node3646Labels := by rfl

theorem canonical30200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30200 raw30200Labels = mixedMoment B node3650 node3650Labels := by
  calc
    mixedMoment B raw30200 raw30200Labels = mixedMoment B raw30200step0 raw30200step0Labels := by
      have ha : raw30200step0 = (fun i j => raw30200 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30200step0 raw30200; decide +kernel
      have hl : raw30200step0Labels = raw30200Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30200 raw30200Labels permutation587 permutation2
    mixedMoment B raw30200step0 raw30200step0Labels = mixedMoment B raw30200step1 raw30200step1Labels := by
      have ha : raw30200step1 = -raw30200step0 := by apply Matrix.ext; change ∀ i j, raw30200step1 i j = -(raw30200step0 i j); unfold raw30200step1 raw30200step0; decide +kernel
      have hl : raw30200step1Labels = raw30200step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3650 node3650Labels := by rfl

theorem canonical30201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30201 raw30201Labels = mixedMoment B node3650 node3650Labels := by
  calc
    mixedMoment B raw30201 raw30201Labels = mixedMoment B raw30201step0 raw30201step0Labels := by
      have ha : raw30201step0 = (fun i j => raw30201 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30201step0 raw30201; decide +kernel
      have hl : raw30201step0Labels = raw30201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30201 raw30201Labels permutation582 permutation2
    mixedMoment B raw30201step0 raw30201step0Labels = mixedMoment B raw30201step1 raw30201step1Labels := by
      have ha : raw30201step1 = -raw30201step0 := by apply Matrix.ext; change ∀ i j, raw30201step1 i j = -(raw30201step0 i j); unfold raw30201step1 raw30201step0; decide +kernel
      have hl : raw30201step1Labels = raw30201step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3650 node3650Labels := by rfl

theorem canonical30202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30202 raw30202Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw30202 raw30202Labels = mixedMoment B raw30202step0 raw30202step0Labels := by
      have ha : raw30202step0 = (fun i j => raw30202 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30202step0 raw30202; decide +kernel
      have hl : raw30202step0Labels = raw30202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30202 raw30202Labels permutation584 permutation2
    mixedMoment B raw30202step0 raw30202step0Labels = mixedMoment B raw30202step1 raw30202step1Labels := by
      have ha : raw30202step1 = -raw30202step0 := by apply Matrix.ext; change ∀ i j, raw30202step1 i j = -(raw30202step0 i j); unfold raw30202step1 raw30202step0; decide +kernel
      have hl : raw30202step1Labels = raw30202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3757 node3757Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10402 raw10402Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw10402 raw10402Labels = mixedMoment B raw10402step0 raw10402step0Labels := by
      have hz : ∀ j, raw10402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10402step0 = (fun i j => raw10402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10402step0 raw10402; decide +kernel
      have hl : raw10402step0Labels = raw10402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10402 raw10402Labels permutation346 hz
    mixedMoment B raw10402step0 raw10402step0Labels = mixedMoment B raw10402step1 raw10402step1Labels := by
      have ha : raw10402step1 = (fun i j => raw10402step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10402step1 raw10402step0; decide +kernel
      have hl : raw10402step1Labels = raw10402step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10402step0 raw10402step0Labels permutation39 permutation7
    mixedMoment B raw10402step1 raw10402step1Labels = mixedMoment B raw10402step2 raw10402step2Labels := by
      have ha : raw10402step2 = -raw10402step1 := by apply Matrix.ext; change ∀ i j, raw10402step2 i j = -(raw10402step1 i j); unfold raw10402step2 raw10402step1; decide +kernel
      have hl : raw10402step2Labels = raw10402step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10402step2 raw10402step2Labels = mixedMoment B raw10402step3 raw10402step3Labels := by
      have ha : raw10402step3 = raw10402step2 := by apply Matrix.ext; unfold raw10402step3 raw10402step2; decide +kernel
      have hl : raw10402step2Labels = labelEmbedding1 ∘ raw10402step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10402step2 raw10402step2Labels raw10402step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical10413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10413 raw10413Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw10413 raw10413Labels = mixedMoment B raw10413step0 raw10413step0Labels := by
      have ha : raw10413step0 = (fun i j => raw10413 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10413step0 raw10413; decide +kernel
      have hl : raw10413step0Labels = raw10413Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10413 raw10413Labels permutation201 permutation7
    mixedMoment B raw10413step0 raw10413step0Labels = mixedMoment B raw10413step1 raw10413step1Labels := by
      have ha : raw10413step1 = -raw10413step0 := by apply Matrix.ext; change ∀ i j, raw10413step1 i j = -(raw10413step0 i j); unfold raw10413step1 raw10413step0; decide +kernel
      have hl : raw10413step1Labels = raw10413step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10413step1 raw10413step1Labels = mixedMoment B raw10413step2 raw10413step2Labels := by
      have ha : raw10413step2 = raw10413step1 := by apply Matrix.ext; unfold raw10413step2 raw10413step1; decide +kernel
      have hl : raw10413step1Labels = labelEmbedding1 ∘ raw10413step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10413step1 raw10413step1Labels raw10413step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3515 node3515Labels := by rfl

theorem canonical10418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10418 raw10418Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw10418 raw10418Labels = mixedMoment B raw10418step0 raw10418step0Labels := by
      have hz : ∀ j, raw10418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10418step0 = (fun i j => raw10418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10418step0 raw10418; decide +kernel
      have hl : raw10418step0Labels = raw10418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10418 raw10418Labels permutation346 hz
    mixedMoment B raw10418step0 raw10418step0Labels = mixedMoment B raw10418step1 raw10418step1Labels := by
      have ha : raw10418step1 = (fun i j => raw10418step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10418step1 raw10418step0; decide +kernel
      have hl : raw10418step1Labels = raw10418step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10418step0 raw10418step0Labels permutation39 permutation7
    mixedMoment B raw10418step1 raw10418step1Labels = mixedMoment B raw10418step2 raw10418step2Labels := by
      have ha : raw10418step2 = -raw10418step1 := by apply Matrix.ext; change ∀ i j, raw10418step2 i j = -(raw10418step1 i j); unfold raw10418step2 raw10418step1; decide +kernel
      have hl : raw10418step2Labels = raw10418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10418step2 raw10418step2Labels = mixedMoment B raw10418step3 raw10418step3Labels := by
      have ha : raw10418step3 = raw10418step2 := by apply Matrix.ext; unfold raw10418step3 raw10418step2; decide +kernel
      have hl : raw10418step2Labels = labelEmbedding1 ∘ raw10418step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10418step2 raw10418step2Labels raw10418step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

theorem canonical10422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10422 raw10422Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw10422 raw10422Labels = mixedMoment B raw10422step0 raw10422step0Labels := by
      have hz : ∀ j, raw10422 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10422step0 = (fun i j => raw10422 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10422step0 raw10422; decide +kernel
      have hl : raw10422step0Labels = raw10422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10422 raw10422Labels permutation346 hz
    mixedMoment B raw10422step0 raw10422step0Labels = mixedMoment B raw10422step1 raw10422step1Labels := by
      have hz : ∀ j, raw10422step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10422step1 = (fun i j => raw10422step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10422step1 raw10422step0; decide +kernel
      have hl : raw10422step1Labels = raw10422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10422step0 raw10422step0Labels permutation56 hz
    mixedMoment B raw10422step1 raw10422step1Labels = mixedMoment B raw10422step2 raw10422step2Labels := by
      have ha : raw10422step2 = (fun i j => raw10422step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10422step2 raw10422step1; decide +kernel
      have hl : raw10422step2Labels = raw10422step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10422step1 raw10422step1Labels permutation9 permutation7
    mixedMoment B raw10422step2 raw10422step2Labels = mixedMoment B raw10422step3 raw10422step3Labels := by
      have ha : raw10422step3 = -raw10422step2 := by apply Matrix.ext; change ∀ i j, raw10422step3 i j = -(raw10422step2 i j); unfold raw10422step3 raw10422step2; decide +kernel
      have hl : raw10422step3Labels = raw10422step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10422step3 raw10422step3Labels = mixedMoment B raw10422step4 raw10422step4Labels := by
      have ha : raw10422step4 = raw10422step3 := by apply Matrix.ext; unfold raw10422step4 raw10422step3; decide +kernel
      have hl : raw10422step3Labels = labelEmbedding1 ∘ raw10422step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10422step3 raw10422step3Labels raw10422step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical10424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10424 raw10424Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw10424 raw10424Labels = mixedMoment B raw10424step0 raw10424step0Labels := by
      have hz : ∀ j, raw10424 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10424step0 = (fun i j => raw10424 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10424step0 raw10424; decide +kernel
      have hl : raw10424step0Labels = raw10424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10424 raw10424Labels permutation265 hz
    mixedMoment B raw10424step0 raw10424step0Labels = mixedMoment B raw10424step1 raw10424step1Labels := by
      have ha : raw10424step1 = (fun i j => raw10424step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10424step1 raw10424step0; decide +kernel
      have hl : raw10424step1Labels = raw10424step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10424step0 raw10424step0Labels permutation39 permutation7
    mixedMoment B raw10424step1 raw10424step1Labels = mixedMoment B raw10424step2 raw10424step2Labels := by
      have ha : raw10424step2 = -raw10424step1 := by apply Matrix.ext; change ∀ i j, raw10424step2 i j = -(raw10424step1 i j); unfold raw10424step2 raw10424step1; decide +kernel
      have hl : raw10424step2Labels = raw10424step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10424step2 raw10424step2Labels = mixedMoment B raw10424step3 raw10424step3Labels := by
      have ha : raw10424step3 = raw10424step2 := by apply Matrix.ext; unfold raw10424step3 raw10424step2; decide +kernel
      have hl : raw10424step2Labels = labelEmbedding1 ∘ raw10424step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10424step2 raw10424step2Labels raw10424step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical10425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10425 raw10425Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw10425 raw10425Labels = mixedMoment B raw10425step0 raw10425step0Labels := by
      have hz : ∀ j, raw10425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10425step0 = (fun i j => raw10425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10425step0 raw10425; decide +kernel
      have hl : raw10425step0Labels = raw10425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10425 raw10425Labels permutation346 hz
    mixedMoment B raw10425step0 raw10425step0Labels = mixedMoment B raw10425step1 raw10425step1Labels := by
      have hz : ∀ j, raw10425step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10425step1 = (fun i j => raw10425step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10425step1 raw10425step0; decide +kernel
      have hl : raw10425step1Labels = raw10425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10425step0 raw10425step0Labels permutation56 hz
    mixedMoment B raw10425step1 raw10425step1Labels = mixedMoment B raw10425step2 raw10425step2Labels := by
      have ha : raw10425step2 = (fun i j => raw10425step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10425step2 raw10425step1; decide +kernel
      have hl : raw10425step2Labels = raw10425step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10425step1 raw10425step1Labels permutation9 permutation7
    mixedMoment B raw10425step2 raw10425step2Labels = mixedMoment B raw10425step3 raw10425step3Labels := by
      have ha : raw10425step3 = -raw10425step2 := by apply Matrix.ext; change ∀ i j, raw10425step3 i j = -(raw10425step2 i j); unfold raw10425step3 raw10425step2; decide +kernel
      have hl : raw10425step3Labels = raw10425step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10425step3 raw10425step3Labels = mixedMoment B raw10425step4 raw10425step4Labels := by
      have ha : raw10425step4 = raw10425step3 := by apply Matrix.ext; unfold raw10425step4 raw10425step3; decide +kernel
      have hl : raw10425step3Labels = labelEmbedding1 ∘ raw10425step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10425step3 raw10425step3Labels raw10425step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3485 node3485Labels := by rfl

theorem canonical10426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10426 raw10426Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw10426 raw10426Labels = mixedMoment B raw10426step0 raw10426step0Labels := by
      have hz : ∀ j, raw10426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10426step0 = (fun i j => raw10426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10426step0 raw10426; decide +kernel
      have hl : raw10426step0Labels = raw10426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10426 raw10426Labels permutation346 hz
    mixedMoment B raw10426step0 raw10426step0Labels = mixedMoment B raw10426step1 raw10426step1Labels := by
      have hz : ∀ j, raw10426step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10426step1 = (fun i j => raw10426step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10426step1 raw10426step0; decide +kernel
      have hl : raw10426step1Labels = raw10426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10426step0 raw10426step0Labels permutation56 hz
    mixedMoment B raw10426step1 raw10426step1Labels = mixedMoment B raw10426step2 raw10426step2Labels := by
      have ha : raw10426step2 = (fun i j => raw10426step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10426step2 raw10426step1; decide +kernel
      have hl : raw10426step2Labels = raw10426step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10426step1 raw10426step1Labels permutation9 permutation7
    mixedMoment B raw10426step2 raw10426step2Labels = mixedMoment B raw10426step3 raw10426step3Labels := by
      have ha : raw10426step3 = -raw10426step2 := by apply Matrix.ext; change ∀ i j, raw10426step3 i j = -(raw10426step2 i j); unfold raw10426step3 raw10426step2; decide +kernel
      have hl : raw10426step3Labels = raw10426step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10426step3 raw10426step3Labels = mixedMoment B raw10426step4 raw10426step4Labels := by
      have ha : raw10426step4 = raw10426step3 := by apply Matrix.ext; unfold raw10426step4 raw10426step3; decide +kernel
      have hl : raw10426step3Labels = labelEmbedding1 ∘ raw10426step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10426step3 raw10426step3Labels raw10426step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical10428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10428 raw10428Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw10428 raw10428Labels = mixedMoment B raw10428step0 raw10428step0Labels := by
      have hz : ∀ j, raw10428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10428step0 = (fun i j => raw10428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10428step0 raw10428; decide +kernel
      have hl : raw10428step0Labels = raw10428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10428 raw10428Labels permutation346 hz
    mixedMoment B raw10428step0 raw10428step0Labels = mixedMoment B raw10428step1 raw10428step1Labels := by
      have ha : raw10428step1 = (fun i j => raw10428step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10428step1 raw10428step0; decide +kernel
      have hl : raw10428step1Labels = raw10428step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10428step0 raw10428step0Labels permutation39 permutation7
    mixedMoment B raw10428step1 raw10428step1Labels = mixedMoment B raw10428step2 raw10428step2Labels := by
      have ha : raw10428step2 = -raw10428step1 := by apply Matrix.ext; change ∀ i j, raw10428step2 i j = -(raw10428step1 i j); unfold raw10428step2 raw10428step1; decide +kernel
      have hl : raw10428step2Labels = raw10428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10428step2 raw10428step2Labels = mixedMoment B raw10428step3 raw10428step3Labels := by
      have ha : raw10428step3 = raw10428step2 := by apply Matrix.ext; unfold raw10428step3 raw10428step2; decide +kernel
      have hl : raw10428step2Labels = labelEmbedding1 ∘ raw10428step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10428step2 raw10428step2Labels raw10428step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical10438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10438 raw10438Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw10438 raw10438Labels = mixedMoment B raw10438step0 raw10438step0Labels := by
      have hz : ∀ j, raw10438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10438step0 = (fun i j => raw10438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10438step0 raw10438; decide +kernel
      have hl : raw10438step0Labels = raw10438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10438 raw10438Labels permutation346 hz
    mixedMoment B raw10438step0 raw10438step0Labels = mixedMoment B raw10438step1 raw10438step1Labels := by
      have hz : ∀ j, raw10438step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10438step1 = (fun i j => raw10438step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10438step1 raw10438step0; decide +kernel
      have hl : raw10438step1Labels = raw10438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10438step0 raw10438step0Labels permutation56 hz
    mixedMoment B raw10438step1 raw10438step1Labels = mixedMoment B raw10438step2 raw10438step2Labels := by
      have ha : raw10438step2 = (fun i j => raw10438step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw10438step2 raw10438step1; decide +kernel
      have hl : raw10438step2Labels = raw10438step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10438step1 raw10438step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical10439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10439 raw10439Labels = mixedMoment B node2554 node2554Labels := by
  calc
    mixedMoment B raw10439 raw10439Labels = mixedMoment B raw10439step0 raw10439step0Labels := by
      have ha : raw10439step0 = (fun i j => raw10439 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10439step0 raw10439; decide +kernel
      have hl : raw10439step0Labels = raw10439Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10439 raw10439Labels permutation158 permutation2
    _ = mixedMoment B node2554 node2554Labels := by rfl

theorem canonical10440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10440 raw10440Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw10440 raw10440Labels = mixedMoment B raw10440step0 raw10440step0Labels := by
      have hz : ∀ j, raw10440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10440step0 = (fun i j => raw10440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10440step0 raw10440; decide +kernel
      have hl : raw10440step0Labels = raw10440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10440 raw10440Labels permutation346 hz
    _ = mixedMoment B node2591 node2591Labels := by rfl

theorem canonical10441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10441 raw10441Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw10441 raw10441Labels = mixedMoment B raw10441step0 raw10441step0Labels := by
      have hz : ∀ j, raw10441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10441step0 = (fun i j => raw10441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10441step0 raw10441; decide +kernel
      have hl : raw10441step0Labels = raw10441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10441 raw10441Labels permutation346 hz
    mixedMoment B raw10441step0 raw10441step0Labels = mixedMoment B raw10441step1 raw10441step1Labels := by
      have ha : raw10441step1 = (fun i j => raw10441step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10441step1 raw10441step0; decide +kernel
      have hl : raw10441step1Labels = raw10441step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10441step0 raw10441step0Labels permutation33 permutation2
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical10448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10448 raw10448Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw10448 raw10448Labels = mixedMoment B raw10448step0 raw10448step0Labels := by
      have hz : ∀ j, raw10448 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10448step0 = (fun i j => raw10448 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10448step0 raw10448; decide +kernel
      have hl : raw10448step0Labels = raw10448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10448 raw10448Labels permutation265 hz
    mixedMoment B raw10448step0 raw10448step0Labels = mixedMoment B raw10448step1 raw10448step1Labels := by
      have ha : raw10448step1 = (fun i j => raw10448step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10448step1 raw10448step0; decide +kernel
      have hl : raw10448step1Labels = raw10448step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10448step0 raw10448step0Labels permutation33 permutation2
    _ = mixedMoment B node2561 node2561Labels := by rfl

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

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

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

theorem sound1149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1149 node1149Labels = Sparse.eval nodeValue1149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1149) = mixedMoment B node1149 node1149Labels := rfl
  simpa [nodeValue1149, Sparse.eval] using hc.symm

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

theorem sound1160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1160 node1160Labels = Sparse.eval nodeValue1160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1160) = mixedMoment B node1160 node1160Labels := rfl
  simpa [nodeValue1160, Sparse.eval] using hc.symm

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

theorem sound1322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1322 node1322Labels = Sparse.eval nodeValue1322 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1322) = mixedMoment B node1322 node1322Labels := rfl
  simpa [nodeValue1322, Sparse.eval] using hc.symm

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

theorem sound1734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1734 node1734Labels = Sparse.eval nodeValue1734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1734) = mixedMoment B node1734 node1734Labels := rfl
  simpa [nodeValue1734, Sparse.eval] using hc.symm

theorem sound1735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1735 node1735Labels = Sparse.eval nodeValue1735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1735) = mixedMoment B node1735 node1735Labels := rfl
  simpa [nodeValue1735, Sparse.eval] using hc.symm

theorem sound1740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1740 node1740Labels = Sparse.eval nodeValue1740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1740) = mixedMoment B node1740 node1740Labels := rfl
  simpa [nodeValue1740, Sparse.eval] using hc.symm

theorem sound1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1748 node1748Labels = Sparse.eval nodeValue1748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1748) = mixedMoment B node1748 node1748Labels := rfl
  simpa [nodeValue1748, Sparse.eval] using hc.symm

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

theorem sound1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1819 node1819Labels = Sparse.eval nodeValue1819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1819) = mixedMoment B node1819 node1819Labels := rfl
  simpa [nodeValue1819, Sparse.eval] using hc.symm

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

theorem zero2319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2319 node2319Labels = 0 := by
  exact mixedMoment_alpha B hF node2319 node2319Labels 1 permutation152
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

theorem sound2319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2319 node2319Labels = Sparse.eval nodeValue2319 (mixedVector B) := by
  simpa only [nodeValue2319, Sparse.eval_nil] using zero2319 B _hB _hF

theorem sound2325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2325 node2325Labels = Sparse.eval nodeValue2325 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2325) = mixedMoment B node2325 node2325Labels := rfl
  simpa [nodeValue2325, Sparse.eval] using hc.symm

theorem sound2345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2345 node2345Labels = Sparse.eval nodeValue2345 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2345) = mixedMoment B node2345 node2345Labels := rfl
  simpa [nodeValue2345, Sparse.eval] using hc.symm

theorem sound2348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2348 node2348Labels = Sparse.eval nodeValue2348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2348) = mixedMoment B node2348 node2348Labels := rfl
  simpa [nodeValue2348, Sparse.eval] using hc.symm

theorem sound2352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2352 node2352Labels = Sparse.eval nodeValue2352 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2352) = mixedMoment B node2352 node2352Labels := rfl
  simpa [nodeValue2352, Sparse.eval] using hc.symm

theorem sound2356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2356 node2356Labels = Sparse.eval nodeValue2356 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2356) = mixedMoment B node2356 node2356Labels := rfl
  simpa [nodeValue2356, Sparse.eval] using hc.symm

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

theorem sound2428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2428 node2428Labels = Sparse.eval nodeValue2428 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2428) = mixedMoment B node2428 node2428Labels := rfl
  simpa [nodeValue2428, Sparse.eval] using hc.symm

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

theorem zero2554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2554 node2554Labels = 0 := by
  exact mixedMoment_alpha B hF node2554 node2554Labels 1 permutation160
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

theorem sound2524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2524 node2524Labels = Sparse.eval nodeValue2524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2524) = mixedMoment B node2524 node2524Labels := rfl
  simpa [nodeValue2524, Sparse.eval] using hc.symm

theorem sound2525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2525 node2525Labels = Sparse.eval nodeValue2525 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2525) = mixedMoment B node2525 node2525Labels := rfl
  simpa [nodeValue2525, Sparse.eval] using hc.symm

theorem sound2533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2533 node2533Labels = Sparse.eval nodeValue2533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2533) = mixedMoment B node2533 node2533Labels := rfl
  simpa [nodeValue2533, Sparse.eval] using hc.symm

theorem sound2541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2541 node2541Labels = Sparse.eval nodeValue2541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2541) = mixedMoment B node2541 node2541Labels := rfl
  simpa [nodeValue2541, Sparse.eval] using hc.symm

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

theorem sound2554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2554 node2554Labels = Sparse.eval nodeValue2554 (mixedVector B) := by
  simpa only [nodeValue2554, Sparse.eval_nil] using zero2554 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2561 node2561Labels = Sparse.eval nodeValue2561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2561) = mixedMoment B node2561 node2561Labels := rfl
  simpa [nodeValue2561, Sparse.eval] using hc.symm

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

theorem sound2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2591 node2591Labels = Sparse.eval nodeValue2591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2591) = mixedMoment B node2591 node2591Labels := rfl
  simpa [nodeValue2591, Sparse.eval] using hc.symm

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

theorem sound2802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2802 node2802Labels = Sparse.eval nodeValue2802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2802) = mixedMoment B node2802 node2802Labels := rfl
  simpa [nodeValue2802, Sparse.eval] using hc.symm

theorem sound2812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2812 node2812Labels = Sparse.eval nodeValue2812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2812) = mixedMoment B node2812 node2812Labels := rfl
  simpa [nodeValue2812, Sparse.eval] using hc.symm

theorem sound2813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2813 node2813Labels = Sparse.eval nodeValue2813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2813) = mixedMoment B node2813 node2813Labels := rfl
  simpa [nodeValue2813, Sparse.eval] using hc.symm

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

theorem sound2818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2818 node2818Labels = Sparse.eval nodeValue2818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2818) = mixedMoment B node2818 node2818Labels := rfl
  simpa [nodeValue2818, Sparse.eval] using hc.symm

theorem sound2820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2820 node2820Labels = Sparse.eval nodeValue2820 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2820) = mixedMoment B node2820 node2820Labels := rfl
  simpa [nodeValue2820, Sparse.eval] using hc.symm

theorem sound2821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2821 node2821Labels = Sparse.eval nodeValue2821 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2821) = mixedMoment B node2821 node2821Labels := rfl
  simpa [nodeValue2821, Sparse.eval] using hc.symm

theorem sound2849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2849 node2849Labels = Sparse.eval nodeValue2849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2849) = mixedMoment B node2849 node2849Labels := rfl
  simpa [nodeValue2849, Sparse.eval] using hc.symm

theorem sound2868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2868 node2868Labels = Sparse.eval nodeValue2868 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2868) = mixedMoment B node2868 node2868Labels := rfl
  simpa [nodeValue2868, Sparse.eval] using hc.symm

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

theorem sound2884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2884 node2884Labels = Sparse.eval nodeValue2884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2884) = mixedMoment B node2884 node2884Labels := rfl
  simpa [nodeValue2884, Sparse.eval] using hc.symm

theorem sound2888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2888 node2888Labels = Sparse.eval nodeValue2888 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2888) = mixedMoment B node2888 node2888Labels := rfl
  simpa [nodeValue2888, Sparse.eval] using hc.symm

theorem sound2889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2889 node2889Labels = Sparse.eval nodeValue2889 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2889) = mixedMoment B node2889 node2889Labels := rfl
  simpa [nodeValue2889, Sparse.eval] using hc.symm

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

theorem sound3267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3267 node3267Labels = Sparse.eval nodeValue3267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3267) = mixedMoment B node3267 node3267Labels := rfl
  simpa [nodeValue3267, Sparse.eval] using hc.symm

theorem sound3268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3268 node3268Labels = Sparse.eval nodeValue3268 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3268) = mixedMoment B node3268 node3268Labels := rfl
  simpa [nodeValue3268, Sparse.eval] using hc.symm

theorem sound3271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3271 node3271Labels = Sparse.eval nodeValue3271 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3271) = mixedMoment B node3271 node3271Labels := rfl
  simpa [nodeValue3271, Sparse.eval] using hc.symm

theorem sound3272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3272 node3272Labels = Sparse.eval nodeValue3272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3272) = mixedMoment B node3272 node3272Labels := rfl
  simpa [nodeValue3272, Sparse.eval] using hc.symm

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

theorem sound3397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3397 node3397Labels = Sparse.eval nodeValue3397 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3397) = mixedMoment B node3397 node3397Labels := rfl
  simpa [nodeValue3397, Sparse.eval] using hc.symm

theorem sound3403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3403 node3403Labels = Sparse.eval nodeValue3403 (mixedVector B) := by
  simpa only [nodeValue3403, Sparse.eval_nil] using zero3403 B _hB _hF

theorem sound3411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3411 node3411Labels = Sparse.eval nodeValue3411 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3411) = mixedMoment B node3411 node3411Labels := rfl
  simpa [nodeValue3411, Sparse.eval] using hc.symm

theorem sound3413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3413 node3413Labels = Sparse.eval nodeValue3413 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3413) = mixedMoment B node3413 node3413Labels := rfl
  simpa [nodeValue3413, Sparse.eval] using hc.symm

theorem sound3415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3415 node3415Labels = Sparse.eval nodeValue3415 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3415) = mixedMoment B node3415 node3415Labels := rfl
  simpa [nodeValue3415, Sparse.eval] using hc.symm

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

theorem zero3485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3485 node3485Labels = 0 := by
  exact mixedMoment_order_one B hB node3485 node3485Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3515 node3515Labels = 0 := by
  exact mixedMoment_alpha B hF node3515 node3515Labels 1 permutation443
    (by decide +kernel)

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

theorem sound3457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3457 node3457Labels = Sparse.eval nodeValue3457 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3457) = mixedMoment B node3457 node3457Labels := rfl
  simpa [nodeValue3457, Sparse.eval] using hc.symm

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3474 node3474Labels = Sparse.eval nodeValue3474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3474) = mixedMoment B node3474 node3474Labels := rfl
  simpa [nodeValue3474, Sparse.eval] using hc.symm

theorem sound3475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3475 node3475Labels = Sparse.eval nodeValue3475 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3475) = mixedMoment B node3475 node3475Labels := rfl
  simpa [nodeValue3475, Sparse.eval] using hc.symm

theorem sound3480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3480 node3480Labels = Sparse.eval nodeValue3480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3480) = mixedMoment B node3480 node3480Labels := rfl
  simpa [nodeValue3480, Sparse.eval] using hc.symm

theorem sound3485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3485 node3485Labels = Sparse.eval nodeValue3485 (mixedVector B) := by
  simpa only [nodeValue3485, Sparse.eval_nil] using zero3485 B _hB _hF

theorem sound3486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3486 node3486Labels = Sparse.eval nodeValue3486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3486) = mixedMoment B node3486 node3486Labels := rfl
  simpa [nodeValue3486, Sparse.eval] using hc.symm

theorem sound3508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3508 node3508Labels = Sparse.eval nodeValue3508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3508) = mixedMoment B node3508 node3508Labels := rfl
  simpa [nodeValue3508, Sparse.eval] using hc.symm

theorem sound3510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3510 node3510Labels = Sparse.eval nodeValue3510 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3510) = mixedMoment B node3510 node3510Labels := rfl
  simpa [nodeValue3510, Sparse.eval] using hc.symm

theorem sound3512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3512 node3512Labels = Sparse.eval nodeValue3512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3512) = mixedMoment B node3512 node3512Labels := rfl
  simpa [nodeValue3512, Sparse.eval] using hc.symm

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

theorem sound3515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3515 node3515Labels = Sparse.eval nodeValue3515 (mixedVector B) := by
  simpa only [nodeValue3515, Sparse.eval_nil] using zero3515 B _hB _hF

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

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

theorem sound3523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3523 node3523Labels = Sparse.eval nodeValue3523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3523) = mixedMoment B node3523 node3523Labels := rfl
  simpa [nodeValue3523, Sparse.eval] using hc.symm

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3555 node3555Labels = Sparse.eval nodeValue3555 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3555) = mixedMoment B node3555 node3555Labels := rfl
  simpa [nodeValue3555, Sparse.eval] using hc.symm

theorem sound3556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3556 node3556Labels = Sparse.eval nodeValue3556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3556) = mixedMoment B node3556 node3556Labels := rfl
  simpa [nodeValue3556, Sparse.eval] using hc.symm

theorem sound3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3564 node3564Labels = Sparse.eval nodeValue3564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3564) = mixedMoment B node3564 node3564Labels := rfl
  simpa [nodeValue3564, Sparse.eval] using hc.symm

theorem sound3565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3565 node3565Labels = Sparse.eval nodeValue3565 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3565) = mixedMoment B node3565 node3565Labels := rfl
  simpa [nodeValue3565, Sparse.eval] using hc.symm

theorem sound3578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3578 node3578Labels = Sparse.eval nodeValue3578 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3578) = mixedMoment B node3578 node3578Labels := rfl
  simpa [nodeValue3578, Sparse.eval] using hc.symm

theorem sound3579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3579 node3579Labels = Sparse.eval nodeValue3579 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3579) = mixedMoment B node3579 node3579Labels := rfl
  simpa [nodeValue3579, Sparse.eval] using hc.symm

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

theorem sound3584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3584 node3584Labels = Sparse.eval nodeValue3584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3584) = mixedMoment B node3584 node3584Labels := rfl
  simpa [nodeValue3584, Sparse.eval] using hc.symm

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

theorem sound3624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3624 node3624Labels = Sparse.eval nodeValue3624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3624) = mixedMoment B node3624 node3624Labels := rfl
  simpa [nodeValue3624, Sparse.eval] using hc.symm

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

theorem zero3650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3650 node3650Labels = 0 := by
  exact mixedMoment_order_one B hB node3650 node3650Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3707 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3707 node3707Labels = 0 := by
  exact mixedMoment_order_one B hB node3707 node3707Labels 1
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

theorem sound3650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3650 node3650Labels = Sparse.eval nodeValue3650 (mixedVector B) := by
  simpa only [nodeValue3650, Sparse.eval_nil] using zero3650 B _hB _hF

theorem sound3679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3679 node3679Labels = Sparse.eval nodeValue3679 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3679) = mixedMoment B node3679 node3679Labels := rfl
  simpa [nodeValue3679, Sparse.eval] using hc.symm

theorem sound3681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3681 node3681Labels = Sparse.eval nodeValue3681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3681) = mixedMoment B node3681 node3681Labels := rfl
  simpa [nodeValue3681, Sparse.eval] using hc.symm

theorem sound3689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3689 node3689Labels = Sparse.eval nodeValue3689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3689) = mixedMoment B node3689 node3689Labels := rfl
  simpa [nodeValue3689, Sparse.eval] using hc.symm

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

theorem sound3695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3695 node3695Labels = Sparse.eval nodeValue3695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3695) = mixedMoment B node3695 node3695Labels := rfl
  simpa [nodeValue3695, Sparse.eval] using hc.symm

theorem sound3707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3707 node3707Labels = Sparse.eval nodeValue3707 (mixedVector B) := by
  simpa only [nodeValue3707, Sparse.eval_nil] using zero3707 B _hB _hF

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

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

theorem sound3766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3766 node3766Labels = Sparse.eval nodeValue3766 (mixedVector B) := by
  simpa only [nodeValue3766, Sparse.eval_nil] using zero3766 B _hB _hF

theorem sound3767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3767 node3767Labels = Sparse.eval nodeValue3767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3767) = mixedMoment B node3767 node3767Labels := rfl
  simpa [nodeValue3767, Sparse.eval] using hc.symm

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

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

theorem zero3807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = 0 := by
  exact mixedMoment_order_one B hB node3807 node3807Labels 1
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

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

theorem sound3817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3817 node3817Labels = Sparse.eval nodeValue3817 (mixedVector B) := by
  simpa only [nodeValue3817, Sparse.eval_nil] using zero3817 B _hB _hF

theorem sound3832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3832 node3832Labels = Sparse.eval nodeValue3832 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3832) = mixedMoment B node3832 node3832Labels := rfl
  simpa [nodeValue3832, Sparse.eval] using hc.symm

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

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

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

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources67
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2175 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2175 + difference 0 1) (sourceB2175 + difference 1 0) sourceC2175) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2175 + difference 0 1) (sourceB2175 + difference 1 0) sourceC2175) = raw29927 := by
      apply Matrix.ext; unfold tripleCharges sourceA2175 sourceB2175 sourceC2175 difference raw29927; decide +kernel
    rw [ha]
    exact (canonical29927 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2175 + difference 1 1) (sourceB2175 + difference 1 1) sourceC2175) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2868) := by
    have ha : (tripleCharges (sourceA2175 + difference 1 1) (sourceB2175 + difference 1 1) sourceC2175) = raw29928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2175 sourceB2175 sourceC2175 difference raw29928; decide +kernel
    rw [ha]
    exact (canonical29928 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2175 + difference 2 1) (sourceB2175 + difference 1 2) sourceC2175) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2818) := by
    have ha : (tripleCharges (sourceA2175 + difference 2 1) (sourceB2175 + difference 1 2) sourceC2175) = raw29929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2175 sourceB2175 sourceC2175 difference raw29929; decide +kernel
    rw [ha]
    exact (canonical29929 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2175 + difference 3 1) (sourceB2175 + difference 1 3) sourceC2175) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2799) := by
    have ha : (tripleCharges (sourceA2175 + difference 3 1) (sourceB2175 + difference 1 3) sourceC2175) = raw29930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2175 sourceB2175 sourceC2175 difference raw29930; decide +kernel
    rw [ha]
    exact (canonical29930 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2175 + difference 4 1) (sourceB2175 + difference 1 4) sourceC2175) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2802) := by
    have ha : (tripleCharges (sourceA2175 + difference 4 1) (sourceB2175 + difference 1 4) sourceC2175) = raw29931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2175 sourceB2175 sourceC2175 difference raw29931; decide +kernel
    rw [ha]
    exact (canonical29931 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2175 + difference 5 1) (sourceB2175 + difference 1 5) sourceC2175) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2802) := by
    have ha : (tripleCharges (sourceA2175 + difference 5 1) (sourceB2175 + difference 1 5) sourceC2175) = raw29932 := by
      apply Matrix.ext; unfold tripleCharges sourceA2175 sourceB2175 sourceC2175 difference raw29932; decide +kernel
    rw [ha]
    exact (canonical29932 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2175 + sourceB2175) sourceC2175) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2175 + sourceB2175) sourceC2175) = raw29933 := by
      apply Matrix.ext; unfold doubleCharges sourceA2175 sourceB2175 sourceC2175 raw29933; decide +kernel
    rw [ha]
    exact (canonical29933 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2175 sourceB2175 sourceC2175
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2175, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

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

theorem sourceEq2176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2176 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2176 + difference 2 0) (sourceB2176 + difference 0 2) sourceC2176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1322) := by
    have ha : (tripleCharges (sourceA2176 + difference 2 0) (sourceB2176 + difference 0 2) sourceC2176) = raw29934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2176 sourceB2176 sourceC2176 difference raw29934; decide +kernel
    rw [ha]
    exact (canonical29934 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2176 + difference 2 1) (sourceB2176 + difference 1 2) sourceC2176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2818) := by
    have ha : (tripleCharges (sourceA2176 + difference 2 1) (sourceB2176 + difference 1 2) sourceC2176) = raw29929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2176 sourceB2176 sourceC2176 difference raw29929; decide +kernel
    rw [ha]
    exact (canonical29929 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2176 + difference 2 2) (sourceB2176 + difference 2 2) sourceC2176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2868) := by
    have ha : (tripleCharges (sourceA2176 + difference 2 2) (sourceB2176 + difference 2 2) sourceC2176) = raw29928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2176 sourceB2176 sourceC2176 difference raw29928; decide +kernel
    rw [ha]
    exact (canonical29928 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2176 + difference 2 3) (sourceB2176 + difference 3 2) sourceC2176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2849) := by
    have ha : (tripleCharges (sourceA2176 + difference 2 3) (sourceB2176 + difference 3 2) sourceC2176) = raw29935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2176 sourceB2176 sourceC2176 difference raw29935; decide +kernel
    rw [ha]
    exact (canonical29935 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2176 + difference 2 4) (sourceB2176 + difference 4 2) sourceC2176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA2176 + difference 2 4) (sourceB2176 + difference 4 2) sourceC2176) = raw29936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2176 sourceB2176 sourceC2176 difference raw29936; decide +kernel
    rw [ha]
    exact (canonical29936 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2176 + difference 2 5) (sourceB2176 + difference 5 2) sourceC2176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA2176 + difference 2 5) (sourceB2176 + difference 5 2) sourceC2176) = raw29937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2176 sourceB2176 sourceC2176 difference raw29937; decide +kernel
    rw [ha]
    exact (canonical29937 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2176 + sourceB2176) sourceC2176) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2176 + sourceB2176) sourceC2176) = raw29933 := by
      apply Matrix.ext; unfold doubleCharges sourceA2176 sourceB2176 sourceC2176 raw29933; decide +kernel
    rw [ha]
    exact (canonical29933 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2176 sourceB2176 sourceC2176
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2176, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2177 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2177 + difference 0 1) (sourceB2177 + difference 1 0) sourceC2177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA2177 + difference 0 1) (sourceB2177 + difference 1 0) sourceC2177) = raw29938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2177 sourceB2177 sourceC2177 difference raw29938; decide +kernel
    rw [ha]
    exact (canonical29938 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2177 + difference 1 1) (sourceB2177 + difference 1 1) sourceC2177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA2177 + difference 1 1) (sourceB2177 + difference 1 1) sourceC2177) = raw29939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2177 sourceB2177 sourceC2177 difference raw29939; decide +kernel
    rw [ha]
    exact (canonical29939 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2177 + difference 2 1) (sourceB2177 + difference 1 2) sourceC2177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2812) := by
    have ha : (tripleCharges (sourceA2177 + difference 2 1) (sourceB2177 + difference 1 2) sourceC2177) = raw29940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2177 sourceB2177 sourceC2177 difference raw29940; decide +kernel
    rw [ha]
    exact (canonical29940 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2177 + difference 3 1) (sourceB2177 + difference 1 3) sourceC2177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2812) := by
    have ha : (tripleCharges (sourceA2177 + difference 3 1) (sourceB2177 + difference 1 3) sourceC2177) = raw29941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2177 sourceB2177 sourceC2177 difference raw29941; decide +kernel
    rw [ha]
    exact (canonical29941 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2177 + difference 4 1) (sourceB2177 + difference 1 4) sourceC2177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1819) := by
    have ha : (tripleCharges (sourceA2177 + difference 4 1) (sourceB2177 + difference 1 4) sourceC2177) = raw29942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2177 sourceB2177 sourceC2177 difference raw29942; decide +kernel
    rw [ha]
    exact (canonical29942 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2177 + difference 5 1) (sourceB2177 + difference 1 5) sourceC2177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2821) := by
    have ha : (tripleCharges (sourceA2177 + difference 5 1) (sourceB2177 + difference 1 5) sourceC2177) = raw29943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2177 sourceB2177 sourceC2177 difference raw29943; decide +kernel
    rw [ha]
    exact (canonical29943 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2177 + sourceB2177) sourceC2177) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2177 + sourceB2177) sourceC2177) = raw29944 := by
      apply Matrix.ext; unfold doubleCharges sourceA2177 sourceB2177 sourceC2177 raw29944; decide +kernel
    rw [ha]
    exact (canonical29944 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2177 sourceB2177 sourceC2177
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2177, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2181 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2181 + difference 0 1) (sourceB2181 + difference 1 0) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3775) := by
    have ha : (tripleCharges (sourceA2181 + difference 0 1) (sourceB2181 + difference 1 0) sourceC2181) = raw18029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18029; decide +kernel
    rw [ha]
    exact (canonical18029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2181 + difference 0 2) (sourceB2181 + difference 2 0) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2181 + difference 0 2) (sourceB2181 + difference 2 0) sourceC2181) = raw18030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18030; decide +kernel
    rw [ha]
    exact (canonical18030 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2181 + difference 0 3) (sourceB2181 + difference 3 0) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2181 + difference 0 3) (sourceB2181 + difference 3 0) sourceC2181) = raw18031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18031; decide +kernel
    rw [ha]
    exact (canonical18031 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2181 + difference 0 4) (sourceB2181 + difference 4 0) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA2181 + difference 0 4) (sourceB2181 + difference 4 0) sourceC2181) = raw30001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30001; decide +kernel
    rw [ha]
    exact (canonical30001 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2181 + difference 0 5) (sourceB2181 + difference 5 0) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA2181 + difference 0 5) (sourceB2181 + difference 5 0) sourceC2181) = raw18032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18032; decide +kernel
    rw [ha]
    exact (canonical18032 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2181 + difference 1 0) (sourceB2181 + difference 0 1) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA2181 + difference 1 0) (sourceB2181 + difference 0 1) sourceC2181) = raw30002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30002; decide +kernel
    rw [ha]
    exact (canonical30002 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2181 + difference 1 2) (sourceB2181 + difference 2 1) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2181 + difference 1 2) (sourceB2181 + difference 2 1) sourceC2181) = raw30003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30003; decide +kernel
    rw [ha]
    exact (canonical30003 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2181 + difference 1 3) (sourceB2181 + difference 3 1) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2181 + difference 1 3) (sourceB2181 + difference 3 1) sourceC2181) = raw30004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30004; decide +kernel
    rw [ha]
    exact (canonical30004 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2181 + difference 1 4) (sourceB2181 + difference 4 1) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA2181 + difference 1 4) (sourceB2181 + difference 4 1) sourceC2181) = raw18013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18013; decide +kernel
    rw [ha]
    exact (canonical18013 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2181 + difference 1 5) (sourceB2181 + difference 5 1) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA2181 + difference 1 5) (sourceB2181 + difference 5 1) sourceC2181) = raw30005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30005; decide +kernel
    rw [ha]
    exact (canonical30005 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2181 + difference 2 0) (sourceB2181 + difference 0 2) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA2181 + difference 2 0) (sourceB2181 + difference 0 2) sourceC2181) = raw30006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30006; decide +kernel
    rw [ha]
    exact (canonical30006 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2181 + difference 2 1) (sourceB2181 + difference 1 2) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2181 + difference 2 1) (sourceB2181 + difference 1 2) sourceC2181) = raw30007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30007; decide +kernel
    rw [ha]
    exact (canonical30007 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2181 + difference 2 3) (sourceB2181 + difference 3 2) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2181 + difference 2 3) (sourceB2181 + difference 3 2) sourceC2181) = raw30008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30008; decide +kernel
    rw [ha]
    exact (canonical30008 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2181 + difference 2 4) (sourceB2181 + difference 4 2) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA2181 + difference 2 4) (sourceB2181 + difference 4 2) sourceC2181) = raw18018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18018; decide +kernel
    rw [ha]
    exact (canonical18018 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2181 + difference 2 5) (sourceB2181 + difference 5 2) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA2181 + difference 2 5) (sourceB2181 + difference 5 2) sourceC2181) = raw30009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30009; decide +kernel
    rw [ha]
    exact (canonical30009 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2181 + difference 3 0) (sourceB2181 + difference 0 3) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA2181 + difference 3 0) (sourceB2181 + difference 0 3) sourceC2181) = raw30010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30010; decide +kernel
    rw [ha]
    exact (canonical30010 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2181 + difference 3 1) (sourceB2181 + difference 1 3) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2181 + difference 3 1) (sourceB2181 + difference 1 3) sourceC2181) = raw30011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30011; decide +kernel
    rw [ha]
    exact (canonical30011 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2181 + difference 3 2) (sourceB2181 + difference 2 3) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2181 + difference 3 2) (sourceB2181 + difference 2 3) sourceC2181) = raw30012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30012; decide +kernel
    rw [ha]
    exact (canonical30012 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2181 + difference 3 4) (sourceB2181 + difference 4 3) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA2181 + difference 3 4) (sourceB2181 + difference 4 3) sourceC2181) = raw18023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18023; decide +kernel
    rw [ha]
    exact (canonical18023 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2181 + difference 3 5) (sourceB2181 + difference 5 3) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA2181 + difference 3 5) (sourceB2181 + difference 5 3) sourceC2181) = raw30013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30013; decide +kernel
    rw [ha]
    exact (canonical30013 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2181 + difference 4 0) (sourceB2181 + difference 0 4) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA2181 + difference 4 0) (sourceB2181 + difference 0 4) sourceC2181) = raw30014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30014; decide +kernel
    rw [ha]
    exact (canonical30014 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2181 + difference 4 1) (sourceB2181 + difference 1 4) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2181 + difference 4 1) (sourceB2181 + difference 1 4) sourceC2181) = raw30015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30015; decide +kernel
    rw [ha]
    exact (canonical30015 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2181 + difference 4 2) (sourceB2181 + difference 2 4) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2181 + difference 4 2) (sourceB2181 + difference 2 4) sourceC2181) = raw30016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30016; decide +kernel
    rw [ha]
    exact (canonical30016 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2181 + difference 4 3) (sourceB2181 + difference 3 4) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2181 + difference 4 3) (sourceB2181 + difference 3 4) sourceC2181) = raw30017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30017; decide +kernel
    rw [ha]
    exact (canonical30017 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2181 + difference 4 5) (sourceB2181 + difference 5 4) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA2181 + difference 4 5) (sourceB2181 + difference 5 4) sourceC2181) = raw30018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30018; decide +kernel
    rw [ha]
    exact (canonical30018 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2181 + difference 5 0) (sourceB2181 + difference 0 5) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1735) := by
    have ha : (tripleCharges (sourceA2181 + difference 5 0) (sourceB2181 + difference 0 5) sourceC2181) = raw30019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30019; decide +kernel
    rw [ha]
    exact (canonical30019 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2181 + difference 5 1) (sourceB2181 + difference 1 5) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3596) := by
    have ha : (tripleCharges (sourceA2181 + difference 5 1) (sourceB2181 + difference 1 5) sourceC2181) = raw30020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30020; decide +kernel
    rw [ha]
    exact (canonical30020 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2181 + difference 5 2) (sourceB2181 + difference 2 5) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2181 + difference 5 2) (sourceB2181 + difference 2 5) sourceC2181) = raw30021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30021; decide +kernel
    rw [ha]
    exact (canonical30021 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2181 + difference 5 3) (sourceB2181 + difference 3 5) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2181 + difference 5 3) (sourceB2181 + difference 3 5) sourceC2181) = raw30022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30022; decide +kernel
    rw [ha]
    exact (canonical30022 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2181 + difference 5 4) (sourceB2181 + difference 4 5) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3579) := by
    have ha : (tripleCharges (sourceA2181 + difference 5 4) (sourceB2181 + difference 4 5) sourceC2181) = raw18033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18033; decide +kernel
    rw [ha]
    exact (canonical18033 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2181 sourceB2181 sourceC2181
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2181, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2182 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2182 + difference 0 1) (sourceB2182 + difference 1 0) sourceC2182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3707) := by
    have ha : (tripleCharges (sourceA2182 + difference 0 1) (sourceB2182 + difference 1 0) sourceC2182) = raw30023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2182 sourceB2182 sourceC2182 difference raw30023; decide +kernel
    rw [ha]
    exact (canonical30023 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2182 + difference 1 1) (sourceB2182 + difference 1 1) sourceC2182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA2182 + difference 1 1) (sourceB2182 + difference 1 1) sourceC2182) = raw30024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2182 sourceB2182 sourceC2182 difference raw30024; decide +kernel
    rw [ha]
    exact (canonical30024 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2182 + difference 2 1) (sourceB2182 + difference 1 2) sourceC2182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2813) := by
    have ha : (tripleCharges (sourceA2182 + difference 2 1) (sourceB2182 + difference 1 2) sourceC2182) = raw30025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2182 sourceB2182 sourceC2182 difference raw30025; decide +kernel
    rw [ha]
    exact (canonical30025 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2182 + difference 3 1) (sourceB2182 + difference 1 3) sourceC2182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2813) := by
    have ha : (tripleCharges (sourceA2182 + difference 3 1) (sourceB2182 + difference 1 3) sourceC2182) = raw30026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2182 sourceB2182 sourceC2182 difference raw30026; decide +kernel
    rw [ha]
    exact (canonical30026 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2182 + difference 4 1) (sourceB2182 + difference 1 4) sourceC2182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2345) := by
    have ha : (tripleCharges (sourceA2182 + difference 4 1) (sourceB2182 + difference 1 4) sourceC2182) = raw30027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2182 sourceB2182 sourceC2182 difference raw30027; decide +kernel
    rw [ha]
    exact (canonical30027 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2182 + difference 5 1) (sourceB2182 + difference 1 5) sourceC2182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2820) := by
    have ha : (tripleCharges (sourceA2182 + difference 5 1) (sourceB2182 + difference 1 5) sourceC2182) = raw28230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2182 sourceB2182 sourceC2182 difference raw28230; decide +kernel
    rw [ha]
    exact (canonical28230 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2182 + sourceB2182) sourceC2182) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2182 + sourceB2182) sourceC2182) = raw28232 := by
      apply Matrix.ext; unfold doubleCharges sourceA2182 sourceB2182 sourceC2182 raw28232; decide +kernel
    rw [ha]
    exact (canonical28232 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2182 sourceB2182 sourceC2182
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2182, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2189 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2189 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2189 + difference 0 0) (sourceB2189 + difference 0 0) sourceC2189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2533) := by
    have ha : (tripleCharges (sourceA2189 + difference 0 0) (sourceB2189 + difference 0 0) sourceC2189) = raw30069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2189 sourceB2189 sourceC2189 difference raw30069; decide +kernel
    rw [ha]
    exact (canonical30069 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2189 + difference 0 1) (sourceB2189 + difference 1 0) sourceC2189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3679) := by
    have ha : (tripleCharges (sourceA2189 + difference 0 1) (sourceB2189 + difference 1 0) sourceC2189) = raw30070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2189 sourceB2189 sourceC2189 difference raw30070; decide +kernel
    rw [ha]
    exact (canonical30070 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2189 + difference 0 2) (sourceB2189 + difference 2 0) sourceC2189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3695) := by
    have ha : (tripleCharges (sourceA2189 + difference 0 2) (sourceB2189 + difference 2 0) sourceC2189) = raw30071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2189 sourceB2189 sourceC2189 difference raw30071; decide +kernel
    rw [ha]
    exact (canonical30071 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2189 + difference 0 3) (sourceB2189 + difference 3 0) sourceC2189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3681) := by
    have ha : (tripleCharges (sourceA2189 + difference 0 3) (sourceB2189 + difference 3 0) sourceC2189) = raw30072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2189 sourceB2189 sourceC2189 difference raw30072; decide +kernel
    rw [ha]
    exact (canonical30072 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2189 + difference 0 4) (sourceB2189 + difference 4 0) sourceC2189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2189 + difference 0 4) (sourceB2189 + difference 4 0) sourceC2189) = raw30073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2189 sourceB2189 sourceC2189 difference raw30073; decide +kernel
    rw [ha]
    exact (canonical30073 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2189 + difference 0 5) (sourceB2189 + difference 5 0) sourceC2189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2189 + difference 0 5) (sourceB2189 + difference 5 0) sourceC2189) = raw30074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2189 sourceB2189 sourceC2189 difference raw30074; decide +kernel
    rw [ha]
    exact (canonical30074 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2189 + sourceB2189) sourceC2189) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2189 + sourceB2189) sourceC2189) = raw30075 := by
      apply Matrix.ext; unfold doubleCharges sourceA2189 sourceB2189 sourceC2189 raw30075; decide +kernel
    rw [ha]
    exact (canonical30075 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2189 sourceB2189 sourceC2189
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2189, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2192 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2192 + difference 0 1) (sourceB2192 + difference 1 0) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2192 + difference 0 1) (sourceB2192 + difference 1 0) sourceC2192) = raw30110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30110; decide +kernel
    rw [ha]
    exact (canonical30110 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2192 + difference 0 2) (sourceB2192 + difference 2 0) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2192 + difference 0 2) (sourceB2192 + difference 2 0) sourceC2192) = raw30111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30111; decide +kernel
    rw [ha]
    exact (canonical30111 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2192 + difference 0 3) (sourceB2192 + difference 3 0) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2192 + difference 0 3) (sourceB2192 + difference 3 0) sourceC2192) = raw30112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30112; decide +kernel
    rw [ha]
    exact (canonical30112 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2192 + difference 0 4) (sourceB2192 + difference 4 0) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA2192 + difference 0 4) (sourceB2192 + difference 4 0) sourceC2192) = raw10402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10402; decide +kernel
    rw [ha]
    exact (canonical10402 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2192 + difference 0 5) (sourceB2192 + difference 5 0) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2192 + difference 0 5) (sourceB2192 + difference 5 0) sourceC2192) = raw30113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30113; decide +kernel
    rw [ha]
    exact (canonical30113 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2192 + difference 1 0) (sourceB2192 + difference 0 1) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA2192 + difference 1 0) (sourceB2192 + difference 0 1) sourceC2192) = raw10422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10422; decide +kernel
    rw [ha]
    exact (canonical10422 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2192 + difference 1 2) (sourceB2192 + difference 2 1) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2192 + difference 1 2) (sourceB2192 + difference 2 1) sourceC2192) = raw10424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10424; decide +kernel
    rw [ha]
    exact (canonical10424 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2192 + difference 1 3) (sourceB2192 + difference 3 1) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA2192 + difference 1 3) (sourceB2192 + difference 3 1) sourceC2192) = raw10425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10425; decide +kernel
    rw [ha]
    exact (canonical10425 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2192 + difference 1 4) (sourceB2192 + difference 4 1) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA2192 + difference 1 4) (sourceB2192 + difference 4 1) sourceC2192) = raw22699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw22699; decide +kernel
    rw [ha]
    exact (canonical22699 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2192 + difference 1 5) (sourceB2192 + difference 5 1) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA2192 + difference 1 5) (sourceB2192 + difference 5 1) sourceC2192) = raw10426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10426; decide +kernel
    rw [ha]
    exact (canonical10426 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2192 + difference 2 0) (sourceB2192 + difference 0 2) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3267) := by
    have ha : (tripleCharges (sourceA2192 + difference 2 0) (sourceB2192 + difference 0 2) sourceC2192) = raw22705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw22705; decide +kernel
    rw [ha]
    exact (canonical22705 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2192 + difference 2 1) (sourceB2192 + difference 1 2) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2192 + difference 2 1) (sourceB2192 + difference 1 2) sourceC2192) = raw30114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30114; decide +kernel
    rw [ha]
    exact (canonical30114 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2192 + difference 2 3) (sourceB2192 + difference 3 2) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3450) := by
    have ha : (tripleCharges (sourceA2192 + difference 2 3) (sourceB2192 + difference 3 2) sourceC2192) = raw30115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30115; decide +kernel
    rw [ha]
    exact (canonical30115 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2192 + difference 2 4) (sourceB2192 + difference 4 2) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA2192 + difference 2 4) (sourceB2192 + difference 4 2) sourceC2192) = raw10413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10413; decide +kernel
    rw [ha]
    exact (canonical10413 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2192 + difference 2 5) (sourceB2192 + difference 5 2) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA2192 + difference 2 5) (sourceB2192 + difference 5 2) sourceC2192) = raw30116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30116; decide +kernel
    rw [ha]
    exact (canonical30116 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2192 + difference 3 0) (sourceB2192 + difference 0 3) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3271) := by
    have ha : (tripleCharges (sourceA2192 + difference 3 0) (sourceB2192 + difference 0 3) sourceC2192) = raw22709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw22709; decide +kernel
    rw [ha]
    exact (canonical22709 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2192 + difference 3 1) (sourceB2192 + difference 1 3) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3555) := by
    have ha : (tripleCharges (sourceA2192 + difference 3 1) (sourceB2192 + difference 1 3) sourceC2192) = raw30117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30117; decide +kernel
    rw [ha]
    exact (canonical30117 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2192 + difference 3 2) (sourceB2192 + difference 2 3) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3556) := by
    have ha : (tripleCharges (sourceA2192 + difference 3 2) (sourceB2192 + difference 2 3) sourceC2192) = raw30118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30118; decide +kernel
    rw [ha]
    exact (canonical30118 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2192 + difference 3 4) (sourceB2192 + difference 4 3) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA2192 + difference 3 4) (sourceB2192 + difference 4 3) sourceC2192) = raw10418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10418; decide +kernel
    rw [ha]
    exact (canonical10418 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2192 + difference 3 5) (sourceB2192 + difference 5 3) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2192 + difference 3 5) (sourceB2192 + difference 5 3) sourceC2192) = raw30119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30119; decide +kernel
    rw [ha]
    exact (canonical30119 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2192 + difference 4 0) (sourceB2192 + difference 0 4) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA2192 + difference 4 0) (sourceB2192 + difference 0 4) sourceC2192) = raw22713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw22713; decide +kernel
    rw [ha]
    exact (canonical22713 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2192 + difference 4 1) (sourceB2192 + difference 1 4) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2192 + difference 4 1) (sourceB2192 + difference 1 4) sourceC2192) = raw30120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30120; decide +kernel
    rw [ha]
    exact (canonical30120 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2192 + difference 4 2) (sourceB2192 + difference 2 4) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3403) := by
    have ha : (tripleCharges (sourceA2192 + difference 4 2) (sourceB2192 + difference 2 4) sourceC2192) = raw30121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30121; decide +kernel
    rw [ha]
    exact (canonical30121 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2192 + difference 4 3) (sourceB2192 + difference 3 4) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2192 + difference 4 3) (sourceB2192 + difference 3 4) sourceC2192) = raw30122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30122; decide +kernel
    rw [ha]
    exact (canonical30122 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2192 + difference 4 5) (sourceB2192 + difference 5 4) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2192 + difference 4 5) (sourceB2192 + difference 5 4) sourceC2192) = raw30123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30123; decide +kernel
    rw [ha]
    exact (canonical30123 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2192 + difference 5 0) (sourceB2192 + difference 0 5) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA2192 + difference 5 0) (sourceB2192 + difference 0 5) sourceC2192) = raw22718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw22718; decide +kernel
    rw [ha]
    exact (canonical22718 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2192 + difference 5 1) (sourceB2192 + difference 1 5) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3512) := by
    have ha : (tripleCharges (sourceA2192 + difference 5 1) (sourceB2192 + difference 1 5) sourceC2192) = raw30124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30124; decide +kernel
    rw [ha]
    exact (canonical30124 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2192 + difference 5 2) (sourceB2192 + difference 2 5) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3510) := by
    have ha : (tripleCharges (sourceA2192 + difference 5 2) (sourceB2192 + difference 2 5) sourceC2192) = raw30125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30125; decide +kernel
    rw [ha]
    exact (canonical30125 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2192 + difference 5 3) (sourceB2192 + difference 3 5) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2192 + difference 5 3) (sourceB2192 + difference 3 5) sourceC2192) = raw30126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30126; decide +kernel
    rw [ha]
    exact (canonical30126 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2192 + difference 5 4) (sourceB2192 + difference 4 5) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA2192 + difference 5 4) (sourceB2192 + difference 4 5) sourceC2192) = raw10428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10428; decide +kernel
    rw [ha]
    exact (canonical10428 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2192 sourceB2192 sourceC2192
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2192, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2193 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2193 + difference 0 1) (sourceB2193 + difference 1 0) sourceC2193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2193 + difference 0 1) (sourceB2193 + difference 1 0) sourceC2193) = raw30127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2193 sourceB2193 sourceC2193 difference raw30127; decide +kernel
    rw [ha]
    exact (canonical30127 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2193 + difference 1 1) (sourceB2193 + difference 1 1) sourceC2193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2193 + difference 1 1) (sourceB2193 + difference 1 1) sourceC2193) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2193 sourceB2193 sourceC2193 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2193 + difference 2 1) (sourceB2193 + difference 1 2) sourceC2193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2348) := by
    have ha : (tripleCharges (sourceA2193 + difference 2 1) (sourceB2193 + difference 1 2) sourceC2193) = raw30128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2193 sourceB2193 sourceC2193 difference raw30128; decide +kernel
    rw [ha]
    exact (canonical30128 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2193 + difference 3 1) (sourceB2193 + difference 1 3) sourceC2193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2356) := by
    have ha : (tripleCharges (sourceA2193 + difference 3 1) (sourceB2193 + difference 1 3) sourceC2193) = raw30129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2193 sourceB2193 sourceC2193 difference raw30129; decide +kernel
    rw [ha]
    exact (canonical30129 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2193 + difference 4 1) (sourceB2193 + difference 1 4) sourceC2193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2325) := by
    have ha : (tripleCharges (sourceA2193 + difference 4 1) (sourceB2193 + difference 1 4) sourceC2193) = raw30130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2193 sourceB2193 sourceC2193 difference raw30130; decide +kernel
    rw [ha]
    exact (canonical30130 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2193 + difference 5 1) (sourceB2193 + difference 1 5) sourceC2193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2352) := by
    have ha : (tripleCharges (sourceA2193 + difference 5 1) (sourceB2193 + difference 1 5) sourceC2193) = raw30131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2193 sourceB2193 sourceC2193 difference raw30131; decide +kernel
    rw [ha]
    exact (canonical30131 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2193 + sourceB2193) sourceC2193) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2193 + sourceB2193) sourceC2193) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA2193 sourceB2193 sourceC2193 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2193 sourceB2193 sourceC2193
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2193, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2194 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2194 + difference 2 0) (sourceB2194 + difference 0 2) sourceC2194) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1149) := by
    have ha : (tripleCharges (sourceA2194 + difference 2 0) (sourceB2194 + difference 0 2) sourceC2194) = raw22730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2194 sourceB2194 sourceC2194 difference raw22730; decide +kernel
    rw [ha]
    exact (canonical22730 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2194 + difference 2 1) (sourceB2194 + difference 1 2) sourceC2194) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2348) := by
    have ha : (tripleCharges (sourceA2194 + difference 2 1) (sourceB2194 + difference 1 2) sourceC2194) = raw30128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2194 sourceB2194 sourceC2194 difference raw30128; decide +kernel
    rw [ha]
    exact (canonical30128 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2194 + difference 2 2) (sourceB2194 + difference 2 2) sourceC2194) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2194 + difference 2 2) (sourceB2194 + difference 2 2) sourceC2194) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2194 sourceB2194 sourceC2194 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2194 + difference 2 3) (sourceB2194 + difference 3 2) sourceC2194) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2428) := by
    have ha : (tripleCharges (sourceA2194 + difference 2 3) (sourceB2194 + difference 3 2) sourceC2194) = raw30132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2194 sourceB2194 sourceC2194 difference raw30132; decide +kernel
    rw [ha]
    exact (canonical30132 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2194 + difference 2 4) (sourceB2194 + difference 4 2) sourceC2194) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2554) := by
    have ha : (tripleCharges (sourceA2194 + difference 2 4) (sourceB2194 + difference 4 2) sourceC2194) = raw10439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2194 sourceB2194 sourceC2194 difference raw10439; decide +kernel
    rw [ha]
    exact (canonical10439 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2194 + difference 2 5) (sourceB2194 + difference 5 2) sourceC2194) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA2194 + difference 2 5) (sourceB2194 + difference 5 2) sourceC2194) = raw30133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2194 sourceB2194 sourceC2194 difference raw30133; decide +kernel
    rw [ha]
    exact (canonical30133 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2194 + sourceB2194) sourceC2194) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2194 + sourceB2194) sourceC2194) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA2194 sourceB2194 sourceC2194 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2194 sourceB2194 sourceC2194
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2194, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2195 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2195 + difference 0 2) (sourceB2195 + difference 2 0) sourceC2195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3689) := by
    have ha : (tripleCharges (sourceA2195 + difference 0 2) (sourceB2195 + difference 2 0) sourceC2195) = raw30134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2195 sourceB2195 sourceC2195 difference raw30134; decide +kernel
    rw [ha]
    exact (canonical30134 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2195 + difference 1 2) (sourceB2195 + difference 2 1) sourceC2195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2195 + difference 1 2) (sourceB2195 + difference 2 1) sourceC2195) = raw10448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2195 sourceB2195 sourceC2195 difference raw10448; decide +kernel
    rw [ha]
    exact (canonical10448 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2195 + difference 2 2) (sourceB2195 + difference 2 2) sourceC2195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2195 + difference 2 2) (sourceB2195 + difference 2 2) sourceC2195) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2195 sourceB2195 sourceC2195 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2195 + difference 3 2) (sourceB2195 + difference 2 3) sourceC2195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2525) := by
    have ha : (tripleCharges (sourceA2195 + difference 3 2) (sourceB2195 + difference 2 3) sourceC2195) = raw30135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2195 sourceB2195 sourceC2195 difference raw30135; decide +kernel
    rw [ha]
    exact (canonical30135 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2195 + difference 4 2) (sourceB2195 + difference 2 4) sourceC2195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2319) := by
    have ha : (tripleCharges (sourceA2195 + difference 4 2) (sourceB2195 + difference 2 4) sourceC2195) = raw30136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2195 sourceB2195 sourceC2195 difference raw30136; decide +kernel
    rw [ha]
    exact (canonical30136 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2195 + difference 5 2) (sourceB2195 + difference 2 5) sourceC2195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2524) := by
    have ha : (tripleCharges (sourceA2195 + difference 5 2) (sourceB2195 + difference 2 5) sourceC2195) = raw30137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2195 sourceB2195 sourceC2195 difference raw30137; decide +kernel
    rw [ha]
    exact (canonical30137 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2195 + sourceB2195) sourceC2195) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2195 + sourceB2195) sourceC2195) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA2195 sourceB2195 sourceC2195 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2195 sourceB2195 sourceC2195
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2195, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2196 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2196 + difference 3 0) (sourceB2196 + difference 0 3) sourceC2196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1160) := by
    have ha : (tripleCharges (sourceA2196 + difference 3 0) (sourceB2196 + difference 0 3) sourceC2196) = raw22731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2196 sourceB2196 sourceC2196 difference raw22731; decide +kernel
    rw [ha]
    exact (canonical22731 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2196 + difference 3 1) (sourceB2196 + difference 1 3) sourceC2196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2356) := by
    have ha : (tripleCharges (sourceA2196 + difference 3 1) (sourceB2196 + difference 1 3) sourceC2196) = raw30129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2196 sourceB2196 sourceC2196 difference raw30129; decide +kernel
    rw [ha]
    exact (canonical30129 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2196 + difference 3 2) (sourceB2196 + difference 2 3) sourceC2196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2525) := by
    have ha : (tripleCharges (sourceA2196 + difference 3 2) (sourceB2196 + difference 2 3) sourceC2196) = raw30135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2196 sourceB2196 sourceC2196 difference raw30135; decide +kernel
    rw [ha]
    exact (canonical30135 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2196 + difference 3 3) (sourceB2196 + difference 3 3) sourceC2196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2196 + difference 3 3) (sourceB2196 + difference 3 3) sourceC2196) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2196 sourceB2196 sourceC2196 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2196 + difference 3 4) (sourceB2196 + difference 4 3) sourceC2196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA2196 + difference 3 4) (sourceB2196 + difference 4 3) sourceC2196) = raw10440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2196 sourceB2196 sourceC2196 difference raw10440; decide +kernel
    rw [ha]
    exact (canonical10440 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2196 + difference 3 5) (sourceB2196 + difference 5 3) sourceC2196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2196 + difference 3 5) (sourceB2196 + difference 5 3) sourceC2196) = raw30138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2196 sourceB2196 sourceC2196 difference raw30138; decide +kernel
    rw [ha]
    exact (canonical30138 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2196 + sourceB2196) sourceC2196) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2196 + sourceB2196) sourceC2196) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA2196 sourceB2196 sourceC2196 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2196 sourceB2196 sourceC2196
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2196, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2203 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2203 + difference 0 0) (sourceB2203 + difference 0 0) sourceC2203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2541) := by
    have ha : (tripleCharges (sourceA2203 + difference 0 0) (sourceB2203 + difference 0 0) sourceC2203) = raw22871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2203 sourceB2203 sourceC2203 difference raw22871; decide +kernel
    rw [ha]
    exact (canonical22871 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2203 + difference 0 1) (sourceB2203 + difference 1 0) sourceC2203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3646) := by
    have ha : (tripleCharges (sourceA2203 + difference 0 1) (sourceB2203 + difference 1 0) sourceC2203) = raw30199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2203 sourceB2203 sourceC2203 difference raw30199; decide +kernel
    rw [ha]
    exact (canonical30199 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2203 + difference 0 2) (sourceB2203 + difference 2 0) sourceC2203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3650) := by
    have ha : (tripleCharges (sourceA2203 + difference 0 2) (sourceB2203 + difference 2 0) sourceC2203) = raw30200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2203 sourceB2203 sourceC2203 difference raw30200; decide +kernel
    rw [ha]
    exact (canonical30200 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2203 + difference 0 3) (sourceB2203 + difference 3 0) sourceC2203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3650) := by
    have ha : (tripleCharges (sourceA2203 + difference 0 3) (sourceB2203 + difference 3 0) sourceC2203) = raw30201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2203 sourceB2203 sourceC2203 difference raw30201; decide +kernel
    rw [ha]
    exact (canonical30201 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2203 + difference 0 4) (sourceB2203 + difference 4 0) sourceC2203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2203 + difference 0 4) (sourceB2203 + difference 4 0) sourceC2203) = raw28989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2203 sourceB2203 sourceC2203 difference raw28989; decide +kernel
    rw [ha]
    exact (canonical28989 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2203 + difference 0 5) (sourceB2203 + difference 5 0) sourceC2203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2203 + difference 0 5) (sourceB2203 + difference 5 0) sourceC2203) = raw30202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2203 sourceB2203 sourceC2203 difference raw30202; decide +kernel
    rw [ha]
    exact (canonical30202 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2203 + sourceB2203) sourceC2203) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2203 + sourceB2203) sourceC2203) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA2203 sourceB2203 sourceC2203 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2203 sourceB2203 sourceC2203
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2203, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1808 : Integer.Sparse.reindex keyMap MixedData.row1808 = numericRow1808 := by decide +kernel

theorem numericCheck1808 (x : Master → ℝ) : Integer.Sparse.eval numericRow1808 x =
    (1 : ℝ) * reducedSource1808 x := by
  norm_num [numericRow1808, reducedSource1808, Integer.Sparse.eval, Sparse.eval, nodeValue2799, nodeValue2802, nodeValue2818, nodeValue2868, nodeValue3694, nodeValue4091]

theorem reindexCheck1809 : Integer.Sparse.reindex keyMap MixedData.row1809 = numericRow1809 := by decide +kernel

theorem numericCheck1809 (x : Master → ℝ) : Integer.Sparse.eval numericRow1809 x =
    (1 : ℝ) * reducedSource1809 x := by
  norm_num [numericRow1809, reducedSource1809, Integer.Sparse.eval, Sparse.eval, nodeValue1322, nodeValue2818, nodeValue2849, nodeValue2868, nodeValue2884, nodeValue4091]

theorem reindexCheck1810 : Integer.Sparse.reindex keyMap MixedData.row1810 = numericRow1810 := by decide +kernel

theorem numericCheck1810 (x : Master → ℝ) : Integer.Sparse.eval numericRow1810 x =
    (1 : ℝ) * reducedSource1810 x := by
  norm_num [numericRow1810, reducedSource1810, Integer.Sparse.eval, Sparse.eval, nodeValue1819, nodeValue2812, nodeValue2821, nodeValue2888, nodeValue3397, nodeValue4084]

theorem reindexCheck1812 : Integer.Sparse.reindex keyMap MixedData.row1812 = numericRow1812 := by decide +kernel

theorem numericCheck1812 (x : Master → ℝ) : Integer.Sparse.eval numericRow1812 x =
    (1 : ℝ) * reducedSource1812 x := by
  norm_num [numericRow1812, reducedSource1812, Integer.Sparse.eval, Sparse.eval, nodeValue1734, nodeValue1735, nodeValue1740, nodeValue1748, nodeValue3413, nodeValue3423, nodeValue3474, nodeValue3475, nodeValue3480, nodeValue3486, nodeValue3578, nodeValue3579, nodeValue3584, nodeValue3595, nodeValue3596, nodeValue3624, nodeValue3626, nodeValue3767, nodeValue3775, nodeValue3817, nodeValue3963]

theorem reindexCheck1813 : Integer.Sparse.reindex keyMap MixedData.row1813 = numericRow1813 := by decide +kernel

theorem numericCheck1813 (x : Master → ℝ) : Integer.Sparse.eval numericRow1813 x =
    (1 : ℝ) * reducedSource1813 x := by
  norm_num [numericRow1813, reducedSource1813, Integer.Sparse.eval, Sparse.eval, nodeValue2345, nodeValue2813, nodeValue2820, nodeValue2889, nodeValue3707, nodeValue4092]

theorem reindexCheck1814 : Integer.Sparse.reindex keyMap MixedData.row1814 = numericRow1814 := by decide +kernel

theorem numericCheck1814 (x : Master → ℝ) : Integer.Sparse.eval numericRow1814 x =
    (1 : ℝ) * reducedSource1814 x := by
  norm_num [numericRow1814, reducedSource1814, Integer.Sparse.eval, Sparse.eval, nodeValue2533, nodeValue3679, nodeValue3681, nodeValue3695, nodeValue3795, nodeValue3832, nodeValue4088]

theorem reindexCheck1817 : Integer.Sparse.reindex keyMap MixedData.row1817 = numericRow1817 := by decide +kernel

theorem numericCheck1817 (x : Master → ℝ) : Integer.Sparse.eval numericRow1817 x =
    (1 : ℝ) * reducedSource1817 x := by
  norm_num [numericRow1817, reducedSource1817, Integer.Sparse.eval, Sparse.eval, nodeValue3267, nodeValue3268, nodeValue3271, nodeValue3272, nodeValue3301, nodeValue3403, nodeValue3411, nodeValue3415, nodeValue3450, nodeValue3457, nodeValue3468, nodeValue3485, nodeValue3508, nodeValue3510, nodeValue3512, nodeValue3514, nodeValue3515, nodeValue3522, nodeValue3523, nodeValue3547, nodeValue3548, nodeValue3555, nodeValue3556, nodeValue3564, nodeValue3565, nodeValue3757, nodeValue3766, nodeValue3770, nodeValue3807, nodeValue3845]

theorem reindexCheck1818 : Integer.Sparse.reindex keyMap MixedData.row1818 = numericRow1818 := by decide +kernel

theorem numericCheck1818 (x : Master → ℝ) : Integer.Sparse.eval numericRow1818 x =
    (1 : ℝ) * reducedSource1818 x := by
  norm_num [numericRow1818, reducedSource1818, Integer.Sparse.eval, Sparse.eval, nodeValue2325, nodeValue2348, nodeValue2352, nodeValue2356, nodeValue2561, nodeValue3693, nodeValue4092]

theorem reindexCheck1819 : Integer.Sparse.reindex keyMap MixedData.row1819 = numericRow1819 := by decide +kernel

theorem numericCheck1819 (x : Master → ℝ) : Integer.Sparse.eval numericRow1819 x =
    (1 : ℝ) * reducedSource1819 x := by
  norm_num [numericRow1819, reducedSource1819, Integer.Sparse.eval, Sparse.eval, nodeValue1149, nodeValue2348, nodeValue2428, nodeValue2553, nodeValue2554, nodeValue2561, nodeValue4092]

theorem reindexCheck1820 : Integer.Sparse.reindex keyMap MixedData.row1820 = numericRow1820 := by decide +kernel

theorem numericCheck1820 (x : Master → ℝ) : Integer.Sparse.eval numericRow1820 x =
    (1 : ℝ) * reducedSource1820 x := by
  norm_num [numericRow1820, reducedSource1820, Integer.Sparse.eval, Sparse.eval, nodeValue2319, nodeValue2524, nodeValue2525, nodeValue2561, nodeValue3689, nodeValue4092]

theorem reindexCheck1821 : Integer.Sparse.reindex keyMap MixedData.row1821 = numericRow1821 := by decide +kernel

theorem numericCheck1821 (x : Master → ℝ) : Integer.Sparse.eval numericRow1821 x =
    (1 : ℝ) * reducedSource1821 x := by
  norm_num [numericRow1821, reducedSource1821, Integer.Sparse.eval, Sparse.eval, nodeValue1160, nodeValue2356, nodeValue2525, nodeValue2561, nodeValue2590, nodeValue2591, nodeValue4092]

theorem reindexCheck1823 : Integer.Sparse.reindex keyMap MixedData.row1823 = numericRow1823 := by decide +kernel

theorem numericCheck1823 (x : Master → ℝ) : Integer.Sparse.eval numericRow1823 x =
    (1 : ℝ) * reducedSource1823 x := by
  norm_num [numericRow1823, reducedSource1823, Integer.Sparse.eval, Sparse.eval, nodeValue2541, nodeValue3646, nodeValue3650, nodeValue3757, nodeValue4088]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1808 (mixedVector B) = 0 := by
  have h2799 : mixedVector B (Sum.inr 2799) = Sparse.eval nodeValue2799 (mixedVector B) := by
    change mixedMoment B node2799 node2799Labels = _
    exact sound2799 B hB hF
  have h2802 : mixedVector B (Sum.inr 2802) = Sparse.eval nodeValue2802 (mixedVector B) := by
    change mixedMoment B node2802 node2802Labels = _
    exact sound2802 B hB hF
  have h2818 : mixedVector B (Sum.inr 2818) = Sparse.eval nodeValue2818 (mixedVector B) := by
    change mixedMoment B node2818 node2818Labels = _
    exact sound2818 B hB hF
  have h2868 : mixedVector B (Sum.inr 2868) = Sparse.eval nodeValue2868 (mixedVector B) := by
    change mixedMoment B node2868 node2868Labels = _
    exact sound2868 B hB hF
  have h3694 : mixedVector B (Sum.inr 3694) = Sparse.eval nodeValue3694 (mixedVector B) := by
    change mixedMoment B node3694 node3694Labels = _
    exact sound3694 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2175, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2799, h2802, h2818, h2868, h3694, h4091, reducedSource1808] using sourceEq2175 B hB

theorem rowSound1808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1808 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1808, numericCheck1808, reducedZero1808 B hB hF, mul_zero]

theorem reducedZero1809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1809 (mixedVector B) = 0 := by
  have h1322 : mixedVector B (Sum.inr 1322) = Sparse.eval nodeValue1322 (mixedVector B) := by
    change mixedMoment B node1322 node1322Labels = _
    exact sound1322 B hB hF
  have h2818 : mixedVector B (Sum.inr 2818) = Sparse.eval nodeValue2818 (mixedVector B) := by
    change mixedMoment B node2818 node2818Labels = _
    exact sound2818 B hB hF
  have h2849 : mixedVector B (Sum.inr 2849) = Sparse.eval nodeValue2849 (mixedVector B) := by
    change mixedMoment B node2849 node2849Labels = _
    exact sound2849 B hB hF
  have h2868 : mixedVector B (Sum.inr 2868) = Sparse.eval nodeValue2868 (mixedVector B) := by
    change mixedMoment B node2868 node2868Labels = _
    exact sound2868 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2176, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1322, h2818, h2849, h2868, h2884, h4091, reducedSource1809] using sourceEq2176 B hB

theorem rowSound1809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1809 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1809, numericCheck1809, reducedZero1809 B hB hF, mul_zero]

theorem reducedZero1810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1810 (mixedVector B) = 0 := by
  have h1819 : mixedVector B (Sum.inr 1819) = Sparse.eval nodeValue1819 (mixedVector B) := by
    change mixedMoment B node1819 node1819Labels = _
    exact sound1819 B hB hF
  have h2812 : mixedVector B (Sum.inr 2812) = Sparse.eval nodeValue2812 (mixedVector B) := by
    change mixedMoment B node2812 node2812Labels = _
    exact sound2812 B hB hF
  have h2821 : mixedVector B (Sum.inr 2821) = Sparse.eval nodeValue2821 (mixedVector B) := by
    change mixedMoment B node2821 node2821Labels = _
    exact sound2821 B hB hF
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h3397 : mixedVector B (Sum.inr 3397) = Sparse.eval nodeValue3397 (mixedVector B) := by
    change mixedMoment B node3397 node3397Labels = _
    exact sound3397 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2177, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1819, h2812, h2821, h2888, h3397, h4084, reducedSource1810] using sourceEq2177 B hB

theorem rowSound1810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1810 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1810, numericCheck1810, reducedZero1810 B hB hF, mul_zero]

theorem reducedZero1812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1812 (mixedVector B) = 0 := by
  have h1734 : mixedVector B (Sum.inr 1734) = Sparse.eval nodeValue1734 (mixedVector B) := by
    change mixedMoment B node1734 node1734Labels = _
    exact sound1734 B hB hF
  have h1735 : mixedVector B (Sum.inr 1735) = Sparse.eval nodeValue1735 (mixedVector B) := by
    change mixedMoment B node1735 node1735Labels = _
    exact sound1735 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h3474 : mixedVector B (Sum.inr 3474) = Sparse.eval nodeValue3474 (mixedVector B) := by
    change mixedMoment B node3474 node3474Labels = _
    exact sound3474 B hB hF
  have h3475 : mixedVector B (Sum.inr 3475) = Sparse.eval nodeValue3475 (mixedVector B) := by
    change mixedMoment B node3475 node3475Labels = _
    exact sound3475 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h3578 : mixedVector B (Sum.inr 3578) = Sparse.eval nodeValue3578 (mixedVector B) := by
    change mixedMoment B node3578 node3578Labels = _
    exact sound3578 B hB hF
  have h3579 : mixedVector B (Sum.inr 3579) = Sparse.eval nodeValue3579 (mixedVector B) := by
    change mixedMoment B node3579 node3579Labels = _
    exact sound3579 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3595 : mixedVector B (Sum.inr 3595) = Sparse.eval nodeValue3595 (mixedVector B) := by
    change mixedMoment B node3595 node3595Labels = _
    exact sound3595 B hB hF
  have h3596 : mixedVector B (Sum.inr 3596) = Sparse.eval nodeValue3596 (mixedVector B) := by
    change mixedMoment B node3596 node3596Labels = _
    exact sound3596 B hB hF
  have h3624 : mixedVector B (Sum.inr 3624) = Sparse.eval nodeValue3624 (mixedVector B) := by
    change mixedMoment B node3624 node3624Labels = _
    exact sound3624 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3767 : mixedVector B (Sum.inr 3767) = Sparse.eval nodeValue3767 (mixedVector B) := by
    change mixedMoment B node3767 node3767Labels = _
    exact sound3767 B hB hF
  have h3775 : mixedVector B (Sum.inr 3775) = Sparse.eval nodeValue3775 (mixedVector B) := by
    change mixedMoment B node3775 node3775Labels = _
    exact sound3775 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  have h3963 : mixedVector B (Sum.inr 3963) = Sparse.eval nodeValue3963 (mixedVector B) := by
    change mixedMoment B node3963 node3963Labels = _
    exact sound3963 B hB hF
  simpa only [sourceForm2181, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1734, h1735, h1740, h1748, h3413, h3423, h3474, h3475, h3480, h3486, h3578, h3579, h3584, h3595, h3596, h3624, h3626, h3767, h3775, h3817, h3963, reducedSource1812] using sourceEq2181 B hB

theorem rowSound1812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1812 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1812, numericCheck1812, reducedZero1812 B hB hF, mul_zero]

theorem reducedZero1813 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1813 (mixedVector B) = 0 := by
  have h2345 : mixedVector B (Sum.inr 2345) = Sparse.eval nodeValue2345 (mixedVector B) := by
    change mixedMoment B node2345 node2345Labels = _
    exact sound2345 B hB hF
  have h2813 : mixedVector B (Sum.inr 2813) = Sparse.eval nodeValue2813 (mixedVector B) := by
    change mixedMoment B node2813 node2813Labels = _
    exact sound2813 B hB hF
  have h2820 : mixedVector B (Sum.inr 2820) = Sparse.eval nodeValue2820 (mixedVector B) := by
    change mixedMoment B node2820 node2820Labels = _
    exact sound2820 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h3707 : mixedVector B (Sum.inr 3707) = Sparse.eval nodeValue3707 (mixedVector B) := by
    change mixedMoment B node3707 node3707Labels = _
    exact sound3707 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2182, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2345, h2813, h2820, h2889, h3707, h4092, reducedSource1813] using sourceEq2182 B hB

theorem rowSound1813 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1813 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1813, numericCheck1813, reducedZero1813 B hB hF, mul_zero]

theorem reducedZero1814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1814 (mixedVector B) = 0 := by
  have h2533 : mixedVector B (Sum.inr 2533) = Sparse.eval nodeValue2533 (mixedVector B) := by
    change mixedMoment B node2533 node2533Labels = _
    exact sound2533 B hB hF
  have h3679 : mixedVector B (Sum.inr 3679) = Sparse.eval nodeValue3679 (mixedVector B) := by
    change mixedMoment B node3679 node3679Labels = _
    exact sound3679 B hB hF
  have h3681 : mixedVector B (Sum.inr 3681) = Sparse.eval nodeValue3681 (mixedVector B) := by
    change mixedMoment B node3681 node3681Labels = _
    exact sound3681 B hB hF
  have h3695 : mixedVector B (Sum.inr 3695) = Sparse.eval nodeValue3695 (mixedVector B) := by
    change mixedMoment B node3695 node3695Labels = _
    exact sound3695 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2189, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2533, h3679, h3681, h3695, h3795, h3832, h4088, reducedSource1814] using sourceEq2189 B hB

theorem rowSound1814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1814 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1814, numericCheck1814, reducedZero1814 B hB hF, mul_zero]

theorem reducedZero1817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1817 (mixedVector B) = 0 := by
  have h3267 : mixedVector B (Sum.inr 3267) = Sparse.eval nodeValue3267 (mixedVector B) := by
    change mixedMoment B node3267 node3267Labels = _
    exact sound3267 B hB hF
  have h3268 : mixedVector B (Sum.inr 3268) = Sparse.eval nodeValue3268 (mixedVector B) := by
    change mixedMoment B node3268 node3268Labels = _
    exact sound3268 B hB hF
  have h3271 : mixedVector B (Sum.inr 3271) = Sparse.eval nodeValue3271 (mixedVector B) := by
    change mixedMoment B node3271 node3271Labels = _
    exact sound3271 B hB hF
  have h3272 : mixedVector B (Sum.inr 3272) = Sparse.eval nodeValue3272 (mixedVector B) := by
    change mixedMoment B node3272 node3272Labels = _
    exact sound3272 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3403 : mixedVector B (Sum.inr 3403) = Sparse.eval nodeValue3403 (mixedVector B) := by
    change mixedMoment B node3403 node3403Labels = _
    exact sound3403 B hB hF
  have h3411 : mixedVector B (Sum.inr 3411) = Sparse.eval nodeValue3411 (mixedVector B) := by
    change mixedMoment B node3411 node3411Labels = _
    exact sound3411 B hB hF
  have h3415 : mixedVector B (Sum.inr 3415) = Sparse.eval nodeValue3415 (mixedVector B) := by
    change mixedMoment B node3415 node3415Labels = _
    exact sound3415 B hB hF
  have h3450 : mixedVector B (Sum.inr 3450) = Sparse.eval nodeValue3450 (mixedVector B) := by
    change mixedMoment B node3450 node3450Labels = _
    exact sound3450 B hB hF
  have h3457 : mixedVector B (Sum.inr 3457) = Sparse.eval nodeValue3457 (mixedVector B) := by
    change mixedMoment B node3457 node3457Labels = _
    exact sound3457 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3485 : mixedVector B (Sum.inr 3485) = Sparse.eval nodeValue3485 (mixedVector B) := by
    change mixedMoment B node3485 node3485Labels = _
    exact sound3485 B hB hF
  have h3508 : mixedVector B (Sum.inr 3508) = Sparse.eval nodeValue3508 (mixedVector B) := by
    change mixedMoment B node3508 node3508Labels = _
    exact sound3508 B hB hF
  have h3510 : mixedVector B (Sum.inr 3510) = Sparse.eval nodeValue3510 (mixedVector B) := by
    change mixedMoment B node3510 node3510Labels = _
    exact sound3510 B hB hF
  have h3512 : mixedVector B (Sum.inr 3512) = Sparse.eval nodeValue3512 (mixedVector B) := by
    change mixedMoment B node3512 node3512Labels = _
    exact sound3512 B hB hF
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3515 : mixedVector B (Sum.inr 3515) = Sparse.eval nodeValue3515 (mixedVector B) := by
    change mixedMoment B node3515 node3515Labels = _
    exact sound3515 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3555 : mixedVector B (Sum.inr 3555) = Sparse.eval nodeValue3555 (mixedVector B) := by
    change mixedMoment B node3555 node3555Labels = _
    exact sound3555 B hB hF
  have h3556 : mixedVector B (Sum.inr 3556) = Sparse.eval nodeValue3556 (mixedVector B) := by
    change mixedMoment B node3556 node3556Labels = _
    exact sound3556 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  simpa only [sourceForm2192, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3267, h3268, h3271, h3272, h3301, h3403, h3411, h3415, h3450, h3457, h3468, h3485, h3508, h3510, h3512, h3514, h3515, h3522, h3523, h3547, h3548, h3555, h3556, h3564, h3565, h3757, h3766, h3770, h3807, h3845, reducedSource1817] using sourceEq2192 B hB

theorem rowSound1817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1817 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1817, numericCheck1817, reducedZero1817 B hB hF, mul_zero]

theorem reducedZero1818 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1818 (mixedVector B) = 0 := by
  have h2325 : mixedVector B (Sum.inr 2325) = Sparse.eval nodeValue2325 (mixedVector B) := by
    change mixedMoment B node2325 node2325Labels = _
    exact sound2325 B hB hF
  have h2348 : mixedVector B (Sum.inr 2348) = Sparse.eval nodeValue2348 (mixedVector B) := by
    change mixedMoment B node2348 node2348Labels = _
    exact sound2348 B hB hF
  have h2352 : mixedVector B (Sum.inr 2352) = Sparse.eval nodeValue2352 (mixedVector B) := by
    change mixedMoment B node2352 node2352Labels = _
    exact sound2352 B hB hF
  have h2356 : mixedVector B (Sum.inr 2356) = Sparse.eval nodeValue2356 (mixedVector B) := by
    change mixedMoment B node2356 node2356Labels = _
    exact sound2356 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2193, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2325, h2348, h2352, h2356, h2561, h3693, h4092, reducedSource1818] using sourceEq2193 B hB

theorem rowSound1818 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1818 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1818, numericCheck1818, reducedZero1818 B hB hF, mul_zero]

theorem reducedZero1819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1819 (mixedVector B) = 0 := by
  have h1149 : mixedVector B (Sum.inr 1149) = Sparse.eval nodeValue1149 (mixedVector B) := by
    change mixedMoment B node1149 node1149Labels = _
    exact sound1149 B hB hF
  have h2348 : mixedVector B (Sum.inr 2348) = Sparse.eval nodeValue2348 (mixedVector B) := by
    change mixedMoment B node2348 node2348Labels = _
    exact sound2348 B hB hF
  have h2428 : mixedVector B (Sum.inr 2428) = Sparse.eval nodeValue2428 (mixedVector B) := by
    change mixedMoment B node2428 node2428Labels = _
    exact sound2428 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h2554 : mixedVector B (Sum.inr 2554) = Sparse.eval nodeValue2554 (mixedVector B) := by
    change mixedMoment B node2554 node2554Labels = _
    exact sound2554 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2194, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1149, h2348, h2428, h2553, h2554, h2561, h4092, reducedSource1819] using sourceEq2194 B hB

theorem rowSound1819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1819 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1819, numericCheck1819, reducedZero1819 B hB hF, mul_zero]

theorem reducedZero1820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1820 (mixedVector B) = 0 := by
  have h2319 : mixedVector B (Sum.inr 2319) = Sparse.eval nodeValue2319 (mixedVector B) := by
    change mixedMoment B node2319 node2319Labels = _
    exact sound2319 B hB hF
  have h2524 : mixedVector B (Sum.inr 2524) = Sparse.eval nodeValue2524 (mixedVector B) := by
    change mixedMoment B node2524 node2524Labels = _
    exact sound2524 B hB hF
  have h2525 : mixedVector B (Sum.inr 2525) = Sparse.eval nodeValue2525 (mixedVector B) := by
    change mixedMoment B node2525 node2525Labels = _
    exact sound2525 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h3689 : mixedVector B (Sum.inr 3689) = Sparse.eval nodeValue3689 (mixedVector B) := by
    change mixedMoment B node3689 node3689Labels = _
    exact sound3689 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2195, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2319, h2524, h2525, h2561, h3689, h4092, reducedSource1820] using sourceEq2195 B hB

theorem rowSound1820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1820 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1820, numericCheck1820, reducedZero1820 B hB hF, mul_zero]

theorem reducedZero1821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1821 (mixedVector B) = 0 := by
  have h1160 : mixedVector B (Sum.inr 1160) = Sparse.eval nodeValue1160 (mixedVector B) := by
    change mixedMoment B node1160 node1160Labels = _
    exact sound1160 B hB hF
  have h2356 : mixedVector B (Sum.inr 2356) = Sparse.eval nodeValue2356 (mixedVector B) := by
    change mixedMoment B node2356 node2356Labels = _
    exact sound2356 B hB hF
  have h2525 : mixedVector B (Sum.inr 2525) = Sparse.eval nodeValue2525 (mixedVector B) := by
    change mixedMoment B node2525 node2525Labels = _
    exact sound2525 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h2591 : mixedVector B (Sum.inr 2591) = Sparse.eval nodeValue2591 (mixedVector B) := by
    change mixedMoment B node2591 node2591Labels = _
    exact sound2591 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2196, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1160, h2356, h2525, h2561, h2590, h2591, h4092, reducedSource1821] using sourceEq2196 B hB

theorem rowSound1821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1821 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1821, numericCheck1821, reducedZero1821 B hB hF, mul_zero]

theorem reducedZero1823 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1823 (mixedVector B) = 0 := by
  have h2541 : mixedVector B (Sum.inr 2541) = Sparse.eval nodeValue2541 (mixedVector B) := by
    change mixedMoment B node2541 node2541Labels = _
    exact sound2541 B hB hF
  have h3646 : mixedVector B (Sum.inr 3646) = Sparse.eval nodeValue3646 (mixedVector B) := by
    change mixedMoment B node3646 node3646Labels = _
    exact sound3646 B hB hF
  have h3650 : mixedVector B (Sum.inr 3650) = Sparse.eval nodeValue3650 (mixedVector B) := by
    change mixedMoment B node3650 node3650Labels = _
    exact sound3650 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2203, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2541, h3646, h3650, h3757, h4088, reducedSource1823] using sourceEq2203 B hB

theorem rowSound1823 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1823 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1823, numericCheck1823, reducedZero1823 B hB hF, mul_zero]

theorem sourceRowsAt1808 : MixedData.sourceRows (1808 : Fin 2425) =
    MixedData.row1808 := by decide +kernel

theorem sourceRowsAt1809 : MixedData.sourceRows (1809 : Fin 2425) =
    MixedData.row1809 := by decide +kernel

theorem sourceRowsAt1810 : MixedData.sourceRows (1810 : Fin 2425) =
    MixedData.row1810 := by decide +kernel

theorem sourceRowsAt1811 : MixedData.sourceRows (1811 : Fin 2425) =
    MixedData.row1811 := by decide +kernel

theorem sourceRowsAt1812 : MixedData.sourceRows (1812 : Fin 2425) =
    MixedData.row1812 := by decide +kernel

theorem sourceRowsAt1813 : MixedData.sourceRows (1813 : Fin 2425) =
    MixedData.row1813 := by decide +kernel

theorem sourceRowsAt1814 : MixedData.sourceRows (1814 : Fin 2425) =
    MixedData.row1814 := by decide +kernel

theorem sourceRowsAt1815 : MixedData.sourceRows (1815 : Fin 2425) =
    MixedData.row1815 := by decide +kernel

theorem sourceRowsAt1816 : MixedData.sourceRows (1816 : Fin 2425) =
    MixedData.row1816 := by decide +kernel

theorem sourceRowsAt1817 : MixedData.sourceRows (1817 : Fin 2425) =
    MixedData.row1817 := by decide +kernel

theorem sourceRowsAt1818 : MixedData.sourceRows (1818 : Fin 2425) =
    MixedData.row1818 := by decide +kernel

theorem sourceRowsAt1819 : MixedData.sourceRows (1819 : Fin 2425) =
    MixedData.row1819 := by decide +kernel

theorem sourceRowsAt1820 : MixedData.sourceRows (1820 : Fin 2425) =
    MixedData.row1820 := by decide +kernel

theorem sourceRowsAt1821 : MixedData.sourceRows (1821 : Fin 2425) =
    MixedData.row1821 := by decide +kernel

theorem sourceRowsAt1822 : MixedData.sourceRows (1822 : Fin 2425) =
    MixedData.row1822 := by decide +kernel

theorem sourceRowsAt1823 : MixedData.sourceRows (1823 : Fin 2425) =
    MixedData.row1823 := by decide +kernel

theorem chunkSound113_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 113) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1808 ∨ k.val = 1809 ∨ k.val = 1810 ∨ k.val = 1811 ∨ k.val = 1812 ∨ k.val = 1813 ∨ k.val = 1814 ∨ k.val = 1815 ∨ k.val = 1816 ∨ k.val = 1817 ∨ k.val = 1818 ∨ k.val = 1819 ∨ k.val = 1820 ∨ k.val = 1821 ∨ k.val = 1822 ∨ k.val = 1823 := by omega
  rcases heq with h1808 | h1809 | h1810 | h1811 | h1812 | h1813 | h1814 | h1815 | h1816 | h1817 | h1818 | h1819 | h1820 | h1821 | h1822 | h1823
  · have he : k = (1808 : Fin 2425) := Fin.ext h1808
    subst k
    rw [sourceRowsAt1808]
    exact rowSound1808 B hB hF
  · have he : k = (1809 : Fin 2425) := Fin.ext h1809
    subst k
    rw [sourceRowsAt1809]
    exact rowSound1809 B hB hF
  · have he : k = (1810 : Fin 2425) := Fin.ext h1810
    subst k
    rw [sourceRowsAt1810]
    exact rowSound1810 B hB hF
  · have he : k = (1811 : Fin 2425) := Fin.ext h1811
    subst k
    rw [sourceRowsAt1811]
    exact rowSound1811_e B hB hF
  · have he : k = (1812 : Fin 2425) := Fin.ext h1812
    subst k
    rw [sourceRowsAt1812]
    exact rowSound1812 B hB hF
  · have he : k = (1813 : Fin 2425) := Fin.ext h1813
    subst k
    rw [sourceRowsAt1813]
    exact rowSound1813 B hB hF
  · have he : k = (1814 : Fin 2425) := Fin.ext h1814
    subst k
    rw [sourceRowsAt1814]
    exact rowSound1814 B hB hF
  · have he : k = (1815 : Fin 2425) := Fin.ext h1815
    subst k
    rw [sourceRowsAt1815]
    exact rowSound1815_e B hB hF
  · have he : k = (1816 : Fin 2425) := Fin.ext h1816
    subst k
    rw [sourceRowsAt1816]
    exact rowSound1816_e B hB hF
  · have he : k = (1817 : Fin 2425) := Fin.ext h1817
    subst k
    rw [sourceRowsAt1817]
    exact rowSound1817 B hB hF
  · have he : k = (1818 : Fin 2425) := Fin.ext h1818
    subst k
    rw [sourceRowsAt1818]
    exact rowSound1818 B hB hF
  · have he : k = (1819 : Fin 2425) := Fin.ext h1819
    subst k
    rw [sourceRowsAt1819]
    exact rowSound1819 B hB hF
  · have he : k = (1820 : Fin 2425) := Fin.ext h1820
    subst k
    rw [sourceRowsAt1820]
    exact rowSound1820 B hB hF
  · have he : k = (1821 : Fin 2425) := Fin.ext h1821
    subst k
    rw [sourceRowsAt1821]
    exact rowSound1821 B hB hF
  · have he : k = (1822 : Fin 2425) := Fin.ext h1822
    subst k
    rw [sourceRowsAt1822]
    exact rowSound1822_e B hB hF
  · have he : k = (1823 : Fin 2425) := Fin.ext h1823
    subst k
    rw [sourceRowsAt1823]
    exact rowSound1823 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e_oai
