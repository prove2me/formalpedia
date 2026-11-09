-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:28:39.350207+00:00
-- url     : https://prove2.me/submissions/0551aa63-5786-46b5-9566-0cb4502ce90f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1030_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1033_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1034_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19830 raw19830Labels = mixedMoment B node832 node832Labels := by
  calc
    mixedMoment B raw19830 raw19830Labels = mixedMoment B raw19830step0 raw19830step0Labels := by
      have hz : ∀ j, raw19830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19830step0 = (fun i j => raw19830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19830step0 raw19830; decide +kernel
      have hl : raw19830step0Labels = raw19830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19830 raw19830Labels permutation434 hz
    mixedMoment B raw19830step0 raw19830step0Labels = mixedMoment B raw19830step1 raw19830step1Labels := by
      have hz : ∀ j, raw19830step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19830step1 = (fun i j => raw19830step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19830step1 raw19830step0; decide +kernel
      have hl : raw19830step1Labels = raw19830step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19830step0 raw19830step0Labels permutation80 hz
    mixedMoment B raw19830step1 raw19830step1Labels = mixedMoment B raw19830step2 raw19830step2Labels := by
      have hz : ∀ j, raw19830step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19830step2 = (fun i j => raw19830step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19830step2 raw19830step1; decide +kernel
      have hl : raw19830step2Labels = raw19830step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19830step1 raw19830step1Labels permutation14 hz
    mixedMoment B raw19830step2 raw19830step2Labels = mixedMoment B raw19830step3 raw19830step3Labels := by
      have ha : raw19830step3 = (fun i j => raw19830step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19830step3 raw19830step2; decide +kernel
      have hl : raw19830step3Labels = raw19830step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19830step2 raw19830step2Labels permutation7 permutation2
    mixedMoment B raw19830step3 raw19830step3Labels = mixedMoment B raw19830step4 raw19830step4Labels := by
      have ha : raw19830step4 = -raw19830step3 := by apply Matrix.ext; change ∀ i j, raw19830step4 i j = -(raw19830step3 i j); unfold raw19830step4 raw19830step3; decide +kernel
      have hl : raw19830step4Labels = raw19830step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node832 node832Labels := by rfl

theorem canonical19834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19834 raw19834Labels = mixedMoment B node859 node859Labels := by
  calc
    mixedMoment B raw19834 raw19834Labels = mixedMoment B raw19834step0 raw19834step0Labels := by
      have hz : ∀ j, raw19834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19834step0 = (fun i j => raw19834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19834step0 raw19834; decide +kernel
      have hl : raw19834step0Labels = raw19834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19834 raw19834Labels permutation434 hz
    mixedMoment B raw19834step0 raw19834step0Labels = mixedMoment B raw19834step1 raw19834step1Labels := by
      have hz : ∀ j, raw19834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19834step1 = (fun i j => raw19834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19834step1 raw19834step0; decide +kernel
      have hl : raw19834step1Labels = raw19834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19834step0 raw19834step0Labels permutation80 hz
    mixedMoment B raw19834step1 raw19834step1Labels = mixedMoment B raw19834step2 raw19834step2Labels := by
      have hz : ∀ j, raw19834step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19834step2 = (fun i j => raw19834step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19834step2 raw19834step1; decide +kernel
      have hl : raw19834step2Labels = raw19834step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19834step1 raw19834step1Labels permutation14 hz
    mixedMoment B raw19834step2 raw19834step2Labels = mixedMoment B raw19834step3 raw19834step3Labels := by
      have ha : raw19834step3 = (fun i j => raw19834step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19834step3 raw19834step2; decide +kernel
      have hl : raw19834step3Labels = raw19834step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19834step2 raw19834step2Labels permutation7 permutation2
    mixedMoment B raw19834step3 raw19834step3Labels = mixedMoment B raw19834step4 raw19834step4Labels := by
      have ha : raw19834step4 = -raw19834step3 := by apply Matrix.ext; change ∀ i j, raw19834step4 i j = -(raw19834step3 i j); unfold raw19834step4 raw19834step3; decide +kernel
      have hl : raw19834step4Labels = raw19834step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node859 node859Labels := by rfl

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

theorem canonical19837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19837 raw19837Labels = mixedMoment B node726 node726Labels := by
  calc
    mixedMoment B raw19837 raw19837Labels = mixedMoment B raw19837step0 raw19837step0Labels := by
      have hz : ∀ j, raw19837 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19837step0 = (fun i j => raw19837 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19837step0 raw19837; decide +kernel
      have hl : raw19837step0Labels = raw19837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19837 raw19837Labels permutation434 hz
    mixedMoment B raw19837step0 raw19837step0Labels = mixedMoment B raw19837step1 raw19837step1Labels := by
      have hz : ∀ j, raw19837step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19837step1 = (fun i j => raw19837step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19837step1 raw19837step0; decide +kernel
      have hl : raw19837step1Labels = raw19837step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19837step0 raw19837step0Labels permutation80 hz
    mixedMoment B raw19837step1 raw19837step1Labels = mixedMoment B raw19837step2 raw19837step2Labels := by
      have ha : raw19837step2 = (fun i j => raw19837step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19837step2 raw19837step1; decide +kernel
      have hl : raw19837step2Labels = raw19837step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19837step1 raw19837step1Labels permutation29 permutation2
    mixedMoment B raw19837step2 raw19837step2Labels = mixedMoment B raw19837step3 raw19837step3Labels := by
      have ha : raw19837step3 = -raw19837step2 := by apply Matrix.ext; change ∀ i j, raw19837step3 i j = -(raw19837step2 i j); unfold raw19837step3 raw19837step2; decide +kernel
      have hl : raw19837step3Labels = raw19837step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node726 node726Labels := by rfl

theorem canonical19838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19838 raw19838Labels = mixedMoment B node726 node726Labels := by
  calc
    mixedMoment B raw19838 raw19838Labels = mixedMoment B raw19838step0 raw19838step0Labels := by
      have hz : ∀ j, raw19838 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19838step0 = (fun i j => raw19838 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19838step0 raw19838; decide +kernel
      have hl : raw19838step0Labels = raw19838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19838 raw19838Labels permutation434 hz
    mixedMoment B raw19838step0 raw19838step0Labels = mixedMoment B raw19838step1 raw19838step1Labels := by
      have hz : ∀ j, raw19838step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19838step1 = (fun i j => raw19838step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19838step1 raw19838step0; decide +kernel
      have hl : raw19838step1Labels = raw19838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19838step0 raw19838step0Labels permutation56 hz
    mixedMoment B raw19838step1 raw19838step1Labels = mixedMoment B raw19838step2 raw19838step2Labels := by
      have ha : raw19838step2 = (fun i j => raw19838step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19838step2 raw19838step1; decide +kernel
      have hl : raw19838step2Labels = raw19838step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19838step1 raw19838step1Labels permutation29 permutation2
    mixedMoment B raw19838step2 raw19838step2Labels = mixedMoment B raw19838step3 raw19838step3Labels := by
      have ha : raw19838step3 = -raw19838step2 := by apply Matrix.ext; change ∀ i j, raw19838step3 i j = -(raw19838step2 i j); unfold raw19838step3 raw19838step2; decide +kernel
      have hl : raw19838step3Labels = raw19838step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node726 node726Labels := by rfl

theorem canonical19839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19839 raw19839Labels = mixedMoment B node726 node726Labels := by
  calc
    mixedMoment B raw19839 raw19839Labels = mixedMoment B raw19839step0 raw19839step0Labels := by
      have hz : ∀ j, raw19839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19839step0 = (fun i j => raw19839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19839step0 raw19839; decide +kernel
      have hl : raw19839step0Labels = raw19839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19839 raw19839Labels permutation346 hz
    mixedMoment B raw19839step0 raw19839step0Labels = mixedMoment B raw19839step1 raw19839step1Labels := by
      have hz : ∀ j, raw19839step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19839step1 = (fun i j => raw19839step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19839step1 raw19839step0; decide +kernel
      have hl : raw19839step1Labels = raw19839step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19839step0 raw19839step0Labels permutation56 hz
    mixedMoment B raw19839step1 raw19839step1Labels = mixedMoment B raw19839step2 raw19839step2Labels := by
      have ha : raw19839step2 = (fun i j => raw19839step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19839step2 raw19839step1; decide +kernel
      have hl : raw19839step2Labels = raw19839step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19839step1 raw19839step1Labels permutation29 permutation2
    mixedMoment B raw19839step2 raw19839step2Labels = mixedMoment B raw19839step3 raw19839step3Labels := by
      have ha : raw19839step3 = -raw19839step2 := by apply Matrix.ext; change ∀ i j, raw19839step3 i j = -(raw19839step2 i j); unfold raw19839step3 raw19839step2; decide +kernel
      have hl : raw19839step3Labels = raw19839step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node726 node726Labels := by rfl

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

theorem canonical19840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19840 raw19840Labels = mixedMoment B node564 node564Labels := by
  calc
    mixedMoment B raw19840 raw19840Labels = mixedMoment B raw19840step0 raw19840step0Labels := by
      have hz : ∀ j, raw19840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19840step0 = (fun i j => raw19840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19840step0 raw19840; decide +kernel
      have hl : raw19840step0Labels = raw19840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19840 raw19840Labels permutation434 hz
    mixedMoment B raw19840step0 raw19840step0Labels = mixedMoment B raw19840step1 raw19840step1Labels := by
      have hz : ∀ j, raw19840step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19840step1 = (fun i j => raw19840step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19840step1 raw19840step0; decide +kernel
      have hl : raw19840step1Labels = raw19840step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19840step0 raw19840step0Labels permutation80 hz
    mixedMoment B raw19840step1 raw19840step1Labels = mixedMoment B raw19840step2 raw19840step2Labels := by
      have hz : ∀ j, raw19840step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19840step2 = (fun i j => raw19840step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19840step2 raw19840step1; decide +kernel
      have hl : raw19840step2Labels = raw19840step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19840step1 raw19840step1Labels permutation14 hz
    mixedMoment B raw19840step2 raw19840step2Labels = mixedMoment B raw19840step3 raw19840step3Labels := by
      have ha : raw19840step3 = (fun i j => raw19840step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19840step3 raw19840step2; decide +kernel
      have hl : raw19840step3Labels = raw19840step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19840step2 raw19840step2Labels permutation7 permutation2
    mixedMoment B raw19840step3 raw19840step3Labels = mixedMoment B raw19840step4 raw19840step4Labels := by
      have ha : raw19840step4 = -raw19840step3 := by apply Matrix.ext; change ∀ i j, raw19840step4 i j = -(raw19840step3 i j); unfold raw19840step4 raw19840step3; decide +kernel
      have hl : raw19840step4Labels = raw19840step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node564 node564Labels := by rfl

theorem canonical19841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19841 raw19841Labels = mixedMoment B node1186 node1186Labels := by
  calc
    mixedMoment B raw19841 raw19841Labels = mixedMoment B raw19841step0 raw19841step0Labels := by
      have hz : ∀ j, raw19841 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19841step0 = (fun i j => raw19841 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19841step0 raw19841; decide +kernel
      have hl : raw19841step0Labels = raw19841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19841 raw19841Labels permutation434 hz
    mixedMoment B raw19841step0 raw19841step0Labels = mixedMoment B raw19841step1 raw19841step1Labels := by
      have hz : ∀ j, raw19841step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19841step1 = (fun i j => raw19841step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19841step1 raw19841step0; decide +kernel
      have hl : raw19841step1Labels = raw19841step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19841step0 raw19841step0Labels permutation80 hz
    mixedMoment B raw19841step1 raw19841step1Labels = mixedMoment B raw19841step2 raw19841step2Labels := by
      have ha : raw19841step2 = (fun i j => raw19841step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19841step2 raw19841step1; decide +kernel
      have hl : raw19841step2Labels = raw19841step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19841step1 raw19841step1Labels permutation10 permutation2
    _ = mixedMoment B node1186 node1186Labels := by rfl

theorem canonical19842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19842 raw19842Labels = mixedMoment B node1186 node1186Labels := by
  calc
    mixedMoment B raw19842 raw19842Labels = mixedMoment B raw19842step0 raw19842step0Labels := by
      have hz : ∀ j, raw19842 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19842step0 = (fun i j => raw19842 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19842step0 raw19842; decide +kernel
      have hl : raw19842step0Labels = raw19842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19842 raw19842Labels permutation434 hz
    mixedMoment B raw19842step0 raw19842step0Labels = mixedMoment B raw19842step1 raw19842step1Labels := by
      have hz : ∀ j, raw19842step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19842step1 = (fun i j => raw19842step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19842step1 raw19842step0; decide +kernel
      have hl : raw19842step1Labels = raw19842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19842step0 raw19842step0Labels permutation56 hz
    mixedMoment B raw19842step1 raw19842step1Labels = mixedMoment B raw19842step2 raw19842step2Labels := by
      have ha : raw19842step2 = (fun i j => raw19842step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19842step2 raw19842step1; decide +kernel
      have hl : raw19842step2Labels = raw19842step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19842step1 raw19842step1Labels permutation10 permutation2
    _ = mixedMoment B node1186 node1186Labels := by rfl

theorem canonical19843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19843 raw19843Labels = mixedMoment B node1186 node1186Labels := by
  calc
    mixedMoment B raw19843 raw19843Labels = mixedMoment B raw19843step0 raw19843step0Labels := by
      have hz : ∀ j, raw19843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19843step0 = (fun i j => raw19843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19843step0 raw19843; decide +kernel
      have hl : raw19843step0Labels = raw19843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19843 raw19843Labels permutation346 hz
    mixedMoment B raw19843step0 raw19843step0Labels = mixedMoment B raw19843step1 raw19843step1Labels := by
      have hz : ∀ j, raw19843step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19843step1 = (fun i j => raw19843step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19843step1 raw19843step0; decide +kernel
      have hl : raw19843step1Labels = raw19843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19843step0 raw19843step0Labels permutation56 hz
    mixedMoment B raw19843step1 raw19843step1Labels = mixedMoment B raw19843step2 raw19843step2Labels := by
      have ha : raw19843step2 = (fun i j => raw19843step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19843step2 raw19843step1; decide +kernel
      have hl : raw19843step2Labels = raw19843step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19843step1 raw19843step1Labels permutation10 permutation2
    _ = mixedMoment B node1186 node1186Labels := by rfl

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

theorem canonical19850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19850 raw19850Labels = mixedMoment B node791 node791Labels := by
  calc
    mixedMoment B raw19850 raw19850Labels = mixedMoment B raw19850step0 raw19850step0Labels := by
      have hz : ∀ j, raw19850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19850step0 = (fun i j => raw19850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19850step0 raw19850; decide +kernel
      have hl : raw19850step0Labels = raw19850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19850 raw19850Labels permutation346 hz
    mixedMoment B raw19850step0 raw19850step0Labels = mixedMoment B raw19850step1 raw19850step1Labels := by
      have hz : ∀ j, raw19850step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19850step1 = (fun i j => raw19850step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19850step1 raw19850step0; decide +kernel
      have hl : raw19850step1Labels = raw19850step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19850step0 raw19850step0Labels permutation56 hz
    mixedMoment B raw19850step1 raw19850step1Labels = mixedMoment B raw19850step2 raw19850step2Labels := by
      have ha : raw19850step2 = (fun i j => raw19850step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19850step2 raw19850step1; decide +kernel
      have hl : raw19850step2Labels = raw19850step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19850step1 raw19850step1Labels permutation29 permutation2
    mixedMoment B raw19850step2 raw19850step2Labels = mixedMoment B raw19850step3 raw19850step3Labels := by
      have ha : raw19850step3 = -raw19850step2 := by apply Matrix.ext; change ∀ i j, raw19850step3 i j = -(raw19850step2 i j); unfold raw19850step3 raw19850step2; decide +kernel
      have hl : raw19850step3Labels = raw19850step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node791 node791Labels := by rfl

theorem canonical19851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19851 raw19851Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw19851 raw19851Labels = mixedMoment B raw19851step0 raw19851step0Labels := by
      have hz : ∀ j, raw19851 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19851step0 = (fun i j => raw19851 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19851step0 raw19851; decide +kernel
      have hl : raw19851step0Labels = raw19851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19851 raw19851Labels permutation346 hz
    mixedMoment B raw19851step0 raw19851step0Labels = mixedMoment B raw19851step1 raw19851step1Labels := by
      have ha : raw19851step1 = (fun i j => raw19851step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19851step1 raw19851step0; decide +kernel
      have hl : raw19851step1Labels = raw19851step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19851step0 raw19851step0Labels permutation145 permutation2
    mixedMoment B raw19851step1 raw19851step1Labels = mixedMoment B raw19851step2 raw19851step2Labels := by
      have ha : raw19851step2 = -raw19851step1 := by apply Matrix.ext; change ∀ i j, raw19851step2 i j = -(raw19851step1 i j); unfold raw19851step2 raw19851step1; decide +kernel
      have hl : raw19851step2Labels = raw19851step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node785 node785Labels := by rfl

theorem canonical19852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19852 raw19852Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw19852 raw19852Labels = mixedMoment B raw19852step0 raw19852step0Labels := by
      have hz : ∀ j, raw19852 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19852step0 = (fun i j => raw19852 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19852step0 raw19852; decide +kernel
      have hl : raw19852step0Labels = raw19852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19852 raw19852Labels permutation265 hz
    mixedMoment B raw19852step0 raw19852step0Labels = mixedMoment B raw19852step1 raw19852step1Labels := by
      have ha : raw19852step1 = (fun i j => raw19852step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19852step1 raw19852step0; decide +kernel
      have hl : raw19852step1Labels = raw19852step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19852step0 raw19852step0Labels permutation145 permutation2
    mixedMoment B raw19852step1 raw19852step1Labels = mixedMoment B raw19852step2 raw19852step2Labels := by
      have ha : raw19852step2 = -raw19852step1 := by apply Matrix.ext; change ∀ i j, raw19852step2 i j = -(raw19852step1 i j); unfold raw19852step2 raw19852step1; decide +kernel
      have hl : raw19852step2Labels = raw19852step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node785 node785Labels := by rfl

theorem canonical19853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19853 raw19853Labels = mixedMoment B node812 node812Labels := by
  calc
    mixedMoment B raw19853 raw19853Labels = mixedMoment B raw19853step0 raw19853step0Labels := by
      have hz : ∀ j, raw19853 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19853step0 = (fun i j => raw19853 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19853step0 raw19853; decide +kernel
      have hl : raw19853step0Labels = raw19853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19853 raw19853Labels permutation346 hz
    mixedMoment B raw19853step0 raw19853step0Labels = mixedMoment B raw19853step1 raw19853step1Labels := by
      have hz : ∀ j, raw19853step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19853step1 = (fun i j => raw19853step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19853step1 raw19853step0; decide +kernel
      have hl : raw19853step1Labels = raw19853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19853step0 raw19853step0Labels permutation56 hz
    mixedMoment B raw19853step1 raw19853step1Labels = mixedMoment B raw19853step2 raw19853step2Labels := by
      have ha : raw19853step2 = (fun i j => raw19853step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19853step2 raw19853step1; decide +kernel
      have hl : raw19853step2Labels = raw19853step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19853step1 raw19853step1Labels permutation31 permutation2
    mixedMoment B raw19853step2 raw19853step2Labels = mixedMoment B raw19853step3 raw19853step3Labels := by
      have ha : raw19853step3 = -raw19853step2 := by apply Matrix.ext; change ∀ i j, raw19853step3 i j = -(raw19853step2 i j); unfold raw19853step3 raw19853step2; decide +kernel
      have hl : raw19853step3Labels = raw19853step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node812 node812Labels := by rfl

theorem canonical19854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19854 raw19854Labels = mixedMoment B node812 node812Labels := by
  calc
    mixedMoment B raw19854 raw19854Labels = mixedMoment B raw19854step0 raw19854step0Labels := by
      have hz : ∀ j, raw19854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19854step0 = (fun i j => raw19854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19854step0 raw19854; decide +kernel
      have hl : raw19854step0Labels = raw19854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19854 raw19854Labels permutation346 hz
    mixedMoment B raw19854step0 raw19854step0Labels = mixedMoment B raw19854step1 raw19854step1Labels := by
      have hz : ∀ j, raw19854step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19854step1 = (fun i j => raw19854step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19854step1 raw19854step0; decide +kernel
      have hl : raw19854step1Labels = raw19854step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19854step0 raw19854step0Labels permutation56 hz
    mixedMoment B raw19854step1 raw19854step1Labels = mixedMoment B raw19854step2 raw19854step2Labels := by
      have ha : raw19854step2 = (fun i j => raw19854step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19854step2 raw19854step1; decide +kernel
      have hl : raw19854step2Labels = raw19854step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19854step1 raw19854step1Labels permutation29 permutation2
    mixedMoment B raw19854step2 raw19854step2Labels = mixedMoment B raw19854step3 raw19854step3Labels := by
      have ha : raw19854step3 = -raw19854step2 := by apply Matrix.ext; change ∀ i j, raw19854step3 i j = -(raw19854step2 i j); unfold raw19854step3 raw19854step2; decide +kernel
      have hl : raw19854step3Labels = raw19854step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node812 node812Labels := by rfl

theorem canonical19855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19855 raw19855Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw19855 raw19855Labels = mixedMoment B raw19855step0 raw19855step0Labels := by
      have hz : ∀ j, raw19855 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19855step0 = (fun i j => raw19855 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19855step0 raw19855; decide +kernel
      have hl : raw19855step0Labels = raw19855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19855 raw19855Labels permutation346 hz
    mixedMoment B raw19855step0 raw19855step0Labels = mixedMoment B raw19855step1 raw19855step1Labels := by
      have hz : ∀ j, raw19855step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19855step1 = (fun i j => raw19855step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19855step1 raw19855step0; decide +kernel
      have hl : raw19855step1Labels = raw19855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19855step0 raw19855step0Labels permutation56 hz
    mixedMoment B raw19855step1 raw19855step1Labels = mixedMoment B raw19855step2 raw19855step2Labels := by
      have ha : raw19855step2 = (fun i j => raw19855step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19855step2 raw19855step1; decide +kernel
      have hl : raw19855step2Labels = raw19855step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19855step1 raw19855step1Labels permutation29 permutation2
    mixedMoment B raw19855step2 raw19855step2Labels = mixedMoment B raw19855step3 raw19855step3Labels := by
      have ha : raw19855step3 = -raw19855step2 := by apply Matrix.ext; change ∀ i j, raw19855step3 i j = -(raw19855step2 i j); unfold raw19855step3 raw19855step2; decide +kernel
      have hl : raw19855step3Labels = raw19855step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical19856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19856 raw19856Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw19856 raw19856Labels = mixedMoment B raw19856step0 raw19856step0Labels := by
      have hz : ∀ j, raw19856 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19856step0 = (fun i j => raw19856 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19856step0 raw19856; decide +kernel
      have hl : raw19856step0Labels = raw19856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19856 raw19856Labels permutation346 hz
    mixedMoment B raw19856step0 raw19856step0Labels = mixedMoment B raw19856step1 raw19856step1Labels := by
      have hz : ∀ j, raw19856step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19856step1 = (fun i j => raw19856step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19856step1 raw19856step0; decide +kernel
      have hl : raw19856step1Labels = raw19856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19856step0 raw19856step0Labels permutation56 hz
    mixedMoment B raw19856step1 raw19856step1Labels = mixedMoment B raw19856step2 raw19856step2Labels := by
      have ha : raw19856step2 = (fun i j => raw19856step1 (permutation29 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19856step2 raw19856step1; decide +kernel
      have hl : raw19856step2Labels = raw19856step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19856step1 raw19856step1Labels permutation29 permutation0
    mixedMoment B raw19856step2 raw19856step2Labels = mixedMoment B raw19856step3 raw19856step3Labels := by
      have ha : raw19856step3 = -raw19856step2 := by apply Matrix.ext; change ∀ i j, raw19856step3 i j = -(raw19856step2 i j); unfold raw19856step3 raw19856step2; decide +kernel
      have hl : raw19856step3Labels = raw19856step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical19857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19857 raw19857Labels = mixedMoment B node705 node705Labels := by
  calc
    mixedMoment B raw19857 raw19857Labels = mixedMoment B raw19857step0 raw19857step0Labels := by
      have hz : ∀ j, raw19857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19857step0 = (fun i j => raw19857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19857step0 raw19857; decide +kernel
      have hl : raw19857step0Labels = raw19857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19857 raw19857Labels permutation346 hz
    mixedMoment B raw19857step0 raw19857step0Labels = mixedMoment B raw19857step1 raw19857step1Labels := by
      have ha : raw19857step1 = (fun i j => raw19857step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19857step1 raw19857step0; decide +kernel
      have hl : raw19857step1Labels = raw19857step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19857step0 raw19857step0Labels permutation139 permutation2
    mixedMoment B raw19857step1 raw19857step1Labels = mixedMoment B raw19857step2 raw19857step2Labels := by
      have ha : raw19857step2 = -raw19857step1 := by apply Matrix.ext; change ∀ i j, raw19857step2 i j = -(raw19857step1 i j); unfold raw19857step2 raw19857step1; decide +kernel
      have hl : raw19857step2Labels = raw19857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node705 node705Labels := by rfl

theorem canonical19858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19858 raw19858Labels = mixedMoment B node705 node705Labels := by
  calc
    mixedMoment B raw19858 raw19858Labels = mixedMoment B raw19858step0 raw19858step0Labels := by
      have hz : ∀ j, raw19858 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19858step0 = (fun i j => raw19858 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19858step0 raw19858; decide +kernel
      have hl : raw19858step0Labels = raw19858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19858 raw19858Labels permutation265 hz
    mixedMoment B raw19858step0 raw19858step0Labels = mixedMoment B raw19858step1 raw19858step1Labels := by
      have ha : raw19858step1 = (fun i j => raw19858step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19858step1 raw19858step0; decide +kernel
      have hl : raw19858step1Labels = raw19858step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19858step0 raw19858step0Labels permutation139 permutation2
    mixedMoment B raw19858step1 raw19858step1Labels = mixedMoment B raw19858step2 raw19858step2Labels := by
      have ha : raw19858step2 = -raw19858step1 := by apply Matrix.ext; change ∀ i j, raw19858step2 i j = -(raw19858step1 i j); unfold raw19858step2 raw19858step1; decide +kernel
      have hl : raw19858step2Labels = raw19858step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node705 node705Labels := by rfl

theorem canonical19859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19859 raw19859Labels = mixedMoment B node740 node740Labels := by
  calc
    mixedMoment B raw19859 raw19859Labels = mixedMoment B raw19859step0 raw19859step0Labels := by
      have hz : ∀ j, raw19859 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19859step0 = (fun i j => raw19859 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19859step0 raw19859; decide +kernel
      have hl : raw19859step0Labels = raw19859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19859 raw19859Labels permutation346 hz
    mixedMoment B raw19859step0 raw19859step0Labels = mixedMoment B raw19859step1 raw19859step1Labels := by
      have hz : ∀ j, raw19859step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19859step1 = (fun i j => raw19859step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19859step1 raw19859step0; decide +kernel
      have hl : raw19859step1Labels = raw19859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19859step0 raw19859step0Labels permutation56 hz
    mixedMoment B raw19859step1 raw19859step1Labels = mixedMoment B raw19859step2 raw19859step2Labels := by
      have ha : raw19859step2 = (fun i j => raw19859step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19859step2 raw19859step1; decide +kernel
      have hl : raw19859step2Labels = raw19859step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19859step1 raw19859step1Labels permutation31 permutation2
    mixedMoment B raw19859step2 raw19859step2Labels = mixedMoment B raw19859step3 raw19859step3Labels := by
      have ha : raw19859step3 = -raw19859step2 := by apply Matrix.ext; change ∀ i j, raw19859step3 i j = -(raw19859step2 i j); unfold raw19859step3 raw19859step2; decide +kernel
      have hl : raw19859step3Labels = raw19859step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node740 node740Labels := by rfl

theorem canonical19860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19860 raw19860Labels = mixedMoment B node545 node545Labels := by
  calc
    mixedMoment B raw19860 raw19860Labels = mixedMoment B raw19860step0 raw19860step0Labels := by
      have hz : ∀ j, raw19860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19860step0 = (fun i j => raw19860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19860step0 raw19860; decide +kernel
      have hl : raw19860step0Labels = raw19860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19860 raw19860Labels permutation346 hz
    mixedMoment B raw19860step0 raw19860step0Labels = mixedMoment B raw19860step1 raw19860step1Labels := by
      have hz : ∀ j, raw19860step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19860step1 = (fun i j => raw19860step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19860step1 raw19860step0; decide +kernel
      have hl : raw19860step1Labels = raw19860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19860step0 raw19860step0Labels permutation56 hz
    mixedMoment B raw19860step1 raw19860step1Labels = mixedMoment B raw19860step2 raw19860step2Labels := by
      have ha : raw19860step2 = (fun i j => raw19860step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19860step2 raw19860step1; decide +kernel
      have hl : raw19860step2Labels = raw19860step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19860step1 raw19860step1Labels permutation31 permutation2
    mixedMoment B raw19860step2 raw19860step2Labels = mixedMoment B raw19860step3 raw19860step3Labels := by
      have ha : raw19860step3 = -raw19860step2 := by apply Matrix.ext; change ∀ i j, raw19860step3 i j = -(raw19860step2 i j); unfold raw19860step3 raw19860step2; decide +kernel
      have hl : raw19860step3Labels = raw19860step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node545 node545Labels := by rfl

theorem canonical19861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19861 raw19861Labels = mixedMoment B node1199 node1199Labels := by
  calc
    mixedMoment B raw19861 raw19861Labels = mixedMoment B raw19861step0 raw19861step0Labels := by
      have hz : ∀ j, raw19861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19861step0 = (fun i j => raw19861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19861step0 raw19861; decide +kernel
      have hl : raw19861step0Labels = raw19861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19861 raw19861Labels permutation346 hz
    mixedMoment B raw19861step0 raw19861step0Labels = mixedMoment B raw19861step1 raw19861step1Labels := by
      have ha : raw19861step1 = (fun i j => raw19861step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19861step1 raw19861step0; decide +kernel
      have hl : raw19861step1Labels = raw19861step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19861step0 raw19861step0Labels permutation40 permutation2
    _ = mixedMoment B node1199 node1199Labels := by rfl

theorem canonical19862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19862 raw19862Labels = mixedMoment B node1199 node1199Labels := by
  calc
    mixedMoment B raw19862 raw19862Labels = mixedMoment B raw19862step0 raw19862step0Labels := by
      have hz : ∀ j, raw19862 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19862step0 = (fun i j => raw19862 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19862step0 raw19862; decide +kernel
      have hl : raw19862step0Labels = raw19862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19862 raw19862Labels permutation265 hz
    mixedMoment B raw19862step0 raw19862step0Labels = mixedMoment B raw19862step1 raw19862step1Labels := by
      have ha : raw19862step1 = (fun i j => raw19862step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19862step1 raw19862step0; decide +kernel
      have hl : raw19862step1Labels = raw19862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19862step0 raw19862step0Labels permutation40 permutation2
    _ = mixedMoment B node1199 node1199Labels := by rfl

theorem canonical19863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19863 raw19863Labels = mixedMoment B node1231 node1231Labels := by
  calc
    mixedMoment B raw19863 raw19863Labels = mixedMoment B raw19863step0 raw19863step0Labels := by
      have hz : ∀ j, raw19863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19863step0 = (fun i j => raw19863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19863step0 raw19863; decide +kernel
      have hl : raw19863step0Labels = raw19863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19863 raw19863Labels permutation346 hz
    mixedMoment B raw19863step0 raw19863step0Labels = mixedMoment B raw19863step1 raw19863step1Labels := by
      have hz : ∀ j, raw19863step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19863step1 = (fun i j => raw19863step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19863step1 raw19863step0; decide +kernel
      have hl : raw19863step1Labels = raw19863step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19863step0 raw19863step0Labels permutation56 hz
    mixedMoment B raw19863step1 raw19863step1Labels = mixedMoment B raw19863step2 raw19863step2Labels := by
      have ha : raw19863step2 = (fun i j => raw19863step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19863step2 raw19863step1; decide +kernel
      have hl : raw19863step2Labels = raw19863step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19863step1 raw19863step1Labels permutation10 permutation2
    _ = mixedMoment B node1231 node1231Labels := by rfl

theorem canonical19864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19864 raw19864Labels = mixedMoment B node1231 node1231Labels := by
  calc
    mixedMoment B raw19864 raw19864Labels = mixedMoment B raw19864step0 raw19864step0Labels := by
      have hz : ∀ j, raw19864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19864step0 = (fun i j => raw19864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19864step0 raw19864; decide +kernel
      have hl : raw19864step0Labels = raw19864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19864 raw19864Labels permutation346 hz
    mixedMoment B raw19864step0 raw19864step0Labels = mixedMoment B raw19864step1 raw19864step1Labels := by
      have hz : ∀ j, raw19864step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19864step1 = (fun i j => raw19864step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19864step1 raw19864step0; decide +kernel
      have hl : raw19864step1Labels = raw19864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19864step0 raw19864step0Labels permutation56 hz
    _ = mixedMoment B node1231 node1231Labels := by rfl

theorem canonical19870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19870 raw19870Labels = mixedMoment B node986 node986Labels := by
  calc
    mixedMoment B raw19870 raw19870Labels = mixedMoment B raw19870step0 raw19870step0Labels := by
      have hz : ∀ j, raw19870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19870step0 = (fun i j => raw19870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19870step0 raw19870; decide +kernel
      have hl : raw19870step0Labels = raw19870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19870 raw19870Labels permutation434 hz
    mixedMoment B raw19870step0 raw19870step0Labels = mixedMoment B raw19870step1 raw19870step1Labels := by
      have hz : ∀ j, raw19870step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19870step1 = (fun i j => raw19870step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19870step1 raw19870step0; decide +kernel
      have hl : raw19870step1Labels = raw19870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19870step0 raw19870step0Labels permutation80 hz
    mixedMoment B raw19870step1 raw19870step1Labels = mixedMoment B raw19870step2 raw19870step2Labels := by
      have ha : raw19870step2 = (fun i j => raw19870step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19870step2 raw19870step1; decide +kernel
      have hl : raw19870step2Labels = raw19870step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19870step1 raw19870step1Labels permutation10 permutation2
    _ = mixedMoment B node986 node986Labels := by rfl

theorem canonical19871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19871 raw19871Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw19871 raw19871Labels = mixedMoment B raw19871step0 raw19871step0Labels := by
      have hz : ∀ j, raw19871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19871step0 = (fun i j => raw19871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19871step0 raw19871; decide +kernel
      have hl : raw19871step0Labels = raw19871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19871 raw19871Labels permutation434 hz
    mixedMoment B raw19871step0 raw19871step0Labels = mixedMoment B raw19871step1 raw19871step1Labels := by
      have hz : ∀ j, raw19871step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19871step1 = (fun i j => raw19871step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19871step1 raw19871step0; decide +kernel
      have hl : raw19871step1Labels = raw19871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19871step0 raw19871step0Labels permutation80 hz
    mixedMoment B raw19871step1 raw19871step1Labels = mixedMoment B raw19871step2 raw19871step2Labels := by
      have ha : raw19871step2 = (fun i j => raw19871step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19871step2 raw19871step1; decide +kernel
      have hl : raw19871step2Labels = raw19871step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19871step1 raw19871step1Labels permutation31 permutation2
    mixedMoment B raw19871step2 raw19871step2Labels = mixedMoment B raw19871step3 raw19871step3Labels := by
      have ha : raw19871step3 = -raw19871step2 := by apply Matrix.ext; change ∀ i j, raw19871step3 i j = -(raw19871step2 i j); unfold raw19871step3 raw19871step2; decide +kernel
      have hl : raw19871step3Labels = raw19871step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1037 node1037Labels := by rfl

theorem canonical19872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19872 raw19872Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw19872 raw19872Labels = mixedMoment B raw19872step0 raw19872step0Labels := by
      have hz : ∀ j, raw19872 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19872step0 = (fun i j => raw19872 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19872step0 raw19872; decide +kernel
      have hl : raw19872step0Labels = raw19872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19872 raw19872Labels permutation434 hz
    mixedMoment B raw19872step0 raw19872step0Labels = mixedMoment B raw19872step1 raw19872step1Labels := by
      have ha : raw19872step1 = (fun i j => raw19872step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19872step1 raw19872step0; decide +kernel
      have hl : raw19872step1Labels = raw19872step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19872step0 raw19872step0Labels permutation139 permutation2
    mixedMoment B raw19872step1 raw19872step1Labels = mixedMoment B raw19872step2 raw19872step2Labels := by
      have ha : raw19872step2 = -raw19872step1 := by apply Matrix.ext; change ∀ i j, raw19872step2 i j = -(raw19872step1 i j); unfold raw19872step2 raw19872step1; decide +kernel
      have hl : raw19872step2Labels = raw19872step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node979 node979Labels := by rfl

theorem canonical19873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19873 raw19873Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw19873 raw19873Labels = mixedMoment B raw19873step0 raw19873step0Labels := by
      have hz : ∀ j, raw19873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19873step0 = (fun i j => raw19873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19873step0 raw19873; decide +kernel
      have hl : raw19873step0Labels = raw19873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19873 raw19873Labels permutation346 hz
    mixedMoment B raw19873step0 raw19873step0Labels = mixedMoment B raw19873step1 raw19873step1Labels := by
      have ha : raw19873step1 = (fun i j => raw19873step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19873step1 raw19873step0; decide +kernel
      have hl : raw19873step1Labels = raw19873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19873step0 raw19873step0Labels permutation139 permutation2
    mixedMoment B raw19873step1 raw19873step1Labels = mixedMoment B raw19873step2 raw19873step2Labels := by
      have ha : raw19873step2 = -raw19873step1 := by apply Matrix.ext; change ∀ i j, raw19873step2 i j = -(raw19873step1 i j); unfold raw19873step2 raw19873step1; decide +kernel
      have hl : raw19873step2Labels = raw19873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node979 node979Labels := by rfl

theorem canonical19874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19874 raw19874Labels = mixedMoment B node1007 node1007Labels := by
  calc
    mixedMoment B raw19874 raw19874Labels = mixedMoment B raw19874step0 raw19874step0Labels := by
      have hz : ∀ j, raw19874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19874step0 = (fun i j => raw19874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19874step0 raw19874; decide +kernel
      have hl : raw19874step0Labels = raw19874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19874 raw19874Labels permutation434 hz
    mixedMoment B raw19874step0 raw19874step0Labels = mixedMoment B raw19874step1 raw19874step1Labels := by
      have hz : ∀ j, raw19874step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19874step1 = (fun i j => raw19874step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19874step1 raw19874step0; decide +kernel
      have hl : raw19874step1Labels = raw19874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19874step0 raw19874step0Labels permutation80 hz
    mixedMoment B raw19874step1 raw19874step1Labels = mixedMoment B raw19874step2 raw19874step2Labels := by
      have ha : raw19874step2 = (fun i j => raw19874step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19874step2 raw19874step1; decide +kernel
      have hl : raw19874step2Labels = raw19874step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19874step1 raw19874step1Labels permutation29 permutation2
    mixedMoment B raw19874step2 raw19874step2Labels = mixedMoment B raw19874step3 raw19874step3Labels := by
      have ha : raw19874step3 = -raw19874step2 := by apply Matrix.ext; change ∀ i j, raw19874step3 i j = -(raw19874step2 i j); unfold raw19874step3 raw19874step2; decide +kernel
      have hl : raw19874step3Labels = raw19874step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1007 node1007Labels := by rfl

theorem canonical19875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19875 raw19875Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw19875 raw19875Labels = mixedMoment B raw19875step0 raw19875step0Labels := by
      have hz : ∀ j, raw19875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19875step0 = (fun i j => raw19875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19875step0 raw19875; decide +kernel
      have hl : raw19875step0Labels = raw19875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19875 raw19875Labels permutation434 hz
    mixedMoment B raw19875step0 raw19875step0Labels = mixedMoment B raw19875step1 raw19875step1Labels := by
      have hz : ∀ j, raw19875step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19875step1 = (fun i j => raw19875step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19875step1 raw19875step0; decide +kernel
      have hl : raw19875step1Labels = raw19875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19875step0 raw19875step0Labels permutation80 hz
    mixedMoment B raw19875step1 raw19875step1Labels = mixedMoment B raw19875step2 raw19875step2Labels := by
      have ha : raw19875step2 = (fun i j => raw19875step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19875step2 raw19875step1; decide +kernel
      have hl : raw19875step2Labels = raw19875step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19875step1 raw19875step1Labels permutation10 permutation2
    _ = mixedMoment B node2208 node2208Labels := by rfl

theorem canonical19876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19876 raw19876Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw19876 raw19876Labels = mixedMoment B raw19876step0 raw19876step0Labels := by
      have hz : ∀ j, raw19876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19876step0 = (fun i j => raw19876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19876step0 raw19876; decide +kernel
      have hl : raw19876step0Labels = raw19876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19876 raw19876Labels permutation434 hz
    mixedMoment B raw19876step0 raw19876step0Labels = mixedMoment B raw19876step1 raw19876step1Labels := by
      have hz : ∀ j, raw19876step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19876step1 = (fun i j => raw19876step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19876step1 raw19876step0; decide +kernel
      have hl : raw19876step1Labels = raw19876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19876step0 raw19876step0Labels permutation80 hz
    mixedMoment B raw19876step1 raw19876step1Labels = mixedMoment B raw19876step2 raw19876step2Labels := by
      have ha : raw19876step2 = (fun i j => raw19876step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19876step2 raw19876step1; decide +kernel
      have hl : raw19876step2Labels = raw19876step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19876step1 raw19876step1Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

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

theorem canonical19918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19918 raw19918Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19918 raw19918Labels = mixedMoment B raw19918step0 raw19918step0Labels := by
      have hz : ∀ j, raw19918 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19918step0 = (fun i j => raw19918 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19918step0 raw19918; decide +kernel
      have hl : raw19918step0Labels = raw19918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19918 raw19918Labels permutation520 hz
    mixedMoment B raw19918step0 raw19918step0Labels = mixedMoment B raw19918step1 raw19918step1Labels := by
      have hz : ∀ j, raw19918step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19918step1 = (fun i j => raw19918step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19918step1 raw19918step0; decide +kernel
      have hl : raw19918step1Labels = raw19918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19918step0 raw19918step0Labels permutation104 hz
    mixedMoment B raw19918step1 raw19918step1Labels = mixedMoment B raw19918step2 raw19918step2Labels := by
      have hz : ∀ j, raw19918step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19918step2 = (fun i j => raw19918step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19918step2 raw19918step1; decide +kernel
      have hl : raw19918step2Labels = raw19918step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19918step1 raw19918step1Labels permutation14 hz
    mixedMoment B raw19918step2 raw19918step2Labels = mixedMoment B raw19918step3 raw19918step3Labels := by
      have ha : raw19918step3 = (fun i j => raw19918step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19918step3 raw19918step2; decide +kernel
      have hl : raw19918step3Labels = raw19918step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19918step2 raw19918step2Labels permutation7 permutation7
    mixedMoment B raw19918step3 raw19918step3Labels = mixedMoment B raw19918step4 raw19918step4Labels := by
      have ha : raw19918step4 = raw19918step3 := by apply Matrix.ext; unfold raw19918step4 raw19918step3; decide +kernel
      have hl : raw19918step3Labels = labelEmbedding1 ∘ raw19918step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19918step3 raw19918step3Labels raw19918step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

theorem canonical19919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19919 raw19919Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19919 raw19919Labels = mixedMoment B raw19919step0 raw19919step0Labels := by
      have hz : ∀ j, raw19919 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19919step0 = (fun i j => raw19919 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19919step0 raw19919; decide +kernel
      have hl : raw19919step0Labels = raw19919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19919 raw19919Labels permutation520 hz
    mixedMoment B raw19919step0 raw19919step0Labels = mixedMoment B raw19919step1 raw19919step1Labels := by
      have hz : ∀ j, raw19919step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19919step1 = (fun i j => raw19919step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19919step1 raw19919step0; decide +kernel
      have hl : raw19919step1Labels = raw19919step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19919step0 raw19919step0Labels permutation80 hz
    mixedMoment B raw19919step1 raw19919step1Labels = mixedMoment B raw19919step2 raw19919step2Labels := by
      have hz : ∀ j, raw19919step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19919step2 = (fun i j => raw19919step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19919step2 raw19919step1; decide +kernel
      have hl : raw19919step2Labels = raw19919step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19919step1 raw19919step1Labels permutation14 hz
    mixedMoment B raw19919step2 raw19919step2Labels = mixedMoment B raw19919step3 raw19919step3Labels := by
      have ha : raw19919step3 = (fun i j => raw19919step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19919step3 raw19919step2; decide +kernel
      have hl : raw19919step3Labels = raw19919step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19919step2 raw19919step2Labels permutation7 permutation7
    mixedMoment B raw19919step3 raw19919step3Labels = mixedMoment B raw19919step4 raw19919step4Labels := by
      have ha : raw19919step4 = raw19919step3 := by apply Matrix.ext; unfold raw19919step4 raw19919step3; decide +kernel
      have hl : raw19919step3Labels = labelEmbedding1 ∘ raw19919step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19919step3 raw19919step3Labels raw19919step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

theorem canonical19920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19920 raw19920Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19920 raw19920Labels = mixedMoment B raw19920step0 raw19920step0Labels := by
      have hz : ∀ j, raw19920 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19920step0 = (fun i j => raw19920 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19920step0 raw19920; decide +kernel
      have hl : raw19920step0Labels = raw19920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19920 raw19920Labels permutation434 hz
    mixedMoment B raw19920step0 raw19920step0Labels = mixedMoment B raw19920step1 raw19920step1Labels := by
      have hz : ∀ j, raw19920step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19920step1 = (fun i j => raw19920step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19920step1 raw19920step0; decide +kernel
      have hl : raw19920step1Labels = raw19920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19920step0 raw19920step0Labels permutation80 hz
    mixedMoment B raw19920step1 raw19920step1Labels = mixedMoment B raw19920step2 raw19920step2Labels := by
      have hz : ∀ j, raw19920step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19920step2 = (fun i j => raw19920step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19920step2 raw19920step1; decide +kernel
      have hl : raw19920step2Labels = raw19920step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19920step1 raw19920step1Labels permutation14 hz
    mixedMoment B raw19920step2 raw19920step2Labels = mixedMoment B raw19920step3 raw19920step3Labels := by
      have ha : raw19920step3 = (fun i j => raw19920step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19920step3 raw19920step2; decide +kernel
      have hl : raw19920step3Labels = raw19920step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19920step2 raw19920step2Labels permutation7 permutation7
    mixedMoment B raw19920step3 raw19920step3Labels = mixedMoment B raw19920step4 raw19920step4Labels := by
      have ha : raw19920step4 = raw19920step3 := by apply Matrix.ext; unfold raw19920step4 raw19920step3; decide +kernel
      have hl : raw19920step3Labels = labelEmbedding1 ∘ raw19920step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19920step3 raw19920step3Labels raw19920step4Labels labelEmbedding1 hl
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

theorem canonical19922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19922 raw19922Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19922 raw19922Labels = mixedMoment B raw19922step0 raw19922step0Labels := by
      have hz : ∀ j, raw19922 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19922step0 = (fun i j => raw19922 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19922step0 raw19922; decide +kernel
      have hl : raw19922step0Labels = raw19922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19922 raw19922Labels permutation520 hz
    mixedMoment B raw19922step0 raw19922step0Labels = mixedMoment B raw19922step1 raw19922step1Labels := by
      have hz : ∀ j, raw19922step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19922step1 = (fun i j => raw19922step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19922step1 raw19922step0; decide +kernel
      have hl : raw19922step1Labels = raw19922step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19922step0 raw19922step0Labels permutation104 hz
    mixedMoment B raw19922step1 raw19922step1Labels = mixedMoment B raw19922step2 raw19922step2Labels := by
      have hz : ∀ j, raw19922step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19922step2 = (fun i j => raw19922step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19922step2 raw19922step1; decide +kernel
      have hl : raw19922step2Labels = raw19922step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19922step1 raw19922step1Labels permutation20 hz
    mixedMoment B raw19922step2 raw19922step2Labels = mixedMoment B raw19922step3 raw19922step3Labels := by
      have ha : raw19922step3 = (fun i j => raw19922step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19922step3 raw19922step2; decide +kernel
      have hl : raw19922step3Labels = raw19922step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19922step2 raw19922step2Labels permutation2 permutation7
    mixedMoment B raw19922step3 raw19922step3Labels = mixedMoment B raw19922step4 raw19922step4Labels := by
      have ha : raw19922step4 = -raw19922step3 := by apply Matrix.ext; change ∀ i j, raw19922step4 i j = -(raw19922step3 i j); unfold raw19922step4 raw19922step3; decide +kernel
      have hl : raw19922step4Labels = raw19922step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19922step4 raw19922step4Labels = mixedMoment B raw19922step5 raw19922step5Labels := by
      have ha : raw19922step5 = raw19922step4 := by apply Matrix.ext; unfold raw19922step5 raw19922step4; decide +kernel
      have hl : raw19922step4Labels = labelEmbedding1 ∘ raw19922step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19922step4 raw19922step4Labels raw19922step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

theorem canonical19923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19923 raw19923Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19923 raw19923Labels = mixedMoment B raw19923step0 raw19923step0Labels := by
      have hz : ∀ j, raw19923 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19923step0 = (fun i j => raw19923 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19923step0 raw19923; decide +kernel
      have hl : raw19923step0Labels = raw19923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19923 raw19923Labels permutation520 hz
    mixedMoment B raw19923step0 raw19923step0Labels = mixedMoment B raw19923step1 raw19923step1Labels := by
      have hz : ∀ j, raw19923step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19923step1 = (fun i j => raw19923step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19923step1 raw19923step0; decide +kernel
      have hl : raw19923step1Labels = raw19923step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19923step0 raw19923step0Labels permutation104 hz
    mixedMoment B raw19923step1 raw19923step1Labels = mixedMoment B raw19923step2 raw19923step2Labels := by
      have ha : raw19923step2 = (fun i j => raw19923step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19923step2 raw19923step1; decide +kernel
      have hl : raw19923step2Labels = raw19923step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19923step1 raw19923step1Labels permutation29 permutation7
    mixedMoment B raw19923step2 raw19923step2Labels = mixedMoment B raw19923step3 raw19923step3Labels := by
      have ha : raw19923step3 = raw19923step2 := by apply Matrix.ext; unfold raw19923step3 raw19923step2; decide +kernel
      have hl : raw19923step2Labels = labelEmbedding1 ∘ raw19923step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19923step2 raw19923step2Labels raw19923step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19924 raw19924Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19924 raw19924Labels = mixedMoment B raw19924step0 raw19924step0Labels := by
      have hz : ∀ j, raw19924 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19924step0 = (fun i j => raw19924 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19924step0 raw19924; decide +kernel
      have hl : raw19924step0Labels = raw19924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19924 raw19924Labels permutation520 hz
    mixedMoment B raw19924step0 raw19924step0Labels = mixedMoment B raw19924step1 raw19924step1Labels := by
      have hz : ∀ j, raw19924step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19924step1 = (fun i j => raw19924step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19924step1 raw19924step0; decide +kernel
      have hl : raw19924step1Labels = raw19924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19924step0 raw19924step0Labels permutation80 hz
    mixedMoment B raw19924step1 raw19924step1Labels = mixedMoment B raw19924step2 raw19924step2Labels := by
      have ha : raw19924step2 = (fun i j => raw19924step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19924step2 raw19924step1; decide +kernel
      have hl : raw19924step2Labels = raw19924step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19924step1 raw19924step1Labels permutation29 permutation7
    mixedMoment B raw19924step2 raw19924step2Labels = mixedMoment B raw19924step3 raw19924step3Labels := by
      have ha : raw19924step3 = raw19924step2 := by apply Matrix.ext; unfold raw19924step3 raw19924step2; decide +kernel
      have hl : raw19924step2Labels = labelEmbedding1 ∘ raw19924step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19924step2 raw19924step2Labels raw19924step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19925 raw19925Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19925 raw19925Labels = mixedMoment B raw19925step0 raw19925step0Labels := by
      have hz : ∀ j, raw19925 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19925step0 = (fun i j => raw19925 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19925step0 raw19925; decide +kernel
      have hl : raw19925step0Labels = raw19925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19925 raw19925Labels permutation434 hz
    mixedMoment B raw19925step0 raw19925step0Labels = mixedMoment B raw19925step1 raw19925step1Labels := by
      have hz : ∀ j, raw19925step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19925step1 = (fun i j => raw19925step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19925step1 raw19925step0; decide +kernel
      have hl : raw19925step1Labels = raw19925step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19925step0 raw19925step0Labels permutation80 hz
    mixedMoment B raw19925step1 raw19925step1Labels = mixedMoment B raw19925step2 raw19925step2Labels := by
      have ha : raw19925step2 = (fun i j => raw19925step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19925step2 raw19925step1; decide +kernel
      have hl : raw19925step2Labels = raw19925step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19925step1 raw19925step1Labels permutation29 permutation7
    mixedMoment B raw19925step2 raw19925step2Labels = mixedMoment B raw19925step3 raw19925step3Labels := by
      have ha : raw19925step3 = raw19925step2 := by apply Matrix.ext; unfold raw19925step3 raw19925step2; decide +kernel
      have hl : raw19925step2Labels = labelEmbedding1 ∘ raw19925step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19925step2 raw19925step2Labels raw19925step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19926 raw19926Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19926 raw19926Labels = mixedMoment B raw19926step0 raw19926step0Labels := by
      have hz : ∀ j, raw19926 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19926step0 = (fun i j => raw19926 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19926step0 raw19926; decide +kernel
      have hl : raw19926step0Labels = raw19926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19926 raw19926Labels permutation520 hz
    mixedMoment B raw19926step0 raw19926step0Labels = mixedMoment B raw19926step1 raw19926step1Labels := by
      have hz : ∀ j, raw19926step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19926step1 = (fun i j => raw19926step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19926step1 raw19926step0; decide +kernel
      have hl : raw19926step1Labels = raw19926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19926step0 raw19926step0Labels permutation104 hz
    mixedMoment B raw19926step1 raw19926step1Labels = mixedMoment B raw19926step2 raw19926step2Labels := by
      have hz : ∀ j, raw19926step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19926step2 = (fun i j => raw19926step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19926step2 raw19926step1; decide +kernel
      have hl : raw19926step2Labels = raw19926step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19926step1 raw19926step1Labels permutation20 hz
    mixedMoment B raw19926step2 raw19926step2Labels = mixedMoment B raw19926step3 raw19926step3Labels := by
      have ha : raw19926step3 = (fun i j => raw19926step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19926step3 raw19926step2; decide +kernel
      have hl : raw19926step3Labels = raw19926step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19926step2 raw19926step2Labels permutation2 permutation7
    mixedMoment B raw19926step3 raw19926step3Labels = mixedMoment B raw19926step4 raw19926step4Labels := by
      have ha : raw19926step4 = -raw19926step3 := by apply Matrix.ext; change ∀ i j, raw19926step4 i j = -(raw19926step3 i j); unfold raw19926step4 raw19926step3; decide +kernel
      have hl : raw19926step4Labels = raw19926step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19926step4 raw19926step4Labels = mixedMoment B raw19926step5 raw19926step5Labels := by
      have ha : raw19926step5 = raw19926step4 := by apply Matrix.ext; unfold raw19926step5 raw19926step4; decide +kernel
      have hl : raw19926step4Labels = labelEmbedding1 ∘ raw19926step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19926step4 raw19926step4Labels raw19926step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

theorem canonical19927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19927 raw19927Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19927 raw19927Labels = mixedMoment B raw19927step0 raw19927step0Labels := by
      have hz : ∀ j, raw19927 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19927step0 = (fun i j => raw19927 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19927step0 raw19927; decide +kernel
      have hl : raw19927step0Labels = raw19927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19927 raw19927Labels permutation520 hz
    mixedMoment B raw19927step0 raw19927step0Labels = mixedMoment B raw19927step1 raw19927step1Labels := by
      have hz : ∀ j, raw19927step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19927step1 = (fun i j => raw19927step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19927step1 raw19927step0; decide +kernel
      have hl : raw19927step1Labels = raw19927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19927step0 raw19927step0Labels permutation104 hz
    mixedMoment B raw19927step1 raw19927step1Labels = mixedMoment B raw19927step2 raw19927step2Labels := by
      have hz : ∀ j, raw19927step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19927step2 = (fun i j => raw19927step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19927step2 raw19927step1; decide +kernel
      have hl : raw19927step2Labels = raw19927step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19927step1 raw19927step1Labels permutation14 hz
    mixedMoment B raw19927step2 raw19927step2Labels = mixedMoment B raw19927step3 raw19927step3Labels := by
      have ha : raw19927step3 = (fun i j => raw19927step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19927step3 raw19927step2; decide +kernel
      have hl : raw19927step3Labels = raw19927step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19927step2 raw19927step2Labels permutation2 permutation7
    mixedMoment B raw19927step3 raw19927step3Labels = mixedMoment B raw19927step4 raw19927step4Labels := by
      have ha : raw19927step4 = -raw19927step3 := by apply Matrix.ext; change ∀ i j, raw19927step4 i j = -(raw19927step3 i j); unfold raw19927step4 raw19927step3; decide +kernel
      have hl : raw19927step4Labels = raw19927step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19927step4 raw19927step4Labels = mixedMoment B raw19927step5 raw19927step5Labels := by
      have ha : raw19927step5 = raw19927step4 := by apply Matrix.ext; unfold raw19927step5 raw19927step4; decide +kernel
      have hl : raw19927step4Labels = labelEmbedding1 ∘ raw19927step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19927step4 raw19927step4Labels raw19927step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

theorem canonical19928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19928 raw19928Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19928 raw19928Labels = mixedMoment B raw19928step0 raw19928step0Labels := by
      have hz : ∀ j, raw19928 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19928step0 = (fun i j => raw19928 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19928step0 raw19928; decide +kernel
      have hl : raw19928step0Labels = raw19928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19928 raw19928Labels permutation520 hz
    mixedMoment B raw19928step0 raw19928step0Labels = mixedMoment B raw19928step1 raw19928step1Labels := by
      have hz : ∀ j, raw19928step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19928step1 = (fun i j => raw19928step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19928step1 raw19928step0; decide +kernel
      have hl : raw19928step1Labels = raw19928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19928step0 raw19928step0Labels permutation104 hz
    mixedMoment B raw19928step1 raw19928step1Labels = mixedMoment B raw19928step2 raw19928step2Labels := by
      have ha : raw19928step2 = (fun i j => raw19928step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19928step2 raw19928step1; decide +kernel
      have hl : raw19928step2Labels = raw19928step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19928step1 raw19928step1Labels permutation31 permutation7
    mixedMoment B raw19928step2 raw19928step2Labels = mixedMoment B raw19928step3 raw19928step3Labels := by
      have ha : raw19928step3 = raw19928step2 := by apply Matrix.ext; unfold raw19928step3 raw19928step2; decide +kernel
      have hl : raw19928step2Labels = labelEmbedding1 ∘ raw19928step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19928step2 raw19928step2Labels raw19928step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19929 raw19929Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19929 raw19929Labels = mixedMoment B raw19929step0 raw19929step0Labels := by
      have hz : ∀ j, raw19929 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19929step0 = (fun i j => raw19929 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19929step0 raw19929; decide +kernel
      have hl : raw19929step0Labels = raw19929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19929 raw19929Labels permutation520 hz
    mixedMoment B raw19929step0 raw19929step0Labels = mixedMoment B raw19929step1 raw19929step1Labels := by
      have hz : ∀ j, raw19929step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19929step1 = (fun i j => raw19929step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19929step1 raw19929step0; decide +kernel
      have hl : raw19929step1Labels = raw19929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19929step0 raw19929step0Labels permutation56 hz
    mixedMoment B raw19929step1 raw19929step1Labels = mixedMoment B raw19929step2 raw19929step2Labels := by
      have ha : raw19929step2 = (fun i j => raw19929step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19929step2 raw19929step1; decide +kernel
      have hl : raw19929step2Labels = raw19929step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19929step1 raw19929step1Labels permutation29 permutation7
    mixedMoment B raw19929step2 raw19929step2Labels = mixedMoment B raw19929step3 raw19929step3Labels := by
      have ha : raw19929step3 = raw19929step2 := by apply Matrix.ext; unfold raw19929step3 raw19929step2; decide +kernel
      have hl : raw19929step2Labels = labelEmbedding1 ∘ raw19929step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19929step2 raw19929step2Labels raw19929step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19930 raw19930Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19930 raw19930Labels = mixedMoment B raw19930step0 raw19930step0Labels := by
      have hz : ∀ j, raw19930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19930step0 = (fun i j => raw19930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19930step0 raw19930; decide +kernel
      have hl : raw19930step0Labels = raw19930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19930 raw19930Labels permutation434 hz
    mixedMoment B raw19930step0 raw19930step0Labels = mixedMoment B raw19930step1 raw19930step1Labels := by
      have hz : ∀ j, raw19930step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19930step1 = (fun i j => raw19930step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19930step1 raw19930step0; decide +kernel
      have hl : raw19930step1Labels = raw19930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19930step0 raw19930step0Labels permutation56 hz
    mixedMoment B raw19930step1 raw19930step1Labels = mixedMoment B raw19930step2 raw19930step2Labels := by
      have ha : raw19930step2 = (fun i j => raw19930step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19930step2 raw19930step1; decide +kernel
      have hl : raw19930step2Labels = raw19930step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19930step1 raw19930step1Labels permutation29 permutation7
    mixedMoment B raw19930step2 raw19930step2Labels = mixedMoment B raw19930step3 raw19930step3Labels := by
      have ha : raw19930step3 = raw19930step2 := by apply Matrix.ext; unfold raw19930step3 raw19930step2; decide +kernel
      have hl : raw19930step2Labels = labelEmbedding1 ∘ raw19930step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19930step2 raw19930step2Labels raw19930step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19931 raw19931Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19931 raw19931Labels = mixedMoment B raw19931step0 raw19931step0Labels := by
      have hz : ∀ j, raw19931 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19931step0 = (fun i j => raw19931 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19931step0 raw19931; decide +kernel
      have hl : raw19931step0Labels = raw19931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19931 raw19931Labels permutation520 hz
    mixedMoment B raw19931step0 raw19931step0Labels = mixedMoment B raw19931step1 raw19931step1Labels := by
      have hz : ∀ j, raw19931step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19931step1 = (fun i j => raw19931step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19931step1 raw19931step0; decide +kernel
      have hl : raw19931step1Labels = raw19931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19931step0 raw19931step0Labels permutation104 hz
    mixedMoment B raw19931step1 raw19931step1Labels = mixedMoment B raw19931step2 raw19931step2Labels := by
      have hz : ∀ j, raw19931step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19931step2 = (fun i j => raw19931step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19931step2 raw19931step1; decide +kernel
      have hl : raw19931step2Labels = raw19931step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19931step1 raw19931step1Labels permutation14 hz
    mixedMoment B raw19931step2 raw19931step2Labels = mixedMoment B raw19931step3 raw19931step3Labels := by
      have ha : raw19931step3 = (fun i j => raw19931step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19931step3 raw19931step2; decide +kernel
      have hl : raw19931step3Labels = raw19931step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19931step2 raw19931step2Labels permutation2 permutation7
    mixedMoment B raw19931step3 raw19931step3Labels = mixedMoment B raw19931step4 raw19931step4Labels := by
      have ha : raw19931step4 = -raw19931step3 := by apply Matrix.ext; change ∀ i j, raw19931step4 i j = -(raw19931step3 i j); unfold raw19931step4 raw19931step3; decide +kernel
      have hl : raw19931step4Labels = raw19931step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19931step4 raw19931step4Labels = mixedMoment B raw19931step5 raw19931step5Labels := by
      have ha : raw19931step5 = raw19931step4 := by apply Matrix.ext; unfold raw19931step5 raw19931step4; decide +kernel
      have hl : raw19931step4Labels = labelEmbedding1 ∘ raw19931step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19931step4 raw19931step4Labels raw19931step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

theorem canonical19932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19932 raw19932Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19932 raw19932Labels = mixedMoment B raw19932step0 raw19932step0Labels := by
      have hz : ∀ j, raw19932 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19932step0 = (fun i j => raw19932 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19932step0 raw19932; decide +kernel
      have hl : raw19932step0Labels = raw19932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19932 raw19932Labels permutation520 hz
    mixedMoment B raw19932step0 raw19932step0Labels = mixedMoment B raw19932step1 raw19932step1Labels := by
      have hz : ∀ j, raw19932step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19932step1 = (fun i j => raw19932step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19932step1 raw19932step0; decide +kernel
      have hl : raw19932step1Labels = raw19932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19932step0 raw19932step0Labels permutation80 hz
    mixedMoment B raw19932step1 raw19932step1Labels = mixedMoment B raw19932step2 raw19932step2Labels := by
      have hz : ∀ j, raw19932step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19932step2 = (fun i j => raw19932step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19932step2 raw19932step1; decide +kernel
      have hl : raw19932step2Labels = raw19932step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19932step1 raw19932step1Labels permutation14 hz
    mixedMoment B raw19932step2 raw19932step2Labels = mixedMoment B raw19932step3 raw19932step3Labels := by
      have ha : raw19932step3 = (fun i j => raw19932step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19932step3 raw19932step2; decide +kernel
      have hl : raw19932step3Labels = raw19932step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19932step2 raw19932step2Labels permutation2 permutation7
    mixedMoment B raw19932step3 raw19932step3Labels = mixedMoment B raw19932step4 raw19932step4Labels := by
      have ha : raw19932step4 = -raw19932step3 := by apply Matrix.ext; change ∀ i j, raw19932step4 i j = -(raw19932step3 i j); unfold raw19932step4 raw19932step3; decide +kernel
      have hl : raw19932step4Labels = raw19932step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19932step4 raw19932step4Labels = mixedMoment B raw19932step5 raw19932step5Labels := by
      have ha : raw19932step5 = raw19932step4 := by apply Matrix.ext; unfold raw19932step5 raw19932step4; decide +kernel
      have hl : raw19932step4Labels = labelEmbedding1 ∘ raw19932step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19932step4 raw19932step4Labels raw19932step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

theorem canonical19933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19933 raw19933Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19933 raw19933Labels = mixedMoment B raw19933step0 raw19933step0Labels := by
      have hz : ∀ j, raw19933 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19933step0 = (fun i j => raw19933 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19933step0 raw19933; decide +kernel
      have hl : raw19933step0Labels = raw19933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19933 raw19933Labels permutation520 hz
    mixedMoment B raw19933step0 raw19933step0Labels = mixedMoment B raw19933step1 raw19933step1Labels := by
      have hz : ∀ j, raw19933step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19933step1 = (fun i j => raw19933step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19933step1 raw19933step0; decide +kernel
      have hl : raw19933step1Labels = raw19933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19933step0 raw19933step0Labels permutation80 hz
    mixedMoment B raw19933step1 raw19933step1Labels = mixedMoment B raw19933step2 raw19933step2Labels := by
      have ha : raw19933step2 = (fun i j => raw19933step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19933step2 raw19933step1; decide +kernel
      have hl : raw19933step2Labels = raw19933step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19933step1 raw19933step1Labels permutation31 permutation7
    mixedMoment B raw19933step2 raw19933step2Labels = mixedMoment B raw19933step3 raw19933step3Labels := by
      have ha : raw19933step3 = raw19933step2 := by apply Matrix.ext; unfold raw19933step3 raw19933step2; decide +kernel
      have hl : raw19933step2Labels = labelEmbedding1 ∘ raw19933step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19933step2 raw19933step2Labels raw19933step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19934 raw19934Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19934 raw19934Labels = mixedMoment B raw19934step0 raw19934step0Labels := by
      have hz : ∀ j, raw19934 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19934step0 = (fun i j => raw19934 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19934step0 raw19934; decide +kernel
      have hl : raw19934step0Labels = raw19934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19934 raw19934Labels permutation520 hz
    mixedMoment B raw19934step0 raw19934step0Labels = mixedMoment B raw19934step1 raw19934step1Labels := by
      have hz : ∀ j, raw19934step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19934step1 = (fun i j => raw19934step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19934step1 raw19934step0; decide +kernel
      have hl : raw19934step1Labels = raw19934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19934step0 raw19934step0Labels permutation56 hz
    mixedMoment B raw19934step1 raw19934step1Labels = mixedMoment B raw19934step2 raw19934step2Labels := by
      have ha : raw19934step2 = (fun i j => raw19934step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19934step2 raw19934step1; decide +kernel
      have hl : raw19934step2Labels = raw19934step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19934step1 raw19934step1Labels permutation31 permutation7
    mixedMoment B raw19934step2 raw19934step2Labels = mixedMoment B raw19934step3 raw19934step3Labels := by
      have ha : raw19934step3 = raw19934step2 := by apply Matrix.ext; unfold raw19934step3 raw19934step2; decide +kernel
      have hl : raw19934step2Labels = labelEmbedding1 ∘ raw19934step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19934step2 raw19934step2Labels raw19934step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19935 raw19935Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19935 raw19935Labels = mixedMoment B raw19935step0 raw19935step0Labels := by
      have hz : ∀ j, raw19935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19935step0 = (fun i j => raw19935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19935step0 raw19935; decide +kernel
      have hl : raw19935step0Labels = raw19935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19935 raw19935Labels permutation346 hz
    mixedMoment B raw19935step0 raw19935step0Labels = mixedMoment B raw19935step1 raw19935step1Labels := by
      have hz : ∀ j, raw19935step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19935step1 = (fun i j => raw19935step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19935step1 raw19935step0; decide +kernel
      have hl : raw19935step1Labels = raw19935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19935step0 raw19935step0Labels permutation56 hz
    mixedMoment B raw19935step1 raw19935step1Labels = mixedMoment B raw19935step2 raw19935step2Labels := by
      have ha : raw19935step2 = (fun i j => raw19935step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19935step2 raw19935step1; decide +kernel
      have hl : raw19935step2Labels = raw19935step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19935step1 raw19935step1Labels permutation29 permutation7
    mixedMoment B raw19935step2 raw19935step2Labels = mixedMoment B raw19935step3 raw19935step3Labels := by
      have ha : raw19935step3 = raw19935step2 := by apply Matrix.ext; unfold raw19935step3 raw19935step2; decide +kernel
      have hl : raw19935step2Labels = labelEmbedding1 ∘ raw19935step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19935step2 raw19935step2Labels raw19935step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

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

theorem canonical19937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19937 raw19937Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19937 raw19937Labels = mixedMoment B raw19937step0 raw19937step0Labels := by
      have hz : ∀ j, raw19937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19937step0 = (fun i j => raw19937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19937step0 raw19937; decide +kernel
      have hl : raw19937step0Labels = raw19937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19937 raw19937Labels permutation434 hz
    mixedMoment B raw19937step0 raw19937step0Labels = mixedMoment B raw19937step1 raw19937step1Labels := by
      have hz : ∀ j, raw19937step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19937step1 = (fun i j => raw19937step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19937step1 raw19937step0; decide +kernel
      have hl : raw19937step1Labels = raw19937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19937step0 raw19937step0Labels permutation80 hz
    mixedMoment B raw19937step1 raw19937step1Labels = mixedMoment B raw19937step2 raw19937step2Labels := by
      have hz : ∀ j, raw19937step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19937step2 = (fun i j => raw19937step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19937step2 raw19937step1; decide +kernel
      have hl : raw19937step2Labels = raw19937step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19937step1 raw19937step1Labels permutation14 hz
    mixedMoment B raw19937step2 raw19937step2Labels = mixedMoment B raw19937step3 raw19937step3Labels := by
      have ha : raw19937step3 = (fun i j => raw19937step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19937step3 raw19937step2; decide +kernel
      have hl : raw19937step3Labels = raw19937step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19937step2 raw19937step2Labels permutation2 permutation7
    mixedMoment B raw19937step3 raw19937step3Labels = mixedMoment B raw19937step4 raw19937step4Labels := by
      have ha : raw19937step4 = -raw19937step3 := by apply Matrix.ext; change ∀ i j, raw19937step4 i j = -(raw19937step3 i j); unfold raw19937step4 raw19937step3; decide +kernel
      have hl : raw19937step4Labels = raw19937step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19937step4 raw19937step4Labels = mixedMoment B raw19937step5 raw19937step5Labels := by
      have ha : raw19937step5 = raw19937step4 := by apply Matrix.ext; unfold raw19937step5 raw19937step4; decide +kernel
      have hl : raw19937step4Labels = labelEmbedding1 ∘ raw19937step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19937step4 raw19937step4Labels raw19937step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

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

theorem canonical19939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19939 raw19939Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19939 raw19939Labels = mixedMoment B raw19939step0 raw19939step0Labels := by
      have hz : ∀ j, raw19939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19939step0 = (fun i j => raw19939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19939step0 raw19939; decide +kernel
      have hl : raw19939step0Labels = raw19939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19939 raw19939Labels permutation434 hz
    mixedMoment B raw19939step0 raw19939step0Labels = mixedMoment B raw19939step1 raw19939step1Labels := by
      have hz : ∀ j, raw19939step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19939step1 = (fun i j => raw19939step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19939step1 raw19939step0; decide +kernel
      have hl : raw19939step1Labels = raw19939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19939step0 raw19939step0Labels permutation56 hz
    mixedMoment B raw19939step1 raw19939step1Labels = mixedMoment B raw19939step2 raw19939step2Labels := by
      have ha : raw19939step2 = (fun i j => raw19939step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19939step2 raw19939step1; decide +kernel
      have hl : raw19939step2Labels = raw19939step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19939step1 raw19939step1Labels permutation31 permutation7
    mixedMoment B raw19939step2 raw19939step2Labels = mixedMoment B raw19939step3 raw19939step3Labels := by
      have ha : raw19939step3 = raw19939step2 := by apply Matrix.ext; unfold raw19939step3 raw19939step2; decide +kernel
      have hl : raw19939step2Labels = labelEmbedding1 ∘ raw19939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19939step2 raw19939step2Labels raw19939step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19940 raw19940Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19940 raw19940Labels = mixedMoment B raw19940step0 raw19940step0Labels := by
      have hz : ∀ j, raw19940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19940step0 = (fun i j => raw19940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19940step0 raw19940; decide +kernel
      have hl : raw19940step0Labels = raw19940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19940 raw19940Labels permutation346 hz
    mixedMoment B raw19940step0 raw19940step0Labels = mixedMoment B raw19940step1 raw19940step1Labels := by
      have hz : ∀ j, raw19940step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19940step1 = (fun i j => raw19940step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19940step1 raw19940step0; decide +kernel
      have hl : raw19940step1Labels = raw19940step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19940step0 raw19940step0Labels permutation56 hz
    mixedMoment B raw19940step1 raw19940step1Labels = mixedMoment B raw19940step2 raw19940step2Labels := by
      have ha : raw19940step2 = (fun i j => raw19940step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19940step2 raw19940step1; decide +kernel
      have hl : raw19940step2Labels = raw19940step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19940step1 raw19940step1Labels permutation31 permutation7
    mixedMoment B raw19940step2 raw19940step2Labels = mixedMoment B raw19940step3 raw19940step3Labels := by
      have ha : raw19940step3 = raw19940step2 := by apply Matrix.ext; unfold raw19940step3 raw19940step2; decide +kernel
      have hl : raw19940step2Labels = labelEmbedding1 ∘ raw19940step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19940step2 raw19940step2Labels raw19940step3Labels labelEmbedding1 hl
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

theorem canonical19942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19942 raw19942Labels = mixedMoment B node1541 node1541Labels := by
  calc
    mixedMoment B raw19942 raw19942Labels = mixedMoment B raw19942step0 raw19942step0Labels := by
      have hz : ∀ j, raw19942 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19942step0 = (fun i j => raw19942 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19942step0 raw19942; decide +kernel
      have hl : raw19942step0Labels = raw19942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19942 raw19942Labels permutation520 hz
    mixedMoment B raw19942step0 raw19942step0Labels = mixedMoment B raw19942step1 raw19942step1Labels := by
      have hz : ∀ j, raw19942step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19942step1 = (fun i j => raw19942step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19942step1 raw19942step0; decide +kernel
      have hl : raw19942step1Labels = raw19942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19942step0 raw19942step0Labels permutation104 hz
    mixedMoment B raw19942step1 raw19942step1Labels = mixedMoment B raw19942step2 raw19942step2Labels := by
      have hz : ∀ j, raw19942step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19942step2 = (fun i j => raw19942step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19942step2 raw19942step1; decide +kernel
      have hl : raw19942step2Labels = raw19942step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19942step1 raw19942step1Labels permutation20 hz
    mixedMoment B raw19942step2 raw19942step2Labels = mixedMoment B raw19942step3 raw19942step3Labels := by
      have hz : ∀ j, raw19942step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19942step3 = (fun i j => raw19942step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19942step3 raw19942step2; decide +kernel
      have hl : raw19942step3Labels = raw19942step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19942step2 raw19942step2Labels permutation4 hz
    mixedMoment B raw19942step3 raw19942step3Labels = mixedMoment B raw19942step4 raw19942step4Labels := by
      have ha : raw19942step4 = (fun i j => raw19942step3 (permutation1 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19942step4 raw19942step3; decide +kernel
      have hl : raw19942step4Labels = raw19942step3Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19942step3 raw19942step3Labels permutation1 permutation7
    mixedMoment B raw19942step4 raw19942step4Labels = mixedMoment B raw19942step5 raw19942step5Labels := by
      have ha : raw19942step5 = raw19942step4 := by apply Matrix.ext; unfold raw19942step5 raw19942step4; decide +kernel
      have hl : raw19942step4Labels = labelEmbedding1 ∘ raw19942step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19942step4 raw19942step4Labels raw19942step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1541 node1541Labels := by rfl

theorem canonical19943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19943 raw19943Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19943 raw19943Labels = mixedMoment B raw19943step0 raw19943step0Labels := by
      have hz : ∀ j, raw19943 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19943step0 = (fun i j => raw19943 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19943step0 raw19943; decide +kernel
      have hl : raw19943step0Labels = raw19943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19943 raw19943Labels permutation520 hz
    mixedMoment B raw19943step0 raw19943step0Labels = mixedMoment B raw19943step1 raw19943step1Labels := by
      have hz : ∀ j, raw19943step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19943step1 = (fun i j => raw19943step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19943step1 raw19943step0; decide +kernel
      have hl : raw19943step1Labels = raw19943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19943step0 raw19943step0Labels permutation104 hz
    mixedMoment B raw19943step1 raw19943step1Labels = mixedMoment B raw19943step2 raw19943step2Labels := by
      have hz : ∀ j, raw19943step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19943step2 = (fun i j => raw19943step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19943step2 raw19943step1; decide +kernel
      have hl : raw19943step2Labels = raw19943step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19943step1 raw19943step1Labels permutation20 hz
    mixedMoment B raw19943step2 raw19943step2Labels = mixedMoment B raw19943step3 raw19943step3Labels := by
      have ha : raw19943step3 = (fun i j => raw19943step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19943step3 raw19943step2; decide +kernel
      have hl : raw19943step3Labels = raw19943step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19943step2 raw19943step2Labels permutation7 permutation7
    mixedMoment B raw19943step3 raw19943step3Labels = mixedMoment B raw19943step4 raw19943step4Labels := by
      have ha : raw19943step4 = raw19943step3 := by apply Matrix.ext; unfold raw19943step4 raw19943step3; decide +kernel
      have hl : raw19943step3Labels = labelEmbedding1 ∘ raw19943step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19943step3 raw19943step3Labels raw19943step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

theorem canonical19944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19944 raw19944Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19944 raw19944Labels = mixedMoment B raw19944step0 raw19944step0Labels := by
      have hz : ∀ j, raw19944 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19944step0 = (fun i j => raw19944 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19944step0 raw19944; decide +kernel
      have hl : raw19944step0Labels = raw19944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19944 raw19944Labels permutation520 hz
    mixedMoment B raw19944step0 raw19944step0Labels = mixedMoment B raw19944step1 raw19944step1Labels := by
      have hz : ∀ j, raw19944step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19944step1 = (fun i j => raw19944step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19944step1 raw19944step0; decide +kernel
      have hl : raw19944step1Labels = raw19944step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19944step0 raw19944step0Labels permutation104 hz
    mixedMoment B raw19944step1 raw19944step1Labels = mixedMoment B raw19944step2 raw19944step2Labels := by
      have hz : ∀ j, raw19944step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19944step2 = (fun i j => raw19944step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19944step2 raw19944step1; decide +kernel
      have hl : raw19944step2Labels = raw19944step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19944step1 raw19944step1Labels permutation14 hz
    mixedMoment B raw19944step2 raw19944step2Labels = mixedMoment B raw19944step3 raw19944step3Labels := by
      have ha : raw19944step3 = (fun i j => raw19944step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19944step3 raw19944step2; decide +kernel
      have hl : raw19944step3Labels = raw19944step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19944step2 raw19944step2Labels permutation7 permutation7
    mixedMoment B raw19944step3 raw19944step3Labels = mixedMoment B raw19944step4 raw19944step4Labels := by
      have ha : raw19944step4 = raw19944step3 := by apply Matrix.ext; unfold raw19944step4 raw19944step3; decide +kernel
      have hl : raw19944step3Labels = labelEmbedding1 ∘ raw19944step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19944step3 raw19944step3Labels raw19944step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

theorem canonical19945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19945 raw19945Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19945 raw19945Labels = mixedMoment B raw19945step0 raw19945step0Labels := by
      have hz : ∀ j, raw19945 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19945step0 = (fun i j => raw19945 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19945step0 raw19945; decide +kernel
      have hl : raw19945step0Labels = raw19945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19945 raw19945Labels permutation520 hz
    mixedMoment B raw19945step0 raw19945step0Labels = mixedMoment B raw19945step1 raw19945step1Labels := by
      have hz : ∀ j, raw19945step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19945step1 = (fun i j => raw19945step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19945step1 raw19945step0; decide +kernel
      have hl : raw19945step1Labels = raw19945step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19945step0 raw19945step0Labels permutation80 hz
    mixedMoment B raw19945step1 raw19945step1Labels = mixedMoment B raw19945step2 raw19945step2Labels := by
      have hz : ∀ j, raw19945step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19945step2 = (fun i j => raw19945step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19945step2 raw19945step1; decide +kernel
      have hl : raw19945step2Labels = raw19945step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19945step1 raw19945step1Labels permutation14 hz
    mixedMoment B raw19945step2 raw19945step2Labels = mixedMoment B raw19945step3 raw19945step3Labels := by
      have ha : raw19945step3 = (fun i j => raw19945step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19945step3 raw19945step2; decide +kernel
      have hl : raw19945step3Labels = raw19945step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19945step2 raw19945step2Labels permutation7 permutation7
    mixedMoment B raw19945step3 raw19945step3Labels = mixedMoment B raw19945step4 raw19945step4Labels := by
      have ha : raw19945step4 = raw19945step3 := by apply Matrix.ext; unfold raw19945step4 raw19945step3; decide +kernel
      have hl : raw19945step3Labels = labelEmbedding1 ∘ raw19945step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19945step3 raw19945step3Labels raw19945step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

theorem canonical19946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19946 raw19946Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19946 raw19946Labels = mixedMoment B raw19946step0 raw19946step0Labels := by
      have hz : ∀ j, raw19946 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19946step0 = (fun i j => raw19946 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19946step0 raw19946; decide +kernel
      have hl : raw19946step0Labels = raw19946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19946 raw19946Labels permutation434 hz
    mixedMoment B raw19946step0 raw19946step0Labels = mixedMoment B raw19946step1 raw19946step1Labels := by
      have hz : ∀ j, raw19946step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19946step1 = (fun i j => raw19946step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19946step1 raw19946step0; decide +kernel
      have hl : raw19946step1Labels = raw19946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19946step0 raw19946step0Labels permutation80 hz
    mixedMoment B raw19946step1 raw19946step1Labels = mixedMoment B raw19946step2 raw19946step2Labels := by
      have hz : ∀ j, raw19946step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19946step2 = (fun i j => raw19946step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19946step2 raw19946step1; decide +kernel
      have hl : raw19946step2Labels = raw19946step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19946step1 raw19946step1Labels permutation14 hz
    mixedMoment B raw19946step2 raw19946step2Labels = mixedMoment B raw19946step3 raw19946step3Labels := by
      have ha : raw19946step3 = (fun i j => raw19946step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19946step3 raw19946step2; decide +kernel
      have hl : raw19946step3Labels = raw19946step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19946step2 raw19946step2Labels permutation7 permutation7
    mixedMoment B raw19946step3 raw19946step3Labels = mixedMoment B raw19946step4 raw19946step4Labels := by
      have ha : raw19946step4 = raw19946step3 := by apply Matrix.ext; unfold raw19946step4 raw19946step3; decide +kernel
      have hl : raw19946step3Labels = labelEmbedding1 ∘ raw19946step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19946step3 raw19946step3Labels raw19946step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

theorem canonical19947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19947 raw19947Labels = mixedMoment B node1096 node1096Labels := by
  calc
    mixedMoment B raw19947 raw19947Labels = mixedMoment B raw19947step0 raw19947step0Labels := by
      have hz : ∀ j, raw19947 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19947step0 = (fun i j => raw19947 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19947step0 raw19947; decide +kernel
      have hl : raw19947step0Labels = raw19947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19947 raw19947Labels permutation520 hz
    mixedMoment B raw19947step0 raw19947step0Labels = mixedMoment B raw19947step1 raw19947step1Labels := by
      have hz : ∀ j, raw19947step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19947step1 = (fun i j => raw19947step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19947step1 raw19947step0; decide +kernel
      have hl : raw19947step1Labels = raw19947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19947step0 raw19947step0Labels permutation104 hz
    mixedMoment B raw19947step1 raw19947step1Labels = mixedMoment B raw19947step2 raw19947step2Labels := by
      have hz : ∀ j, raw19947step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19947step2 = (fun i j => raw19947step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19947step2 raw19947step1; decide +kernel
      have hl : raw19947step2Labels = raw19947step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19947step1 raw19947step1Labels permutation20 hz
    mixedMoment B raw19947step2 raw19947step2Labels = mixedMoment B raw19947step3 raw19947step3Labels := by
      have hz : ∀ j, raw19947step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19947step3 = (fun i j => raw19947step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19947step3 raw19947step2; decide +kernel
      have hl : raw19947step3Labels = raw19947step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19947step2 raw19947step2Labels permutation4 hz
    _ = mixedMoment B node1096 node1096Labels := by rfl

theorem canonical19948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19948 raw19948Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw19948 raw19948Labels = mixedMoment B raw19948step0 raw19948step0Labels := by
      have hz : ∀ j, raw19948 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19948step0 = (fun i j => raw19948 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19948step0 raw19948; decide +kernel
      have hl : raw19948step0Labels = raw19948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19948 raw19948Labels permutation520 hz
    mixedMoment B raw19948step0 raw19948step0Labels = mixedMoment B raw19948step1 raw19948step1Labels := by
      have hz : ∀ j, raw19948step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19948step1 = (fun i j => raw19948step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19948step1 raw19948step0; decide +kernel
      have hl : raw19948step1Labels = raw19948step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19948step0 raw19948step0Labels permutation104 hz
    mixedMoment B raw19948step1 raw19948step1Labels = mixedMoment B raw19948step2 raw19948step2Labels := by
      have hz : ∀ j, raw19948step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19948step2 = (fun i j => raw19948step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19948step2 raw19948step1; decide +kernel
      have hl : raw19948step2Labels = raw19948step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19948step1 raw19948step1Labels permutation20 hz
    _ = mixedMoment B node609 node609Labels := by rfl

theorem canonical19949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19949 raw19949Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw19949 raw19949Labels = mixedMoment B raw19949step0 raw19949step0Labels := by
      have hz : ∀ j, raw19949 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19949step0 = (fun i j => raw19949 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19949step0 raw19949; decide +kernel
      have hl : raw19949step0Labels = raw19949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19949 raw19949Labels permutation520 hz
    mixedMoment B raw19949step0 raw19949step0Labels = mixedMoment B raw19949step1 raw19949step1Labels := by
      have hz : ∀ j, raw19949step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19949step1 = (fun i j => raw19949step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19949step1 raw19949step0; decide +kernel
      have hl : raw19949step1Labels = raw19949step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19949step0 raw19949step0Labels permutation104 hz
    mixedMoment B raw19949step1 raw19949step1Labels = mixedMoment B raw19949step2 raw19949step2Labels := by
      have hz : ∀ j, raw19949step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19949step2 = (fun i j => raw19949step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19949step2 raw19949step1; decide +kernel
      have hl : raw19949step2Labels = raw19949step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19949step1 raw19949step1Labels permutation14 hz
    _ = mixedMoment B node609 node609Labels := by rfl

theorem canonical19950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19950 raw19950Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw19950 raw19950Labels = mixedMoment B raw19950step0 raw19950step0Labels := by
      have hz : ∀ j, raw19950 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19950step0 = (fun i j => raw19950 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19950step0 raw19950; decide +kernel
      have hl : raw19950step0Labels = raw19950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19950 raw19950Labels permutation520 hz
    mixedMoment B raw19950step0 raw19950step0Labels = mixedMoment B raw19950step1 raw19950step1Labels := by
      have hz : ∀ j, raw19950step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19950step1 = (fun i j => raw19950step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19950step1 raw19950step0; decide +kernel
      have hl : raw19950step1Labels = raw19950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19950step0 raw19950step0Labels permutation80 hz
    mixedMoment B raw19950step1 raw19950step1Labels = mixedMoment B raw19950step2 raw19950step2Labels := by
      have hz : ∀ j, raw19950step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19950step2 = (fun i j => raw19950step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19950step2 raw19950step1; decide +kernel
      have hl : raw19950step2Labels = raw19950step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19950step1 raw19950step1Labels permutation14 hz
    _ = mixedMoment B node609 node609Labels := by rfl

theorem canonical19951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19951 raw19951Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw19951 raw19951Labels = mixedMoment B raw19951step0 raw19951step0Labels := by
      have hz : ∀ j, raw19951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19951step0 = (fun i j => raw19951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19951step0 raw19951; decide +kernel
      have hl : raw19951step0Labels = raw19951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19951 raw19951Labels permutation434 hz
    mixedMoment B raw19951step0 raw19951step0Labels = mixedMoment B raw19951step1 raw19951step1Labels := by
      have hz : ∀ j, raw19951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19951step1 = (fun i j => raw19951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19951step1 raw19951step0; decide +kernel
      have hl : raw19951step1Labels = raw19951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19951step0 raw19951step0Labels permutation80 hz
    mixedMoment B raw19951step1 raw19951step1Labels = mixedMoment B raw19951step2 raw19951step2Labels := by
      have hz : ∀ j, raw19951step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19951step2 = (fun i j => raw19951step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19951step2 raw19951step1; decide +kernel
      have hl : raw19951step2Labels = raw19951step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19951step1 raw19951step1Labels permutation14 hz
    _ = mixedMoment B node609 node609Labels := by rfl

theorem canonical19952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19952 raw19952Labels = mixedMoment B node622 node622Labels := by
  calc
    mixedMoment B raw19952 raw19952Labels = mixedMoment B raw19952step0 raw19952step0Labels := by
      have hz : ∀ j, raw19952 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19952step0 = (fun i j => raw19952 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19952step0 raw19952; decide +kernel
      have hl : raw19952step0Labels = raw19952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19952 raw19952Labels permutation520 hz
    mixedMoment B raw19952step0 raw19952step0Labels = mixedMoment B raw19952step1 raw19952step1Labels := by
      have hz : ∀ j, raw19952step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19952step1 = (fun i j => raw19952step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19952step1 raw19952step0; decide +kernel
      have hl : raw19952step1Labels = raw19952step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19952step0 raw19952step0Labels permutation104 hz
    mixedMoment B raw19952step1 raw19952step1Labels = mixedMoment B raw19952step2 raw19952step2Labels := by
      have hz : ∀ j, raw19952step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19952step2 = (fun i j => raw19952step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19952step2 raw19952step1; decide +kernel
      have hl : raw19952step2Labels = raw19952step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19952step1 raw19952step1Labels permutation20 hz
    mixedMoment B raw19952step2 raw19952step2Labels = mixedMoment B raw19952step3 raw19952step3Labels := by
      have hz : ∀ j, raw19952step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19952step3 = (fun i j => raw19952step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19952step3 raw19952step2; decide +kernel
      have hl : raw19952step3Labels = raw19952step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19952step2 raw19952step2Labels permutation4 hz
    _ = mixedMoment B node622 node622Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20001 raw20001Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw20001 raw20001Labels = mixedMoment B raw20001step0 raw20001step0Labels := by
      have hz : ∀ j, raw20001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20001step0 = (fun i j => raw20001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20001step0 raw20001; decide +kernel
      have hl : raw20001step0Labels = raw20001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20001 raw20001Labels permutation434 hz
    mixedMoment B raw20001step0 raw20001step0Labels = mixedMoment B raw20001step1 raw20001step1Labels := by
      have hz : ∀ j, raw20001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20001step1 = (fun i j => raw20001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20001step1 raw20001step0; decide +kernel
      have hl : raw20001step1Labels = raw20001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20001step0 raw20001step0Labels permutation80 hz
    mixedMoment B raw20001step1 raw20001step1Labels = mixedMoment B raw20001step2 raw20001step2Labels := by
      have ha : raw20001step2 = (fun i j => raw20001step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20001step2 raw20001step1; decide +kernel
      have hl : raw20001step2Labels = raw20001step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20001step1 raw20001step1Labels permutation29 permutation7
    mixedMoment B raw20001step2 raw20001step2Labels = mixedMoment B raw20001step3 raw20001step3Labels := by
      have ha : raw20001step3 = raw20001step2 := by apply Matrix.ext; unfold raw20001step3 raw20001step2; decide +kernel
      have hl : raw20001step2Labels = labelEmbedding1 ∘ raw20001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20001step2 raw20001step2Labels raw20001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node809 node809Labels := by rfl

theorem canonical20002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20002 raw20002Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw20002 raw20002Labels = mixedMoment B raw20002step0 raw20002step0Labels := by
      have hz : ∀ j, raw20002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20002step0 = (fun i j => raw20002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20002step0 raw20002; decide +kernel
      have hl : raw20002step0Labels = raw20002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20002 raw20002Labels permutation434 hz
    mixedMoment B raw20002step0 raw20002step0Labels = mixedMoment B raw20002step1 raw20002step1Labels := by
      have hz : ∀ j, raw20002step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20002step1 = (fun i j => raw20002step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20002step1 raw20002step0; decide +kernel
      have hl : raw20002step1Labels = raw20002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20002step0 raw20002step0Labels permutation56 hz
    mixedMoment B raw20002step1 raw20002step1Labels = mixedMoment B raw20002step2 raw20002step2Labels := by
      have ha : raw20002step2 = (fun i j => raw20002step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20002step2 raw20002step1; decide +kernel
      have hl : raw20002step2Labels = raw20002step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20002step1 raw20002step1Labels permutation29 permutation7
    mixedMoment B raw20002step2 raw20002step2Labels = mixedMoment B raw20002step3 raw20002step3Labels := by
      have ha : raw20002step3 = raw20002step2 := by apply Matrix.ext; unfold raw20002step3 raw20002step2; decide +kernel
      have hl : raw20002step2Labels = labelEmbedding1 ∘ raw20002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20002step2 raw20002step2Labels raw20002step3Labels labelEmbedding1 hl
    _ = mixedMoment B node809 node809Labels := by rfl

theorem canonical20003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20003 raw20003Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw20003 raw20003Labels = mixedMoment B raw20003step0 raw20003step0Labels := by
      have hz : ∀ j, raw20003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20003step0 = (fun i j => raw20003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20003step0 raw20003; decide +kernel
      have hl : raw20003step0Labels = raw20003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20003 raw20003Labels permutation346 hz
    mixedMoment B raw20003step0 raw20003step0Labels = mixedMoment B raw20003step1 raw20003step1Labels := by
      have hz : ∀ j, raw20003step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20003step1 = (fun i j => raw20003step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20003step1 raw20003step0; decide +kernel
      have hl : raw20003step1Labels = raw20003step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20003step0 raw20003step0Labels permutation56 hz
    mixedMoment B raw20003step1 raw20003step1Labels = mixedMoment B raw20003step2 raw20003step2Labels := by
      have ha : raw20003step2 = (fun i j => raw20003step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20003step2 raw20003step1; decide +kernel
      have hl : raw20003step2Labels = raw20003step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20003step1 raw20003step1Labels permutation29 permutation7
    mixedMoment B raw20003step2 raw20003step2Labels = mixedMoment B raw20003step3 raw20003step3Labels := by
      have ha : raw20003step3 = raw20003step2 := by apply Matrix.ext; unfold raw20003step3 raw20003step2; decide +kernel
      have hl : raw20003step2Labels = labelEmbedding1 ∘ raw20003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20003step2 raw20003step2Labels raw20003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node809 node809Labels := by rfl

theorem canonical20004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20004 raw20004Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw20004 raw20004Labels = mixedMoment B raw20004step0 raw20004step0Labels := by
      have hz : ∀ j, raw20004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20004step0 = (fun i j => raw20004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20004step0 raw20004; decide +kernel
      have hl : raw20004step0Labels = raw20004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20004 raw20004Labels permutation434 hz
    mixedMoment B raw20004step0 raw20004step0Labels = mixedMoment B raw20004step1 raw20004step1Labels := by
      have hz : ∀ j, raw20004step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20004step1 = (fun i j => raw20004step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20004step1 raw20004step0; decide +kernel
      have hl : raw20004step1Labels = raw20004step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20004step0 raw20004step0Labels permutation80 hz
    mixedMoment B raw20004step1 raw20004step1Labels = mixedMoment B raw20004step2 raw20004step2Labels := by
      have hz : ∀ j, raw20004step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20004step2 = (fun i j => raw20004step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20004step2 raw20004step1; decide +kernel
      have hl : raw20004step2Labels = raw20004step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20004step1 raw20004step1Labels permutation14 hz
    mixedMoment B raw20004step2 raw20004step2Labels = mixedMoment B raw20004step3 raw20004step3Labels := by
      have hz : ∀ i, raw20004step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw20004step3 = (fun i j => raw20004step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw20004step3 raw20004step2; decide +kernel
      have hl : raw20004step3Labels = (fun j => raw20004step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20004step2 raw20004step2Labels permutation4 hz
    mixedMoment B raw20004step3 raw20004step3Labels = mixedMoment B raw20004step4 raw20004step4Labels := by
      have ha : raw20004step4 = (fun i j => raw20004step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20004step4 raw20004step3; decide +kernel
      have hl : raw20004step4Labels = raw20004step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20004step3 raw20004step3Labels permutation7 permutation0
    mixedMoment B raw20004step4 raw20004step4Labels = mixedMoment B raw20004step5 raw20004step5Labels := by
      have ha : raw20004step5 = -raw20004step4 := by apply Matrix.ext; change ∀ i j, raw20004step5 i j = -(raw20004step4 i j); unfold raw20004step5 raw20004step4; decide +kernel
      have hl : raw20004step5Labels = raw20004step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical20005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20005 raw20005Labels = mixedMoment B node1085 node1085Labels := by
  calc
    mixedMoment B raw20005 raw20005Labels = mixedMoment B raw20005step0 raw20005step0Labels := by
      have hz : ∀ j, raw20005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20005step0 = (fun i j => raw20005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20005step0 raw20005; decide +kernel
      have hl : raw20005step0Labels = raw20005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20005 raw20005Labels permutation434 hz
    mixedMoment B raw20005step0 raw20005step0Labels = mixedMoment B raw20005step1 raw20005step1Labels := by
      have hz : ∀ j, raw20005step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20005step1 = (fun i j => raw20005step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20005step1 raw20005step0; decide +kernel
      have hl : raw20005step1Labels = raw20005step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20005step0 raw20005step0Labels permutation80 hz
    mixedMoment B raw20005step1 raw20005step1Labels = mixedMoment B raw20005step2 raw20005step2Labels := by
      have hz : ∀ j, raw20005step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20005step2 = (fun i j => raw20005step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20005step2 raw20005step1; decide +kernel
      have hl : raw20005step2Labels = raw20005step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20005step1 raw20005step1Labels permutation14 hz
    mixedMoment B raw20005step2 raw20005step2Labels = mixedMoment B raw20005step3 raw20005step3Labels := by
      have ha : raw20005step3 = (fun i j => raw20005step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20005step3 raw20005step2; decide +kernel
      have hl : raw20005step3Labels = raw20005step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20005step2 raw20005step2Labels permutation7 permutation7
    mixedMoment B raw20005step3 raw20005step3Labels = mixedMoment B raw20005step4 raw20005step4Labels := by
      have ha : raw20005step4 = raw20005step3 := by apply Matrix.ext; unfold raw20005step4 raw20005step3; decide +kernel
      have hl : raw20005step3Labels = labelEmbedding1 ∘ raw20005step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20005step3 raw20005step3Labels raw20005step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1085 node1085Labels := by rfl

theorem canonical20006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20006 raw20006Labels = mixedMoment B node765 node765Labels := by
  calc
    mixedMoment B raw20006 raw20006Labels = mixedMoment B raw20006step0 raw20006step0Labels := by
      have hz : ∀ j, raw20006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20006step0 = (fun i j => raw20006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20006step0 raw20006; decide +kernel
      have hl : raw20006step0Labels = raw20006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20006 raw20006Labels permutation434 hz
    mixedMoment B raw20006step0 raw20006step0Labels = mixedMoment B raw20006step1 raw20006step1Labels := by
      have hz : ∀ j, raw20006step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20006step1 = (fun i j => raw20006step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20006step1 raw20006step0; decide +kernel
      have hl : raw20006step1Labels = raw20006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20006step0 raw20006step0Labels permutation80 hz
    mixedMoment B raw20006step1 raw20006step1Labels = mixedMoment B raw20006step2 raw20006step2Labels := by
      have ha : raw20006step2 = (fun i j => raw20006step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20006step2 raw20006step1; decide +kernel
      have hl : raw20006step2Labels = raw20006step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20006step1 raw20006step1Labels permutation29 permutation7
    mixedMoment B raw20006step2 raw20006step2Labels = mixedMoment B raw20006step3 raw20006step3Labels := by
      have ha : raw20006step3 = raw20006step2 := by apply Matrix.ext; unfold raw20006step3 raw20006step2; decide +kernel
      have hl : raw20006step2Labels = labelEmbedding1 ∘ raw20006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20006step2 raw20006step2Labels raw20006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node765 node765Labels := by rfl

theorem canonical20007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20007 raw20007Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw20007 raw20007Labels = mixedMoment B raw20007step0 raw20007step0Labels := by
      have hz : ∀ j, raw20007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20007step0 = (fun i j => raw20007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20007step0 raw20007; decide +kernel
      have hl : raw20007step0Labels = raw20007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20007 raw20007Labels permutation434 hz
    mixedMoment B raw20007step0 raw20007step0Labels = mixedMoment B raw20007step1 raw20007step1Labels := by
      have ha : raw20007step1 = (fun i j => raw20007step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20007step1 raw20007step0; decide +kernel
      have hl : raw20007step1Labels = raw20007step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20007step0 raw20007step0Labels permutation137 permutation7
    mixedMoment B raw20007step1 raw20007step1Labels = mixedMoment B raw20007step2 raw20007step2Labels := by
      have ha : raw20007step2 = raw20007step1 := by apply Matrix.ext; unfold raw20007step2 raw20007step1; decide +kernel
      have hl : raw20007step1Labels = labelEmbedding1 ∘ raw20007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20007step1 raw20007step1Labels raw20007step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

theorem canonical20008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20008 raw20008Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw20008 raw20008Labels = mixedMoment B raw20008step0 raw20008step0Labels := by
      have hz : ∀ j, raw20008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20008step0 = (fun i j => raw20008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20008step0 raw20008; decide +kernel
      have hl : raw20008step0Labels = raw20008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20008 raw20008Labels permutation346 hz
    mixedMoment B raw20008step0 raw20008step0Labels = mixedMoment B raw20008step1 raw20008step1Labels := by
      have ha : raw20008step1 = (fun i j => raw20008step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20008step1 raw20008step0; decide +kernel
      have hl : raw20008step1Labels = raw20008step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20008step0 raw20008step0Labels permutation137 permutation7
    mixedMoment B raw20008step1 raw20008step1Labels = mixedMoment B raw20008step2 raw20008step2Labels := by
      have ha : raw20008step2 = raw20008step1 := by apply Matrix.ext; unfold raw20008step2 raw20008step1; decide +kernel
      have hl : raw20008step1Labels = labelEmbedding1 ∘ raw20008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20008step1 raw20008step1Labels raw20008step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

theorem canonical20009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20009 raw20009Labels = mixedMoment B node770 node770Labels := by
  calc
    mixedMoment B raw20009 raw20009Labels = mixedMoment B raw20009step0 raw20009step0Labels := by
      have hz : ∀ j, raw20009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20009step0 = (fun i j => raw20009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20009step0 raw20009; decide +kernel
      have hl : raw20009step0Labels = raw20009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20009 raw20009Labels permutation434 hz
    mixedMoment B raw20009step0 raw20009step0Labels = mixedMoment B raw20009step1 raw20009step1Labels := by
      have hz : ∀ j, raw20009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20009step1 = (fun i j => raw20009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20009step1 raw20009step0; decide +kernel
      have hl : raw20009step1Labels = raw20009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20009step0 raw20009step0Labels permutation80 hz
    mixedMoment B raw20009step1 raw20009step1Labels = mixedMoment B raw20009step2 raw20009step2Labels := by
      have ha : raw20009step2 = (fun i j => raw20009step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20009step2 raw20009step1; decide +kernel
      have hl : raw20009step2Labels = raw20009step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20009step1 raw20009step1Labels permutation29 permutation7
    mixedMoment B raw20009step2 raw20009step2Labels = mixedMoment B raw20009step3 raw20009step3Labels := by
      have ha : raw20009step3 = raw20009step2 := by apply Matrix.ext; unfold raw20009step3 raw20009step2; decide +kernel
      have hl : raw20009step2Labels = labelEmbedding1 ∘ raw20009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20009step2 raw20009step2Labels raw20009step3Labels labelEmbedding1 hl
    _ = mixedMoment B node770 node770Labels := by rfl

theorem canonical20010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20010 raw20010Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw20010 raw20010Labels = mixedMoment B raw20010step0 raw20010step0Labels := by
      have hz : ∀ j, raw20010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20010step0 = (fun i j => raw20010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20010step0 raw20010; decide +kernel
      have hl : raw20010step0Labels = raw20010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20010 raw20010Labels permutation434 hz
    mixedMoment B raw20010step0 raw20010step0Labels = mixedMoment B raw20010step1 raw20010step1Labels := by
      have hz : ∀ j, raw20010step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20010step1 = (fun i j => raw20010step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20010step1 raw20010step0; decide +kernel
      have hl : raw20010step1Labels = raw20010step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20010step0 raw20010step0Labels permutation80 hz
    mixedMoment B raw20010step1 raw20010step1Labels = mixedMoment B raw20010step2 raw20010step2Labels := by
      have ha : raw20010step2 = (fun i j => raw20010step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20010step2 raw20010step1; decide +kernel
      have hl : raw20010step2Labels = raw20010step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20010step1 raw20010step1Labels permutation29 permutation7
    mixedMoment B raw20010step2 raw20010step2Labels = mixedMoment B raw20010step3 raw20010step3Labels := by
      have ha : raw20010step3 = raw20010step2 := by apply Matrix.ext; unfold raw20010step3 raw20010step2; decide +kernel
      have hl : raw20010step2Labels = labelEmbedding1 ∘ raw20010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20010step2 raw20010step2Labels raw20010step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1002 node1002Labels := by rfl

theorem canonical20011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20011 raw20011Labels = mixedMoment B node765 node765Labels := by
  calc
    mixedMoment B raw20011 raw20011Labels = mixedMoment B raw20011step0 raw20011step0Labels := by
      have hz : ∀ j, raw20011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20011step0 = (fun i j => raw20011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20011step0 raw20011; decide +kernel
      have hl : raw20011step0Labels = raw20011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20011 raw20011Labels permutation434 hz
    mixedMoment B raw20011step0 raw20011step0Labels = mixedMoment B raw20011step1 raw20011step1Labels := by
      have hz : ∀ j, raw20011step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20011step1 = (fun i j => raw20011step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20011step1 raw20011step0; decide +kernel
      have hl : raw20011step1Labels = raw20011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20011step0 raw20011step0Labels permutation56 hz
    mixedMoment B raw20011step1 raw20011step1Labels = mixedMoment B raw20011step2 raw20011step2Labels := by
      have ha : raw20011step2 = (fun i j => raw20011step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20011step2 raw20011step1; decide +kernel
      have hl : raw20011step2Labels = raw20011step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20011step1 raw20011step1Labels permutation29 permutation7
    mixedMoment B raw20011step2 raw20011step2Labels = mixedMoment B raw20011step3 raw20011step3Labels := by
      have ha : raw20011step3 = raw20011step2 := by apply Matrix.ext; unfold raw20011step3 raw20011step2; decide +kernel
      have hl : raw20011step2Labels = labelEmbedding1 ∘ raw20011step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20011step2 raw20011step2Labels raw20011step3Labels labelEmbedding1 hl
    _ = mixedMoment B node765 node765Labels := by rfl

theorem canonical20012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20012 raw20012Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw20012 raw20012Labels = mixedMoment B raw20012step0 raw20012step0Labels := by
      have hz : ∀ j, raw20012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20012step0 = (fun i j => raw20012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20012step0 raw20012; decide +kernel
      have hl : raw20012step0Labels = raw20012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20012 raw20012Labels permutation434 hz
    mixedMoment B raw20012step0 raw20012step0Labels = mixedMoment B raw20012step1 raw20012step1Labels := by
      have ha : raw20012step1 = (fun i j => raw20012step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20012step1 raw20012step0; decide +kernel
      have hl : raw20012step1Labels = raw20012step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20012step0 raw20012step0Labels permutation143 permutation7
    mixedMoment B raw20012step1 raw20012step1Labels = mixedMoment B raw20012step2 raw20012step2Labels := by
      have ha : raw20012step2 = raw20012step1 := by apply Matrix.ext; unfold raw20012step2 raw20012step1; decide +kernel
      have hl : raw20012step1Labels = labelEmbedding1 ∘ raw20012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20012step1 raw20012step1Labels raw20012step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

theorem canonical20013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20013 raw20013Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw20013 raw20013Labels = mixedMoment B raw20013step0 raw20013step0Labels := by
      have hz : ∀ j, raw20013 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20013step0 = (fun i j => raw20013 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20013step0 raw20013; decide +kernel
      have hl : raw20013step0Labels = raw20013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20013 raw20013Labels permutation265 hz
    mixedMoment B raw20013step0 raw20013step0Labels = mixedMoment B raw20013step1 raw20013step1Labels := by
      have ha : raw20013step1 = (fun i j => raw20013step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20013step1 raw20013step0; decide +kernel
      have hl : raw20013step1Labels = raw20013step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20013step0 raw20013step0Labels permutation137 permutation7
    mixedMoment B raw20013step1 raw20013step1Labels = mixedMoment B raw20013step2 raw20013step2Labels := by
      have ha : raw20013step2 = raw20013step1 := by apply Matrix.ext; unfold raw20013step2 raw20013step1; decide +kernel
      have hl : raw20013step1Labels = labelEmbedding1 ∘ raw20013step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20013step1 raw20013step1Labels raw20013step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

theorem canonical20014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20014 raw20014Labels = mixedMoment B node770 node770Labels := by
  calc
    mixedMoment B raw20014 raw20014Labels = mixedMoment B raw20014step0 raw20014step0Labels := by
      have hz : ∀ j, raw20014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20014step0 = (fun i j => raw20014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20014step0 raw20014; decide +kernel
      have hl : raw20014step0Labels = raw20014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20014 raw20014Labels permutation434 hz
    mixedMoment B raw20014step0 raw20014step0Labels = mixedMoment B raw20014step1 raw20014step1Labels := by
      have hz : ∀ j, raw20014step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20014step1 = (fun i j => raw20014step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20014step1 raw20014step0; decide +kernel
      have hl : raw20014step1Labels = raw20014step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20014step0 raw20014step0Labels permutation56 hz
    mixedMoment B raw20014step1 raw20014step1Labels = mixedMoment B raw20014step2 raw20014step2Labels := by
      have ha : raw20014step2 = (fun i j => raw20014step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20014step2 raw20014step1; decide +kernel
      have hl : raw20014step2Labels = raw20014step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20014step1 raw20014step1Labels permutation29 permutation7
    mixedMoment B raw20014step2 raw20014step2Labels = mixedMoment B raw20014step3 raw20014step3Labels := by
      have ha : raw20014step3 = raw20014step2 := by apply Matrix.ext; unfold raw20014step3 raw20014step2; decide +kernel
      have hl : raw20014step2Labels = labelEmbedding1 ∘ raw20014step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20014step2 raw20014step2Labels raw20014step3Labels labelEmbedding1 hl
    _ = mixedMoment B node770 node770Labels := by rfl

theorem canonical20015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20015 raw20015Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw20015 raw20015Labels = mixedMoment B raw20015step0 raw20015step0Labels := by
      have hz : ∀ j, raw20015 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20015step0 = (fun i j => raw20015 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20015step0 raw20015; decide +kernel
      have hl : raw20015step0Labels = raw20015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20015 raw20015Labels permutation434 hz
    mixedMoment B raw20015step0 raw20015step0Labels = mixedMoment B raw20015step1 raw20015step1Labels := by
      have hz : ∀ j, raw20015step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20015step1 = (fun i j => raw20015step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20015step1 raw20015step0; decide +kernel
      have hl : raw20015step1Labels = raw20015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20015step0 raw20015step0Labels permutation56 hz
    mixedMoment B raw20015step1 raw20015step1Labels = mixedMoment B raw20015step2 raw20015step2Labels := by
      have ha : raw20015step2 = (fun i j => raw20015step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20015step2 raw20015step1; decide +kernel
      have hl : raw20015step2Labels = raw20015step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20015step1 raw20015step1Labels permutation29 permutation7
    mixedMoment B raw20015step2 raw20015step2Labels = mixedMoment B raw20015step3 raw20015step3Labels := by
      have ha : raw20015step3 = raw20015step2 := by apply Matrix.ext; unfold raw20015step3 raw20015step2; decide +kernel
      have hl : raw20015step2Labels = labelEmbedding1 ∘ raw20015step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20015step2 raw20015step2Labels raw20015step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1002 node1002Labels := by rfl

theorem canonical20016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20016 raw20016Labels = mixedMoment B node765 node765Labels := by
  calc
    mixedMoment B raw20016 raw20016Labels = mixedMoment B raw20016step0 raw20016step0Labels := by
      have hz : ∀ j, raw20016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20016step0 = (fun i j => raw20016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20016step0 raw20016; decide +kernel
      have hl : raw20016step0Labels = raw20016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20016 raw20016Labels permutation346 hz
    mixedMoment B raw20016step0 raw20016step0Labels = mixedMoment B raw20016step1 raw20016step1Labels := by
      have hz : ∀ j, raw20016step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20016step1 = (fun i j => raw20016step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20016step1 raw20016step0; decide +kernel
      have hl : raw20016step1Labels = raw20016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20016step0 raw20016step0Labels permutation56 hz
    mixedMoment B raw20016step1 raw20016step1Labels = mixedMoment B raw20016step2 raw20016step2Labels := by
      have ha : raw20016step2 = (fun i j => raw20016step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20016step2 raw20016step1; decide +kernel
      have hl : raw20016step2Labels = raw20016step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20016step1 raw20016step1Labels permutation29 permutation7
    mixedMoment B raw20016step2 raw20016step2Labels = mixedMoment B raw20016step3 raw20016step3Labels := by
      have ha : raw20016step3 = raw20016step2 := by apply Matrix.ext; unfold raw20016step3 raw20016step2; decide +kernel
      have hl : raw20016step2Labels = labelEmbedding1 ∘ raw20016step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20016step2 raw20016step2Labels raw20016step3Labels labelEmbedding1 hl
    _ = mixedMoment B node765 node765Labels := by rfl

theorem canonical20017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20017 raw20017Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw20017 raw20017Labels = mixedMoment B raw20017step0 raw20017step0Labels := by
      have hz : ∀ j, raw20017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20017step0 = (fun i j => raw20017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20017step0 raw20017; decide +kernel
      have hl : raw20017step0Labels = raw20017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20017 raw20017Labels permutation346 hz
    mixedMoment B raw20017step0 raw20017step0Labels = mixedMoment B raw20017step1 raw20017step1Labels := by
      have ha : raw20017step1 = (fun i j => raw20017step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20017step1 raw20017step0; decide +kernel
      have hl : raw20017step1Labels = raw20017step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20017step0 raw20017step0Labels permutation143 permutation7
    mixedMoment B raw20017step1 raw20017step1Labels = mixedMoment B raw20017step2 raw20017step2Labels := by
      have ha : raw20017step2 = raw20017step1 := by apply Matrix.ext; unfold raw20017step2 raw20017step1; decide +kernel
      have hl : raw20017step1Labels = labelEmbedding1 ∘ raw20017step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20017step1 raw20017step1Labels raw20017step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

theorem canonical20018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20018 raw20018Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw20018 raw20018Labels = mixedMoment B raw20018step0 raw20018step0Labels := by
      have hz : ∀ j, raw20018 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20018step0 = (fun i j => raw20018 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20018step0 raw20018; decide +kernel
      have hl : raw20018step0Labels = raw20018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20018 raw20018Labels permutation265 hz
    mixedMoment B raw20018step0 raw20018step0Labels = mixedMoment B raw20018step1 raw20018step1Labels := by
      have ha : raw20018step1 = (fun i j => raw20018step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20018step1 raw20018step0; decide +kernel
      have hl : raw20018step1Labels = raw20018step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20018step0 raw20018step0Labels permutation143 permutation7
    mixedMoment B raw20018step1 raw20018step1Labels = mixedMoment B raw20018step2 raw20018step2Labels := by
      have ha : raw20018step2 = raw20018step1 := by apply Matrix.ext; unfold raw20018step2 raw20018step1; decide +kernel
      have hl : raw20018step1Labels = labelEmbedding1 ∘ raw20018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20018step1 raw20018step1Labels raw20018step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

theorem canonical20019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20019 raw20019Labels = mixedMoment B node770 node770Labels := by
  calc
    mixedMoment B raw20019 raw20019Labels = mixedMoment B raw20019step0 raw20019step0Labels := by
      have hz : ∀ j, raw20019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20019step0 = (fun i j => raw20019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20019step0 raw20019; decide +kernel
      have hl : raw20019step0Labels = raw20019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20019 raw20019Labels permutation346 hz
    mixedMoment B raw20019step0 raw20019step0Labels = mixedMoment B raw20019step1 raw20019step1Labels := by
      have hz : ∀ j, raw20019step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20019step1 = (fun i j => raw20019step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20019step1 raw20019step0; decide +kernel
      have hl : raw20019step1Labels = raw20019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20019step0 raw20019step0Labels permutation56 hz
    mixedMoment B raw20019step1 raw20019step1Labels = mixedMoment B raw20019step2 raw20019step2Labels := by
      have ha : raw20019step2 = (fun i j => raw20019step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20019step2 raw20019step1; decide +kernel
      have hl : raw20019step2Labels = raw20019step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20019step1 raw20019step1Labels permutation29 permutation7
    mixedMoment B raw20019step2 raw20019step2Labels = mixedMoment B raw20019step3 raw20019step3Labels := by
      have ha : raw20019step3 = raw20019step2 := by apply Matrix.ext; unfold raw20019step3 raw20019step2; decide +kernel
      have hl : raw20019step2Labels = labelEmbedding1 ∘ raw20019step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20019step2 raw20019step2Labels raw20019step3Labels labelEmbedding1 hl
    _ = mixedMoment B node770 node770Labels := by rfl

theorem canonical20020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20020 raw20020Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw20020 raw20020Labels = mixedMoment B raw20020step0 raw20020step0Labels := by
      have hz : ∀ j, raw20020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20020step0 = (fun i j => raw20020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20020step0 raw20020; decide +kernel
      have hl : raw20020step0Labels = raw20020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20020 raw20020Labels permutation346 hz
    mixedMoment B raw20020step0 raw20020step0Labels = mixedMoment B raw20020step1 raw20020step1Labels := by
      have hz : ∀ j, raw20020step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20020step1 = (fun i j => raw20020step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20020step1 raw20020step0; decide +kernel
      have hl : raw20020step1Labels = raw20020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20020step0 raw20020step0Labels permutation56 hz
    mixedMoment B raw20020step1 raw20020step1Labels = mixedMoment B raw20020step2 raw20020step2Labels := by
      have ha : raw20020step2 = (fun i j => raw20020step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20020step2 raw20020step1; decide +kernel
      have hl : raw20020step2Labels = raw20020step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20020step1 raw20020step1Labels permutation29 permutation7
    mixedMoment B raw20020step2 raw20020step2Labels = mixedMoment B raw20020step3 raw20020step3Labels := by
      have ha : raw20020step3 = raw20020step2 := by apply Matrix.ext; unfold raw20020step3 raw20020step2; decide +kernel
      have hl : raw20020step2Labels = labelEmbedding1 ∘ raw20020step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20020step2 raw20020step2Labels raw20020step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1002 node1002Labels := by rfl

theorem canonical20021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20021 raw20021Labels = mixedMoment B node845 node845Labels := by
  calc
    mixedMoment B raw20021 raw20021Labels = mixedMoment B raw20021step0 raw20021step0Labels := by
      have hz : ∀ j, raw20021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20021step0 = (fun i j => raw20021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20021step0 raw20021; decide +kernel
      have hl : raw20021step0Labels = raw20021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20021 raw20021Labels permutation434 hz
    mixedMoment B raw20021step0 raw20021step0Labels = mixedMoment B raw20021step1 raw20021step1Labels := by
      have hz : ∀ j, raw20021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20021step1 = (fun i j => raw20021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20021step1 raw20021step0; decide +kernel
      have hl : raw20021step1Labels = raw20021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20021step0 raw20021step0Labels permutation80 hz
    mixedMoment B raw20021step1 raw20021step1Labels = mixedMoment B raw20021step2 raw20021step2Labels := by
      have hz : ∀ j, raw20021step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20021step2 = (fun i j => raw20021step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20021step2 raw20021step1; decide +kernel
      have hl : raw20021step2Labels = raw20021step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20021step1 raw20021step1Labels permutation14 hz
    mixedMoment B raw20021step2 raw20021step2Labels = mixedMoment B raw20021step3 raw20021step3Labels := by
      have ha : raw20021step3 = (fun i j => raw20021step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20021step3 raw20021step2; decide +kernel
      have hl : raw20021step3Labels = raw20021step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20021step2 raw20021step2Labels permutation7 permutation7
    mixedMoment B raw20021step3 raw20021step3Labels = mixedMoment B raw20021step4 raw20021step4Labels := by
      have ha : raw20021step4 = raw20021step3 := by apply Matrix.ext; unfold raw20021step4 raw20021step3; decide +kernel
      have hl : raw20021step3Labels = labelEmbedding1 ∘ raw20021step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20021step3 raw20021step3Labels raw20021step4Labels labelEmbedding1 hl
    _ = mixedMoment B node845 node845Labels := by rfl

theorem canonical20022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20022 raw20022Labels = mixedMoment B node801 node801Labels := by
  calc
    mixedMoment B raw20022 raw20022Labels = mixedMoment B raw20022step0 raw20022step0Labels := by
      have hz : ∀ j, raw20022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20022step0 = (fun i j => raw20022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20022step0 raw20022; decide +kernel
      have hl : raw20022step0Labels = raw20022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20022 raw20022Labels permutation434 hz
    mixedMoment B raw20022step0 raw20022step0Labels = mixedMoment B raw20022step1 raw20022step1Labels := by
      have hz : ∀ j, raw20022step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20022step1 = (fun i j => raw20022step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20022step1 raw20022step0; decide +kernel
      have hl : raw20022step1Labels = raw20022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20022step0 raw20022step0Labels permutation80 hz
    mixedMoment B raw20022step1 raw20022step1Labels = mixedMoment B raw20022step2 raw20022step2Labels := by
      have ha : raw20022step2 = (fun i j => raw20022step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20022step2 raw20022step1; decide +kernel
      have hl : raw20022step2Labels = raw20022step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20022step1 raw20022step1Labels permutation29 permutation7
    mixedMoment B raw20022step2 raw20022step2Labels = mixedMoment B raw20022step3 raw20022step3Labels := by
      have ha : raw20022step3 = raw20022step2 := by apply Matrix.ext; unfold raw20022step3 raw20022step2; decide +kernel
      have hl : raw20022step2Labels = labelEmbedding1 ∘ raw20022step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20022step2 raw20022step2Labels raw20022step3Labels labelEmbedding1 hl
    _ = mixedMoment B node801 node801Labels := by rfl

theorem canonical20023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20023 raw20023Labels = mixedMoment B node801 node801Labels := by
  calc
    mixedMoment B raw20023 raw20023Labels = mixedMoment B raw20023step0 raw20023step0Labels := by
      have hz : ∀ j, raw20023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20023step0 = (fun i j => raw20023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20023step0 raw20023; decide +kernel
      have hl : raw20023step0Labels = raw20023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20023 raw20023Labels permutation434 hz
    mixedMoment B raw20023step0 raw20023step0Labels = mixedMoment B raw20023step1 raw20023step1Labels := by
      have hz : ∀ j, raw20023step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20023step1 = (fun i j => raw20023step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20023step1 raw20023step0; decide +kernel
      have hl : raw20023step1Labels = raw20023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20023step0 raw20023step0Labels permutation56 hz
    mixedMoment B raw20023step1 raw20023step1Labels = mixedMoment B raw20023step2 raw20023step2Labels := by
      have ha : raw20023step2 = (fun i j => raw20023step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20023step2 raw20023step1; decide +kernel
      have hl : raw20023step2Labels = raw20023step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20023step1 raw20023step1Labels permutation29 permutation7
    mixedMoment B raw20023step2 raw20023step2Labels = mixedMoment B raw20023step3 raw20023step3Labels := by
      have ha : raw20023step3 = raw20023step2 := by apply Matrix.ext; unfold raw20023step3 raw20023step2; decide +kernel
      have hl : raw20023step2Labels = labelEmbedding1 ∘ raw20023step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20023step2 raw20023step2Labels raw20023step3Labels labelEmbedding1 hl
    _ = mixedMoment B node801 node801Labels := by rfl

theorem canonical20024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20024 raw20024Labels = mixedMoment B node801 node801Labels := by
  calc
    mixedMoment B raw20024 raw20024Labels = mixedMoment B raw20024step0 raw20024step0Labels := by
      have hz : ∀ j, raw20024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20024step0 = (fun i j => raw20024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20024step0 raw20024; decide +kernel
      have hl : raw20024step0Labels = raw20024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20024 raw20024Labels permutation346 hz
    mixedMoment B raw20024step0 raw20024step0Labels = mixedMoment B raw20024step1 raw20024step1Labels := by
      have hz : ∀ j, raw20024step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20024step1 = (fun i j => raw20024step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20024step1 raw20024step0; decide +kernel
      have hl : raw20024step1Labels = raw20024step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20024step0 raw20024step0Labels permutation56 hz
    mixedMoment B raw20024step1 raw20024step1Labels = mixedMoment B raw20024step2 raw20024step2Labels := by
      have ha : raw20024step2 = (fun i j => raw20024step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20024step2 raw20024step1; decide +kernel
      have hl : raw20024step2Labels = raw20024step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20024step1 raw20024step1Labels permutation29 permutation7
    mixedMoment B raw20024step2 raw20024step2Labels = mixedMoment B raw20024step3 raw20024step3Labels := by
      have ha : raw20024step3 = raw20024step2 := by apply Matrix.ext; unfold raw20024step3 raw20024step2; decide +kernel
      have hl : raw20024step2Labels = labelEmbedding1 ∘ raw20024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20024step2 raw20024step2Labels raw20024step3Labels labelEmbedding1 hl
    _ = mixedMoment B node801 node801Labels := by rfl

theorem canonical20025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20025 raw20025Labels = mixedMoment B node1077 node1077Labels := by
  calc
    mixedMoment B raw20025 raw20025Labels = mixedMoment B raw20025step0 raw20025step0Labels := by
      have hz : ∀ j, raw20025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20025step0 = (fun i j => raw20025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20025step0 raw20025; decide +kernel
      have hl : raw20025step0Labels = raw20025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20025 raw20025Labels permutation434 hz
    mixedMoment B raw20025step0 raw20025step0Labels = mixedMoment B raw20025step1 raw20025step1Labels := by
      have hz : ∀ j, raw20025step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20025step1 = (fun i j => raw20025step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20025step1 raw20025step0; decide +kernel
      have hl : raw20025step1Labels = raw20025step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20025step0 raw20025step0Labels permutation80 hz
    mixedMoment B raw20025step1 raw20025step1Labels = mixedMoment B raw20025step2 raw20025step2Labels := by
      have hz : ∀ j, raw20025step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20025step2 = (fun i j => raw20025step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20025step2 raw20025step1; decide +kernel
      have hl : raw20025step2Labels = raw20025step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20025step1 raw20025step1Labels permutation14 hz
    mixedMoment B raw20025step2 raw20025step2Labels = mixedMoment B raw20025step3 raw20025step3Labels := by
      have ha : raw20025step3 = (fun i j => raw20025step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20025step3 raw20025step2; decide +kernel
      have hl : raw20025step3Labels = raw20025step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20025step2 raw20025step2Labels permutation7 permutation7
    mixedMoment B raw20025step3 raw20025step3Labels = mixedMoment B raw20025step4 raw20025step4Labels := by
      have ha : raw20025step4 = raw20025step3 := by apply Matrix.ext; unfold raw20025step4 raw20025step3; decide +kernel
      have hl : raw20025step3Labels = labelEmbedding1 ∘ raw20025step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20025step3 raw20025step3Labels raw20025step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1077 node1077Labels := by rfl

theorem canonical20026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20026 raw20026Labels = mixedMoment B node686 node686Labels := by
  calc
    mixedMoment B raw20026 raw20026Labels = mixedMoment B raw20026step0 raw20026step0Labels := by
      have hz : ∀ j, raw20026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20026step0 = (fun i j => raw20026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20026step0 raw20026; decide +kernel
      have hl : raw20026step0Labels = raw20026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20026 raw20026Labels permutation434 hz
    mixedMoment B raw20026step0 raw20026step0Labels = mixedMoment B raw20026step1 raw20026step1Labels := by
      have hz : ∀ j, raw20026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20026step1 = (fun i j => raw20026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20026step1 raw20026step0; decide +kernel
      have hl : raw20026step1Labels = raw20026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20026step0 raw20026step0Labels permutation80 hz
    mixedMoment B raw20026step1 raw20026step1Labels = mixedMoment B raw20026step2 raw20026step2Labels := by
      have hz : ∀ j, raw20026step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20026step2 = (fun i j => raw20026step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20026step2 raw20026step1; decide +kernel
      have hl : raw20026step2Labels = raw20026step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20026step1 raw20026step1Labels permutation14 hz
    mixedMoment B raw20026step2 raw20026step2Labels = mixedMoment B raw20026step3 raw20026step3Labels := by
      have ha : raw20026step3 = (fun i j => raw20026step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20026step3 raw20026step2; decide +kernel
      have hl : raw20026step3Labels = raw20026step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20026step2 raw20026step2Labels permutation7 permutation7
    mixedMoment B raw20026step3 raw20026step3Labels = mixedMoment B raw20026step4 raw20026step4Labels := by
      have ha : raw20026step4 = raw20026step3 := by apply Matrix.ext; unfold raw20026step4 raw20026step3; decide +kernel
      have hl : raw20026step3Labels = labelEmbedding1 ∘ raw20026step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20026step3 raw20026step3Labels raw20026step4Labels labelEmbedding1 hl
    _ = mixedMoment B node686 node686Labels := by rfl

theorem canonical20027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20027 raw20027Labels = mixedMoment B node665 node665Labels := by
  calc
    mixedMoment B raw20027 raw20027Labels = mixedMoment B raw20027step0 raw20027step0Labels := by
      have hz : ∀ j, raw20027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20027step0 = (fun i j => raw20027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20027step0 raw20027; decide +kernel
      have hl : raw20027step0Labels = raw20027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20027 raw20027Labels permutation434 hz
    mixedMoment B raw20027step0 raw20027step0Labels = mixedMoment B raw20027step1 raw20027step1Labels := by
      have hz : ∀ j, raw20027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20027step1 = (fun i j => raw20027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20027step1 raw20027step0; decide +kernel
      have hl : raw20027step1Labels = raw20027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20027step0 raw20027step0Labels permutation80 hz
    mixedMoment B raw20027step1 raw20027step1Labels = mixedMoment B raw20027step2 raw20027step2Labels := by
      have ha : raw20027step2 = (fun i j => raw20027step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20027step2 raw20027step1; decide +kernel
      have hl : raw20027step2Labels = raw20027step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20027step1 raw20027step1Labels permutation29 permutation7
    mixedMoment B raw20027step2 raw20027step2Labels = mixedMoment B raw20027step3 raw20027step3Labels := by
      have ha : raw20027step3 = raw20027step2 := by apply Matrix.ext; unfold raw20027step3 raw20027step2; decide +kernel
      have hl : raw20027step2Labels = labelEmbedding1 ∘ raw20027step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20027step2 raw20027step2Labels raw20027step3Labels labelEmbedding1 hl
    _ = mixedMoment B node665 node665Labels := by rfl

theorem canonical20028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20028 raw20028Labels = mixedMoment B node665 node665Labels := by
  calc
    mixedMoment B raw20028 raw20028Labels = mixedMoment B raw20028step0 raw20028step0Labels := by
      have hz : ∀ j, raw20028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20028step0 = (fun i j => raw20028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20028step0 raw20028; decide +kernel
      have hl : raw20028step0Labels = raw20028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20028 raw20028Labels permutation434 hz
    mixedMoment B raw20028step0 raw20028step0Labels = mixedMoment B raw20028step1 raw20028step1Labels := by
      have hz : ∀ j, raw20028step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20028step1 = (fun i j => raw20028step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20028step1 raw20028step0; decide +kernel
      have hl : raw20028step1Labels = raw20028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20028step0 raw20028step0Labels permutation56 hz
    mixedMoment B raw20028step1 raw20028step1Labels = mixedMoment B raw20028step2 raw20028step2Labels := by
      have ha : raw20028step2 = (fun i j => raw20028step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20028step2 raw20028step1; decide +kernel
      have hl : raw20028step2Labels = raw20028step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20028step1 raw20028step1Labels permutation29 permutation7
    mixedMoment B raw20028step2 raw20028step2Labels = mixedMoment B raw20028step3 raw20028step3Labels := by
      have ha : raw20028step3 = raw20028step2 := by apply Matrix.ext; unfold raw20028step3 raw20028step2; decide +kernel
      have hl : raw20028step2Labels = labelEmbedding1 ∘ raw20028step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20028step2 raw20028step2Labels raw20028step3Labels labelEmbedding1 hl
    _ = mixedMoment B node665 node665Labels := by rfl

theorem canonical20029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20029 raw20029Labels = mixedMoment B node665 node665Labels := by
  calc
    mixedMoment B raw20029 raw20029Labels = mixedMoment B raw20029step0 raw20029step0Labels := by
      have hz : ∀ j, raw20029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20029step0 = (fun i j => raw20029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20029step0 raw20029; decide +kernel
      have hl : raw20029step0Labels = raw20029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20029 raw20029Labels permutation346 hz
    mixedMoment B raw20029step0 raw20029step0Labels = mixedMoment B raw20029step1 raw20029step1Labels := by
      have hz : ∀ j, raw20029step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20029step1 = (fun i j => raw20029step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20029step1 raw20029step0; decide +kernel
      have hl : raw20029step1Labels = raw20029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20029step0 raw20029step0Labels permutation56 hz
    mixedMoment B raw20029step1 raw20029step1Labels = mixedMoment B raw20029step2 raw20029step2Labels := by
      have ha : raw20029step2 = (fun i j => raw20029step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20029step2 raw20029step1; decide +kernel
      have hl : raw20029step2Labels = raw20029step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20029step1 raw20029step1Labels permutation29 permutation7
    mixedMoment B raw20029step2 raw20029step2Labels = mixedMoment B raw20029step3 raw20029step3Labels := by
      have ha : raw20029step3 = raw20029step2 := by apply Matrix.ext; unfold raw20029step3 raw20029step2; decide +kernel
      have hl : raw20029step2Labels = labelEmbedding1 ∘ raw20029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20029step2 raw20029step2Labels raw20029step3Labels labelEmbedding1 hl
    _ = mixedMoment B node665 node665Labels := by rfl

theorem canonical20030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20030 raw20030Labels = mixedMoment B node691 node691Labels := by
  calc
    mixedMoment B raw20030 raw20030Labels = mixedMoment B raw20030step0 raw20030step0Labels := by
      have hz : ∀ j, raw20030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20030step0 = (fun i j => raw20030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20030step0 raw20030; decide +kernel
      have hl : raw20030step0Labels = raw20030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20030 raw20030Labels permutation434 hz
    mixedMoment B raw20030step0 raw20030step0Labels = mixedMoment B raw20030step1 raw20030step1Labels := by
      have hz : ∀ j, raw20030step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20030step1 = (fun i j => raw20030step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20030step1 raw20030step0; decide +kernel
      have hl : raw20030step1Labels = raw20030step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20030step0 raw20030step0Labels permutation80 hz
    mixedMoment B raw20030step1 raw20030step1Labels = mixedMoment B raw20030step2 raw20030step2Labels := by
      have hz : ∀ j, raw20030step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20030step2 = (fun i j => raw20030step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20030step2 raw20030step1; decide +kernel
      have hl : raw20030step2Labels = raw20030step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20030step1 raw20030step1Labels permutation14 hz
    mixedMoment B raw20030step2 raw20030step2Labels = mixedMoment B raw20030step3 raw20030step3Labels := by
      have ha : raw20030step3 = (fun i j => raw20030step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20030step3 raw20030step2; decide +kernel
      have hl : raw20030step3Labels = raw20030step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20030step2 raw20030step2Labels permutation7 permutation7
    mixedMoment B raw20030step3 raw20030step3Labels = mixedMoment B raw20030step4 raw20030step4Labels := by
      have ha : raw20030step4 = raw20030step3 := by apply Matrix.ext; unfold raw20030step4 raw20030step3; decide +kernel
      have hl : raw20030step3Labels = labelEmbedding1 ∘ raw20030step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20030step3 raw20030step3Labels raw20030step4Labels labelEmbedding1 hl
    _ = mixedMoment B node691 node691Labels := by rfl

theorem canonical20031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20031 raw20031Labels = mixedMoment B node817 node817Labels := by
  calc
    mixedMoment B raw20031 raw20031Labels = mixedMoment B raw20031step0 raw20031step0Labels := by
      have hz : ∀ j, raw20031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20031step0 = (fun i j => raw20031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20031step0 raw20031; decide +kernel
      have hl : raw20031step0Labels = raw20031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20031 raw20031Labels permutation434 hz
    mixedMoment B raw20031step0 raw20031step0Labels = mixedMoment B raw20031step1 raw20031step1Labels := by
      have hz : ∀ j, raw20031step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20031step1 = (fun i j => raw20031step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20031step1 raw20031step0; decide +kernel
      have hl : raw20031step1Labels = raw20031step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20031step0 raw20031step0Labels permutation80 hz
    mixedMoment B raw20031step1 raw20031step1Labels = mixedMoment B raw20031step2 raw20031step2Labels := by
      have hz : ∀ j, raw20031step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20031step2 = (fun i j => raw20031step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20031step2 raw20031step1; decide +kernel
      have hl : raw20031step2Labels = raw20031step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20031step1 raw20031step1Labels permutation14 hz
    mixedMoment B raw20031step2 raw20031step2Labels = mixedMoment B raw20031step3 raw20031step3Labels := by
      have ha : raw20031step3 = (fun i j => raw20031step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20031step3 raw20031step2; decide +kernel
      have hl : raw20031step3Labels = raw20031step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20031step2 raw20031step2Labels permutation7 permutation2
    mixedMoment B raw20031step3 raw20031step3Labels = mixedMoment B raw20031step4 raw20031step4Labels := by
      have ha : raw20031step4 = -raw20031step3 := by apply Matrix.ext; change ∀ i j, raw20031step4 i j = -(raw20031step3 i j); unfold raw20031step4 raw20031step3; decide +kernel
      have hl : raw20031step4Labels = raw20031step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node817 node817Labels := by rfl

theorem canonical20032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20032 raw20032Labels = mixedMoment B node570 node570Labels := by
  calc
    mixedMoment B raw20032 raw20032Labels = mixedMoment B raw20032step0 raw20032step0Labels := by
      have hz : ∀ j, raw20032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20032step0 = (fun i j => raw20032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20032step0 raw20032; decide +kernel
      have hl : raw20032step0Labels = raw20032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20032 raw20032Labels permutation434 hz
    mixedMoment B raw20032step0 raw20032step0Labels = mixedMoment B raw20032step1 raw20032step1Labels := by
      have hz : ∀ j, raw20032step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20032step1 = (fun i j => raw20032step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20032step1 raw20032step0; decide +kernel
      have hl : raw20032step1Labels = raw20032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20032step0 raw20032step0Labels permutation80 hz
    mixedMoment B raw20032step1 raw20032step1Labels = mixedMoment B raw20032step2 raw20032step2Labels := by
      have ha : raw20032step2 = (fun i j => raw20032step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20032step2 raw20032step1; decide +kernel
      have hl : raw20032step2Labels = raw20032step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20032step1 raw20032step1Labels permutation10 permutation2
    _ = mixedMoment B node570 node570Labels := by rfl

theorem canonical20033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20033 raw20033Labels = mixedMoment B node570 node570Labels := by
  calc
    mixedMoment B raw20033 raw20033Labels = mixedMoment B raw20033step0 raw20033step0Labels := by
      have hz : ∀ j, raw20033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20033step0 = (fun i j => raw20033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20033step0 raw20033; decide +kernel
      have hl : raw20033step0Labels = raw20033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20033 raw20033Labels permutation434 hz
    mixedMoment B raw20033step0 raw20033step0Labels = mixedMoment B raw20033step1 raw20033step1Labels := by
      have hz : ∀ j, raw20033step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20033step1 = (fun i j => raw20033step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20033step1 raw20033step0; decide +kernel
      have hl : raw20033step1Labels = raw20033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20033step0 raw20033step0Labels permutation56 hz
    mixedMoment B raw20033step1 raw20033step1Labels = mixedMoment B raw20033step2 raw20033step2Labels := by
      have ha : raw20033step2 = (fun i j => raw20033step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20033step2 raw20033step1; decide +kernel
      have hl : raw20033step2Labels = raw20033step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20033step1 raw20033step1Labels permutation10 permutation2
    _ = mixedMoment B node570 node570Labels := by rfl

theorem canonical20034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20034 raw20034Labels = mixedMoment B node570 node570Labels := by
  calc
    mixedMoment B raw20034 raw20034Labels = mixedMoment B raw20034step0 raw20034step0Labels := by
      have hz : ∀ j, raw20034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20034step0 = (fun i j => raw20034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20034step0 raw20034; decide +kernel
      have hl : raw20034step0Labels = raw20034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20034 raw20034Labels permutation346 hz
    mixedMoment B raw20034step0 raw20034step0Labels = mixedMoment B raw20034step1 raw20034step1Labels := by
      have hz : ∀ j, raw20034step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20034step1 = (fun i j => raw20034step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20034step1 raw20034step0; decide +kernel
      have hl : raw20034step1Labels = raw20034step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20034step0 raw20034step0Labels permutation56 hz
    mixedMoment B raw20034step1 raw20034step1Labels = mixedMoment B raw20034step2 raw20034step2Labels := by
      have ha : raw20034step2 = (fun i j => raw20034step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20034step2 raw20034step1; decide +kernel
      have hl : raw20034step2Labels = raw20034step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20034step1 raw20034step1Labels permutation10 permutation2
    _ = mixedMoment B node570 node570Labels := by rfl

theorem canonical20035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20035 raw20035Labels = mixedMoment B node596 node596Labels := by
  calc
    mixedMoment B raw20035 raw20035Labels = mixedMoment B raw20035step0 raw20035step0Labels := by
      have hz : ∀ j, raw20035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20035step0 = (fun i j => raw20035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20035step0 raw20035; decide +kernel
      have hl : raw20035step0Labels = raw20035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20035 raw20035Labels permutation434 hz
    mixedMoment B raw20035step0 raw20035step0Labels = mixedMoment B raw20035step1 raw20035step1Labels := by
      have hz : ∀ j, raw20035step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20035step1 = (fun i j => raw20035step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20035step1 raw20035step0; decide +kernel
      have hl : raw20035step1Labels = raw20035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20035step0 raw20035step0Labels permutation80 hz
    mixedMoment B raw20035step1 raw20035step1Labels = mixedMoment B raw20035step2 raw20035step2Labels := by
      have hz : ∀ j, raw20035step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20035step2 = (fun i j => raw20035step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20035step2 raw20035step1; decide +kernel
      have hl : raw20035step2Labels = raw20035step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20035step1 raw20035step1Labels permutation14 hz
    _ = mixedMoment B node596 node596Labels := by rfl

theorem canonical20036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20036 raw20036Labels = mixedMoment B node549 node549Labels := by
  calc
    mixedMoment B raw20036 raw20036Labels = mixedMoment B raw20036step0 raw20036step0Labels := by
      have hz : ∀ j, raw20036 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20036step0 = (fun i j => raw20036 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20036step0 raw20036; decide +kernel
      have hl : raw20036step0Labels = raw20036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20036 raw20036Labels permutation434 hz
    mixedMoment B raw20036step0 raw20036step0Labels = mixedMoment B raw20036step1 raw20036step1Labels := by
      have hz : ∀ j, raw20036step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20036step1 = (fun i j => raw20036step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20036step1 raw20036step0; decide +kernel
      have hl : raw20036step1Labels = raw20036step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20036step0 raw20036step0Labels permutation80 hz
    mixedMoment B raw20036step1 raw20036step1Labels = mixedMoment B raw20036step2 raw20036step2Labels := by
      have hz : ∀ j, raw20036step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20036step2 = (fun i j => raw20036step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20036step2 raw20036step1; decide +kernel
      have hl : raw20036step2Labels = raw20036step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20036step1 raw20036step1Labels permutation14 hz
    mixedMoment B raw20036step2 raw20036step2Labels = mixedMoment B raw20036step3 raw20036step3Labels := by
      have ha : raw20036step3 = (fun i j => raw20036step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20036step3 raw20036step2; decide +kernel
      have hl : raw20036step3Labels = raw20036step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20036step2 raw20036step2Labels permutation7 permutation2
    mixedMoment B raw20036step3 raw20036step3Labels = mixedMoment B raw20036step4 raw20036step4Labels := by
      have ha : raw20036step4 = -raw20036step3 := by apply Matrix.ext; change ∀ i j, raw20036step4 i j = -(raw20036step3 i j); unfold raw20036step4 raw20036step3; decide +kernel
      have hl : raw20036step4Labels = raw20036step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node549 node549Labels := by rfl

theorem canonical20037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20037 raw20037Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw20037 raw20037Labels = mixedMoment B raw20037step0 raw20037step0Labels := by
      have hz : ∀ j, raw20037 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20037step0 = (fun i j => raw20037 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20037step0 raw20037; decide +kernel
      have hl : raw20037step0Labels = raw20037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20037 raw20037Labels permutation434 hz
    mixedMoment B raw20037step0 raw20037step0Labels = mixedMoment B raw20037step1 raw20037step1Labels := by
      have hz : ∀ j, raw20037step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20037step1 = (fun i j => raw20037step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20037step1 raw20037step0; decide +kernel
      have hl : raw20037step1Labels = raw20037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20037step0 raw20037step0Labels permutation80 hz
    mixedMoment B raw20037step1 raw20037step1Labels = mixedMoment B raw20037step2 raw20037step2Labels := by
      have hz : ∀ j, raw20037step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20037step2 = (fun i j => raw20037step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20037step2 raw20037step1; decide +kernel
      have hl : raw20037step2Labels = raw20037step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20037step1 raw20037step1Labels permutation14 hz
    mixedMoment B raw20037step2 raw20037step2Labels = mixedMoment B raw20037step3 raw20037step3Labels := by
      have ha : raw20037step3 = (fun i j => raw20037step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20037step3 raw20037step2; decide +kernel
      have hl : raw20037step3Labels = raw20037step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20037step2 raw20037step2Labels permutation7 permutation0
    mixedMoment B raw20037step3 raw20037step3Labels = mixedMoment B raw20037step4 raw20037step4Labels := by
      have ha : raw20037step4 = -raw20037step3 := by apply Matrix.ext; change ∀ i j, raw20037step4 i j = -(raw20037step3 i j); unfold raw20037step4 raw20037step3; decide +kernel
      have hl : raw20037step4Labels = raw20037step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical20042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20042 raw20042Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw20042 raw20042Labels = mixedMoment B raw20042step0 raw20042step0Labels := by
      have hz : ∀ j, raw20042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20042step0 = (fun i j => raw20042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20042step0 raw20042; decide +kernel
      have hl : raw20042step0Labels = raw20042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20042 raw20042Labels permutation434 hz
    mixedMoment B raw20042step0 raw20042step0Labels = mixedMoment B raw20042step1 raw20042step1Labels := by
      have hz : ∀ j, raw20042step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20042step1 = (fun i j => raw20042step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20042step1 raw20042step0; decide +kernel
      have hl : raw20042step1Labels = raw20042step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20042step0 raw20042step0Labels permutation80 hz
    mixedMoment B raw20042step1 raw20042step1Labels = mixedMoment B raw20042step2 raw20042step2Labels := by
      have ha : raw20042step2 = (fun i j => raw20042step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20042step2 raw20042step1; decide +kernel
      have hl : raw20042step2Labels = raw20042step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20042step1 raw20042step1Labels permutation31 permutation2
    mixedMoment B raw20042step2 raw20042step2Labels = mixedMoment B raw20042step3 raw20042step3Labels := by
      have ha : raw20042step3 = -raw20042step2 := by apply Matrix.ext; change ∀ i j, raw20042step3 i j = -(raw20042step2 i j); unfold raw20042step3 raw20042step2; decide +kernel
      have hl : raw20042step3Labels = raw20042step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node809 node809Labels := by rfl

theorem canonical20043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20043 raw20043Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw20043 raw20043Labels = mixedMoment B raw20043step0 raw20043step0Labels := by
      have hz : ∀ j, raw20043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20043step0 = (fun i j => raw20043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20043step0 raw20043; decide +kernel
      have hl : raw20043step0Labels = raw20043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20043 raw20043Labels permutation434 hz
    mixedMoment B raw20043step0 raw20043step0Labels = mixedMoment B raw20043step1 raw20043step1Labels := by
      have ha : raw20043step1 = (fun i j => raw20043step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20043step1 raw20043step0; decide +kernel
      have hl : raw20043step1Labels = raw20043step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20043step0 raw20043step0Labels permutation145 permutation2
    mixedMoment B raw20043step1 raw20043step1Labels = mixedMoment B raw20043step2 raw20043step2Labels := by
      have ha : raw20043step2 = -raw20043step1 := by apply Matrix.ext; change ∀ i j, raw20043step2 i j = -(raw20043step1 i j); unfold raw20043step2 raw20043step1; decide +kernel
      have hl : raw20043step2Labels = raw20043step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node701 node701Labels := by rfl

theorem canonical20044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20044 raw20044Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw20044 raw20044Labels = mixedMoment B raw20044step0 raw20044step0Labels := by
      have hz : ∀ j, raw20044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20044step0 = (fun i j => raw20044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20044step0 raw20044; decide +kernel
      have hl : raw20044step0Labels = raw20044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20044 raw20044Labels permutation346 hz
    mixedMoment B raw20044step0 raw20044step0Labels = mixedMoment B raw20044step1 raw20044step1Labels := by
      have ha : raw20044step1 = (fun i j => raw20044step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20044step1 raw20044step0; decide +kernel
      have hl : raw20044step1Labels = raw20044step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20044step0 raw20044step0Labels permutation145 permutation2
    mixedMoment B raw20044step1 raw20044step1Labels = mixedMoment B raw20044step2 raw20044step2Labels := by
      have ha : raw20044step2 = -raw20044step1 := by apply Matrix.ext; change ∀ i j, raw20044step2 i j = -(raw20044step1 i j); unfold raw20044step2 raw20044step1; decide +kernel
      have hl : raw20044step2Labels = raw20044step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node701 node701Labels := by rfl

theorem canonical20045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20045 raw20045Labels = mixedMoment B node735 node735Labels := by
  calc
    mixedMoment B raw20045 raw20045Labels = mixedMoment B raw20045step0 raw20045step0Labels := by
      have hz : ∀ j, raw20045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20045step0 = (fun i j => raw20045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20045step0 raw20045; decide +kernel
      have hl : raw20045step0Labels = raw20045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20045 raw20045Labels permutation434 hz
    mixedMoment B raw20045step0 raw20045step0Labels = mixedMoment B raw20045step1 raw20045step1Labels := by
      have hz : ∀ j, raw20045step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20045step1 = (fun i j => raw20045step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20045step1 raw20045step0; decide +kernel
      have hl : raw20045step1Labels = raw20045step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20045step0 raw20045step0Labels permutation80 hz
    mixedMoment B raw20045step1 raw20045step1Labels = mixedMoment B raw20045step2 raw20045step2Labels := by
      have ha : raw20045step2 = (fun i j => raw20045step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20045step2 raw20045step1; decide +kernel
      have hl : raw20045step2Labels = raw20045step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20045step1 raw20045step1Labels permutation31 permutation2
    mixedMoment B raw20045step2 raw20045step2Labels = mixedMoment B raw20045step3 raw20045step3Labels := by
      have ha : raw20045step3 = -raw20045step2 := by apply Matrix.ext; change ∀ i j, raw20045step3 i j = -(raw20045step2 i j); unfold raw20045step3 raw20045step2; decide +kernel
      have hl : raw20045step3Labels = raw20045step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node735 node735Labels := by rfl

theorem canonical20046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20046 raw20046Labels = mixedMoment B node540 node540Labels := by
  calc
    mixedMoment B raw20046 raw20046Labels = mixedMoment B raw20046step0 raw20046step0Labels := by
      have hz : ∀ j, raw20046 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20046step0 = (fun i j => raw20046 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20046step0 raw20046; decide +kernel
      have hl : raw20046step0Labels = raw20046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20046 raw20046Labels permutation434 hz
    mixedMoment B raw20046step0 raw20046step0Labels = mixedMoment B raw20046step1 raw20046step1Labels := by
      have hz : ∀ j, raw20046step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20046step1 = (fun i j => raw20046step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20046step1 raw20046step0; decide +kernel
      have hl : raw20046step1Labels = raw20046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20046step0 raw20046step0Labels permutation80 hz
    mixedMoment B raw20046step1 raw20046step1Labels = mixedMoment B raw20046step2 raw20046step2Labels := by
      have ha : raw20046step2 = (fun i j => raw20046step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20046step2 raw20046step1; decide +kernel
      have hl : raw20046step2Labels = raw20046step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20046step1 raw20046step1Labels permutation31 permutation2
    mixedMoment B raw20046step2 raw20046step2Labels = mixedMoment B raw20046step3 raw20046step3Labels := by
      have ha : raw20046step3 = -raw20046step2 := by apply Matrix.ext; change ∀ i j, raw20046step3 i j = -(raw20046step2 i j); unfold raw20046step3 raw20046step2; decide +kernel
      have hl : raw20046step3Labels = raw20046step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node540 node540Labels := by rfl

theorem canonical20047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20047 raw20047Labels = mixedMoment B node735 node735Labels := by
  calc
    mixedMoment B raw20047 raw20047Labels = mixedMoment B raw20047step0 raw20047step0Labels := by
      have hz : ∀ j, raw20047 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20047step0 = (fun i j => raw20047 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20047step0 raw20047; decide +kernel
      have hl : raw20047step0Labels = raw20047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20047 raw20047Labels permutation434 hz
    mixedMoment B raw20047step0 raw20047step0Labels = mixedMoment B raw20047step1 raw20047step1Labels := by
      have hz : ∀ j, raw20047step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20047step1 = (fun i j => raw20047step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20047step1 raw20047step0; decide +kernel
      have hl : raw20047step1Labels = raw20047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20047step0 raw20047step0Labels permutation56 hz
    mixedMoment B raw20047step1 raw20047step1Labels = mixedMoment B raw20047step2 raw20047step2Labels := by
      have ha : raw20047step2 = (fun i j => raw20047step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20047step2 raw20047step1; decide +kernel
      have hl : raw20047step2Labels = raw20047step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20047step1 raw20047step1Labels permutation31 permutation2
    mixedMoment B raw20047step2 raw20047step2Labels = mixedMoment B raw20047step3 raw20047step3Labels := by
      have ha : raw20047step3 = -raw20047step2 := by apply Matrix.ext; change ∀ i j, raw20047step3 i j = -(raw20047step2 i j); unfold raw20047step3 raw20047step2; decide +kernel
      have hl : raw20047step3Labels = raw20047step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node735 node735Labels := by rfl

theorem canonical20048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20048 raw20048Labels = mixedMoment B node735 node735Labels := by
  calc
    mixedMoment B raw20048 raw20048Labels = mixedMoment B raw20048step0 raw20048step0Labels := by
      have hz : ∀ j, raw20048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20048step0 = (fun i j => raw20048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20048step0 raw20048; decide +kernel
      have hl : raw20048step0Labels = raw20048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20048 raw20048Labels permutation346 hz
    mixedMoment B raw20048step0 raw20048step0Labels = mixedMoment B raw20048step1 raw20048step1Labels := by
      have hz : ∀ j, raw20048step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20048step1 = (fun i j => raw20048step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20048step1 raw20048step0; decide +kernel
      have hl : raw20048step1Labels = raw20048step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20048step0 raw20048step0Labels permutation56 hz
    mixedMoment B raw20048step1 raw20048step1Labels = mixedMoment B raw20048step2 raw20048step2Labels := by
      have ha : raw20048step2 = (fun i j => raw20048step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20048step2 raw20048step1; decide +kernel
      have hl : raw20048step2Labels = raw20048step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20048step1 raw20048step1Labels permutation31 permutation2
    mixedMoment B raw20048step2 raw20048step2Labels = mixedMoment B raw20048step3 raw20048step3Labels := by
      have ha : raw20048step3 = -raw20048step2 := by apply Matrix.ext; change ∀ i j, raw20048step3 i j = -(raw20048step2 i j); unfold raw20048step3 raw20048step2; decide +kernel
      have hl : raw20048step3Labels = raw20048step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node735 node735Labels := by rfl

theorem canonical20049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20049 raw20049Labels = mixedMoment B node1077 node1077Labels := by
  calc
    mixedMoment B raw20049 raw20049Labels = mixedMoment B raw20049step0 raw20049step0Labels := by
      have hz : ∀ j, raw20049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20049step0 = (fun i j => raw20049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20049step0 raw20049; decide +kernel
      have hl : raw20049step0Labels = raw20049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20049 raw20049Labels permutation434 hz
    mixedMoment B raw20049step0 raw20049step0Labels = mixedMoment B raw20049step1 raw20049step1Labels := by
      have hz : ∀ j, raw20049step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20049step1 = (fun i j => raw20049step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20049step1 raw20049step0; decide +kernel
      have hl : raw20049step1Labels = raw20049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20049step0 raw20049step0Labels permutation80 hz
    mixedMoment B raw20049step1 raw20049step1Labels = mixedMoment B raw20049step2 raw20049step2Labels := by
      have hz : ∀ j, raw20049step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20049step2 = (fun i j => raw20049step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20049step2 raw20049step1; decide +kernel
      have hl : raw20049step2Labels = raw20049step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20049step1 raw20049step1Labels permutation14 hz
    _ = mixedMoment B node1077 node1077Labels := by rfl

theorem canonical20067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20067 raw20067Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20067 raw20067Labels = mixedMoment B raw20067step0 raw20067step0Labels := by
      have hz : ∀ j, raw20067 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20067step0 = (fun i j => raw20067 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20067step0 raw20067; decide +kernel
      have hl : raw20067step0Labels = raw20067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20067 raw20067Labels permutation520 hz
    mixedMoment B raw20067step0 raw20067step0Labels = mixedMoment B raw20067step1 raw20067step1Labels := by
      have hz : ∀ j, raw20067step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20067step1 = (fun i j => raw20067step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20067step1 raw20067step0; decide +kernel
      have hl : raw20067step1Labels = raw20067step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20067step0 raw20067step0Labels permutation104 hz
    mixedMoment B raw20067step1 raw20067step1Labels = mixedMoment B raw20067step2 raw20067step2Labels := by
      have hz : ∀ j, raw20067step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw20067step2 = (fun i j => raw20067step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw20067step2 raw20067step1; decide +kernel
      have hl : raw20067step2Labels = raw20067step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20067step1 raw20067step1Labels permutation20 hz
    mixedMoment B raw20067step2 raw20067step2Labels = mixedMoment B raw20067step3 raw20067step3Labels := by
      have hz : ∀ i, raw20067step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20067step3 = (fun i j => raw20067step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20067step3 raw20067step2; decide +kernel
      have hl : raw20067step3Labels = (fun j => raw20067step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20067step2 raw20067step2Labels permutation6 hz
    _ = mixedMoment B node4060 node4060Labels := by rfl

theorem canonical20068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20068 raw20068Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20068 raw20068Labels = mixedMoment B raw20068step0 raw20068step0Labels := by
      have hz : ∀ j, raw20068 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20068step0 = (fun i j => raw20068 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20068step0 raw20068; decide +kernel
      have hl : raw20068step0Labels = raw20068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20068 raw20068Labels permutation520 hz
    mixedMoment B raw20068step0 raw20068step0Labels = mixedMoment B raw20068step1 raw20068step1Labels := by
      have hz : ∀ j, raw20068step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20068step1 = (fun i j => raw20068step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20068step1 raw20068step0; decide +kernel
      have hl : raw20068step1Labels = raw20068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20068step0 raw20068step0Labels permutation104 hz
    mixedMoment B raw20068step1 raw20068step1Labels = mixedMoment B raw20068step2 raw20068step2Labels := by
      have hz : ∀ i, raw20068step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20068step2 = (fun i j => raw20068step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20068step2 raw20068step1; decide +kernel
      have hl : raw20068step2Labels = (fun j => raw20068step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20068step1 raw20068step1Labels permutation6 hz
    mixedMoment B raw20068step2 raw20068step2Labels = mixedMoment B raw20068step3 raw20068step3Labels := by
      have ha : raw20068step3 = (fun i j => raw20068step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20068step3 raw20068step2; decide +kernel
      have hl : raw20068step3Labels = raw20068step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20068step2 raw20068step2Labels permutation10 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20069 raw20069Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20069 raw20069Labels = mixedMoment B raw20069step0 raw20069step0Labels := by
      have hz : ∀ j, raw20069 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20069step0 = (fun i j => raw20069 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20069step0 raw20069; decide +kernel
      have hl : raw20069step0Labels = raw20069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20069 raw20069Labels permutation520 hz
    mixedMoment B raw20069step0 raw20069step0Labels = mixedMoment B raw20069step1 raw20069step1Labels := by
      have hz : ∀ j, raw20069step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20069step1 = (fun i j => raw20069step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20069step1 raw20069step0; decide +kernel
      have hl : raw20069step1Labels = raw20069step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20069step0 raw20069step0Labels permutation80 hz
    mixedMoment B raw20069step1 raw20069step1Labels = mixedMoment B raw20069step2 raw20069step2Labels := by
      have hz : ∀ i, raw20069step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20069step2 = (fun i j => raw20069step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20069step2 raw20069step1; decide +kernel
      have hl : raw20069step2Labels = (fun j => raw20069step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20069step1 raw20069step1Labels permutation6 hz
    mixedMoment B raw20069step2 raw20069step2Labels = mixedMoment B raw20069step3 raw20069step3Labels := by
      have ha : raw20069step3 = (fun i j => raw20069step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20069step3 raw20069step2; decide +kernel
      have hl : raw20069step3Labels = raw20069step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20069step2 raw20069step2Labels permutation10 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20070 raw20070Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20070 raw20070Labels = mixedMoment B raw20070step0 raw20070step0Labels := by
      have hz : ∀ j, raw20070 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20070step0 = (fun i j => raw20070 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20070step0 raw20070; decide +kernel
      have hl : raw20070step0Labels = raw20070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20070 raw20070Labels permutation434 hz
    mixedMoment B raw20070step0 raw20070step0Labels = mixedMoment B raw20070step1 raw20070step1Labels := by
      have hz : ∀ j, raw20070step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20070step1 = (fun i j => raw20070step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20070step1 raw20070step0; decide +kernel
      have hl : raw20070step1Labels = raw20070step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20070step0 raw20070step0Labels permutation80 hz
    mixedMoment B raw20070step1 raw20070step1Labels = mixedMoment B raw20070step2 raw20070step2Labels := by
      have hz : ∀ i, raw20070step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20070step2 = (fun i j => raw20070step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20070step2 raw20070step1; decide +kernel
      have hl : raw20070step2Labels = (fun j => raw20070step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20070step1 raw20070step1Labels permutation6 hz
    mixedMoment B raw20070step2 raw20070step2Labels = mixedMoment B raw20070step3 raw20070step3Labels := by
      have ha : raw20070step3 = (fun i j => raw20070step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20070step3 raw20070step2; decide +kernel
      have hl : raw20070step3Labels = raw20070step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20070step2 raw20070step2Labels permutation10 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20071 raw20071Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20071 raw20071Labels = mixedMoment B raw20071step0 raw20071step0Labels := by
      have hz : ∀ j, raw20071 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20071step0 = (fun i j => raw20071 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20071step0 raw20071; decide +kernel
      have hl : raw20071step0Labels = raw20071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20071 raw20071Labels permutation520 hz
    mixedMoment B raw20071step0 raw20071step0Labels = mixedMoment B raw20071step1 raw20071step1Labels := by
      have hz : ∀ j, raw20071step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20071step1 = (fun i j => raw20071step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20071step1 raw20071step0; decide +kernel
      have hl : raw20071step1Labels = raw20071step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20071step0 raw20071step0Labels permutation104 hz
    mixedMoment B raw20071step1 raw20071step1Labels = mixedMoment B raw20071step2 raw20071step2Labels := by
      have hz : ∀ j, raw20071step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20071step2 = (fun i j => raw20071step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20071step2 raw20071step1; decide +kernel
      have hl : raw20071step2Labels = raw20071step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20071step1 raw20071step1Labels permutation14 hz
    mixedMoment B raw20071step2 raw20071step2Labels = mixedMoment B raw20071step3 raw20071step3Labels := by
      have hz : ∀ i, raw20071step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20071step3 = (fun i j => raw20071step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20071step3 raw20071step2; decide +kernel
      have hl : raw20071step3Labels = (fun j => raw20071step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20071step2 raw20071step2Labels permutation6 hz
    _ = mixedMoment B node4060 node4060Labels := by rfl

theorem canonical20072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20072 raw20072Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20072 raw20072Labels = mixedMoment B raw20072step0 raw20072step0Labels := by
      have hz : ∀ j, raw20072 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20072step0 = (fun i j => raw20072 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20072step0 raw20072; decide +kernel
      have hl : raw20072step0Labels = raw20072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20072 raw20072Labels permutation520 hz
    mixedMoment B raw20072step0 raw20072step0Labels = mixedMoment B raw20072step1 raw20072step1Labels := by
      have hz : ∀ j, raw20072step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20072step1 = (fun i j => raw20072step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20072step1 raw20072step0; decide +kernel
      have hl : raw20072step1Labels = raw20072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20072step0 raw20072step0Labels permutation104 hz
    mixedMoment B raw20072step1 raw20072step1Labels = mixedMoment B raw20072step2 raw20072step2Labels := by
      have hz : ∀ i, raw20072step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20072step2 = (fun i j => raw20072step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20072step2 raw20072step1; decide +kernel
      have hl : raw20072step2Labels = (fun j => raw20072step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20072step1 raw20072step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20073 raw20073Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20073 raw20073Labels = mixedMoment B raw20073step0 raw20073step0Labels := by
      have hz : ∀ j, raw20073 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20073step0 = (fun i j => raw20073 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20073step0 raw20073; decide +kernel
      have hl : raw20073step0Labels = raw20073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20073 raw20073Labels permutation520 hz
    mixedMoment B raw20073step0 raw20073step0Labels = mixedMoment B raw20073step1 raw20073step1Labels := by
      have hz : ∀ j, raw20073step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20073step1 = (fun i j => raw20073step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20073step1 raw20073step0; decide +kernel
      have hl : raw20073step1Labels = raw20073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20073step0 raw20073step0Labels permutation56 hz
    mixedMoment B raw20073step1 raw20073step1Labels = mixedMoment B raw20073step2 raw20073step2Labels := by
      have hz : ∀ i, raw20073step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20073step2 = (fun i j => raw20073step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20073step2 raw20073step1; decide +kernel
      have hl : raw20073step2Labels = (fun j => raw20073step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20073step1 raw20073step1Labels permutation6 hz
    mixedMoment B raw20073step2 raw20073step2Labels = mixedMoment B raw20073step3 raw20073step3Labels := by
      have ha : raw20073step3 = (fun i j => raw20073step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20073step3 raw20073step2; decide +kernel
      have hl : raw20073step3Labels = raw20073step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20073step2 raw20073step2Labels permutation10 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20074 raw20074Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20074 raw20074Labels = mixedMoment B raw20074step0 raw20074step0Labels := by
      have hz : ∀ j, raw20074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20074step0 = (fun i j => raw20074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20074step0 raw20074; decide +kernel
      have hl : raw20074step0Labels = raw20074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20074 raw20074Labels permutation434 hz
    mixedMoment B raw20074step0 raw20074step0Labels = mixedMoment B raw20074step1 raw20074step1Labels := by
      have hz : ∀ j, raw20074step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20074step1 = (fun i j => raw20074step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20074step1 raw20074step0; decide +kernel
      have hl : raw20074step1Labels = raw20074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20074step0 raw20074step0Labels permutation56 hz
    mixedMoment B raw20074step1 raw20074step1Labels = mixedMoment B raw20074step2 raw20074step2Labels := by
      have hz : ∀ i, raw20074step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20074step2 = (fun i j => raw20074step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20074step2 raw20074step1; decide +kernel
      have hl : raw20074step2Labels = (fun j => raw20074step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20074step1 raw20074step1Labels permutation6 hz
    mixedMoment B raw20074step2 raw20074step2Labels = mixedMoment B raw20074step3 raw20074step3Labels := by
      have ha : raw20074step3 = (fun i j => raw20074step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20074step3 raw20074step2; decide +kernel
      have hl : raw20074step3Labels = raw20074step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20074step2 raw20074step2Labels permutation10 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20075 raw20075Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20075 raw20075Labels = mixedMoment B raw20075step0 raw20075step0Labels := by
      have hz : ∀ j, raw20075 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20075step0 = (fun i j => raw20075 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20075step0 raw20075; decide +kernel
      have hl : raw20075step0Labels = raw20075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20075 raw20075Labels permutation520 hz
    mixedMoment B raw20075step0 raw20075step0Labels = mixedMoment B raw20075step1 raw20075step1Labels := by
      have hz : ∀ j, raw20075step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20075step1 = (fun i j => raw20075step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20075step1 raw20075step0; decide +kernel
      have hl : raw20075step1Labels = raw20075step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20075step0 raw20075step0Labels permutation80 hz
    mixedMoment B raw20075step1 raw20075step1Labels = mixedMoment B raw20075step2 raw20075step2Labels := by
      have hz : ∀ j, raw20075step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20075step2 = (fun i j => raw20075step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20075step2 raw20075step1; decide +kernel
      have hl : raw20075step2Labels = raw20075step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20075step1 raw20075step1Labels permutation14 hz
    mixedMoment B raw20075step2 raw20075step2Labels = mixedMoment B raw20075step3 raw20075step3Labels := by
      have hz : ∀ i, raw20075step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20075step3 = (fun i j => raw20075step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20075step3 raw20075step2; decide +kernel
      have hl : raw20075step3Labels = (fun j => raw20075step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20075step2 raw20075step2Labels permutation6 hz
    _ = mixedMoment B node4060 node4060Labels := by rfl

theorem canonical20076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20076 raw20076Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20076 raw20076Labels = mixedMoment B raw20076step0 raw20076step0Labels := by
      have hz : ∀ j, raw20076 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20076step0 = (fun i j => raw20076 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20076step0 raw20076; decide +kernel
      have hl : raw20076step0Labels = raw20076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20076 raw20076Labels permutation520 hz
    mixedMoment B raw20076step0 raw20076step0Labels = mixedMoment B raw20076step1 raw20076step1Labels := by
      have hz : ∀ j, raw20076step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20076step1 = (fun i j => raw20076step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20076step1 raw20076step0; decide +kernel
      have hl : raw20076step1Labels = raw20076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20076step0 raw20076step0Labels permutation80 hz
    mixedMoment B raw20076step1 raw20076step1Labels = mixedMoment B raw20076step2 raw20076step2Labels := by
      have hz : ∀ i, raw20076step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20076step2 = (fun i j => raw20076step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20076step2 raw20076step1; decide +kernel
      have hl : raw20076step2Labels = (fun j => raw20076step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20076step1 raw20076step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20077 raw20077Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20077 raw20077Labels = mixedMoment B raw20077step0 raw20077step0Labels := by
      have hz : ∀ j, raw20077 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20077step0 = (fun i j => raw20077 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20077step0 raw20077; decide +kernel
      have hl : raw20077step0Labels = raw20077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20077 raw20077Labels permutation520 hz
    mixedMoment B raw20077step0 raw20077step0Labels = mixedMoment B raw20077step1 raw20077step1Labels := by
      have hz : ∀ j, raw20077step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20077step1 = (fun i j => raw20077step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20077step1 raw20077step0; decide +kernel
      have hl : raw20077step1Labels = raw20077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20077step0 raw20077step0Labels permutation56 hz
    mixedMoment B raw20077step1 raw20077step1Labels = mixedMoment B raw20077step2 raw20077step2Labels := by
      have hz : ∀ i, raw20077step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20077step2 = (fun i j => raw20077step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20077step2 raw20077step1; decide +kernel
      have hl : raw20077step2Labels = (fun j => raw20077step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20077step1 raw20077step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20078 raw20078Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20078 raw20078Labels = mixedMoment B raw20078step0 raw20078step0Labels := by
      have hz : ∀ j, raw20078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20078step0 = (fun i j => raw20078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20078step0 raw20078; decide +kernel
      have hl : raw20078step0Labels = raw20078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20078 raw20078Labels permutation346 hz
    mixedMoment B raw20078step0 raw20078step0Labels = mixedMoment B raw20078step1 raw20078step1Labels := by
      have hz : ∀ j, raw20078step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20078step1 = (fun i j => raw20078step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20078step1 raw20078step0; decide +kernel
      have hl : raw20078step1Labels = raw20078step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20078step0 raw20078step0Labels permutation56 hz
    mixedMoment B raw20078step1 raw20078step1Labels = mixedMoment B raw20078step2 raw20078step2Labels := by
      have hz : ∀ i, raw20078step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20078step2 = (fun i j => raw20078step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20078step2 raw20078step1; decide +kernel
      have hl : raw20078step2Labels = (fun j => raw20078step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20078step1 raw20078step1Labels permutation6 hz
    mixedMoment B raw20078step2 raw20078step2Labels = mixedMoment B raw20078step3 raw20078step3Labels := by
      have ha : raw20078step3 = (fun i j => raw20078step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20078step3 raw20078step2; decide +kernel
      have hl : raw20078step3Labels = raw20078step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20078step2 raw20078step2Labels permutation10 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20079 raw20079Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20079 raw20079Labels = mixedMoment B raw20079step0 raw20079step0Labels := by
      have hz : ∀ j, raw20079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20079step0 = (fun i j => raw20079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20079step0 raw20079; decide +kernel
      have hl : raw20079step0Labels = raw20079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20079 raw20079Labels permutation434 hz
    mixedMoment B raw20079step0 raw20079step0Labels = mixedMoment B raw20079step1 raw20079step1Labels := by
      have hz : ∀ j, raw20079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20079step1 = (fun i j => raw20079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20079step1 raw20079step0; decide +kernel
      have hl : raw20079step1Labels = raw20079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20079step0 raw20079step0Labels permutation80 hz
    mixedMoment B raw20079step1 raw20079step1Labels = mixedMoment B raw20079step2 raw20079step2Labels := by
      have hz : ∀ j, raw20079step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20079step2 = (fun i j => raw20079step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20079step2 raw20079step1; decide +kernel
      have hl : raw20079step2Labels = raw20079step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20079step1 raw20079step1Labels permutation14 hz
    mixedMoment B raw20079step2 raw20079step2Labels = mixedMoment B raw20079step3 raw20079step3Labels := by
      have hz : ∀ i, raw20079step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20079step3 = (fun i j => raw20079step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20079step3 raw20079step2; decide +kernel
      have hl : raw20079step3Labels = (fun j => raw20079step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20079step2 raw20079step2Labels permutation6 hz
    _ = mixedMoment B node4060 node4060Labels := by rfl

theorem canonical20080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20080 raw20080Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20080 raw20080Labels = mixedMoment B raw20080step0 raw20080step0Labels := by
      have hz : ∀ j, raw20080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20080step0 = (fun i j => raw20080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20080step0 raw20080; decide +kernel
      have hl : raw20080step0Labels = raw20080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20080 raw20080Labels permutation434 hz
    mixedMoment B raw20080step0 raw20080step0Labels = mixedMoment B raw20080step1 raw20080step1Labels := by
      have hz : ∀ j, raw20080step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20080step1 = (fun i j => raw20080step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20080step1 raw20080step0; decide +kernel
      have hl : raw20080step1Labels = raw20080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20080step0 raw20080step0Labels permutation80 hz
    mixedMoment B raw20080step1 raw20080step1Labels = mixedMoment B raw20080step2 raw20080step2Labels := by
      have hz : ∀ i, raw20080step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20080step2 = (fun i j => raw20080step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20080step2 raw20080step1; decide +kernel
      have hl : raw20080step2Labels = (fun j => raw20080step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20080step1 raw20080step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20081 raw20081Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20081 raw20081Labels = mixedMoment B raw20081step0 raw20081step0Labels := by
      have hz : ∀ j, raw20081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20081step0 = (fun i j => raw20081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20081step0 raw20081; decide +kernel
      have hl : raw20081step0Labels = raw20081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20081 raw20081Labels permutation434 hz
    mixedMoment B raw20081step0 raw20081step0Labels = mixedMoment B raw20081step1 raw20081step1Labels := by
      have hz : ∀ j, raw20081step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20081step1 = (fun i j => raw20081step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20081step1 raw20081step0; decide +kernel
      have hl : raw20081step1Labels = raw20081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20081step0 raw20081step0Labels permutation56 hz
    mixedMoment B raw20081step1 raw20081step1Labels = mixedMoment B raw20081step2 raw20081step2Labels := by
      have hz : ∀ i, raw20081step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20081step2 = (fun i j => raw20081step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20081step2 raw20081step1; decide +kernel
      have hl : raw20081step2Labels = (fun j => raw20081step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20081step1 raw20081step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20082 raw20082Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20082 raw20082Labels = mixedMoment B raw20082step0 raw20082step0Labels := by
      have hz : ∀ j, raw20082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20082step0 = (fun i j => raw20082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20082step0 raw20082; decide +kernel
      have hl : raw20082step0Labels = raw20082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20082 raw20082Labels permutation346 hz
    mixedMoment B raw20082step0 raw20082step0Labels = mixedMoment B raw20082step1 raw20082step1Labels := by
      have hz : ∀ j, raw20082step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20082step1 = (fun i j => raw20082step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20082step1 raw20082step0; decide +kernel
      have hl : raw20082step1Labels = raw20082step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20082step0 raw20082step0Labels permutation56 hz
    mixedMoment B raw20082step1 raw20082step1Labels = mixedMoment B raw20082step2 raw20082step2Labels := by
      have hz : ∀ i, raw20082step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20082step2 = (fun i j => raw20082step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20082step2 raw20082step1; decide +kernel
      have hl : raw20082step2Labels = (fun j => raw20082step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20082step1 raw20082step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20083 raw20083Labels = mixedMoment B node4062 node4062Labels := by
  calc
    mixedMoment B raw20083 raw20083Labels = mixedMoment B raw20083step0 raw20083step0Labels := by
      have hz : ∀ j, raw20083 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20083step0 = (fun i j => raw20083 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20083step0 raw20083; decide +kernel
      have hl : raw20083step0Labels = raw20083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20083 raw20083Labels permutation520 hz
    mixedMoment B raw20083step0 raw20083step0Labels = mixedMoment B raw20083step1 raw20083step1Labels := by
      have hz : ∀ j, raw20083step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20083step1 = (fun i j => raw20083step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20083step1 raw20083step0; decide +kernel
      have hl : raw20083step1Labels = raw20083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20083step0 raw20083step0Labels permutation104 hz
    mixedMoment B raw20083step1 raw20083step1Labels = mixedMoment B raw20083step2 raw20083step2Labels := by
      have hz : ∀ j, raw20083step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw20083step2 = (fun i j => raw20083step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw20083step2 raw20083step1; decide +kernel
      have hl : raw20083step2Labels = raw20083step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20083step1 raw20083step1Labels permutation20 hz
    mixedMoment B raw20083step2 raw20083step2Labels = mixedMoment B raw20083step3 raw20083step3Labels := by
      have hz : ∀ j, raw20083step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw20083step3 = (fun i j => raw20083step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw20083step3 raw20083step2; decide +kernel
      have hl : raw20083step3Labels = raw20083step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20083step2 raw20083step2Labels permutation4 hz
    mixedMoment B raw20083step3 raw20083step3Labels = mixedMoment B raw20083step4 raw20083step4Labels := by
      have hz : ∀ i, raw20083step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20083step4 = (fun i j => raw20083step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20083step4 raw20083step3; decide +kernel
      have hl : raw20083step4Labels = (fun j => raw20083step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20083step3 raw20083step3Labels permutation6 hz
    _ = mixedMoment B node4062 node4062Labels := by rfl

theorem canonical20084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20084 raw20084Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20084 raw20084Labels = mixedMoment B raw20084step0 raw20084step0Labels := by
      have hz : ∀ j, raw20084 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20084step0 = (fun i j => raw20084 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20084step0 raw20084; decide +kernel
      have hl : raw20084step0Labels = raw20084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20084 raw20084Labels permutation520 hz
    mixedMoment B raw20084step0 raw20084step0Labels = mixedMoment B raw20084step1 raw20084step1Labels := by
      have hz : ∀ j, raw20084step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20084step1 = (fun i j => raw20084step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20084step1 raw20084step0; decide +kernel
      have hl : raw20084step1Labels = raw20084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20084step0 raw20084step0Labels permutation104 hz
    mixedMoment B raw20084step1 raw20084step1Labels = mixedMoment B raw20084step2 raw20084step2Labels := by
      have hz : ∀ j, raw20084step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw20084step2 = (fun i j => raw20084step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw20084step2 raw20084step1; decide +kernel
      have hl : raw20084step2Labels = raw20084step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20084step1 raw20084step1Labels permutation20 hz
    mixedMoment B raw20084step2 raw20084step2Labels = mixedMoment B raw20084step3 raw20084step3Labels := by
      have hz : ∀ i, raw20084step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20084step3 = (fun i j => raw20084step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20084step3 raw20084step2; decide +kernel
      have hl : raw20084step3Labels = (fun j => raw20084step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20084step2 raw20084step2Labels permutation6 hz
    mixedMoment B raw20084step3 raw20084step3Labels = mixedMoment B raw20084step4 raw20084step4Labels := by
      have ha : raw20084step4 = (fun i j => raw20084step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20084step4 raw20084step3; decide +kernel
      have hl : raw20084step4Labels = raw20084step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20084step3 raw20084step3Labels permutation7 permutation0
    mixedMoment B raw20084step4 raw20084step4Labels = mixedMoment B raw20084step5 raw20084step5Labels := by
      have ha : raw20084step5 = -raw20084step4 := by apply Matrix.ext; change ∀ i j, raw20084step5 i j = -(raw20084step4 i j); unfold raw20084step5 raw20084step4; decide +kernel
      have hl : raw20084step5Labels = raw20084step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4060 node4060Labels := by rfl

theorem canonical20085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20085 raw20085Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20085 raw20085Labels = mixedMoment B raw20085step0 raw20085step0Labels := by
      have hz : ∀ j, raw20085 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20085step0 = (fun i j => raw20085 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20085step0 raw20085; decide +kernel
      have hl : raw20085step0Labels = raw20085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20085 raw20085Labels permutation520 hz
    mixedMoment B raw20085step0 raw20085step0Labels = mixedMoment B raw20085step1 raw20085step1Labels := by
      have hz : ∀ j, raw20085step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20085step1 = (fun i j => raw20085step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20085step1 raw20085step0; decide +kernel
      have hl : raw20085step1Labels = raw20085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20085step0 raw20085step0Labels permutation104 hz
    mixedMoment B raw20085step1 raw20085step1Labels = mixedMoment B raw20085step2 raw20085step2Labels := by
      have hz : ∀ j, raw20085step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20085step2 = (fun i j => raw20085step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20085step2 raw20085step1; decide +kernel
      have hl : raw20085step2Labels = raw20085step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20085step1 raw20085step1Labels permutation14 hz
    mixedMoment B raw20085step2 raw20085step2Labels = mixedMoment B raw20085step3 raw20085step3Labels := by
      have hz : ∀ i, raw20085step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20085step3 = (fun i j => raw20085step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20085step3 raw20085step2; decide +kernel
      have hl : raw20085step3Labels = (fun j => raw20085step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20085step2 raw20085step2Labels permutation6 hz
    mixedMoment B raw20085step3 raw20085step3Labels = mixedMoment B raw20085step4 raw20085step4Labels := by
      have ha : raw20085step4 = (fun i j => raw20085step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20085step4 raw20085step3; decide +kernel
      have hl : raw20085step4Labels = raw20085step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20085step3 raw20085step3Labels permutation7 permutation0
    mixedMoment B raw20085step4 raw20085step4Labels = mixedMoment B raw20085step5 raw20085step5Labels := by
      have ha : raw20085step5 = -raw20085step4 := by apply Matrix.ext; change ∀ i j, raw20085step5 i j = -(raw20085step4 i j); unfold raw20085step5 raw20085step4; decide +kernel
      have hl : raw20085step5Labels = raw20085step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4060 node4060Labels := by rfl

theorem canonical20086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20086 raw20086Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20086 raw20086Labels = mixedMoment B raw20086step0 raw20086step0Labels := by
      have hz : ∀ j, raw20086 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20086step0 = (fun i j => raw20086 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20086step0 raw20086; decide +kernel
      have hl : raw20086step0Labels = raw20086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20086 raw20086Labels permutation520 hz
    mixedMoment B raw20086step0 raw20086step0Labels = mixedMoment B raw20086step1 raw20086step1Labels := by
      have hz : ∀ j, raw20086step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20086step1 = (fun i j => raw20086step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20086step1 raw20086step0; decide +kernel
      have hl : raw20086step1Labels = raw20086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20086step0 raw20086step0Labels permutation80 hz
    mixedMoment B raw20086step1 raw20086step1Labels = mixedMoment B raw20086step2 raw20086step2Labels := by
      have hz : ∀ j, raw20086step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20086step2 = (fun i j => raw20086step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20086step2 raw20086step1; decide +kernel
      have hl : raw20086step2Labels = raw20086step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20086step1 raw20086step1Labels permutation14 hz
    mixedMoment B raw20086step2 raw20086step2Labels = mixedMoment B raw20086step3 raw20086step3Labels := by
      have hz : ∀ i, raw20086step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20086step3 = (fun i j => raw20086step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20086step3 raw20086step2; decide +kernel
      have hl : raw20086step3Labels = (fun j => raw20086step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20086step2 raw20086step2Labels permutation6 hz
    mixedMoment B raw20086step3 raw20086step3Labels = mixedMoment B raw20086step4 raw20086step4Labels := by
      have ha : raw20086step4 = (fun i j => raw20086step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20086step4 raw20086step3; decide +kernel
      have hl : raw20086step4Labels = raw20086step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20086step3 raw20086step3Labels permutation7 permutation0
    mixedMoment B raw20086step4 raw20086step4Labels = mixedMoment B raw20086step5 raw20086step5Labels := by
      have ha : raw20086step5 = -raw20086step4 := by apply Matrix.ext; change ∀ i j, raw20086step5 i j = -(raw20086step4 i j); unfold raw20086step5 raw20086step4; decide +kernel
      have hl : raw20086step5Labels = raw20086step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4060 node4060Labels := by rfl

theorem canonical20087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20087 raw20087Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20087 raw20087Labels = mixedMoment B raw20087step0 raw20087step0Labels := by
      have hz : ∀ j, raw20087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20087step0 = (fun i j => raw20087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20087step0 raw20087; decide +kernel
      have hl : raw20087step0Labels = raw20087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20087 raw20087Labels permutation434 hz
    mixedMoment B raw20087step0 raw20087step0Labels = mixedMoment B raw20087step1 raw20087step1Labels := by
      have hz : ∀ j, raw20087step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20087step1 = (fun i j => raw20087step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20087step1 raw20087step0; decide +kernel
      have hl : raw20087step1Labels = raw20087step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20087step0 raw20087step0Labels permutation80 hz
    mixedMoment B raw20087step1 raw20087step1Labels = mixedMoment B raw20087step2 raw20087step2Labels := by
      have hz : ∀ j, raw20087step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20087step2 = (fun i j => raw20087step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20087step2 raw20087step1; decide +kernel
      have hl : raw20087step2Labels = raw20087step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20087step1 raw20087step1Labels permutation14 hz
    mixedMoment B raw20087step2 raw20087step2Labels = mixedMoment B raw20087step3 raw20087step3Labels := by
      have hz : ∀ i, raw20087step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20087step3 = (fun i j => raw20087step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20087step3 raw20087step2; decide +kernel
      have hl : raw20087step3Labels = (fun j => raw20087step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20087step2 raw20087step2Labels permutation6 hz
    mixedMoment B raw20087step3 raw20087step3Labels = mixedMoment B raw20087step4 raw20087step4Labels := by
      have ha : raw20087step4 = (fun i j => raw20087step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20087step4 raw20087step3; decide +kernel
      have hl : raw20087step4Labels = raw20087step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20087step3 raw20087step3Labels permutation7 permutation0
    mixedMoment B raw20087step4 raw20087step4Labels = mixedMoment B raw20087step5 raw20087step5Labels := by
      have ha : raw20087step5 = -raw20087step4 := by apply Matrix.ext; change ∀ i j, raw20087step5 i j = -(raw20087step4 i j); unfold raw20087step5 raw20087step4; decide +kernel
      have hl : raw20087step5Labels = raw20087step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4060 node4060Labels := by rfl

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

theorem canonical2934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2934 raw2934Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw2934 raw2934Labels = mixedMoment B raw2934step0 raw2934step0Labels := by
      have hz : ∀ j, raw2934 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2934step0 = (fun i j => raw2934 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2934step0 raw2934; decide +kernel
      have hl : raw2934step0Labels = raw2934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934 raw2934Labels permutation520 hz
    mixedMoment B raw2934step0 raw2934step0Labels = mixedMoment B raw2934step1 raw2934step1Labels := by
      have hz : ∀ j, raw2934step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2934step1 = (fun i j => raw2934step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2934step1 raw2934step0; decide +kernel
      have hl : raw2934step1Labels = raw2934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step0 raw2934step0Labels permutation104 hz
    mixedMoment B raw2934step1 raw2934step1Labels = mixedMoment B raw2934step2 raw2934step2Labels := by
      have hz : ∀ j, raw2934step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2934step2 = (fun i j => raw2934step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2934step2 raw2934step1; decide +kernel
      have hl : raw2934step2Labels = raw2934step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step1 raw2934step1Labels permutation20 hz
    mixedMoment B raw2934step2 raw2934step2Labels = mixedMoment B raw2934step3 raw2934step3Labels := by
      have hz : ∀ j, raw2934step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2934step3 = (fun i j => raw2934step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2934step3 raw2934step2; decide +kernel
      have hl : raw2934step3Labels = raw2934step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step2 raw2934step2Labels permutation4 hz
    mixedMoment B raw2934step3 raw2934step3Labels = mixedMoment B raw2934step4 raw2934step4Labels := by
      have hz : ∀ i, raw2934step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2934step4 = (fun i j => raw2934step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2934step4 raw2934step3; decide +kernel
      have hl : raw2934step4Labels = (fun j => raw2934step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2934step3 raw2934step3Labels permutation6 hz
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

theorem canonical5197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5197 raw5197Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5197 raw5197Labels = mixedMoment B raw5197step0 raw5197step0Labels := by
      have hz : ∀ j, raw5197 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5197step0 = (fun i j => raw5197 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5197step0 raw5197; decide +kernel
      have hl : raw5197step0Labels = raw5197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5197 raw5197Labels permutation520 hz
    mixedMoment B raw5197step0 raw5197step0Labels = mixedMoment B raw5197step1 raw5197step1Labels := by
      have hz : ∀ j, raw5197step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5197step1 = (fun i j => raw5197step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5197step1 raw5197step0; decide +kernel
      have hl : raw5197step1Labels = raw5197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5197step0 raw5197step0Labels permutation104 hz
    mixedMoment B raw5197step1 raw5197step1Labels = mixedMoment B raw5197step2 raw5197step2Labels := by
      have hz : ∀ j, raw5197step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5197step2 = (fun i j => raw5197step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5197step2 raw5197step1; decide +kernel
      have hl : raw5197step2Labels = raw5197step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5197step1 raw5197step1Labels permutation20 hz
    mixedMoment B raw5197step2 raw5197step2Labels = mixedMoment B raw5197step3 raw5197step3Labels := by
      have hz : ∀ i, raw5197step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5197step3 = (fun i j => raw5197step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5197step3 raw5197step2; decide +kernel
      have hl : raw5197step3Labels = (fun j => raw5197step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5197step2 raw5197step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5201 raw5201Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5201 raw5201Labels = mixedMoment B raw5201step0 raw5201step0Labels := by
      have hz : ∀ j, raw5201 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5201step0 = (fun i j => raw5201 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5201step0 raw5201; decide +kernel
      have hl : raw5201step0Labels = raw5201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5201 raw5201Labels permutation520 hz
    mixedMoment B raw5201step0 raw5201step0Labels = mixedMoment B raw5201step1 raw5201step1Labels := by
      have hz : ∀ j, raw5201step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5201step1 = (fun i j => raw5201step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5201step1 raw5201step0; decide +kernel
      have hl : raw5201step1Labels = raw5201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5201step0 raw5201step0Labels permutation104 hz
    mixedMoment B raw5201step1 raw5201step1Labels = mixedMoment B raw5201step2 raw5201step2Labels := by
      have hz : ∀ j, raw5201step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5201step2 = (fun i j => raw5201step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5201step2 raw5201step1; decide +kernel
      have hl : raw5201step2Labels = raw5201step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5201step1 raw5201step1Labels permutation14 hz
    mixedMoment B raw5201step2 raw5201step2Labels = mixedMoment B raw5201step3 raw5201step3Labels := by
      have hz : ∀ i, raw5201step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5201step3 = (fun i j => raw5201step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5201step3 raw5201step2; decide +kernel
      have hl : raw5201step3Labels = (fun j => raw5201step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5201step2 raw5201step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5205 raw5205Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5205 raw5205Labels = mixedMoment B raw5205step0 raw5205step0Labels := by
      have hz : ∀ j, raw5205 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5205step0 = (fun i j => raw5205 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5205step0 raw5205; decide +kernel
      have hl : raw5205step0Labels = raw5205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205 raw5205Labels permutation520 hz
    mixedMoment B raw5205step0 raw5205step0Labels = mixedMoment B raw5205step1 raw5205step1Labels := by
      have hz : ∀ j, raw5205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5205step1 = (fun i j => raw5205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5205step1 raw5205step0; decide +kernel
      have hl : raw5205step1Labels = raw5205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205step0 raw5205step0Labels permutation80 hz
    mixedMoment B raw5205step1 raw5205step1Labels = mixedMoment B raw5205step2 raw5205step2Labels := by
      have hz : ∀ j, raw5205step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5205step2 = (fun i j => raw5205step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5205step2 raw5205step1; decide +kernel
      have hl : raw5205step2Labels = raw5205step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205step1 raw5205step1Labels permutation14 hz
    mixedMoment B raw5205step2 raw5205step2Labels = mixedMoment B raw5205step3 raw5205step3Labels := by
      have hz : ∀ i, raw5205step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5205step3 = (fun i j => raw5205step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5205step3 raw5205step2; decide +kernel
      have hl : raw5205step3Labels = (fun j => raw5205step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5205step2 raw5205step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5209 raw5209Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5209 raw5209Labels = mixedMoment B raw5209step0 raw5209step0Labels := by
      have hz : ∀ j, raw5209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5209step0 = (fun i j => raw5209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5209step0 raw5209; decide +kernel
      have hl : raw5209step0Labels = raw5209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209 raw5209Labels permutation434 hz
    mixedMoment B raw5209step0 raw5209step0Labels = mixedMoment B raw5209step1 raw5209step1Labels := by
      have hz : ∀ j, raw5209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5209step1 = (fun i j => raw5209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5209step1 raw5209step0; decide +kernel
      have hl : raw5209step1Labels = raw5209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209step0 raw5209step0Labels permutation80 hz
    mixedMoment B raw5209step1 raw5209step1Labels = mixedMoment B raw5209step2 raw5209step2Labels := by
      have hz : ∀ j, raw5209step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5209step2 = (fun i j => raw5209step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5209step2 raw5209step1; decide +kernel
      have hl : raw5209step2Labels = raw5209step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209step1 raw5209step1Labels permutation14 hz
    mixedMoment B raw5209step2 raw5209step2Labels = mixedMoment B raw5209step3 raw5209step3Labels := by
      have hz : ∀ i, raw5209step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5209step3 = (fun i j => raw5209step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5209step3 raw5209step2; decide +kernel
      have hl : raw5209step3Labels = (fun j => raw5209step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5209step2 raw5209step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5214 raw5214Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5214 raw5214Labels = mixedMoment B raw5214step0 raw5214step0Labels := by
      have hz : ∀ j, raw5214 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5214step0 = (fun i j => raw5214 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5214step0 raw5214; decide +kernel
      have hl : raw5214step0Labels = raw5214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5214 raw5214Labels permutation520 hz
    mixedMoment B raw5214step0 raw5214step0Labels = mixedMoment B raw5214step1 raw5214step1Labels := by
      have hz : ∀ j, raw5214step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5214step1 = (fun i j => raw5214step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5214step1 raw5214step0; decide +kernel
      have hl : raw5214step1Labels = raw5214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5214step0 raw5214step0Labels permutation104 hz
    mixedMoment B raw5214step1 raw5214step1Labels = mixedMoment B raw5214step2 raw5214step2Labels := by
      have hz : ∀ j, raw5214step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5214step2 = (fun i j => raw5214step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5214step2 raw5214step1; decide +kernel
      have hl : raw5214step2Labels = raw5214step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5214step1 raw5214step1Labels permutation20 hz
    mixedMoment B raw5214step2 raw5214step2Labels = mixedMoment B raw5214step3 raw5214step3Labels := by
      have hz : ∀ i, raw5214step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5214step3 = (fun i j => raw5214step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5214step3 raw5214step2; decide +kernel
      have hl : raw5214step3Labels = (fun j => raw5214step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5214step2 raw5214step2Labels permutation6 hz
    mixedMoment B raw5214step3 raw5214step3Labels = mixedMoment B raw5214step4 raw5214step4Labels := by
      have ha : raw5214step4 = (fun i j => raw5214step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5214step4 raw5214step3; decide +kernel
      have hl : raw5214step4Labels = raw5214step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5214step3 raw5214step3Labels permutation7 permutation0
    mixedMoment B raw5214step4 raw5214step4Labels = mixedMoment B raw5214step5 raw5214step5Labels := by
      have ha : raw5214step5 = -raw5214step4 := by apply Matrix.ext; change ∀ i j, raw5214step5 i j = -(raw5214step4 i j); unfold raw5214step5 raw5214step4; decide +kernel
      have hl : raw5214step5Labels = raw5214step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5215 raw5215Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5215 raw5215Labels = mixedMoment B raw5215step0 raw5215step0Labels := by
      have hz : ∀ j, raw5215 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5215step0 = (fun i j => raw5215 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5215step0 raw5215; decide +kernel
      have hl : raw5215step0Labels = raw5215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5215 raw5215Labels permutation520 hz
    mixedMoment B raw5215step0 raw5215step0Labels = mixedMoment B raw5215step1 raw5215step1Labels := by
      have hz : ∀ j, raw5215step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5215step1 = (fun i j => raw5215step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5215step1 raw5215step0; decide +kernel
      have hl : raw5215step1Labels = raw5215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5215step0 raw5215step0Labels permutation104 hz
    mixedMoment B raw5215step1 raw5215step1Labels = mixedMoment B raw5215step2 raw5215step2Labels := by
      have hz : ∀ j, raw5215step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5215step2 = (fun i j => raw5215step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5215step2 raw5215step1; decide +kernel
      have hl : raw5215step2Labels = raw5215step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5215step1 raw5215step1Labels permutation14 hz
    mixedMoment B raw5215step2 raw5215step2Labels = mixedMoment B raw5215step3 raw5215step3Labels := by
      have hz : ∀ i, raw5215step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5215step3 = (fun i j => raw5215step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5215step3 raw5215step2; decide +kernel
      have hl : raw5215step3Labels = (fun j => raw5215step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5215step2 raw5215step2Labels permutation6 hz
    mixedMoment B raw5215step3 raw5215step3Labels = mixedMoment B raw5215step4 raw5215step4Labels := by
      have ha : raw5215step4 = (fun i j => raw5215step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5215step4 raw5215step3; decide +kernel
      have hl : raw5215step4Labels = raw5215step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5215step3 raw5215step3Labels permutation7 permutation0
    mixedMoment B raw5215step4 raw5215step4Labels = mixedMoment B raw5215step5 raw5215step5Labels := by
      have ha : raw5215step5 = -raw5215step4 := by apply Matrix.ext; change ∀ i j, raw5215step5 i j = -(raw5215step4 i j); unfold raw5215step5 raw5215step4; decide +kernel
      have hl : raw5215step5Labels = raw5215step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5216 raw5216Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5216 raw5216Labels = mixedMoment B raw5216step0 raw5216step0Labels := by
      have hz : ∀ j, raw5216 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5216step0 = (fun i j => raw5216 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5216step0 raw5216; decide +kernel
      have hl : raw5216step0Labels = raw5216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5216 raw5216Labels permutation520 hz
    mixedMoment B raw5216step0 raw5216step0Labels = mixedMoment B raw5216step1 raw5216step1Labels := by
      have hz : ∀ j, raw5216step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5216step1 = (fun i j => raw5216step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5216step1 raw5216step0; decide +kernel
      have hl : raw5216step1Labels = raw5216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5216step0 raw5216step0Labels permutation80 hz
    mixedMoment B raw5216step1 raw5216step1Labels = mixedMoment B raw5216step2 raw5216step2Labels := by
      have hz : ∀ j, raw5216step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5216step2 = (fun i j => raw5216step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5216step2 raw5216step1; decide +kernel
      have hl : raw5216step2Labels = raw5216step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5216step1 raw5216step1Labels permutation14 hz
    mixedMoment B raw5216step2 raw5216step2Labels = mixedMoment B raw5216step3 raw5216step3Labels := by
      have hz : ∀ i, raw5216step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5216step3 = (fun i j => raw5216step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5216step3 raw5216step2; decide +kernel
      have hl : raw5216step3Labels = (fun j => raw5216step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5216step2 raw5216step2Labels permutation6 hz
    mixedMoment B raw5216step3 raw5216step3Labels = mixedMoment B raw5216step4 raw5216step4Labels := by
      have ha : raw5216step4 = (fun i j => raw5216step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5216step4 raw5216step3; decide +kernel
      have hl : raw5216step4Labels = raw5216step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5216step3 raw5216step3Labels permutation7 permutation0
    mixedMoment B raw5216step4 raw5216step4Labels = mixedMoment B raw5216step5 raw5216step5Labels := by
      have ha : raw5216step5 = -raw5216step4 := by apply Matrix.ext; change ∀ i j, raw5216step5 i j = -(raw5216step4 i j); unfold raw5216step5 raw5216step4; decide +kernel
      have hl : raw5216step5Labels = raw5216step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5217 raw5217Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5217 raw5217Labels = mixedMoment B raw5217step0 raw5217step0Labels := by
      have hz : ∀ j, raw5217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5217step0 = (fun i j => raw5217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5217step0 raw5217; decide +kernel
      have hl : raw5217step0Labels = raw5217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5217 raw5217Labels permutation434 hz
    mixedMoment B raw5217step0 raw5217step0Labels = mixedMoment B raw5217step1 raw5217step1Labels := by
      have hz : ∀ j, raw5217step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5217step1 = (fun i j => raw5217step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5217step1 raw5217step0; decide +kernel
      have hl : raw5217step1Labels = raw5217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5217step0 raw5217step0Labels permutation80 hz
    mixedMoment B raw5217step1 raw5217step1Labels = mixedMoment B raw5217step2 raw5217step2Labels := by
      have hz : ∀ j, raw5217step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5217step2 = (fun i j => raw5217step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5217step2 raw5217step1; decide +kernel
      have hl : raw5217step2Labels = raw5217step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5217step1 raw5217step1Labels permutation14 hz
    mixedMoment B raw5217step2 raw5217step2Labels = mixedMoment B raw5217step3 raw5217step3Labels := by
      have hz : ∀ i, raw5217step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5217step3 = (fun i j => raw5217step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5217step3 raw5217step2; decide +kernel
      have hl : raw5217step3Labels = (fun j => raw5217step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5217step2 raw5217step2Labels permutation6 hz
    mixedMoment B raw5217step3 raw5217step3Labels = mixedMoment B raw5217step4 raw5217step4Labels := by
      have ha : raw5217step4 = (fun i j => raw5217step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5217step4 raw5217step3; decide +kernel
      have hl : raw5217step4Labels = raw5217step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5217step3 raw5217step3Labels permutation7 permutation0
    mixedMoment B raw5217step4 raw5217step4Labels = mixedMoment B raw5217step5 raw5217step5Labels := by
      have ha : raw5217step5 = -raw5217step4 := by apply Matrix.ext; change ∀ i j, raw5217step5 i j = -(raw5217step4 i j); unfold raw5217step5 raw5217step4; decide +kernel
      have hl : raw5217step5Labels = raw5217step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node691 node691Labels = 0 := by
  exact mixedMoment_order_one B hB node691 node691Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

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

theorem sound665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node665 node665Labels = Sparse.eval nodeValue665 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 665) = mixedMoment B node665 node665Labels := rfl
  simpa [nodeValue665, Sparse.eval] using hc.symm

theorem sound686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node686 node686Labels = Sparse.eval nodeValue686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 686) = mixedMoment B node686 node686Labels := rfl
  simpa [nodeValue686, Sparse.eval] using hc.symm

theorem sound691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node691 node691Labels = Sparse.eval nodeValue691 (mixedVector B) := by
  simpa only [nodeValue691, Sparse.eval_nil] using zero691 B _hB _hF

theorem sound701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node701 node701Labels = Sparse.eval nodeValue701 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 701) = mixedMoment B node701 node701Labels := rfl
  simpa [nodeValue701, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node705 node705Labels = Sparse.eval nodeValue705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 705) = mixedMoment B node705 node705Labels := rfl
  simpa [nodeValue705, Sparse.eval] using hc.symm

theorem sound726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node726 node726Labels = Sparse.eval nodeValue726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 726) = mixedMoment B node726 node726Labels := rfl
  simpa [nodeValue726, Sparse.eval] using hc.symm

theorem sound735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node735 node735Labels = Sparse.eval nodeValue735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 735) = mixedMoment B node735 node735Labels := rfl
  simpa [nodeValue735, Sparse.eval] using hc.symm

theorem sound740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node740 node740Labels = Sparse.eval nodeValue740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 740) = mixedMoment B node740 node740Labels := rfl
  simpa [nodeValue740, Sparse.eval] using hc.symm

theorem sound750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node750 node750Labels = Sparse.eval nodeValue750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 750) = mixedMoment B node750 node750Labels := rfl
  simpa [nodeValue750, Sparse.eval] using hc.symm

theorem sound765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node765 node765Labels = Sparse.eval nodeValue765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 765) = mixedMoment B node765 node765Labels := rfl
  simpa [nodeValue765, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node770 node770Labels = 0 := by
  exact mixedMoment_order_one B hB node770 node770Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node809 node809Labels = 0 := by
  exact mixedMoment_order_one B hB node809 node809Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node812 node812Labels = 0 := by
  exact mixedMoment_order_one B hB node812 node812Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node817 node817Labels = 0 := by
  exact mixedMoment_order_one B hB node817 node817Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node770 node770Labels = Sparse.eval nodeValue770 (mixedVector B) := by
  simpa only [nodeValue770, Sparse.eval_nil] using zero770 B _hB _hF

theorem sound785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node785 node785Labels = Sparse.eval nodeValue785 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 785) = mixedMoment B node785 node785Labels := rfl
  simpa [nodeValue785, Sparse.eval] using hc.symm

theorem sound791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node791 node791Labels = Sparse.eval nodeValue791 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 791) = mixedMoment B node791 node791Labels := rfl
  simpa [nodeValue791, Sparse.eval] using hc.symm

theorem sound801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node801 node801Labels = Sparse.eval nodeValue801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 801) = mixedMoment B node801 node801Labels := rfl
  simpa [nodeValue801, Sparse.eval] using hc.symm

theorem sound809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node809 node809Labels = Sparse.eval nodeValue809 (mixedVector B) := by
  simpa only [nodeValue809, Sparse.eval_nil] using zero809 B _hB _hF

theorem sound812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node812 node812Labels = Sparse.eval nodeValue812 (mixedVector B) := by
  simpa only [nodeValue812, Sparse.eval_nil] using zero812 B _hB _hF

theorem sound817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node817 node817Labels = Sparse.eval nodeValue817 (mixedVector B) := by
  simpa only [nodeValue817, Sparse.eval_nil] using zero817 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node859 node859Labels = 0 := by
  exact mixedMoment_order_one B hB node859 node859Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node832 node832Labels = Sparse.eval nodeValue832 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 832) = mixedMoment B node832 node832Labels := rfl
  simpa [nodeValue832, Sparse.eval] using hc.symm

theorem sound845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node845 node845Labels = Sparse.eval nodeValue845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 845) = mixedMoment B node845 node845Labels := rfl
  simpa [nodeValue845, Sparse.eval] using hc.symm

theorem sound859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node859 node859Labels = Sparse.eval nodeValue859 (mixedVector B) := by
  simpa only [nodeValue859, Sparse.eval_nil] using zero859 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1007 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1007 node1007Labels = 0 := by
  exact mixedMoment_order_one B hB node1007 node1007Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node979 node979Labels = Sparse.eval nodeValue979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 979) = mixedMoment B node979 node979Labels := rfl
  simpa [nodeValue979, Sparse.eval] using hc.symm

theorem sound986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node986 node986Labels = Sparse.eval nodeValue986 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 986) = mixedMoment B node986 node986Labels := rfl
  simpa [nodeValue986, Sparse.eval] using hc.symm

theorem sound1002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1002 node1002Labels = Sparse.eval nodeValue1002 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1002) = mixedMoment B node1002 node1002Labels := rfl
  simpa [nodeValue1002, Sparse.eval] using hc.symm

theorem sound1007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1007 node1007Labels = Sparse.eval nodeValue1007 (mixedVector B) := by
  simpa only [nodeValue1007, Sparse.eval_nil] using zero1007 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1085 node1085Labels = 0 := by
  exact mixedMoment_order_one B hB node1085 node1085Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1037 node1037Labels = Sparse.eval nodeValue1037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1037) = mixedMoment B node1037 node1037Labels := rfl
  simpa [nodeValue1037, Sparse.eval] using hc.symm

theorem sound1077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1077 node1077Labels = Sparse.eval nodeValue1077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1077) = mixedMoment B node1077 node1077Labels := rfl
  simpa [nodeValue1077, Sparse.eval] using hc.symm

theorem sound1085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1085 node1085Labels = Sparse.eval nodeValue1085 (mixedVector B) := by
  simpa only [nodeValue1085, Sparse.eval_nil] using zero1085 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1096 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1096 node1096Labels = 0 := by
  exact mixedMoment_order_one B hB node1096 node1096Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1096 node1096Labels = Sparse.eval nodeValue1096 (mixedVector B) := by
  simpa only [nodeValue1096, Sparse.eval_nil] using zero1096 B _hB _hF

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

theorem sound1186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1186 node1186Labels = Sparse.eval nodeValue1186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1186) = mixedMoment B node1186 node1186Labels := rfl
  simpa [nodeValue1186, Sparse.eval] using hc.symm

theorem sound1199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1199 node1199Labels = Sparse.eval nodeValue1199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1199) = mixedMoment B node1199 node1199Labels := rfl
  simpa [nodeValue1199, Sparse.eval] using hc.symm

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

theorem sound1231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1231 node1231Labels = Sparse.eval nodeValue1231 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1231) = mixedMoment B node1231 node1231Labels := rfl
  simpa [nodeValue1231, Sparse.eval] using hc.symm

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

theorem sound1521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1521 node1521Labels = Sparse.eval nodeValue1521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1521) = mixedMoment B node1521 node1521Labels := rfl
  simpa [nodeValue1521, Sparse.eval] using hc.symm

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

theorem sound1541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1541 node1541Labels = Sparse.eval nodeValue1541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1541) = mixedMoment B node1541 node1541Labels := rfl
  simpa [nodeValue1541, Sparse.eval] using hc.symm

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

theorem sound1677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1677 node1677Labels = Sparse.eval nodeValue1677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1677) = mixedMoment B node1677 node1677Labels := rfl
  simpa [nodeValue1677, Sparse.eval] using hc.symm

theorem sound1710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1710 node1710Labels = Sparse.eval nodeValue1710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1710) = mixedMoment B node1710 node1710Labels := rfl
  simpa [nodeValue1710, Sparse.eval] using hc.symm

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

theorem zero2208 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2208 node2208Labels = 0 := by
  exact mixedMoment_order_one B hB node2208 node2208Labels 1
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

theorem sound2208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2208 node2208Labels = Sparse.eval nodeValue2208 (mixedVector B) := by
  simpa only [nodeValue2208, Sparse.eval_nil] using zero2208 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node540 node540Labels = Sparse.eval nodeValue540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 540) = mixedMoment B node540 node540Labels := rfl
  simpa [nodeValue540, Sparse.eval] using hc.symm

theorem sound545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node545 node545Labels = Sparse.eval nodeValue545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 545) = mixedMoment B node545 node545Labels := rfl
  simpa [nodeValue545, Sparse.eval] using hc.symm

theorem sound549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node549 node549Labels = Sparse.eval nodeValue549 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 549) = mixedMoment B node549 node549Labels := rfl
  simpa [nodeValue549, Sparse.eval] using hc.symm

theorem sound564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node564 node564Labels = Sparse.eval nodeValue564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 564) = mixedMoment B node564 node564Labels := rfl
  simpa [nodeValue564, Sparse.eval] using hc.symm

theorem sound570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node570 node570Labels = Sparse.eval nodeValue570 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 570) = mixedMoment B node570 node570Labels := rfl
  simpa [nodeValue570, Sparse.eval] using hc.symm

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

theorem sound4060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4060 node4060Labels = Sparse.eval nodeValue4060 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4060) = mixedMoment B node4060 node4060Labels := rfl
  simpa [nodeValue4060, Sparse.eval] using hc.symm

theorem sound4062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4062 node4062Labels = Sparse.eval nodeValue4062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4062) = mixedMoment B node4062 node4062Labels := rfl
  simpa [nodeValue4062, Sparse.eval] using hc.symm

theorem sound4066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4066 node4066Labels = Sparse.eval nodeValue4066 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4066) = mixedMoment B node4066 node4066Labels := rfl
  simpa [nodeValue4066, Sparse.eval] using hc.symm

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

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

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

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

theorem sound596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node596 node596Labels = Sparse.eval nodeValue596 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 596) = mixedMoment B node596 node596Labels := rfl
  simpa [nodeValue596, Sparse.eval] using hc.symm

theorem sound609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node609 node609Labels = Sparse.eval nodeValue609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 609) = mixedMoment B node609 node609Labels := rfl
  simpa [nodeValue609, Sparse.eval] using hc.symm

theorem sound622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node622 node622Labels = Sparse.eval nodeValue622 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 622) = mixedMoment B node622 node622Labels := rfl
  simpa [nodeValue622, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources36
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1179 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1179 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1179 + difference 0 4) (sourceB1179 + difference 4 0) sourceC1179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 859) := by
    have ha : (tripleCharges (sourceA1179 + difference 0 4) (sourceB1179 + difference 4 0) sourceC1179) = raw19834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1179 sourceB1179 sourceC1179 difference raw19834; decide +kernel
    rw [ha]
    exact (canonical19834 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1179 + difference 1 4) (sourceB1179 + difference 4 1) sourceC1179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 726) := by
    have ha : (tripleCharges (sourceA1179 + difference 1 4) (sourceB1179 + difference 4 1) sourceC1179) = raw19837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1179 sourceB1179 sourceC1179 difference raw19837; decide +kernel
    rw [ha]
    exact (canonical19837 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1179 + difference 2 4) (sourceB1179 + difference 4 2) sourceC1179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 726) := by
    have ha : (tripleCharges (sourceA1179 + difference 2 4) (sourceB1179 + difference 4 2) sourceC1179) = raw19838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1179 sourceB1179 sourceC1179 difference raw19838; decide +kernel
    rw [ha]
    exact (canonical19838 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1179 + difference 3 4) (sourceB1179 + difference 4 3) sourceC1179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 726) := by
    have ha : (tripleCharges (sourceA1179 + difference 3 4) (sourceB1179 + difference 4 3) sourceC1179) = raw19839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1179 sourceB1179 sourceC1179 difference raw19839; decide +kernel
    rw [ha]
    exact (canonical19839 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1179 + difference 4 4) (sourceB1179 + difference 4 4) sourceC1179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 832) := by
    have ha : (tripleCharges (sourceA1179 + difference 4 4) (sourceB1179 + difference 4 4) sourceC1179) = raw19830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1179 sourceB1179 sourceC1179 difference raw19830; decide +kernel
    rw [ha]
    exact (canonical19830 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1179 + difference 5 4) (sourceB1179 + difference 4 5) sourceC1179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 564) := by
    have ha : (tripleCharges (sourceA1179 + difference 5 4) (sourceB1179 + difference 4 5) sourceC1179) = raw19840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1179 sourceB1179 sourceC1179 difference raw19840; decide +kernel
    rw [ha]
    exact (canonical19840 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1179 + sourceB1179) sourceC1179) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1179 + sourceB1179) sourceC1179) = raw19836 := by
      apply Matrix.ext; unfold doubleCharges sourceA1179 sourceB1179 sourceC1179 raw19836; decide +kernel
    rw [ha]
    exact (canonical19836 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1179 sourceB1179 sourceC1179
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1179, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1180 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1180 + difference 0 5) (sourceB1180 + difference 5 0) sourceC1180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1180 + difference 0 5) (sourceB1180 + difference 5 0) sourceC1180) = raw19835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1180 sourceB1180 sourceC1180 difference raw19835; decide +kernel
    rw [ha]
    exact (canonical19835 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1180 + difference 1 5) (sourceB1180 + difference 5 1) sourceC1180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1186) := by
    have ha : (tripleCharges (sourceA1180 + difference 1 5) (sourceB1180 + difference 5 1) sourceC1180) = raw19841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1180 sourceB1180 sourceC1180 difference raw19841; decide +kernel
    rw [ha]
    exact (canonical19841 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1180 + difference 2 5) (sourceB1180 + difference 5 2) sourceC1180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1186) := by
    have ha : (tripleCharges (sourceA1180 + difference 2 5) (sourceB1180 + difference 5 2) sourceC1180) = raw19842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1180 sourceB1180 sourceC1180 difference raw19842; decide +kernel
    rw [ha]
    exact (canonical19842 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1180 + difference 3 5) (sourceB1180 + difference 5 3) sourceC1180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1186) := by
    have ha : (tripleCharges (sourceA1180 + difference 3 5) (sourceB1180 + difference 5 3) sourceC1180) = raw19843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1180 sourceB1180 sourceC1180 difference raw19843; decide +kernel
    rw [ha]
    exact (canonical19843 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1180 + difference 4 5) (sourceB1180 + difference 5 4) sourceC1180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1289) := by
    have ha : (tripleCharges (sourceA1180 + difference 4 5) (sourceB1180 + difference 5 4) sourceC1180) = raw19844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1180 sourceB1180 sourceC1180 difference raw19844; decide +kernel
    rw [ha]
    exact (canonical19844 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1180 + difference 5 5) (sourceB1180 + difference 5 5) sourceC1180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 832) := by
    have ha : (tripleCharges (sourceA1180 + difference 5 5) (sourceB1180 + difference 5 5) sourceC1180) = raw19830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1180 sourceB1180 sourceC1180 difference raw19830; decide +kernel
    rw [ha]
    exact (canonical19830 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1180 + sourceB1180) sourceC1180) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1180 + sourceB1180) sourceC1180) = raw19836 := by
      apply Matrix.ext; unfold doubleCharges sourceA1180 sourceB1180 sourceC1180 raw19836; decide +kernel
    rw [ha]
    exact (canonical19836 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1180 sourceB1180 sourceC1180
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1180, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1182 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1182 + difference 0 0) (sourceB1182 + difference 0 0) sourceC1182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 791) := by
    have ha : (tripleCharges (sourceA1182 + difference 0 0) (sourceB1182 + difference 0 0) sourceC1182) = raw19850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1182 sourceB1182 sourceC1182 difference raw19850; decide +kernel
    rw [ha]
    exact (canonical19850 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1182 + difference 0 1) (sourceB1182 + difference 1 0) sourceC1182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA1182 + difference 0 1) (sourceB1182 + difference 1 0) sourceC1182) = raw19851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1182 sourceB1182 sourceC1182 difference raw19851; decide +kernel
    rw [ha]
    exact (canonical19851 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1182 + difference 0 2) (sourceB1182 + difference 2 0) sourceC1182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA1182 + difference 0 2) (sourceB1182 + difference 2 0) sourceC1182) = raw19852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1182 sourceB1182 sourceC1182 difference raw19852; decide +kernel
    rw [ha]
    exact (canonical19852 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1182 + difference 0 3) (sourceB1182 + difference 3 0) sourceC1182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1182 + difference 0 3) (sourceB1182 + difference 3 0) sourceC1182) = raw19853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1182 sourceB1182 sourceC1182 difference raw19853; decide +kernel
    rw [ha]
    exact (canonical19853 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1182 + difference 0 4) (sourceB1182 + difference 4 0) sourceC1182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1182 + difference 0 4) (sourceB1182 + difference 4 0) sourceC1182) = raw19854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1182 sourceB1182 sourceC1182 difference raw19854; decide +kernel
    rw [ha]
    exact (canonical19854 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1182 + difference 0 5) (sourceB1182 + difference 5 0) sourceC1182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1182 + difference 0 5) (sourceB1182 + difference 5 0) sourceC1182) = raw19855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1182 sourceB1182 sourceC1182 difference raw19855; decide +kernel
    rw [ha]
    exact (canonical19855 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1182 + sourceB1182) sourceC1182) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1182 + sourceB1182) sourceC1182) = raw19856 := by
      apply Matrix.ext; unfold doubleCharges sourceA1182 sourceB1182 sourceC1182 raw19856; decide +kernel
    rw [ha]
    exact (canonical19856 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1182 sourceB1182 sourceC1182
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1182, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1183 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1183 + difference 0 3) (sourceB1183 + difference 3 0) sourceC1183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1183 + difference 0 3) (sourceB1183 + difference 3 0) sourceC1183) = raw19853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1183 sourceB1183 sourceC1183 difference raw19853; decide +kernel
    rw [ha]
    exact (canonical19853 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1183 + difference 1 3) (sourceB1183 + difference 3 1) sourceC1183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 705) := by
    have ha : (tripleCharges (sourceA1183 + difference 1 3) (sourceB1183 + difference 3 1) sourceC1183) = raw19857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1183 sourceB1183 sourceC1183 difference raw19857; decide +kernel
    rw [ha]
    exact (canonical19857 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1183 + difference 2 3) (sourceB1183 + difference 3 2) sourceC1183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 705) := by
    have ha : (tripleCharges (sourceA1183 + difference 2 3) (sourceB1183 + difference 3 2) sourceC1183) = raw19858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1183 sourceB1183 sourceC1183 difference raw19858; decide +kernel
    rw [ha]
    exact (canonical19858 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1183 + difference 3 3) (sourceB1183 + difference 3 3) sourceC1183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 791) := by
    have ha : (tripleCharges (sourceA1183 + difference 3 3) (sourceB1183 + difference 3 3) sourceC1183) = raw19850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1183 sourceB1183 sourceC1183 difference raw19850; decide +kernel
    rw [ha]
    exact (canonical19850 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1183 + difference 4 3) (sourceB1183 + difference 3 4) sourceC1183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 740) := by
    have ha : (tripleCharges (sourceA1183 + difference 4 3) (sourceB1183 + difference 3 4) sourceC1183) = raw19859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1183 sourceB1183 sourceC1183 difference raw19859; decide +kernel
    rw [ha]
    exact (canonical19859 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1183 + difference 5 3) (sourceB1183 + difference 3 5) sourceC1183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 545) := by
    have ha : (tripleCharges (sourceA1183 + difference 5 3) (sourceB1183 + difference 3 5) sourceC1183) = raw19860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1183 sourceB1183 sourceC1183 difference raw19860; decide +kernel
    rw [ha]
    exact (canonical19860 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1183 + sourceB1183) sourceC1183) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1183 + sourceB1183) sourceC1183) = raw19856 := by
      apply Matrix.ext; unfold doubleCharges sourceA1183 sourceB1183 sourceC1183 raw19856; decide +kernel
    rw [ha]
    exact (canonical19856 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1183 sourceB1183 sourceC1183
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1183, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources37
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1184 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1184 + difference 0 5) (sourceB1184 + difference 5 0) sourceC1184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1184 + difference 0 5) (sourceB1184 + difference 5 0) sourceC1184) = raw19855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1184 sourceB1184 sourceC1184 difference raw19855; decide +kernel
    rw [ha]
    exact (canonical19855 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1184 + difference 1 5) (sourceB1184 + difference 5 1) sourceC1184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1199) := by
    have ha : (tripleCharges (sourceA1184 + difference 1 5) (sourceB1184 + difference 5 1) sourceC1184) = raw19861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1184 sourceB1184 sourceC1184 difference raw19861; decide +kernel
    rw [ha]
    exact (canonical19861 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1184 + difference 2 5) (sourceB1184 + difference 5 2) sourceC1184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1199) := by
    have ha : (tripleCharges (sourceA1184 + difference 2 5) (sourceB1184 + difference 5 2) sourceC1184) = raw19862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1184 sourceB1184 sourceC1184 difference raw19862; decide +kernel
    rw [ha]
    exact (canonical19862 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1184 + difference 3 5) (sourceB1184 + difference 5 3) sourceC1184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1231) := by
    have ha : (tripleCharges (sourceA1184 + difference 3 5) (sourceB1184 + difference 5 3) sourceC1184) = raw19863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1184 sourceB1184 sourceC1184 difference raw19863; decide +kernel
    rw [ha]
    exact (canonical19863 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1184 + difference 4 5) (sourceB1184 + difference 5 4) sourceC1184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1231) := by
    have ha : (tripleCharges (sourceA1184 + difference 4 5) (sourceB1184 + difference 5 4) sourceC1184) = raw19864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1184 sourceB1184 sourceC1184 difference raw19864; decide +kernel
    rw [ha]
    exact (canonical19864 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1184 + difference 5 5) (sourceB1184 + difference 5 5) sourceC1184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 791) := by
    have ha : (tripleCharges (sourceA1184 + difference 5 5) (sourceB1184 + difference 5 5) sourceC1184) = raw19850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1184 sourceB1184 sourceC1184 difference raw19850; decide +kernel
    rw [ha]
    exact (canonical19850 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1184 + sourceB1184) sourceC1184) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1184 + sourceB1184) sourceC1184) = raw19856 := by
      apply Matrix.ext; unfold doubleCharges sourceA1184 sourceB1184 sourceC1184 raw19856; decide +kernel
    rw [ha]
    exact (canonical19856 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1184 sourceB1184 sourceC1184
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1184, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1186 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1186 + difference 0 0) (sourceB1186 + difference 0 0) sourceC1186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 986) := by
    have ha : (tripleCharges (sourceA1186 + difference 0 0) (sourceB1186 + difference 0 0) sourceC1186) = raw19870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1186 sourceB1186 sourceC1186 difference raw19870; decide +kernel
    rw [ha]
    exact (canonical19870 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1186 + difference 0 1) (sourceB1186 + difference 1 0) sourceC1186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1186 + difference 0 1) (sourceB1186 + difference 1 0) sourceC1186) = raw19871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1186 sourceB1186 sourceC1186 difference raw19871; decide +kernel
    rw [ha]
    exact (canonical19871 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1186 + difference 0 2) (sourceB1186 + difference 2 0) sourceC1186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1186 + difference 0 2) (sourceB1186 + difference 2 0) sourceC1186) = raw19872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1186 sourceB1186 sourceC1186 difference raw19872; decide +kernel
    rw [ha]
    exact (canonical19872 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1186 + difference 0 3) (sourceB1186 + difference 3 0) sourceC1186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1186 + difference 0 3) (sourceB1186 + difference 3 0) sourceC1186) = raw19873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1186 sourceB1186 sourceC1186 difference raw19873; decide +kernel
    rw [ha]
    exact (canonical19873 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1186 + difference 0 4) (sourceB1186 + difference 4 0) sourceC1186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1007) := by
    have ha : (tripleCharges (sourceA1186 + difference 0 4) (sourceB1186 + difference 4 0) sourceC1186) = raw19874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1186 sourceB1186 sourceC1186 difference raw19874; decide +kernel
    rw [ha]
    exact (canonical19874 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1186 + difference 0 5) (sourceB1186 + difference 5 0) sourceC1186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA1186 + difference 0 5) (sourceB1186 + difference 5 0) sourceC1186) = raw19875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1186 sourceB1186 sourceC1186 difference raw19875; decide +kernel
    rw [ha]
    exact (canonical19875 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1186 + sourceB1186) sourceC1186) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1186 + sourceB1186) sourceC1186) = raw19876 := by
      apply Matrix.ext; unfold doubleCharges sourceA1186 sourceB1186 sourceC1186 raw19876; decide +kernel
    rw [ha]
    exact (canonical19876 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1186 sourceB1186 sourceC1186
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1186, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1190 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1190 + difference 0 1) (sourceB1190 + difference 1 0) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 0 1) (sourceB1190 + difference 1 0) sourceC1190) = raw19917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19917; decide +kernel
    rw [ha]
    exact (canonical19917 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1190 + difference 0 2) (sourceB1190 + difference 2 0) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 0 2) (sourceB1190 + difference 2 0) sourceC1190) = raw19918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19918; decide +kernel
    rw [ha]
    exact (canonical19918 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1190 + difference 0 3) (sourceB1190 + difference 3 0) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 0 3) (sourceB1190 + difference 3 0) sourceC1190) = raw19919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19919; decide +kernel
    rw [ha]
    exact (canonical19919 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1190 + difference 0 4) (sourceB1190 + difference 4 0) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 0 4) (sourceB1190 + difference 4 0) sourceC1190) = raw19920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19920; decide +kernel
    rw [ha]
    exact (canonical19920 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1190 + difference 0 5) (sourceB1190 + difference 5 0) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA1190 + difference 0 5) (sourceB1190 + difference 5 0) sourceC1190) = raw19921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19921; decide +kernel
    rw [ha]
    exact (canonical19921 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1190 + difference 1 0) (sourceB1190 + difference 0 1) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 1 0) (sourceB1190 + difference 0 1) sourceC1190) = raw19922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19922; decide +kernel
    rw [ha]
    exact (canonical19922 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1190 + difference 1 2) (sourceB1190 + difference 2 1) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 1 2) (sourceB1190 + difference 2 1) sourceC1190) = raw19923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19923; decide +kernel
    rw [ha]
    exact (canonical19923 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1190 + difference 1 3) (sourceB1190 + difference 3 1) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 1 3) (sourceB1190 + difference 3 1) sourceC1190) = raw19924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19924; decide +kernel
    rw [ha]
    exact (canonical19924 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1190 + difference 1 4) (sourceB1190 + difference 4 1) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 1 4) (sourceB1190 + difference 4 1) sourceC1190) = raw19925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19925; decide +kernel
    rw [ha]
    exact (canonical19925 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1190 + difference 1 5) (sourceB1190 + difference 5 1) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 1 5) (sourceB1190 + difference 5 1) sourceC1190) = raw19926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19926; decide +kernel
    rw [ha]
    exact (canonical19926 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1190 + difference 2 0) (sourceB1190 + difference 0 2) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 2 0) (sourceB1190 + difference 0 2) sourceC1190) = raw19927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19927; decide +kernel
    rw [ha]
    exact (canonical19927 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1190 + difference 2 1) (sourceB1190 + difference 1 2) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 2 1) (sourceB1190 + difference 1 2) sourceC1190) = raw19928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19928; decide +kernel
    rw [ha]
    exact (canonical19928 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1190 + difference 2 3) (sourceB1190 + difference 3 2) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 2 3) (sourceB1190 + difference 3 2) sourceC1190) = raw19929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19929; decide +kernel
    rw [ha]
    exact (canonical19929 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1190 + difference 2 4) (sourceB1190 + difference 4 2) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 2 4) (sourceB1190 + difference 4 2) sourceC1190) = raw19930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19930; decide +kernel
    rw [ha]
    exact (canonical19930 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1190 + difference 2 5) (sourceB1190 + difference 5 2) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 2 5) (sourceB1190 + difference 5 2) sourceC1190) = raw19931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19931; decide +kernel
    rw [ha]
    exact (canonical19931 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1190 + difference 3 0) (sourceB1190 + difference 0 3) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 3 0) (sourceB1190 + difference 0 3) sourceC1190) = raw19932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19932; decide +kernel
    rw [ha]
    exact (canonical19932 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1190 + difference 3 1) (sourceB1190 + difference 1 3) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 3 1) (sourceB1190 + difference 1 3) sourceC1190) = raw19933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19933; decide +kernel
    rw [ha]
    exact (canonical19933 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1190 + difference 3 2) (sourceB1190 + difference 2 3) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 3 2) (sourceB1190 + difference 2 3) sourceC1190) = raw19934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19934; decide +kernel
    rw [ha]
    exact (canonical19934 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1190 + difference 3 4) (sourceB1190 + difference 4 3) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 3 4) (sourceB1190 + difference 4 3) sourceC1190) = raw19935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19935; decide +kernel
    rw [ha]
    exact (canonical19935 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1190 + difference 3 5) (sourceB1190 + difference 5 3) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 3 5) (sourceB1190 + difference 5 3) sourceC1190) = raw19936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19936; decide +kernel
    rw [ha]
    exact (canonical19936 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1190 + difference 4 0) (sourceB1190 + difference 0 4) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 4 0) (sourceB1190 + difference 0 4) sourceC1190) = raw19937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19937; decide +kernel
    rw [ha]
    exact (canonical19937 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1190 + difference 4 1) (sourceB1190 + difference 1 4) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 4 1) (sourceB1190 + difference 1 4) sourceC1190) = raw19938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19938; decide +kernel
    rw [ha]
    exact (canonical19938 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1190 + difference 4 2) (sourceB1190 + difference 2 4) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 4 2) (sourceB1190 + difference 2 4) sourceC1190) = raw19939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19939; decide +kernel
    rw [ha]
    exact (canonical19939 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1190 + difference 4 3) (sourceB1190 + difference 3 4) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 4 3) (sourceB1190 + difference 3 4) sourceC1190) = raw19940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19940; decide +kernel
    rw [ha]
    exact (canonical19940 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1190 + difference 4 5) (sourceB1190 + difference 5 4) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 4 5) (sourceB1190 + difference 5 4) sourceC1190) = raw19941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19941; decide +kernel
    rw [ha]
    exact (canonical19941 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1190 + difference 5 0) (sourceB1190 + difference 0 5) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1541) := by
    have ha : (tripleCharges (sourceA1190 + difference 5 0) (sourceB1190 + difference 0 5) sourceC1190) = raw19942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19942; decide +kernel
    rw [ha]
    exact (canonical19942 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1190 + difference 5 1) (sourceB1190 + difference 1 5) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 5 1) (sourceB1190 + difference 1 5) sourceC1190) = raw19943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19943; decide +kernel
    rw [ha]
    exact (canonical19943 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1190 + difference 5 2) (sourceB1190 + difference 2 5) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 5 2) (sourceB1190 + difference 2 5) sourceC1190) = raw19944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19944; decide +kernel
    rw [ha]
    exact (canonical19944 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1190 + difference 5 3) (sourceB1190 + difference 3 5) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 5 3) (sourceB1190 + difference 3 5) sourceC1190) = raw19945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19945; decide +kernel
    rw [ha]
    exact (canonical19945 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1190 + difference 5 4) (sourceB1190 + difference 4 5) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 5 4) (sourceB1190 + difference 4 5) sourceC1190) = raw19946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19946; decide +kernel
    rw [ha]
    exact (canonical19946 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1190 sourceB1190 sourceC1190
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1190, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1191 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1191 + difference 0 0) (sourceB1191 + difference 0 0) sourceC1191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1096) := by
    have ha : (tripleCharges (sourceA1191 + difference 0 0) (sourceB1191 + difference 0 0) sourceC1191) = raw19947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1191 sourceB1191 sourceC1191 difference raw19947; decide +kernel
    rw [ha]
    exact (canonical19947 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1191 + difference 1 0) (sourceB1191 + difference 0 1) sourceC1191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 609) := by
    have ha : (tripleCharges (sourceA1191 + difference 1 0) (sourceB1191 + difference 0 1) sourceC1191) = raw19948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1191 sourceB1191 sourceC1191 difference raw19948; decide +kernel
    rw [ha]
    exact (canonical19948 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1191 + difference 2 0) (sourceB1191 + difference 0 2) sourceC1191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 609) := by
    have ha : (tripleCharges (sourceA1191 + difference 2 0) (sourceB1191 + difference 0 2) sourceC1191) = raw19949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1191 sourceB1191 sourceC1191 difference raw19949; decide +kernel
    rw [ha]
    exact (canonical19949 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1191 + difference 3 0) (sourceB1191 + difference 0 3) sourceC1191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 609) := by
    have ha : (tripleCharges (sourceA1191 + difference 3 0) (sourceB1191 + difference 0 3) sourceC1191) = raw19950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1191 sourceB1191 sourceC1191 difference raw19950; decide +kernel
    rw [ha]
    exact (canonical19950 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1191 + difference 4 0) (sourceB1191 + difference 0 4) sourceC1191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 609) := by
    have ha : (tripleCharges (sourceA1191 + difference 4 0) (sourceB1191 + difference 0 4) sourceC1191) = raw19951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1191 sourceB1191 sourceC1191 difference raw19951; decide +kernel
    rw [ha]
    exact (canonical19951 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1191 + difference 5 0) (sourceB1191 + difference 0 5) sourceC1191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 622) := by
    have ha : (tripleCharges (sourceA1191 + difference 5 0) (sourceB1191 + difference 0 5) sourceC1191) = raw19952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1191 sourceB1191 sourceC1191 difference raw19952; decide +kernel
    rw [ha]
    exact (canonical19952 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1191 + sourceB1191) sourceC1191) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1191 + sourceB1191) sourceC1191) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA1191 sourceB1191 sourceC1191 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1191 sourceB1191 sourceC1191
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1191, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1194 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1194 + difference 0 1) (sourceB1194 + difference 1 0) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1194 + difference 0 1) (sourceB1194 + difference 1 0) sourceC1194) = raw20001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20001; decide +kernel
    rw [ha]
    exact (canonical20001 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1194 + difference 0 2) (sourceB1194 + difference 2 0) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1194 + difference 0 2) (sourceB1194 + difference 2 0) sourceC1194) = raw20002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20002; decide +kernel
    rw [ha]
    exact (canonical20002 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1194 + difference 0 3) (sourceB1194 + difference 3 0) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1194 + difference 0 3) (sourceB1194 + difference 3 0) sourceC1194) = raw20003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20003; decide +kernel
    rw [ha]
    exact (canonical20003 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1194 + difference 0 4) (sourceB1194 + difference 4 0) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1194 + difference 0 4) (sourceB1194 + difference 4 0) sourceC1194) = raw20004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20004; decide +kernel
    rw [ha]
    exact (canonical20004 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1194 + difference 0 5) (sourceB1194 + difference 5 0) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1085) := by
    have ha : (tripleCharges (sourceA1194 + difference 0 5) (sourceB1194 + difference 5 0) sourceC1194) = raw20005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20005; decide +kernel
    rw [ha]
    exact (canonical20005 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1194 + difference 1 0) (sourceB1194 + difference 0 1) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 765) := by
    have ha : (tripleCharges (sourceA1194 + difference 1 0) (sourceB1194 + difference 0 1) sourceC1194) = raw20006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20006; decide +kernel
    rw [ha]
    exact (canonical20006 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1194 + difference 1 2) (sourceB1194 + difference 2 1) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 750) := by
    have ha : (tripleCharges (sourceA1194 + difference 1 2) (sourceB1194 + difference 2 1) sourceC1194) = raw20007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20007; decide +kernel
    rw [ha]
    exact (canonical20007 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1194 + difference 1 3) (sourceB1194 + difference 3 1) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 750) := by
    have ha : (tripleCharges (sourceA1194 + difference 1 3) (sourceB1194 + difference 3 1) sourceC1194) = raw20008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20008; decide +kernel
    rw [ha]
    exact (canonical20008 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1194 + difference 1 4) (sourceB1194 + difference 4 1) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 770) := by
    have ha : (tripleCharges (sourceA1194 + difference 1 4) (sourceB1194 + difference 4 1) sourceC1194) = raw20009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20009; decide +kernel
    rw [ha]
    exact (canonical20009 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1194 + difference 1 5) (sourceB1194 + difference 5 1) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1002) := by
    have ha : (tripleCharges (sourceA1194 + difference 1 5) (sourceB1194 + difference 5 1) sourceC1194) = raw20010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20010; decide +kernel
    rw [ha]
    exact (canonical20010 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1194 + difference 2 0) (sourceB1194 + difference 0 2) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 765) := by
    have ha : (tripleCharges (sourceA1194 + difference 2 0) (sourceB1194 + difference 0 2) sourceC1194) = raw20011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20011; decide +kernel
    rw [ha]
    exact (canonical20011 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1194 + difference 2 1) (sourceB1194 + difference 1 2) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 750) := by
    have ha : (tripleCharges (sourceA1194 + difference 2 1) (sourceB1194 + difference 1 2) sourceC1194) = raw20012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20012; decide +kernel
    rw [ha]
    exact (canonical20012 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1194 + difference 2 3) (sourceB1194 + difference 3 2) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 750) := by
    have ha : (tripleCharges (sourceA1194 + difference 2 3) (sourceB1194 + difference 3 2) sourceC1194) = raw20013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20013; decide +kernel
    rw [ha]
    exact (canonical20013 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1194 + difference 2 4) (sourceB1194 + difference 4 2) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 770) := by
    have ha : (tripleCharges (sourceA1194 + difference 2 4) (sourceB1194 + difference 4 2) sourceC1194) = raw20014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20014; decide +kernel
    rw [ha]
    exact (canonical20014 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1194 + difference 2 5) (sourceB1194 + difference 5 2) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1002) := by
    have ha : (tripleCharges (sourceA1194 + difference 2 5) (sourceB1194 + difference 5 2) sourceC1194) = raw20015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20015; decide +kernel
    rw [ha]
    exact (canonical20015 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1194 + difference 3 0) (sourceB1194 + difference 0 3) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 765) := by
    have ha : (tripleCharges (sourceA1194 + difference 3 0) (sourceB1194 + difference 0 3) sourceC1194) = raw20016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20016; decide +kernel
    rw [ha]
    exact (canonical20016 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1194 + difference 3 1) (sourceB1194 + difference 1 3) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 750) := by
    have ha : (tripleCharges (sourceA1194 + difference 3 1) (sourceB1194 + difference 1 3) sourceC1194) = raw20017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20017; decide +kernel
    rw [ha]
    exact (canonical20017 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1194 + difference 3 2) (sourceB1194 + difference 2 3) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 750) := by
    have ha : (tripleCharges (sourceA1194 + difference 3 2) (sourceB1194 + difference 2 3) sourceC1194) = raw20018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20018; decide +kernel
    rw [ha]
    exact (canonical20018 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1194 + difference 3 4) (sourceB1194 + difference 4 3) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 770) := by
    have ha : (tripleCharges (sourceA1194 + difference 3 4) (sourceB1194 + difference 4 3) sourceC1194) = raw20019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20019; decide +kernel
    rw [ha]
    exact (canonical20019 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1194 + difference 3 5) (sourceB1194 + difference 5 3) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1002) := by
    have ha : (tripleCharges (sourceA1194 + difference 3 5) (sourceB1194 + difference 5 3) sourceC1194) = raw20020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20020; decide +kernel
    rw [ha]
    exact (canonical20020 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1194 + difference 4 0) (sourceB1194 + difference 0 4) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 845) := by
    have ha : (tripleCharges (sourceA1194 + difference 4 0) (sourceB1194 + difference 0 4) sourceC1194) = raw20021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20021; decide +kernel
    rw [ha]
    exact (canonical20021 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1194 + difference 4 1) (sourceB1194 + difference 1 4) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 801) := by
    have ha : (tripleCharges (sourceA1194 + difference 4 1) (sourceB1194 + difference 1 4) sourceC1194) = raw20022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20022; decide +kernel
    rw [ha]
    exact (canonical20022 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1194 + difference 4 2) (sourceB1194 + difference 2 4) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 801) := by
    have ha : (tripleCharges (sourceA1194 + difference 4 2) (sourceB1194 + difference 2 4) sourceC1194) = raw20023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20023; decide +kernel
    rw [ha]
    exact (canonical20023 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1194 + difference 4 3) (sourceB1194 + difference 3 4) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 801) := by
    have ha : (tripleCharges (sourceA1194 + difference 4 3) (sourceB1194 + difference 3 4) sourceC1194) = raw20024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20024; decide +kernel
    rw [ha]
    exact (canonical20024 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1194 + difference 4 5) (sourceB1194 + difference 5 4) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1077) := by
    have ha : (tripleCharges (sourceA1194 + difference 4 5) (sourceB1194 + difference 5 4) sourceC1194) = raw20025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20025; decide +kernel
    rw [ha]
    exact (canonical20025 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1194 + difference 5 0) (sourceB1194 + difference 0 5) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 686) := by
    have ha : (tripleCharges (sourceA1194 + difference 5 0) (sourceB1194 + difference 0 5) sourceC1194) = raw20026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20026; decide +kernel
    rw [ha]
    exact (canonical20026 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1194 + difference 5 1) (sourceB1194 + difference 1 5) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 665) := by
    have ha : (tripleCharges (sourceA1194 + difference 5 1) (sourceB1194 + difference 1 5) sourceC1194) = raw20027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20027; decide +kernel
    rw [ha]
    exact (canonical20027 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1194 + difference 5 2) (sourceB1194 + difference 2 5) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 665) := by
    have ha : (tripleCharges (sourceA1194 + difference 5 2) (sourceB1194 + difference 2 5) sourceC1194) = raw20028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20028; decide +kernel
    rw [ha]
    exact (canonical20028 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1194 + difference 5 3) (sourceB1194 + difference 3 5) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 665) := by
    have ha : (tripleCharges (sourceA1194 + difference 5 3) (sourceB1194 + difference 3 5) sourceC1194) = raw20029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20029; decide +kernel
    rw [ha]
    exact (canonical20029 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1194 + difference 5 4) (sourceB1194 + difference 4 5) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 691) := by
    have ha : (tripleCharges (sourceA1194 + difference 5 4) (sourceB1194 + difference 4 5) sourceC1194) = raw20030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20030; decide +kernel
    rw [ha]
    exact (canonical20030 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1194 sourceB1194 sourceC1194
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1194, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1195 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1195 + difference 0 0) (sourceB1195 + difference 0 0) sourceC1195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 817) := by
    have ha : (tripleCharges (sourceA1195 + difference 0 0) (sourceB1195 + difference 0 0) sourceC1195) = raw20031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1195 sourceB1195 sourceC1195 difference raw20031; decide +kernel
    rw [ha]
    exact (canonical20031 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1195 + difference 1 0) (sourceB1195 + difference 0 1) sourceC1195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 570) := by
    have ha : (tripleCharges (sourceA1195 + difference 1 0) (sourceB1195 + difference 0 1) sourceC1195) = raw20032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1195 sourceB1195 sourceC1195 difference raw20032; decide +kernel
    rw [ha]
    exact (canonical20032 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1195 + difference 2 0) (sourceB1195 + difference 0 2) sourceC1195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 570) := by
    have ha : (tripleCharges (sourceA1195 + difference 2 0) (sourceB1195 + difference 0 2) sourceC1195) = raw20033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1195 sourceB1195 sourceC1195 difference raw20033; decide +kernel
    rw [ha]
    exact (canonical20033 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1195 + difference 3 0) (sourceB1195 + difference 0 3) sourceC1195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 570) := by
    have ha : (tripleCharges (sourceA1195 + difference 3 0) (sourceB1195 + difference 0 3) sourceC1195) = raw20034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1195 sourceB1195 sourceC1195 difference raw20034; decide +kernel
    rw [ha]
    exact (canonical20034 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1195 + difference 4 0) (sourceB1195 + difference 0 4) sourceC1195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 596) := by
    have ha : (tripleCharges (sourceA1195 + difference 4 0) (sourceB1195 + difference 0 4) sourceC1195) = raw20035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1195 sourceB1195 sourceC1195 difference raw20035; decide +kernel
    rw [ha]
    exact (canonical20035 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1195 + difference 5 0) (sourceB1195 + difference 0 5) sourceC1195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 549) := by
    have ha : (tripleCharges (sourceA1195 + difference 5 0) (sourceB1195 + difference 0 5) sourceC1195) = raw20036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1195 sourceB1195 sourceC1195 difference raw20036; decide +kernel
    rw [ha]
    exact (canonical20036 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1195 + sourceB1195) sourceC1195) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1195 + sourceB1195) sourceC1195) = raw20037 := by
      apply Matrix.ext; unfold doubleCharges sourceA1195 sourceB1195 sourceC1195 raw20037; decide +kernel
    rw [ha]
    exact (canonical20037 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1195 sourceB1195 sourceC1195
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1195, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1197 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1197 + difference 0 1) (sourceB1197 + difference 1 0) sourceC1197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1197 + difference 0 1) (sourceB1197 + difference 1 0) sourceC1197) = raw20042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1197 sourceB1197 sourceC1197 difference raw20042; decide +kernel
    rw [ha]
    exact (canonical20042 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1197 + difference 1 1) (sourceB1197 + difference 1 1) sourceC1197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 817) := by
    have ha : (tripleCharges (sourceA1197 + difference 1 1) (sourceB1197 + difference 1 1) sourceC1197) = raw20031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1197 sourceB1197 sourceC1197 difference raw20031; decide +kernel
    rw [ha]
    exact (canonical20031 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1197 + difference 2 1) (sourceB1197 + difference 1 2) sourceC1197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 701) := by
    have ha : (tripleCharges (sourceA1197 + difference 2 1) (sourceB1197 + difference 1 2) sourceC1197) = raw20043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1197 sourceB1197 sourceC1197 difference raw20043; decide +kernel
    rw [ha]
    exact (canonical20043 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1197 + difference 3 1) (sourceB1197 + difference 1 3) sourceC1197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 701) := by
    have ha : (tripleCharges (sourceA1197 + difference 3 1) (sourceB1197 + difference 1 3) sourceC1197) = raw20044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1197 sourceB1197 sourceC1197 difference raw20044; decide +kernel
    rw [ha]
    exact (canonical20044 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1197 + difference 4 1) (sourceB1197 + difference 1 4) sourceC1197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 735) := by
    have ha : (tripleCharges (sourceA1197 + difference 4 1) (sourceB1197 + difference 1 4) sourceC1197) = raw20045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1197 sourceB1197 sourceC1197 difference raw20045; decide +kernel
    rw [ha]
    exact (canonical20045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1197 + difference 5 1) (sourceB1197 + difference 1 5) sourceC1197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 540) := by
    have ha : (tripleCharges (sourceA1197 + difference 5 1) (sourceB1197 + difference 1 5) sourceC1197) = raw20046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1197 sourceB1197 sourceC1197 difference raw20046; decide +kernel
    rw [ha]
    exact (canonical20046 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1197 + sourceB1197) sourceC1197) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1197 + sourceB1197) sourceC1197) = raw20037 := by
      apply Matrix.ext; unfold doubleCharges sourceA1197 sourceB1197 sourceC1197 raw20037; decide +kernel
    rw [ha]
    exact (canonical20037 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1197 sourceB1197 sourceC1197
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1197, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1198 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1198 + difference 4 0) (sourceB1198 + difference 0 4) sourceC1198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 596) := by
    have ha : (tripleCharges (sourceA1198 + difference 4 0) (sourceB1198 + difference 0 4) sourceC1198) = raw20035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1198 sourceB1198 sourceC1198 difference raw20035; decide +kernel
    rw [ha]
    exact (canonical20035 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1198 + difference 4 1) (sourceB1198 + difference 1 4) sourceC1198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 735) := by
    have ha : (tripleCharges (sourceA1198 + difference 4 1) (sourceB1198 + difference 1 4) sourceC1198) = raw20045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1198 sourceB1198 sourceC1198 difference raw20045; decide +kernel
    rw [ha]
    exact (canonical20045 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1198 + difference 4 2) (sourceB1198 + difference 2 4) sourceC1198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 735) := by
    have ha : (tripleCharges (sourceA1198 + difference 4 2) (sourceB1198 + difference 2 4) sourceC1198) = raw20047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1198 sourceB1198 sourceC1198 difference raw20047; decide +kernel
    rw [ha]
    exact (canonical20047 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1198 + difference 4 3) (sourceB1198 + difference 3 4) sourceC1198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 735) := by
    have ha : (tripleCharges (sourceA1198 + difference 4 3) (sourceB1198 + difference 3 4) sourceC1198) = raw20048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1198 sourceB1198 sourceC1198 difference raw20048; decide +kernel
    rw [ha]
    exact (canonical20048 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1198 + difference 4 4) (sourceB1198 + difference 4 4) sourceC1198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 817) := by
    have ha : (tripleCharges (sourceA1198 + difference 4 4) (sourceB1198 + difference 4 4) sourceC1198) = raw20031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1198 sourceB1198 sourceC1198 difference raw20031; decide +kernel
    rw [ha]
    exact (canonical20031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1198 + difference 4 5) (sourceB1198 + difference 5 4) sourceC1198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1077) := by
    have ha : (tripleCharges (sourceA1198 + difference 4 5) (sourceB1198 + difference 5 4) sourceC1198) = raw20049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1198 sourceB1198 sourceC1198 difference raw20049; decide +kernel
    rw [ha]
    exact (canonical20049 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1198 + sourceB1198) sourceC1198) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1198 + sourceB1198) sourceC1198) = raw20037 := by
      apply Matrix.ext; unfold doubleCharges sourceA1198 sourceB1198 sourceC1198 raw20037; decide +kernel
    rw [ha]
    exact (canonical20037 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1198 sourceB1198 sourceC1198
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1198, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1200 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1200 + difference 0 1) (sourceB1200 + difference 1 0) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 0 1) (sourceB1200 + difference 1 0) sourceC1200) = raw5214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5214; decide +kernel
    rw [ha]
    exact (canonical5214 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1200 + difference 0 2) (sourceB1200 + difference 2 0) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 0 2) (sourceB1200 + difference 2 0) sourceC1200) = raw5215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5215; decide +kernel
    rw [ha]
    exact (canonical5215 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1200 + difference 0 3) (sourceB1200 + difference 3 0) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 0 3) (sourceB1200 + difference 3 0) sourceC1200) = raw5216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5216; decide +kernel
    rw [ha]
    exact (canonical5216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1200 + difference 0 4) (sourceB1200 + difference 4 0) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 0 4) (sourceB1200 + difference 4 0) sourceC1200) = raw5217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5217; decide +kernel
    rw [ha]
    exact (canonical5217 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1200 + difference 0 5) (sourceB1200 + difference 5 0) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA1200 + difference 0 5) (sourceB1200 + difference 5 0) sourceC1200) = raw2934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw2934; decide +kernel
    rw [ha]
    exact (canonical2934 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1200 + difference 1 0) (sourceB1200 + difference 0 1) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 1 0) (sourceB1200 + difference 0 1) sourceC1200) = raw20067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20067; decide +kernel
    rw [ha]
    exact (canonical20067 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1200 + difference 1 2) (sourceB1200 + difference 2 1) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 1 2) (sourceB1200 + difference 2 1) sourceC1200) = raw20068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20068; decide +kernel
    rw [ha]
    exact (canonical20068 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1200 + difference 1 3) (sourceB1200 + difference 3 1) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 1 3) (sourceB1200 + difference 3 1) sourceC1200) = raw20069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20069; decide +kernel
    rw [ha]
    exact (canonical20069 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1200 + difference 1 4) (sourceB1200 + difference 4 1) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 1 4) (sourceB1200 + difference 4 1) sourceC1200) = raw20070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20070; decide +kernel
    rw [ha]
    exact (canonical20070 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1200 + difference 1 5) (sourceB1200 + difference 5 1) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 1 5) (sourceB1200 + difference 5 1) sourceC1200) = raw5197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5197; decide +kernel
    rw [ha]
    exact (canonical5197 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1200 + difference 2 0) (sourceB1200 + difference 0 2) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 2 0) (sourceB1200 + difference 0 2) sourceC1200) = raw20071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20071; decide +kernel
    rw [ha]
    exact (canonical20071 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1200 + difference 2 1) (sourceB1200 + difference 1 2) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 2 1) (sourceB1200 + difference 1 2) sourceC1200) = raw20072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20072; decide +kernel
    rw [ha]
    exact (canonical20072 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1200 + difference 2 3) (sourceB1200 + difference 3 2) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 2 3) (sourceB1200 + difference 3 2) sourceC1200) = raw20073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20073; decide +kernel
    rw [ha]
    exact (canonical20073 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1200 + difference 2 4) (sourceB1200 + difference 4 2) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 2 4) (sourceB1200 + difference 4 2) sourceC1200) = raw20074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20074; decide +kernel
    rw [ha]
    exact (canonical20074 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1200 + difference 2 5) (sourceB1200 + difference 5 2) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 2 5) (sourceB1200 + difference 5 2) sourceC1200) = raw5201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5201; decide +kernel
    rw [ha]
    exact (canonical5201 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1200 + difference 3 0) (sourceB1200 + difference 0 3) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 3 0) (sourceB1200 + difference 0 3) sourceC1200) = raw20075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20075; decide +kernel
    rw [ha]
    exact (canonical20075 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1200 + difference 3 1) (sourceB1200 + difference 1 3) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 3 1) (sourceB1200 + difference 1 3) sourceC1200) = raw20076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20076; decide +kernel
    rw [ha]
    exact (canonical20076 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1200 + difference 3 2) (sourceB1200 + difference 2 3) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 3 2) (sourceB1200 + difference 2 3) sourceC1200) = raw20077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20077; decide +kernel
    rw [ha]
    exact (canonical20077 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1200 + difference 3 4) (sourceB1200 + difference 4 3) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 3 4) (sourceB1200 + difference 4 3) sourceC1200) = raw20078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20078; decide +kernel
    rw [ha]
    exact (canonical20078 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1200 + difference 3 5) (sourceB1200 + difference 5 3) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 3 5) (sourceB1200 + difference 5 3) sourceC1200) = raw5205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5205; decide +kernel
    rw [ha]
    exact (canonical5205 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1200 + difference 4 0) (sourceB1200 + difference 0 4) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 4 0) (sourceB1200 + difference 0 4) sourceC1200) = raw20079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20079; decide +kernel
    rw [ha]
    exact (canonical20079 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1200 + difference 4 1) (sourceB1200 + difference 1 4) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 4 1) (sourceB1200 + difference 1 4) sourceC1200) = raw20080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20080; decide +kernel
    rw [ha]
    exact (canonical20080 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1200 + difference 4 2) (sourceB1200 + difference 2 4) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 4 2) (sourceB1200 + difference 2 4) sourceC1200) = raw20081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20081; decide +kernel
    rw [ha]
    exact (canonical20081 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1200 + difference 4 3) (sourceB1200 + difference 3 4) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 4 3) (sourceB1200 + difference 3 4) sourceC1200) = raw20082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20082; decide +kernel
    rw [ha]
    exact (canonical20082 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1200 + difference 4 5) (sourceB1200 + difference 5 4) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 4 5) (sourceB1200 + difference 5 4) sourceC1200) = raw5209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5209; decide +kernel
    rw [ha]
    exact (canonical5209 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1200 + difference 5 0) (sourceB1200 + difference 0 5) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4062) := by
    have ha : (tripleCharges (sourceA1200 + difference 5 0) (sourceB1200 + difference 0 5) sourceC1200) = raw20083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20083; decide +kernel
    rw [ha]
    exact (canonical20083 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1200 + difference 5 1) (sourceB1200 + difference 1 5) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 5 1) (sourceB1200 + difference 1 5) sourceC1200) = raw20084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20084; decide +kernel
    rw [ha]
    exact (canonical20084 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1200 + difference 5 2) (sourceB1200 + difference 2 5) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 5 2) (sourceB1200 + difference 2 5) sourceC1200) = raw20085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20085; decide +kernel
    rw [ha]
    exact (canonical20085 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1200 + difference 5 3) (sourceB1200 + difference 3 5) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 5 3) (sourceB1200 + difference 3 5) sourceC1200) = raw20086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20086; decide +kernel
    rw [ha]
    exact (canonical20086 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1200 + difference 5 4) (sourceB1200 + difference 4 5) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 5 4) (sourceB1200 + difference 4 5) sourceC1200) = raw20087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20087; decide +kernel
    rw [ha]
    exact (canonical20087 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1200 sourceB1200 sourceC1200
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1200, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1024 : Integer.Sparse.reindex keyMap MixedData.row1024 = numericRow1024 := by decide +kernel

theorem numericCheck1024 (x : Master → ℝ) : Integer.Sparse.eval numericRow1024 x =
    (1 : ℝ) * reducedSource1024 x := by
  norm_num [numericRow1024, reducedSource1024, Integer.Sparse.eval, Sparse.eval, nodeValue564, nodeValue726, nodeValue832, nodeValue859, nodeValue4071]

theorem reindexCheck1025 : Integer.Sparse.reindex keyMap MixedData.row1025 = numericRow1025 := by decide +kernel

theorem numericCheck1025 (x : Master → ℝ) : Integer.Sparse.eval numericRow1025 x =
    (1 : ℝ) * reducedSource1025 x := by
  norm_num [numericRow1025, reducedSource1025, Integer.Sparse.eval, Sparse.eval, nodeValue832, nodeValue1186, nodeValue1289, nodeValue1741, nodeValue4071]

theorem reindexCheck1026 : Integer.Sparse.reindex keyMap MixedData.row1026 = numericRow1026 := by decide +kernel

theorem numericCheck1026 (x : Master → ℝ) : Integer.Sparse.eval numericRow1026 x =
    (1 : ℝ) * reducedSource1026 x := by
  norm_num [numericRow1026, reducedSource1026, Integer.Sparse.eval, Sparse.eval, nodeValue785, nodeValue791, nodeValue812, nodeValue1710, nodeValue4069]

theorem reindexCheck1027 : Integer.Sparse.reindex keyMap MixedData.row1027 = numericRow1027 := by decide +kernel

theorem numericCheck1027 (x : Master → ℝ) : Integer.Sparse.eval numericRow1027 x =
    (1 : ℝ) * reducedSource1027 x := by
  norm_num [numericRow1027, reducedSource1027, Integer.Sparse.eval, Sparse.eval, nodeValue545, nodeValue705, nodeValue740, nodeValue791, nodeValue812, nodeValue4069]

theorem reindexCheck1028 : Integer.Sparse.reindex keyMap MixedData.row1028 = numericRow1028 := by decide +kernel

theorem numericCheck1028 (x : Master → ℝ) : Integer.Sparse.eval numericRow1028 x =
    (1 : ℝ) * reducedSource1028 x := by
  norm_num [numericRow1028, reducedSource1028, Integer.Sparse.eval, Sparse.eval, nodeValue791, nodeValue1199, nodeValue1231, nodeValue1710, nodeValue4069]

theorem reindexCheck1029 : Integer.Sparse.reindex keyMap MixedData.row1029 = numericRow1029 := by decide +kernel

theorem numericCheck1029 (x : Master → ℝ) : Integer.Sparse.eval numericRow1029 x =
    (1 : ℝ) * reducedSource1029 x := by
  norm_num [numericRow1029, reducedSource1029, Integer.Sparse.eval, Sparse.eval, nodeValue979, nodeValue986, nodeValue1007, nodeValue1037, nodeValue2208, nodeValue4081]

theorem reindexCheck1031 : Integer.Sparse.reindex keyMap MixedData.row1031 = numericRow1031 := by decide +kernel

theorem numericCheck1031 (x : Master → ℝ) : Integer.Sparse.eval numericRow1031 x =
    (1 : ℝ) * reducedSource1031 x := by
  norm_num [numericRow1031, reducedSource1031, Integer.Sparse.eval, Sparse.eval, nodeValue1521, nodeValue1541, nodeValue1677, nodeValue1730, nodeValue4085]

theorem reindexCheck1032 : Integer.Sparse.reindex keyMap MixedData.row1032 = numericRow1032 := by decide +kernel

theorem numericCheck1032 (x : Master → ℝ) : Integer.Sparse.eval numericRow1032 x =
    (1 : ℝ) * reducedSource1032 x := by
  norm_num [numericRow1032, reducedSource1032, Integer.Sparse.eval, Sparse.eval, nodeValue609, nodeValue622, nodeValue1096, nodeValue4085]

theorem reindexCheck1035 : Integer.Sparse.reindex keyMap MixedData.row1035 = numericRow1035 := by decide +kernel

theorem numericCheck1035 (x : Master → ℝ) : Integer.Sparse.eval numericRow1035 x =
    (1 : ℝ) * reducedSource1035 x := by
  norm_num [numericRow1035, reducedSource1035, Integer.Sparse.eval, Sparse.eval, nodeValue665, nodeValue686, nodeValue691, nodeValue750, nodeValue765, nodeValue770, nodeValue801, nodeValue809, nodeValue845, nodeValue1002, nodeValue1077, nodeValue1085, nodeValue4070]

theorem reindexCheck1036 : Integer.Sparse.reindex keyMap MixedData.row1036 = numericRow1036 := by decide +kernel

theorem numericCheck1036 (x : Master → ℝ) : Integer.Sparse.eval numericRow1036 x =
    (1 : ℝ) * reducedSource1036 x := by
  norm_num [numericRow1036, reducedSource1036, Integer.Sparse.eval, Sparse.eval, nodeValue549, nodeValue570, nodeValue596, nodeValue817, nodeValue4070]

theorem reindexCheck1037 : Integer.Sparse.reindex keyMap MixedData.row1037 = numericRow1037 := by decide +kernel

theorem numericCheck1037 (x : Master → ℝ) : Integer.Sparse.eval numericRow1037 x =
    (1 : ℝ) * reducedSource1037 x := by
  norm_num [numericRow1037, reducedSource1037, Integer.Sparse.eval, Sparse.eval, nodeValue540, nodeValue701, nodeValue735, nodeValue809, nodeValue817, nodeValue4070]

theorem reindexCheck1038 : Integer.Sparse.reindex keyMap MixedData.row1038 = numericRow1038 := by decide +kernel

theorem numericCheck1038 (x : Master → ℝ) : Integer.Sparse.eval numericRow1038 x =
    (1 : ℝ) * reducedSource1038 x := by
  norm_num [numericRow1038, reducedSource1038, Integer.Sparse.eval, Sparse.eval, nodeValue596, nodeValue735, nodeValue817, nodeValue1077, nodeValue4070]

theorem reindexCheck1039 : Integer.Sparse.reindex keyMap MixedData.row1039 = numericRow1039 := by decide +kernel

theorem numericCheck1039 (x : Master → ℝ) : Integer.Sparse.eval numericRow1039 x =
    (1 : ℝ) * reducedSource1039 x := by
  norm_num [numericRow1039, reducedSource1039, Integer.Sparse.eval, Sparse.eval, nodeValue4060, nodeValue4062, nodeValue4066, nodeValue4070, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1024 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1024 (mixedVector B) = 0 := by
  have h564 : mixedVector B (Sum.inr 564) = Sparse.eval nodeValue564 (mixedVector B) := by
    change mixedMoment B node564 node564Labels = _
    exact sound564 B hB hF
  have h726 : mixedVector B (Sum.inr 726) = Sparse.eval nodeValue726 (mixedVector B) := by
    change mixedMoment B node726 node726Labels = _
    exact sound726 B hB hF
  have h832 : mixedVector B (Sum.inr 832) = Sparse.eval nodeValue832 (mixedVector B) := by
    change mixedMoment B node832 node832Labels = _
    exact sound832 B hB hF
  have h859 : mixedVector B (Sum.inr 859) = Sparse.eval nodeValue859 (mixedVector B) := by
    change mixedMoment B node859 node859Labels = _
    exact sound859 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1179, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h564, h726, h832, h859, h4071, reducedSource1024] using sourceEq1179 B hB

theorem rowSound1024 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1024 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1024, numericCheck1024, reducedZero1024 B hB hF, mul_zero]

theorem reducedZero1025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1025 (mixedVector B) = 0 := by
  have h832 : mixedVector B (Sum.inr 832) = Sparse.eval nodeValue832 (mixedVector B) := by
    change mixedMoment B node832 node832Labels = _
    exact sound832 B hB hF
  have h1186 : mixedVector B (Sum.inr 1186) = Sparse.eval nodeValue1186 (mixedVector B) := by
    change mixedMoment B node1186 node1186Labels = _
    exact sound1186 B hB hF
  have h1289 : mixedVector B (Sum.inr 1289) = Sparse.eval nodeValue1289 (mixedVector B) := by
    change mixedMoment B node1289 node1289Labels = _
    exact sound1289 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1180, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h832, h1186, h1289, h1741, h4071, reducedSource1025] using sourceEq1180 B hB

theorem rowSound1025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1025 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1025, numericCheck1025, reducedZero1025 B hB hF, mul_zero]

theorem reducedZero1026 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1026 (mixedVector B) = 0 := by
  have h785 : mixedVector B (Sum.inr 785) = Sparse.eval nodeValue785 (mixedVector B) := by
    change mixedMoment B node785 node785Labels = _
    exact sound785 B hB hF
  have h791 : mixedVector B (Sum.inr 791) = Sparse.eval nodeValue791 (mixedVector B) := by
    change mixedMoment B node791 node791Labels = _
    exact sound791 B hB hF
  have h812 : mixedVector B (Sum.inr 812) = Sparse.eval nodeValue812 (mixedVector B) := by
    change mixedMoment B node812 node812Labels = _
    exact sound812 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1182, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h785, h791, h812, h1710, h4069, reducedSource1026] using sourceEq1182 B hB

theorem rowSound1026 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1026 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1026, numericCheck1026, reducedZero1026 B hB hF, mul_zero]

theorem reducedZero1027 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1027 (mixedVector B) = 0 := by
  have h545 : mixedVector B (Sum.inr 545) = Sparse.eval nodeValue545 (mixedVector B) := by
    change mixedMoment B node545 node545Labels = _
    exact sound545 B hB hF
  have h705 : mixedVector B (Sum.inr 705) = Sparse.eval nodeValue705 (mixedVector B) := by
    change mixedMoment B node705 node705Labels = _
    exact sound705 B hB hF
  have h740 : mixedVector B (Sum.inr 740) = Sparse.eval nodeValue740 (mixedVector B) := by
    change mixedMoment B node740 node740Labels = _
    exact sound740 B hB hF
  have h791 : mixedVector B (Sum.inr 791) = Sparse.eval nodeValue791 (mixedVector B) := by
    change mixedMoment B node791 node791Labels = _
    exact sound791 B hB hF
  have h812 : mixedVector B (Sum.inr 812) = Sparse.eval nodeValue812 (mixedVector B) := by
    change mixedMoment B node812 node812Labels = _
    exact sound812 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1183, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h545, h705, h740, h791, h812, h4069, reducedSource1027] using sourceEq1183 B hB

theorem rowSound1027 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1027 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1027, numericCheck1027, reducedZero1027 B hB hF, mul_zero]

theorem reducedZero1028 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1028 (mixedVector B) = 0 := by
  have h791 : mixedVector B (Sum.inr 791) = Sparse.eval nodeValue791 (mixedVector B) := by
    change mixedMoment B node791 node791Labels = _
    exact sound791 B hB hF
  have h1199 : mixedVector B (Sum.inr 1199) = Sparse.eval nodeValue1199 (mixedVector B) := by
    change mixedMoment B node1199 node1199Labels = _
    exact sound1199 B hB hF
  have h1231 : mixedVector B (Sum.inr 1231) = Sparse.eval nodeValue1231 (mixedVector B) := by
    change mixedMoment B node1231 node1231Labels = _
    exact sound1231 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1184, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h791, h1199, h1231, h1710, h4069, reducedSource1028] using sourceEq1184 B hB

theorem rowSound1028 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1028 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1028, numericCheck1028, reducedZero1028 B hB hF, mul_zero]

theorem reducedZero1029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1029 (mixedVector B) = 0 := by
  have h979 : mixedVector B (Sum.inr 979) = Sparse.eval nodeValue979 (mixedVector B) := by
    change mixedMoment B node979 node979Labels = _
    exact sound979 B hB hF
  have h986 : mixedVector B (Sum.inr 986) = Sparse.eval nodeValue986 (mixedVector B) := by
    change mixedMoment B node986 node986Labels = _
    exact sound986 B hB hF
  have h1007 : mixedVector B (Sum.inr 1007) = Sparse.eval nodeValue1007 (mixedVector B) := by
    change mixedMoment B node1007 node1007Labels = _
    exact sound1007 B hB hF
  have h1037 : mixedVector B (Sum.inr 1037) = Sparse.eval nodeValue1037 (mixedVector B) := by
    change mixedMoment B node1037 node1037Labels = _
    exact sound1037 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1186, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h979, h986, h1007, h1037, h2208, h4081, reducedSource1029] using sourceEq1186 B hB

theorem rowSound1029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1029 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1029, numericCheck1029, reducedZero1029 B hB hF, mul_zero]

theorem reducedZero1031 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1031 (mixedVector B) = 0 := by
  have h1521 : mixedVector B (Sum.inr 1521) = Sparse.eval nodeValue1521 (mixedVector B) := by
    change mixedMoment B node1521 node1521Labels = _
    exact sound1521 B hB hF
  have h1541 : mixedVector B (Sum.inr 1541) = Sparse.eval nodeValue1541 (mixedVector B) := by
    change mixedMoment B node1541 node1541Labels = _
    exact sound1541 B hB hF
  have h1677 : mixedVector B (Sum.inr 1677) = Sparse.eval nodeValue1677 (mixedVector B) := by
    change mixedMoment B node1677 node1677Labels = _
    exact sound1677 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1190, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1521, h1541, h1677, h1730, h4085, reducedSource1031] using sourceEq1190 B hB

theorem rowSound1031 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1031 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1031, numericCheck1031, reducedZero1031 B hB hF, mul_zero]

theorem reducedZero1032 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1032 (mixedVector B) = 0 := by
  have h609 : mixedVector B (Sum.inr 609) = Sparse.eval nodeValue609 (mixedVector B) := by
    change mixedMoment B node609 node609Labels = _
    exact sound609 B hB hF
  have h622 : mixedVector B (Sum.inr 622) = Sparse.eval nodeValue622 (mixedVector B) := by
    change mixedMoment B node622 node622Labels = _
    exact sound622 B hB hF
  have h1096 : mixedVector B (Sum.inr 1096) = Sparse.eval nodeValue1096 (mixedVector B) := by
    change mixedMoment B node1096 node1096Labels = _
    exact sound1096 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1191, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h609, h622, h1096, h4085, reducedSource1032] using sourceEq1191 B hB

theorem rowSound1032 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1032 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1032, numericCheck1032, reducedZero1032 B hB hF, mul_zero]

theorem reducedZero1035 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1035 (mixedVector B) = 0 := by
  have h665 : mixedVector B (Sum.inr 665) = Sparse.eval nodeValue665 (mixedVector B) := by
    change mixedMoment B node665 node665Labels = _
    exact sound665 B hB hF
  have h686 : mixedVector B (Sum.inr 686) = Sparse.eval nodeValue686 (mixedVector B) := by
    change mixedMoment B node686 node686Labels = _
    exact sound686 B hB hF
  have h691 : mixedVector B (Sum.inr 691) = Sparse.eval nodeValue691 (mixedVector B) := by
    change mixedMoment B node691 node691Labels = _
    exact sound691 B hB hF
  have h750 : mixedVector B (Sum.inr 750) = Sparse.eval nodeValue750 (mixedVector B) := by
    change mixedMoment B node750 node750Labels = _
    exact sound750 B hB hF
  have h765 : mixedVector B (Sum.inr 765) = Sparse.eval nodeValue765 (mixedVector B) := by
    change mixedMoment B node765 node765Labels = _
    exact sound765 B hB hF
  have h770 : mixedVector B (Sum.inr 770) = Sparse.eval nodeValue770 (mixedVector B) := by
    change mixedMoment B node770 node770Labels = _
    exact sound770 B hB hF
  have h801 : mixedVector B (Sum.inr 801) = Sparse.eval nodeValue801 (mixedVector B) := by
    change mixedMoment B node801 node801Labels = _
    exact sound801 B hB hF
  have h809 : mixedVector B (Sum.inr 809) = Sparse.eval nodeValue809 (mixedVector B) := by
    change mixedMoment B node809 node809Labels = _
    exact sound809 B hB hF
  have h845 : mixedVector B (Sum.inr 845) = Sparse.eval nodeValue845 (mixedVector B) := by
    change mixedMoment B node845 node845Labels = _
    exact sound845 B hB hF
  have h1002 : mixedVector B (Sum.inr 1002) = Sparse.eval nodeValue1002 (mixedVector B) := by
    change mixedMoment B node1002 node1002Labels = _
    exact sound1002 B hB hF
  have h1077 : mixedVector B (Sum.inr 1077) = Sparse.eval nodeValue1077 (mixedVector B) := by
    change mixedMoment B node1077 node1077Labels = _
    exact sound1077 B hB hF
  have h1085 : mixedVector B (Sum.inr 1085) = Sparse.eval nodeValue1085 (mixedVector B) := by
    change mixedMoment B node1085 node1085Labels = _
    exact sound1085 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1194, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h665, h686, h691, h750, h765, h770, h801, h809, h845, h1002, h1077, h1085, h4070, reducedSource1035] using sourceEq1194 B hB

theorem rowSound1035 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1035 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1035, numericCheck1035, reducedZero1035 B hB hF, mul_zero]

theorem reducedZero1036 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1036 (mixedVector B) = 0 := by
  have h549 : mixedVector B (Sum.inr 549) = Sparse.eval nodeValue549 (mixedVector B) := by
    change mixedMoment B node549 node549Labels = _
    exact sound549 B hB hF
  have h570 : mixedVector B (Sum.inr 570) = Sparse.eval nodeValue570 (mixedVector B) := by
    change mixedMoment B node570 node570Labels = _
    exact sound570 B hB hF
  have h596 : mixedVector B (Sum.inr 596) = Sparse.eval nodeValue596 (mixedVector B) := by
    change mixedMoment B node596 node596Labels = _
    exact sound596 B hB hF
  have h817 : mixedVector B (Sum.inr 817) = Sparse.eval nodeValue817 (mixedVector B) := by
    change mixedMoment B node817 node817Labels = _
    exact sound817 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1195, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h549, h570, h596, h817, h4070, reducedSource1036] using sourceEq1195 B hB

theorem rowSound1036 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1036 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1036, numericCheck1036, reducedZero1036 B hB hF, mul_zero]

theorem reducedZero1037 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1037 (mixedVector B) = 0 := by
  have h540 : mixedVector B (Sum.inr 540) = Sparse.eval nodeValue540 (mixedVector B) := by
    change mixedMoment B node540 node540Labels = _
    exact sound540 B hB hF
  have h701 : mixedVector B (Sum.inr 701) = Sparse.eval nodeValue701 (mixedVector B) := by
    change mixedMoment B node701 node701Labels = _
    exact sound701 B hB hF
  have h735 : mixedVector B (Sum.inr 735) = Sparse.eval nodeValue735 (mixedVector B) := by
    change mixedMoment B node735 node735Labels = _
    exact sound735 B hB hF
  have h809 : mixedVector B (Sum.inr 809) = Sparse.eval nodeValue809 (mixedVector B) := by
    change mixedMoment B node809 node809Labels = _
    exact sound809 B hB hF
  have h817 : mixedVector B (Sum.inr 817) = Sparse.eval nodeValue817 (mixedVector B) := by
    change mixedMoment B node817 node817Labels = _
    exact sound817 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1197, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h540, h701, h735, h809, h817, h4070, reducedSource1037] using sourceEq1197 B hB

theorem rowSound1037 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1037 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1037, numericCheck1037, reducedZero1037 B hB hF, mul_zero]

theorem reducedZero1038 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1038 (mixedVector B) = 0 := by
  have h596 : mixedVector B (Sum.inr 596) = Sparse.eval nodeValue596 (mixedVector B) := by
    change mixedMoment B node596 node596Labels = _
    exact sound596 B hB hF
  have h735 : mixedVector B (Sum.inr 735) = Sparse.eval nodeValue735 (mixedVector B) := by
    change mixedMoment B node735 node735Labels = _
    exact sound735 B hB hF
  have h817 : mixedVector B (Sum.inr 817) = Sparse.eval nodeValue817 (mixedVector B) := by
    change mixedMoment B node817 node817Labels = _
    exact sound817 B hB hF
  have h1077 : mixedVector B (Sum.inr 1077) = Sparse.eval nodeValue1077 (mixedVector B) := by
    change mixedMoment B node1077 node1077Labels = _
    exact sound1077 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1198, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h596, h735, h817, h1077, h4070, reducedSource1038] using sourceEq1198 B hB

theorem rowSound1038 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1038 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1038, numericCheck1038, reducedZero1038 B hB hF, mul_zero]

theorem reducedZero1039 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1039 (mixedVector B) = 0 := by
  have h4060 : mixedVector B (Sum.inr 4060) = Sparse.eval nodeValue4060 (mixedVector B) := by
    change mixedMoment B node4060 node4060Labels = _
    exact sound4060 B hB hF
  have h4062 : mixedVector B (Sum.inr 4062) = Sparse.eval nodeValue4062 (mixedVector B) := by
    change mixedMoment B node4062 node4062Labels = _
    exact sound4062 B hB hF
  have h4066 : mixedVector B (Sum.inr 4066) = Sparse.eval nodeValue4066 (mixedVector B) := by
    change mixedMoment B node4066 node4066Labels = _
    exact sound4066 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1200, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4060, h4062, h4066, h4070, h4085, reducedSource1039] using sourceEq1200 B hB

theorem rowSound1039 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1039 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1039, numericCheck1039, reducedZero1039 B hB hF, mul_zero]

theorem sourceRowsAt1024 : MixedData.sourceRows (1024 : Fin 2425) =
    MixedData.row1024 := by decide +kernel

theorem sourceRowsAt1025 : MixedData.sourceRows (1025 : Fin 2425) =
    MixedData.row1025 := by decide +kernel

theorem sourceRowsAt1026 : MixedData.sourceRows (1026 : Fin 2425) =
    MixedData.row1026 := by decide +kernel

theorem sourceRowsAt1027 : MixedData.sourceRows (1027 : Fin 2425) =
    MixedData.row1027 := by decide +kernel

theorem sourceRowsAt1028 : MixedData.sourceRows (1028 : Fin 2425) =
    MixedData.row1028 := by decide +kernel

theorem sourceRowsAt1029 : MixedData.sourceRows (1029 : Fin 2425) =
    MixedData.row1029 := by decide +kernel

theorem sourceRowsAt1030 : MixedData.sourceRows (1030 : Fin 2425) =
    MixedData.row1030 := by decide +kernel

theorem sourceRowsAt1031 : MixedData.sourceRows (1031 : Fin 2425) =
    MixedData.row1031 := by decide +kernel

theorem sourceRowsAt1032 : MixedData.sourceRows (1032 : Fin 2425) =
    MixedData.row1032 := by decide +kernel

theorem sourceRowsAt1033 : MixedData.sourceRows (1033 : Fin 2425) =
    MixedData.row1033 := by decide +kernel

theorem sourceRowsAt1034 : MixedData.sourceRows (1034 : Fin 2425) =
    MixedData.row1034 := by decide +kernel

theorem sourceRowsAt1035 : MixedData.sourceRows (1035 : Fin 2425) =
    MixedData.row1035 := by decide +kernel

theorem sourceRowsAt1036 : MixedData.sourceRows (1036 : Fin 2425) =
    MixedData.row1036 := by decide +kernel

theorem sourceRowsAt1037 : MixedData.sourceRows (1037 : Fin 2425) =
    MixedData.row1037 := by decide +kernel

theorem sourceRowsAt1038 : MixedData.sourceRows (1038 : Fin 2425) =
    MixedData.row1038 := by decide +kernel

theorem sourceRowsAt1039 : MixedData.sourceRows (1039 : Fin 2425) =
    MixedData.row1039 := by decide +kernel

theorem chunkSound64_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 64) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1024 ∨ k.val = 1025 ∨ k.val = 1026 ∨ k.val = 1027 ∨ k.val = 1028 ∨ k.val = 1029 ∨ k.val = 1030 ∨ k.val = 1031 ∨ k.val = 1032 ∨ k.val = 1033 ∨ k.val = 1034 ∨ k.val = 1035 ∨ k.val = 1036 ∨ k.val = 1037 ∨ k.val = 1038 ∨ k.val = 1039 := by omega
  rcases heq with h1024 | h1025 | h1026 | h1027 | h1028 | h1029 | h1030 | h1031 | h1032 | h1033 | h1034 | h1035 | h1036 | h1037 | h1038 | h1039
  · have he : k = (1024 : Fin 2425) := Fin.ext h1024
    subst k
    rw [sourceRowsAt1024]
    exact rowSound1024 B hB hF
  · have he : k = (1025 : Fin 2425) := Fin.ext h1025
    subst k
    rw [sourceRowsAt1025]
    exact rowSound1025 B hB hF
  · have he : k = (1026 : Fin 2425) := Fin.ext h1026
    subst k
    rw [sourceRowsAt1026]
    exact rowSound1026 B hB hF
  · have he : k = (1027 : Fin 2425) := Fin.ext h1027
    subst k
    rw [sourceRowsAt1027]
    exact rowSound1027 B hB hF
  · have he : k = (1028 : Fin 2425) := Fin.ext h1028
    subst k
    rw [sourceRowsAt1028]
    exact rowSound1028 B hB hF
  · have he : k = (1029 : Fin 2425) := Fin.ext h1029
    subst k
    rw [sourceRowsAt1029]
    exact rowSound1029 B hB hF
  · have he : k = (1030 : Fin 2425) := Fin.ext h1030
    subst k
    rw [sourceRowsAt1030]
    exact rowSound1030_e B hB hF
  · have he : k = (1031 : Fin 2425) := Fin.ext h1031
    subst k
    rw [sourceRowsAt1031]
    exact rowSound1031 B hB hF
  · have he : k = (1032 : Fin 2425) := Fin.ext h1032
    subst k
    rw [sourceRowsAt1032]
    exact rowSound1032 B hB hF
  · have he : k = (1033 : Fin 2425) := Fin.ext h1033
    subst k
    rw [sourceRowsAt1033]
    exact rowSound1033_e B hB hF
  · have he : k = (1034 : Fin 2425) := Fin.ext h1034
    subst k
    rw [sourceRowsAt1034]
    exact rowSound1034_e B hB hF
  · have he : k = (1035 : Fin 2425) := Fin.ext h1035
    subst k
    rw [sourceRowsAt1035]
    exact rowSound1035 B hB hF
  · have he : k = (1036 : Fin 2425) := Fin.ext h1036
    subst k
    rw [sourceRowsAt1036]
    exact rowSound1036 B hB hF
  · have he : k = (1037 : Fin 2425) := Fin.ext h1037
    subst k
    rw [sourceRowsAt1037]
    exact rowSound1037 B hB hF
  · have he : k = (1038 : Fin 2425) := Fin.ext h1038
    subst k
    rw [sourceRowsAt1038]
    exact rowSound1038 B hB hF
  · have he : k = (1039 : Fin 2425) := Fin.ext h1039
    subst k
    rw [sourceRowsAt1039]
    exact rowSound1039 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64_e_oai
