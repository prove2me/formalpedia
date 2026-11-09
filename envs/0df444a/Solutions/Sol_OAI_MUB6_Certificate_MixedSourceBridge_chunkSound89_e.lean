-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:57:05.211285+00:00
-- url     : https://prove2.me/submissions/5e716237-e6be-4f0d-b7b0-6b9b5beb4635

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1428_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1429_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1435_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1436_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1437_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical190
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24364 raw24364Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw24364 raw24364Labels = mixedMoment B raw24364step0 raw24364step0Labels := by
      have hz : ∀ j, raw24364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24364step0 = (fun i j => raw24364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24364step0 raw24364; decide +kernel
      have hl : raw24364step0Labels = raw24364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24364 raw24364Labels permutation346 hz
    mixedMoment B raw24364step0 raw24364step0Labels = mixedMoment B raw24364step1 raw24364step1Labels := by
      have ha : raw24364step1 = (fun i j => raw24364step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24364step1 raw24364step0; decide +kernel
      have hl : raw24364step1Labels = raw24364step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24364step0 raw24364step0Labels permutation44 permutation7
    mixedMoment B raw24364step1 raw24364step1Labels = mixedMoment B raw24364step2 raw24364step2Labels := by
      have ha : raw24364step2 = -raw24364step1 := by apply Matrix.ext; change ∀ i j, raw24364step2 i j = -(raw24364step1 i j); unfold raw24364step2 raw24364step1; decide +kernel
      have hl : raw24364step2Labels = raw24364step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24364step2 raw24364step2Labels = mixedMoment B raw24364step3 raw24364step3Labels := by
      have ha : raw24364step3 = raw24364step2 := by apply Matrix.ext; unfold raw24364step3 raw24364step2; decide +kernel
      have hl : raw24364step2Labels = labelEmbedding1 ∘ raw24364step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24364step2 raw24364step2Labels raw24364step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical24365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24365 raw24365Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw24365 raw24365Labels = mixedMoment B raw24365step0 raw24365step0Labels := by
      have hz : ∀ j, raw24365 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24365step0 = (fun i j => raw24365 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24365step0 raw24365; decide +kernel
      have hl : raw24365step0Labels = raw24365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24365 raw24365Labels permutation265 hz
    mixedMoment B raw24365step0 raw24365step0Labels = mixedMoment B raw24365step1 raw24365step1Labels := by
      have ha : raw24365step1 = (fun i j => raw24365step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24365step1 raw24365step0; decide +kernel
      have hl : raw24365step1Labels = raw24365step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24365step0 raw24365step0Labels permutation44 permutation7
    mixedMoment B raw24365step1 raw24365step1Labels = mixedMoment B raw24365step2 raw24365step2Labels := by
      have ha : raw24365step2 = -raw24365step1 := by apply Matrix.ext; change ∀ i j, raw24365step2 i j = -(raw24365step1 i j); unfold raw24365step2 raw24365step1; decide +kernel
      have hl : raw24365step2Labels = raw24365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24365step2 raw24365step2Labels = mixedMoment B raw24365step3 raw24365step3Labels := by
      have ha : raw24365step3 = raw24365step2 := by apply Matrix.ext; unfold raw24365step3 raw24365step2; decide +kernel
      have hl : raw24365step2Labels = labelEmbedding1 ∘ raw24365step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24365step2 raw24365step2Labels raw24365step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical24366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24366 raw24366Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw24366 raw24366Labels = mixedMoment B raw24366step0 raw24366step0Labels := by
      have hz : ∀ j, raw24366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24366step0 = (fun i j => raw24366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24366step0 raw24366; decide +kernel
      have hl : raw24366step0Labels = raw24366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24366 raw24366Labels permutation346 hz
    mixedMoment B raw24366step0 raw24366step0Labels = mixedMoment B raw24366step1 raw24366step1Labels := by
      have hz : ∀ j, raw24366step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24366step1 = (fun i j => raw24366step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24366step1 raw24366step0; decide +kernel
      have hl : raw24366step1Labels = raw24366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24366step0 raw24366step0Labels permutation56 hz
    mixedMoment B raw24366step1 raw24366step1Labels = mixedMoment B raw24366step2 raw24366step2Labels := by
      have ha : raw24366step2 = (fun i j => raw24366step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24366step2 raw24366step1; decide +kernel
      have hl : raw24366step2Labels = raw24366step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24366step1 raw24366step1Labels permutation10 permutation7
    mixedMoment B raw24366step2 raw24366step2Labels = mixedMoment B raw24366step3 raw24366step3Labels := by
      have ha : raw24366step3 = -raw24366step2 := by apply Matrix.ext; change ∀ i j, raw24366step3 i j = -(raw24366step2 i j); unfold raw24366step3 raw24366step2; decide +kernel
      have hl : raw24366step3Labels = raw24366step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24366step3 raw24366step3Labels = mixedMoment B raw24366step4 raw24366step4Labels := by
      have ha : raw24366step4 = raw24366step3 := by apply Matrix.ext; unfold raw24366step4 raw24366step3; decide +kernel
      have hl : raw24366step3Labels = labelEmbedding1 ∘ raw24366step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24366step3 raw24366step3Labels raw24366step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

theorem canonical24367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24367 raw24367Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw24367 raw24367Labels = mixedMoment B raw24367step0 raw24367step0Labels := by
      have hz : ∀ j, raw24367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24367step0 = (fun i j => raw24367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24367step0 raw24367; decide +kernel
      have hl : raw24367step0Labels = raw24367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24367 raw24367Labels permutation346 hz
    mixedMoment B raw24367step0 raw24367step0Labels = mixedMoment B raw24367step1 raw24367step1Labels := by
      have hz : ∀ j, raw24367step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24367step1 = (fun i j => raw24367step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24367step1 raw24367step0; decide +kernel
      have hl : raw24367step1Labels = raw24367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24367step0 raw24367step0Labels permutation56 hz
    mixedMoment B raw24367step1 raw24367step1Labels = mixedMoment B raw24367step2 raw24367step2Labels := by
      have ha : raw24367step2 = (fun i j => raw24367step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24367step2 raw24367step1; decide +kernel
      have hl : raw24367step2Labels = raw24367step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24367step1 raw24367step1Labels permutation10 permutation7
    mixedMoment B raw24367step2 raw24367step2Labels = mixedMoment B raw24367step3 raw24367step3Labels := by
      have ha : raw24367step3 = -raw24367step2 := by apply Matrix.ext; change ∀ i j, raw24367step3 i j = -(raw24367step2 i j); unfold raw24367step3 raw24367step2; decide +kernel
      have hl : raw24367step3Labels = raw24367step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24367step3 raw24367step3Labels = mixedMoment B raw24367step4 raw24367step4Labels := by
      have ha : raw24367step4 = raw24367step3 := by apply Matrix.ext; unfold raw24367step4 raw24367step3; decide +kernel
      have hl : raw24367step3Labels = labelEmbedding1 ∘ raw24367step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24367step3 raw24367step3Labels raw24367step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical24368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24368 raw24368Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw24368 raw24368Labels = mixedMoment B raw24368step0 raw24368step0Labels := by
      have hz : ∀ j, raw24368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24368step0 = (fun i j => raw24368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24368step0 raw24368; decide +kernel
      have hl : raw24368step0Labels = raw24368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24368 raw24368Labels permutation346 hz
    mixedMoment B raw24368step0 raw24368step0Labels = mixedMoment B raw24368step1 raw24368step1Labels := by
      have hz : ∀ j, raw24368step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24368step1 = (fun i j => raw24368step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24368step1 raw24368step0; decide +kernel
      have hl : raw24368step1Labels = raw24368step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24368step0 raw24368step0Labels permutation56 hz
    mixedMoment B raw24368step1 raw24368step1Labels = mixedMoment B raw24368step2 raw24368step2Labels := by
      have ha : raw24368step2 = (fun i j => raw24368step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24368step2 raw24368step1; decide +kernel
      have hl : raw24368step2Labels = raw24368step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24368step1 raw24368step1Labels permutation10 permutation7
    mixedMoment B raw24368step2 raw24368step2Labels = mixedMoment B raw24368step3 raw24368step3Labels := by
      have ha : raw24368step3 = -raw24368step2 := by apply Matrix.ext; change ∀ i j, raw24368step3 i j = -(raw24368step2 i j); unfold raw24368step3 raw24368step2; decide +kernel
      have hl : raw24368step3Labels = raw24368step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24368step3 raw24368step3Labels = mixedMoment B raw24368step4 raw24368step4Labels := by
      have ha : raw24368step4 = raw24368step3 := by apply Matrix.ext; unfold raw24368step4 raw24368step3; decide +kernel
      have hl : raw24368step3Labels = labelEmbedding1 ∘ raw24368step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24368step3 raw24368step3Labels raw24368step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical24369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24369 raw24369Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw24369 raw24369Labels = mixedMoment B raw24369step0 raw24369step0Labels := by
      have hz : ∀ j, raw24369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24369step0 = (fun i j => raw24369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24369step0 raw24369; decide +kernel
      have hl : raw24369step0Labels = raw24369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24369 raw24369Labels permutation346 hz
    mixedMoment B raw24369step0 raw24369step0Labels = mixedMoment B raw24369step1 raw24369step1Labels := by
      have ha : raw24369step1 = (fun i j => raw24369step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24369step1 raw24369step0; decide +kernel
      have hl : raw24369step1Labels = raw24369step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24369step0 raw24369step0Labels permutation42 permutation5
    mixedMoment B raw24369step1 raw24369step1Labels = mixedMoment B raw24369step2 raw24369step2Labels := by
      have ha : raw24369step2 = -raw24369step1 := by apply Matrix.ext; change ∀ i j, raw24369step2 i j = -(raw24369step1 i j); unfold raw24369step2 raw24369step1; decide +kernel
      have hl : raw24369step2Labels = raw24369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24369step2 raw24369step2Labels = mixedMoment B raw24369step3 raw24369step3Labels := by
      have ha : raw24369step3 = raw24369step2 := by apply Matrix.ext; unfold raw24369step3 raw24369step2; decide +kernel
      have hl : raw24369step2Labels = labelEmbedding1 ∘ raw24369step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24369step2 raw24369step2Labels raw24369step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

theorem canonical24370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24370 raw24370Labels = mixedMoment B node3259 node3259Labels := by
  calc
    mixedMoment B raw24370 raw24370Labels = mixedMoment B raw24370step0 raw24370step0Labels := by
      have ha : raw24370step0 = (fun i j => raw24370 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24370step0 raw24370; decide +kernel
      have hl : raw24370step0Labels = raw24370Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24370 raw24370Labels permutation186 permutation5
    mixedMoment B raw24370step0 raw24370step0Labels = mixedMoment B raw24370step1 raw24370step1Labels := by
      have ha : raw24370step1 = -raw24370step0 := by apply Matrix.ext; change ∀ i j, raw24370step1 i j = -(raw24370step0 i j); unfold raw24370step1 raw24370step0; decide +kernel
      have hl : raw24370step1Labels = raw24370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24370step1 raw24370step1Labels = mixedMoment B raw24370step2 raw24370step2Labels := by
      have ha : raw24370step2 = raw24370step1 := by apply Matrix.ext; unfold raw24370step2 raw24370step1; decide +kernel
      have hl : raw24370step1Labels = labelEmbedding1 ∘ raw24370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24370step1 raw24370step1Labels raw24370step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3259 node3259Labels := by rfl

theorem canonical24371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24371 raw24371Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw24371 raw24371Labels = mixedMoment B raw24371step0 raw24371step0Labels := by
      have hz : ∀ j, raw24371 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24371step0 = (fun i j => raw24371 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24371step0 raw24371; decide +kernel
      have hl : raw24371step0Labels = raw24371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24371 raw24371Labels permutation346 hz
    mixedMoment B raw24371step0 raw24371step0Labels = mixedMoment B raw24371step1 raw24371step1Labels := by
      have ha : raw24371step1 = (fun i j => raw24371step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24371step1 raw24371step0; decide +kernel
      have hl : raw24371step1Labels = raw24371step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24371step0 raw24371step0Labels permutation42 permutation5
    mixedMoment B raw24371step1 raw24371step1Labels = mixedMoment B raw24371step2 raw24371step2Labels := by
      have ha : raw24371step2 = -raw24371step1 := by apply Matrix.ext; change ∀ i j, raw24371step2 i j = -(raw24371step1 i j); unfold raw24371step2 raw24371step1; decide +kernel
      have hl : raw24371step2Labels = raw24371step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24371step2 raw24371step2Labels = mixedMoment B raw24371step3 raw24371step3Labels := by
      have ha : raw24371step3 = raw24371step2 := by apply Matrix.ext; unfold raw24371step3 raw24371step2; decide +kernel
      have hl : raw24371step2Labels = labelEmbedding1 ∘ raw24371step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24371step2 raw24371step2Labels raw24371step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical24372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24372 raw24372Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw24372 raw24372Labels = mixedMoment B raw24372step0 raw24372step0Labels := by
      have hz : ∀ j, raw24372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24372step0 = (fun i j => raw24372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24372step0 raw24372; decide +kernel
      have hl : raw24372step0Labels = raw24372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24372 raw24372Labels permutation346 hz
    mixedMoment B raw24372step0 raw24372step0Labels = mixedMoment B raw24372step1 raw24372step1Labels := by
      have ha : raw24372step1 = (fun i j => raw24372step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24372step1 raw24372step0; decide +kernel
      have hl : raw24372step1Labels = raw24372step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24372step0 raw24372step0Labels permutation44 permutation7
    mixedMoment B raw24372step1 raw24372step1Labels = mixedMoment B raw24372step2 raw24372step2Labels := by
      have ha : raw24372step2 = -raw24372step1 := by apply Matrix.ext; change ∀ i j, raw24372step2 i j = -(raw24372step1 i j); unfold raw24372step2 raw24372step1; decide +kernel
      have hl : raw24372step2Labels = raw24372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24372step2 raw24372step2Labels = mixedMoment B raw24372step3 raw24372step3Labels := by
      have ha : raw24372step3 = raw24372step2 := by apply Matrix.ext; unfold raw24372step3 raw24372step2; decide +kernel
      have hl : raw24372step2Labels = labelEmbedding1 ∘ raw24372step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24372step2 raw24372step2Labels raw24372step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical24373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24373 raw24373Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw24373 raw24373Labels = mixedMoment B raw24373step0 raw24373step0Labels := by
      have hz : ∀ j, raw24373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24373step0 = (fun i j => raw24373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24373step0 raw24373; decide +kernel
      have hl : raw24373step0Labels = raw24373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24373 raw24373Labels permutation346 hz
    mixedMoment B raw24373step0 raw24373step0Labels = mixedMoment B raw24373step1 raw24373step1Labels := by
      have ha : raw24373step1 = (fun i j => raw24373step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24373step1 raw24373step0; decide +kernel
      have hl : raw24373step1Labels = raw24373step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24373step0 raw24373step0Labels permutation52 permutation5
    mixedMoment B raw24373step1 raw24373step1Labels = mixedMoment B raw24373step2 raw24373step2Labels := by
      have ha : raw24373step2 = -raw24373step1 := by apply Matrix.ext; change ∀ i j, raw24373step2 i j = -(raw24373step1 i j); unfold raw24373step2 raw24373step1; decide +kernel
      have hl : raw24373step2Labels = raw24373step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24373step2 raw24373step2Labels = mixedMoment B raw24373step3 raw24373step3Labels := by
      have ha : raw24373step3 = raw24373step2 := by apply Matrix.ext; unfold raw24373step3 raw24373step2; decide +kernel
      have hl : raw24373step2Labels = labelEmbedding1 ∘ raw24373step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24373step2 raw24373step2Labels raw24373step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

theorem canonical24374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24374 raw24374Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw24374 raw24374Labels = mixedMoment B raw24374step0 raw24374step0Labels := by
      have hz : ∀ j, raw24374 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24374step0 = (fun i j => raw24374 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24374step0 raw24374; decide +kernel
      have hl : raw24374step0Labels = raw24374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24374 raw24374Labels permutation265 hz
    mixedMoment B raw24374step0 raw24374step0Labels = mixedMoment B raw24374step1 raw24374step1Labels := by
      have ha : raw24374step1 = (fun i j => raw24374step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24374step1 raw24374step0; decide +kernel
      have hl : raw24374step1Labels = raw24374step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24374step0 raw24374step0Labels permutation42 permutation5
    mixedMoment B raw24374step1 raw24374step1Labels = mixedMoment B raw24374step2 raw24374step2Labels := by
      have ha : raw24374step2 = -raw24374step1 := by apply Matrix.ext; change ∀ i j, raw24374step2 i j = -(raw24374step1 i j); unfold raw24374step2 raw24374step1; decide +kernel
      have hl : raw24374step2Labels = raw24374step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24374step2 raw24374step2Labels = mixedMoment B raw24374step3 raw24374step3Labels := by
      have ha : raw24374step3 = raw24374step2 := by apply Matrix.ext; unfold raw24374step3 raw24374step2; decide +kernel
      have hl : raw24374step2Labels = labelEmbedding1 ∘ raw24374step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24374step2 raw24374step2Labels raw24374step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

theorem canonical24375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24375 raw24375Labels = mixedMoment B node3259 node3259Labels := by
  calc
    mixedMoment B raw24375 raw24375Labels = mixedMoment B raw24375step0 raw24375step0Labels := by
      have ha : raw24375step0 = (fun i j => raw24375 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24375step0 raw24375; decide +kernel
      have hl : raw24375step0Labels = raw24375Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24375 raw24375Labels permutation162 permutation5
    mixedMoment B raw24375step0 raw24375step0Labels = mixedMoment B raw24375step1 raw24375step1Labels := by
      have ha : raw24375step1 = -raw24375step0 := by apply Matrix.ext; change ∀ i j, raw24375step1 i j = -(raw24375step0 i j); unfold raw24375step1 raw24375step0; decide +kernel
      have hl : raw24375step1Labels = raw24375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24375step1 raw24375step1Labels = mixedMoment B raw24375step2 raw24375step2Labels := by
      have ha : raw24375step2 = raw24375step1 := by apply Matrix.ext; unfold raw24375step2 raw24375step1; decide +kernel
      have hl : raw24375step1Labels = labelEmbedding1 ∘ raw24375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24375step1 raw24375step1Labels raw24375step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3259 node3259Labels := by rfl

theorem canonical24376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24376 raw24376Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw24376 raw24376Labels = mixedMoment B raw24376step0 raw24376step0Labels := by
      have hz : ∀ j, raw24376 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24376step0 = (fun i j => raw24376 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24376step0 raw24376; decide +kernel
      have hl : raw24376step0Labels = raw24376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24376 raw24376Labels permutation265 hz
    mixedMoment B raw24376step0 raw24376step0Labels = mixedMoment B raw24376step1 raw24376step1Labels := by
      have ha : raw24376step1 = (fun i j => raw24376step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24376step1 raw24376step0; decide +kernel
      have hl : raw24376step1Labels = raw24376step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24376step0 raw24376step0Labels permutation42 permutation5
    mixedMoment B raw24376step1 raw24376step1Labels = mixedMoment B raw24376step2 raw24376step2Labels := by
      have ha : raw24376step2 = -raw24376step1 := by apply Matrix.ext; change ∀ i j, raw24376step2 i j = -(raw24376step1 i j); unfold raw24376step2 raw24376step1; decide +kernel
      have hl : raw24376step2Labels = raw24376step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24376step2 raw24376step2Labels = mixedMoment B raw24376step3 raw24376step3Labels := by
      have ha : raw24376step3 = raw24376step2 := by apply Matrix.ext; unfold raw24376step3 raw24376step2; decide +kernel
      have hl : raw24376step2Labels = labelEmbedding1 ∘ raw24376step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24376step2 raw24376step2Labels raw24376step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical24377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24377 raw24377Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw24377 raw24377Labels = mixedMoment B raw24377step0 raw24377step0Labels := by
      have hz : ∀ j, raw24377 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24377step0 = (fun i j => raw24377 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24377step0 raw24377; decide +kernel
      have hl : raw24377step0Labels = raw24377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24377 raw24377Labels permutation265 hz
    mixedMoment B raw24377step0 raw24377step0Labels = mixedMoment B raw24377step1 raw24377step1Labels := by
      have ha : raw24377step1 = (fun i j => raw24377step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24377step1 raw24377step0; decide +kernel
      have hl : raw24377step1Labels = raw24377step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24377step0 raw24377step0Labels permutation44 permutation7
    mixedMoment B raw24377step1 raw24377step1Labels = mixedMoment B raw24377step2 raw24377step2Labels := by
      have ha : raw24377step2 = -raw24377step1 := by apply Matrix.ext; change ∀ i j, raw24377step2 i j = -(raw24377step1 i j); unfold raw24377step2 raw24377step1; decide +kernel
      have hl : raw24377step2Labels = raw24377step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24377step2 raw24377step2Labels = mixedMoment B raw24377step3 raw24377step3Labels := by
      have ha : raw24377step3 = raw24377step2 := by apply Matrix.ext; unfold raw24377step3 raw24377step2; decide +kernel
      have hl : raw24377step2Labels = labelEmbedding1 ∘ raw24377step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24377step2 raw24377step2Labels raw24377step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical24378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24378 raw24378Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw24378 raw24378Labels = mixedMoment B raw24378step0 raw24378step0Labels := by
      have hz : ∀ j, raw24378 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24378step0 = (fun i j => raw24378 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24378step0 raw24378; decide +kernel
      have hl : raw24378step0Labels = raw24378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24378 raw24378Labels permutation265 hz
    mixedMoment B raw24378step0 raw24378step0Labels = mixedMoment B raw24378step1 raw24378step1Labels := by
      have ha : raw24378step1 = (fun i j => raw24378step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24378step1 raw24378step0; decide +kernel
      have hl : raw24378step1Labels = raw24378step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24378step0 raw24378step0Labels permutation52 permutation5
    mixedMoment B raw24378step1 raw24378step1Labels = mixedMoment B raw24378step2 raw24378step2Labels := by
      have ha : raw24378step2 = -raw24378step1 := by apply Matrix.ext; change ∀ i j, raw24378step2 i j = -(raw24378step1 i j); unfold raw24378step2 raw24378step1; decide +kernel
      have hl : raw24378step2Labels = raw24378step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24378step2 raw24378step2Labels = mixedMoment B raw24378step3 raw24378step3Labels := by
      have ha : raw24378step3 = raw24378step2 := by apply Matrix.ext; unfold raw24378step3 raw24378step2; decide +kernel
      have hl : raw24378step2Labels = labelEmbedding1 ∘ raw24378step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24378step2 raw24378step2Labels raw24378step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

theorem canonical24379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24379 raw24379Labels = mixedMoment B node1526 node1526Labels := by
  calc
    mixedMoment B raw24379 raw24379Labels = mixedMoment B raw24379step0 raw24379step0Labels := by
      have hz : ∀ j, raw24379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24379step0 = (fun i j => raw24379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24379step0 raw24379; decide +kernel
      have hl : raw24379step0Labels = raw24379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24379 raw24379Labels permutation346 hz
    mixedMoment B raw24379step0 raw24379step0Labels = mixedMoment B raw24379step1 raw24379step1Labels := by
      have hz : ∀ j, raw24379step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24379step1 = (fun i j => raw24379step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24379step1 raw24379step0; decide +kernel
      have hl : raw24379step1Labels = raw24379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24379step0 raw24379step0Labels permutation56 hz
    mixedMoment B raw24379step1 raw24379step1Labels = mixedMoment B raw24379step2 raw24379step2Labels := by
      have ha : raw24379step2 = (fun i j => raw24379step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24379step2 raw24379step1; decide +kernel
      have hl : raw24379step2Labels = raw24379step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24379step1 raw24379step1Labels permutation12 permutation5
    mixedMoment B raw24379step2 raw24379step2Labels = mixedMoment B raw24379step3 raw24379step3Labels := by
      have ha : raw24379step3 = -raw24379step2 := by apply Matrix.ext; change ∀ i j, raw24379step3 i j = -(raw24379step2 i j); unfold raw24379step3 raw24379step2; decide +kernel
      have hl : raw24379step3Labels = raw24379step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24379step3 raw24379step3Labels = mixedMoment B raw24379step4 raw24379step4Labels := by
      have ha : raw24379step4 = raw24379step3 := by apply Matrix.ext; unfold raw24379step4 raw24379step3; decide +kernel
      have hl : raw24379step3Labels = labelEmbedding1 ∘ raw24379step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24379step3 raw24379step3Labels raw24379step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1526 node1526Labels := by rfl

theorem canonical24380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24380 raw24380Labels = mixedMoment B node3271 node3271Labels := by
  calc
    mixedMoment B raw24380 raw24380Labels = mixedMoment B raw24380step0 raw24380step0Labels := by
      have hz : ∀ j, raw24380 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24380step0 = (fun i j => raw24380 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24380step0 raw24380; decide +kernel
      have hl : raw24380step0Labels = raw24380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24380 raw24380Labels permutation346 hz
    mixedMoment B raw24380step0 raw24380step0Labels = mixedMoment B raw24380step1 raw24380step1Labels := by
      have ha : raw24380step1 = (fun i j => raw24380step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24380step1 raw24380step0; decide +kernel
      have hl : raw24380step1Labels = raw24380step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24380step0 raw24380step0Labels permutation36 permutation5
    mixedMoment B raw24380step1 raw24380step1Labels = mixedMoment B raw24380step2 raw24380step2Labels := by
      have ha : raw24380step2 = -raw24380step1 := by apply Matrix.ext; change ∀ i j, raw24380step2 i j = -(raw24380step1 i j); unfold raw24380step2 raw24380step1; decide +kernel
      have hl : raw24380step2Labels = raw24380step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24380step2 raw24380step2Labels = mixedMoment B raw24380step3 raw24380step3Labels := by
      have ha : raw24380step3 = raw24380step2 := by apply Matrix.ext; unfold raw24380step3 raw24380step2; decide +kernel
      have hl : raw24380step2Labels = labelEmbedding1 ∘ raw24380step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24380step2 raw24380step2Labels raw24380step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3271 node3271Labels := by rfl

theorem canonical24381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24381 raw24381Labels = mixedMoment B node3271 node3271Labels := by
  calc
    mixedMoment B raw24381 raw24381Labels = mixedMoment B raw24381step0 raw24381step0Labels := by
      have hz : ∀ j, raw24381 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24381step0 = (fun i j => raw24381 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24381step0 raw24381; decide +kernel
      have hl : raw24381step0Labels = raw24381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24381 raw24381Labels permutation265 hz
    mixedMoment B raw24381step0 raw24381step0Labels = mixedMoment B raw24381step1 raw24381step1Labels := by
      have ha : raw24381step1 = (fun i j => raw24381step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24381step1 raw24381step0; decide +kernel
      have hl : raw24381step1Labels = raw24381step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24381step0 raw24381step0Labels permutation36 permutation5
    mixedMoment B raw24381step1 raw24381step1Labels = mixedMoment B raw24381step2 raw24381step2Labels := by
      have ha : raw24381step2 = -raw24381step1 := by apply Matrix.ext; change ∀ i j, raw24381step2 i j = -(raw24381step1 i j); unfold raw24381step2 raw24381step1; decide +kernel
      have hl : raw24381step2Labels = raw24381step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24381step2 raw24381step2Labels = mixedMoment B raw24381step3 raw24381step3Labels := by
      have ha : raw24381step3 = raw24381step2 := by apply Matrix.ext; unfold raw24381step3 raw24381step2; decide +kernel
      have hl : raw24381step2Labels = labelEmbedding1 ∘ raw24381step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24381step2 raw24381step2Labels raw24381step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3271 node3271Labels := by rfl

theorem canonical24382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24382 raw24382Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw24382 raw24382Labels = mixedMoment B raw24382step0 raw24382step0Labels := by
      have hz : ∀ j, raw24382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24382step0 = (fun i j => raw24382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24382step0 raw24382; decide +kernel
      have hl : raw24382step0Labels = raw24382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24382 raw24382Labels permutation346 hz
    mixedMoment B raw24382step0 raw24382step0Labels = mixedMoment B raw24382step1 raw24382step1Labels := by
      have hz : ∀ j, raw24382step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24382step1 = (fun i j => raw24382step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24382step1 raw24382step0; decide +kernel
      have hl : raw24382step1Labels = raw24382step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24382step0 raw24382step0Labels permutation56 hz
    mixedMoment B raw24382step1 raw24382step1Labels = mixedMoment B raw24382step2 raw24382step2Labels := by
      have ha : raw24382step2 = (fun i j => raw24382step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24382step2 raw24382step1; decide +kernel
      have hl : raw24382step2Labels = raw24382step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24382step1 raw24382step1Labels permutation10 permutation7
    mixedMoment B raw24382step2 raw24382step2Labels = mixedMoment B raw24382step3 raw24382step3Labels := by
      have ha : raw24382step3 = -raw24382step2 := by apply Matrix.ext; change ∀ i j, raw24382step3 i j = -(raw24382step2 i j); unfold raw24382step3 raw24382step2; decide +kernel
      have hl : raw24382step3Labels = raw24382step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24382step3 raw24382step3Labels = mixedMoment B raw24382step4 raw24382step4Labels := by
      have ha : raw24382step4 = raw24382step3 := by apply Matrix.ext; unfold raw24382step4 raw24382step3; decide +kernel
      have hl : raw24382step3Labels = labelEmbedding1 ∘ raw24382step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24382step3 raw24382step3Labels raw24382step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical24383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24383 raw24383Labels = mixedMoment B node3306 node3306Labels := by
  calc
    mixedMoment B raw24383 raw24383Labels = mixedMoment B raw24383step0 raw24383step0Labels := by
      have hz : ∀ j, raw24383 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24383step0 = (fun i j => raw24383 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24383step0 raw24383; decide +kernel
      have hl : raw24383step0Labels = raw24383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24383 raw24383Labels permutation346 hz
    mixedMoment B raw24383step0 raw24383step0Labels = mixedMoment B raw24383step1 raw24383step1Labels := by
      have hz : ∀ j, raw24383step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24383step1 = (fun i j => raw24383step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24383step1 raw24383step0; decide +kernel
      have hl : raw24383step1Labels = raw24383step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24383step0 raw24383step0Labels permutation56 hz
    mixedMoment B raw24383step1 raw24383step1Labels = mixedMoment B raw24383step2 raw24383step2Labels := by
      have ha : raw24383step2 = (fun i j => raw24383step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24383step2 raw24383step1; decide +kernel
      have hl : raw24383step2Labels = raw24383step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24383step1 raw24383step1Labels permutation12 permutation5
    mixedMoment B raw24383step2 raw24383step2Labels = mixedMoment B raw24383step3 raw24383step3Labels := by
      have ha : raw24383step3 = -raw24383step2 := by apply Matrix.ext; change ∀ i j, raw24383step3 i j = -(raw24383step2 i j); unfold raw24383step3 raw24383step2; decide +kernel
      have hl : raw24383step3Labels = raw24383step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24383step3 raw24383step3Labels = mixedMoment B raw24383step4 raw24383step4Labels := by
      have ha : raw24383step4 = raw24383step3 := by apply Matrix.ext; unfold raw24383step4 raw24383step3; decide +kernel
      have hl : raw24383step3Labels = labelEmbedding1 ∘ raw24383step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24383step3 raw24383step3Labels raw24383step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3306 node3306Labels := by rfl

theorem canonical24384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24384 raw24384Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw24384 raw24384Labels = mixedMoment B raw24384step0 raw24384step0Labels := by
      have hz : ∀ j, raw24384 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24384step0 = (fun i j => raw24384 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24384step0 raw24384; decide +kernel
      have hl : raw24384step0Labels = raw24384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24384 raw24384Labels permutation346 hz
    mixedMoment B raw24384step0 raw24384step0Labels = mixedMoment B raw24384step1 raw24384step1Labels := by
      have hz : ∀ j, raw24384step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24384step1 = (fun i j => raw24384step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24384step1 raw24384step0; decide +kernel
      have hl : raw24384step1Labels = raw24384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24384step0 raw24384step0Labels permutation56 hz
    mixedMoment B raw24384step1 raw24384step1Labels = mixedMoment B raw24384step2 raw24384step2Labels := by
      have ha : raw24384step2 = (fun i j => raw24384step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24384step2 raw24384step1; decide +kernel
      have hl : raw24384step2Labels = raw24384step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24384step1 raw24384step1Labels permutation9 permutation5
    mixedMoment B raw24384step2 raw24384step2Labels = mixedMoment B raw24384step3 raw24384step3Labels := by
      have ha : raw24384step3 = -raw24384step2 := by apply Matrix.ext; change ∀ i j, raw24384step3 i j = -(raw24384step2 i j); unfold raw24384step3 raw24384step2; decide +kernel
      have hl : raw24384step3Labels = raw24384step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24384step3 raw24384step3Labels = mixedMoment B raw24384step4 raw24384step4Labels := by
      have ha : raw24384step4 = raw24384step3 := by apply Matrix.ext; unfold raw24384step4 raw24384step3; decide +kernel
      have hl : raw24384step3Labels = labelEmbedding1 ∘ raw24384step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24384step3 raw24384step3Labels raw24384step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

theorem canonical24385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24385 raw24385Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw24385 raw24385Labels = mixedMoment B raw24385step0 raw24385step0Labels := by
      have hz : ∀ j, raw24385 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24385step0 = (fun i j => raw24385 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24385step0 raw24385; decide +kernel
      have hl : raw24385step0Labels = raw24385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24385 raw24385Labels permutation346 hz
    mixedMoment B raw24385step0 raw24385step0Labels = mixedMoment B raw24385step1 raw24385step1Labels := by
      have ha : raw24385step1 = (fun i j => raw24385step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24385step1 raw24385step0; decide +kernel
      have hl : raw24385step1Labels = raw24385step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24385step0 raw24385step0Labels permutation127 permutation5
    mixedMoment B raw24385step1 raw24385step1Labels = mixedMoment B raw24385step2 raw24385step2Labels := by
      have ha : raw24385step2 = raw24385step1 := by apply Matrix.ext; unfold raw24385step2 raw24385step1; decide +kernel
      have hl : raw24385step1Labels = labelEmbedding1 ∘ raw24385step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24385step1 raw24385step1Labels raw24385step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

theorem canonical24386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24386 raw24386Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw24386 raw24386Labels = mixedMoment B raw24386step0 raw24386step0Labels := by
      have hz : ∀ j, raw24386 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24386step0 = (fun i j => raw24386 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24386step0 raw24386; decide +kernel
      have hl : raw24386step0Labels = raw24386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24386 raw24386Labels permutation265 hz
    mixedMoment B raw24386step0 raw24386step0Labels = mixedMoment B raw24386step1 raw24386step1Labels := by
      have ha : raw24386step1 = (fun i j => raw24386step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24386step1 raw24386step0; decide +kernel
      have hl : raw24386step1Labels = raw24386step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24386step0 raw24386step0Labels permutation127 permutation5
    mixedMoment B raw24386step1 raw24386step1Labels = mixedMoment B raw24386step2 raw24386step2Labels := by
      have ha : raw24386step2 = raw24386step1 := by apply Matrix.ext; unfold raw24386step2 raw24386step1; decide +kernel
      have hl : raw24386step1Labels = labelEmbedding1 ∘ raw24386step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24386step1 raw24386step1Labels raw24386step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

theorem canonical24387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24387 raw24387Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw24387 raw24387Labels = mixedMoment B raw24387step0 raw24387step0Labels := by
      have hz : ∀ j, raw24387 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24387step0 = (fun i j => raw24387 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24387step0 raw24387; decide +kernel
      have hl : raw24387step0Labels = raw24387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24387 raw24387Labels permutation346 hz
    mixedMoment B raw24387step0 raw24387step0Labels = mixedMoment B raw24387step1 raw24387step1Labels := by
      have hz : ∀ j, raw24387step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24387step1 = (fun i j => raw24387step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24387step1 raw24387step0; decide +kernel
      have hl : raw24387step1Labels = raw24387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24387step0 raw24387step0Labels permutation56 hz
    mixedMoment B raw24387step1 raw24387step1Labels = mixedMoment B raw24387step2 raw24387step2Labels := by
      have ha : raw24387step2 = (fun i j => raw24387step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24387step2 raw24387step1; decide +kernel
      have hl : raw24387step2Labels = raw24387step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24387step1 raw24387step1Labels permutation25 permutation5
    mixedMoment B raw24387step2 raw24387step2Labels = mixedMoment B raw24387step3 raw24387step3Labels := by
      have ha : raw24387step3 = raw24387step2 := by apply Matrix.ext; unfold raw24387step3 raw24387step2; decide +kernel
      have hl : raw24387step2Labels = labelEmbedding1 ∘ raw24387step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24387step2 raw24387step2Labels raw24387step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical24388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24388 raw24388Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw24388 raw24388Labels = mixedMoment B raw24388step0 raw24388step0Labels := by
      have hz : ∀ j, raw24388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24388step0 = (fun i j => raw24388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24388step0 raw24388; decide +kernel
      have hl : raw24388step0Labels = raw24388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24388 raw24388Labels permutation346 hz
    mixedMoment B raw24388step0 raw24388step0Labels = mixedMoment B raw24388step1 raw24388step1Labels := by
      have hz : ∀ j, raw24388step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24388step1 = (fun i j => raw24388step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24388step1 raw24388step0; decide +kernel
      have hl : raw24388step1Labels = raw24388step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24388step0 raw24388step0Labels permutation56 hz
    mixedMoment B raw24388step1 raw24388step1Labels = mixedMoment B raw24388step2 raw24388step2Labels := by
      have ha : raw24388step2 = (fun i j => raw24388step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24388step2 raw24388step1; decide +kernel
      have hl : raw24388step2Labels = raw24388step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24388step1 raw24388step1Labels permutation23 permutation5
    mixedMoment B raw24388step2 raw24388step2Labels = mixedMoment B raw24388step3 raw24388step3Labels := by
      have ha : raw24388step3 = raw24388step2 := by apply Matrix.ext; unfold raw24388step3 raw24388step2; decide +kernel
      have hl : raw24388step2Labels = labelEmbedding1 ∘ raw24388step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24388step2 raw24388step2Labels raw24388step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical24389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24389 raw24389Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw24389 raw24389Labels = mixedMoment B raw24389step0 raw24389step0Labels := by
      have hz : ∀ j, raw24389 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24389step0 = (fun i j => raw24389 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24389step0 raw24389; decide +kernel
      have hl : raw24389step0Labels = raw24389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24389 raw24389Labels permutation346 hz
    mixedMoment B raw24389step0 raw24389step0Labels = mixedMoment B raw24389step1 raw24389step1Labels := by
      have hz : ∀ j, raw24389step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24389step1 = (fun i j => raw24389step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24389step1 raw24389step0; decide +kernel
      have hl : raw24389step1Labels = raw24389step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24389step0 raw24389step0Labels permutation56 hz
    mixedMoment B raw24389step1 raw24389step1Labels = mixedMoment B raw24389step2 raw24389step2Labels := by
      have ha : raw24389step2 = (fun i j => raw24389step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24389step2 raw24389step1; decide +kernel
      have hl : raw24389step2Labels = raw24389step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24389step1 raw24389step1Labels permutation9 permutation5
    mixedMoment B raw24389step2 raw24389step2Labels = mixedMoment B raw24389step3 raw24389step3Labels := by
      have ha : raw24389step3 = -raw24389step2 := by apply Matrix.ext; change ∀ i j, raw24389step3 i j = -(raw24389step2 i j); unfold raw24389step3 raw24389step2; decide +kernel
      have hl : raw24389step3Labels = raw24389step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24389step3 raw24389step3Labels = mixedMoment B raw24389step4 raw24389step4Labels := by
      have ha : raw24389step4 = raw24389step3 := by apply Matrix.ext; unfold raw24389step4 raw24389step3; decide +kernel
      have hl : raw24389step3Labels = labelEmbedding1 ∘ raw24389step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24389step3 raw24389step3Labels raw24389step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

theorem canonical24390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24390 raw24390Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw24390 raw24390Labels = mixedMoment B raw24390step0 raw24390step0Labels := by
      have hz : ∀ j, raw24390 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24390step0 = (fun i j => raw24390 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24390step0 raw24390; decide +kernel
      have hl : raw24390step0Labels = raw24390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24390 raw24390Labels permutation346 hz
    mixedMoment B raw24390step0 raw24390step0Labels = mixedMoment B raw24390step1 raw24390step1Labels := by
      have ha : raw24390step1 = (fun i j => raw24390step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24390step1 raw24390step0; decide +kernel
      have hl : raw24390step1Labels = raw24390step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24390step0 raw24390step0Labels permutation33 permutation5
    mixedMoment B raw24390step1 raw24390step1Labels = mixedMoment B raw24390step2 raw24390step2Labels := by
      have ha : raw24390step2 = -raw24390step1 := by apply Matrix.ext; change ∀ i j, raw24390step2 i j = -(raw24390step1 i j); unfold raw24390step2 raw24390step1; decide +kernel
      have hl : raw24390step2Labels = raw24390step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24390step2 raw24390step2Labels = mixedMoment B raw24390step3 raw24390step3Labels := by
      have ha : raw24390step3 = raw24390step2 := by apply Matrix.ext; unfold raw24390step3 raw24390step2; decide +kernel
      have hl : raw24390step2Labels = labelEmbedding1 ∘ raw24390step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24390step2 raw24390step2Labels raw24390step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

theorem canonical24391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24391 raw24391Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw24391 raw24391Labels = mixedMoment B raw24391step0 raw24391step0Labels := by
      have hz : ∀ j, raw24391 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24391step0 = (fun i j => raw24391 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24391step0 raw24391; decide +kernel
      have hl : raw24391step0Labels = raw24391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24391 raw24391Labels permutation265 hz
    mixedMoment B raw24391step0 raw24391step0Labels = mixedMoment B raw24391step1 raw24391step1Labels := by
      have ha : raw24391step1 = (fun i j => raw24391step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24391step1 raw24391step0; decide +kernel
      have hl : raw24391step1Labels = raw24391step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24391step0 raw24391step0Labels permutation33 permutation5
    mixedMoment B raw24391step1 raw24391step1Labels = mixedMoment B raw24391step2 raw24391step2Labels := by
      have ha : raw24391step2 = -raw24391step1 := by apply Matrix.ext; change ∀ i j, raw24391step2 i j = -(raw24391step1 i j); unfold raw24391step2 raw24391step1; decide +kernel
      have hl : raw24391step2Labels = raw24391step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24391step2 raw24391step2Labels = mixedMoment B raw24391step3 raw24391step3Labels := by
      have ha : raw24391step3 = raw24391step2 := by apply Matrix.ext; unfold raw24391step3 raw24391step2; decide +kernel
      have hl : raw24391step2Labels = labelEmbedding1 ∘ raw24391step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24391step2 raw24391step2Labels raw24391step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

theorem canonical24392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24392 raw24392Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw24392 raw24392Labels = mixedMoment B raw24392step0 raw24392step0Labels := by
      have hz : ∀ j, raw24392 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24392step0 = (fun i j => raw24392 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24392step0 raw24392; decide +kernel
      have hl : raw24392step0Labels = raw24392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24392 raw24392Labels permutation346 hz
    mixedMoment B raw24392step0 raw24392step0Labels = mixedMoment B raw24392step1 raw24392step1Labels := by
      have hz : ∀ j, raw24392step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24392step1 = (fun i j => raw24392step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24392step1 raw24392step0; decide +kernel
      have hl : raw24392step1Labels = raw24392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24392step0 raw24392step0Labels permutation56 hz
    mixedMoment B raw24392step1 raw24392step1Labels = mixedMoment B raw24392step2 raw24392step2Labels := by
      have ha : raw24392step2 = (fun i j => raw24392step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24392step2 raw24392step1; decide +kernel
      have hl : raw24392step2Labels = raw24392step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24392step1 raw24392step1Labels permutation9 permutation5
    mixedMoment B raw24392step2 raw24392step2Labels = mixedMoment B raw24392step3 raw24392step3Labels := by
      have ha : raw24392step3 = -raw24392step2 := by apply Matrix.ext; change ∀ i j, raw24392step3 i j = -(raw24392step2 i j); unfold raw24392step3 raw24392step2; decide +kernel
      have hl : raw24392step3Labels = raw24392step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24392step3 raw24392step3Labels = mixedMoment B raw24392step4 raw24392step4Labels := by
      have ha : raw24392step4 = raw24392step3 := by apply Matrix.ext; unfold raw24392step4 raw24392step3; decide +kernel
      have hl : raw24392step3Labels = labelEmbedding1 ∘ raw24392step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24392step3 raw24392step3Labels raw24392step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical24393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24393 raw24393Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw24393 raw24393Labels = mixedMoment B raw24393step0 raw24393step0Labels := by
      have hz : ∀ j, raw24393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24393step0 = (fun i j => raw24393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24393step0 raw24393; decide +kernel
      have hl : raw24393step0Labels = raw24393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24393 raw24393Labels permutation346 hz
    mixedMoment B raw24393step0 raw24393step0Labels = mixedMoment B raw24393step1 raw24393step1Labels := by
      have hz : ∀ j, raw24393step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24393step1 = (fun i j => raw24393step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24393step1 raw24393step0; decide +kernel
      have hl : raw24393step1Labels = raw24393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24393step0 raw24393step0Labels permutation56 hz
    mixedMoment B raw24393step1 raw24393step1Labels = mixedMoment B raw24393step2 raw24393step2Labels := by
      have ha : raw24393step2 = (fun i j => raw24393step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24393step2 raw24393step1; decide +kernel
      have hl : raw24393step2Labels = raw24393step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24393step1 raw24393step1Labels permutation10 permutation7
    mixedMoment B raw24393step2 raw24393step2Labels = mixedMoment B raw24393step3 raw24393step3Labels := by
      have ha : raw24393step3 = -raw24393step2 := by apply Matrix.ext; change ∀ i j, raw24393step3 i j = -(raw24393step2 i j); unfold raw24393step3 raw24393step2; decide +kernel
      have hl : raw24393step3Labels = raw24393step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24393step3 raw24393step3Labels = mixedMoment B raw24393step4 raw24393step4Labels := by
      have ha : raw24393step4 = raw24393step3 := by apply Matrix.ext; unfold raw24393step4 raw24393step3; decide +kernel
      have hl : raw24393step3Labels = labelEmbedding1 ∘ raw24393step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24393step3 raw24393step3Labels raw24393step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical24394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24394 raw24394Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw24394 raw24394Labels = mixedMoment B raw24394step0 raw24394step0Labels := by
      have hz : ∀ j, raw24394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24394step0 = (fun i j => raw24394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24394step0 raw24394; decide +kernel
      have hl : raw24394step0Labels = raw24394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24394 raw24394Labels permutation346 hz
    mixedMoment B raw24394step0 raw24394step0Labels = mixedMoment B raw24394step1 raw24394step1Labels := by
      have hz : ∀ j, raw24394step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24394step1 = (fun i j => raw24394step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24394step1 raw24394step0; decide +kernel
      have hl : raw24394step1Labels = raw24394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24394step0 raw24394step0Labels permutation56 hz
    mixedMoment B raw24394step1 raw24394step1Labels = mixedMoment B raw24394step2 raw24394step2Labels := by
      have ha : raw24394step2 = (fun i j => raw24394step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24394step2 raw24394step1; decide +kernel
      have hl : raw24394step2Labels = raw24394step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24394step1 raw24394step1Labels permutation10 permutation2
    _ = mixedMoment B node1294 node1294Labels := by rfl

theorem canonical24395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24395 raw24395Labels = mixedMoment B node638 node638Labels := by
  calc
    mixedMoment B raw24395 raw24395Labels = mixedMoment B raw24395step0 raw24395step0Labels := by
      have hz : ∀ j, raw24395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24395step0 = (fun i j => raw24395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24395step0 raw24395; decide +kernel
      have hl : raw24395step0Labels = raw24395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24395 raw24395Labels permutation346 hz
    mixedMoment B raw24395step0 raw24395step0Labels = mixedMoment B raw24395step1 raw24395step1Labels := by
      have ha : raw24395step1 = (fun i j => raw24395step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24395step1 raw24395step0; decide +kernel
      have hl : raw24395step1Labels = raw24395step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24395step0 raw24395step0Labels permutation44 permutation2
    _ = mixedMoment B node638 node638Labels := by rfl

theorem canonical24396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24396 raw24396Labels = mixedMoment B node638 node638Labels := by
  calc
    mixedMoment B raw24396 raw24396Labels = mixedMoment B raw24396step0 raw24396step0Labels := by
      have hz : ∀ j, raw24396 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24396step0 = (fun i j => raw24396 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24396step0 raw24396; decide +kernel
      have hl : raw24396step0Labels = raw24396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24396 raw24396Labels permutation265 hz
    mixedMoment B raw24396step0 raw24396step0Labels = mixedMoment B raw24396step1 raw24396step1Labels := by
      have ha : raw24396step1 = (fun i j => raw24396step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24396step1 raw24396step0; decide +kernel
      have hl : raw24396step1Labels = raw24396step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24396step0 raw24396step0Labels permutation44 permutation2
    _ = mixedMoment B node638 node638Labels := by rfl

theorem canonical24397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24397 raw24397Labels = mixedMoment B node642 node642Labels := by
  calc
    mixedMoment B raw24397 raw24397Labels = mixedMoment B raw24397step0 raw24397step0Labels := by
      have hz : ∀ j, raw24397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24397step0 = (fun i j => raw24397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24397step0 raw24397; decide +kernel
      have hl : raw24397step0Labels = raw24397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24397 raw24397Labels permutation346 hz
    mixedMoment B raw24397step0 raw24397step0Labels = mixedMoment B raw24397step1 raw24397step1Labels := by
      have hz : ∀ j, raw24397step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24397step1 = (fun i j => raw24397step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24397step1 raw24397step0; decide +kernel
      have hl : raw24397step1Labels = raw24397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24397step0 raw24397step0Labels permutation56 hz
    mixedMoment B raw24397step1 raw24397step1Labels = mixedMoment B raw24397step2 raw24397step2Labels := by
      have ha : raw24397step2 = (fun i j => raw24397step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24397step2 raw24397step1; decide +kernel
      have hl : raw24397step2Labels = raw24397step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24397step1 raw24397step1Labels permutation10 permutation2
    _ = mixedMoment B node642 node642Labels := by rfl

theorem canonical24398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24398 raw24398Labels = mixedMoment B node653 node653Labels := by
  calc
    mixedMoment B raw24398 raw24398Labels = mixedMoment B raw24398step0 raw24398step0Labels := by
      have hz : ∀ j, raw24398 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24398step0 = (fun i j => raw24398 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24398step0 raw24398; decide +kernel
      have hl : raw24398step0Labels = raw24398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24398 raw24398Labels permutation346 hz
    mixedMoment B raw24398step0 raw24398step0Labels = mixedMoment B raw24398step1 raw24398step1Labels := by
      have hz : ∀ j, raw24398step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24398step1 = (fun i j => raw24398step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24398step1 raw24398step0; decide +kernel
      have hl : raw24398step1Labels = raw24398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24398step0 raw24398step0Labels permutation56 hz
    _ = mixedMoment B node653 node653Labels := by rfl

theorem canonical24399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24399 raw24399Labels = mixedMoment B node641 node641Labels := by
  calc
    mixedMoment B raw24399 raw24399Labels = mixedMoment B raw24399step0 raw24399step0Labels := by
      have hz : ∀ j, raw24399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24399step0 = (fun i j => raw24399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24399step0 raw24399; decide +kernel
      have hl : raw24399step0Labels = raw24399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24399 raw24399Labels permutation346 hz
    mixedMoment B raw24399step0 raw24399step0Labels = mixedMoment B raw24399step1 raw24399step1Labels := by
      have hz : ∀ j, raw24399step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24399step1 = (fun i j => raw24399step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24399step1 raw24399step0; decide +kernel
      have hl : raw24399step1Labels = raw24399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24399step0 raw24399step0Labels permutation56 hz
    mixedMoment B raw24399step1 raw24399step1Labels = mixedMoment B raw24399step2 raw24399step2Labels := by
      have ha : raw24399step2 = (fun i j => raw24399step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24399step2 raw24399step1; decide +kernel
      have hl : raw24399step2Labels = raw24399step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24399step1 raw24399step1Labels permutation10 permutation2
    _ = mixedMoment B node641 node641Labels := by rfl

theorem canonical24400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24400 raw24400Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw24400 raw24400Labels = mixedMoment B raw24400step0 raw24400step0Labels := by
      have hz : ∀ j, raw24400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24400step0 = (fun i j => raw24400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24400step0 raw24400; decide +kernel
      have hl : raw24400step0Labels = raw24400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24400 raw24400Labels permutation346 hz
    mixedMoment B raw24400step0 raw24400step0Labels = mixedMoment B raw24400step1 raw24400step1Labels := by
      have hz : ∀ j, raw24400step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24400step1 = (fun i j => raw24400step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24400step1 raw24400step0; decide +kernel
      have hl : raw24400step1Labels = raw24400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24400step0 raw24400step0Labels permutation56 hz
    mixedMoment B raw24400step1 raw24400step1Labels = mixedMoment B raw24400step2 raw24400step2Labels := by
      have ha : raw24400step2 = (fun i j => raw24400step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24400step2 raw24400step1; decide +kernel
      have hl : raw24400step2Labels = raw24400step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24400step1 raw24400step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

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

theorem canonical24451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24451 raw24451Labels = mixedMoment B node1287 node1287Labels := by
  calc
    mixedMoment B raw24451 raw24451Labels = mixedMoment B raw24451step0 raw24451step0Labels := by
      have hz : ∀ j, raw24451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24451step0 = (fun i j => raw24451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24451step0 raw24451; decide +kernel
      have hl : raw24451step0Labels = raw24451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24451 raw24451Labels permutation346 hz
    mixedMoment B raw24451step0 raw24451step0Labels = mixedMoment B raw24451step1 raw24451step1Labels := by
      have hz : ∀ j, raw24451step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24451step1 = (fun i j => raw24451step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24451step1 raw24451step0; decide +kernel
      have hl : raw24451step1Labels = raw24451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24451step0 raw24451step0Labels permutation56 hz
    mixedMoment B raw24451step1 raw24451step1Labels = mixedMoment B raw24451step2 raw24451step2Labels := by
      have ha : raw24451step2 = (fun i j => raw24451step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24451step2 raw24451step1; decide +kernel
      have hl : raw24451step2Labels = raw24451step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24451step1 raw24451step1Labels permutation10 permutation2
    _ = mixedMoment B node1287 node1287Labels := by rfl

theorem canonical24452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24452 raw24452Labels = mixedMoment B node2584 node2584Labels := by
  calc
    mixedMoment B raw24452 raw24452Labels = mixedMoment B raw24452step0 raw24452step0Labels := by
      have hz : ∀ j, raw24452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24452step0 = (fun i j => raw24452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24452step0 raw24452; decide +kernel
      have hl : raw24452step0Labels = raw24452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24452 raw24452Labels permutation346 hz
    mixedMoment B raw24452step0 raw24452step0Labels = mixedMoment B raw24452step1 raw24452step1Labels := by
      have ha : raw24452step1 = (fun i j => raw24452step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24452step1 raw24452step0; decide +kernel
      have hl : raw24452step1Labels = raw24452step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24452step0 raw24452step0Labels permutation34 permutation2
    _ = mixedMoment B node2584 node2584Labels := by rfl

theorem canonical24453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24453 raw24453Labels = mixedMoment B node2584 node2584Labels := by
  calc
    mixedMoment B raw24453 raw24453Labels = mixedMoment B raw24453step0 raw24453step0Labels := by
      have hz : ∀ j, raw24453 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24453step0 = (fun i j => raw24453 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24453step0 raw24453; decide +kernel
      have hl : raw24453step0Labels = raw24453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24453 raw24453Labels permutation265 hz
    mixedMoment B raw24453step0 raw24453step0Labels = mixedMoment B raw24453step1 raw24453step1Labels := by
      have ha : raw24453step1 = (fun i j => raw24453step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24453step1 raw24453step0; decide +kernel
      have hl : raw24453step1Labels = raw24453step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24453step0 raw24453step0Labels permutation34 permutation2
    _ = mixedMoment B node2584 node2584Labels := by rfl

theorem canonical24454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24454 raw24454Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw24454 raw24454Labels = mixedMoment B raw24454step0 raw24454step0Labels := by
      have hz : ∀ j, raw24454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24454step0 = (fun i j => raw24454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24454step0 raw24454; decide +kernel
      have hl : raw24454step0Labels = raw24454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24454 raw24454Labels permutation346 hz
    mixedMoment B raw24454step0 raw24454step0Labels = mixedMoment B raw24454step1 raw24454step1Labels := by
      have hz : ∀ j, raw24454step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24454step1 = (fun i j => raw24454step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24454step1 raw24454step0; decide +kernel
      have hl : raw24454step1Labels = raw24454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24454step0 raw24454step0Labels permutation56 hz
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical24455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24455 raw24455Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw24455 raw24455Labels = mixedMoment B raw24455step0 raw24455step0Labels := by
      have hz : ∀ j, raw24455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24455step0 = (fun i j => raw24455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24455step0 raw24455; decide +kernel
      have hl : raw24455step0Labels = raw24455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24455 raw24455Labels permutation346 hz
    mixedMoment B raw24455step0 raw24455step0Labels = mixedMoment B raw24455step1 raw24455step1Labels := by
      have hz : ∀ j, raw24455step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24455step1 = (fun i j => raw24455step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24455step1 raw24455step0; decide +kernel
      have hl : raw24455step1Labels = raw24455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24455step0 raw24455step0Labels permutation56 hz
    mixedMoment B raw24455step1 raw24455step1Labels = mixedMoment B raw24455step2 raw24455step2Labels := by
      have ha : raw24455step2 = (fun i j => raw24455step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24455step2 raw24455step1; decide +kernel
      have hl : raw24455step2Labels = raw24455step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24455step1 raw24455step1Labels permutation10 permutation2
    _ = mixedMoment B node2685 node2685Labels := by rfl

theorem canonical24456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24456 raw24456Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw24456 raw24456Labels = mixedMoment B raw24456step0 raw24456step0Labels := by
      have hz : ∀ j, raw24456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24456step0 = (fun i j => raw24456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24456step0 raw24456; decide +kernel
      have hl : raw24456step0Labels = raw24456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24456 raw24456Labels permutation346 hz
    mixedMoment B raw24456step0 raw24456step0Labels = mixedMoment B raw24456step1 raw24456step1Labels := by
      have hz : ∀ j, raw24456step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24456step1 = (fun i j => raw24456step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24456step1 raw24456step0; decide +kernel
      have hl : raw24456step1Labels = raw24456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24456step0 raw24456step0Labels permutation56 hz
    mixedMoment B raw24456step1 raw24456step1Labels = mixedMoment B raw24456step2 raw24456step2Labels := by
      have ha : raw24456step2 = (fun i j => raw24456step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24456step2 raw24456step1; decide +kernel
      have hl : raw24456step2Labels = raw24456step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24456step1 raw24456step1Labels permutation22 permutation4
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical24457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24457 raw24457Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw24457 raw24457Labels = mixedMoment B raw24457step0 raw24457step0Labels := by
      have hz : ∀ j, raw24457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24457step0 = (fun i j => raw24457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24457step0 raw24457; decide +kernel
      have hl : raw24457step0Labels = raw24457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24457 raw24457Labels permutation346 hz
    mixedMoment B raw24457step0 raw24457step0Labels = mixedMoment B raw24457step1 raw24457step1Labels := by
      have hz : ∀ j, raw24457step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24457step1 = (fun i j => raw24457step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24457step1 raw24457step0; decide +kernel
      have hl : raw24457step1Labels = raw24457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24457step0 raw24457step0Labels permutation56 hz
    mixedMoment B raw24457step1 raw24457step1Labels = mixedMoment B raw24457step2 raw24457step2Labels := by
      have ha : raw24457step2 = (fun i j => raw24457step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24457step2 raw24457step1; decide +kernel
      have hl : raw24457step2Labels = raw24457step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24457step1 raw24457step1Labels permutation28 permutation0
    mixedMoment B raw24457step2 raw24457step2Labels = mixedMoment B raw24457step3 raw24457step3Labels := by
      have ha : raw24457step3 = -raw24457step2 := by apply Matrix.ext; change ∀ i j, raw24457step3 i j = -(raw24457step2 i j); unfold raw24457step3 raw24457step2; decide +kernel
      have hl : raw24457step3Labels = raw24457step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical24458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24458 raw24458Labels = mixedMoment B node1230 node1230Labels := by
  calc
    mixedMoment B raw24458 raw24458Labels = mixedMoment B raw24458step0 raw24458step0Labels := by
      have hz : ∀ j, raw24458 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24458step0 = (fun i j => raw24458 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24458step0 raw24458; decide +kernel
      have hl : raw24458step0Labels = raw24458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24458 raw24458Labels permutation265 hz
    mixedMoment B raw24458step0 raw24458step0Labels = mixedMoment B raw24458step1 raw24458step1Labels := by
      have ha : raw24458step1 = (fun i j => raw24458step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24458step1 raw24458step0; decide +kernel
      have hl : raw24458step1Labels = raw24458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24458step0 raw24458step0Labels permutation34 permutation2
    _ = mixedMoment B node1230 node1230Labels := by rfl

theorem canonical24459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24459 raw24459Labels = mixedMoment B node2551 node2551Labels := by
  calc
    mixedMoment B raw24459 raw24459Labels = mixedMoment B raw24459step0 raw24459step0Labels := by
      have ha : raw24459step0 = (fun i j => raw24459 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24459step0 raw24459; decide +kernel
      have hl : raw24459step0Labels = raw24459Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24459 raw24459Labels permutation154 permutation2
    _ = mixedMoment B node2551 node2551Labels := by rfl

theorem canonical24460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24460 raw24460Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw24460 raw24460Labels = mixedMoment B raw24460step0 raw24460step0Labels := by
      have hz : ∀ j, raw24460 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24460step0 = (fun i j => raw24460 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24460step0 raw24460; decide +kernel
      have hl : raw24460step0Labels = raw24460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24460 raw24460Labels permutation265 hz
    mixedMoment B raw24460step0 raw24460step0Labels = mixedMoment B raw24460step1 raw24460step1Labels := by
      have ha : raw24460step1 = (fun i j => raw24460step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24460step1 raw24460step0; decide +kernel
      have hl : raw24460step1Labels = raw24460step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24460step0 raw24460step0Labels permutation34 permutation2
    _ = mixedMoment B node2505 node2505Labels := by rfl

theorem canonical24461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24461 raw24461Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw24461 raw24461Labels = mixedMoment B raw24461step0 raw24461step0Labels := by
      have hz : ∀ j, raw24461 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24461step0 = (fun i j => raw24461 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24461step0 raw24461; decide +kernel
      have hl : raw24461step0Labels = raw24461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24461 raw24461Labels permutation265 hz
    _ = mixedMoment B node2729 node2729Labels := by rfl

theorem canonical24462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24462 raw24462Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw24462 raw24462Labels = mixedMoment B raw24462step0 raw24462step0Labels := by
      have hz : ∀ j, raw24462 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24462step0 = (fun i j => raw24462 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24462step0 raw24462; decide +kernel
      have hl : raw24462step0Labels = raw24462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24462 raw24462Labels permutation265 hz
    mixedMoment B raw24462step0 raw24462step0Labels = mixedMoment B raw24462step1 raw24462step1Labels := by
      have ha : raw24462step1 = (fun i j => raw24462step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24462step1 raw24462step0; decide +kernel
      have hl : raw24462step1Labels = raw24462step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24462step0 raw24462step0Labels permutation34 permutation2
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical24463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24463 raw24463Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw24463 raw24463Labels = mixedMoment B raw24463step0 raw24463step0Labels := by
      have hz : ∀ j, raw24463 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24463step0 = (fun i j => raw24463 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24463step0 raw24463; decide +kernel
      have hl : raw24463step0Labels = raw24463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24463 raw24463Labels permutation265 hz
    mixedMoment B raw24463step0 raw24463step0Labels = mixedMoment B raw24463step1 raw24463step1Labels := by
      have ha : raw24463step1 = (fun i j => raw24463step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24463step1 raw24463step0; decide +kernel
      have hl : raw24463step1Labels = raw24463step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24463step0 raw24463step0Labels permutation34 permutation2
    _ = mixedMoment B node2736 node2736Labels := by rfl

theorem canonical24464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24464 raw24464Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw24464 raw24464Labels = mixedMoment B raw24464step0 raw24464step0Labels := by
      have hz : ∀ j, raw24464 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24464step0 = (fun i j => raw24464 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24464step0 raw24464; decide +kernel
      have hl : raw24464step0Labels = raw24464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24464 raw24464Labels permutation265 hz
    mixedMoment B raw24464step0 raw24464step0Labels = mixedMoment B raw24464step1 raw24464step1Labels := by
      have ha : raw24464step1 = (fun i j => raw24464step0 (permutation101 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24464step1 raw24464step0; decide +kernel
      have hl : raw24464step1Labels = raw24464step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24464step0 raw24464step0Labels permutation101 permutation0
    mixedMoment B raw24464step1 raw24464step1Labels = mixedMoment B raw24464step2 raw24464step2Labels := by
      have ha : raw24464step2 = -raw24464step1 := by apply Matrix.ext; change ∀ i j, raw24464step2 i j = -(raw24464step1 i j); unfold raw24464step2 raw24464step1; decide +kernel
      have hl : raw24464step2Labels = raw24464step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical24516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24516 raw24516Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw24516 raw24516Labels = mixedMoment B raw24516step0 raw24516step0Labels := by
      have ha : raw24516step0 = (fun i j => raw24516 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24516step0 raw24516; decide +kernel
      have hl : raw24516step0Labels = raw24516Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24516 raw24516Labels permutation176 permutation7
    mixedMoment B raw24516step0 raw24516step0Labels = mixedMoment B raw24516step1 raw24516step1Labels := by
      have ha : raw24516step1 = -raw24516step0 := by apply Matrix.ext; change ∀ i j, raw24516step1 i j = -(raw24516step0 i j); unfold raw24516step1 raw24516step0; decide +kernel
      have hl : raw24516step1Labels = raw24516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24516step1 raw24516step1Labels = mixedMoment B raw24516step2 raw24516step2Labels := by
      have ha : raw24516step2 = raw24516step1 := by apply Matrix.ext; unfold raw24516step2 raw24516step1; decide +kernel
      have hl : raw24516step1Labels = labelEmbedding1 ∘ raw24516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24516step1 raw24516step1Labels raw24516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

theorem canonical24517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24517 raw24517Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw24517 raw24517Labels = mixedMoment B raw24517step0 raw24517step0Labels := by
      have hz : ∀ j, raw24517 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24517step0 = (fun i j => raw24517 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24517step0 raw24517; decide +kernel
      have hl : raw24517step0Labels = raw24517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24517 raw24517Labels permutation265 hz
    mixedMoment B raw24517step0 raw24517step0Labels = mixedMoment B raw24517step1 raw24517step1Labels := by
      have ha : raw24517step1 = (fun i j => raw24517step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24517step1 raw24517step0; decide +kernel
      have hl : raw24517step1Labels = raw24517step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24517step0 raw24517step0Labels permutation32 permutation7
    mixedMoment B raw24517step1 raw24517step1Labels = mixedMoment B raw24517step2 raw24517step2Labels := by
      have ha : raw24517step2 = -raw24517step1 := by apply Matrix.ext; change ∀ i j, raw24517step2 i j = -(raw24517step1 i j); unfold raw24517step2 raw24517step1; decide +kernel
      have hl : raw24517step2Labels = raw24517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24517step2 raw24517step2Labels = mixedMoment B raw24517step3 raw24517step3Labels := by
      have ha : raw24517step3 = raw24517step2 := by apply Matrix.ext; unfold raw24517step3 raw24517step2; decide +kernel
      have hl : raw24517step2Labels = labelEmbedding1 ∘ raw24517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24517step2 raw24517step2Labels raw24517step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

theorem canonical24518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24518 raw24518Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw24518 raw24518Labels = mixedMoment B raw24518step0 raw24518step0Labels := by
      have hz : ∀ j, raw24518 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24518step0 = (fun i j => raw24518 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24518step0 raw24518; decide +kernel
      have hl : raw24518step0Labels = raw24518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24518 raw24518Labels permutation265 hz
    mixedMoment B raw24518step0 raw24518step0Labels = mixedMoment B raw24518step1 raw24518step1Labels := by
      have ha : raw24518step1 = (fun i j => raw24518step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24518step1 raw24518step0; decide +kernel
      have hl : raw24518step1Labels = raw24518step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24518step0 raw24518step0Labels permutation32 permutation7
    mixedMoment B raw24518step1 raw24518step1Labels = mixedMoment B raw24518step2 raw24518step2Labels := by
      have ha : raw24518step2 = -raw24518step1 := by apply Matrix.ext; change ∀ i j, raw24518step2 i j = -(raw24518step1 i j); unfold raw24518step2 raw24518step1; decide +kernel
      have hl : raw24518step2Labels = raw24518step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24518step2 raw24518step2Labels = mixedMoment B raw24518step3 raw24518step3Labels := by
      have ha : raw24518step3 = raw24518step2 := by apply Matrix.ext; unfold raw24518step3 raw24518step2; decide +kernel
      have hl : raw24518step2Labels = labelEmbedding1 ∘ raw24518step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24518step2 raw24518step2Labels raw24518step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical24519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24519 raw24519Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw24519 raw24519Labels = mixedMoment B raw24519step0 raw24519step0Labels := by
      have hz : ∀ j, raw24519 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24519step0 = (fun i j => raw24519 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24519step0 raw24519; decide +kernel
      have hl : raw24519step0Labels = raw24519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24519 raw24519Labels permutation265 hz
    mixedMoment B raw24519step0 raw24519step0Labels = mixedMoment B raw24519step1 raw24519step1Labels := by
      have ha : raw24519step1 = (fun i j => raw24519step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24519step1 raw24519step0; decide +kernel
      have hl : raw24519step1Labels = raw24519step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24519step0 raw24519step0Labels permutation34 permutation7
    mixedMoment B raw24519step1 raw24519step1Labels = mixedMoment B raw24519step2 raw24519step2Labels := by
      have ha : raw24519step2 = -raw24519step1 := by apply Matrix.ext; change ∀ i j, raw24519step2 i j = -(raw24519step1 i j); unfold raw24519step2 raw24519step1; decide +kernel
      have hl : raw24519step2Labels = raw24519step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24519step2 raw24519step2Labels = mixedMoment B raw24519step3 raw24519step3Labels := by
      have ha : raw24519step3 = raw24519step2 := by apply Matrix.ext; unfold raw24519step3 raw24519step2; decide +kernel
      have hl : raw24519step2Labels = labelEmbedding1 ∘ raw24519step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24519step2 raw24519step2Labels raw24519step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical24520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24520 raw24520Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw24520 raw24520Labels = mixedMoment B raw24520step0 raw24520step0Labels := by
      have hz : ∀ j, raw24520 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24520step0 = (fun i j => raw24520 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24520step0 raw24520; decide +kernel
      have hl : raw24520step0Labels = raw24520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24520 raw24520Labels permutation265 hz
    mixedMoment B raw24520step0 raw24520step0Labels = mixedMoment B raw24520step1 raw24520step1Labels := by
      have ha : raw24520step1 = (fun i j => raw24520step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24520step1 raw24520step0; decide +kernel
      have hl : raw24520step1Labels = raw24520step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24520step0 raw24520step0Labels permutation32 permutation7
    mixedMoment B raw24520step1 raw24520step1Labels = mixedMoment B raw24520step2 raw24520step2Labels := by
      have ha : raw24520step2 = -raw24520step1 := by apply Matrix.ext; change ∀ i j, raw24520step2 i j = -(raw24520step1 i j); unfold raw24520step2 raw24520step1; decide +kernel
      have hl : raw24520step2Labels = raw24520step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24520step2 raw24520step2Labels = mixedMoment B raw24520step3 raw24520step3Labels := by
      have ha : raw24520step3 = raw24520step2 := by apply Matrix.ext; unfold raw24520step3 raw24520step2; decide +kernel
      have hl : raw24520step2Labels = labelEmbedding1 ∘ raw24520step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24520step2 raw24520step2Labels raw24520step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

theorem canonical24521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24521 raw24521Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw24521 raw24521Labels = mixedMoment B raw24521step0 raw24521step0Labels := by
      have ha : raw24521step0 = (fun i j => raw24521 (permutation214 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24521step0 raw24521; decide +kernel
      have hl : raw24521step0Labels = raw24521Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24521 raw24521Labels permutation214 permutation5
    mixedMoment B raw24521step0 raw24521step0Labels = mixedMoment B raw24521step1 raw24521step1Labels := by
      have ha : raw24521step1 = -raw24521step0 := by apply Matrix.ext; change ∀ i j, raw24521step1 i j = -(raw24521step0 i j); unfold raw24521step1 raw24521step0; decide +kernel
      have hl : raw24521step1Labels = raw24521step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24521step1 raw24521step1Labels = mixedMoment B raw24521step2 raw24521step2Labels := by
      have ha : raw24521step2 = raw24521step1 := by apply Matrix.ext; unfold raw24521step2 raw24521step1; decide +kernel
      have hl : raw24521step1Labels = labelEmbedding1 ∘ raw24521step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24521step1 raw24521step1Labels raw24521step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

theorem canonical24522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24522 raw24522Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw24522 raw24522Labels = mixedMoment B raw24522step0 raw24522step0Labels := by
      have ha : raw24522step0 = (fun i j => raw24522 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24522step0 raw24522; decide +kernel
      have hl : raw24522step0Labels = raw24522Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24522 raw24522Labels permutation176 permutation7
    mixedMoment B raw24522step0 raw24522step0Labels = mixedMoment B raw24522step1 raw24522step1Labels := by
      have ha : raw24522step1 = -raw24522step0 := by apply Matrix.ext; change ∀ i j, raw24522step1 i j = -(raw24522step0 i j); unfold raw24522step1 raw24522step0; decide +kernel
      have hl : raw24522step1Labels = raw24522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24522step1 raw24522step1Labels = mixedMoment B raw24522step2 raw24522step2Labels := by
      have ha : raw24522step2 = raw24522step1 := by apply Matrix.ext; unfold raw24522step2 raw24522step1; decide +kernel
      have hl : raw24522step1Labels = labelEmbedding1 ∘ raw24522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24522step1 raw24522step1Labels raw24522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

theorem canonical24523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24523 raw24523Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw24523 raw24523Labels = mixedMoment B raw24523step0 raw24523step0Labels := by
      have ha : raw24523step0 = (fun i j => raw24523 (permutation214 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24523step0 raw24523; decide +kernel
      have hl : raw24523step0Labels = raw24523Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24523 raw24523Labels permutation214 permutation5
    mixedMoment B raw24523step0 raw24523step0Labels = mixedMoment B raw24523step1 raw24523step1Labels := by
      have ha : raw24523step1 = -raw24523step0 := by apply Matrix.ext; change ∀ i j, raw24523step1 i j = -(raw24523step0 i j); unfold raw24523step1 raw24523step0; decide +kernel
      have hl : raw24523step1Labels = raw24523step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24523step1 raw24523step1Labels = mixedMoment B raw24523step2 raw24523step2Labels := by
      have ha : raw24523step2 = raw24523step1 := by apply Matrix.ext; unfold raw24523step2 raw24523step1; decide +kernel
      have hl : raw24523step1Labels = labelEmbedding1 ∘ raw24523step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24523step1 raw24523step1Labels raw24523step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical24524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24524 raw24524Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw24524 raw24524Labels = mixedMoment B raw24524step0 raw24524step0Labels := by
      have ha : raw24524step0 = (fun i j => raw24524 (permutation236 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24524step0 raw24524; decide +kernel
      have hl : raw24524step0Labels = raw24524Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24524 raw24524Labels permutation236 permutation5
    mixedMoment B raw24524step0 raw24524step0Labels = mixedMoment B raw24524step1 raw24524step1Labels := by
      have ha : raw24524step1 = -raw24524step0 := by apply Matrix.ext; change ∀ i j, raw24524step1 i j = -(raw24524step0 i j); unfold raw24524step1 raw24524step0; decide +kernel
      have hl : raw24524step1Labels = raw24524step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24524step1 raw24524step1Labels = mixedMoment B raw24524step2 raw24524step2Labels := by
      have ha : raw24524step2 = raw24524step1 := by apply Matrix.ext; unfold raw24524step2 raw24524step1; decide +kernel
      have hl : raw24524step1Labels = labelEmbedding1 ∘ raw24524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24524step1 raw24524step1Labels raw24524step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical24525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24525 raw24525Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw24525 raw24525Labels = mixedMoment B raw24525step0 raw24525step0Labels := by
      have ha : raw24525step0 = (fun i j => raw24525 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24525step0 raw24525; decide +kernel
      have hl : raw24525step0Labels = raw24525Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24525 raw24525Labels permutation176 permutation7
    mixedMoment B raw24525step0 raw24525step0Labels = mixedMoment B raw24525step1 raw24525step1Labels := by
      have ha : raw24525step1 = -raw24525step0 := by apply Matrix.ext; change ∀ i j, raw24525step1 i j = -(raw24525step0 i j); unfold raw24525step1 raw24525step0; decide +kernel
      have hl : raw24525step1Labels = raw24525step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24525step1 raw24525step1Labels = mixedMoment B raw24525step2 raw24525step2Labels := by
      have ha : raw24525step2 = raw24525step1 := by apply Matrix.ext; unfold raw24525step2 raw24525step1; decide +kernel
      have hl : raw24525step1Labels = labelEmbedding1 ∘ raw24525step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24525step1 raw24525step1Labels raw24525step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

theorem canonical24526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24526 raw24526Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw24526 raw24526Labels = mixedMoment B raw24526step0 raw24526step0Labels := by
      have hz : ∀ j, raw24526 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24526step0 = (fun i j => raw24526 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24526step0 raw24526; decide +kernel
      have hl : raw24526step0Labels = raw24526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24526 raw24526Labels permutation265 hz
    mixedMoment B raw24526step0 raw24526step0Labels = mixedMoment B raw24526step1 raw24526step1Labels := by
      have ha : raw24526step1 = (fun i j => raw24526step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24526step1 raw24526step0; decide +kernel
      have hl : raw24526step1Labels = raw24526step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24526step0 raw24526step0Labels permutation41 permutation5
    mixedMoment B raw24526step1 raw24526step1Labels = mixedMoment B raw24526step2 raw24526step2Labels := by
      have ha : raw24526step2 = -raw24526step1 := by apply Matrix.ext; change ∀ i j, raw24526step2 i j = -(raw24526step1 i j); unfold raw24526step2 raw24526step1; decide +kernel
      have hl : raw24526step2Labels = raw24526step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24526step2 raw24526step2Labels = mixedMoment B raw24526step3 raw24526step3Labels := by
      have ha : raw24526step3 = raw24526step2 := by apply Matrix.ext; unfold raw24526step3 raw24526step2; decide +kernel
      have hl : raw24526step2Labels = labelEmbedding1 ∘ raw24526step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24526step2 raw24526step2Labels raw24526step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

theorem canonical24527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24527 raw24527Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw24527 raw24527Labels = mixedMoment B raw24527step0 raw24527step0Labels := by
      have ha : raw24527step0 = (fun i j => raw24527 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24527step0 raw24527; decide +kernel
      have hl : raw24527step0Labels = raw24527Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24527 raw24527Labels permutation161 permutation5
    mixedMoment B raw24527step0 raw24527step0Labels = mixedMoment B raw24527step1 raw24527step1Labels := by
      have ha : raw24527step1 = -raw24527step0 := by apply Matrix.ext; change ∀ i j, raw24527step1 i j = -(raw24527step0 i j); unfold raw24527step1 raw24527step0; decide +kernel
      have hl : raw24527step1Labels = raw24527step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24527step1 raw24527step1Labels = mixedMoment B raw24527step2 raw24527step2Labels := by
      have ha : raw24527step2 = raw24527step1 := by apply Matrix.ext; unfold raw24527step2 raw24527step1; decide +kernel
      have hl : raw24527step1Labels = labelEmbedding1 ∘ raw24527step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24527step1 raw24527step1Labels raw24527step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

theorem canonical24528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24528 raw24528Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw24528 raw24528Labels = mixedMoment B raw24528step0 raw24528step0Labels := by
      have hz : ∀ j, raw24528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24528step0 = (fun i j => raw24528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24528step0 raw24528; decide +kernel
      have hl : raw24528step0Labels = raw24528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24528 raw24528Labels permutation265 hz
    mixedMoment B raw24528step0 raw24528step0Labels = mixedMoment B raw24528step1 raw24528step1Labels := by
      have ha : raw24528step1 = (fun i j => raw24528step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24528step1 raw24528step0; decide +kernel
      have hl : raw24528step1Labels = raw24528step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24528step0 raw24528step0Labels permutation41 permutation5
    mixedMoment B raw24528step1 raw24528step1Labels = mixedMoment B raw24528step2 raw24528step2Labels := by
      have ha : raw24528step2 = -raw24528step1 := by apply Matrix.ext; change ∀ i j, raw24528step2 i j = -(raw24528step1 i j); unfold raw24528step2 raw24528step1; decide +kernel
      have hl : raw24528step2Labels = raw24528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24528step2 raw24528step2Labels = mixedMoment B raw24528step3 raw24528step3Labels := by
      have ha : raw24528step3 = raw24528step2 := by apply Matrix.ext; unfold raw24528step3 raw24528step2; decide +kernel
      have hl : raw24528step2Labels = labelEmbedding1 ∘ raw24528step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24528step2 raw24528step2Labels raw24528step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical24529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24529 raw24529Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw24529 raw24529Labels = mixedMoment B raw24529step0 raw24529step0Labels := by
      have hz : ∀ j, raw24529 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24529step0 = (fun i j => raw24529 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24529step0 raw24529; decide +kernel
      have hl : raw24529step0Labels = raw24529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24529 raw24529Labels permutation265 hz
    mixedMoment B raw24529step0 raw24529step0Labels = mixedMoment B raw24529step1 raw24529step1Labels := by
      have ha : raw24529step1 = (fun i j => raw24529step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24529step1 raw24529step0; decide +kernel
      have hl : raw24529step1Labels = raw24529step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24529step0 raw24529step0Labels permutation47 permutation5
    mixedMoment B raw24529step1 raw24529step1Labels = mixedMoment B raw24529step2 raw24529step2Labels := by
      have ha : raw24529step2 = -raw24529step1 := by apply Matrix.ext; change ∀ i j, raw24529step2 i j = -(raw24529step1 i j); unfold raw24529step2 raw24529step1; decide +kernel
      have hl : raw24529step2Labels = raw24529step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24529step2 raw24529step2Labels = mixedMoment B raw24529step3 raw24529step3Labels := by
      have ha : raw24529step3 = raw24529step2 := by apply Matrix.ext; unfold raw24529step3 raw24529step2; decide +kernel
      have hl : raw24529step2Labels = labelEmbedding1 ∘ raw24529step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24529step2 raw24529step2Labels raw24529step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical24530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24530 raw24530Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw24530 raw24530Labels = mixedMoment B raw24530step0 raw24530step0Labels := by
      have hz : ∀ j, raw24530 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24530step0 = (fun i j => raw24530 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24530step0 raw24530; decide +kernel
      have hl : raw24530step0Labels = raw24530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24530 raw24530Labels permutation265 hz
    mixedMoment B raw24530step0 raw24530step0Labels = mixedMoment B raw24530step1 raw24530step1Labels := by
      have ha : raw24530step1 = (fun i j => raw24530step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24530step1 raw24530step0; decide +kernel
      have hl : raw24530step1Labels = raw24530step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24530step0 raw24530step0Labels permutation32 permutation7
    mixedMoment B raw24530step1 raw24530step1Labels = mixedMoment B raw24530step2 raw24530step2Labels := by
      have ha : raw24530step2 = -raw24530step1 := by apply Matrix.ext; change ∀ i j, raw24530step2 i j = -(raw24530step1 i j); unfold raw24530step2 raw24530step1; decide +kernel
      have hl : raw24530step2Labels = raw24530step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24530step2 raw24530step2Labels = mixedMoment B raw24530step3 raw24530step3Labels := by
      have ha : raw24530step3 = raw24530step2 := by apply Matrix.ext; unfold raw24530step3 raw24530step2; decide +kernel
      have hl : raw24530step2Labels = labelEmbedding1 ∘ raw24530step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24530step2 raw24530step2Labels raw24530step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3304 node3304Labels := by rfl

theorem canonical24531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24531 raw24531Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw24531 raw24531Labels = mixedMoment B raw24531step0 raw24531step0Labels := by
      have hz : ∀ j, raw24531 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24531step0 = (fun i j => raw24531 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24531step0 raw24531; decide +kernel
      have hl : raw24531step0Labels = raw24531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24531 raw24531Labels permutation265 hz
    mixedMoment B raw24531step0 raw24531step0Labels = mixedMoment B raw24531step1 raw24531step1Labels := by
      have ha : raw24531step1 = (fun i j => raw24531step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24531step1 raw24531step0; decide +kernel
      have hl : raw24531step1Labels = raw24531step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24531step0 raw24531step0Labels permutation44 permutation5
    mixedMoment B raw24531step1 raw24531step1Labels = mixedMoment B raw24531step2 raw24531step2Labels := by
      have ha : raw24531step2 = -raw24531step1 := by apply Matrix.ext; change ∀ i j, raw24531step2 i j = -(raw24531step1 i j); unfold raw24531step2 raw24531step1; decide +kernel
      have hl : raw24531step2Labels = raw24531step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24531step2 raw24531step2Labels = mixedMoment B raw24531step3 raw24531step3Labels := by
      have ha : raw24531step3 = raw24531step2 := by apply Matrix.ext; unfold raw24531step3 raw24531step2; decide +kernel
      have hl : raw24531step2Labels = labelEmbedding1 ∘ raw24531step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24531step2 raw24531step2Labels raw24531step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

theorem canonical24532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24532 raw24532Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw24532 raw24532Labels = mixedMoment B raw24532step0 raw24532step0Labels := by
      have ha : raw24532step0 = (fun i j => raw24532 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24532step0 raw24532; decide +kernel
      have hl : raw24532step0Labels = raw24532Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24532 raw24532Labels permutation164 permutation5
    mixedMoment B raw24532step0 raw24532step0Labels = mixedMoment B raw24532step1 raw24532step1Labels := by
      have ha : raw24532step1 = -raw24532step0 := by apply Matrix.ext; change ∀ i j, raw24532step1 i j = -(raw24532step0 i j); unfold raw24532step1 raw24532step0; decide +kernel
      have hl : raw24532step1Labels = raw24532step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24532step1 raw24532step1Labels = mixedMoment B raw24532step2 raw24532step2Labels := by
      have ha : raw24532step2 = raw24532step1 := by apply Matrix.ext; unfold raw24532step2 raw24532step1; decide +kernel
      have hl : raw24532step1Labels = labelEmbedding1 ∘ raw24532step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24532step1 raw24532step1Labels raw24532step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

theorem canonical24533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24533 raw24533Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw24533 raw24533Labels = mixedMoment B raw24533step0 raw24533step0Labels := by
      have hz : ∀ j, raw24533 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24533step0 = (fun i j => raw24533 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24533step0 raw24533; decide +kernel
      have hl : raw24533step0Labels = raw24533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24533 raw24533Labels permutation265 hz
    mixedMoment B raw24533step0 raw24533step0Labels = mixedMoment B raw24533step1 raw24533step1Labels := by
      have ha : raw24533step1 = (fun i j => raw24533step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24533step1 raw24533step0; decide +kernel
      have hl : raw24533step1Labels = raw24533step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24533step0 raw24533step0Labels permutation34 permutation7
    mixedMoment B raw24533step1 raw24533step1Labels = mixedMoment B raw24533step2 raw24533step2Labels := by
      have ha : raw24533step2 = -raw24533step1 := by apply Matrix.ext; change ∀ i j, raw24533step2 i j = -(raw24533step1 i j); unfold raw24533step2 raw24533step1; decide +kernel
      have hl : raw24533step2Labels = raw24533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24533step2 raw24533step2Labels = mixedMoment B raw24533step3 raw24533step3Labels := by
      have ha : raw24533step3 = raw24533step2 := by apply Matrix.ext; unfold raw24533step3 raw24533step2; decide +kernel
      have hl : raw24533step2Labels = labelEmbedding1 ∘ raw24533step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24533step2 raw24533step2Labels raw24533step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3274 node3274Labels := by rfl

theorem canonical24534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24534 raw24534Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw24534 raw24534Labels = mixedMoment B raw24534step0 raw24534step0Labels := by
      have hz : ∀ j, raw24534 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24534step0 = (fun i j => raw24534 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24534step0 raw24534; decide +kernel
      have hl : raw24534step0Labels = raw24534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24534 raw24534Labels permutation265 hz
    mixedMoment B raw24534step0 raw24534step0Labels = mixedMoment B raw24534step1 raw24534step1Labels := by
      have ha : raw24534step1 = (fun i j => raw24534step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24534step1 raw24534step0; decide +kernel
      have hl : raw24534step1Labels = raw24534step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24534step0 raw24534step0Labels permutation44 permutation5
    mixedMoment B raw24534step1 raw24534step1Labels = mixedMoment B raw24534step2 raw24534step2Labels := by
      have ha : raw24534step2 = -raw24534step1 := by apply Matrix.ext; change ∀ i j, raw24534step2 i j = -(raw24534step1 i j); unfold raw24534step2 raw24534step1; decide +kernel
      have hl : raw24534step2Labels = raw24534step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24534step2 raw24534step2Labels = mixedMoment B raw24534step3 raw24534step3Labels := by
      have ha : raw24534step3 = raw24534step2 := by apply Matrix.ext; unfold raw24534step3 raw24534step2; decide +kernel
      have hl : raw24534step2Labels = labelEmbedding1 ∘ raw24534step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24534step2 raw24534step2Labels raw24534step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3297 node3297Labels := by rfl

theorem canonical24535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24535 raw24535Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw24535 raw24535Labels = mixedMoment B raw24535step0 raw24535step0Labels := by
      have hz : ∀ j, raw24535 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24535step0 = (fun i j => raw24535 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24535step0 raw24535; decide +kernel
      have hl : raw24535step0Labels = raw24535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24535 raw24535Labels permutation265 hz
    mixedMoment B raw24535step0 raw24535step0Labels = mixedMoment B raw24535step1 raw24535step1Labels := by
      have ha : raw24535step1 = (fun i j => raw24535step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24535step1 raw24535step0; decide +kernel
      have hl : raw24535step1Labels = raw24535step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24535step0 raw24535step0Labels permutation35 permutation7
    mixedMoment B raw24535step1 raw24535step1Labels = mixedMoment B raw24535step2 raw24535step2Labels := by
      have ha : raw24535step2 = -raw24535step1 := by apply Matrix.ext; change ∀ i j, raw24535step2 i j = -(raw24535step1 i j); unfold raw24535step2 raw24535step1; decide +kernel
      have hl : raw24535step2Labels = raw24535step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24535step2 raw24535step2Labels = mixedMoment B raw24535step3 raw24535step3Labels := by
      have ha : raw24535step3 = raw24535step2 := by apply Matrix.ext; unfold raw24535step3 raw24535step2; decide +kernel
      have hl : raw24535step2Labels = labelEmbedding1 ∘ raw24535step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24535step2 raw24535step2Labels raw24535step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical24536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24536 raw24536Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw24536 raw24536Labels = mixedMoment B raw24536step0 raw24536step0Labels := by
      have hz : ∀ j, raw24536 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24536step0 = (fun i j => raw24536 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24536step0 raw24536; decide +kernel
      have hl : raw24536step0Labels = raw24536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24536 raw24536Labels permutation265 hz
    mixedMoment B raw24536step0 raw24536step0Labels = mixedMoment B raw24536step1 raw24536step1Labels := by
      have ha : raw24536step1 = (fun i j => raw24536step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24536step1 raw24536step0; decide +kernel
      have hl : raw24536step1Labels = raw24536step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24536step0 raw24536step0Labels permutation38 permutation5
    mixedMoment B raw24536step1 raw24536step1Labels = mixedMoment B raw24536step2 raw24536step2Labels := by
      have ha : raw24536step2 = -raw24536step1 := by apply Matrix.ext; change ∀ i j, raw24536step2 i j = -(raw24536step1 i j); unfold raw24536step2 raw24536step1; decide +kernel
      have hl : raw24536step2Labels = raw24536step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24536step2 raw24536step2Labels = mixedMoment B raw24536step3 raw24536step3Labels := by
      have ha : raw24536step3 = raw24536step2 := by apply Matrix.ext; unfold raw24536step3 raw24536step2; decide +kernel
      have hl : raw24536step2Labels = labelEmbedding1 ∘ raw24536step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24536step2 raw24536step2Labels raw24536step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

theorem canonical24537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24537 raw24537Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw24537 raw24537Labels = mixedMoment B raw24537step0 raw24537step0Labels := by
      have ha : raw24537step0 = (fun i j => raw24537 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24537step0 raw24537; decide +kernel
      have hl : raw24537step0Labels = raw24537Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24537 raw24537Labels permutation158 permutation5
    mixedMoment B raw24537step0 raw24537step0Labels = mixedMoment B raw24537step1 raw24537step1Labels := by
      have ha : raw24537step1 = -raw24537step0 := by apply Matrix.ext; change ∀ i j, raw24537step1 i j = -(raw24537step0 i j); unfold raw24537step1 raw24537step0; decide +kernel
      have hl : raw24537step1Labels = raw24537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24537step1 raw24537step1Labels = mixedMoment B raw24537step2 raw24537step2Labels := by
      have ha : raw24537step2 = raw24537step1 := by apply Matrix.ext; unfold raw24537step2 raw24537step1; decide +kernel
      have hl : raw24537step1Labels = labelEmbedding1 ∘ raw24537step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24537step1 raw24537step1Labels raw24537step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

theorem canonical24538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24538 raw24538Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw24538 raw24538Labels = mixedMoment B raw24538step0 raw24538step0Labels := by
      have hz : ∀ j, raw24538 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24538step0 = (fun i j => raw24538 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24538step0 raw24538; decide +kernel
      have hl : raw24538step0Labels = raw24538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24538 raw24538Labels permutation265 hz
    mixedMoment B raw24538step0 raw24538step0Labels = mixedMoment B raw24538step1 raw24538step1Labels := by
      have ha : raw24538step1 = (fun i j => raw24538step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24538step1 raw24538step0; decide +kernel
      have hl : raw24538step1Labels = raw24538step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24538step0 raw24538step0Labels permutation32 permutation7
    mixedMoment B raw24538step1 raw24538step1Labels = mixedMoment B raw24538step2 raw24538step2Labels := by
      have ha : raw24538step2 = -raw24538step1 := by apply Matrix.ext; change ∀ i j, raw24538step2 i j = -(raw24538step1 i j); unfold raw24538step2 raw24538step1; decide +kernel
      have hl : raw24538step2Labels = raw24538step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24538step2 raw24538step2Labels = mixedMoment B raw24538step3 raw24538step3Labels := by
      have ha : raw24538step3 = raw24538step2 := by apply Matrix.ext; unfold raw24538step3 raw24538step2; decide +kernel
      have hl : raw24538step2Labels = labelEmbedding1 ∘ raw24538step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24538step2 raw24538step2Labels raw24538step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3274 node3274Labels := by rfl

theorem canonical24539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24539 raw24539Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw24539 raw24539Labels = mixedMoment B raw24539step0 raw24539step0Labels := by
      have hz : ∀ j, raw24539 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24539step0 = (fun i j => raw24539 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24539step0 raw24539; decide +kernel
      have hl : raw24539step0Labels = raw24539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24539 raw24539Labels permutation265 hz
    mixedMoment B raw24539step0 raw24539step0Labels = mixedMoment B raw24539step1 raw24539step1Labels := by
      have ha : raw24539step1 = (fun i j => raw24539step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24539step1 raw24539step0; decide +kernel
      have hl : raw24539step1Labels = raw24539step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24539step0 raw24539step0Labels permutation38 permutation5
    mixedMoment B raw24539step1 raw24539step1Labels = mixedMoment B raw24539step2 raw24539step2Labels := by
      have ha : raw24539step2 = -raw24539step1 := by apply Matrix.ext; change ∀ i j, raw24539step2 i j = -(raw24539step1 i j); unfold raw24539step2 raw24539step1; decide +kernel
      have hl : raw24539step2Labels = raw24539step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24539step2 raw24539step2Labels = mixedMoment B raw24539step3 raw24539step3Labels := by
      have ha : raw24539step3 = raw24539step2 := by apply Matrix.ext; unfold raw24539step3 raw24539step2; decide +kernel
      have hl : raw24539step2Labels = labelEmbedding1 ∘ raw24539step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24539step2 raw24539step2Labels raw24539step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3297 node3297Labels := by rfl

theorem canonical24540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24540 raw24540Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw24540 raw24540Labels = mixedMoment B raw24540step0 raw24540step0Labels := by
      have hz : ∀ j, raw24540 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24540step0 = (fun i j => raw24540 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24540step0 raw24540; decide +kernel
      have hl : raw24540step0Labels = raw24540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24540 raw24540Labels permutation265 hz
    mixedMoment B raw24540step0 raw24540step0Labels = mixedMoment B raw24540step1 raw24540step1Labels := by
      have ha : raw24540step1 = (fun i j => raw24540step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24540step1 raw24540step0; decide +kernel
      have hl : raw24540step1Labels = raw24540step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24540step0 raw24540step0Labels permutation33 permutation7
    mixedMoment B raw24540step1 raw24540step1Labels = mixedMoment B raw24540step2 raw24540step2Labels := by
      have ha : raw24540step2 = -raw24540step1 := by apply Matrix.ext; change ∀ i j, raw24540step2 i j = -(raw24540step1 i j); unfold raw24540step2 raw24540step1; decide +kernel
      have hl : raw24540step2Labels = raw24540step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24540step2 raw24540step2Labels = mixedMoment B raw24540step3 raw24540step3Labels := by
      have ha : raw24540step3 = raw24540step2 := by apply Matrix.ext; unfold raw24540step3 raw24540step2; decide +kernel
      have hl : raw24540step2Labels = labelEmbedding1 ∘ raw24540step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24540step2 raw24540step2Labels raw24540step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical24541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24541 raw24541Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw24541 raw24541Labels = mixedMoment B raw24541step0 raw24541step0Labels := by
      have hz : ∀ j, raw24541 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24541step0 = (fun i j => raw24541 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24541step0 raw24541; decide +kernel
      have hl : raw24541step0Labels = raw24541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24541 raw24541Labels permutation265 hz
    mixedMoment B raw24541step0 raw24541step0Labels = mixedMoment B raw24541step1 raw24541step1Labels := by
      have ha : raw24541step1 = (fun i j => raw24541step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24541step1 raw24541step0; decide +kernel
      have hl : raw24541step1Labels = raw24541step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24541step0 raw24541step0Labels permutation40 permutation5
    mixedMoment B raw24541step1 raw24541step1Labels = mixedMoment B raw24541step2 raw24541step2Labels := by
      have ha : raw24541step2 = -raw24541step1 := by apply Matrix.ext; change ∀ i j, raw24541step2 i j = -(raw24541step1 i j); unfold raw24541step2 raw24541step1; decide +kernel
      have hl : raw24541step2Labels = raw24541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24541step2 raw24541step2Labels = mixedMoment B raw24541step3 raw24541step3Labels := by
      have ha : raw24541step3 = raw24541step2 := by apply Matrix.ext; unfold raw24541step3 raw24541step2; decide +kernel
      have hl : raw24541step2Labels = labelEmbedding1 ∘ raw24541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24541step2 raw24541step2Labels raw24541step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1505 node1505Labels := by rfl

theorem canonical24542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24542 raw24542Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw24542 raw24542Labels = mixedMoment B raw24542step0 raw24542step0Labels := by
      have ha : raw24542step0 = (fun i j => raw24542 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24542step0 raw24542; decide +kernel
      have hl : raw24542step0Labels = raw24542Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24542 raw24542Labels permutation160 permutation5
    mixedMoment B raw24542step0 raw24542step0Labels = mixedMoment B raw24542step1 raw24542step1Labels := by
      have ha : raw24542step1 = -raw24542step0 := by apply Matrix.ext; change ∀ i j, raw24542step1 i j = -(raw24542step0 i j); unfold raw24542step1 raw24542step0; decide +kernel
      have hl : raw24542step1Labels = raw24542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24542step1 raw24542step1Labels = mixedMoment B raw24542step2 raw24542step2Labels := by
      have ha : raw24542step2 = raw24542step1 := by apply Matrix.ext; unfold raw24542step2 raw24542step1; decide +kernel
      have hl : raw24542step1Labels = labelEmbedding1 ∘ raw24542step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24542step1 raw24542step1Labels raw24542step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3255 node3255Labels := by rfl

theorem canonical24543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24543 raw24543Labels = mixedMoment B node3273 node3273Labels := by
  calc
    mixedMoment B raw24543 raw24543Labels = mixedMoment B raw24543step0 raw24543step0Labels := by
      have hz : ∀ j, raw24543 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24543step0 = (fun i j => raw24543 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24543step0 raw24543; decide +kernel
      have hl : raw24543step0Labels = raw24543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24543 raw24543Labels permutation265 hz
    mixedMoment B raw24543step0 raw24543step0Labels = mixedMoment B raw24543step1 raw24543step1Labels := by
      have ha : raw24543step1 = (fun i j => raw24543step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24543step1 raw24543step0; decide +kernel
      have hl : raw24543step1Labels = raw24543step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24543step0 raw24543step0Labels permutation32 permutation7
    mixedMoment B raw24543step1 raw24543step1Labels = mixedMoment B raw24543step2 raw24543step2Labels := by
      have ha : raw24543step2 = -raw24543step1 := by apply Matrix.ext; change ∀ i j, raw24543step2 i j = -(raw24543step1 i j); unfold raw24543step2 raw24543step1; decide +kernel
      have hl : raw24543step2Labels = raw24543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24543step2 raw24543step2Labels = mixedMoment B raw24543step3 raw24543step3Labels := by
      have ha : raw24543step3 = raw24543step2 := by apply Matrix.ext; unfold raw24543step3 raw24543step2; decide +kernel
      have hl : raw24543step2Labels = labelEmbedding1 ∘ raw24543step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24543step2 raw24543step2Labels raw24543step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3273 node3273Labels := by rfl

theorem canonical24544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24544 raw24544Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw24544 raw24544Labels = mixedMoment B raw24544step0 raw24544step0Labels := by
      have hz : ∀ j, raw24544 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24544step0 = (fun i j => raw24544 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24544step0 raw24544; decide +kernel
      have hl : raw24544step0Labels = raw24544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24544 raw24544Labels permutation265 hz
    mixedMoment B raw24544step0 raw24544step0Labels = mixedMoment B raw24544step1 raw24544step1Labels := by
      have ha : raw24544step1 = (fun i j => raw24544step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24544step1 raw24544step0; decide +kernel
      have hl : raw24544step1Labels = raw24544step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24544step0 raw24544step0Labels permutation40 permutation5
    mixedMoment B raw24544step1 raw24544step1Labels = mixedMoment B raw24544step2 raw24544step2Labels := by
      have ha : raw24544step2 = -raw24544step1 := by apply Matrix.ext; change ∀ i j, raw24544step2 i j = -(raw24544step1 i j); unfold raw24544step2 raw24544step1; decide +kernel
      have hl : raw24544step2Labels = raw24544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24544step2 raw24544step2Labels = mixedMoment B raw24544step3 raw24544step3Labels := by
      have ha : raw24544step3 = raw24544step2 := by apply Matrix.ext; unfold raw24544step3 raw24544step2; decide +kernel
      have hl : raw24544step2Labels = labelEmbedding1 ∘ raw24544step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24544step2 raw24544step2Labels raw24544step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical24545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24545 raw24545Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw24545 raw24545Labels = mixedMoment B raw24545step0 raw24545step0Labels := by
      have hz : ∀ j, raw24545 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24545step0 = (fun i j => raw24545 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24545step0 raw24545; decide +kernel
      have hl : raw24545step0Labels = raw24545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24545 raw24545Labels permutation265 hz
    mixedMoment B raw24545step0 raw24545step0Labels = mixedMoment B raw24545step1 raw24545step1Labels := by
      have ha : raw24545step1 = (fun i j => raw24545step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24545step1 raw24545step0; decide +kernel
      have hl : raw24545step1Labels = raw24545step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24545step0 raw24545step0Labels permutation46 permutation5
    mixedMoment B raw24545step1 raw24545step1Labels = mixedMoment B raw24545step2 raw24545step2Labels := by
      have ha : raw24545step2 = -raw24545step1 := by apply Matrix.ext; change ∀ i j, raw24545step2 i j = -(raw24545step1 i j); unfold raw24545step2 raw24545step1; decide +kernel
      have hl : raw24545step2Labels = raw24545step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24545step2 raw24545step2Labels = mixedMoment B raw24545step3 raw24545step3Labels := by
      have ha : raw24545step3 = raw24545step2 := by apply Matrix.ext; unfold raw24545step3 raw24545step2; decide +kernel
      have hl : raw24545step2Labels = labelEmbedding1 ∘ raw24545step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24545step2 raw24545step2Labels raw24545step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical24546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24546 raw24546Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw24546 raw24546Labels = mixedMoment B raw24546step0 raw24546step0Labels := by
      have hz : ∀ j, raw24546 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24546step0 = (fun i j => raw24546 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24546step0 raw24546; decide +kernel
      have hl : raw24546step0Labels = raw24546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24546 raw24546Labels permutation265 hz
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical24547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24547 raw24547Labels = mixedMoment B node625 node625Labels := by
  calc
    mixedMoment B raw24547 raw24547Labels = mixedMoment B raw24547step0 raw24547step0Labels := by
      have ha : raw24547step0 = (fun i j => raw24547 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24547step0 raw24547; decide +kernel
      have hl : raw24547step0Labels = raw24547Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24547 raw24547Labels permutation176 permutation2
    _ = mixedMoment B node625 node625Labels := by rfl

theorem canonical24548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24548 raw24548Labels = mixedMoment B node640 node640Labels := by
  calc
    mixedMoment B raw24548 raw24548Labels = mixedMoment B raw24548step0 raw24548step0Labels := by
      have hz : ∀ j, raw24548 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24548step0 = (fun i j => raw24548 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24548step0 raw24548; decide +kernel
      have hl : raw24548step0Labels = raw24548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24548 raw24548Labels permutation265 hz
    _ = mixedMoment B node640 node640Labels := by rfl

theorem canonical24549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24549 raw24549Labels = mixedMoment B node632 node632Labels := by
  calc
    mixedMoment B raw24549 raw24549Labels = mixedMoment B raw24549step0 raw24549step0Labels := by
      have hz : ∀ j, raw24549 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24549step0 = (fun i j => raw24549 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24549step0 raw24549; decide +kernel
      have hl : raw24549step0Labels = raw24549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24549 raw24549Labels permutation265 hz
    mixedMoment B raw24549step0 raw24549step0Labels = mixedMoment B raw24549step1 raw24549step1Labels := by
      have ha : raw24549step1 = (fun i j => raw24549step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24549step1 raw24549step0; decide +kernel
      have hl : raw24549step1Labels = raw24549step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24549step0 raw24549step0Labels permutation34 permutation2
    _ = mixedMoment B node632 node632Labels := by rfl

theorem canonical24550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24550 raw24550Labels = mixedMoment B node632 node632Labels := by
  calc
    mixedMoment B raw24550 raw24550Labels = mixedMoment B raw24550step0 raw24550step0Labels := by
      have hz : ∀ j, raw24550 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24550step0 = (fun i j => raw24550 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24550step0 raw24550; decide +kernel
      have hl : raw24550step0Labels = raw24550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24550 raw24550Labels permutation265 hz
    _ = mixedMoment B node632 node632Labels := by rfl

theorem canonical24551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24551 raw24551Labels = mixedMoment B node630 node630Labels := by
  calc
    mixedMoment B raw24551 raw24551Labels = mixedMoment B raw24551step0 raw24551step0Labels := by
      have hz : ∀ j, raw24551 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24551step0 = (fun i j => raw24551 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24551step0 raw24551; decide +kernel
      have hl : raw24551step0Labels = raw24551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24551 raw24551Labels permutation265 hz
    _ = mixedMoment B node630 node630Labels := by rfl

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

theorem canonical24553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24553 raw24553Labels = mixedMoment B node2556 node2556Labels := by
  calc
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical24554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24554 raw24554Labels = mixedMoment B node1158 node1158Labels := by
  calc
    _ = mixedMoment B node1158 node1158Labels := by rfl

theorem canonical24555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24555 raw24555Labels = mixedMoment B node1152 node1152Labels := by
  calc
    mixedMoment B raw24555 raw24555Labels = mixedMoment B raw24555step0 raw24555step0Labels := by
      have ha : raw24555step0 = (fun i j => raw24555 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24555step0 raw24555; decide +kernel
      have hl : raw24555step0Labels = raw24555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24555 raw24555Labels permutation154 permutation2
    _ = mixedMoment B node1152 node1152Labels := by rfl

theorem canonical24556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24556 raw24556Labels = mixedMoment B node1152 node1152Labels := by
  calc
    _ = mixedMoment B node1152 node1152Labels := by rfl

theorem canonical24557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24557 raw24557Labels = mixedMoment B node1150 node1150Labels := by
  calc
    _ = mixedMoment B node1150 node1150Labels := by rfl

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

theorem canonical24710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24710 raw24710Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw24710 raw24710Labels = mixedMoment B raw24710step0 raw24710step0Labels := by
      have ha : raw24710step0 = (fun i j => raw24710 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24710step0 raw24710; decide +kernel
      have hl : raw24710step0Labels = raw24710Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24710 raw24710Labels permutation178 permutation7
    mixedMoment B raw24710step0 raw24710step0Labels = mixedMoment B raw24710step1 raw24710step1Labels := by
      have ha : raw24710step1 = -raw24710step0 := by apply Matrix.ext; change ∀ i j, raw24710step1 i j = -(raw24710step0 i j); unfold raw24710step1 raw24710step0; decide +kernel
      have hl : raw24710step1Labels = raw24710step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24710step1 raw24710step1Labels = mixedMoment B raw24710step2 raw24710step2Labels := by
      have ha : raw24710step2 = raw24710step1 := by apply Matrix.ext; unfold raw24710step2 raw24710step1; decide +kernel
      have hl : raw24710step1Labels = labelEmbedding1 ∘ raw24710step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24710step1 raw24710step1Labels raw24710step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical24711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24711 raw24711Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw24711 raw24711Labels = mixedMoment B raw24711step0 raw24711step0Labels := by
      have hz : ∀ j, raw24711 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24711step0 = (fun i j => raw24711 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24711step0 raw24711; decide +kernel
      have hl : raw24711step0Labels = raw24711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24711 raw24711Labels permutation265 hz
    mixedMoment B raw24711step0 raw24711step0Labels = mixedMoment B raw24711step1 raw24711step1Labels := by
      have ha : raw24711step1 = (fun i j => raw24711step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24711step1 raw24711step0; decide +kernel
      have hl : raw24711step1Labels = raw24711step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24711step0 raw24711step0Labels permutation34 permutation7
    mixedMoment B raw24711step1 raw24711step1Labels = mixedMoment B raw24711step2 raw24711step2Labels := by
      have ha : raw24711step2 = -raw24711step1 := by apply Matrix.ext; change ∀ i j, raw24711step2 i j = -(raw24711step1 i j); unfold raw24711step2 raw24711step1; decide +kernel
      have hl : raw24711step2Labels = raw24711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24711step2 raw24711step2Labels = mixedMoment B raw24711step3 raw24711step3Labels := by
      have ha : raw24711step3 = raw24711step2 := by apply Matrix.ext; unfold raw24711step3 raw24711step2; decide +kernel
      have hl : raw24711step2Labels = labelEmbedding1 ∘ raw24711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24711step2 raw24711step2Labels raw24711step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

theorem canonical24712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24712 raw24712Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw24712 raw24712Labels = mixedMoment B raw24712step0 raw24712step0Labels := by
      have hz : ∀ j, raw24712 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24712step0 = (fun i j => raw24712 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24712step0 raw24712; decide +kernel
      have hl : raw24712step0Labels = raw24712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24712 raw24712Labels permutation265 hz
    mixedMoment B raw24712step0 raw24712step0Labels = mixedMoment B raw24712step1 raw24712step1Labels := by
      have ha : raw24712step1 = (fun i j => raw24712step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24712step1 raw24712step0; decide +kernel
      have hl : raw24712step1Labels = raw24712step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24712step0 raw24712step0Labels permutation34 permutation7
    mixedMoment B raw24712step1 raw24712step1Labels = mixedMoment B raw24712step2 raw24712step2Labels := by
      have ha : raw24712step2 = -raw24712step1 := by apply Matrix.ext; change ∀ i j, raw24712step2 i j = -(raw24712step1 i j); unfold raw24712step2 raw24712step1; decide +kernel
      have hl : raw24712step2Labels = raw24712step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24712step2 raw24712step2Labels = mixedMoment B raw24712step3 raw24712step3Labels := by
      have ha : raw24712step3 = raw24712step2 := by apply Matrix.ext; unfold raw24712step3 raw24712step2; decide +kernel
      have hl : raw24712step2Labels = labelEmbedding1 ∘ raw24712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24712step2 raw24712step2Labels raw24712step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical24713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24713 raw24713Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw24713 raw24713Labels = mixedMoment B raw24713step0 raw24713step0Labels := by
      have hz : ∀ j, raw24713 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24713step0 = (fun i j => raw24713 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24713step0 raw24713; decide +kernel
      have hl : raw24713step0Labels = raw24713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24713 raw24713Labels permutation520 hz
    mixedMoment B raw24713step0 raw24713step0Labels = mixedMoment B raw24713step1 raw24713step1Labels := by
      have hz : ∀ j, raw24713step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24713step1 = (fun i j => raw24713step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24713step1 raw24713step0; decide +kernel
      have hl : raw24713step1Labels = raw24713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24713step0 raw24713step0Labels permutation56 hz
    mixedMoment B raw24713step1 raw24713step1Labels = mixedMoment B raw24713step2 raw24713step2Labels := by
      have ha : raw24713step2 = (fun i j => raw24713step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24713step2 raw24713step1; decide +kernel
      have hl : raw24713step2Labels = raw24713step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24713step1 raw24713step1Labels permutation8 permutation7
    mixedMoment B raw24713step2 raw24713step2Labels = mixedMoment B raw24713step3 raw24713step3Labels := by
      have ha : raw24713step3 = -raw24713step2 := by apply Matrix.ext; change ∀ i j, raw24713step3 i j = -(raw24713step2 i j); unfold raw24713step3 raw24713step2; decide +kernel
      have hl : raw24713step3Labels = raw24713step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24713step3 raw24713step3Labels = mixedMoment B raw24713step4 raw24713step4Labels := by
      have ha : raw24713step4 = raw24713step3 := by apply Matrix.ext; unfold raw24713step4 raw24713step3; decide +kernel
      have hl : raw24713step3Labels = labelEmbedding1 ∘ raw24713step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24713step3 raw24713step3Labels raw24713step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical24714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24714 raw24714Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw24714 raw24714Labels = mixedMoment B raw24714step0 raw24714step0Labels := by
      have hz : ∀ j, raw24714 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24714step0 = (fun i j => raw24714 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24714step0 raw24714; decide +kernel
      have hl : raw24714step0Labels = raw24714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24714 raw24714Labels permutation265 hz
    mixedMoment B raw24714step0 raw24714step0Labels = mixedMoment B raw24714step1 raw24714step1Labels := by
      have ha : raw24714step1 = (fun i j => raw24714step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24714step1 raw24714step0; decide +kernel
      have hl : raw24714step1Labels = raw24714step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24714step0 raw24714step0Labels permutation34 permutation7
    mixedMoment B raw24714step1 raw24714step1Labels = mixedMoment B raw24714step2 raw24714step2Labels := by
      have ha : raw24714step2 = -raw24714step1 := by apply Matrix.ext; change ∀ i j, raw24714step2 i j = -(raw24714step1 i j); unfold raw24714step2 raw24714step1; decide +kernel
      have hl : raw24714step2Labels = raw24714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24714step2 raw24714step2Labels = mixedMoment B raw24714step3 raw24714step3Labels := by
      have ha : raw24714step3 = raw24714step2 := by apply Matrix.ext; unfold raw24714step3 raw24714step2; decide +kernel
      have hl : raw24714step2Labels = labelEmbedding1 ∘ raw24714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24714step2 raw24714step2Labels raw24714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical24715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24715 raw24715Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw24715 raw24715Labels = mixedMoment B raw24715step0 raw24715step0Labels := by
      have ha : raw24715step0 = (fun i j => raw24715 (permutation220 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24715step0 raw24715; decide +kernel
      have hl : raw24715step0Labels = raw24715Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24715 raw24715Labels permutation220 permutation5
    mixedMoment B raw24715step0 raw24715step0Labels = mixedMoment B raw24715step1 raw24715step1Labels := by
      have ha : raw24715step1 = -raw24715step0 := by apply Matrix.ext; change ∀ i j, raw24715step1 i j = -(raw24715step0 i j); unfold raw24715step1 raw24715step0; decide +kernel
      have hl : raw24715step1Labels = raw24715step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24715step1 raw24715step1Labels = mixedMoment B raw24715step2 raw24715step2Labels := by
      have ha : raw24715step2 = raw24715step1 := by apply Matrix.ext; unfold raw24715step2 raw24715step1; decide +kernel
      have hl : raw24715step1Labels = labelEmbedding1 ∘ raw24715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24715step1 raw24715step1Labels raw24715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1510 node1510Labels := by rfl

theorem canonical24716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24716 raw24716Labels = mixedMoment B node3256 node3256Labels := by
  calc
    mixedMoment B raw24716 raw24716Labels = mixedMoment B raw24716step0 raw24716step0Labels := by
      have ha : raw24716step0 = (fun i j => raw24716 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24716step0 raw24716; decide +kernel
      have hl : raw24716step0Labels = raw24716Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24716 raw24716Labels permutation178 permutation7
    mixedMoment B raw24716step0 raw24716step0Labels = mixedMoment B raw24716step1 raw24716step1Labels := by
      have ha : raw24716step1 = -raw24716step0 := by apply Matrix.ext; change ∀ i j, raw24716step1 i j = -(raw24716step0 i j); unfold raw24716step1 raw24716step0; decide +kernel
      have hl : raw24716step1Labels = raw24716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24716step1 raw24716step1Labels = mixedMoment B raw24716step2 raw24716step2Labels := by
      have ha : raw24716step2 = raw24716step1 := by apply Matrix.ext; unfold raw24716step2 raw24716step1; decide +kernel
      have hl : raw24716step1Labels = labelEmbedding1 ∘ raw24716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24716step1 raw24716step1Labels raw24716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3256 node3256Labels := by rfl

theorem canonical24717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24717 raw24717Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw24717 raw24717Labels = mixedMoment B raw24717step0 raw24717step0Labels := by
      have ha : raw24717step0 = (fun i j => raw24717 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24717step0 raw24717; decide +kernel
      have hl : raw24717step0Labels = raw24717Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24717 raw24717Labels permutation178 permutation7
    mixedMoment B raw24717step0 raw24717step0Labels = mixedMoment B raw24717step1 raw24717step1Labels := by
      have ha : raw24717step1 = -raw24717step0 := by apply Matrix.ext; change ∀ i j, raw24717step1 i j = -(raw24717step0 i j); unfold raw24717step1 raw24717step0; decide +kernel
      have hl : raw24717step1Labels = raw24717step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24717step1 raw24717step1Labels = mixedMoment B raw24717step2 raw24717step2Labels := by
      have ha : raw24717step2 = raw24717step1 := by apply Matrix.ext; unfold raw24717step2 raw24717step1; decide +kernel
      have hl : raw24717step1Labels = labelEmbedding1 ∘ raw24717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24717step1 raw24717step1Labels raw24717step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical24718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24718 raw24718Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw24718 raw24718Labels = mixedMoment B raw24718step0 raw24718step0Labels := by
      have hz : ∀ j, raw24718 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24718step0 = (fun i j => raw24718 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24718step0 raw24718; decide +kernel
      have hl : raw24718step0Labels = raw24718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24718 raw24718Labels permutation520 hz
    mixedMoment B raw24718step0 raw24718step0Labels = mixedMoment B raw24718step1 raw24718step1Labels := by
      have ha : raw24718step1 = (fun i j => raw24718step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24718step1 raw24718step0; decide +kernel
      have hl : raw24718step1Labels = raw24718step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24718step0 raw24718step0Labels permutation38 permutation7
    mixedMoment B raw24718step1 raw24718step1Labels = mixedMoment B raw24718step2 raw24718step2Labels := by
      have ha : raw24718step2 = -raw24718step1 := by apply Matrix.ext; change ∀ i j, raw24718step2 i j = -(raw24718step1 i j); unfold raw24718step2 raw24718step1; decide +kernel
      have hl : raw24718step2Labels = raw24718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24718step2 raw24718step2Labels = mixedMoment B raw24718step3 raw24718step3Labels := by
      have ha : raw24718step3 = raw24718step2 := by apply Matrix.ext; unfold raw24718step3 raw24718step2; decide +kernel
      have hl : raw24718step2Labels = labelEmbedding1 ∘ raw24718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24718step2 raw24718step2Labels raw24718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical24719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24719 raw24719Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw24719 raw24719Labels = mixedMoment B raw24719step0 raw24719step0Labels := by
      have ha : raw24719step0 = (fun i j => raw24719 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24719step0 raw24719; decide +kernel
      have hl : raw24719step0Labels = raw24719Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24719 raw24719Labels permutation178 permutation7
    mixedMoment B raw24719step0 raw24719step0Labels = mixedMoment B raw24719step1 raw24719step1Labels := by
      have ha : raw24719step1 = -raw24719step0 := by apply Matrix.ext; change ∀ i j, raw24719step1 i j = -(raw24719step0 i j); unfold raw24719step1 raw24719step0; decide +kernel
      have hl : raw24719step1Labels = raw24719step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24719step1 raw24719step1Labels = mixedMoment B raw24719step2 raw24719step2Labels := by
      have ha : raw24719step2 = raw24719step1 := by apply Matrix.ext; unfold raw24719step2 raw24719step1; decide +kernel
      have hl : raw24719step1Labels = labelEmbedding1 ∘ raw24719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24719step1 raw24719step1Labels raw24719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical24720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24720 raw24720Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw24720 raw24720Labels = mixedMoment B raw24720step0 raw24720step0Labels := by
      have hz : ∀ j, raw24720 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24720step0 = (fun i j => raw24720 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24720step0 raw24720; decide +kernel
      have hl : raw24720step0Labels = raw24720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24720 raw24720Labels permutation265 hz
    mixedMoment B raw24720step0 raw24720step0Labels = mixedMoment B raw24720step1 raw24720step1Labels := by
      have ha : raw24720step1 = (fun i j => raw24720step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24720step1 raw24720step0; decide +kernel
      have hl : raw24720step1Labels = raw24720step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24720step0 raw24720step0Labels permutation43 permutation5
    mixedMoment B raw24720step1 raw24720step1Labels = mixedMoment B raw24720step2 raw24720step2Labels := by
      have ha : raw24720step2 = -raw24720step1 := by apply Matrix.ext; change ∀ i j, raw24720step2 i j = -(raw24720step1 i j); unfold raw24720step2 raw24720step1; decide +kernel
      have hl : raw24720step2Labels = raw24720step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24720step2 raw24720step2Labels = mixedMoment B raw24720step3 raw24720step3Labels := by
      have ha : raw24720step3 = raw24720step2 := by apply Matrix.ext; unfold raw24720step3 raw24720step2; decide +kernel
      have hl : raw24720step2Labels = labelEmbedding1 ∘ raw24720step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24720step2 raw24720step2Labels raw24720step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

theorem canonical24721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24721 raw24721Labels = mixedMoment B node3259 node3259Labels := by
  calc
    mixedMoment B raw24721 raw24721Labels = mixedMoment B raw24721step0 raw24721step0Labels := by
      have ha : raw24721step0 = (fun i j => raw24721 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24721step0 raw24721; decide +kernel
      have hl : raw24721step0Labels = raw24721Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24721 raw24721Labels permutation163 permutation5
    mixedMoment B raw24721step0 raw24721step0Labels = mixedMoment B raw24721step1 raw24721step1Labels := by
      have ha : raw24721step1 = -raw24721step0 := by apply Matrix.ext; change ∀ i j, raw24721step1 i j = -(raw24721step0 i j); unfold raw24721step1 raw24721step0; decide +kernel
      have hl : raw24721step1Labels = raw24721step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24721step1 raw24721step1Labels = mixedMoment B raw24721step2 raw24721step2Labels := by
      have ha : raw24721step2 = raw24721step1 := by apply Matrix.ext; unfold raw24721step2 raw24721step1; decide +kernel
      have hl : raw24721step1Labels = labelEmbedding1 ∘ raw24721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24721step1 raw24721step1Labels raw24721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3259 node3259Labels := by rfl

theorem canonical24722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24722 raw24722Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw24722 raw24722Labels = mixedMoment B raw24722step0 raw24722step0Labels := by
      have hz : ∀ j, raw24722 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24722step0 = (fun i j => raw24722 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24722step0 raw24722; decide +kernel
      have hl : raw24722step0Labels = raw24722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24722 raw24722Labels permutation265 hz
    mixedMoment B raw24722step0 raw24722step0Labels = mixedMoment B raw24722step1 raw24722step1Labels := by
      have ha : raw24722step1 = (fun i j => raw24722step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24722step1 raw24722step0; decide +kernel
      have hl : raw24722step1Labels = raw24722step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24722step0 raw24722step0Labels permutation43 permutation5
    mixedMoment B raw24722step1 raw24722step1Labels = mixedMoment B raw24722step2 raw24722step2Labels := by
      have ha : raw24722step2 = -raw24722step1 := by apply Matrix.ext; change ∀ i j, raw24722step2 i j = -(raw24722step1 i j); unfold raw24722step2 raw24722step1; decide +kernel
      have hl : raw24722step2Labels = raw24722step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24722step2 raw24722step2Labels = mixedMoment B raw24722step3 raw24722step3Labels := by
      have ha : raw24722step3 = raw24722step2 := by apply Matrix.ext; unfold raw24722step3 raw24722step2; decide +kernel
      have hl : raw24722step2Labels = labelEmbedding1 ∘ raw24722step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24722step2 raw24722step2Labels raw24722step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical24723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24723 raw24723Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw24723 raw24723Labels = mixedMoment B raw24723step0 raw24723step0Labels := by
      have hz : ∀ j, raw24723 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24723step0 = (fun i j => raw24723 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24723step0 raw24723; decide +kernel
      have hl : raw24723step0Labels = raw24723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24723 raw24723Labels permutation520 hz
    mixedMoment B raw24723step0 raw24723step0Labels = mixedMoment B raw24723step1 raw24723step1Labels := by
      have hz : ∀ j, raw24723step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24723step1 = (fun i j => raw24723step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24723step1 raw24723step0; decide +kernel
      have hl : raw24723step1Labels = raw24723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24723step0 raw24723step0Labels permutation56 hz
    mixedMoment B raw24723step1 raw24723step1Labels = mixedMoment B raw24723step2 raw24723step2Labels := by
      have ha : raw24723step2 = (fun i j => raw24723step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24723step2 raw24723step1; decide +kernel
      have hl : raw24723step2Labels = raw24723step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24723step1 raw24723step1Labels permutation8 permutation7
    mixedMoment B raw24723step2 raw24723step2Labels = mixedMoment B raw24723step3 raw24723step3Labels := by
      have ha : raw24723step3 = -raw24723step2 := by apply Matrix.ext; change ∀ i j, raw24723step3 i j = -(raw24723step2 i j); unfold raw24723step3 raw24723step2; decide +kernel
      have hl : raw24723step3Labels = raw24723step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24723step3 raw24723step3Labels = mixedMoment B raw24723step4 raw24723step4Labels := by
      have ha : raw24723step4 = raw24723step3 := by apply Matrix.ext; unfold raw24723step4 raw24723step3; decide +kernel
      have hl : raw24723step3Labels = labelEmbedding1 ∘ raw24723step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24723step3 raw24723step3Labels raw24723step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

theorem canonical24724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24724 raw24724Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw24724 raw24724Labels = mixedMoment B raw24724step0 raw24724step0Labels := by
      have hz : ∀ j, raw24724 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24724step0 = (fun i j => raw24724 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24724step0 raw24724; decide +kernel
      have hl : raw24724step0Labels = raw24724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24724 raw24724Labels permutation265 hz
    mixedMoment B raw24724step0 raw24724step0Labels = mixedMoment B raw24724step1 raw24724step1Labels := by
      have ha : raw24724step1 = (fun i j => raw24724step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24724step1 raw24724step0; decide +kernel
      have hl : raw24724step1Labels = raw24724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24724step0 raw24724step0Labels permutation53 permutation5
    mixedMoment B raw24724step1 raw24724step1Labels = mixedMoment B raw24724step2 raw24724step2Labels := by
      have ha : raw24724step2 = -raw24724step1 := by apply Matrix.ext; change ∀ i j, raw24724step2 i j = -(raw24724step1 i j); unfold raw24724step2 raw24724step1; decide +kernel
      have hl : raw24724step2Labels = raw24724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24724step2 raw24724step2Labels = mixedMoment B raw24724step3 raw24724step3Labels := by
      have ha : raw24724step3 = raw24724step2 := by apply Matrix.ext; unfold raw24724step3 raw24724step2; decide +kernel
      have hl : raw24724step2Labels = labelEmbedding1 ∘ raw24724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24724step2 raw24724step2Labels raw24724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

theorem canonical24725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24725 raw24725Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw24725 raw24725Labels = mixedMoment B raw24725step0 raw24725step0Labels := by
      have hz : ∀ j, raw24725 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24725step0 = (fun i j => raw24725 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24725step0 raw24725; decide +kernel
      have hl : raw24725step0Labels = raw24725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24725 raw24725Labels permutation265 hz
    mixedMoment B raw24725step0 raw24725step0Labels = mixedMoment B raw24725step1 raw24725step1Labels := by
      have ha : raw24725step1 = (fun i j => raw24725step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24725step1 raw24725step0; decide +kernel
      have hl : raw24725step1Labels = raw24725step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24725step0 raw24725step0Labels permutation51 permutation5
    mixedMoment B raw24725step1 raw24725step1Labels = mixedMoment B raw24725step2 raw24725step2Labels := by
      have ha : raw24725step2 = -raw24725step1 := by apply Matrix.ext; change ∀ i j, raw24725step2 i j = -(raw24725step1 i j); unfold raw24725step2 raw24725step1; decide +kernel
      have hl : raw24725step2Labels = raw24725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24725step2 raw24725step2Labels = mixedMoment B raw24725step3 raw24725step3Labels := by
      have ha : raw24725step3 = raw24725step2 := by apply Matrix.ext; unfold raw24725step3 raw24725step2; decide +kernel
      have hl : raw24725step2Labels = labelEmbedding1 ∘ raw24725step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24725step2 raw24725step2Labels raw24725step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

theorem canonical24726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24726 raw24726Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw24726 raw24726Labels = mixedMoment B raw24726step0 raw24726step0Labels := by
      have ha : raw24726step0 = (fun i j => raw24726 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24726step0 raw24726; decide +kernel
      have hl : raw24726step0Labels = raw24726Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24726 raw24726Labels permutation171 permutation5
    mixedMoment B raw24726step0 raw24726step0Labels = mixedMoment B raw24726step1 raw24726step1Labels := by
      have ha : raw24726step1 = -raw24726step0 := by apply Matrix.ext; change ∀ i j, raw24726step1 i j = -(raw24726step0 i j); unfold raw24726step1 raw24726step0; decide +kernel
      have hl : raw24726step1Labels = raw24726step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24726step1 raw24726step1Labels = mixedMoment B raw24726step2 raw24726step2Labels := by
      have ha : raw24726step2 = raw24726step1 := by apply Matrix.ext; unfold raw24726step2 raw24726step1; decide +kernel
      have hl : raw24726step1Labels = labelEmbedding1 ∘ raw24726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24726step1 raw24726step1Labels raw24726step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

theorem canonical24727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24727 raw24727Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw24727 raw24727Labels = mixedMoment B raw24727step0 raw24727step0Labels := by
      have hz : ∀ j, raw24727 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24727step0 = (fun i j => raw24727 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24727step0 raw24727; decide +kernel
      have hl : raw24727step0Labels = raw24727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24727 raw24727Labels permutation265 hz
    mixedMoment B raw24727step0 raw24727step0Labels = mixedMoment B raw24727step1 raw24727step1Labels := by
      have ha : raw24727step1 = (fun i j => raw24727step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24727step1 raw24727step0; decide +kernel
      have hl : raw24727step1Labels = raw24727step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24727step0 raw24727step0Labels permutation34 permutation7
    mixedMoment B raw24727step1 raw24727step1Labels = mixedMoment B raw24727step2 raw24727step2Labels := by
      have ha : raw24727step2 = -raw24727step1 := by apply Matrix.ext; change ∀ i j, raw24727step2 i j = -(raw24727step1 i j); unfold raw24727step2 raw24727step1; decide +kernel
      have hl : raw24727step2Labels = raw24727step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24727step2 raw24727step2Labels = mixedMoment B raw24727step3 raw24727step3Labels := by
      have ha : raw24727step3 = raw24727step2 := by apply Matrix.ext; unfold raw24727step3 raw24727step2; decide +kernel
      have hl : raw24727step2Labels = labelEmbedding1 ∘ raw24727step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24727step2 raw24727step2Labels raw24727step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

theorem canonical24728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24728 raw24728Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw24728 raw24728Labels = mixedMoment B raw24728step0 raw24728step0Labels := by
      have hz : ∀ j, raw24728 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24728step0 = (fun i j => raw24728 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24728step0 raw24728; decide +kernel
      have hl : raw24728step0Labels = raw24728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24728 raw24728Labels permutation520 hz
    mixedMoment B raw24728step0 raw24728step0Labels = mixedMoment B raw24728step1 raw24728step1Labels := by
      have hz : ∀ j, raw24728step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24728step1 = (fun i j => raw24728step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24728step1 raw24728step0; decide +kernel
      have hl : raw24728step1Labels = raw24728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24728step0 raw24728step0Labels permutation56 hz
    mixedMoment B raw24728step1 raw24728step1Labels = mixedMoment B raw24728step2 raw24728step2Labels := by
      have ha : raw24728step2 = (fun i j => raw24728step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24728step2 raw24728step1; decide +kernel
      have hl : raw24728step2Labels = raw24728step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24728step1 raw24728step1Labels permutation8 permutation7
    mixedMoment B raw24728step2 raw24728step2Labels = mixedMoment B raw24728step3 raw24728step3Labels := by
      have ha : raw24728step3 = -raw24728step2 := by apply Matrix.ext; change ∀ i j, raw24728step3 i j = -(raw24728step2 i j); unfold raw24728step3 raw24728step2; decide +kernel
      have hl : raw24728step3Labels = raw24728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24728step3 raw24728step3Labels = mixedMoment B raw24728step4 raw24728step4Labels := by
      have ha : raw24728step4 = raw24728step3 := by apply Matrix.ext; unfold raw24728step4 raw24728step3; decide +kernel
      have hl : raw24728step3Labels = labelEmbedding1 ∘ raw24728step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24728step3 raw24728step3Labels raw24728step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical24729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24729 raw24729Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw24729 raw24729Labels = mixedMoment B raw24729step0 raw24729step0Labels := by
      have hz : ∀ j, raw24729 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24729step0 = (fun i j => raw24729 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24729step0 raw24729; decide +kernel
      have hl : raw24729step0Labels = raw24729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24729 raw24729Labels permutation265 hz
    mixedMoment B raw24729step0 raw24729step0Labels = mixedMoment B raw24729step1 raw24729step1Labels := by
      have ha : raw24729step1 = (fun i j => raw24729step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24729step1 raw24729step0; decide +kernel
      have hl : raw24729step1Labels = raw24729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24729step0 raw24729step0Labels permutation34 permutation7
    mixedMoment B raw24729step1 raw24729step1Labels = mixedMoment B raw24729step2 raw24729step2Labels := by
      have ha : raw24729step2 = -raw24729step1 := by apply Matrix.ext; change ∀ i j, raw24729step2 i j = -(raw24729step1 i j); unfold raw24729step2 raw24729step1; decide +kernel
      have hl : raw24729step2Labels = raw24729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24729step2 raw24729step2Labels = mixedMoment B raw24729step3 raw24729step3Labels := by
      have ha : raw24729step3 = raw24729step2 := by apply Matrix.ext; unfold raw24729step3 raw24729step2; decide +kernel
      have hl : raw24729step2Labels = labelEmbedding1 ∘ raw24729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24729step2 raw24729step2Labels raw24729step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical24730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24730 raw24730Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw24730 raw24730Labels = mixedMoment B raw24730step0 raw24730step0Labels := by
      have hz : ∀ j, raw24730 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24730step0 = (fun i j => raw24730 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24730step0 raw24730; decide +kernel
      have hl : raw24730step0Labels = raw24730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24730 raw24730Labels permutation265 hz
    mixedMoment B raw24730step0 raw24730step0Labels = mixedMoment B raw24730step1 raw24730step1Labels := by
      have ha : raw24730step1 = (fun i j => raw24730step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24730step1 raw24730step0; decide +kernel
      have hl : raw24730step1Labels = raw24730step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24730step0 raw24730step0Labels permutation42 permutation5
    mixedMoment B raw24730step1 raw24730step1Labels = mixedMoment B raw24730step2 raw24730step2Labels := by
      have ha : raw24730step2 = -raw24730step1 := by apply Matrix.ext; change ∀ i j, raw24730step2 i j = -(raw24730step1 i j); unfold raw24730step2 raw24730step1; decide +kernel
      have hl : raw24730step2Labels = raw24730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24730step2 raw24730step2Labels = mixedMoment B raw24730step3 raw24730step3Labels := by
      have ha : raw24730step3 = raw24730step2 := by apply Matrix.ext; unfold raw24730step3 raw24730step2; decide +kernel
      have hl : raw24730step2Labels = labelEmbedding1 ∘ raw24730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24730step2 raw24730step2Labels raw24730step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

theorem canonical24731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24731 raw24731Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw24731 raw24731Labels = mixedMoment B raw24731step0 raw24731step0Labels := by
      have ha : raw24731step0 = (fun i j => raw24731 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24731step0 raw24731; decide +kernel
      have hl : raw24731step0Labels = raw24731Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24731 raw24731Labels permutation162 permutation5
    mixedMoment B raw24731step0 raw24731step0Labels = mixedMoment B raw24731step1 raw24731step1Labels := by
      have ha : raw24731step1 = -raw24731step0 := by apply Matrix.ext; change ∀ i j, raw24731step1 i j = -(raw24731step0 i j); unfold raw24731step1 raw24731step0; decide +kernel
      have hl : raw24731step1Labels = raw24731step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24731step1 raw24731step1Labels = mixedMoment B raw24731step2 raw24731step2Labels := by
      have ha : raw24731step2 = raw24731step1 := by apply Matrix.ext; unfold raw24731step2 raw24731step1; decide +kernel
      have hl : raw24731step1Labels = labelEmbedding1 ∘ raw24731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24731step1 raw24731step1Labels raw24731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3258 node3258Labels := by rfl

theorem canonical24732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24732 raw24732Labels = mixedMoment B node3270 node3270Labels := by
  calc
    mixedMoment B raw24732 raw24732Labels = mixedMoment B raw24732step0 raw24732step0Labels := by
      have hz : ∀ j, raw24732 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24732step0 = (fun i j => raw24732 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24732step0 raw24732; decide +kernel
      have hl : raw24732step0Labels = raw24732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24732 raw24732Labels permutation265 hz
    mixedMoment B raw24732step0 raw24732step0Labels = mixedMoment B raw24732step1 raw24732step1Labels := by
      have ha : raw24732step1 = (fun i j => raw24732step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24732step1 raw24732step0; decide +kernel
      have hl : raw24732step1Labels = raw24732step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24732step0 raw24732step0Labels permutation34 permutation7
    mixedMoment B raw24732step1 raw24732step1Labels = mixedMoment B raw24732step2 raw24732step2Labels := by
      have ha : raw24732step2 = -raw24732step1 := by apply Matrix.ext; change ∀ i j, raw24732step2 i j = -(raw24732step1 i j); unfold raw24732step2 raw24732step1; decide +kernel
      have hl : raw24732step2Labels = raw24732step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24732step2 raw24732step2Labels = mixedMoment B raw24732step3 raw24732step3Labels := by
      have ha : raw24732step3 = raw24732step2 := by apply Matrix.ext; unfold raw24732step3 raw24732step2; decide +kernel
      have hl : raw24732step2Labels = labelEmbedding1 ∘ raw24732step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24732step2 raw24732step2Labels raw24732step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3270 node3270Labels := by rfl

theorem canonical24733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24733 raw24733Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw24733 raw24733Labels = mixedMoment B raw24733step0 raw24733step0Labels := by
      have hz : ∀ j, raw24733 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24733step0 = (fun i j => raw24733 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24733step0 raw24733; decide +kernel
      have hl : raw24733step0Labels = raw24733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24733 raw24733Labels permutation265 hz
    mixedMoment B raw24733step0 raw24733step0Labels = mixedMoment B raw24733step1 raw24733step1Labels := by
      have ha : raw24733step1 = (fun i j => raw24733step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24733step1 raw24733step0; decide +kernel
      have hl : raw24733step1Labels = raw24733step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24733step0 raw24733step0Labels permutation42 permutation5
    mixedMoment B raw24733step1 raw24733step1Labels = mixedMoment B raw24733step2 raw24733step2Labels := by
      have ha : raw24733step2 = -raw24733step1 := by apply Matrix.ext; change ∀ i j, raw24733step2 i j = -(raw24733step1 i j); unfold raw24733step2 raw24733step1; decide +kernel
      have hl : raw24733step2Labels = raw24733step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24733step2 raw24733step2Labels = mixedMoment B raw24733step3 raw24733step3Labels := by
      have ha : raw24733step3 = raw24733step2 := by apply Matrix.ext; unfold raw24733step3 raw24733step2; decide +kernel
      have hl : raw24733step2Labels = labelEmbedding1 ∘ raw24733step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24733step2 raw24733step2Labels raw24733step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3295 node3295Labels := by rfl

theorem canonical24734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24734 raw24734Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw24734 raw24734Labels = mixedMoment B raw24734step0 raw24734step0Labels := by
      have hz : ∀ j, raw24734 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24734step0 = (fun i j => raw24734 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24734step0 raw24734; decide +kernel
      have hl : raw24734step0Labels = raw24734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24734 raw24734Labels permutation265 hz
    mixedMoment B raw24734step0 raw24734step0Labels = mixedMoment B raw24734step1 raw24734step1Labels := by
      have ha : raw24734step1 = (fun i j => raw24734step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24734step1 raw24734step0; decide +kernel
      have hl : raw24734step1Labels = raw24734step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24734step0 raw24734step0Labels permutation34 permutation7
    mixedMoment B raw24734step1 raw24734step1Labels = mixedMoment B raw24734step2 raw24734step2Labels := by
      have ha : raw24734step2 = -raw24734step1 := by apply Matrix.ext; change ∀ i j, raw24734step2 i j = -(raw24734step1 i j); unfold raw24734step2 raw24734step1; decide +kernel
      have hl : raw24734step2Labels = raw24734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24734step2 raw24734step2Labels = mixedMoment B raw24734step3 raw24734step3Labels := by
      have ha : raw24734step3 = raw24734step2 := by apply Matrix.ext; unfold raw24734step3 raw24734step2; decide +kernel
      have hl : raw24734step2Labels = labelEmbedding1 ∘ raw24734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24734step2 raw24734step2Labels raw24734step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical24735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24735 raw24735Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw24735 raw24735Labels = mixedMoment B raw24735step0 raw24735step0Labels := by
      have hz : ∀ j, raw24735 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24735step0 = (fun i j => raw24735 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24735step0 raw24735; decide +kernel
      have hl : raw24735step0Labels = raw24735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24735 raw24735Labels permutation265 hz
    mixedMoment B raw24735step0 raw24735step0Labels = mixedMoment B raw24735step1 raw24735step1Labels := by
      have ha : raw24735step1 = (fun i j => raw24735step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24735step1 raw24735step0; decide +kernel
      have hl : raw24735step1Labels = raw24735step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24735step0 raw24735step0Labels permutation38 permutation5
    mixedMoment B raw24735step1 raw24735step1Labels = mixedMoment B raw24735step2 raw24735step2Labels := by
      have ha : raw24735step2 = -raw24735step1 := by apply Matrix.ext; change ∀ i j, raw24735step2 i j = -(raw24735step1 i j); unfold raw24735step2 raw24735step1; decide +kernel
      have hl : raw24735step2Labels = raw24735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24735step2 raw24735step2Labels = mixedMoment B raw24735step3 raw24735step3Labels := by
      have ha : raw24735step3 = raw24735step2 := by apply Matrix.ext; unfold raw24735step3 raw24735step2; decide +kernel
      have hl : raw24735step2Labels = labelEmbedding1 ∘ raw24735step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24735step2 raw24735step2Labels raw24735step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

theorem canonical24736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24736 raw24736Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw24736 raw24736Labels = mixedMoment B raw24736step0 raw24736step0Labels := by
      have ha : raw24736step0 = (fun i j => raw24736 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24736step0 raw24736; decide +kernel
      have hl : raw24736step0Labels = raw24736Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24736 raw24736Labels permutation158 permutation5
    mixedMoment B raw24736step0 raw24736step0Labels = mixedMoment B raw24736step1 raw24736step1Labels := by
      have ha : raw24736step1 = -raw24736step0 := by apply Matrix.ext; change ∀ i j, raw24736step1 i j = -(raw24736step0 i j); unfold raw24736step1 raw24736step0; decide +kernel
      have hl : raw24736step1Labels = raw24736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24736step1 raw24736step1Labels = mixedMoment B raw24736step2 raw24736step2Labels := by
      have ha : raw24736step2 = raw24736step1 := by apply Matrix.ext; unfold raw24736step2 raw24736step1; decide +kernel
      have hl : raw24736step1Labels = labelEmbedding1 ∘ raw24736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24736step1 raw24736step1Labels raw24736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

theorem canonical24737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24737 raw24737Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw24737 raw24737Labels = mixedMoment B raw24737step0 raw24737step0Labels := by
      have hz : ∀ j, raw24737 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24737step0 = (fun i j => raw24737 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24737step0 raw24737; decide +kernel
      have hl : raw24737step0Labels = raw24737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24737 raw24737Labels permutation265 hz
    mixedMoment B raw24737step0 raw24737step0Labels = mixedMoment B raw24737step1 raw24737step1Labels := by
      have ha : raw24737step1 = (fun i j => raw24737step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24737step1 raw24737step0; decide +kernel
      have hl : raw24737step1Labels = raw24737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24737step0 raw24737step0Labels permutation34 permutation7
    mixedMoment B raw24737step1 raw24737step1Labels = mixedMoment B raw24737step2 raw24737step2Labels := by
      have ha : raw24737step2 = -raw24737step1 := by apply Matrix.ext; change ∀ i j, raw24737step2 i j = -(raw24737step1 i j); unfold raw24737step2 raw24737step1; decide +kernel
      have hl : raw24737step2Labels = raw24737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24737step2 raw24737step2Labels = mixedMoment B raw24737step3 raw24737step3Labels := by
      have ha : raw24737step3 = raw24737step2 := by apply Matrix.ext; unfold raw24737step3 raw24737step2; decide +kernel
      have hl : raw24737step2Labels = labelEmbedding1 ∘ raw24737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24737step2 raw24737step2Labels raw24737step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

theorem canonical24738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24738 raw24738Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw24738 raw24738Labels = mixedMoment B raw24738step0 raw24738step0Labels := by
      have hz : ∀ j, raw24738 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24738step0 = (fun i j => raw24738 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24738step0 raw24738; decide +kernel
      have hl : raw24738step0Labels = raw24738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24738 raw24738Labels permutation265 hz
    mixedMoment B raw24738step0 raw24738step0Labels = mixedMoment B raw24738step1 raw24738step1Labels := by
      have ha : raw24738step1 = (fun i j => raw24738step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24738step1 raw24738step0; decide +kernel
      have hl : raw24738step1Labels = raw24738step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24738step0 raw24738step0Labels permutation34 permutation7
    mixedMoment B raw24738step1 raw24738step1Labels = mixedMoment B raw24738step2 raw24738step2Labels := by
      have ha : raw24738step2 = -raw24738step1 := by apply Matrix.ext; change ∀ i j, raw24738step2 i j = -(raw24738step1 i j); unfold raw24738step2 raw24738step1; decide +kernel
      have hl : raw24738step2Labels = raw24738step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24738step2 raw24738step2Labels = mixedMoment B raw24738step3 raw24738step3Labels := by
      have ha : raw24738step3 = raw24738step2 := by apply Matrix.ext; unfold raw24738step3 raw24738step2; decide +kernel
      have hl : raw24738step2Labels = labelEmbedding1 ∘ raw24738step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24738step2 raw24738step2Labels raw24738step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical24739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24739 raw24739Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw24739 raw24739Labels = mixedMoment B raw24739step0 raw24739step0Labels := by
      have hz : ∀ j, raw24739 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24739step0 = (fun i j => raw24739 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24739step0 raw24739; decide +kernel
      have hl : raw24739step0Labels = raw24739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24739 raw24739Labels permutation520 hz
    mixedMoment B raw24739step0 raw24739step0Labels = mixedMoment B raw24739step1 raw24739step1Labels := by
      have hz : ∀ j, raw24739step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24739step1 = (fun i j => raw24739step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24739step1 raw24739step0; decide +kernel
      have hl : raw24739step1Labels = raw24739step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24739step0 raw24739step0Labels permutation56 hz
    mixedMoment B raw24739step1 raw24739step1Labels = mixedMoment B raw24739step2 raw24739step2Labels := by
      have ha : raw24739step2 = (fun i j => raw24739step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24739step2 raw24739step1; decide +kernel
      have hl : raw24739step2Labels = raw24739step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24739step1 raw24739step1Labels permutation8 permutation7
    mixedMoment B raw24739step2 raw24739step2Labels = mixedMoment B raw24739step3 raw24739step3Labels := by
      have ha : raw24739step3 = -raw24739step2 := by apply Matrix.ext; change ∀ i j, raw24739step3 i j = -(raw24739step2 i j); unfold raw24739step3 raw24739step2; decide +kernel
      have hl : raw24739step3Labels = raw24739step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24739step3 raw24739step3Labels = mixedMoment B raw24739step4 raw24739step4Labels := by
      have ha : raw24739step4 = raw24739step3 := by apply Matrix.ext; unfold raw24739step4 raw24739step3; decide +kernel
      have hl : raw24739step3Labels = labelEmbedding1 ∘ raw24739step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24739step3 raw24739step3Labels raw24739step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical24740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24740 raw24740Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24740 raw24740Labels = mixedMoment B raw24740step0 raw24740step0Labels := by
      have hz : ∀ j, raw24740 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24740step0 = (fun i j => raw24740 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24740step0 raw24740; decide +kernel
      have hl : raw24740step0Labels = raw24740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24740 raw24740Labels permutation265 hz
    mixedMoment B raw24740step0 raw24740step0Labels = mixedMoment B raw24740step1 raw24740step1Labels := by
      have ha : raw24740step1 = (fun i j => raw24740step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24740step1 raw24740step0; decide +kernel
      have hl : raw24740step1Labels = raw24740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24740step0 raw24740step0Labels permutation34 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical24741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24741 raw24741Labels = mixedMoment B node623 node623Labels := by
  calc
    mixedMoment B raw24741 raw24741Labels = mixedMoment B raw24741step0 raw24741step0Labels := by
      have ha : raw24741step0 = (fun i j => raw24741 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24741step0 raw24741; decide +kernel
      have hl : raw24741step0Labels = raw24741Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24741 raw24741Labels permutation178 permutation2
    _ = mixedMoment B node623 node623Labels := by rfl

theorem canonical24742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24742 raw24742Labels = mixedMoment B node638 node638Labels := by
  calc
    mixedMoment B raw24742 raw24742Labels = mixedMoment B raw24742step0 raw24742step0Labels := by
      have hz : ∀ j, raw24742 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24742step0 = (fun i j => raw24742 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24742step0 raw24742; decide +kernel
      have hl : raw24742step0Labels = raw24742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24742 raw24742Labels permutation265 hz
    mixedMoment B raw24742step0 raw24742step0Labels = mixedMoment B raw24742step1 raw24742step1Labels := by
      have ha : raw24742step1 = (fun i j => raw24742step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24742step1 raw24742step0; decide +kernel
      have hl : raw24742step1Labels = raw24742step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24742step0 raw24742step0Labels permutation34 permutation2
    _ = mixedMoment B node638 node638Labels := by rfl

theorem canonical24743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24743 raw24743Labels = mixedMoment B node627 node627Labels := by
  calc
    mixedMoment B raw24743 raw24743Labels = mixedMoment B raw24743step0 raw24743step0Labels := by
      have hz : ∀ j, raw24743 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24743step0 = (fun i j => raw24743 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24743step0 raw24743; decide +kernel
      have hl : raw24743step0Labels = raw24743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24743 raw24743Labels permutation265 hz
    mixedMoment B raw24743step0 raw24743step0Labels = mixedMoment B raw24743step1 raw24743step1Labels := by
      have ha : raw24743step1 = (fun i j => raw24743step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24743step1 raw24743step0; decide +kernel
      have hl : raw24743step1Labels = raw24743step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24743step0 raw24743step0Labels permutation34 permutation2
    _ = mixedMoment B node627 node627Labels := by rfl

theorem canonical24744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24744 raw24744Labels = mixedMoment B node631 node631Labels := by
  calc
    mixedMoment B raw24744 raw24744Labels = mixedMoment B raw24744step0 raw24744step0Labels := by
      have hz : ∀ j, raw24744 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24744step0 = (fun i j => raw24744 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24744step0 raw24744; decide +kernel
      have hl : raw24744step0Labels = raw24744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24744 raw24744Labels permutation265 hz
    _ = mixedMoment B node631 node631Labels := by rfl

theorem canonical24745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24745 raw24745Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw24745 raw24745Labels = mixedMoment B raw24745step0 raw24745step0Labels := by
      have hz : ∀ j, raw24745 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24745step0 = (fun i j => raw24745 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24745step0 raw24745; decide +kernel
      have hl : raw24745step0Labels = raw24745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24745 raw24745Labels permutation265 hz
    mixedMoment B raw24745step0 raw24745step0Labels = mixedMoment B raw24745step1 raw24745step1Labels := by
      have ha : raw24745step1 = (fun i j => raw24745step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24745step1 raw24745step0; decide +kernel
      have hl : raw24745step1Labels = raw24745step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24745step0 raw24745step0Labels permutation34 permutation2
    _ = mixedMoment B node626 node626Labels := by rfl

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

theorem sound640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node640 node640Labels = Sparse.eval nodeValue640 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 640) = mixedMoment B node640 node640Labels := rfl
  simpa [nodeValue640, Sparse.eval] using hc.symm

theorem sound641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node641 node641Labels = Sparse.eval nodeValue641 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 641) = mixedMoment B node641 node641Labels := rfl
  simpa [nodeValue641, Sparse.eval] using hc.symm

theorem sound642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node642 node642Labels = Sparse.eval nodeValue642 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 642) = mixedMoment B node642 node642Labels := rfl
  simpa [nodeValue642, Sparse.eval] using hc.symm

theorem sound653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node653 node653Labels = Sparse.eval nodeValue653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 653) = mixedMoment B node653 node653Labels := rfl
  simpa [nodeValue653, Sparse.eval] using hc.symm

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

theorem sound1150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1150 node1150Labels = Sparse.eval nodeValue1150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1150) = mixedMoment B node1150 node1150Labels := rfl
  simpa [nodeValue1150, Sparse.eval] using hc.symm

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

theorem sound1152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1152 node1152Labels = Sparse.eval nodeValue1152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1152) = mixedMoment B node1152 node1152Labels := rfl
  simpa [nodeValue1152, Sparse.eval] using hc.symm

theorem sound1158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1158 node1158Labels = Sparse.eval nodeValue1158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1158) = mixedMoment B node1158 node1158Labels := rfl
  simpa [nodeValue1158, Sparse.eval] using hc.symm

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

theorem sound1230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1230 node1230Labels = Sparse.eval nodeValue1230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1230) = mixedMoment B node1230 node1230Labels := rfl
  simpa [nodeValue1230, Sparse.eval] using hc.symm

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

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

theorem sound1287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1287 node1287Labels = Sparse.eval nodeValue1287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1287) = mixedMoment B node1287 node1287Labels := rfl
  simpa [nodeValue1287, Sparse.eval] using hc.symm

theorem sound1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1294 node1294Labels = Sparse.eval nodeValue1294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1294) = mixedMoment B node1294 node1294Labels := rfl
  simpa [nodeValue1294, Sparse.eval] using hc.symm

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

theorem sound1504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1504 node1504Labels = Sparse.eval nodeValue1504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1504) = mixedMoment B node1504 node1504Labels := rfl
  simpa [nodeValue1504, Sparse.eval] using hc.symm

theorem sound1505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1505 node1505Labels = Sparse.eval nodeValue1505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1505) = mixedMoment B node1505 node1505Labels := rfl
  simpa [nodeValue1505, Sparse.eval] using hc.symm

theorem sound1508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1508 node1508Labels = Sparse.eval nodeValue1508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1508) = mixedMoment B node1508 node1508Labels := rfl
  simpa [nodeValue1508, Sparse.eval] using hc.symm

theorem sound1510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1510 node1510Labels = Sparse.eval nodeValue1510 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1510) = mixedMoment B node1510 node1510Labels := rfl
  simpa [nodeValue1510, Sparse.eval] using hc.symm

theorem sound1511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1511 node1511Labels = Sparse.eval nodeValue1511 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1511) = mixedMoment B node1511 node1511Labels := rfl
  simpa [nodeValue1511, Sparse.eval] using hc.symm

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

theorem sound1514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1514 node1514Labels = Sparse.eval nodeValue1514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1514) = mixedMoment B node1514 node1514Labels := rfl
  simpa [nodeValue1514, Sparse.eval] using hc.symm

theorem sound1515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1515 node1515Labels = Sparse.eval nodeValue1515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1515) = mixedMoment B node1515 node1515Labels := rfl
  simpa [nodeValue1515, Sparse.eval] using hc.symm

theorem sound1520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1520 node1520Labels = Sparse.eval nodeValue1520 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1520) = mixedMoment B node1520 node1520Labels := rfl
  simpa [nodeValue1520, Sparse.eval] using hc.symm

theorem sound1522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1522 node1522Labels = Sparse.eval nodeValue1522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1522) = mixedMoment B node1522 node1522Labels := rfl
  simpa [nodeValue1522, Sparse.eval] using hc.symm

theorem sound1526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1526 node1526Labels = Sparse.eval nodeValue1526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1526) = mixedMoment B node1526 node1526Labels := rfl
  simpa [nodeValue1526, Sparse.eval] using hc.symm

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

theorem sound2505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2505 node2505Labels = Sparse.eval nodeValue2505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2505) = mixedMoment B node2505 node2505Labels := rfl
  simpa [nodeValue2505, Sparse.eval] using hc.symm

theorem sound2551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2551 node2551Labels = Sparse.eval nodeValue2551 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2551) = mixedMoment B node2551 node2551Labels := rfl
  simpa [nodeValue2551, Sparse.eval] using hc.symm

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

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

theorem sound2584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2584 node2584Labels = Sparse.eval nodeValue2584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2584) = mixedMoment B node2584 node2584Labels := rfl
  simpa [nodeValue2584, Sparse.eval] using hc.symm

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

theorem sound2657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2657 node2657Labels = Sparse.eval nodeValue2657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2657) = mixedMoment B node2657 node2657Labels := rfl
  simpa [nodeValue2657, Sparse.eval] using hc.symm

theorem sound2683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2683 node2683Labels = Sparse.eval nodeValue2683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2683) = mixedMoment B node2683 node2683Labels := rfl
  simpa [nodeValue2683, Sparse.eval] using hc.symm

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

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

theorem sound2729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2729 node2729Labels = Sparse.eval nodeValue2729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2729) = mixedMoment B node2729 node2729Labels := rfl
  simpa [nodeValue2729, Sparse.eval] using hc.symm

theorem sound2736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2736 node2736Labels = Sparse.eval nodeValue2736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2736) = mixedMoment B node2736 node2736Labels := rfl
  simpa [nodeValue2736, Sparse.eval] using hc.symm

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

theorem sound2761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2761 node2761Labels = Sparse.eval nodeValue2761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2761) = mixedMoment B node2761 node2761Labels := rfl
  simpa [nodeValue2761, Sparse.eval] using hc.symm

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

theorem sound3255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3255 node3255Labels = Sparse.eval nodeValue3255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3255) = mixedMoment B node3255 node3255Labels := rfl
  simpa [nodeValue3255, Sparse.eval] using hc.symm

theorem sound3256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3256 node3256Labels = Sparse.eval nodeValue3256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3256) = mixedMoment B node3256 node3256Labels := rfl
  simpa [nodeValue3256, Sparse.eval] using hc.symm

theorem sound3257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3257 node3257Labels = Sparse.eval nodeValue3257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3257) = mixedMoment B node3257 node3257Labels := rfl
  simpa [nodeValue3257, Sparse.eval] using hc.symm

theorem sound3258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3258 node3258Labels = Sparse.eval nodeValue3258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3258) = mixedMoment B node3258 node3258Labels := rfl
  simpa [nodeValue3258, Sparse.eval] using hc.symm

theorem sound3259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3259 node3259Labels = Sparse.eval nodeValue3259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3259) = mixedMoment B node3259 node3259Labels := rfl
  simpa [nodeValue3259, Sparse.eval] using hc.symm

theorem sound3260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3260 node3260Labels = Sparse.eval nodeValue3260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3260) = mixedMoment B node3260 node3260Labels := rfl
  simpa [nodeValue3260, Sparse.eval] using hc.symm

theorem sound3261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3261 node3261Labels = Sparse.eval nodeValue3261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3261) = mixedMoment B node3261 node3261Labels := rfl
  simpa [nodeValue3261, Sparse.eval] using hc.symm

theorem sound3263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3263 node3263Labels = Sparse.eval nodeValue3263 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3263) = mixedMoment B node3263 node3263Labels := rfl
  simpa [nodeValue3263, Sparse.eval] using hc.symm

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

theorem sound3265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3265 node3265Labels = Sparse.eval nodeValue3265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3265) = mixedMoment B node3265 node3265Labels := rfl
  simpa [nodeValue3265, Sparse.eval] using hc.symm

theorem sound3266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3266 node3266Labels = Sparse.eval nodeValue3266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3266) = mixedMoment B node3266 node3266Labels := rfl
  simpa [nodeValue3266, Sparse.eval] using hc.symm

theorem sound3267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3267 node3267Labels = Sparse.eval nodeValue3267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3267) = mixedMoment B node3267 node3267Labels := rfl
  simpa [nodeValue3267, Sparse.eval] using hc.symm

theorem sound3270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3270 node3270Labels = Sparse.eval nodeValue3270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3270) = mixedMoment B node3270 node3270Labels := rfl
  simpa [nodeValue3270, Sparse.eval] using hc.symm

theorem sound3271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3271 node3271Labels = Sparse.eval nodeValue3271 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3271) = mixedMoment B node3271 node3271Labels := rfl
  simpa [nodeValue3271, Sparse.eval] using hc.symm

theorem sound3273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3273 node3273Labels = Sparse.eval nodeValue3273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3273) = mixedMoment B node3273 node3273Labels := rfl
  simpa [nodeValue3273, Sparse.eval] using hc.symm

theorem sound3274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3274 node3274Labels = Sparse.eval nodeValue3274 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3274) = mixedMoment B node3274 node3274Labels := rfl
  simpa [nodeValue3274, Sparse.eval] using hc.symm

theorem sound3288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3288 node3288Labels = Sparse.eval nodeValue3288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3288) = mixedMoment B node3288 node3288Labels := rfl
  simpa [nodeValue3288, Sparse.eval] using hc.symm

theorem sound3289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3289 node3289Labels = Sparse.eval nodeValue3289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3289) = mixedMoment B node3289 node3289Labels := rfl
  simpa [nodeValue3289, Sparse.eval] using hc.symm

theorem sound3290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3290 node3290Labels = Sparse.eval nodeValue3290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3290) = mixedMoment B node3290 node3290Labels := rfl
  simpa [nodeValue3290, Sparse.eval] using hc.symm

theorem sound3291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3291 node3291Labels = Sparse.eval nodeValue3291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3291) = mixedMoment B node3291 node3291Labels := rfl
  simpa [nodeValue3291, Sparse.eval] using hc.symm

theorem sound3292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3292 node3292Labels = Sparse.eval nodeValue3292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3292) = mixedMoment B node3292 node3292Labels := rfl
  simpa [nodeValue3292, Sparse.eval] using hc.symm

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

theorem sound3294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3294 node3294Labels = Sparse.eval nodeValue3294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3294) = mixedMoment B node3294 node3294Labels := rfl
  simpa [nodeValue3294, Sparse.eval] using hc.symm

theorem sound3295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3295 node3295Labels = Sparse.eval nodeValue3295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3295) = mixedMoment B node3295 node3295Labels := rfl
  simpa [nodeValue3295, Sparse.eval] using hc.symm

theorem sound3296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3296 node3296Labels = Sparse.eval nodeValue3296 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3296) = mixedMoment B node3296 node3296Labels := rfl
  simpa [nodeValue3296, Sparse.eval] using hc.symm

theorem sound3297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3297 node3297Labels = Sparse.eval nodeValue3297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3297) = mixedMoment B node3297 node3297Labels := rfl
  simpa [nodeValue3297, Sparse.eval] using hc.symm

theorem sound3299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3299 node3299Labels = Sparse.eval nodeValue3299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3299) = mixedMoment B node3299 node3299Labels := rfl
  simpa [nodeValue3299, Sparse.eval] using hc.symm

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

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

theorem sound3303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3303 node3303Labels = Sparse.eval nodeValue3303 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3303) = mixedMoment B node3303 node3303Labels := rfl
  simpa [nodeValue3303, Sparse.eval] using hc.symm

theorem sound3304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3304 node3304Labels = Sparse.eval nodeValue3304 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3304) = mixedMoment B node3304 node3304Labels := rfl
  simpa [nodeValue3304, Sparse.eval] using hc.symm

theorem sound3305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3305 node3305Labels = Sparse.eval nodeValue3305 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3305) = mixedMoment B node3305 node3305Labels := rfl
  simpa [nodeValue3305, Sparse.eval] using hc.symm

theorem sound3306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3306 node3306Labels = Sparse.eval nodeValue3306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3306) = mixedMoment B node3306 node3306Labels := rfl
  simpa [nodeValue3306, Sparse.eval] using hc.symm

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

theorem sound3470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3470 node3470Labels = Sparse.eval nodeValue3470 (mixedVector B) := by
  simpa only [nodeValue3470, Sparse.eval_nil] using zero3470 B _hB _hF

theorem sound3483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3483 node3483Labels = Sparse.eval nodeValue3483 (mixedVector B) := by
  simpa only [nodeValue3483, Sparse.eval_nil] using zero3483 B _hB _hF

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

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

theorem sound3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3521 node3521Labels = Sparse.eval nodeValue3521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3521) = mixedMoment B node3521 node3521Labels := rfl
  simpa [nodeValue3521, Sparse.eval] using hc.symm

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = Sparse.eval nodeValue3546 (mixedVector B) := by
  simpa only [nodeValue3546, Sparse.eval_nil] using zero3546 B _hB _hF

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

theorem sound3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3564 node3564Labels = Sparse.eval nodeValue3564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3564) = mixedMoment B node3564 node3564Labels := rfl
  simpa [nodeValue3564, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

theorem sound3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3583 node3583Labels = Sparse.eval nodeValue3583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3583) = mixedMoment B node3583 node3583Labels := rfl
  simpa [nodeValue3583, Sparse.eval] using hc.symm

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

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node623 node623Labels = Sparse.eval nodeValue623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 623) = mixedMoment B node623 node623Labels := rfl
  simpa [nodeValue623, Sparse.eval] using hc.symm

theorem sound625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node625 node625Labels = Sparse.eval nodeValue625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 625) = mixedMoment B node625 node625Labels := rfl
  simpa [nodeValue625, Sparse.eval] using hc.symm

theorem sound626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node626 node626Labels = Sparse.eval nodeValue626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 626) = mixedMoment B node626 node626Labels := rfl
  simpa [nodeValue626, Sparse.eval] using hc.symm

theorem sound627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node627 node627Labels = Sparse.eval nodeValue627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 627) = mixedMoment B node627 node627Labels := rfl
  simpa [nodeValue627, Sparse.eval] using hc.symm

theorem sound630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node630 node630Labels = Sparse.eval nodeValue630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 630) = mixedMoment B node630 node630Labels := rfl
  simpa [nodeValue630, Sparse.eval] using hc.symm

theorem sound631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node631 node631Labels = Sparse.eval nodeValue631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 631) = mixedMoment B node631 node631Labels := rfl
  simpa [nodeValue631, Sparse.eval] using hc.symm

theorem sound632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node632 node632Labels = Sparse.eval nodeValue632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 632) = mixedMoment B node632 node632Labels := rfl
  simpa [nodeValue632, Sparse.eval] using hc.symm

theorem sound638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node638 node638Labels = Sparse.eval nodeValue638 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 638) = mixedMoment B node638 node638Labels := rfl
  simpa [nodeValue638, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources51
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1663 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1663 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1663 + difference 0 1) (sourceB1663 + difference 1 0) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA1663 + difference 0 1) (sourceB1663 + difference 1 0) sourceC1663) = raw24364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24364; decide +kernel
    rw [ha]
    exact (canonical24364 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1663 + difference 0 2) (sourceB1663 + difference 2 0) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA1663 + difference 0 2) (sourceB1663 + difference 2 0) sourceC1663) = raw24365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24365; decide +kernel
    rw [ha]
    exact (canonical24365 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1663 + difference 0 3) (sourceB1663 + difference 3 0) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA1663 + difference 0 3) (sourceB1663 + difference 3 0) sourceC1663) = raw24366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24366; decide +kernel
    rw [ha]
    exact (canonical24366 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1663 + difference 0 4) (sourceB1663 + difference 4 0) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA1663 + difference 0 4) (sourceB1663 + difference 4 0) sourceC1663) = raw24367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24367; decide +kernel
    rw [ha]
    exact (canonical24367 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1663 + difference 0 5) (sourceB1663 + difference 5 0) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA1663 + difference 0 5) (sourceB1663 + difference 5 0) sourceC1663) = raw24368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24368; decide +kernel
    rw [ha]
    exact (canonical24368 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1663 + difference 1 0) (sourceB1663 + difference 0 1) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1663 + difference 1 0) (sourceB1663 + difference 0 1) sourceC1663) = raw24369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24369; decide +kernel
    rw [ha]
    exact (canonical24369 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1663 + difference 1 2) (sourceB1663 + difference 2 1) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3259) := by
    have ha : (tripleCharges (sourceA1663 + difference 1 2) (sourceB1663 + difference 2 1) sourceC1663) = raw24370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24370; decide +kernel
    rw [ha]
    exact (canonical24370 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1663 + difference 1 3) (sourceB1663 + difference 3 1) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1663 + difference 1 3) (sourceB1663 + difference 3 1) sourceC1663) = raw24371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24371; decide +kernel
    rw [ha]
    exact (canonical24371 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1663 + difference 1 4) (sourceB1663 + difference 4 1) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1663 + difference 1 4) (sourceB1663 + difference 4 1) sourceC1663) = raw24372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24372; decide +kernel
    rw [ha]
    exact (canonical24372 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1663 + difference 1 5) (sourceB1663 + difference 5 1) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1663 + difference 1 5) (sourceB1663 + difference 5 1) sourceC1663) = raw24373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24373; decide +kernel
    rw [ha]
    exact (canonical24373 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1663 + difference 2 0) (sourceB1663 + difference 0 2) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1663 + difference 2 0) (sourceB1663 + difference 0 2) sourceC1663) = raw24374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24374; decide +kernel
    rw [ha]
    exact (canonical24374 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1663 + difference 2 1) (sourceB1663 + difference 1 2) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3259) := by
    have ha : (tripleCharges (sourceA1663 + difference 2 1) (sourceB1663 + difference 1 2) sourceC1663) = raw24375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24375; decide +kernel
    rw [ha]
    exact (canonical24375 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1663 + difference 2 3) (sourceB1663 + difference 3 2) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1663 + difference 2 3) (sourceB1663 + difference 3 2) sourceC1663) = raw24376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24376; decide +kernel
    rw [ha]
    exact (canonical24376 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1663 + difference 2 4) (sourceB1663 + difference 4 2) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1663 + difference 2 4) (sourceB1663 + difference 4 2) sourceC1663) = raw24377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24377; decide +kernel
    rw [ha]
    exact (canonical24377 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1663 + difference 2 5) (sourceB1663 + difference 5 2) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1663 + difference 2 5) (sourceB1663 + difference 5 2) sourceC1663) = raw24378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24378; decide +kernel
    rw [ha]
    exact (canonical24378 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1663 + difference 3 0) (sourceB1663 + difference 0 3) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1526) := by
    have ha : (tripleCharges (sourceA1663 + difference 3 0) (sourceB1663 + difference 0 3) sourceC1663) = raw24379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24379; decide +kernel
    rw [ha]
    exact (canonical24379 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1663 + difference 3 1) (sourceB1663 + difference 1 3) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3271) := by
    have ha : (tripleCharges (sourceA1663 + difference 3 1) (sourceB1663 + difference 1 3) sourceC1663) = raw24380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24380; decide +kernel
    rw [ha]
    exact (canonical24380 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1663 + difference 3 2) (sourceB1663 + difference 2 3) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3271) := by
    have ha : (tripleCharges (sourceA1663 + difference 3 2) (sourceB1663 + difference 2 3) sourceC1663) = raw24381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24381; decide +kernel
    rw [ha]
    exact (canonical24381 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1663 + difference 3 4) (sourceB1663 + difference 4 3) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1663 + difference 3 4) (sourceB1663 + difference 4 3) sourceC1663) = raw24382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24382; decide +kernel
    rw [ha]
    exact (canonical24382 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1663 + difference 3 5) (sourceB1663 + difference 5 3) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA1663 + difference 3 5) (sourceB1663 + difference 5 3) sourceC1663) = raw24383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24383; decide +kernel
    rw [ha]
    exact (canonical24383 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1663 + difference 4 0) (sourceB1663 + difference 0 4) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA1663 + difference 4 0) (sourceB1663 + difference 0 4) sourceC1663) = raw24384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24384; decide +kernel
    rw [ha]
    exact (canonical24384 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1663 + difference 4 1) (sourceB1663 + difference 1 4) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA1663 + difference 4 1) (sourceB1663 + difference 1 4) sourceC1663) = raw24385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24385; decide +kernel
    rw [ha]
    exact (canonical24385 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1663 + difference 4 2) (sourceB1663 + difference 2 4) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA1663 + difference 4 2) (sourceB1663 + difference 2 4) sourceC1663) = raw24386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24386; decide +kernel
    rw [ha]
    exact (canonical24386 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1663 + difference 4 3) (sourceB1663 + difference 3 4) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1663 + difference 4 3) (sourceB1663 + difference 3 4) sourceC1663) = raw24387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24387; decide +kernel
    rw [ha]
    exact (canonical24387 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1663 + difference 4 5) (sourceB1663 + difference 5 4) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1663 + difference 4 5) (sourceB1663 + difference 5 4) sourceC1663) = raw24388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24388; decide +kernel
    rw [ha]
    exact (canonical24388 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1663 + difference 5 0) (sourceB1663 + difference 0 5) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA1663 + difference 5 0) (sourceB1663 + difference 0 5) sourceC1663) = raw24389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24389; decide +kernel
    rw [ha]
    exact (canonical24389 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1663 + difference 5 1) (sourceB1663 + difference 1 5) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA1663 + difference 5 1) (sourceB1663 + difference 1 5) sourceC1663) = raw24390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24390; decide +kernel
    rw [ha]
    exact (canonical24390 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1663 + difference 5 2) (sourceB1663 + difference 2 5) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA1663 + difference 5 2) (sourceB1663 + difference 2 5) sourceC1663) = raw24391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24391; decide +kernel
    rw [ha]
    exact (canonical24391 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1663 + difference 5 3) (sourceB1663 + difference 3 5) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1663 + difference 5 3) (sourceB1663 + difference 3 5) sourceC1663) = raw24392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24392; decide +kernel
    rw [ha]
    exact (canonical24392 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1663 + difference 5 4) (sourceB1663 + difference 4 5) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1663 + difference 5 4) (sourceB1663 + difference 4 5) sourceC1663) = raw24393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24393; decide +kernel
    rw [ha]
    exact (canonical24393 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1663 sourceB1663 sourceC1663
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1663, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources52
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1664 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1664 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1664 + difference 0 0) (sourceB1664 + difference 0 0) sourceC1664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1664 + difference 0 0) (sourceB1664 + difference 0 0) sourceC1664) = raw24394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1664 sourceB1664 sourceC1664 difference raw24394; decide +kernel
    rw [ha]
    exact (canonical24394 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1664 + difference 1 0) (sourceB1664 + difference 0 1) sourceC1664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 638) := by
    have ha : (tripleCharges (sourceA1664 + difference 1 0) (sourceB1664 + difference 0 1) sourceC1664) = raw24395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1664 sourceB1664 sourceC1664 difference raw24395; decide +kernel
    rw [ha]
    exact (canonical24395 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1664 + difference 2 0) (sourceB1664 + difference 0 2) sourceC1664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 638) := by
    have ha : (tripleCharges (sourceA1664 + difference 2 0) (sourceB1664 + difference 0 2) sourceC1664) = raw24396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1664 sourceB1664 sourceC1664 difference raw24396; decide +kernel
    rw [ha]
    exact (canonical24396 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1664 + difference 3 0) (sourceB1664 + difference 0 3) sourceC1664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 642) := by
    have ha : (tripleCharges (sourceA1664 + difference 3 0) (sourceB1664 + difference 0 3) sourceC1664) = raw24397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1664 sourceB1664 sourceC1664 difference raw24397; decide +kernel
    rw [ha]
    exact (canonical24397 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1664 + difference 4 0) (sourceB1664 + difference 0 4) sourceC1664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 653) := by
    have ha : (tripleCharges (sourceA1664 + difference 4 0) (sourceB1664 + difference 0 4) sourceC1664) = raw24398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1664 sourceB1664 sourceC1664 difference raw24398; decide +kernel
    rw [ha]
    exact (canonical24398 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1664 + difference 5 0) (sourceB1664 + difference 0 5) sourceC1664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 641) := by
    have ha : (tripleCharges (sourceA1664 + difference 5 0) (sourceB1664 + difference 0 5) sourceC1664) = raw24399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1664 sourceB1664 sourceC1664 difference raw24399; decide +kernel
    rw [ha]
    exact (canonical24399 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1664 + sourceB1664) sourceC1664) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1664 + sourceB1664) sourceC1664) = raw24400 := by
      apply Matrix.ext; unfold doubleCharges sourceA1664 sourceB1664 sourceC1664 raw24400; decide +kernel
    rw [ha]
    exact (canonical24400 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1664 sourceB1664 sourceC1664
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1664, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1667 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1667 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1667 + difference 0 0) (sourceB1667 + difference 0 0) sourceC1667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1287) := by
    have ha : (tripleCharges (sourceA1667 + difference 0 0) (sourceB1667 + difference 0 0) sourceC1667) = raw24451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1667 sourceB1667 sourceC1667 difference raw24451; decide +kernel
    rw [ha]
    exact (canonical24451 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1667 + difference 0 1) (sourceB1667 + difference 1 0) sourceC1667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2584) := by
    have ha : (tripleCharges (sourceA1667 + difference 0 1) (sourceB1667 + difference 1 0) sourceC1667) = raw24452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1667 sourceB1667 sourceC1667 difference raw24452; decide +kernel
    rw [ha]
    exact (canonical24452 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1667 + difference 0 2) (sourceB1667 + difference 2 0) sourceC1667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2584) := by
    have ha : (tripleCharges (sourceA1667 + difference 0 2) (sourceB1667 + difference 2 0) sourceC1667) = raw24453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1667 sourceB1667 sourceC1667 difference raw24453; decide +kernel
    rw [ha]
    exact (canonical24453 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1667 + difference 0 3) (sourceB1667 + difference 3 0) sourceC1667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA1667 + difference 0 3) (sourceB1667 + difference 3 0) sourceC1667) = raw24454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1667 sourceB1667 sourceC1667 difference raw24454; decide +kernel
    rw [ha]
    exact (canonical24454 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1667 + difference 0 4) (sourceB1667 + difference 4 0) sourceC1667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA1667 + difference 0 4) (sourceB1667 + difference 4 0) sourceC1667) = raw24455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1667 sourceB1667 sourceC1667 difference raw24455; decide +kernel
    rw [ha]
    exact (canonical24455 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1667 + difference 0 5) (sourceB1667 + difference 5 0) sourceC1667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA1667 + difference 0 5) (sourceB1667 + difference 5 0) sourceC1667) = raw24456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1667 sourceB1667 sourceC1667 difference raw24456; decide +kernel
    rw [ha]
    exact (canonical24456 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1667 + sourceB1667) sourceC1667) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1667 + sourceB1667) sourceC1667) = raw24457 := by
      apply Matrix.ext; unfold doubleCharges sourceA1667 sourceB1667 sourceC1667 raw24457; decide +kernel
    rw [ha]
    exact (canonical24457 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1667 sourceB1667 sourceC1667
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1667, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1668 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1668 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1668 + difference 0 0) (sourceB1668 + difference 0 0) sourceC1668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1230) := by
    have ha : (tripleCharges (sourceA1668 + difference 0 0) (sourceB1668 + difference 0 0) sourceC1668) = raw24458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1668 sourceB1668 sourceC1668 difference raw24458; decide +kernel
    rw [ha]
    exact (canonical24458 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1668 + difference 0 1) (sourceB1668 + difference 1 0) sourceC1668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2551) := by
    have ha : (tripleCharges (sourceA1668 + difference 0 1) (sourceB1668 + difference 1 0) sourceC1668) = raw24459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1668 sourceB1668 sourceC1668 difference raw24459; decide +kernel
    rw [ha]
    exact (canonical24459 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1668 + difference 0 2) (sourceB1668 + difference 2 0) sourceC1668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA1668 + difference 0 2) (sourceB1668 + difference 2 0) sourceC1668) = raw24460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1668 sourceB1668 sourceC1668 difference raw24460; decide +kernel
    rw [ha]
    exact (canonical24460 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1668 + difference 0 3) (sourceB1668 + difference 3 0) sourceC1668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA1668 + difference 0 3) (sourceB1668 + difference 3 0) sourceC1668) = raw24461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1668 sourceB1668 sourceC1668 difference raw24461; decide +kernel
    rw [ha]
    exact (canonical24461 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1668 + difference 0 4) (sourceB1668 + difference 4 0) sourceC1668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA1668 + difference 0 4) (sourceB1668 + difference 4 0) sourceC1668) = raw24462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1668 sourceB1668 sourceC1668 difference raw24462; decide +kernel
    rw [ha]
    exact (canonical24462 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1668 + difference 0 5) (sourceB1668 + difference 5 0) sourceC1668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA1668 + difference 0 5) (sourceB1668 + difference 5 0) sourceC1668) = raw24463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1668 sourceB1668 sourceC1668 difference raw24463; decide +kernel
    rw [ha]
    exact (canonical24463 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1668 + sourceB1668) sourceC1668) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1668 + sourceB1668) sourceC1668) = raw24464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1668 sourceB1668 sourceC1668 raw24464; decide +kernel
    rw [ha]
    exact (canonical24464 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1668 sourceB1668 sourceC1668
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1668, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1671 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1671 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1671 + difference 0 1) (sourceB1671 + difference 1 0) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA1671 + difference 0 1) (sourceB1671 + difference 1 0) sourceC1671) = raw24516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24516; decide +kernel
    rw [ha]
    exact (canonical24516 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1671 + difference 0 2) (sourceB1671 + difference 2 0) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA1671 + difference 0 2) (sourceB1671 + difference 2 0) sourceC1671) = raw24517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24517; decide +kernel
    rw [ha]
    exact (canonical24517 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1671 + difference 0 3) (sourceB1671 + difference 3 0) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA1671 + difference 0 3) (sourceB1671 + difference 3 0) sourceC1671) = raw24518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24518; decide +kernel
    rw [ha]
    exact (canonical24518 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1671 + difference 0 4) (sourceB1671 + difference 4 0) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA1671 + difference 0 4) (sourceB1671 + difference 4 0) sourceC1671) = raw24519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24519; decide +kernel
    rw [ha]
    exact (canonical24519 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1671 + difference 0 5) (sourceB1671 + difference 5 0) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA1671 + difference 0 5) (sourceB1671 + difference 5 0) sourceC1671) = raw24520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24520; decide +kernel
    rw [ha]
    exact (canonical24520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1671 + difference 1 0) (sourceB1671 + difference 0 1) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1671 + difference 1 0) (sourceB1671 + difference 0 1) sourceC1671) = raw24521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24521; decide +kernel
    rw [ha]
    exact (canonical24521 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1671 + difference 1 2) (sourceB1671 + difference 2 1) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3263) := by
    have ha : (tripleCharges (sourceA1671 + difference 1 2) (sourceB1671 + difference 2 1) sourceC1671) = raw24522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24522; decide +kernel
    rw [ha]
    exact (canonical24522 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1671 + difference 1 3) (sourceB1671 + difference 3 1) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1671 + difference 1 3) (sourceB1671 + difference 3 1) sourceC1671) = raw24523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24523; decide +kernel
    rw [ha]
    exact (canonical24523 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1671 + difference 1 4) (sourceB1671 + difference 4 1) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1671 + difference 1 4) (sourceB1671 + difference 4 1) sourceC1671) = raw24524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24524; decide +kernel
    rw [ha]
    exact (canonical24524 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1671 + difference 1 5) (sourceB1671 + difference 5 1) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1671 + difference 1 5) (sourceB1671 + difference 5 1) sourceC1671) = raw24525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24525; decide +kernel
    rw [ha]
    exact (canonical24525 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1671 + difference 2 0) (sourceB1671 + difference 0 2) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1671 + difference 2 0) (sourceB1671 + difference 0 2) sourceC1671) = raw24526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24526; decide +kernel
    rw [ha]
    exact (canonical24526 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1671 + difference 2 1) (sourceB1671 + difference 1 2) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA1671 + difference 2 1) (sourceB1671 + difference 1 2) sourceC1671) = raw24527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24527; decide +kernel
    rw [ha]
    exact (canonical24527 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1671 + difference 2 3) (sourceB1671 + difference 3 2) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1671 + difference 2 3) (sourceB1671 + difference 3 2) sourceC1671) = raw24528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24528; decide +kernel
    rw [ha]
    exact (canonical24528 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1671 + difference 2 4) (sourceB1671 + difference 4 2) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1671 + difference 2 4) (sourceB1671 + difference 4 2) sourceC1671) = raw24529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24529; decide +kernel
    rw [ha]
    exact (canonical24529 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1671 + difference 2 5) (sourceB1671 + difference 5 2) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1671 + difference 2 5) (sourceB1671 + difference 5 2) sourceC1671) = raw24530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24530; decide +kernel
    rw [ha]
    exact (canonical24530 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1671 + difference 3 0) (sourceB1671 + difference 0 3) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA1671 + difference 3 0) (sourceB1671 + difference 0 3) sourceC1671) = raw24531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24531; decide +kernel
    rw [ha]
    exact (canonical24531 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1671 + difference 3 1) (sourceB1671 + difference 1 3) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA1671 + difference 3 1) (sourceB1671 + difference 1 3) sourceC1671) = raw24532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24532; decide +kernel
    rw [ha]
    exact (canonical24532 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1671 + difference 3 2) (sourceB1671 + difference 2 3) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3274) := by
    have ha : (tripleCharges (sourceA1671 + difference 3 2) (sourceB1671 + difference 2 3) sourceC1671) = raw24533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24533; decide +kernel
    rw [ha]
    exact (canonical24533 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1671 + difference 3 4) (sourceB1671 + difference 4 3) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA1671 + difference 3 4) (sourceB1671 + difference 4 3) sourceC1671) = raw24534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24534; decide +kernel
    rw [ha]
    exact (canonical24534 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1671 + difference 3 5) (sourceB1671 + difference 5 3) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1671 + difference 3 5) (sourceB1671 + difference 5 3) sourceC1671) = raw24535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24535; decide +kernel
    rw [ha]
    exact (canonical24535 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1671 + difference 4 0) (sourceB1671 + difference 0 4) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA1671 + difference 4 0) (sourceB1671 + difference 0 4) sourceC1671) = raw24536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24536; decide +kernel
    rw [ha]
    exact (canonical24536 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1671 + difference 4 1) (sourceB1671 + difference 1 4) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA1671 + difference 4 1) (sourceB1671 + difference 1 4) sourceC1671) = raw24537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24537; decide +kernel
    rw [ha]
    exact (canonical24537 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1671 + difference 4 2) (sourceB1671 + difference 2 4) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3274) := by
    have ha : (tripleCharges (sourceA1671 + difference 4 2) (sourceB1671 + difference 2 4) sourceC1671) = raw24538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24538; decide +kernel
    rw [ha]
    exact (canonical24538 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1671 + difference 4 3) (sourceB1671 + difference 3 4) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA1671 + difference 4 3) (sourceB1671 + difference 3 4) sourceC1671) = raw24539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24539; decide +kernel
    rw [ha]
    exact (canonical24539 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1671 + difference 4 5) (sourceB1671 + difference 5 4) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1671 + difference 4 5) (sourceB1671 + difference 5 4) sourceC1671) = raw24540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24540; decide +kernel
    rw [ha]
    exact (canonical24540 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1671 + difference 5 0) (sourceB1671 + difference 0 5) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1505) := by
    have ha : (tripleCharges (sourceA1671 + difference 5 0) (sourceB1671 + difference 0 5) sourceC1671) = raw24541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24541; decide +kernel
    rw [ha]
    exact (canonical24541 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1671 + difference 5 1) (sourceB1671 + difference 1 5) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3255) := by
    have ha : (tripleCharges (sourceA1671 + difference 5 1) (sourceB1671 + difference 1 5) sourceC1671) = raw24542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24542; decide +kernel
    rw [ha]
    exact (canonical24542 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1671 + difference 5 2) (sourceB1671 + difference 2 5) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3273) := by
    have ha : (tripleCharges (sourceA1671 + difference 5 2) (sourceB1671 + difference 2 5) sourceC1671) = raw24543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24543; decide +kernel
    rw [ha]
    exact (canonical24543 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1671 + difference 5 3) (sourceB1671 + difference 3 5) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1671 + difference 5 3) (sourceB1671 + difference 3 5) sourceC1671) = raw24544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24544; decide +kernel
    rw [ha]
    exact (canonical24544 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1671 + difference 5 4) (sourceB1671 + difference 4 5) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1671 + difference 5 4) (sourceB1671 + difference 4 5) sourceC1671) = raw24545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24545; decide +kernel
    rw [ha]
    exact (canonical24545 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1671 sourceB1671 sourceC1671
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1671, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1672 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1672 + difference 0 0) (sourceB1672 + difference 0 0) sourceC1672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1672 + difference 0 0) (sourceB1672 + difference 0 0) sourceC1672) = raw24546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1672 sourceB1672 sourceC1672 difference raw24546; decide +kernel
    rw [ha]
    exact (canonical24546 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1672 + difference 1 0) (sourceB1672 + difference 0 1) sourceC1672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 625) := by
    have ha : (tripleCharges (sourceA1672 + difference 1 0) (sourceB1672 + difference 0 1) sourceC1672) = raw24547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1672 sourceB1672 sourceC1672 difference raw24547; decide +kernel
    rw [ha]
    exact (canonical24547 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1672 + difference 2 0) (sourceB1672 + difference 0 2) sourceC1672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 640) := by
    have ha : (tripleCharges (sourceA1672 + difference 2 0) (sourceB1672 + difference 0 2) sourceC1672) = raw24548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1672 sourceB1672 sourceC1672 difference raw24548; decide +kernel
    rw [ha]
    exact (canonical24548 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1672 + difference 3 0) (sourceB1672 + difference 0 3) sourceC1672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 632) := by
    have ha : (tripleCharges (sourceA1672 + difference 3 0) (sourceB1672 + difference 0 3) sourceC1672) = raw24549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1672 sourceB1672 sourceC1672 difference raw24549; decide +kernel
    rw [ha]
    exact (canonical24549 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1672 + difference 4 0) (sourceB1672 + difference 0 4) sourceC1672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 632) := by
    have ha : (tripleCharges (sourceA1672 + difference 4 0) (sourceB1672 + difference 0 4) sourceC1672) = raw24550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1672 sourceB1672 sourceC1672 difference raw24550; decide +kernel
    rw [ha]
    exact (canonical24550 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1672 + difference 5 0) (sourceB1672 + difference 0 5) sourceC1672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 630) := by
    have ha : (tripleCharges (sourceA1672 + difference 5 0) (sourceB1672 + difference 0 5) sourceC1672) = raw24551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1672 sourceB1672 sourceC1672 difference raw24551; decide +kernel
    rw [ha]
    exact (canonical24551 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1672 + sourceB1672) sourceC1672) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1672 + sourceB1672) sourceC1672) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA1672 sourceB1672 sourceC1672 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1672 sourceB1672 sourceC1672
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1672, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1673 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1673 + difference 0 1) (sourceB1673 + difference 1 0) sourceC1673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA1673 + difference 0 1) (sourceB1673 + difference 1 0) sourceC1673) = raw24553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1673 sourceB1673 sourceC1673 difference raw24553; decide +kernel
    rw [ha]
    exact (canonical24553 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1673 + difference 1 1) (sourceB1673 + difference 1 1) sourceC1673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1673 + difference 1 1) (sourceB1673 + difference 1 1) sourceC1673) = raw24546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1673 sourceB1673 sourceC1673 difference raw24546; decide +kernel
    rw [ha]
    exact (canonical24546 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1673 + difference 2 1) (sourceB1673 + difference 1 2) sourceC1673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1158) := by
    have ha : (tripleCharges (sourceA1673 + difference 2 1) (sourceB1673 + difference 1 2) sourceC1673) = raw24554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1673 sourceB1673 sourceC1673 difference raw24554; decide +kernel
    rw [ha]
    exact (canonical24554 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1673 + difference 3 1) (sourceB1673 + difference 1 3) sourceC1673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1152) := by
    have ha : (tripleCharges (sourceA1673 + difference 3 1) (sourceB1673 + difference 1 3) sourceC1673) = raw24555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1673 sourceB1673 sourceC1673 difference raw24555; decide +kernel
    rw [ha]
    exact (canonical24555 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1673 + difference 4 1) (sourceB1673 + difference 1 4) sourceC1673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1152) := by
    have ha : (tripleCharges (sourceA1673 + difference 4 1) (sourceB1673 + difference 1 4) sourceC1673) = raw24556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1673 sourceB1673 sourceC1673 difference raw24556; decide +kernel
    rw [ha]
    exact (canonical24556 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1673 + difference 5 1) (sourceB1673 + difference 1 5) sourceC1673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1150) := by
    have ha : (tripleCharges (sourceA1673 + difference 5 1) (sourceB1673 + difference 1 5) sourceC1673) = raw24557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1673 sourceB1673 sourceC1673 difference raw24557; decide +kernel
    rw [ha]
    exact (canonical24557 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1673 + sourceB1673) sourceC1673) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1673 + sourceB1673) sourceC1673) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA1673 sourceB1673 sourceC1673 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1673 sourceB1673 sourceC1673
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1673, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1680 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1680 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1680 + difference 0 1) (sourceB1680 + difference 1 0) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA1680 + difference 0 1) (sourceB1680 + difference 1 0) sourceC1680) = raw24710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24710; decide +kernel
    rw [ha]
    exact (canonical24710 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1680 + difference 0 2) (sourceB1680 + difference 2 0) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA1680 + difference 0 2) (sourceB1680 + difference 2 0) sourceC1680) = raw24711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24711; decide +kernel
    rw [ha]
    exact (canonical24711 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1680 + difference 0 3) (sourceB1680 + difference 3 0) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA1680 + difference 0 3) (sourceB1680 + difference 3 0) sourceC1680) = raw24712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24712; decide +kernel
    rw [ha]
    exact (canonical24712 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1680 + difference 0 4) (sourceB1680 + difference 4 0) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA1680 + difference 0 4) (sourceB1680 + difference 4 0) sourceC1680) = raw24713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24713; decide +kernel
    rw [ha]
    exact (canonical24713 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1680 + difference 0 5) (sourceB1680 + difference 5 0) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA1680 + difference 0 5) (sourceB1680 + difference 5 0) sourceC1680) = raw24714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24714; decide +kernel
    rw [ha]
    exact (canonical24714 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1680 + difference 1 0) (sourceB1680 + difference 0 1) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1510) := by
    have ha : (tripleCharges (sourceA1680 + difference 1 0) (sourceB1680 + difference 0 1) sourceC1680) = raw24715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24715; decide +kernel
    rw [ha]
    exact (canonical24715 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1680 + difference 1 2) (sourceB1680 + difference 2 1) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3256) := by
    have ha : (tripleCharges (sourceA1680 + difference 1 2) (sourceB1680 + difference 2 1) sourceC1680) = raw24716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24716; decide +kernel
    rw [ha]
    exact (canonical24716 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1680 + difference 1 3) (sourceB1680 + difference 3 1) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1680 + difference 1 3) (sourceB1680 + difference 3 1) sourceC1680) = raw24717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24717; decide +kernel
    rw [ha]
    exact (canonical24717 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1680 + difference 1 4) (sourceB1680 + difference 4 1) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1680 + difference 1 4) (sourceB1680 + difference 4 1) sourceC1680) = raw24718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24718; decide +kernel
    rw [ha]
    exact (canonical24718 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1680 + difference 1 5) (sourceB1680 + difference 5 1) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1680 + difference 1 5) (sourceB1680 + difference 5 1) sourceC1680) = raw24719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24719; decide +kernel
    rw [ha]
    exact (canonical24719 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1680 + difference 2 0) (sourceB1680 + difference 0 2) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1680 + difference 2 0) (sourceB1680 + difference 0 2) sourceC1680) = raw24720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24720; decide +kernel
    rw [ha]
    exact (canonical24720 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1680 + difference 2 1) (sourceB1680 + difference 1 2) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3259) := by
    have ha : (tripleCharges (sourceA1680 + difference 2 1) (sourceB1680 + difference 1 2) sourceC1680) = raw24721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24721; decide +kernel
    rw [ha]
    exact (canonical24721 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1680 + difference 2 3) (sourceB1680 + difference 3 2) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1680 + difference 2 3) (sourceB1680 + difference 3 2) sourceC1680) = raw24722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24722; decide +kernel
    rw [ha]
    exact (canonical24722 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1680 + difference 2 4) (sourceB1680 + difference 4 2) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1680 + difference 2 4) (sourceB1680 + difference 4 2) sourceC1680) = raw24723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24723; decide +kernel
    rw [ha]
    exact (canonical24723 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1680 + difference 2 5) (sourceB1680 + difference 5 2) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1680 + difference 2 5) (sourceB1680 + difference 5 2) sourceC1680) = raw24724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24724; decide +kernel
    rw [ha]
    exact (canonical24724 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1680 + difference 3 0) (sourceB1680 + difference 0 3) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA1680 + difference 3 0) (sourceB1680 + difference 0 3) sourceC1680) = raw24725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24725; decide +kernel
    rw [ha]
    exact (canonical24725 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1680 + difference 3 1) (sourceB1680 + difference 1 3) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3267) := by
    have ha : (tripleCharges (sourceA1680 + difference 3 1) (sourceB1680 + difference 1 3) sourceC1680) = raw24726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24726; decide +kernel
    rw [ha]
    exact (canonical24726 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1680 + difference 3 2) (sourceB1680 + difference 2 3) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA1680 + difference 3 2) (sourceB1680 + difference 2 3) sourceC1680) = raw24727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24727; decide +kernel
    rw [ha]
    exact (canonical24727 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1680 + difference 3 4) (sourceB1680 + difference 4 3) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1680 + difference 3 4) (sourceB1680 + difference 4 3) sourceC1680) = raw24728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24728; decide +kernel
    rw [ha]
    exact (canonical24728 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1680 + difference 3 5) (sourceB1680 + difference 5 3) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1680 + difference 3 5) (sourceB1680 + difference 5 3) sourceC1680) = raw24729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24729; decide +kernel
    rw [ha]
    exact (canonical24729 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1680 + difference 4 0) (sourceB1680 + difference 0 4) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA1680 + difference 4 0) (sourceB1680 + difference 0 4) sourceC1680) = raw24730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24730; decide +kernel
    rw [ha]
    exact (canonical24730 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1680 + difference 4 1) (sourceB1680 + difference 1 4) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3258) := by
    have ha : (tripleCharges (sourceA1680 + difference 4 1) (sourceB1680 + difference 1 4) sourceC1680) = raw24731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24731; decide +kernel
    rw [ha]
    exact (canonical24731 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1680 + difference 4 2) (sourceB1680 + difference 2 4) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3270) := by
    have ha : (tripleCharges (sourceA1680 + difference 4 2) (sourceB1680 + difference 2 4) sourceC1680) = raw24732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24732; decide +kernel
    rw [ha]
    exact (canonical24732 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1680 + difference 4 3) (sourceB1680 + difference 3 4) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA1680 + difference 4 3) (sourceB1680 + difference 3 4) sourceC1680) = raw24733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24733; decide +kernel
    rw [ha]
    exact (canonical24733 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1680 + difference 4 5) (sourceB1680 + difference 5 4) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1680 + difference 4 5) (sourceB1680 + difference 5 4) sourceC1680) = raw24734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24734; decide +kernel
    rw [ha]
    exact (canonical24734 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1680 + difference 5 0) (sourceB1680 + difference 0 5) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA1680 + difference 5 0) (sourceB1680 + difference 0 5) sourceC1680) = raw24735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24735; decide +kernel
    rw [ha]
    exact (canonical24735 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1680 + difference 5 1) (sourceB1680 + difference 1 5) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA1680 + difference 5 1) (sourceB1680 + difference 1 5) sourceC1680) = raw24736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24736; decide +kernel
    rw [ha]
    exact (canonical24736 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1680 + difference 5 2) (sourceB1680 + difference 2 5) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3264) := by
    have ha : (tripleCharges (sourceA1680 + difference 5 2) (sourceB1680 + difference 2 5) sourceC1680) = raw24737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24737; decide +kernel
    rw [ha]
    exact (canonical24737 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1680 + difference 5 3) (sourceB1680 + difference 3 5) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1680 + difference 5 3) (sourceB1680 + difference 3 5) sourceC1680) = raw24738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24738; decide +kernel
    rw [ha]
    exact (canonical24738 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1680 + difference 5 4) (sourceB1680 + difference 4 5) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1680 + difference 5 4) (sourceB1680 + difference 4 5) sourceC1680) = raw24739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24739; decide +kernel
    rw [ha]
    exact (canonical24739 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1680 sourceB1680 sourceC1680
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1680, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1681 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1681 + difference 0 0) (sourceB1681 + difference 0 0) sourceC1681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1681 + difference 0 0) (sourceB1681 + difference 0 0) sourceC1681) = raw24740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1681 sourceB1681 sourceC1681 difference raw24740; decide +kernel
    rw [ha]
    exact (canonical24740 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1681 + difference 1 0) (sourceB1681 + difference 0 1) sourceC1681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 623) := by
    have ha : (tripleCharges (sourceA1681 + difference 1 0) (sourceB1681 + difference 0 1) sourceC1681) = raw24741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1681 sourceB1681 sourceC1681 difference raw24741; decide +kernel
    rw [ha]
    exact (canonical24741 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1681 + difference 2 0) (sourceB1681 + difference 0 2) sourceC1681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 638) := by
    have ha : (tripleCharges (sourceA1681 + difference 2 0) (sourceB1681 + difference 0 2) sourceC1681) = raw24742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1681 sourceB1681 sourceC1681 difference raw24742; decide +kernel
    rw [ha]
    exact (canonical24742 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1681 + difference 3 0) (sourceB1681 + difference 0 3) sourceC1681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 627) := by
    have ha : (tripleCharges (sourceA1681 + difference 3 0) (sourceB1681 + difference 0 3) sourceC1681) = raw24743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1681 sourceB1681 sourceC1681 difference raw24743; decide +kernel
    rw [ha]
    exact (canonical24743 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1681 + difference 4 0) (sourceB1681 + difference 0 4) sourceC1681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 631) := by
    have ha : (tripleCharges (sourceA1681 + difference 4 0) (sourceB1681 + difference 0 4) sourceC1681) = raw24744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1681 sourceB1681 sourceC1681 difference raw24744; decide +kernel
    rw [ha]
    exact (canonical24744 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1681 + difference 5 0) (sourceB1681 + difference 0 5) sourceC1681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 626) := by
    have ha : (tripleCharges (sourceA1681 + difference 5 0) (sourceB1681 + difference 0 5) sourceC1681) = raw24745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1681 sourceB1681 sourceC1681 difference raw24745; decide +kernel
    rw [ha]
    exact (canonical24745 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1681 + sourceB1681) sourceC1681) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1681 + sourceB1681) sourceC1681) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA1681 sourceB1681 sourceC1681 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1681 sourceB1681 sourceC1681
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1681, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1424 : Integer.Sparse.reindex keyMap MixedData.row1424 = numericRow1424 := by decide +kernel

theorem numericCheck1424 (x : Master → ℝ) : Integer.Sparse.eval numericRow1424 x =
    (1 : ℝ) * reducedSource1424 x := by
  norm_num [numericRow1424, reducedSource1424, Integer.Sparse.eval, Sparse.eval, nodeValue1512, nodeValue1513, nodeValue1520, nodeValue1526, nodeValue2657, nodeValue2683, nodeValue2737, nodeValue3259, nodeValue3266, nodeValue3271, nodeValue3293, nodeValue3296, nodeValue3300, nodeValue3301, nodeValue3302, nodeValue3303, nodeValue3306, nodeValue3547, nodeValue3564, nodeValue3582, nodeValue3583]

theorem reindexCheck1425 : Integer.Sparse.reindex keyMap MixedData.row1425 = numericRow1425 := by decide +kernel

theorem numericCheck1425 (x : Master → ℝ) : Integer.Sparse.eval numericRow1425 x =
    (1 : ℝ) * reducedSource1425 x := by
  norm_num [numericRow1425, reducedSource1425, Integer.Sparse.eval, Sparse.eval, nodeValue638, nodeValue641, nodeValue642, nodeValue653, nodeValue1294, nodeValue4092]

theorem reindexCheck1426 : Integer.Sparse.reindex keyMap MixedData.row1426 = numericRow1426 := by decide +kernel

theorem numericCheck1426 (x : Master → ℝ) : Integer.Sparse.eval numericRow1426 x =
    (1 : ℝ) * reducedSource1426 x := by
  norm_num [numericRow1426, reducedSource1426, Integer.Sparse.eval, Sparse.eval, nodeValue1287, nodeValue2584, nodeValue2685, nodeValue2761, nodeValue4082]

theorem reindexCheck1427 : Integer.Sparse.reindex keyMap MixedData.row1427 = numericRow1427 := by decide +kernel

theorem numericCheck1427 (x : Master → ℝ) : Integer.Sparse.eval numericRow1427 x =
    (1 : ℝ) * reducedSource1427 x := by
  norm_num [numericRow1427, reducedSource1427, Integer.Sparse.eval, Sparse.eval, nodeValue1230, nodeValue2505, nodeValue2551, nodeValue2705, nodeValue2729, nodeValue2736, nodeValue4088]

theorem reindexCheck1430 : Integer.Sparse.reindex keyMap MixedData.row1430 = numericRow1430 := by decide +kernel

theorem numericCheck1430 (x : Master → ℝ) : Integer.Sparse.eval numericRow1430 x =
    (1 : ℝ) * reducedSource1430 x := by
  norm_num [numericRow1430, reducedSource1430, Integer.Sparse.eval, Sparse.eval, nodeValue1504, nodeValue1505, nodeValue1508, nodeValue1515, nodeValue3255, nodeValue3257, nodeValue3261, nodeValue3263, nodeValue3273, nodeValue3274, nodeValue3290, nodeValue3291, nodeValue3292, nodeValue3294, nodeValue3297, nodeValue3299, nodeValue3304, nodeValue3483, nodeValue3521, nodeValue3544, nodeValue3546]

theorem reindexCheck1431 : Integer.Sparse.reindex keyMap MixedData.row1431 = numericRow1431 := by decide +kernel

theorem numericCheck1431 (x : Master → ℝ) : Integer.Sparse.eval numericRow1431 x =
    (1 : ℝ) * reducedSource1431 x := by
  norm_num [numericRow1431, reducedSource1431, Integer.Sparse.eval, Sparse.eval, nodeValue625, nodeValue630, nodeValue632, nodeValue640, nodeValue1240, nodeValue4091]

theorem reindexCheck1432 : Integer.Sparse.reindex keyMap MixedData.row1432 = numericRow1432 := by decide +kernel

theorem numericCheck1432 (x : Master → ℝ) : Integer.Sparse.eval numericRow1432 x =
    (1 : ℝ) * reducedSource1432 x := by
  norm_num [numericRow1432, reducedSource1432, Integer.Sparse.eval, Sparse.eval, nodeValue1150, nodeValue1152, nodeValue1158, nodeValue1240, nodeValue2556, nodeValue4091]

theorem reindexCheck1438 : Integer.Sparse.reindex keyMap MixedData.row1438 = numericRow1438 := by decide +kernel

theorem numericCheck1438 (x : Master → ℝ) : Integer.Sparse.eval numericRow1438 x =
    (1 : ℝ) * reducedSource1438 x := by
  norm_num [numericRow1438, reducedSource1438, Integer.Sparse.eval, Sparse.eval, nodeValue1510, nodeValue1511, nodeValue1512, nodeValue1514, nodeValue1522, nodeValue3256, nodeValue3258, nodeValue3259, nodeValue3260, nodeValue3264, nodeValue3265, nodeValue3267, nodeValue3270, nodeValue3288, nodeValue3289, nodeValue3291, nodeValue3293, nodeValue3294, nodeValue3295, nodeValue3296, nodeValue3300, nodeValue3301, nodeValue3303, nodeValue3305, nodeValue3470, nodeValue3514, nodeValue3533, nodeValue3534, nodeValue3547]

theorem reindexCheck1439 : Integer.Sparse.reindex keyMap MixedData.row1439 = numericRow1439 := by decide +kernel

theorem numericCheck1439 (x : Master → ℝ) : Integer.Sparse.eval numericRow1439 x =
    (1 : ℝ) * reducedSource1439 x := by
  norm_num [numericRow1439, reducedSource1439, Integer.Sparse.eval, Sparse.eval, nodeValue623, nodeValue626, nodeValue627, nodeValue631, nodeValue638, nodeValue1236, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1424 (mixedVector B) = 0 := by
  have h1512 : mixedVector B (Sum.inr 1512) = Sparse.eval nodeValue1512 (mixedVector B) := by
    change mixedMoment B node1512 node1512Labels = _
    exact sound1512 B hB hF
  have h1513 : mixedVector B (Sum.inr 1513) = Sparse.eval nodeValue1513 (mixedVector B) := by
    change mixedMoment B node1513 node1513Labels = _
    exact sound1513 B hB hF
  have h1520 : mixedVector B (Sum.inr 1520) = Sparse.eval nodeValue1520 (mixedVector B) := by
    change mixedMoment B node1520 node1520Labels = _
    exact sound1520 B hB hF
  have h1526 : mixedVector B (Sum.inr 1526) = Sparse.eval nodeValue1526 (mixedVector B) := by
    change mixedMoment B node1526 node1526Labels = _
    exact sound1526 B hB hF
  have h2657 : mixedVector B (Sum.inr 2657) = Sparse.eval nodeValue2657 (mixedVector B) := by
    change mixedMoment B node2657 node2657Labels = _
    exact sound2657 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h3259 : mixedVector B (Sum.inr 3259) = Sparse.eval nodeValue3259 (mixedVector B) := by
    change mixedMoment B node3259 node3259Labels = _
    exact sound3259 B hB hF
  have h3266 : mixedVector B (Sum.inr 3266) = Sparse.eval nodeValue3266 (mixedVector B) := by
    change mixedMoment B node3266 node3266Labels = _
    exact sound3266 B hB hF
  have h3271 : mixedVector B (Sum.inr 3271) = Sparse.eval nodeValue3271 (mixedVector B) := by
    change mixedMoment B node3271 node3271Labels = _
    exact sound3271 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3303 : mixedVector B (Sum.inr 3303) = Sparse.eval nodeValue3303 (mixedVector B) := by
    change mixedMoment B node3303 node3303Labels = _
    exact sound3303 B hB hF
  have h3306 : mixedVector B (Sum.inr 3306) = Sparse.eval nodeValue3306 (mixedVector B) := by
    change mixedMoment B node3306 node3306Labels = _
    exact sound3306 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  simpa only [sourceForm1663, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1512, h1513, h1520, h1526, h2657, h2683, h2737, h3259, h3266, h3271, h3293, h3296, h3300, h3301, h3302, h3303, h3306, h3547, h3564, h3582, h3583, reducedSource1424] using sourceEq1663 B hB

theorem rowSound1424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1424 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1424, numericCheck1424, reducedZero1424 B hB hF, mul_zero]

theorem reducedZero1425 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1425 (mixedVector B) = 0 := by
  have h638 : mixedVector B (Sum.inr 638) = Sparse.eval nodeValue638 (mixedVector B) := by
    change mixedMoment B node638 node638Labels = _
    exact sound638 B hB hF
  have h641 : mixedVector B (Sum.inr 641) = Sparse.eval nodeValue641 (mixedVector B) := by
    change mixedMoment B node641 node641Labels = _
    exact sound641 B hB hF
  have h642 : mixedVector B (Sum.inr 642) = Sparse.eval nodeValue642 (mixedVector B) := by
    change mixedMoment B node642 node642Labels = _
    exact sound642 B hB hF
  have h653 : mixedVector B (Sum.inr 653) = Sparse.eval nodeValue653 (mixedVector B) := by
    change mixedMoment B node653 node653Labels = _
    exact sound653 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1664, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h638, h641, h642, h653, h1294, h4092, reducedSource1425] using sourceEq1664 B hB

theorem rowSound1425 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1425 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1425, numericCheck1425, reducedZero1425 B hB hF, mul_zero]

theorem reducedZero1426 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1426 (mixedVector B) = 0 := by
  have h1287 : mixedVector B (Sum.inr 1287) = Sparse.eval nodeValue1287 (mixedVector B) := by
    change mixedMoment B node1287 node1287Labels = _
    exact sound1287 B hB hF
  have h2584 : mixedVector B (Sum.inr 2584) = Sparse.eval nodeValue2584 (mixedVector B) := by
    change mixedMoment B node2584 node2584Labels = _
    exact sound2584 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2761 : mixedVector B (Sum.inr 2761) = Sparse.eval nodeValue2761 (mixedVector B) := by
    change mixedMoment B node2761 node2761Labels = _
    exact sound2761 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1667, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1287, h2584, h2685, h2761, h4082, reducedSource1426] using sourceEq1667 B hB

theorem rowSound1426 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1426 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1426, numericCheck1426, reducedZero1426 B hB hF, mul_zero]

theorem reducedZero1427 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1427 (mixedVector B) = 0 := by
  have h1230 : mixedVector B (Sum.inr 1230) = Sparse.eval nodeValue1230 (mixedVector B) := by
    change mixedMoment B node1230 node1230Labels = _
    exact sound1230 B hB hF
  have h2505 : mixedVector B (Sum.inr 2505) = Sparse.eval nodeValue2505 (mixedVector B) := by
    change mixedMoment B node2505 node2505Labels = _
    exact sound2505 B hB hF
  have h2551 : mixedVector B (Sum.inr 2551) = Sparse.eval nodeValue2551 (mixedVector B) := by
    change mixedMoment B node2551 node2551Labels = _
    exact sound2551 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h2736 : mixedVector B (Sum.inr 2736) = Sparse.eval nodeValue2736 (mixedVector B) := by
    change mixedMoment B node2736 node2736Labels = _
    exact sound2736 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1668, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1230, h2505, h2551, h2705, h2729, h2736, h4088, reducedSource1427] using sourceEq1668 B hB

theorem rowSound1427 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1427 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1427, numericCheck1427, reducedZero1427 B hB hF, mul_zero]

theorem reducedZero1430 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1430 (mixedVector B) = 0 := by
  have h1504 : mixedVector B (Sum.inr 1504) = Sparse.eval nodeValue1504 (mixedVector B) := by
    change mixedMoment B node1504 node1504Labels = _
    exact sound1504 B hB hF
  have h1505 : mixedVector B (Sum.inr 1505) = Sparse.eval nodeValue1505 (mixedVector B) := by
    change mixedMoment B node1505 node1505Labels = _
    exact sound1505 B hB hF
  have h1508 : mixedVector B (Sum.inr 1508) = Sparse.eval nodeValue1508 (mixedVector B) := by
    change mixedMoment B node1508 node1508Labels = _
    exact sound1508 B hB hF
  have h1515 : mixedVector B (Sum.inr 1515) = Sparse.eval nodeValue1515 (mixedVector B) := by
    change mixedMoment B node1515 node1515Labels = _
    exact sound1515 B hB hF
  have h3255 : mixedVector B (Sum.inr 3255) = Sparse.eval nodeValue3255 (mixedVector B) := by
    change mixedMoment B node3255 node3255Labels = _
    exact sound3255 B hB hF
  have h3257 : mixedVector B (Sum.inr 3257) = Sparse.eval nodeValue3257 (mixedVector B) := by
    change mixedMoment B node3257 node3257Labels = _
    exact sound3257 B hB hF
  have h3261 : mixedVector B (Sum.inr 3261) = Sparse.eval nodeValue3261 (mixedVector B) := by
    change mixedMoment B node3261 node3261Labels = _
    exact sound3261 B hB hF
  have h3263 : mixedVector B (Sum.inr 3263) = Sparse.eval nodeValue3263 (mixedVector B) := by
    change mixedMoment B node3263 node3263Labels = _
    exact sound3263 B hB hF
  have h3273 : mixedVector B (Sum.inr 3273) = Sparse.eval nodeValue3273 (mixedVector B) := by
    change mixedMoment B node3273 node3273Labels = _
    exact sound3273 B hB hF
  have h3274 : mixedVector B (Sum.inr 3274) = Sparse.eval nodeValue3274 (mixedVector B) := by
    change mixedMoment B node3274 node3274Labels = _
    exact sound3274 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3297 : mixedVector B (Sum.inr 3297) = Sparse.eval nodeValue3297 (mixedVector B) := by
    change mixedMoment B node3297 node3297Labels = _
    exact sound3297 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h3483 : mixedVector B (Sum.inr 3483) = Sparse.eval nodeValue3483 (mixedVector B) := by
    change mixedMoment B node3483 node3483Labels = _
    exact sound3483 B hB hF
  have h3521 : mixedVector B (Sum.inr 3521) = Sparse.eval nodeValue3521 (mixedVector B) := by
    change mixedMoment B node3521 node3521Labels = _
    exact sound3521 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  simpa only [sourceForm1671, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1504, h1505, h1508, h1515, h3255, h3257, h3261, h3263, h3273, h3274, h3290, h3291, h3292, h3294, h3297, h3299, h3304, h3483, h3521, h3544, h3546, reducedSource1430] using sourceEq1671 B hB

theorem rowSound1430 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1430 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1430, numericCheck1430, reducedZero1430 B hB hF, mul_zero]

theorem reducedZero1431 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1431 (mixedVector B) = 0 := by
  have h625 : mixedVector B (Sum.inr 625) = Sparse.eval nodeValue625 (mixedVector B) := by
    change mixedMoment B node625 node625Labels = _
    exact sound625 B hB hF
  have h630 : mixedVector B (Sum.inr 630) = Sparse.eval nodeValue630 (mixedVector B) := by
    change mixedMoment B node630 node630Labels = _
    exact sound630 B hB hF
  have h632 : mixedVector B (Sum.inr 632) = Sparse.eval nodeValue632 (mixedVector B) := by
    change mixedMoment B node632 node632Labels = _
    exact sound632 B hB hF
  have h640 : mixedVector B (Sum.inr 640) = Sparse.eval nodeValue640 (mixedVector B) := by
    change mixedMoment B node640 node640Labels = _
    exact sound640 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1672, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h625, h630, h632, h640, h1240, h4091, reducedSource1431] using sourceEq1672 B hB

theorem rowSound1431 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1431 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1431, numericCheck1431, reducedZero1431 B hB hF, mul_zero]

theorem reducedZero1432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1432 (mixedVector B) = 0 := by
  have h1150 : mixedVector B (Sum.inr 1150) = Sparse.eval nodeValue1150 (mixedVector B) := by
    change mixedMoment B node1150 node1150Labels = _
    exact sound1150 B hB hF
  have h1152 : mixedVector B (Sum.inr 1152) = Sparse.eval nodeValue1152 (mixedVector B) := by
    change mixedMoment B node1152 node1152Labels = _
    exact sound1152 B hB hF
  have h1158 : mixedVector B (Sum.inr 1158) = Sparse.eval nodeValue1158 (mixedVector B) := by
    change mixedMoment B node1158 node1158Labels = _
    exact sound1158 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1673, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1150, h1152, h1158, h1240, h2556, h4091, reducedSource1432] using sourceEq1673 B hB

theorem rowSound1432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1432 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1432, numericCheck1432, reducedZero1432 B hB hF, mul_zero]

theorem reducedZero1438 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1438 (mixedVector B) = 0 := by
  have h1510 : mixedVector B (Sum.inr 1510) = Sparse.eval nodeValue1510 (mixedVector B) := by
    change mixedMoment B node1510 node1510Labels = _
    exact sound1510 B hB hF
  have h1511 : mixedVector B (Sum.inr 1511) = Sparse.eval nodeValue1511 (mixedVector B) := by
    change mixedMoment B node1511 node1511Labels = _
    exact sound1511 B hB hF
  have h1512 : mixedVector B (Sum.inr 1512) = Sparse.eval nodeValue1512 (mixedVector B) := by
    change mixedMoment B node1512 node1512Labels = _
    exact sound1512 B hB hF
  have h1514 : mixedVector B (Sum.inr 1514) = Sparse.eval nodeValue1514 (mixedVector B) := by
    change mixedMoment B node1514 node1514Labels = _
    exact sound1514 B hB hF
  have h1522 : mixedVector B (Sum.inr 1522) = Sparse.eval nodeValue1522 (mixedVector B) := by
    change mixedMoment B node1522 node1522Labels = _
    exact sound1522 B hB hF
  have h3256 : mixedVector B (Sum.inr 3256) = Sparse.eval nodeValue3256 (mixedVector B) := by
    change mixedMoment B node3256 node3256Labels = _
    exact sound3256 B hB hF
  have h3258 : mixedVector B (Sum.inr 3258) = Sparse.eval nodeValue3258 (mixedVector B) := by
    change mixedMoment B node3258 node3258Labels = _
    exact sound3258 B hB hF
  have h3259 : mixedVector B (Sum.inr 3259) = Sparse.eval nodeValue3259 (mixedVector B) := by
    change mixedMoment B node3259 node3259Labels = _
    exact sound3259 B hB hF
  have h3260 : mixedVector B (Sum.inr 3260) = Sparse.eval nodeValue3260 (mixedVector B) := by
    change mixedMoment B node3260 node3260Labels = _
    exact sound3260 B hB hF
  have h3264 : mixedVector B (Sum.inr 3264) = Sparse.eval nodeValue3264 (mixedVector B) := by
    change mixedMoment B node3264 node3264Labels = _
    exact sound3264 B hB hF
  have h3265 : mixedVector B (Sum.inr 3265) = Sparse.eval nodeValue3265 (mixedVector B) := by
    change mixedMoment B node3265 node3265Labels = _
    exact sound3265 B hB hF
  have h3267 : mixedVector B (Sum.inr 3267) = Sparse.eval nodeValue3267 (mixedVector B) := by
    change mixedMoment B node3267 node3267Labels = _
    exact sound3267 B hB hF
  have h3270 : mixedVector B (Sum.inr 3270) = Sparse.eval nodeValue3270 (mixedVector B) := by
    change mixedMoment B node3270 node3270Labels = _
    exact sound3270 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3295 : mixedVector B (Sum.inr 3295) = Sparse.eval nodeValue3295 (mixedVector B) := by
    change mixedMoment B node3295 node3295Labels = _
    exact sound3295 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3303 : mixedVector B (Sum.inr 3303) = Sparse.eval nodeValue3303 (mixedVector B) := by
    change mixedMoment B node3303 node3303Labels = _
    exact sound3303 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3470 : mixedVector B (Sum.inr 3470) = Sparse.eval nodeValue3470 (mixedVector B) := by
    change mixedMoment B node3470 node3470Labels = _
    exact sound3470 B hB hF
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  simpa only [sourceForm1680, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1510, h1511, h1512, h1514, h1522, h3256, h3258, h3259, h3260, h3264, h3265, h3267, h3270, h3288, h3289, h3291, h3293, h3294, h3295, h3296, h3300, h3301, h3303, h3305, h3470, h3514, h3533, h3534, h3547, reducedSource1438] using sourceEq1680 B hB

theorem rowSound1438 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1438 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1438, numericCheck1438, reducedZero1438 B hB hF, mul_zero]

theorem reducedZero1439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1439 (mixedVector B) = 0 := by
  have h623 : mixedVector B (Sum.inr 623) = Sparse.eval nodeValue623 (mixedVector B) := by
    change mixedMoment B node623 node623Labels = _
    exact sound623 B hB hF
  have h626 : mixedVector B (Sum.inr 626) = Sparse.eval nodeValue626 (mixedVector B) := by
    change mixedMoment B node626 node626Labels = _
    exact sound626 B hB hF
  have h627 : mixedVector B (Sum.inr 627) = Sparse.eval nodeValue627 (mixedVector B) := by
    change mixedMoment B node627 node627Labels = _
    exact sound627 B hB hF
  have h631 : mixedVector B (Sum.inr 631) = Sparse.eval nodeValue631 (mixedVector B) := by
    change mixedMoment B node631 node631Labels = _
    exact sound631 B hB hF
  have h638 : mixedVector B (Sum.inr 638) = Sparse.eval nodeValue638 (mixedVector B) := by
    change mixedMoment B node638 node638Labels = _
    exact sound638 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1681, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h623, h626, h627, h631, h638, h1236, h4092, reducedSource1439] using sourceEq1681 B hB

theorem rowSound1439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1439 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1439, numericCheck1439, reducedZero1439 B hB hF, mul_zero]

theorem sourceRowsAt1424 : MixedData.sourceRows (1424 : Fin 2425) =
    MixedData.row1424 := by decide +kernel

theorem sourceRowsAt1425 : MixedData.sourceRows (1425 : Fin 2425) =
    MixedData.row1425 := by decide +kernel

theorem sourceRowsAt1426 : MixedData.sourceRows (1426 : Fin 2425) =
    MixedData.row1426 := by decide +kernel

theorem sourceRowsAt1427 : MixedData.sourceRows (1427 : Fin 2425) =
    MixedData.row1427 := by decide +kernel

theorem sourceRowsAt1428 : MixedData.sourceRows (1428 : Fin 2425) =
    MixedData.row1428 := by decide +kernel

theorem sourceRowsAt1429 : MixedData.sourceRows (1429 : Fin 2425) =
    MixedData.row1429 := by decide +kernel

theorem sourceRowsAt1430 : MixedData.sourceRows (1430 : Fin 2425) =
    MixedData.row1430 := by decide +kernel

theorem sourceRowsAt1431 : MixedData.sourceRows (1431 : Fin 2425) =
    MixedData.row1431 := by decide +kernel

theorem sourceRowsAt1432 : MixedData.sourceRows (1432 : Fin 2425) =
    MixedData.row1432 := by decide +kernel

theorem sourceRowsAt1433 : MixedData.sourceRows (1433 : Fin 2425) =
    MixedData.row1433 := by decide +kernel

theorem sourceRowsAt1434 : MixedData.sourceRows (1434 : Fin 2425) =
    MixedData.row1434 := by decide +kernel

theorem sourceRowsAt1435 : MixedData.sourceRows (1435 : Fin 2425) =
    MixedData.row1435 := by decide +kernel

theorem sourceRowsAt1436 : MixedData.sourceRows (1436 : Fin 2425) =
    MixedData.row1436 := by decide +kernel

theorem sourceRowsAt1437 : MixedData.sourceRows (1437 : Fin 2425) =
    MixedData.row1437 := by decide +kernel

theorem sourceRowsAt1438 : MixedData.sourceRows (1438 : Fin 2425) =
    MixedData.row1438 := by decide +kernel

theorem sourceRowsAt1439 : MixedData.sourceRows (1439 : Fin 2425) =
    MixedData.row1439 := by decide +kernel

theorem chunkSound89_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 89) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1424 ∨ k.val = 1425 ∨ k.val = 1426 ∨ k.val = 1427 ∨ k.val = 1428 ∨ k.val = 1429 ∨ k.val = 1430 ∨ k.val = 1431 ∨ k.val = 1432 ∨ k.val = 1433 ∨ k.val = 1434 ∨ k.val = 1435 ∨ k.val = 1436 ∨ k.val = 1437 ∨ k.val = 1438 ∨ k.val = 1439 := by omega
  rcases heq with h1424 | h1425 | h1426 | h1427 | h1428 | h1429 | h1430 | h1431 | h1432 | h1433 | h1434 | h1435 | h1436 | h1437 | h1438 | h1439
  · have he : k = (1424 : Fin 2425) := Fin.ext h1424
    subst k
    rw [sourceRowsAt1424]
    exact rowSound1424 B hB hF
  · have he : k = (1425 : Fin 2425) := Fin.ext h1425
    subst k
    rw [sourceRowsAt1425]
    exact rowSound1425 B hB hF
  · have he : k = (1426 : Fin 2425) := Fin.ext h1426
    subst k
    rw [sourceRowsAt1426]
    exact rowSound1426 B hB hF
  · have he : k = (1427 : Fin 2425) := Fin.ext h1427
    subst k
    rw [sourceRowsAt1427]
    exact rowSound1427 B hB hF
  · have he : k = (1428 : Fin 2425) := Fin.ext h1428
    subst k
    rw [sourceRowsAt1428]
    exact rowSound1428_e B hB hF
  · have he : k = (1429 : Fin 2425) := Fin.ext h1429
    subst k
    rw [sourceRowsAt1429]
    exact rowSound1429_e B hB hF
  · have he : k = (1430 : Fin 2425) := Fin.ext h1430
    subst k
    rw [sourceRowsAt1430]
    exact rowSound1430 B hB hF
  · have he : k = (1431 : Fin 2425) := Fin.ext h1431
    subst k
    rw [sourceRowsAt1431]
    exact rowSound1431 B hB hF
  · have he : k = (1432 : Fin 2425) := Fin.ext h1432
    subst k
    rw [sourceRowsAt1432]
    exact rowSound1432 B hB hF
  · have he : k = (1433 : Fin 2425) := Fin.ext h1433
    subst k
    rw [sourceRowsAt1433]
    exact rowSound1433_e B hB hF
  · have he : k = (1434 : Fin 2425) := Fin.ext h1434
    subst k
    rw [sourceRowsAt1434]
    exact rowSound1434_e B hB hF
  · have he : k = (1435 : Fin 2425) := Fin.ext h1435
    subst k
    rw [sourceRowsAt1435]
    exact rowSound1435_e B hB hF
  · have he : k = (1436 : Fin 2425) := Fin.ext h1436
    subst k
    rw [sourceRowsAt1436]
    exact rowSound1436_e B hB hF
  · have he : k = (1437 : Fin 2425) := Fin.ext h1437
    subst k
    rw [sourceRowsAt1437]
    exact rowSound1437_e B hB hF
  · have he : k = (1438 : Fin 2425) := Fin.ext h1438
    subst k
    rw [sourceRowsAt1438]
    exact rowSound1438 B hB hF
  · have he : k = (1439 : Fin 2425) := Fin.ext h1439
    subst k
    rw [sourceRowsAt1439]
    exact rowSound1439 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89_e_oai
