-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:44:59.151961+00:00
-- url     : https://prove2.me/submissions/994affb2-3062-4932-8d39-1f4ce1134dc0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1984_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1985_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1988_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1989_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1990_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1991_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1993_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1994_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1995_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1998_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1999_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20196 raw20196Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw20196 raw20196Labels = mixedMoment B raw20196step0 raw20196step0Labels := by
      have hz : ∀ j, raw20196 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20196step0 = (fun i j => raw20196 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20196step0 raw20196; decide +kernel
      have hl : raw20196step0Labels = raw20196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20196 raw20196Labels permutation520 hz
    mixedMoment B raw20196step0 raw20196step0Labels = mixedMoment B raw20196step1 raw20196step1Labels := by
      have hz : ∀ j, raw20196step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20196step1 = (fun i j => raw20196step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20196step1 raw20196step0; decide +kernel
      have hl : raw20196step1Labels = raw20196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20196step0 raw20196step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical265
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33934 raw33934Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw33934 raw33934Labels = mixedMoment B raw33934step0 raw33934step0Labels := by
      have ha : raw33934step0 = (fun i j => raw33934 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33934step0 raw33934; decide +kernel
      have hl : raw33934step0Labels = raw33934Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33934 raw33934Labels permutation164 permutation7
    mixedMoment B raw33934step0 raw33934step0Labels = mixedMoment B raw33934step1 raw33934step1Labels := by
      have ha : raw33934step1 = -raw33934step0 := by apply Matrix.ext; change ∀ i j, raw33934step1 i j = -(raw33934step0 i j); unfold raw33934step1 raw33934step0; decide +kernel
      have hl : raw33934step1Labels = raw33934step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33934step1 raw33934step1Labels = mixedMoment B raw33934step2 raw33934step2Labels := by
      have ha : raw33934step2 = raw33934step1 := by apply Matrix.ext; unfold raw33934step2 raw33934step1; decide +kernel
      have hl : raw33934step1Labels = labelEmbedding1 ∘ raw33934step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33934step1 raw33934step1Labels raw33934step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical33935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33935 raw33935Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw33935 raw33935Labels = mixedMoment B raw33935step0 raw33935step0Labels := by
      have ha : raw33935step0 = (fun i j => raw33935 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33935step0 raw33935; decide +kernel
      have hl : raw33935step0Labels = raw33935Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33935 raw33935Labels permutation164 permutation7
    mixedMoment B raw33935step0 raw33935step0Labels = mixedMoment B raw33935step1 raw33935step1Labels := by
      have ha : raw33935step1 = -raw33935step0 := by apply Matrix.ext; change ∀ i j, raw33935step1 i j = -(raw33935step0 i j); unfold raw33935step1 raw33935step0; decide +kernel
      have hl : raw33935step1Labels = raw33935step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33935step1 raw33935step1Labels = mixedMoment B raw33935step2 raw33935step2Labels := by
      have ha : raw33935step2 = raw33935step1 := by apply Matrix.ext; unfold raw33935step2 raw33935step1; decide +kernel
      have hl : raw33935step1Labels = labelEmbedding1 ∘ raw33935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33935step1 raw33935step1Labels raw33935step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

theorem canonical33936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33936 raw33936Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw33936 raw33936Labels = mixedMoment B raw33936step0 raw33936step0Labels := by
      have ha : raw33936step0 = (fun i j => raw33936 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33936step0 raw33936; decide +kernel
      have hl : raw33936step0Labels = raw33936Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33936 raw33936Labels permutation164 permutation7
    mixedMoment B raw33936step0 raw33936step0Labels = mixedMoment B raw33936step1 raw33936step1Labels := by
      have ha : raw33936step1 = -raw33936step0 := by apply Matrix.ext; change ∀ i j, raw33936step1 i j = -(raw33936step0 i j); unfold raw33936step1 raw33936step0; decide +kernel
      have hl : raw33936step1Labels = raw33936step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33936step1 raw33936step1Labels = mixedMoment B raw33936step2 raw33936step2Labels := by
      have ha : raw33936step2 = raw33936step1 := by apply Matrix.ext; unfold raw33936step2 raw33936step1; decide +kernel
      have hl : raw33936step1Labels = labelEmbedding1 ∘ raw33936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33936step1 raw33936step1Labels raw33936step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2720 node2720Labels := by rfl

theorem canonical33937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33937 raw33937Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw33937 raw33937Labels = mixedMoment B raw33937step0 raw33937step0Labels := by
      have hz : ∀ j, raw33937 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33937step0 = (fun i j => raw33937 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33937step0 raw33937; decide +kernel
      have hl : raw33937step0Labels = raw33937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33937 raw33937Labels permutation520 hz
    mixedMoment B raw33937step0 raw33937step0Labels = mixedMoment B raw33937step1 raw33937step1Labels := by
      have ha : raw33937step1 = (fun i j => raw33937step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33937step1 raw33937step0; decide +kernel
      have hl : raw33937step1Labels = raw33937step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33937step0 raw33937step0Labels permutation32 permutation7
    mixedMoment B raw33937step1 raw33937step1Labels = mixedMoment B raw33937step2 raw33937step2Labels := by
      have ha : raw33937step2 = -raw33937step1 := by apply Matrix.ext; change ∀ i j, raw33937step2 i j = -(raw33937step1 i j); unfold raw33937step2 raw33937step1; decide +kernel
      have hl : raw33937step2Labels = raw33937step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33937step2 raw33937step2Labels = mixedMoment B raw33937step3 raw33937step3Labels := by
      have ha : raw33937step3 = raw33937step2 := by apply Matrix.ext; unfold raw33937step3 raw33937step2; decide +kernel
      have hl : raw33937step2Labels = labelEmbedding1 ∘ raw33937step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33937step2 raw33937step2Labels raw33937step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical33938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33938 raw33938Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw33938 raw33938Labels = mixedMoment B raw33938step0 raw33938step0Labels := by
      have ha : raw33938step0 = (fun i j => raw33938 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33938step0 raw33938; decide +kernel
      have hl : raw33938step0Labels = raw33938Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33938 raw33938Labels permutation164 permutation7
    mixedMoment B raw33938step0 raw33938step0Labels = mixedMoment B raw33938step1 raw33938step1Labels := by
      have ha : raw33938step1 = -raw33938step0 := by apply Matrix.ext; change ∀ i j, raw33938step1 i j = -(raw33938step0 i j); unfold raw33938step1 raw33938step0; decide +kernel
      have hl : raw33938step1Labels = raw33938step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33938step1 raw33938step1Labels = mixedMoment B raw33938step2 raw33938step2Labels := by
      have ha : raw33938step2 = raw33938step1 := by apply Matrix.ext; unfold raw33938step2 raw33938step1; decide +kernel
      have hl : raw33938step1Labels = labelEmbedding1 ∘ raw33938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33938step1 raw33938step1Labels raw33938step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical33939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33939 raw33939Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw33939 raw33939Labels = mixedMoment B raw33939step0 raw33939step0Labels := by
      have hz : ∀ j, raw33939 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33939step0 = (fun i j => raw33939 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33939step0 raw33939; decide +kernel
      have hl : raw33939step0Labels = raw33939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33939 raw33939Labels permutation265 hz
    mixedMoment B raw33939step0 raw33939step0Labels = mixedMoment B raw33939step1 raw33939step1Labels := by
      have ha : raw33939step1 = (fun i j => raw33939step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33939step1 raw33939step0; decide +kernel
      have hl : raw33939step1Labels = raw33939step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33939step0 raw33939step0Labels permutation44 permutation7
    mixedMoment B raw33939step1 raw33939step1Labels = mixedMoment B raw33939step2 raw33939step2Labels := by
      have ha : raw33939step2 = -raw33939step1 := by apply Matrix.ext; change ∀ i j, raw33939step2 i j = -(raw33939step1 i j); unfold raw33939step2 raw33939step1; decide +kernel
      have hl : raw33939step2Labels = raw33939step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33939step2 raw33939step2Labels = mixedMoment B raw33939step3 raw33939step3Labels := by
      have ha : raw33939step3 = raw33939step2 := by apply Matrix.ext; unfold raw33939step3 raw33939step2; decide +kernel
      have hl : raw33939step2Labels = labelEmbedding1 ∘ raw33939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33939step2 raw33939step2Labels raw33939step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical33940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33940 raw33940Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw33940 raw33940Labels = mixedMoment B raw33940step0 raw33940step0Labels := by
      have hz : ∀ j, raw33940 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33940step0 = (fun i j => raw33940 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33940step0 raw33940; decide +kernel
      have hl : raw33940step0Labels = raw33940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33940 raw33940Labels permutation265 hz
    mixedMoment B raw33940step0 raw33940step0Labels = mixedMoment B raw33940step1 raw33940step1Labels := by
      have ha : raw33940step1 = (fun i j => raw33940step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33940step1 raw33940step0; decide +kernel
      have hl : raw33940step1Labels = raw33940step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33940step0 raw33940step0Labels permutation44 permutation7
    mixedMoment B raw33940step1 raw33940step1Labels = mixedMoment B raw33940step2 raw33940step2Labels := by
      have ha : raw33940step2 = -raw33940step1 := by apply Matrix.ext; change ∀ i j, raw33940step2 i j = -(raw33940step1 i j); unfold raw33940step2 raw33940step1; decide +kernel
      have hl : raw33940step2Labels = raw33940step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33940step2 raw33940step2Labels = mixedMoment B raw33940step3 raw33940step3Labels := by
      have ha : raw33940step3 = raw33940step2 := by apply Matrix.ext; unfold raw33940step3 raw33940step2; decide +kernel
      have hl : raw33940step2Labels = labelEmbedding1 ∘ raw33940step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33940step2 raw33940step2Labels raw33940step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical33941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33941 raw33941Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw33941 raw33941Labels = mixedMoment B raw33941step0 raw33941step0Labels := by
      have hz : ∀ j, raw33941 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33941step0 = (fun i j => raw33941 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33941step0 raw33941; decide +kernel
      have hl : raw33941step0Labels = raw33941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33941 raw33941Labels permutation265 hz
    mixedMoment B raw33941step0 raw33941step0Labels = mixedMoment B raw33941step1 raw33941step1Labels := by
      have ha : raw33941step1 = (fun i j => raw33941step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33941step1 raw33941step0; decide +kernel
      have hl : raw33941step1Labels = raw33941step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33941step0 raw33941step0Labels permutation44 permutation7
    mixedMoment B raw33941step1 raw33941step1Labels = mixedMoment B raw33941step2 raw33941step2Labels := by
      have ha : raw33941step2 = -raw33941step1 := by apply Matrix.ext; change ∀ i j, raw33941step2 i j = -(raw33941step1 i j); unfold raw33941step2 raw33941step1; decide +kernel
      have hl : raw33941step2Labels = raw33941step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33941step2 raw33941step2Labels = mixedMoment B raw33941step3 raw33941step3Labels := by
      have ha : raw33941step3 = raw33941step2 := by apply Matrix.ext; unfold raw33941step3 raw33941step2; decide +kernel
      have hl : raw33941step2Labels = labelEmbedding1 ∘ raw33941step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33941step2 raw33941step2Labels raw33941step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical33942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33942 raw33942Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw33942 raw33942Labels = mixedMoment B raw33942step0 raw33942step0Labels := by
      have hz : ∀ j, raw33942 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33942step0 = (fun i j => raw33942 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33942step0 raw33942; decide +kernel
      have hl : raw33942step0Labels = raw33942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33942 raw33942Labels permutation520 hz
    mixedMoment B raw33942step0 raw33942step0Labels = mixedMoment B raw33942step1 raw33942step1Labels := by
      have hz : ∀ j, raw33942step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw33942step1 = (fun i j => raw33942step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw33942step1 raw33942step0; decide +kernel
      have hl : raw33942step1Labels = raw33942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33942step0 raw33942step0Labels permutation56 hz
    mixedMoment B raw33942step1 raw33942step1Labels = mixedMoment B raw33942step2 raw33942step2Labels := by
      have ha : raw33942step2 = (fun i j => raw33942step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33942step2 raw33942step1; decide +kernel
      have hl : raw33942step2Labels = raw33942step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33942step1 raw33942step1Labels permutation8 permutation7
    mixedMoment B raw33942step2 raw33942step2Labels = mixedMoment B raw33942step3 raw33942step3Labels := by
      have ha : raw33942step3 = -raw33942step2 := by apply Matrix.ext; change ∀ i j, raw33942step3 i j = -(raw33942step2 i j); unfold raw33942step3 raw33942step2; decide +kernel
      have hl : raw33942step3Labels = raw33942step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33942step3 raw33942step3Labels = mixedMoment B raw33942step4 raw33942step4Labels := by
      have ha : raw33942step4 = raw33942step3 := by apply Matrix.ext; unfold raw33942step4 raw33942step3; decide +kernel
      have hl : raw33942step3Labels = labelEmbedding1 ∘ raw33942step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33942step3 raw33942step3Labels raw33942step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical33943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33943 raw33943Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw33943 raw33943Labels = mixedMoment B raw33943step0 raw33943step0Labels := by
      have hz : ∀ j, raw33943 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33943step0 = (fun i j => raw33943 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33943step0 raw33943; decide +kernel
      have hl : raw33943step0Labels = raw33943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33943 raw33943Labels permutation265 hz
    mixedMoment B raw33943step0 raw33943step0Labels = mixedMoment B raw33943step1 raw33943step1Labels := by
      have ha : raw33943step1 = (fun i j => raw33943step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33943step1 raw33943step0; decide +kernel
      have hl : raw33943step1Labels = raw33943step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33943step0 raw33943step0Labels permutation44 permutation7
    mixedMoment B raw33943step1 raw33943step1Labels = mixedMoment B raw33943step2 raw33943step2Labels := by
      have ha : raw33943step2 = -raw33943step1 := by apply Matrix.ext; change ∀ i j, raw33943step2 i j = -(raw33943step1 i j); unfold raw33943step2 raw33943step1; decide +kernel
      have hl : raw33943step2Labels = raw33943step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33943step2 raw33943step2Labels = mixedMoment B raw33943step3 raw33943step3Labels := by
      have ha : raw33943step3 = raw33943step2 := by apply Matrix.ext; unfold raw33943step3 raw33943step2; decide +kernel
      have hl : raw33943step2Labels = labelEmbedding1 ∘ raw33943step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33943step2 raw33943step2Labels raw33943step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical33944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33944 raw33944Labels = mixedMoment B node1673 node1673Labels := by
  calc
    mixedMoment B raw33944 raw33944Labels = mixedMoment B raw33944step0 raw33944step0Labels := by
      have ha : raw33944step0 = (fun i j => raw33944 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33944step0 raw33944; decide +kernel
      have hl : raw33944step0Labels = raw33944Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33944 raw33944Labels permutation164 permutation7
    mixedMoment B raw33944step0 raw33944step0Labels = mixedMoment B raw33944step1 raw33944step1Labels := by
      have ha : raw33944step1 = -raw33944step0 := by apply Matrix.ext; change ∀ i j, raw33944step1 i j = -(raw33944step0 i j); unfold raw33944step1 raw33944step0; decide +kernel
      have hl : raw33944step1Labels = raw33944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33944step1 raw33944step1Labels = mixedMoment B raw33944step2 raw33944step2Labels := by
      have ha : raw33944step2 = raw33944step1 := by apply Matrix.ext; unfold raw33944step2 raw33944step1; decide +kernel
      have hl : raw33944step1Labels = labelEmbedding1 ∘ raw33944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33944step1 raw33944step1Labels raw33944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1673 node1673Labels := by rfl

theorem canonical33945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33945 raw33945Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw33945 raw33945Labels = mixedMoment B raw33945step0 raw33945step0Labels := by
      have ha : raw33945step0 = (fun i j => raw33945 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33945step0 raw33945; decide +kernel
      have hl : raw33945step0Labels = raw33945Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33945 raw33945Labels permutation164 permutation7
    mixedMoment B raw33945step0 raw33945step0Labels = mixedMoment B raw33945step1 raw33945step1Labels := by
      have ha : raw33945step1 = -raw33945step0 := by apply Matrix.ext; change ∀ i j, raw33945step1 i j = -(raw33945step0 i j); unfold raw33945step1 raw33945step0; decide +kernel
      have hl : raw33945step1Labels = raw33945step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33945step1 raw33945step1Labels = mixedMoment B raw33945step2 raw33945step2Labels := by
      have ha : raw33945step2 = raw33945step1 := by apply Matrix.ext; unfold raw33945step2 raw33945step1; decide +kernel
      have hl : raw33945step1Labels = labelEmbedding1 ∘ raw33945step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33945step1 raw33945step1Labels raw33945step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

theorem canonical33946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33946 raw33946Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw33946 raw33946Labels = mixedMoment B raw33946step0 raw33946step0Labels := by
      have ha : raw33946step0 = (fun i j => raw33946 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33946step0 raw33946; decide +kernel
      have hl : raw33946step0Labels = raw33946Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33946 raw33946Labels permutation166 permutation7
    mixedMoment B raw33946step0 raw33946step0Labels = mixedMoment B raw33946step1 raw33946step1Labels := by
      have ha : raw33946step1 = -raw33946step0 := by apply Matrix.ext; change ∀ i j, raw33946step1 i j = -(raw33946step0 i j); unfold raw33946step1 raw33946step0; decide +kernel
      have hl : raw33946step1Labels = raw33946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33946step1 raw33946step1Labels = mixedMoment B raw33946step2 raw33946step2Labels := by
      have ha : raw33946step2 = raw33946step1 := by apply Matrix.ext; unfold raw33946step2 raw33946step1; decide +kernel
      have hl : raw33946step1Labels = labelEmbedding1 ∘ raw33946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33946step1 raw33946step1Labels raw33946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical33947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33947 raw33947Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw33947 raw33947Labels = mixedMoment B raw33947step0 raw33947step0Labels := by
      have hz : ∀ j, raw33947 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33947step0 = (fun i j => raw33947 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33947step0 raw33947; decide +kernel
      have hl : raw33947step0Labels = raw33947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33947 raw33947Labels permutation520 hz
    mixedMoment B raw33947step0 raw33947step0Labels = mixedMoment B raw33947step1 raw33947step1Labels := by
      have ha : raw33947step1 = (fun i j => raw33947step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33947step1 raw33947step0; decide +kernel
      have hl : raw33947step1Labels = raw33947step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33947step0 raw33947step0Labels permutation32 permutation7
    mixedMoment B raw33947step1 raw33947step1Labels = mixedMoment B raw33947step2 raw33947step2Labels := by
      have ha : raw33947step2 = -raw33947step1 := by apply Matrix.ext; change ∀ i j, raw33947step2 i j = -(raw33947step1 i j); unfold raw33947step2 raw33947step1; decide +kernel
      have hl : raw33947step2Labels = raw33947step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33947step2 raw33947step2Labels = mixedMoment B raw33947step3 raw33947step3Labels := by
      have ha : raw33947step3 = raw33947step2 := by apply Matrix.ext; unfold raw33947step3 raw33947step2; decide +kernel
      have hl : raw33947step2Labels = labelEmbedding1 ∘ raw33947step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33947step2 raw33947step2Labels raw33947step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2227 node2227Labels := by rfl

theorem canonical33948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33948 raw33948Labels = mixedMoment B node2204 node2204Labels := by
  calc
    mixedMoment B raw33948 raw33948Labels = mixedMoment B raw33948step0 raw33948step0Labels := by
      have ha : raw33948step0 = (fun i j => raw33948 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33948step0 raw33948; decide +kernel
      have hl : raw33948step0Labels = raw33948Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33948 raw33948Labels permutation164 permutation7
    mixedMoment B raw33948step0 raw33948step0Labels = mixedMoment B raw33948step1 raw33948step1Labels := by
      have ha : raw33948step1 = -raw33948step0 := by apply Matrix.ext; change ∀ i j, raw33948step1 i j = -(raw33948step0 i j); unfold raw33948step1 raw33948step0; decide +kernel
      have hl : raw33948step1Labels = raw33948step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33948step1 raw33948step1Labels = mixedMoment B raw33948step2 raw33948step2Labels := by
      have ha : raw33948step2 = raw33948step1 := by apply Matrix.ext; unfold raw33948step2 raw33948step1; decide +kernel
      have hl : raw33948step1Labels = labelEmbedding1 ∘ raw33948step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33948step1 raw33948step1Labels raw33948step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2204 node2204Labels := by rfl

theorem canonical33949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33949 raw33949Labels = mixedMoment B node1671 node1671Labels := by
  calc
    mixedMoment B raw33949 raw33949Labels = mixedMoment B raw33949step0 raw33949step0Labels := by
      have ha : raw33949step0 = (fun i j => raw33949 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33949step0 raw33949; decide +kernel
      have hl : raw33949step0Labels = raw33949Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33949 raw33949Labels permutation164 permutation7
    mixedMoment B raw33949step0 raw33949step0Labels = mixedMoment B raw33949step1 raw33949step1Labels := by
      have ha : raw33949step1 = -raw33949step0 := by apply Matrix.ext; change ∀ i j, raw33949step1 i j = -(raw33949step0 i j); unfold raw33949step1 raw33949step0; decide +kernel
      have hl : raw33949step1Labels = raw33949step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33949step1 raw33949step1Labels = mixedMoment B raw33949step2 raw33949step2Labels := by
      have ha : raw33949step2 = raw33949step1 := by apply Matrix.ext; unfold raw33949step2 raw33949step1; decide +kernel
      have hl : raw33949step1Labels = labelEmbedding1 ∘ raw33949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33949step1 raw33949step1Labels raw33949step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1671 node1671Labels := by rfl

theorem canonical33950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33950 raw33950Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw33950 raw33950Labels = mixedMoment B raw33950step0 raw33950step0Labels := by
      have ha : raw33950step0 = (fun i j => raw33950 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33950step0 raw33950; decide +kernel
      have hl : raw33950step0Labels = raw33950Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33950 raw33950Labels permutation164 permutation7
    mixedMoment B raw33950step0 raw33950step0Labels = mixedMoment B raw33950step1 raw33950step1Labels := by
      have ha : raw33950step1 = -raw33950step0 := by apply Matrix.ext; change ∀ i j, raw33950step1 i j = -(raw33950step0 i j); unfold raw33950step1 raw33950step0; decide +kernel
      have hl : raw33950step1Labels = raw33950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33950step1 raw33950step1Labels = mixedMoment B raw33950step2 raw33950step2Labels := by
      have ha : raw33950step2 = raw33950step1 := by apply Matrix.ext; unfold raw33950step2 raw33950step1; decide +kernel
      have hl : raw33950step1Labels = labelEmbedding1 ∘ raw33950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33950step1 raw33950step1Labels raw33950step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2148 node2148Labels := by rfl

theorem canonical33951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33951 raw33951Labels = mixedMoment B node2199 node2199Labels := by
  calc
    mixedMoment B raw33951 raw33951Labels = mixedMoment B raw33951step0 raw33951step0Labels := by
      have ha : raw33951step0 = (fun i j => raw33951 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33951step0 raw33951; decide +kernel
      have hl : raw33951step0Labels = raw33951Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33951 raw33951Labels permutation164 permutation7
    mixedMoment B raw33951step0 raw33951step0Labels = mixedMoment B raw33951step1 raw33951step1Labels := by
      have ha : raw33951step1 = -raw33951step0 := by apply Matrix.ext; change ∀ i j, raw33951step1 i j = -(raw33951step0 i j); unfold raw33951step1 raw33951step0; decide +kernel
      have hl : raw33951step1Labels = raw33951step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33951step1 raw33951step1Labels = mixedMoment B raw33951step2 raw33951step2Labels := by
      have ha : raw33951step2 = raw33951step1 := by apply Matrix.ext; unfold raw33951step2 raw33951step1; decide +kernel
      have hl : raw33951step1Labels = labelEmbedding1 ∘ raw33951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33951step1 raw33951step1Labels raw33951step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2199 node2199Labels := by rfl

theorem canonical33952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33952 raw33952Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw33952 raw33952Labels = mixedMoment B raw33952step0 raw33952step0Labels := by
      have hz : ∀ j, raw33952 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33952step0 = (fun i j => raw33952 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33952step0 raw33952; decide +kernel
      have hl : raw33952step0Labels = raw33952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33952 raw33952Labels permutation520 hz
    mixedMoment B raw33952step0 raw33952step0Labels = mixedMoment B raw33952step1 raw33952step1Labels := by
      have ha : raw33952step1 = (fun i j => raw33952step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33952step1 raw33952step0; decide +kernel
      have hl : raw33952step1Labels = raw33952step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33952step0 raw33952step0Labels permutation32 permutation7
    mixedMoment B raw33952step1 raw33952step1Labels = mixedMoment B raw33952step2 raw33952step2Labels := by
      have ha : raw33952step2 = -raw33952step1 := by apply Matrix.ext; change ∀ i j, raw33952step2 i j = -(raw33952step1 i j); unfold raw33952step2 raw33952step1; decide +kernel
      have hl : raw33952step2Labels = raw33952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33952step2 raw33952step2Labels = mixedMoment B raw33952step3 raw33952step3Labels := by
      have ha : raw33952step3 = raw33952step2 := by apply Matrix.ext; unfold raw33952step3 raw33952step2; decide +kernel
      have hl : raw33952step2Labels = labelEmbedding1 ∘ raw33952step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33952step2 raw33952step2Labels raw33952step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical33953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33953 raw33953Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw33953 raw33953Labels = mixedMoment B raw33953step0 raw33953step0Labels := by
      have ha : raw33953step0 = (fun i j => raw33953 (permutation165 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33953step0 raw33953; decide +kernel
      have hl : raw33953step0Labels = raw33953Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33953 raw33953Labels permutation165 permutation7
    mixedMoment B raw33953step0 raw33953step0Labels = mixedMoment B raw33953step1 raw33953step1Labels := by
      have ha : raw33953step1 = -raw33953step0 := by apply Matrix.ext; change ∀ i j, raw33953step1 i j = -(raw33953step0 i j); unfold raw33953step1 raw33953step0; decide +kernel
      have hl : raw33953step1Labels = raw33953step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33953step1 raw33953step1Labels = mixedMoment B raw33953step2 raw33953step2Labels := by
      have ha : raw33953step2 = raw33953step1 := by apply Matrix.ext; unfold raw33953step2 raw33953step1; decide +kernel
      have hl : raw33953step1Labels = labelEmbedding1 ∘ raw33953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33953step1 raw33953step1Labels raw33953step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical33954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33954 raw33954Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw33954 raw33954Labels = mixedMoment B raw33954step0 raw33954step0Labels := by
      have ha : raw33954step0 = (fun i j => raw33954 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33954step0 raw33954; decide +kernel
      have hl : raw33954step0Labels = raw33954Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33954 raw33954Labels permutation164 permutation7
    mixedMoment B raw33954step0 raw33954step0Labels = mixedMoment B raw33954step1 raw33954step1Labels := by
      have ha : raw33954step1 = -raw33954step0 := by apply Matrix.ext; change ∀ i j, raw33954step1 i j = -(raw33954step0 i j); unfold raw33954step1 raw33954step0; decide +kernel
      have hl : raw33954step1Labels = raw33954step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33954step1 raw33954step1Labels = mixedMoment B raw33954step2 raw33954step2Labels := by
      have ha : raw33954step2 = raw33954step1 := by apply Matrix.ext; unfold raw33954step2 raw33954step1; decide +kernel
      have hl : raw33954step1Labels = labelEmbedding1 ∘ raw33954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33954step1 raw33954step1Labels raw33954step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

theorem canonical33955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33955 raw33955Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw33955 raw33955Labels = mixedMoment B raw33955step0 raw33955step0Labels := by
      have ha : raw33955step0 = (fun i j => raw33955 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33955step0 raw33955; decide +kernel
      have hl : raw33955step0Labels = raw33955Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33955 raw33955Labels permutation164 permutation7
    mixedMoment B raw33955step0 raw33955step0Labels = mixedMoment B raw33955step1 raw33955step1Labels := by
      have ha : raw33955step1 = -raw33955step0 := by apply Matrix.ext; change ∀ i j, raw33955step1 i j = -(raw33955step0 i j); unfold raw33955step1 raw33955step0; decide +kernel
      have hl : raw33955step1Labels = raw33955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33955step1 raw33955step1Labels = mixedMoment B raw33955step2 raw33955step2Labels := by
      have ha : raw33955step2 = raw33955step1 := by apply Matrix.ext; unfold raw33955step2 raw33955step1; decide +kernel
      have hl : raw33955step1Labels = labelEmbedding1 ∘ raw33955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33955step1 raw33955step1Labels raw33955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

theorem canonical33956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33956 raw33956Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw33956 raw33956Labels = mixedMoment B raw33956step0 raw33956step0Labels := by
      have ha : raw33956step0 = (fun i j => raw33956 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33956step0 raw33956; decide +kernel
      have hl : raw33956step0Labels = raw33956Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33956 raw33956Labels permutation164 permutation7
    mixedMoment B raw33956step0 raw33956step0Labels = mixedMoment B raw33956step1 raw33956step1Labels := by
      have ha : raw33956step1 = -raw33956step0 := by apply Matrix.ext; change ∀ i j, raw33956step1 i j = -(raw33956step0 i j); unfold raw33956step1 raw33956step0; decide +kernel
      have hl : raw33956step1Labels = raw33956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33956step1 raw33956step1Labels = mixedMoment B raw33956step2 raw33956step2Labels := by
      have ha : raw33956step2 = raw33956step1 := by apply Matrix.ext; unfold raw33956step2 raw33956step1; decide +kernel
      have hl : raw33956step1Labels = labelEmbedding1 ∘ raw33956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33956step1 raw33956step1Labels raw33956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

theorem canonical33957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33957 raw33957Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw33957 raw33957Labels = mixedMoment B raw33957step0 raw33957step0Labels := by
      have ha : raw33957step0 = (fun i j => raw33957 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33957step0 raw33957; decide +kernel
      have hl : raw33957step0Labels = raw33957Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33957 raw33957Labels permutation164 permutation7
    mixedMoment B raw33957step0 raw33957step0Labels = mixedMoment B raw33957step1 raw33957step1Labels := by
      have ha : raw33957step1 = -raw33957step0 := by apply Matrix.ext; change ∀ i j, raw33957step1 i j = -(raw33957step0 i j); unfold raw33957step1 raw33957step0; decide +kernel
      have hl : raw33957step1Labels = raw33957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33957step1 raw33957step1Labels = mixedMoment B raw33957step2 raw33957step2Labels := by
      have ha : raw33957step2 = raw33957step1 := by apply Matrix.ext; unfold raw33957step2 raw33957step1; decide +kernel
      have hl : raw33957step1Labels = labelEmbedding1 ∘ raw33957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33957step1 raw33957step1Labels raw33957step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

theorem canonical33958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33958 raw33958Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw33958 raw33958Labels = mixedMoment B raw33958step0 raw33958step0Labels := by
      have ha : raw33958step0 = (fun i j => raw33958 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33958step0 raw33958; decide +kernel
      have hl : raw33958step0Labels = raw33958Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33958 raw33958Labels permutation164 permutation7
    mixedMoment B raw33958step0 raw33958step0Labels = mixedMoment B raw33958step1 raw33958step1Labels := by
      have ha : raw33958step1 = -raw33958step0 := by apply Matrix.ext; change ∀ i j, raw33958step1 i j = -(raw33958step0 i j); unfold raw33958step1 raw33958step0; decide +kernel
      have hl : raw33958step1Labels = raw33958step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33958step1 raw33958step1Labels = mixedMoment B raw33958step2 raw33958step2Labels := by
      have ha : raw33958step2 = raw33958step1 := by apply Matrix.ext; unfold raw33958step2 raw33958step1; decide +kernel
      have hl : raw33958step1Labels = labelEmbedding1 ∘ raw33958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33958step1 raw33958step1Labels raw33958step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

theorem canonical33959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33959 raw33959Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw33959 raw33959Labels = mixedMoment B raw33959step0 raw33959step0Labels := by
      have ha : raw33959step0 = (fun i j => raw33959 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33959step0 raw33959; decide +kernel
      have hl : raw33959step0Labels = raw33959Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33959 raw33959Labels permutation164 permutation7
    mixedMoment B raw33959step0 raw33959step0Labels = mixedMoment B raw33959step1 raw33959step1Labels := by
      have ha : raw33959step1 = -raw33959step0 := by apply Matrix.ext; change ∀ i j, raw33959step1 i j = -(raw33959step0 i j); unfold raw33959step1 raw33959step0; decide +kernel
      have hl : raw33959step1Labels = raw33959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33959step1 raw33959step1Labels = mixedMoment B raw33959step2 raw33959step2Labels := by
      have ha : raw33959step2 = raw33959step1 := by apply Matrix.ext; unfold raw33959step2 raw33959step1; decide +kernel
      have hl : raw33959step1Labels = labelEmbedding1 ∘ raw33959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33959step1 raw33959step1Labels raw33959step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

theorem canonical33960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33960 raw33960Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw33960 raw33960Labels = mixedMoment B raw33960step0 raw33960step0Labels := by
      have ha : raw33960step0 = (fun i j => raw33960 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33960step0 raw33960; decide +kernel
      have hl : raw33960step0Labels = raw33960Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33960 raw33960Labels permutation164 permutation7
    mixedMoment B raw33960step0 raw33960step0Labels = mixedMoment B raw33960step1 raw33960step1Labels := by
      have ha : raw33960step1 = -raw33960step0 := by apply Matrix.ext; change ∀ i j, raw33960step1 i j = -(raw33960step0 i j); unfold raw33960step1 raw33960step0; decide +kernel
      have hl : raw33960step1Labels = raw33960step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33960step1 raw33960step1Labels = mixedMoment B raw33960step2 raw33960step2Labels := by
      have ha : raw33960step2 = raw33960step1 := by apply Matrix.ext; unfold raw33960step2 raw33960step1; decide +kernel
      have hl : raw33960step1Labels = labelEmbedding1 ∘ raw33960step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33960step1 raw33960step1Labels raw33960step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2147 node2147Labels := by rfl

theorem canonical33961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33961 raw33961Labels = mixedMoment B node2198 node2198Labels := by
  calc
    mixedMoment B raw33961 raw33961Labels = mixedMoment B raw33961step0 raw33961step0Labels := by
      have ha : raw33961step0 = (fun i j => raw33961 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33961step0 raw33961; decide +kernel
      have hl : raw33961step0Labels = raw33961Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33961 raw33961Labels permutation164 permutation7
    mixedMoment B raw33961step0 raw33961step0Labels = mixedMoment B raw33961step1 raw33961step1Labels := by
      have ha : raw33961step1 = -raw33961step0 := by apply Matrix.ext; change ∀ i j, raw33961step1 i j = -(raw33961step0 i j); unfold raw33961step1 raw33961step0; decide +kernel
      have hl : raw33961step1Labels = raw33961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33961step1 raw33961step1Labels = mixedMoment B raw33961step2 raw33961step2Labels := by
      have ha : raw33961step2 = raw33961step1 := by apply Matrix.ext; unfold raw33961step2 raw33961step1; decide +kernel
      have hl : raw33961step1Labels = labelEmbedding1 ∘ raw33961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33961step1 raw33961step1Labels raw33961step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2198 node2198Labels := by rfl

theorem canonical33962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33962 raw33962Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw33962 raw33962Labels = mixedMoment B raw33962step0 raw33962step0Labels := by
      have ha : raw33962step0 = (fun i j => raw33962 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33962step0 raw33962; decide +kernel
      have hl : raw33962step0Labels = raw33962Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33962 raw33962Labels permutation164 permutation7
    mixedMoment B raw33962step0 raw33962step0Labels = mixedMoment B raw33962step1 raw33962step1Labels := by
      have ha : raw33962step1 = -raw33962step0 := by apply Matrix.ext; change ∀ i j, raw33962step1 i j = -(raw33962step0 i j); unfold raw33962step1 raw33962step0; decide +kernel
      have hl : raw33962step1Labels = raw33962step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33962step1 raw33962step1Labels = mixedMoment B raw33962step2 raw33962step2Labels := by
      have ha : raw33962step2 = raw33962step1 := by apply Matrix.ext; unfold raw33962step2 raw33962step1; decide +kernel
      have hl : raw33962step1Labels = labelEmbedding1 ∘ raw33962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33962step1 raw33962step1Labels raw33962step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

theorem canonical33963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33963 raw33963Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw33963 raw33963Labels = mixedMoment B raw33963step0 raw33963step0Labels := by
      have hz : ∀ j, raw33963 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33963step0 = (fun i j => raw33963 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33963step0 raw33963; decide +kernel
      have hl : raw33963step0Labels = raw33963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33963 raw33963Labels permutation520 hz
    mixedMoment B raw33963step0 raw33963step0Labels = mixedMoment B raw33963step1 raw33963step1Labels := by
      have ha : raw33963step1 = (fun i j => raw33963step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33963step1 raw33963step0; decide +kernel
      have hl : raw33963step1Labels = raw33963step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33963step0 raw33963step0Labels permutation32 permutation7
    mixedMoment B raw33963step1 raw33963step1Labels = mixedMoment B raw33963step2 raw33963step2Labels := by
      have ha : raw33963step2 = -raw33963step1 := by apply Matrix.ext; change ∀ i j, raw33963step2 i j = -(raw33963step1 i j); unfold raw33963step2 raw33963step1; decide +kernel
      have hl : raw33963step2Labels = raw33963step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33963step2 raw33963step2Labels = mixedMoment B raw33963step3 raw33963step3Labels := by
      have ha : raw33963step3 = raw33963step2 := by apply Matrix.ext; unfold raw33963step3 raw33963step2; decide +kernel
      have hl : raw33963step2Labels = labelEmbedding1 ∘ raw33963step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33963step2 raw33963step2Labels raw33963step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical33964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33964 raw33964Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw33964 raw33964Labels = mixedMoment B raw33964step0 raw33964step0Labels := by
      have ha : raw33964step0 = (fun i j => raw33964 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33964step0 raw33964; decide +kernel
      have hl : raw33964step0Labels = raw33964Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33964 raw33964Labels permutation154 permutation2
    _ = mixedMoment B node3376 node3376Labels := by rfl

theorem canonical33965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33965 raw33965Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw33965 raw33965Labels = mixedMoment B raw33965step0 raw33965step0Labels := by
      have ha : raw33965step0 = (fun i j => raw33965 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33965step0 raw33965; decide +kernel
      have hl : raw33965step0Labels = raw33965Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33965 raw33965Labels permutation154 permutation2
    _ = mixedMoment B node2020 node2020Labels := by rfl

theorem canonical33966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33966 raw33966Labels = mixedMoment B node1805 node1805Labels := by
  calc
    mixedMoment B raw33966 raw33966Labels = mixedMoment B raw33966step0 raw33966step0Labels := by
      have ha : raw33966step0 = (fun i j => raw33966 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33966step0 raw33966; decide +kernel
      have hl : raw33966step0Labels = raw33966Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33966 raw33966Labels permutation164 permutation2
    _ = mixedMoment B node1805 node1805Labels := by rfl

theorem canonical33967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33967 raw33967Labels = mixedMoment B node1792 node1792Labels := by
  calc
    mixedMoment B raw33967 raw33967Labels = mixedMoment B raw33967step0 raw33967step0Labels := by
      have ha : raw33967step0 = (fun i j => raw33967 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33967step0 raw33967; decide +kernel
      have hl : raw33967step0Labels = raw33967Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33967 raw33967Labels permutation154 permutation2
    _ = mixedMoment B node1792 node1792Labels := by rfl

theorem canonical33968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33968 raw33968Labels = mixedMoment B node1794 node1794Labels := by
  calc
    _ = mixedMoment B node1794 node1794Labels := by rfl

theorem canonical33969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33969 raw33969Labels = mixedMoment B node1790 node1790Labels := by
  calc
    mixedMoment B raw33969 raw33969Labels = mixedMoment B raw33969step0 raw33969step0Labels := by
      have ha : raw33969step0 = (fun i j => raw33969 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33969step0 raw33969; decide +kernel
      have hl : raw33969step0Labels = raw33969Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33969 raw33969Labels permutation154 permutation2
    _ = mixedMoment B node1790 node1790Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical266
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34049 raw34049Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw34049 raw34049Labels = mixedMoment B raw34049step0 raw34049step0Labels := by
      have ha : raw34049step0 = (fun i j => raw34049 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34049step0 raw34049; decide +kernel
      have hl : raw34049step0Labels = raw34049Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34049 raw34049Labels permutation160 permutation7
    mixedMoment B raw34049step0 raw34049step0Labels = mixedMoment B raw34049step1 raw34049step1Labels := by
      have ha : raw34049step1 = -raw34049step0 := by apply Matrix.ext; change ∀ i j, raw34049step1 i j = -(raw34049step0 i j); unfold raw34049step1 raw34049step0; decide +kernel
      have hl : raw34049step1Labels = raw34049step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34049step1 raw34049step1Labels = mixedMoment B raw34049step2 raw34049step2Labels := by
      have ha : raw34049step2 = raw34049step1 := by apply Matrix.ext; unfold raw34049step2 raw34049step1; decide +kernel
      have hl : raw34049step1Labels = labelEmbedding1 ∘ raw34049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34049step1 raw34049step1Labels raw34049step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

theorem canonical34050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34050 raw34050Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw34050 raw34050Labels = mixedMoment B raw34050step0 raw34050step0Labels := by
      have ha : raw34050step0 = (fun i j => raw34050 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34050step0 raw34050; decide +kernel
      have hl : raw34050step0Labels = raw34050Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34050 raw34050Labels permutation160 permutation7
    mixedMoment B raw34050step0 raw34050step0Labels = mixedMoment B raw34050step1 raw34050step1Labels := by
      have ha : raw34050step1 = -raw34050step0 := by apply Matrix.ext; change ∀ i j, raw34050step1 i j = -(raw34050step0 i j); unfold raw34050step1 raw34050step0; decide +kernel
      have hl : raw34050step1Labels = raw34050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34050step1 raw34050step1Labels = mixedMoment B raw34050step2 raw34050step2Labels := by
      have ha : raw34050step2 = raw34050step1 := by apply Matrix.ext; unfold raw34050step2 raw34050step1; decide +kernel
      have hl : raw34050step1Labels = labelEmbedding1 ∘ raw34050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34050step1 raw34050step1Labels raw34050step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2708 node2708Labels := by rfl

theorem canonical34051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34051 raw34051Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw34051 raw34051Labels = mixedMoment B raw34051step0 raw34051step0Labels := by
      have hz : ∀ j, raw34051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34051step0 = (fun i j => raw34051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34051step0 raw34051; decide +kernel
      have hl : raw34051step0Labels = raw34051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34051 raw34051Labels permutation434 hz
    mixedMoment B raw34051step0 raw34051step0Labels = mixedMoment B raw34051step1 raw34051step1Labels := by
      have ha : raw34051step1 = (fun i j => raw34051step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34051step1 raw34051step0; decide +kernel
      have hl : raw34051step1Labels = raw34051step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34051step0 raw34051step0Labels permutation34 permutation7
    mixedMoment B raw34051step1 raw34051step1Labels = mixedMoment B raw34051step2 raw34051step2Labels := by
      have ha : raw34051step2 = -raw34051step1 := by apply Matrix.ext; change ∀ i j, raw34051step2 i j = -(raw34051step1 i j); unfold raw34051step2 raw34051step1; decide +kernel
      have hl : raw34051step2Labels = raw34051step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34051step2 raw34051step2Labels = mixedMoment B raw34051step3 raw34051step3Labels := by
      have ha : raw34051step3 = raw34051step2 := by apply Matrix.ext; unfold raw34051step3 raw34051step2; decide +kernel
      have hl : raw34051step2Labels = labelEmbedding1 ∘ raw34051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34051step2 raw34051step2Labels raw34051step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical34052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34052 raw34052Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw34052 raw34052Labels = mixedMoment B raw34052step0 raw34052step0Labels := by
      have hz : ∀ j, raw34052 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34052step0 = (fun i j => raw34052 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34052step0 raw34052; decide +kernel
      have hl : raw34052step0Labels = raw34052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34052 raw34052Labels permutation520 hz
    mixedMoment B raw34052step0 raw34052step0Labels = mixedMoment B raw34052step1 raw34052step1Labels := by
      have ha : raw34052step1 = (fun i j => raw34052step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34052step1 raw34052step0; decide +kernel
      have hl : raw34052step1Labels = raw34052step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34052step0 raw34052step0Labels permutation34 permutation7
    mixedMoment B raw34052step1 raw34052step1Labels = mixedMoment B raw34052step2 raw34052step2Labels := by
      have ha : raw34052step2 = -raw34052step1 := by apply Matrix.ext; change ∀ i j, raw34052step2 i j = -(raw34052step1 i j); unfold raw34052step2 raw34052step1; decide +kernel
      have hl : raw34052step2Labels = raw34052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34052step2 raw34052step2Labels = mixedMoment B raw34052step3 raw34052step3Labels := by
      have ha : raw34052step3 = raw34052step2 := by apply Matrix.ext; unfold raw34052step3 raw34052step2; decide +kernel
      have hl : raw34052step2Labels = labelEmbedding1 ∘ raw34052step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34052step2 raw34052step2Labels raw34052step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical34053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34053 raw34053Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw34053 raw34053Labels = mixedMoment B raw34053step0 raw34053step0Labels := by
      have ha : raw34053step0 = (fun i j => raw34053 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34053step0 raw34053; decide +kernel
      have hl : raw34053step0Labels = raw34053Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34053 raw34053Labels permutation160 permutation7
    mixedMoment B raw34053step0 raw34053step0Labels = mixedMoment B raw34053step1 raw34053step1Labels := by
      have ha : raw34053step1 = -raw34053step0 := by apply Matrix.ext; change ∀ i j, raw34053step1 i j = -(raw34053step0 i j); unfold raw34053step1 raw34053step0; decide +kernel
      have hl : raw34053step1Labels = raw34053step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34053step1 raw34053step1Labels = mixedMoment B raw34053step2 raw34053step2Labels := by
      have ha : raw34053step2 = raw34053step1 := by apply Matrix.ext; unfold raw34053step2 raw34053step1; decide +kernel
      have hl : raw34053step1Labels = labelEmbedding1 ∘ raw34053step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34053step1 raw34053step1Labels raw34053step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2709 node2709Labels := by rfl

theorem canonical34054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34054 raw34054Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw34054 raw34054Labels = mixedMoment B raw34054step0 raw34054step0Labels := by
      have hz : ∀ j, raw34054 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34054step0 = (fun i j => raw34054 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34054step0 raw34054; decide +kernel
      have hl : raw34054step0Labels = raw34054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34054 raw34054Labels permutation265 hz
    mixedMoment B raw34054step0 raw34054step0Labels = mixedMoment B raw34054step1 raw34054step1Labels := by
      have ha : raw34054step1 = (fun i j => raw34054step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34054step1 raw34054step0; decide +kernel
      have hl : raw34054step1Labels = raw34054step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34054step0 raw34054step0Labels permutation40 permutation7
    mixedMoment B raw34054step1 raw34054step1Labels = mixedMoment B raw34054step2 raw34054step2Labels := by
      have ha : raw34054step2 = -raw34054step1 := by apply Matrix.ext; change ∀ i j, raw34054step2 i j = -(raw34054step1 i j); unfold raw34054step2 raw34054step1; decide +kernel
      have hl : raw34054step2Labels = raw34054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34054step2 raw34054step2Labels = mixedMoment B raw34054step3 raw34054step3Labels := by
      have ha : raw34054step3 = raw34054step2 := by apply Matrix.ext; unfold raw34054step3 raw34054step2; decide +kernel
      have hl : raw34054step2Labels = labelEmbedding1 ∘ raw34054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34054step2 raw34054step2Labels raw34054step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical34055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34055 raw34055Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw34055 raw34055Labels = mixedMoment B raw34055step0 raw34055step0Labels := by
      have hz : ∀ j, raw34055 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34055step0 = (fun i j => raw34055 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34055step0 raw34055; decide +kernel
      have hl : raw34055step0Labels = raw34055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34055 raw34055Labels permutation265 hz
    mixedMoment B raw34055step0 raw34055step0Labels = mixedMoment B raw34055step1 raw34055step1Labels := by
      have ha : raw34055step1 = (fun i j => raw34055step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34055step1 raw34055step0; decide +kernel
      have hl : raw34055step1Labels = raw34055step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34055step0 raw34055step0Labels permutation40 permutation7
    mixedMoment B raw34055step1 raw34055step1Labels = mixedMoment B raw34055step2 raw34055step2Labels := by
      have ha : raw34055step2 = -raw34055step1 := by apply Matrix.ext; change ∀ i j, raw34055step2 i j = -(raw34055step1 i j); unfold raw34055step2 raw34055step1; decide +kernel
      have hl : raw34055step2Labels = raw34055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34055step2 raw34055step2Labels = mixedMoment B raw34055step3 raw34055step3Labels := by
      have ha : raw34055step3 = raw34055step2 := by apply Matrix.ext; unfold raw34055step3 raw34055step2; decide +kernel
      have hl : raw34055step2Labels = labelEmbedding1 ∘ raw34055step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34055step2 raw34055step2Labels raw34055step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical34056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34056 raw34056Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw34056 raw34056Labels = mixedMoment B raw34056step0 raw34056step0Labels := by
      have hz : ∀ j, raw34056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34056step0 = (fun i j => raw34056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34056step0 raw34056; decide +kernel
      have hl : raw34056step0Labels = raw34056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34056 raw34056Labels permutation434 hz
    mixedMoment B raw34056step0 raw34056step0Labels = mixedMoment B raw34056step1 raw34056step1Labels := by
      have hz : ∀ j, raw34056step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34056step1 = (fun i j => raw34056step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34056step1 raw34056step0; decide +kernel
      have hl : raw34056step1Labels = raw34056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34056step0 raw34056step0Labels permutation56 hz
    mixedMoment B raw34056step1 raw34056step1Labels = mixedMoment B raw34056step2 raw34056step2Labels := by
      have ha : raw34056step2 = (fun i j => raw34056step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34056step2 raw34056step1; decide +kernel
      have hl : raw34056step2Labels = raw34056step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34056step1 raw34056step1Labels permutation10 permutation7
    mixedMoment B raw34056step2 raw34056step2Labels = mixedMoment B raw34056step3 raw34056step3Labels := by
      have ha : raw34056step3 = -raw34056step2 := by apply Matrix.ext; change ∀ i j, raw34056step3 i j = -(raw34056step2 i j); unfold raw34056step3 raw34056step2; decide +kernel
      have hl : raw34056step3Labels = raw34056step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34056step3 raw34056step3Labels = mixedMoment B raw34056step4 raw34056step4Labels := by
      have ha : raw34056step4 = raw34056step3 := by apply Matrix.ext; unfold raw34056step4 raw34056step3; decide +kernel
      have hl : raw34056step3Labels = labelEmbedding1 ∘ raw34056step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34056step3 raw34056step3Labels raw34056step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical34057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34057 raw34057Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw34057 raw34057Labels = mixedMoment B raw34057step0 raw34057step0Labels := by
      have hz : ∀ j, raw34057 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34057step0 = (fun i j => raw34057 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34057step0 raw34057; decide +kernel
      have hl : raw34057step0Labels = raw34057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34057 raw34057Labels permutation520 hz
    mixedMoment B raw34057step0 raw34057step0Labels = mixedMoment B raw34057step1 raw34057step1Labels := by
      have hz : ∀ j, raw34057step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34057step1 = (fun i j => raw34057step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34057step1 raw34057step0; decide +kernel
      have hl : raw34057step1Labels = raw34057step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34057step0 raw34057step0Labels permutation56 hz
    mixedMoment B raw34057step1 raw34057step1Labels = mixedMoment B raw34057step2 raw34057step2Labels := by
      have ha : raw34057step2 = (fun i j => raw34057step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34057step2 raw34057step1; decide +kernel
      have hl : raw34057step2Labels = raw34057step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34057step1 raw34057step1Labels permutation10 permutation7
    mixedMoment B raw34057step2 raw34057step2Labels = mixedMoment B raw34057step3 raw34057step3Labels := by
      have ha : raw34057step3 = -raw34057step2 := by apply Matrix.ext; change ∀ i j, raw34057step3 i j = -(raw34057step2 i j); unfold raw34057step3 raw34057step2; decide +kernel
      have hl : raw34057step3Labels = raw34057step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34057step3 raw34057step3Labels = mixedMoment B raw34057step4 raw34057step4Labels := by
      have ha : raw34057step4 = raw34057step3 := by apply Matrix.ext; unfold raw34057step4 raw34057step3; decide +kernel
      have hl : raw34057step3Labels = labelEmbedding1 ∘ raw34057step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34057step3 raw34057step3Labels raw34057step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical34058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34058 raw34058Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw34058 raw34058Labels = mixedMoment B raw34058step0 raw34058step0Labels := by
      have hz : ∀ j, raw34058 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34058step0 = (fun i j => raw34058 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34058step0 raw34058; decide +kernel
      have hl : raw34058step0Labels = raw34058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34058 raw34058Labels permutation265 hz
    mixedMoment B raw34058step0 raw34058step0Labels = mixedMoment B raw34058step1 raw34058step1Labels := by
      have ha : raw34058step1 = (fun i j => raw34058step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34058step1 raw34058step0; decide +kernel
      have hl : raw34058step1Labels = raw34058step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34058step0 raw34058step0Labels permutation40 permutation7
    mixedMoment B raw34058step1 raw34058step1Labels = mixedMoment B raw34058step2 raw34058step2Labels := by
      have ha : raw34058step2 = -raw34058step1 := by apply Matrix.ext; change ∀ i j, raw34058step2 i j = -(raw34058step1 i j); unfold raw34058step2 raw34058step1; decide +kernel
      have hl : raw34058step2Labels = raw34058step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34058step2 raw34058step2Labels = mixedMoment B raw34058step3 raw34058step3Labels := by
      have ha : raw34058step3 = raw34058step2 := by apply Matrix.ext; unfold raw34058step3 raw34058step2; decide +kernel
      have hl : raw34058step2Labels = labelEmbedding1 ∘ raw34058step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34058step2 raw34058step2Labels raw34058step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical34059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34059 raw34059Labels = mixedMoment B node1664 node1664Labels := by
  calc
    mixedMoment B raw34059 raw34059Labels = mixedMoment B raw34059step0 raw34059step0Labels := by
      have ha : raw34059step0 = (fun i j => raw34059 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34059step0 raw34059; decide +kernel
      have hl : raw34059step0Labels = raw34059Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34059 raw34059Labels permutation160 permutation7
    mixedMoment B raw34059step0 raw34059step0Labels = mixedMoment B raw34059step1 raw34059step1Labels := by
      have ha : raw34059step1 = -raw34059step0 := by apply Matrix.ext; change ∀ i j, raw34059step1 i j = -(raw34059step0 i j); unfold raw34059step1 raw34059step0; decide +kernel
      have hl : raw34059step1Labels = raw34059step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34059step1 raw34059step1Labels = mixedMoment B raw34059step2 raw34059step2Labels := by
      have ha : raw34059step2 = raw34059step1 := by apply Matrix.ext; unfold raw34059step2 raw34059step1; decide +kernel
      have hl : raw34059step1Labels = labelEmbedding1 ∘ raw34059step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34059step1 raw34059step1Labels raw34059step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1664 node1664Labels := by rfl

theorem canonical34060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34060 raw34060Labels = mixedMoment B node2141 node2141Labels := by
  calc
    mixedMoment B raw34060 raw34060Labels = mixedMoment B raw34060step0 raw34060step0Labels := by
      have ha : raw34060step0 = (fun i j => raw34060 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34060step0 raw34060; decide +kernel
      have hl : raw34060step0Labels = raw34060Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34060 raw34060Labels permutation160 permutation7
    mixedMoment B raw34060step0 raw34060step0Labels = mixedMoment B raw34060step1 raw34060step1Labels := by
      have ha : raw34060step1 = -raw34060step0 := by apply Matrix.ext; change ∀ i j, raw34060step1 i j = -(raw34060step0 i j); unfold raw34060step1 raw34060step0; decide +kernel
      have hl : raw34060step1Labels = raw34060step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34060step1 raw34060step1Labels = mixedMoment B raw34060step2 raw34060step2Labels := by
      have ha : raw34060step2 = raw34060step1 := by apply Matrix.ext; unfold raw34060step2 raw34060step1; decide +kernel
      have hl : raw34060step1Labels = labelEmbedding1 ∘ raw34060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34060step1 raw34060step1Labels raw34060step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2141 node2141Labels := by rfl

theorem canonical34061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34061 raw34061Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw34061 raw34061Labels = mixedMoment B raw34061step0 raw34061step0Labels := by
      have hz : ∀ j, raw34061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34061step0 = (fun i j => raw34061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34061step0 raw34061; decide +kernel
      have hl : raw34061step0Labels = raw34061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34061 raw34061Labels permutation434 hz
    mixedMoment B raw34061step0 raw34061step0Labels = mixedMoment B raw34061step1 raw34061step1Labels := by
      have ha : raw34061step1 = (fun i j => raw34061step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34061step1 raw34061step0; decide +kernel
      have hl : raw34061step1Labels = raw34061step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34061step0 raw34061step0Labels permutation34 permutation7
    mixedMoment B raw34061step1 raw34061step1Labels = mixedMoment B raw34061step2 raw34061step2Labels := by
      have ha : raw34061step2 = -raw34061step1 := by apply Matrix.ext; change ∀ i j, raw34061step2 i j = -(raw34061step1 i j); unfold raw34061step2 raw34061step1; decide +kernel
      have hl : raw34061step2Labels = raw34061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34061step2 raw34061step2Labels = mixedMoment B raw34061step3 raw34061step3Labels := by
      have ha : raw34061step3 = raw34061step2 := by apply Matrix.ext; unfold raw34061step3 raw34061step2; decide +kernel
      have hl : raw34061step2Labels = labelEmbedding1 ∘ raw34061step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34061step2 raw34061step2Labels raw34061step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical34062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34062 raw34062Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw34062 raw34062Labels = mixedMoment B raw34062step0 raw34062step0Labels := by
      have hz : ∀ j, raw34062 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34062step0 = (fun i j => raw34062 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34062step0 raw34062; decide +kernel
      have hl : raw34062step0Labels = raw34062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34062 raw34062Labels permutation520 hz
    mixedMoment B raw34062step0 raw34062step0Labels = mixedMoment B raw34062step1 raw34062step1Labels := by
      have ha : raw34062step1 = (fun i j => raw34062step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34062step1 raw34062step0; decide +kernel
      have hl : raw34062step1Labels = raw34062step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34062step0 raw34062step0Labels permutation34 permutation7
    mixedMoment B raw34062step1 raw34062step1Labels = mixedMoment B raw34062step2 raw34062step2Labels := by
      have ha : raw34062step2 = -raw34062step1 := by apply Matrix.ext; change ∀ i j, raw34062step2 i j = -(raw34062step1 i j); unfold raw34062step2 raw34062step1; decide +kernel
      have hl : raw34062step2Labels = raw34062step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34062step2 raw34062step2Labels = mixedMoment B raw34062step3 raw34062step3Labels := by
      have ha : raw34062step3 = raw34062step2 := by apply Matrix.ext; unfold raw34062step3 raw34062step2; decide +kernel
      have hl : raw34062step2Labels = labelEmbedding1 ∘ raw34062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34062step2 raw34062step2Labels raw34062step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical34063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34063 raw34063Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw34063 raw34063Labels = mixedMoment B raw34063step0 raw34063step0Labels := by
      have ha : raw34063step0 = (fun i j => raw34063 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34063step0 raw34063; decide +kernel
      have hl : raw34063step0Labels = raw34063Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34063 raw34063Labels permutation160 permutation7
    mixedMoment B raw34063step0 raw34063step0Labels = mixedMoment B raw34063step1 raw34063step1Labels := by
      have ha : raw34063step1 = -raw34063step0 := by apply Matrix.ext; change ∀ i j, raw34063step1 i j = -(raw34063step0 i j); unfold raw34063step1 raw34063step0; decide +kernel
      have hl : raw34063step1Labels = raw34063step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34063step1 raw34063step1Labels = mixedMoment B raw34063step2 raw34063step2Labels := by
      have ha : raw34063step2 = raw34063step1 := by apply Matrix.ext; unfold raw34063step2 raw34063step1; decide +kernel
      have hl : raw34063step1Labels = labelEmbedding1 ∘ raw34063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34063step1 raw34063step1Labels raw34063step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical34064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34064 raw34064Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw34064 raw34064Labels = mixedMoment B raw34064step0 raw34064step0Labels := by
      have ha : raw34064step0 = (fun i j => raw34064 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34064step0 raw34064; decide +kernel
      have hl : raw34064step0Labels = raw34064Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34064 raw34064Labels permutation166 permutation7
    mixedMoment B raw34064step0 raw34064step0Labels = mixedMoment B raw34064step1 raw34064step1Labels := by
      have ha : raw34064step1 = -raw34064step0 := by apply Matrix.ext; change ∀ i j, raw34064step1 i j = -(raw34064step0 i j); unfold raw34064step1 raw34064step0; decide +kernel
      have hl : raw34064step1Labels = raw34064step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34064step1 raw34064step1Labels = mixedMoment B raw34064step2 raw34064step2Labels := by
      have ha : raw34064step2 = raw34064step1 := by apply Matrix.ext; unfold raw34064step2 raw34064step1; decide +kernel
      have hl : raw34064step1Labels = labelEmbedding1 ∘ raw34064step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34064step1 raw34064step1Labels raw34064step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

theorem canonical34065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34065 raw34065Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw34065 raw34065Labels = mixedMoment B raw34065step0 raw34065step0Labels := by
      have ha : raw34065step0 = (fun i j => raw34065 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34065step0 raw34065; decide +kernel
      have hl : raw34065step0Labels = raw34065Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34065 raw34065Labels permutation166 permutation7
    mixedMoment B raw34065step0 raw34065step0Labels = mixedMoment B raw34065step1 raw34065step1Labels := by
      have ha : raw34065step1 = -raw34065step0 := by apply Matrix.ext; change ∀ i j, raw34065step1 i j = -(raw34065step0 i j); unfold raw34065step1 raw34065step0; decide +kernel
      have hl : raw34065step1Labels = raw34065step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34065step1 raw34065step1Labels = mixedMoment B raw34065step2 raw34065step2Labels := by
      have ha : raw34065step2 = raw34065step1 := by apply Matrix.ext; unfold raw34065step2 raw34065step1; decide +kernel
      have hl : raw34065step1Labels = labelEmbedding1 ∘ raw34065step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34065step1 raw34065step1Labels raw34065step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2144 node2144Labels := by rfl

theorem canonical34066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34066 raw34066Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw34066 raw34066Labels = mixedMoment B raw34066step0 raw34066step0Labels := by
      have ha : raw34066step0 = (fun i j => raw34066 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34066step0 raw34066; decide +kernel
      have hl : raw34066step0Labels = raw34066Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34066 raw34066Labels permutation166 permutation7
    mixedMoment B raw34066step0 raw34066step0Labels = mixedMoment B raw34066step1 raw34066step1Labels := by
      have ha : raw34066step1 = -raw34066step0 := by apply Matrix.ext; change ∀ i j, raw34066step1 i j = -(raw34066step0 i j); unfold raw34066step1 raw34066step0; decide +kernel
      have hl : raw34066step1Labels = raw34066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34066step1 raw34066step1Labels = mixedMoment B raw34066step2 raw34066step2Labels := by
      have ha : raw34066step2 = raw34066step1 := by apply Matrix.ext; unfold raw34066step2 raw34066step1; decide +kernel
      have hl : raw34066step1Labels = labelEmbedding1 ∘ raw34066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34066step1 raw34066step1Labels raw34066step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

theorem canonical34067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34067 raw34067Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw34067 raw34067Labels = mixedMoment B raw34067step0 raw34067step0Labels := by
      have hz : ∀ j, raw34067 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34067step0 = (fun i j => raw34067 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34067step0 raw34067; decide +kernel
      have hl : raw34067step0Labels = raw34067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34067 raw34067Labels permutation520 hz
    mixedMoment B raw34067step0 raw34067step0Labels = mixedMoment B raw34067step1 raw34067step1Labels := by
      have ha : raw34067step1 = (fun i j => raw34067step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34067step1 raw34067step0; decide +kernel
      have hl : raw34067step1Labels = raw34067step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34067step0 raw34067step0Labels permutation34 permutation7
    mixedMoment B raw34067step1 raw34067step1Labels = mixedMoment B raw34067step2 raw34067step2Labels := by
      have ha : raw34067step2 = -raw34067step1 := by apply Matrix.ext; change ∀ i j, raw34067step2 i j = -(raw34067step1 i j); unfold raw34067step2 raw34067step1; decide +kernel
      have hl : raw34067step2Labels = raw34067step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34067step2 raw34067step2Labels = mixedMoment B raw34067step3 raw34067step3Labels := by
      have ha : raw34067step3 = raw34067step2 := by apply Matrix.ext; unfold raw34067step3 raw34067step2; decide +kernel
      have hl : raw34067step2Labels = labelEmbedding1 ∘ raw34067step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34067step2 raw34067step2Labels raw34067step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical34068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34068 raw34068Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw34068 raw34068Labels = mixedMoment B raw34068step0 raw34068step0Labels := by
      have ha : raw34068step0 = (fun i j => raw34068 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34068step0 raw34068; decide +kernel
      have hl : raw34068step0Labels = raw34068Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34068 raw34068Labels permutation166 permutation7
    mixedMoment B raw34068step0 raw34068step0Labels = mixedMoment B raw34068step1 raw34068step1Labels := by
      have ha : raw34068step1 = -raw34068step0 := by apply Matrix.ext; change ∀ i j, raw34068step1 i j = -(raw34068step0 i j); unfold raw34068step1 raw34068step0; decide +kernel
      have hl : raw34068step1Labels = raw34068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34068step1 raw34068step1Labels = mixedMoment B raw34068step2 raw34068step2Labels := by
      have ha : raw34068step2 = raw34068step1 := by apply Matrix.ext; unfold raw34068step2 raw34068step1; decide +kernel
      have hl : raw34068step1Labels = labelEmbedding1 ∘ raw34068step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34068step1 raw34068step1Labels raw34068step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical34069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34069 raw34069Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw34069 raw34069Labels = mixedMoment B raw34069step0 raw34069step0Labels := by
      have ha : raw34069step0 = (fun i j => raw34069 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34069step0 raw34069; decide +kernel
      have hl : raw34069step0Labels = raw34069Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34069 raw34069Labels permutation160 permutation7
    mixedMoment B raw34069step0 raw34069step0Labels = mixedMoment B raw34069step1 raw34069step1Labels := by
      have ha : raw34069step1 = -raw34069step0 := by apply Matrix.ext; change ∀ i j, raw34069step1 i j = -(raw34069step0 i j); unfold raw34069step1 raw34069step0; decide +kernel
      have hl : raw34069step1Labels = raw34069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34069step1 raw34069step1Labels = mixedMoment B raw34069step2 raw34069step2Labels := by
      have ha : raw34069step2 = raw34069step1 := by apply Matrix.ext; unfold raw34069step2 raw34069step1; decide +kernel
      have hl : raw34069step1Labels = labelEmbedding1 ∘ raw34069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34069step1 raw34069step1Labels raw34069step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

theorem canonical34070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34070 raw34070Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw34070 raw34070Labels = mixedMoment B raw34070step0 raw34070step0Labels := by
      have ha : raw34070step0 = (fun i j => raw34070 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34070step0 raw34070; decide +kernel
      have hl : raw34070step0Labels = raw34070Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34070 raw34070Labels permutation160 permutation7
    mixedMoment B raw34070step0 raw34070step0Labels = mixedMoment B raw34070step1 raw34070step1Labels := by
      have ha : raw34070step1 = -raw34070step0 := by apply Matrix.ext; change ∀ i j, raw34070step1 i j = -(raw34070step0 i j); unfold raw34070step1 raw34070step0; decide +kernel
      have hl : raw34070step1Labels = raw34070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34070step1 raw34070step1Labels = mixedMoment B raw34070step2 raw34070step2Labels := by
      have ha : raw34070step2 = raw34070step1 := by apply Matrix.ext; unfold raw34070step2 raw34070step1; decide +kernel
      have hl : raw34070step1Labels = labelEmbedding1 ∘ raw34070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34070step1 raw34070step1Labels raw34070step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2144 node2144Labels := by rfl

theorem canonical34071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34071 raw34071Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw34071 raw34071Labels = mixedMoment B raw34071step0 raw34071step0Labels := by
      have ha : raw34071step0 = (fun i j => raw34071 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34071step0 raw34071; decide +kernel
      have hl : raw34071step0Labels = raw34071Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34071 raw34071Labels permutation160 permutation7
    mixedMoment B raw34071step0 raw34071step0Labels = mixedMoment B raw34071step1 raw34071step1Labels := by
      have ha : raw34071step1 = -raw34071step0 := by apply Matrix.ext; change ∀ i j, raw34071step1 i j = -(raw34071step0 i j); unfold raw34071step1 raw34071step0; decide +kernel
      have hl : raw34071step1Labels = raw34071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34071step1 raw34071step1Labels = mixedMoment B raw34071step2 raw34071step2Labels := by
      have ha : raw34071step2 = raw34071step1 := by apply Matrix.ext; unfold raw34071step2 raw34071step1; decide +kernel
      have hl : raw34071step1Labels = labelEmbedding1 ∘ raw34071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34071step1 raw34071step1Labels raw34071step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

theorem canonical34072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34072 raw34072Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw34072 raw34072Labels = mixedMoment B raw34072step0 raw34072step0Labels := by
      have hz : ∀ j, raw34072 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34072step0 = (fun i j => raw34072 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34072step0 raw34072; decide +kernel
      have hl : raw34072step0Labels = raw34072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34072 raw34072Labels permutation434 hz
    mixedMoment B raw34072step0 raw34072step0Labels = mixedMoment B raw34072step1 raw34072step1Labels := by
      have ha : raw34072step1 = (fun i j => raw34072step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34072step1 raw34072step0; decide +kernel
      have hl : raw34072step1Labels = raw34072step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34072step0 raw34072step0Labels permutation34 permutation7
    mixedMoment B raw34072step1 raw34072step1Labels = mixedMoment B raw34072step2 raw34072step2Labels := by
      have ha : raw34072step2 = -raw34072step1 := by apply Matrix.ext; change ∀ i j, raw34072step2 i j = -(raw34072step1 i j); unfold raw34072step2 raw34072step1; decide +kernel
      have hl : raw34072step2Labels = raw34072step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34072step2 raw34072step2Labels = mixedMoment B raw34072step3 raw34072step3Labels := by
      have ha : raw34072step3 = raw34072step2 := by apply Matrix.ext; unfold raw34072step3 raw34072step2; decide +kernel
      have hl : raw34072step2Labels = labelEmbedding1 ∘ raw34072step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34072step2 raw34072step2Labels raw34072step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical34073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34073 raw34073Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw34073 raw34073Labels = mixedMoment B raw34073step0 raw34073step0Labels := by
      have ha : raw34073step0 = (fun i j => raw34073 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34073step0 raw34073; decide +kernel
      have hl : raw34073step0Labels = raw34073Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34073 raw34073Labels permutation160 permutation7
    mixedMoment B raw34073step0 raw34073step0Labels = mixedMoment B raw34073step1 raw34073step1Labels := by
      have ha : raw34073step1 = -raw34073step0 := by apply Matrix.ext; change ∀ i j, raw34073step1 i j = -(raw34073step0 i j); unfold raw34073step1 raw34073step0; decide +kernel
      have hl : raw34073step1Labels = raw34073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34073step1 raw34073step1Labels = mixedMoment B raw34073step2 raw34073step2Labels := by
      have ha : raw34073step2 = raw34073step1 := by apply Matrix.ext; unfold raw34073step2 raw34073step1; decide +kernel
      have hl : raw34073step1Labels = labelEmbedding1 ∘ raw34073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34073step1 raw34073step1Labels raw34073step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical34074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34074 raw34074Labels = mixedMoment B node1663 node1663Labels := by
  calc
    mixedMoment B raw34074 raw34074Labels = mixedMoment B raw34074step0 raw34074step0Labels := by
      have ha : raw34074step0 = (fun i j => raw34074 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34074step0 raw34074; decide +kernel
      have hl : raw34074step0Labels = raw34074Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34074 raw34074Labels permutation160 permutation7
    mixedMoment B raw34074step0 raw34074step0Labels = mixedMoment B raw34074step1 raw34074step1Labels := by
      have ha : raw34074step1 = -raw34074step0 := by apply Matrix.ext; change ∀ i j, raw34074step1 i j = -(raw34074step0 i j); unfold raw34074step1 raw34074step0; decide +kernel
      have hl : raw34074step1Labels = raw34074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34074step1 raw34074step1Labels = mixedMoment B raw34074step2 raw34074step2Labels := by
      have ha : raw34074step2 = raw34074step1 := by apply Matrix.ext; unfold raw34074step2 raw34074step1; decide +kernel
      have hl : raw34074step1Labels = labelEmbedding1 ∘ raw34074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34074step1 raw34074step1Labels raw34074step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1663 node1663Labels := by rfl

theorem canonical34075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34075 raw34075Labels = mixedMoment B node2140 node2140Labels := by
  calc
    mixedMoment B raw34075 raw34075Labels = mixedMoment B raw34075step0 raw34075step0Labels := by
      have ha : raw34075step0 = (fun i j => raw34075 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34075step0 raw34075; decide +kernel
      have hl : raw34075step0Labels = raw34075Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34075 raw34075Labels permutation160 permutation7
    mixedMoment B raw34075step0 raw34075step0Labels = mixedMoment B raw34075step1 raw34075step1Labels := by
      have ha : raw34075step1 = -raw34075step0 := by apply Matrix.ext; change ∀ i j, raw34075step1 i j = -(raw34075step0 i j); unfold raw34075step1 raw34075step0; decide +kernel
      have hl : raw34075step1Labels = raw34075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34075step1 raw34075step1Labels = mixedMoment B raw34075step2 raw34075step2Labels := by
      have ha : raw34075step2 = raw34075step1 := by apply Matrix.ext; unfold raw34075step2 raw34075step1; decide +kernel
      have hl : raw34075step1Labels = labelEmbedding1 ∘ raw34075step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34075step1 raw34075step1Labels raw34075step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2140 node2140Labels := by rfl

theorem canonical34076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34076 raw34076Labels = mixedMoment B node2189 node2189Labels := by
  calc
    mixedMoment B raw34076 raw34076Labels = mixedMoment B raw34076step0 raw34076step0Labels := by
      have ha : raw34076step0 = (fun i j => raw34076 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34076step0 raw34076; decide +kernel
      have hl : raw34076step0Labels = raw34076Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34076 raw34076Labels permutation160 permutation7
    mixedMoment B raw34076step0 raw34076step0Labels = mixedMoment B raw34076step1 raw34076step1Labels := by
      have ha : raw34076step1 = -raw34076step0 := by apply Matrix.ext; change ∀ i j, raw34076step1 i j = -(raw34076step0 i j); unfold raw34076step1 raw34076step0; decide +kernel
      have hl : raw34076step1Labels = raw34076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34076step1 raw34076step1Labels = mixedMoment B raw34076step2 raw34076step2Labels := by
      have ha : raw34076step2 = raw34076step1 := by apply Matrix.ext; unfold raw34076step2 raw34076step1; decide +kernel
      have hl : raw34076step1Labels = labelEmbedding1 ∘ raw34076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34076step1 raw34076step1Labels raw34076step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2189 node2189Labels := by rfl

theorem canonical34077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34077 raw34077Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw34077 raw34077Labels = mixedMoment B raw34077step0 raw34077step0Labels := by
      have hz : ∀ j, raw34077 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34077step0 = (fun i j => raw34077 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34077step0 raw34077; decide +kernel
      have hl : raw34077step0Labels = raw34077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34077 raw34077Labels permutation434 hz
    mixedMoment B raw34077step0 raw34077step0Labels = mixedMoment B raw34077step1 raw34077step1Labels := by
      have ha : raw34077step1 = (fun i j => raw34077step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34077step1 raw34077step0; decide +kernel
      have hl : raw34077step1Labels = raw34077step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34077step0 raw34077step0Labels permutation34 permutation7
    mixedMoment B raw34077step1 raw34077step1Labels = mixedMoment B raw34077step2 raw34077step2Labels := by
      have ha : raw34077step2 = -raw34077step1 := by apply Matrix.ext; change ∀ i j, raw34077step2 i j = -(raw34077step1 i j); unfold raw34077step2 raw34077step1; decide +kernel
      have hl : raw34077step2Labels = raw34077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34077step2 raw34077step2Labels = mixedMoment B raw34077step3 raw34077step3Labels := by
      have ha : raw34077step3 = raw34077step2 := by apply Matrix.ext; unfold raw34077step3 raw34077step2; decide +kernel
      have hl : raw34077step2Labels = labelEmbedding1 ∘ raw34077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34077step2 raw34077step2Labels raw34077step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical34078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34078 raw34078Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw34078 raw34078Labels = mixedMoment B raw34078step0 raw34078step0Labels := by
      have hz : ∀ j, raw34078 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34078step0 = (fun i j => raw34078 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34078step0 raw34078; decide +kernel
      have hl : raw34078step0Labels = raw34078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34078 raw34078Labels permutation520 hz
    mixedMoment B raw34078step0 raw34078step0Labels = mixedMoment B raw34078step1 raw34078step1Labels := by
      have ha : raw34078step1 = (fun i j => raw34078step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34078step1 raw34078step0; decide +kernel
      have hl : raw34078step1Labels = raw34078step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34078step0 raw34078step0Labels permutation34 permutation7
    mixedMoment B raw34078step1 raw34078step1Labels = mixedMoment B raw34078step2 raw34078step2Labels := by
      have ha : raw34078step2 = -raw34078step1 := by apply Matrix.ext; change ∀ i j, raw34078step2 i j = -(raw34078step1 i j); unfold raw34078step2 raw34078step1; decide +kernel
      have hl : raw34078step2Labels = raw34078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34078step2 raw34078step2Labels = mixedMoment B raw34078step3 raw34078step3Labels := by
      have ha : raw34078step3 = raw34078step2 := by apply Matrix.ext; unfold raw34078step3 raw34078step2; decide +kernel
      have hl : raw34078step2Labels = labelEmbedding1 ∘ raw34078step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34078step2 raw34078step2Labels raw34078step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical34126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34126 raw34126Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw34126 raw34126Labels = mixedMoment B raw34126step0 raw34126step0Labels := by
      have hz : ∀ j, raw34126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34126step0 = (fun i j => raw34126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34126step0 raw34126; decide +kernel
      have hl : raw34126step0Labels = raw34126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34126 raw34126Labels permutation346 hz
    mixedMoment B raw34126step0 raw34126step0Labels = mixedMoment B raw34126step1 raw34126step1Labels := by
      have ha : raw34126step1 = (fun i j => raw34126step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34126step1 raw34126step0; decide +kernel
      have hl : raw34126step1Labels = raw34126step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34126step0 raw34126step0Labels permutation37 permutation7
    mixedMoment B raw34126step1 raw34126step1Labels = mixedMoment B raw34126step2 raw34126step2Labels := by
      have ha : raw34126step2 = -raw34126step1 := by apply Matrix.ext; change ∀ i j, raw34126step2 i j = -(raw34126step1 i j); unfold raw34126step2 raw34126step1; decide +kernel
      have hl : raw34126step2Labels = raw34126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34126step2 raw34126step2Labels = mixedMoment B raw34126step3 raw34126step3Labels := by
      have ha : raw34126step3 = raw34126step2 := by apply Matrix.ext; unfold raw34126step3 raw34126step2; decide +kernel
      have hl : raw34126step2Labels = labelEmbedding1 ∘ raw34126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34126step2 raw34126step2Labels raw34126step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

theorem canonical34127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34127 raw34127Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw34127 raw34127Labels = mixedMoment B raw34127step0 raw34127step0Labels := by
      have ha : raw34127step0 = (fun i j => raw34127 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34127step0 raw34127; decide +kernel
      have hl : raw34127step0Labels = raw34127Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34127 raw34127Labels permutation157 permutation7
    mixedMoment B raw34127step0 raw34127step0Labels = mixedMoment B raw34127step1 raw34127step1Labels := by
      have ha : raw34127step1 = -raw34127step0 := by apply Matrix.ext; change ∀ i j, raw34127step1 i j = -(raw34127step0 i j); unfold raw34127step1 raw34127step0; decide +kernel
      have hl : raw34127step1Labels = raw34127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34127step1 raw34127step1Labels = mixedMoment B raw34127step2 raw34127step2Labels := by
      have ha : raw34127step2 = raw34127step1 := by apply Matrix.ext; unfold raw34127step2 raw34127step1; decide +kernel
      have hl : raw34127step1Labels = labelEmbedding1 ∘ raw34127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34127step1 raw34127step1Labels raw34127step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2698 node2698Labels := by rfl

theorem canonical34128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34128 raw34128Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw34128 raw34128Labels = mixedMoment B raw34128step0 raw34128step0Labels := by
      have hz : ∀ j, raw34128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34128step0 = (fun i j => raw34128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34128step0 raw34128; decide +kernel
      have hl : raw34128step0Labels = raw34128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34128 raw34128Labels permutation346 hz
    mixedMoment B raw34128step0 raw34128step0Labels = mixedMoment B raw34128step1 raw34128step1Labels := by
      have ha : raw34128step1 = (fun i j => raw34128step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34128step1 raw34128step0; decide +kernel
      have hl : raw34128step1Labels = raw34128step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34128step0 raw34128step0Labels permutation37 permutation7
    mixedMoment B raw34128step1 raw34128step1Labels = mixedMoment B raw34128step2 raw34128step2Labels := by
      have ha : raw34128step2 = -raw34128step1 := by apply Matrix.ext; change ∀ i j, raw34128step2 i j = -(raw34128step1 i j); unfold raw34128step2 raw34128step1; decide +kernel
      have hl : raw34128step2Labels = raw34128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34128step2 raw34128step2Labels = mixedMoment B raw34128step3 raw34128step3Labels := by
      have ha : raw34128step3 = raw34128step2 := by apply Matrix.ext; unfold raw34128step3 raw34128step2; decide +kernel
      have hl : raw34128step2Labels = labelEmbedding1 ∘ raw34128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34128step2 raw34128step2Labels raw34128step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical34129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34129 raw34129Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw34129 raw34129Labels = mixedMoment B raw34129step0 raw34129step0Labels := by
      have hz : ∀ j, raw34129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34129step0 = (fun i j => raw34129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34129step0 raw34129; decide +kernel
      have hl : raw34129step0Labels = raw34129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34129 raw34129Labels permutation346 hz
    mixedMoment B raw34129step0 raw34129step0Labels = mixedMoment B raw34129step1 raw34129step1Labels := by
      have ha : raw34129step1 = (fun i j => raw34129step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34129step1 raw34129step0; decide +kernel
      have hl : raw34129step1Labels = raw34129step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34129step0 raw34129step0Labels permutation37 permutation7
    mixedMoment B raw34129step1 raw34129step1Labels = mixedMoment B raw34129step2 raw34129step2Labels := by
      have ha : raw34129step2 = -raw34129step1 := by apply Matrix.ext; change ∀ i j, raw34129step2 i j = -(raw34129step1 i j); unfold raw34129step2 raw34129step1; decide +kernel
      have hl : raw34129step2Labels = raw34129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34129step2 raw34129step2Labels = mixedMoment B raw34129step3 raw34129step3Labels := by
      have ha : raw34129step3 = raw34129step2 := by apply Matrix.ext; unfold raw34129step3 raw34129step2; decide +kernel
      have hl : raw34129step2Labels = labelEmbedding1 ∘ raw34129step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34129step2 raw34129step2Labels raw34129step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical34130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34130 raw34130Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw34130 raw34130Labels = mixedMoment B raw34130step0 raw34130step0Labels := by
      have hz : ∀ j, raw34130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34130step0 = (fun i j => raw34130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34130step0 raw34130; decide +kernel
      have hl : raw34130step0Labels = raw34130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34130 raw34130Labels permutation346 hz
    mixedMoment B raw34130step0 raw34130step0Labels = mixedMoment B raw34130step1 raw34130step1Labels := by
      have ha : raw34130step1 = (fun i j => raw34130step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34130step1 raw34130step0; decide +kernel
      have hl : raw34130step1Labels = raw34130step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34130step0 raw34130step0Labels permutation37 permutation7
    mixedMoment B raw34130step1 raw34130step1Labels = mixedMoment B raw34130step2 raw34130step2Labels := by
      have ha : raw34130step2 = -raw34130step1 := by apply Matrix.ext; change ∀ i j, raw34130step2 i j = -(raw34130step1 i j); unfold raw34130step2 raw34130step1; decide +kernel
      have hl : raw34130step2Labels = raw34130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34130step2 raw34130step2Labels = mixedMoment B raw34130step3 raw34130step3Labels := by
      have ha : raw34130step3 = raw34130step2 := by apply Matrix.ext; unfold raw34130step3 raw34130step2; decide +kernel
      have hl : raw34130step2Labels = labelEmbedding1 ∘ raw34130step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34130step2 raw34130step2Labels raw34130step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical34131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34131 raw34131Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw34131 raw34131Labels = mixedMoment B raw34131step0 raw34131step0Labels := by
      have hz : ∀ j, raw34131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34131step0 = (fun i j => raw34131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34131step0 raw34131; decide +kernel
      have hl : raw34131step0Labels = raw34131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34131 raw34131Labels permutation346 hz
    mixedMoment B raw34131step0 raw34131step0Labels = mixedMoment B raw34131step1 raw34131step1Labels := by
      have hz : ∀ j, raw34131step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34131step1 = (fun i j => raw34131step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34131step1 raw34131step0; decide +kernel
      have hl : raw34131step1Labels = raw34131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34131step0 raw34131step0Labels permutation56 hz
    mixedMoment B raw34131step1 raw34131step1Labels = mixedMoment B raw34131step2 raw34131step2Labels := by
      have ha : raw34131step2 = (fun i j => raw34131step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34131step2 raw34131step1; decide +kernel
      have hl : raw34131step2Labels = raw34131step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34131step1 raw34131step1Labels permutation13 permutation7
    mixedMoment B raw34131step2 raw34131step2Labels = mixedMoment B raw34131step3 raw34131step3Labels := by
      have ha : raw34131step3 = -raw34131step2 := by apply Matrix.ext; change ∀ i j, raw34131step3 i j = -(raw34131step2 i j); unfold raw34131step3 raw34131step2; decide +kernel
      have hl : raw34131step3Labels = raw34131step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34131step3 raw34131step3Labels = mixedMoment B raw34131step4 raw34131step4Labels := by
      have ha : raw34131step4 = raw34131step3 := by apply Matrix.ext; unfold raw34131step4 raw34131step3; decide +kernel
      have hl : raw34131step3Labels = labelEmbedding1 ∘ raw34131step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34131step3 raw34131step3Labels raw34131step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical34132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34132 raw34132Labels = mixedMoment B node2145 node2145Labels := by
  calc
    mixedMoment B raw34132 raw34132Labels = mixedMoment B raw34132step0 raw34132step0Labels := by
      have ha : raw34132step0 = (fun i j => raw34132 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34132step0 raw34132; decide +kernel
      have hl : raw34132step0Labels = raw34132Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34132 raw34132Labels permutation157 permutation7
    mixedMoment B raw34132step0 raw34132step0Labels = mixedMoment B raw34132step1 raw34132step1Labels := by
      have ha : raw34132step1 = -raw34132step0 := by apply Matrix.ext; change ∀ i j, raw34132step1 i j = -(raw34132step0 i j); unfold raw34132step1 raw34132step0; decide +kernel
      have hl : raw34132step1Labels = raw34132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34132step1 raw34132step1Labels = mixedMoment B raw34132step2 raw34132step2Labels := by
      have ha : raw34132step2 = raw34132step1 := by apply Matrix.ext; unfold raw34132step2 raw34132step1; decide +kernel
      have hl : raw34132step1Labels = labelEmbedding1 ∘ raw34132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34132step1 raw34132step1Labels raw34132step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2145 node2145Labels := by rfl

theorem canonical34133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34133 raw34133Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw34133 raw34133Labels = mixedMoment B raw34133step0 raw34133step0Labels := by
      have ha : raw34133step0 = (fun i j => raw34133 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34133step0 raw34133; decide +kernel
      have hl : raw34133step0Labels = raw34133Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34133 raw34133Labels permutation157 permutation7
    mixedMoment B raw34133step0 raw34133step0Labels = mixedMoment B raw34133step1 raw34133step1Labels := by
      have ha : raw34133step1 = -raw34133step0 := by apply Matrix.ext; change ∀ i j, raw34133step1 i j = -(raw34133step0 i j); unfold raw34133step1 raw34133step0; decide +kernel
      have hl : raw34133step1Labels = raw34133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34133step1 raw34133step1Labels = mixedMoment B raw34133step2 raw34133step2Labels := by
      have ha : raw34133step2 = raw34133step1 := by apply Matrix.ext; unfold raw34133step2 raw34133step1; decide +kernel
      have hl : raw34133step1Labels = labelEmbedding1 ∘ raw34133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34133step1 raw34133step1Labels raw34133step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

theorem canonical34134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34134 raw34134Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw34134 raw34134Labels = mixedMoment B raw34134step0 raw34134step0Labels := by
      have ha : raw34134step0 = (fun i j => raw34134 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34134step0 raw34134; decide +kernel
      have hl : raw34134step0Labels = raw34134Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34134 raw34134Labels permutation157 permutation7
    mixedMoment B raw34134step0 raw34134step0Labels = mixedMoment B raw34134step1 raw34134step1Labels := by
      have ha : raw34134step1 = -raw34134step0 := by apply Matrix.ext; change ∀ i j, raw34134step1 i j = -(raw34134step0 i j); unfold raw34134step1 raw34134step0; decide +kernel
      have hl : raw34134step1Labels = raw34134step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34134step1 raw34134step1Labels = mixedMoment B raw34134step2 raw34134step2Labels := by
      have ha : raw34134step2 = raw34134step1 := by apply Matrix.ext; unfold raw34134step2 raw34134step1; decide +kernel
      have hl : raw34134step1Labels = labelEmbedding1 ∘ raw34134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34134step1 raw34134step1Labels raw34134step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical34135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34135 raw34135Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw34135 raw34135Labels = mixedMoment B raw34135step0 raw34135step0Labels := by
      have ha : raw34135step0 = (fun i j => raw34135 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34135step0 raw34135; decide +kernel
      have hl : raw34135step0Labels = raw34135Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34135 raw34135Labels permutation157 permutation7
    mixedMoment B raw34135step0 raw34135step0Labels = mixedMoment B raw34135step1 raw34135step1Labels := by
      have ha : raw34135step1 = -raw34135step0 := by apply Matrix.ext; change ∀ i j, raw34135step1 i j = -(raw34135step0 i j); unfold raw34135step1 raw34135step0; decide +kernel
      have hl : raw34135step1Labels = raw34135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34135step1 raw34135step1Labels = mixedMoment B raw34135step2 raw34135step2Labels := by
      have ha : raw34135step2 = raw34135step1 := by apply Matrix.ext; unfold raw34135step2 raw34135step1; decide +kernel
      have hl : raw34135step1Labels = labelEmbedding1 ∘ raw34135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34135step1 raw34135step1Labels raw34135step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical34136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34136 raw34136Labels = mixedMoment B node2157 node2157Labels := by
  calc
    mixedMoment B raw34136 raw34136Labels = mixedMoment B raw34136step0 raw34136step0Labels := by
      have hz : ∀ j, raw34136 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34136step0 = (fun i j => raw34136 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34136step0 raw34136; decide +kernel
      have hl : raw34136step0Labels = raw34136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34136 raw34136Labels permutation346 hz
    mixedMoment B raw34136step0 raw34136step0Labels = mixedMoment B raw34136step1 raw34136step1Labels := by
      have ha : raw34136step1 = (fun i j => raw34136step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34136step1 raw34136step0; decide +kernel
      have hl : raw34136step1Labels = raw34136step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34136step0 raw34136step0Labels permutation37 permutation7
    mixedMoment B raw34136step1 raw34136step1Labels = mixedMoment B raw34136step2 raw34136step2Labels := by
      have ha : raw34136step2 = -raw34136step1 := by apply Matrix.ext; change ∀ i j, raw34136step2 i j = -(raw34136step1 i j); unfold raw34136step2 raw34136step1; decide +kernel
      have hl : raw34136step2Labels = raw34136step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34136step2 raw34136step2Labels = mixedMoment B raw34136step3 raw34136step3Labels := by
      have ha : raw34136step3 = raw34136step2 := by apply Matrix.ext; unfold raw34136step3 raw34136step2; decide +kernel
      have hl : raw34136step2Labels = labelEmbedding1 ∘ raw34136step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34136step2 raw34136step2Labels raw34136step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2157 node2157Labels := by rfl

theorem canonical34137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34137 raw34137Labels = mixedMoment B node2177 node2177Labels := by
  calc
    mixedMoment B raw34137 raw34137Labels = mixedMoment B raw34137step0 raw34137step0Labels := by
      have ha : raw34137step0 = (fun i j => raw34137 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34137step0 raw34137; decide +kernel
      have hl : raw34137step0Labels = raw34137Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34137 raw34137Labels permutation157 permutation7
    mixedMoment B raw34137step0 raw34137step0Labels = mixedMoment B raw34137step1 raw34137step1Labels := by
      have ha : raw34137step1 = -raw34137step0 := by apply Matrix.ext; change ∀ i j, raw34137step1 i j = -(raw34137step0 i j); unfold raw34137step1 raw34137step0; decide +kernel
      have hl : raw34137step1Labels = raw34137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34137step1 raw34137step1Labels = mixedMoment B raw34137step2 raw34137step2Labels := by
      have ha : raw34137step2 = raw34137step1 := by apply Matrix.ext; unfold raw34137step2 raw34137step1; decide +kernel
      have hl : raw34137step1Labels = labelEmbedding1 ∘ raw34137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34137step1 raw34137step1Labels raw34137step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2177 node2177Labels := by rfl

theorem canonical34138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34138 raw34138Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw34138 raw34138Labels = mixedMoment B raw34138step0 raw34138step0Labels := by
      have hz : ∀ j, raw34138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34138step0 = (fun i j => raw34138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34138step0 raw34138; decide +kernel
      have hl : raw34138step0Labels = raw34138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34138 raw34138Labels permutation346 hz
    mixedMoment B raw34138step0 raw34138step0Labels = mixedMoment B raw34138step1 raw34138step1Labels := by
      have ha : raw34138step1 = (fun i j => raw34138step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34138step1 raw34138step0; decide +kernel
      have hl : raw34138step1Labels = raw34138step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34138step0 raw34138step0Labels permutation37 permutation7
    mixedMoment B raw34138step1 raw34138step1Labels = mixedMoment B raw34138step2 raw34138step2Labels := by
      have ha : raw34138step2 = -raw34138step1 := by apply Matrix.ext; change ∀ i j, raw34138step2 i j = -(raw34138step1 i j); unfold raw34138step2 raw34138step1; decide +kernel
      have hl : raw34138step2Labels = raw34138step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34138step2 raw34138step2Labels = mixedMoment B raw34138step3 raw34138step3Labels := by
      have ha : raw34138step3 = raw34138step2 := by apply Matrix.ext; unfold raw34138step3 raw34138step2; decide +kernel
      have hl : raw34138step2Labels = labelEmbedding1 ∘ raw34138step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34138step2 raw34138step2Labels raw34138step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical34139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34139 raw34139Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw34139 raw34139Labels = mixedMoment B raw34139step0 raw34139step0Labels := by
      have hz : ∀ j, raw34139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34139step0 = (fun i j => raw34139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34139step0 raw34139; decide +kernel
      have hl : raw34139step0Labels = raw34139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34139 raw34139Labels permutation346 hz
    mixedMoment B raw34139step0 raw34139step0Labels = mixedMoment B raw34139step1 raw34139step1Labels := by
      have ha : raw34139step1 = (fun i j => raw34139step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34139step1 raw34139step0; decide +kernel
      have hl : raw34139step1Labels = raw34139step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34139step0 raw34139step0Labels permutation37 permutation7
    mixedMoment B raw34139step1 raw34139step1Labels = mixedMoment B raw34139step2 raw34139step2Labels := by
      have ha : raw34139step2 = -raw34139step1 := by apply Matrix.ext; change ∀ i j, raw34139step2 i j = -(raw34139step1 i j); unfold raw34139step2 raw34139step1; decide +kernel
      have hl : raw34139step2Labels = raw34139step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34139step2 raw34139step2Labels = mixedMoment B raw34139step3 raw34139step3Labels := by
      have ha : raw34139step3 = raw34139step2 := by apply Matrix.ext; unfold raw34139step3 raw34139step2; decide +kernel
      have hl : raw34139step2Labels = labelEmbedding1 ∘ raw34139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34139step2 raw34139step2Labels raw34139step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical34140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34140 raw34140Labels = mixedMoment B node2158 node2158Labels := by
  calc
    mixedMoment B raw34140 raw34140Labels = mixedMoment B raw34140step0 raw34140step0Labels := by
      have hz : ∀ j, raw34140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34140step0 = (fun i j => raw34140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34140step0 raw34140; decide +kernel
      have hl : raw34140step0Labels = raw34140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34140 raw34140Labels permutation346 hz
    mixedMoment B raw34140step0 raw34140step0Labels = mixedMoment B raw34140step1 raw34140step1Labels := by
      have ha : raw34140step1 = (fun i j => raw34140step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34140step1 raw34140step0; decide +kernel
      have hl : raw34140step1Labels = raw34140step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34140step0 raw34140step0Labels permutation37 permutation7
    mixedMoment B raw34140step1 raw34140step1Labels = mixedMoment B raw34140step2 raw34140step2Labels := by
      have ha : raw34140step2 = -raw34140step1 := by apply Matrix.ext; change ∀ i j, raw34140step2 i j = -(raw34140step1 i j); unfold raw34140step2 raw34140step1; decide +kernel
      have hl : raw34140step2Labels = raw34140step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34140step2 raw34140step2Labels = mixedMoment B raw34140step3 raw34140step3Labels := by
      have ha : raw34140step3 = raw34140step2 := by apply Matrix.ext; unfold raw34140step3 raw34140step2; decide +kernel
      have hl : raw34140step2Labels = labelEmbedding1 ∘ raw34140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34140step2 raw34140step2Labels raw34140step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2158 node2158Labels := by rfl

theorem canonical34141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34141 raw34141Labels = mixedMoment B node2178 node2178Labels := by
  calc
    mixedMoment B raw34141 raw34141Labels = mixedMoment B raw34141step0 raw34141step0Labels := by
      have ha : raw34141step0 = (fun i j => raw34141 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34141step0 raw34141; decide +kernel
      have hl : raw34141step0Labels = raw34141Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34141 raw34141Labels permutation157 permutation7
    mixedMoment B raw34141step0 raw34141step0Labels = mixedMoment B raw34141step1 raw34141step1Labels := by
      have ha : raw34141step1 = -raw34141step0 := by apply Matrix.ext; change ∀ i j, raw34141step1 i j = -(raw34141step0 i j); unfold raw34141step1 raw34141step0; decide +kernel
      have hl : raw34141step1Labels = raw34141step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34141step1 raw34141step1Labels = mixedMoment B raw34141step2 raw34141step2Labels := by
      have ha : raw34141step2 = raw34141step1 := by apply Matrix.ext; unfold raw34141step2 raw34141step1; decide +kernel
      have hl : raw34141step1Labels = labelEmbedding1 ∘ raw34141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34141step1 raw34141step1Labels raw34141step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2178 node2178Labels := by rfl

theorem canonical34142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34142 raw34142Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw34142 raw34142Labels = mixedMoment B raw34142step0 raw34142step0Labels := by
      have hz : ∀ j, raw34142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34142step0 = (fun i j => raw34142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34142step0 raw34142; decide +kernel
      have hl : raw34142step0Labels = raw34142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34142 raw34142Labels permutation346 hz
    mixedMoment B raw34142step0 raw34142step0Labels = mixedMoment B raw34142step1 raw34142step1Labels := by
      have ha : raw34142step1 = (fun i j => raw34142step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34142step1 raw34142step0; decide +kernel
      have hl : raw34142step1Labels = raw34142step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34142step0 raw34142step0Labels permutation37 permutation7
    mixedMoment B raw34142step1 raw34142step1Labels = mixedMoment B raw34142step2 raw34142step2Labels := by
      have ha : raw34142step2 = -raw34142step1 := by apply Matrix.ext; change ∀ i j, raw34142step2 i j = -(raw34142step1 i j); unfold raw34142step2 raw34142step1; decide +kernel
      have hl : raw34142step2Labels = raw34142step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34142step2 raw34142step2Labels = mixedMoment B raw34142step3 raw34142step3Labels := by
      have ha : raw34142step3 = raw34142step2 := by apply Matrix.ext; unfold raw34142step3 raw34142step2; decide +kernel
      have hl : raw34142step2Labels = labelEmbedding1 ∘ raw34142step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34142step2 raw34142step2Labels raw34142step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

theorem canonical34143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34143 raw34143Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw34143 raw34143Labels = mixedMoment B raw34143step0 raw34143step0Labels := by
      have hz : ∀ j, raw34143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34143step0 = (fun i j => raw34143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34143step0 raw34143; decide +kernel
      have hl : raw34143step0Labels = raw34143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34143 raw34143Labels permutation346 hz
    mixedMoment B raw34143step0 raw34143step0Labels = mixedMoment B raw34143step1 raw34143step1Labels := by
      have ha : raw34143step1 = (fun i j => raw34143step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34143step1 raw34143step0; decide +kernel
      have hl : raw34143step1Labels = raw34143step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34143step0 raw34143step0Labels permutation37 permutation7
    mixedMoment B raw34143step1 raw34143step1Labels = mixedMoment B raw34143step2 raw34143step2Labels := by
      have ha : raw34143step2 = -raw34143step1 := by apply Matrix.ext; change ∀ i j, raw34143step2 i j = -(raw34143step1 i j); unfold raw34143step2 raw34143step1; decide +kernel
      have hl : raw34143step2Labels = raw34143step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34143step2 raw34143step2Labels = mixedMoment B raw34143step3 raw34143step3Labels := by
      have ha : raw34143step3 = raw34143step2 := by apply Matrix.ext; unfold raw34143step3 raw34143step2; decide +kernel
      have hl : raw34143step2Labels = labelEmbedding1 ∘ raw34143step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34143step2 raw34143step2Labels raw34143step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical34144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34144 raw34144Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw34144 raw34144Labels = mixedMoment B raw34144step0 raw34144step0Labels := by
      have hz : ∀ j, raw34144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34144step0 = (fun i j => raw34144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34144step0 raw34144; decide +kernel
      have hl : raw34144step0Labels = raw34144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34144 raw34144Labels permutation346 hz
    mixedMoment B raw34144step0 raw34144step0Labels = mixedMoment B raw34144step1 raw34144step1Labels := by
      have ha : raw34144step1 = (fun i j => raw34144step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34144step1 raw34144step0; decide +kernel
      have hl : raw34144step1Labels = raw34144step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34144step0 raw34144step0Labels permutation37 permutation7
    mixedMoment B raw34144step1 raw34144step1Labels = mixedMoment B raw34144step2 raw34144step2Labels := by
      have ha : raw34144step2 = -raw34144step1 := by apply Matrix.ext; change ∀ i j, raw34144step2 i j = -(raw34144step1 i j); unfold raw34144step2 raw34144step1; decide +kernel
      have hl : raw34144step2Labels = raw34144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34144step2 raw34144step2Labels = mixedMoment B raw34144step3 raw34144step3Labels := by
      have ha : raw34144step3 = raw34144step2 := by apply Matrix.ext; unfold raw34144step3 raw34144step2; decide +kernel
      have hl : raw34144step2Labels = labelEmbedding1 ∘ raw34144step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34144step2 raw34144step2Labels raw34144step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2162 node2162Labels := by rfl

theorem canonical34145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34145 raw34145Labels = mixedMoment B node2179 node2179Labels := by
  calc
    mixedMoment B raw34145 raw34145Labels = mixedMoment B raw34145step0 raw34145step0Labels := by
      have ha : raw34145step0 = (fun i j => raw34145 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34145step0 raw34145; decide +kernel
      have hl : raw34145step0Labels = raw34145Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34145 raw34145Labels permutation157 permutation7
    mixedMoment B raw34145step0 raw34145step0Labels = mixedMoment B raw34145step1 raw34145step1Labels := by
      have ha : raw34145step1 = -raw34145step0 := by apply Matrix.ext; change ∀ i j, raw34145step1 i j = -(raw34145step0 i j); unfold raw34145step1 raw34145step0; decide +kernel
      have hl : raw34145step1Labels = raw34145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34145step1 raw34145step1Labels = mixedMoment B raw34145step2 raw34145step2Labels := by
      have ha : raw34145step2 = raw34145step1 := by apply Matrix.ext; unfold raw34145step2 raw34145step1; decide +kernel
      have hl : raw34145step1Labels = labelEmbedding1 ∘ raw34145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34145step1 raw34145step1Labels raw34145step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2179 node2179Labels := by rfl

theorem canonical34146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34146 raw34146Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw34146 raw34146Labels = mixedMoment B raw34146step0 raw34146step0Labels := by
      have hz : ∀ j, raw34146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34146step0 = (fun i j => raw34146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34146step0 raw34146; decide +kernel
      have hl : raw34146step0Labels = raw34146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34146 raw34146Labels permutation346 hz
    mixedMoment B raw34146step0 raw34146step0Labels = mixedMoment B raw34146step1 raw34146step1Labels := by
      have ha : raw34146step1 = (fun i j => raw34146step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34146step1 raw34146step0; decide +kernel
      have hl : raw34146step1Labels = raw34146step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34146step0 raw34146step0Labels permutation146 permutation5
    mixedMoment B raw34146step1 raw34146step1Labels = mixedMoment B raw34146step2 raw34146step2Labels := by
      have ha : raw34146step2 = raw34146step1 := by apply Matrix.ext; unfold raw34146step2 raw34146step1; decide +kernel
      have hl : raw34146step1Labels = labelEmbedding1 ∘ raw34146step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34146step1 raw34146step1Labels raw34146step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2221 node2221Labels := by rfl

theorem canonical34147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34147 raw34147Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw34147 raw34147Labels = mixedMoment B raw34147step0 raw34147step0Labels := by
      have hz : ∀ j, raw34147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34147step0 = (fun i j => raw34147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34147step0 raw34147; decide +kernel
      have hl : raw34147step0Labels = raw34147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34147 raw34147Labels permutation346 hz
    mixedMoment B raw34147step0 raw34147step0Labels = mixedMoment B raw34147step1 raw34147step1Labels := by
      have ha : raw34147step1 = (fun i j => raw34147step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34147step1 raw34147step0; decide +kernel
      have hl : raw34147step1Labels = raw34147step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34147step0 raw34147step0Labels permutation37 permutation7
    mixedMoment B raw34147step1 raw34147step1Labels = mixedMoment B raw34147step2 raw34147step2Labels := by
      have ha : raw34147step2 = -raw34147step1 := by apply Matrix.ext; change ∀ i j, raw34147step2 i j = -(raw34147step1 i j); unfold raw34147step2 raw34147step1; decide +kernel
      have hl : raw34147step2Labels = raw34147step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34147step2 raw34147step2Labels = mixedMoment B raw34147step3 raw34147step3Labels := by
      have ha : raw34147step3 = raw34147step2 := by apply Matrix.ext; unfold raw34147step3 raw34147step2; decide +kernel
      have hl : raw34147step2Labels = labelEmbedding1 ∘ raw34147step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34147step2 raw34147step2Labels raw34147step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

theorem canonical34148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34148 raw34148Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw34148 raw34148Labels = mixedMoment B raw34148step0 raw34148step0Labels := by
      have hz : ∀ j, raw34148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34148step0 = (fun i j => raw34148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34148step0 raw34148; decide +kernel
      have hl : raw34148step0Labels = raw34148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34148 raw34148Labels permutation346 hz
    mixedMoment B raw34148step0 raw34148step0Labels = mixedMoment B raw34148step1 raw34148step1Labels := by
      have ha : raw34148step1 = (fun i j => raw34148step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34148step1 raw34148step0; decide +kernel
      have hl : raw34148step1Labels = raw34148step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34148step0 raw34148step0Labels permutation34 permutation2
    _ = mixedMoment B node3395 node3395Labels := by rfl

theorem canonical34149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34149 raw34149Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw34149 raw34149Labels = mixedMoment B raw34149step0 raw34149step0Labels := by
      have hz : ∀ j, raw34149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34149step0 = (fun i j => raw34149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34149step0 raw34149; decide +kernel
      have hl : raw34149step0Labels = raw34149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34149 raw34149Labels permutation346 hz
    mixedMoment B raw34149step0 raw34149step0Labels = mixedMoment B raw34149step1 raw34149step1Labels := by
      have ha : raw34149step1 = (fun i j => raw34149step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34149step1 raw34149step0; decide +kernel
      have hl : raw34149step1Labels = raw34149step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34149step0 raw34149step0Labels permutation34 permutation2
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical34150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34150 raw34150Labels = mixedMoment B node1806 node1806Labels := by
  calc
    mixedMoment B raw34150 raw34150Labels = mixedMoment B raw34150step0 raw34150step0Labels := by
      have ha : raw34150step0 = (fun i j => raw34150 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34150step0 raw34150; decide +kernel
      have hl : raw34150step0Labels = raw34150Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34150 raw34150Labels permutation154 permutation2
    _ = mixedMoment B node1806 node1806Labels := by rfl

theorem canonical34151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34151 raw34151Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw34151 raw34151Labels = mixedMoment B raw34151step0 raw34151step0Labels := by
      have hz : ∀ j, raw34151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34151step0 = (fun i j => raw34151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34151step0 raw34151; decide +kernel
      have hl : raw34151step0Labels = raw34151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34151 raw34151Labels permutation346 hz
    mixedMoment B raw34151step0 raw34151step0Labels = mixedMoment B raw34151step1 raw34151step1Labels := by
      have ha : raw34151step1 = (fun i j => raw34151step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34151step1 raw34151step0; decide +kernel
      have hl : raw34151step1Labels = raw34151step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34151step0 raw34151step0Labels permutation35 permutation2
    _ = mixedMoment B node1814 node1814Labels := by rfl

theorem canonical34152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34152 raw34152Labels = mixedMoment B node1816 node1816Labels := by
  calc
    mixedMoment B raw34152 raw34152Labels = mixedMoment B raw34152step0 raw34152step0Labels := by
      have hz : ∀ j, raw34152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34152step0 = (fun i j => raw34152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34152step0 raw34152; decide +kernel
      have hl : raw34152step0Labels = raw34152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34152 raw34152Labels permutation346 hz
    mixedMoment B raw34152step0 raw34152step0Labels = mixedMoment B raw34152step1 raw34152step1Labels := by
      have ha : raw34152step1 = (fun i j => raw34152step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34152step1 raw34152step0; decide +kernel
      have hl : raw34152step1Labels = raw34152step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34152step0 raw34152step0Labels permutation33 permutation2
    _ = mixedMoment B node1816 node1816Labels := by rfl

theorem canonical34153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34153 raw34153Labels = mixedMoment B node1813 node1813Labels := by
  calc
    mixedMoment B raw34153 raw34153Labels = mixedMoment B raw34153step0 raw34153step0Labels := by
      have hz : ∀ j, raw34153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34153step0 = (fun i j => raw34153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34153step0 raw34153; decide +kernel
      have hl : raw34153step0Labels = raw34153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34153 raw34153Labels permutation346 hz
    mixedMoment B raw34153step0 raw34153step0Labels = mixedMoment B raw34153step1 raw34153step1Labels := by
      have ha : raw34153step1 = (fun i j => raw34153step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34153step1 raw34153step0; decide +kernel
      have hl : raw34153step1Labels = raw34153step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34153step0 raw34153step0Labels permutation34 permutation2
    _ = mixedMoment B node1813 node1813Labels := by rfl

theorem canonical34154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34154 raw34154Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw34154 raw34154Labels = mixedMoment B raw34154step0 raw34154step0Labels := by
      have hz : ∀ j, raw34154 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34154step0 = (fun i j => raw34154 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34154step0 raw34154; decide +kernel
      have hl : raw34154step0Labels = raw34154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34154 raw34154Labels permutation590 hz
    mixedMoment B raw34154step0 raw34154step0Labels = mixedMoment B raw34154step1 raw34154step1Labels := by
      have hz : ∀ j, raw34154step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34154step1 = (fun i j => raw34154step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34154step1 raw34154step0; decide +kernel
      have hl : raw34154step1Labels = raw34154step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34154step0 raw34154step0Labels permutation80 hz
    mixedMoment B raw34154step1 raw34154step1Labels = mixedMoment B raw34154step2 raw34154step2Labels := by
      have hz : ∀ j, raw34154step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw34154step2 = (fun i j => raw34154step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw34154step2 raw34154step1; decide +kernel
      have hl : raw34154step2Labels = raw34154step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34154step1 raw34154step1Labels permutation14 hz
    mixedMoment B raw34154step2 raw34154step2Labels = mixedMoment B raw34154step3 raw34154step3Labels := by
      have ha : raw34154step3 = (fun i j => raw34154step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34154step3 raw34154step2; decide +kernel
      have hl : raw34154step3Labels = raw34154step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34154step2 raw34154step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1663 node1663Labels = 0 := by
  exact mixedMoment_alpha B hF node1663 node1663Labels 1 permutation485
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

theorem sound1663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1663 node1663Labels = Sparse.eval nodeValue1663 (mixedVector B) := by
  simpa only [nodeValue1663, Sparse.eval_nil] using zero1663 B _hB _hF

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

theorem zero1671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1671 node1671Labels = 0 := by
  exact mixedMoment_alpha B hF node1671 node1671Labels 1 permutation487
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

theorem sound1667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1667 node1667Labels = Sparse.eval nodeValue1667 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1667) = mixedMoment B node1667 node1667Labels := rfl
  simpa [nodeValue1667, Sparse.eval] using hc.symm

theorem sound1668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1668 node1668Labels = Sparse.eval nodeValue1668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1668) = mixedMoment B node1668 node1668Labels := rfl
  simpa [nodeValue1668, Sparse.eval] using hc.symm

theorem sound1670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1670 node1670Labels = Sparse.eval nodeValue1670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1670) = mixedMoment B node1670 node1670Labels := rfl
  simpa [nodeValue1670, Sparse.eval] using hc.symm

theorem sound1671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1671 node1671Labels = Sparse.eval nodeValue1671 (mixedVector B) := by
  simpa only [nodeValue1671, Sparse.eval_nil] using zero1671 B _hB _hF

theorem sound1673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1673 node1673Labels = Sparse.eval nodeValue1673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1673) = mixedMoment B node1673 node1673Labels := rfl
  simpa [nodeValue1673, Sparse.eval] using hc.symm

theorem sound1678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1678 node1678Labels = Sparse.eval nodeValue1678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1678) = mixedMoment B node1678 node1678Labels := rfl
  simpa [nodeValue1678, Sparse.eval] using hc.symm

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

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

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

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

theorem sound1790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1790 node1790Labels = Sparse.eval nodeValue1790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1790) = mixedMoment B node1790 node1790Labels := rfl
  simpa [nodeValue1790, Sparse.eval] using hc.symm

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

theorem sound1792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1792 node1792Labels = Sparse.eval nodeValue1792 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1792) = mixedMoment B node1792 node1792Labels := rfl
  simpa [nodeValue1792, Sparse.eval] using hc.symm

theorem sound1794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1794 node1794Labels = Sparse.eval nodeValue1794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1794) = mixedMoment B node1794 node1794Labels := rfl
  simpa [nodeValue1794, Sparse.eval] using hc.symm

theorem sound1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1805 node1805Labels = Sparse.eval nodeValue1805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1805) = mixedMoment B node1805 node1805Labels := rfl
  simpa [nodeValue1805, Sparse.eval] using hc.symm

theorem sound1806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1806 node1806Labels = Sparse.eval nodeValue1806 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1806) = mixedMoment B node1806 node1806Labels := rfl
  simpa [nodeValue1806, Sparse.eval] using hc.symm

theorem sound1813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1813 node1813Labels = Sparse.eval nodeValue1813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1813) = mixedMoment B node1813 node1813Labels := rfl
  simpa [nodeValue1813, Sparse.eval] using hc.symm

theorem sound1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1814 node1814Labels = Sparse.eval nodeValue1814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1814) = mixedMoment B node1814 node1814Labels := rfl
  simpa [nodeValue1814, Sparse.eval] using hc.symm

theorem sound1816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1816 node1816Labels = Sparse.eval nodeValue1816 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1816) = mixedMoment B node1816 node1816Labels := rfl
  simpa [nodeValue1816, Sparse.eval] using hc.symm

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

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

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

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

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

theorem sound2140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2140 node2140Labels = Sparse.eval nodeValue2140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2140) = mixedMoment B node2140 node2140Labels := rfl
  simpa [nodeValue2140, Sparse.eval] using hc.symm

theorem sound2141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2141 node2141Labels = Sparse.eval nodeValue2141 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2141) = mixedMoment B node2141 node2141Labels := rfl
  simpa [nodeValue2141, Sparse.eval] using hc.symm

theorem sound2144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2144 node2144Labels = Sparse.eval nodeValue2144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2144) = mixedMoment B node2144 node2144Labels := rfl
  simpa [nodeValue2144, Sparse.eval] using hc.symm

theorem sound2145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2145 node2145Labels = Sparse.eval nodeValue2145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2145) = mixedMoment B node2145 node2145Labels := rfl
  simpa [nodeValue2145, Sparse.eval] using hc.symm

theorem sound2147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2147 node2147Labels = Sparse.eval nodeValue2147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2147) = mixedMoment B node2147 node2147Labels := rfl
  simpa [nodeValue2147, Sparse.eval] using hc.symm

theorem sound2148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2148 node2148Labels = Sparse.eval nodeValue2148 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2148) = mixedMoment B node2148 node2148Labels := rfl
  simpa [nodeValue2148, Sparse.eval] using hc.symm

theorem sound2150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2150 node2150Labels = Sparse.eval nodeValue2150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2150) = mixedMoment B node2150 node2150Labels := rfl
  simpa [nodeValue2150, Sparse.eval] using hc.symm

theorem sound2154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2154 node2154Labels = Sparse.eval nodeValue2154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2154) = mixedMoment B node2154 node2154Labels := rfl
  simpa [nodeValue2154, Sparse.eval] using hc.symm

theorem sound2157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2157 node2157Labels = Sparse.eval nodeValue2157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2157) = mixedMoment B node2157 node2157Labels := rfl
  simpa [nodeValue2157, Sparse.eval] using hc.symm

theorem sound2158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2158 node2158Labels = Sparse.eval nodeValue2158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2158) = mixedMoment B node2158 node2158Labels := rfl
  simpa [nodeValue2158, Sparse.eval] using hc.symm

theorem sound2162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2162 node2162Labels = Sparse.eval nodeValue2162 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2162) = mixedMoment B node2162 node2162Labels := rfl
  simpa [nodeValue2162, Sparse.eval] using hc.symm

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

theorem zero2204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2204 node2204Labels = 0 := by
  exact mixedMoment_order_one B hB node2204 node2204Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = 0 := by
  exact mixedMoment_order_one B hB node2205 node2205Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2227 node2227Labels = 0 := by
  exact mixedMoment_order_one B hB node2227 node2227Labels 1
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

theorem sound2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2177 node2177Labels = Sparse.eval nodeValue2177 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2177) = mixedMoment B node2177 node2177Labels := rfl
  simpa [nodeValue2177, Sparse.eval] using hc.symm

theorem sound2178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2178 node2178Labels = Sparse.eval nodeValue2178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2178) = mixedMoment B node2178 node2178Labels := rfl
  simpa [nodeValue2178, Sparse.eval] using hc.symm

theorem sound2179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2179 node2179Labels = Sparse.eval nodeValue2179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2179) = mixedMoment B node2179 node2179Labels := rfl
  simpa [nodeValue2179, Sparse.eval] using hc.symm

theorem sound2189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2189 node2189Labels = Sparse.eval nodeValue2189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2189) = mixedMoment B node2189 node2189Labels := rfl
  simpa [nodeValue2189, Sparse.eval] using hc.symm

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

theorem sound2194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2194 node2194Labels = Sparse.eval nodeValue2194 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2194) = mixedMoment B node2194 node2194Labels := rfl
  simpa [nodeValue2194, Sparse.eval] using hc.symm

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

theorem sound2198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2198 node2198Labels = Sparse.eval nodeValue2198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2198) = mixedMoment B node2198 node2198Labels := rfl
  simpa [nodeValue2198, Sparse.eval] using hc.symm

theorem sound2199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2199 node2199Labels = Sparse.eval nodeValue2199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2199) = mixedMoment B node2199 node2199Labels := rfl
  simpa [nodeValue2199, Sparse.eval] using hc.symm

theorem sound2201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2201 node2201Labels = Sparse.eval nodeValue2201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2201) = mixedMoment B node2201 node2201Labels := rfl
  simpa [nodeValue2201, Sparse.eval] using hc.symm

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2204 node2204Labels = Sparse.eval nodeValue2204 (mixedVector B) := by
  simpa only [nodeValue2204, Sparse.eval_nil] using zero2204 B _hB _hF

theorem sound2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = Sparse.eval nodeValue2205 (mixedVector B) := by
  simpa only [nodeValue2205, Sparse.eval_nil] using zero2205 B _hB _hF

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2211 node2211Labels = Sparse.eval nodeValue2211 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2211) = mixedMoment B node2211 node2211Labels := rfl
  simpa [nodeValue2211, Sparse.eval] using hc.symm

theorem sound2213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2213 node2213Labels = Sparse.eval nodeValue2213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2213) = mixedMoment B node2213 node2213Labels := rfl
  simpa [nodeValue2213, Sparse.eval] using hc.symm

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

theorem sound2217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2217 node2217Labels = Sparse.eval nodeValue2217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2217) = mixedMoment B node2217 node2217Labels := rfl
  simpa [nodeValue2217, Sparse.eval] using hc.symm

theorem sound2220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2220 node2220Labels = Sparse.eval nodeValue2220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2220) = mixedMoment B node2220 node2220Labels := rfl
  simpa [nodeValue2220, Sparse.eval] using hc.symm

theorem sound2221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2221 node2221Labels = Sparse.eval nodeValue2221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2221) = mixedMoment B node2221 node2221Labels := rfl
  simpa [nodeValue2221, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

theorem sound2227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2227 node2227Labels = Sparse.eval nodeValue2227 (mixedVector B) := by
  simpa only [nodeValue2227, Sparse.eval_nil] using zero2227 B _hB _hF

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

theorem zero2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = 0 := by
  exact mixedMoment_order_one B hB node2264 node2264Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = 0 := by
  exact mixedMoment_order_one B hB node2265 node2265Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
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

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = Sparse.eval nodeValue2263 (mixedVector B) := by
  simpa only [nodeValue2263, Sparse.eval_nil] using zero2263 B _hB _hF

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = Sparse.eval nodeValue2265 (mixedVector B) := by
  simpa only [nodeValue2265, Sparse.eval_nil] using zero2265 B _hB _hF

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

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

theorem sound2661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2661 node2661Labels = Sparse.eval nodeValue2661 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2661) = mixedMoment B node2661 node2661Labels := rfl
  simpa [nodeValue2661, Sparse.eval] using hc.symm

theorem sound2669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2669 node2669Labels = Sparse.eval nodeValue2669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2669) = mixedMoment B node2669 node2669Labels := rfl
  simpa [nodeValue2669, Sparse.eval] using hc.symm

theorem sound2678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2678 node2678Labels = Sparse.eval nodeValue2678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2678) = mixedMoment B node2678 node2678Labels := rfl
  simpa [nodeValue2678, Sparse.eval] using hc.symm

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

theorem zero2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2720 node2720Labels = 0 := by
  exact mixedMoment_alpha B hF node2720 node2720Labels 1 permutation203
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

theorem sound2698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2698 node2698Labels = Sparse.eval nodeValue2698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2698) = mixedMoment B node2698 node2698Labels := rfl
  simpa [nodeValue2698, Sparse.eval] using hc.symm

theorem sound2708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2708 node2708Labels = Sparse.eval nodeValue2708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2708) = mixedMoment B node2708 node2708Labels := rfl
  simpa [nodeValue2708, Sparse.eval] using hc.symm

theorem sound2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2709 node2709Labels = Sparse.eval nodeValue2709 (mixedVector B) := by
  simpa only [nodeValue2709, Sparse.eval_nil] using zero2709 B _hB _hF

theorem sound2718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2718 node2718Labels = Sparse.eval nodeValue2718 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2718) = mixedMoment B node2718 node2718Labels := rfl
  simpa [nodeValue2718, Sparse.eval] using hc.symm

theorem sound2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2720 node2720Labels = Sparse.eval nodeValue2720 (mixedVector B) := by
  simpa only [nodeValue2720, Sparse.eval_nil] using zero2720 B _hB _hF

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

theorem sound2731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2731 node2731Labels = Sparse.eval nodeValue2731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2731) = mixedMoment B node2731 node2731Labels := rfl
  simpa [nodeValue2731, Sparse.eval] using hc.symm

theorem sound2732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2732 node2732Labels = Sparse.eval nodeValue2732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2732) = mixedMoment B node2732 node2732Labels := rfl
  simpa [nodeValue2732, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound3376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3376 node3376Labels = Sparse.eval nodeValue3376 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3376) = mixedMoment B node3376 node3376Labels := rfl
  simpa [nodeValue3376, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources77
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2468 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2468 + difference 0 1) (sourceB2468 + difference 1 0) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2468 + difference 0 1) (sourceB2468 + difference 1 0) sourceC2468) = raw33934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33934; decide +kernel
    rw [ha]
    exact (canonical33934 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2468 + difference 0 2) (sourceB2468 + difference 2 0) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA2468 + difference 0 2) (sourceB2468 + difference 2 0) sourceC2468) = raw33935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33935; decide +kernel
    rw [ha]
    exact (canonical33935 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2468 + difference 0 3) (sourceB2468 + difference 3 0) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA2468 + difference 0 3) (sourceB2468 + difference 3 0) sourceC2468) = raw33936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33936; decide +kernel
    rw [ha]
    exact (canonical33936 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2468 + difference 0 4) (sourceB2468 + difference 4 0) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA2468 + difference 0 4) (sourceB2468 + difference 4 0) sourceC2468) = raw33937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33937; decide +kernel
    rw [ha]
    exact (canonical33937 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2468 + difference 0 5) (sourceB2468 + difference 5 0) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA2468 + difference 0 5) (sourceB2468 + difference 5 0) sourceC2468) = raw33938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33938; decide +kernel
    rw [ha]
    exact (canonical33938 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2468 + difference 1 0) (sourceB2468 + difference 0 1) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA2468 + difference 1 0) (sourceB2468 + difference 0 1) sourceC2468) = raw33939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33939; decide +kernel
    rw [ha]
    exact (canonical33939 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2468 + difference 1 2) (sourceB2468 + difference 2 1) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2468 + difference 1 2) (sourceB2468 + difference 2 1) sourceC2468) = raw33940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33940; decide +kernel
    rw [ha]
    exact (canonical33940 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2468 + difference 1 3) (sourceB2468 + difference 3 1) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA2468 + difference 1 3) (sourceB2468 + difference 3 1) sourceC2468) = raw33941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33941; decide +kernel
    rw [ha]
    exact (canonical33941 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2468 + difference 1 4) (sourceB2468 + difference 4 1) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA2468 + difference 1 4) (sourceB2468 + difference 4 1) sourceC2468) = raw33942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33942; decide +kernel
    rw [ha]
    exact (canonical33942 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2468 + difference 1 5) (sourceB2468 + difference 5 1) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA2468 + difference 1 5) (sourceB2468 + difference 5 1) sourceC2468) = raw33943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33943; decide +kernel
    rw [ha]
    exact (canonical33943 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2468 + difference 2 0) (sourceB2468 + difference 0 2) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1673) := by
    have ha : (tripleCharges (sourceA2468 + difference 2 0) (sourceB2468 + difference 0 2) sourceC2468) = raw33944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33944; decide +kernel
    rw [ha]
    exact (canonical33944 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2468 + difference 2 1) (sourceB2468 + difference 1 2) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2150) := by
    have ha : (tripleCharges (sourceA2468 + difference 2 1) (sourceB2468 + difference 1 2) sourceC2468) = raw33945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33945; decide +kernel
    rw [ha]
    exact (canonical33945 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2468 + difference 2 3) (sourceB2468 + difference 3 2) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2468 + difference 2 3) (sourceB2468 + difference 3 2) sourceC2468) = raw33946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33946; decide +kernel
    rw [ha]
    exact (canonical33946 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2468 + difference 2 4) (sourceB2468 + difference 4 2) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA2468 + difference 2 4) (sourceB2468 + difference 4 2) sourceC2468) = raw33947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33947; decide +kernel
    rw [ha]
    exact (canonical33947 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2468 + difference 2 5) (sourceB2468 + difference 5 2) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA2468 + difference 2 5) (sourceB2468 + difference 5 2) sourceC2468) = raw33948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33948; decide +kernel
    rw [ha]
    exact (canonical33948 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2468 + difference 3 0) (sourceB2468 + difference 0 3) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1671) := by
    have ha : (tripleCharges (sourceA2468 + difference 3 0) (sourceB2468 + difference 0 3) sourceC2468) = raw33949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33949; decide +kernel
    rw [ha]
    exact (canonical33949 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2468 + difference 3 1) (sourceB2468 + difference 1 3) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2148) := by
    have ha : (tripleCharges (sourceA2468 + difference 3 1) (sourceB2468 + difference 1 3) sourceC2468) = raw33950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33950; decide +kernel
    rw [ha]
    exact (canonical33950 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2468 + difference 3 2) (sourceB2468 + difference 2 3) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2199) := by
    have ha : (tripleCharges (sourceA2468 + difference 3 2) (sourceB2468 + difference 2 3) sourceC2468) = raw33951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33951; decide +kernel
    rw [ha]
    exact (canonical33951 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2468 + difference 3 4) (sourceB2468 + difference 4 3) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA2468 + difference 3 4) (sourceB2468 + difference 4 3) sourceC2468) = raw33952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33952; decide +kernel
    rw [ha]
    exact (canonical33952 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2468 + difference 3 5) (sourceB2468 + difference 5 3) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2468 + difference 3 5) (sourceB2468 + difference 5 3) sourceC2468) = raw33953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33953; decide +kernel
    rw [ha]
    exact (canonical33953 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2468 + difference 4 0) (sourceB2468 + difference 0 4) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA2468 + difference 4 0) (sourceB2468 + difference 0 4) sourceC2468) = raw33954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33954; decide +kernel
    rw [ha]
    exact (canonical33954 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2468 + difference 4 1) (sourceB2468 + difference 1 4) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2154) := by
    have ha : (tripleCharges (sourceA2468 + difference 4 1) (sourceB2468 + difference 1 4) sourceC2468) = raw33955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33955; decide +kernel
    rw [ha]
    exact (canonical33955 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2468 + difference 4 2) (sourceB2468 + difference 2 4) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2468 + difference 4 2) (sourceB2468 + difference 2 4) sourceC2468) = raw33956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33956; decide +kernel
    rw [ha]
    exact (canonical33956 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2468 + difference 4 3) (sourceB2468 + difference 3 4) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2468 + difference 4 3) (sourceB2468 + difference 3 4) sourceC2468) = raw33957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33957; decide +kernel
    rw [ha]
    exact (canonical33957 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2468 + difference 4 5) (sourceB2468 + difference 5 4) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA2468 + difference 4 5) (sourceB2468 + difference 5 4) sourceC2468) = raw33958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33958; decide +kernel
    rw [ha]
    exact (canonical33958 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2468 + difference 5 0) (sourceB2468 + difference 0 5) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA2468 + difference 5 0) (sourceB2468 + difference 0 5) sourceC2468) = raw33959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33959; decide +kernel
    rw [ha]
    exact (canonical33959 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2468 + difference 5 1) (sourceB2468 + difference 1 5) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2147) := by
    have ha : (tripleCharges (sourceA2468 + difference 5 1) (sourceB2468 + difference 1 5) sourceC2468) = raw33960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33960; decide +kernel
    rw [ha]
    exact (canonical33960 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2468 + difference 5 2) (sourceB2468 + difference 2 5) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2198) := by
    have ha : (tripleCharges (sourceA2468 + difference 5 2) (sourceB2468 + difference 2 5) sourceC2468) = raw33961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33961; decide +kernel
    rw [ha]
    exact (canonical33961 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2468 + difference 5 3) (sourceB2468 + difference 3 5) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA2468 + difference 5 3) (sourceB2468 + difference 3 5) sourceC2468) = raw33962 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33962; decide +kernel
    rw [ha]
    exact (canonical33962 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2468 + difference 5 4) (sourceB2468 + difference 4 5) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA2468 + difference 5 4) (sourceB2468 + difference 4 5) sourceC2468) = raw33963 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33963; decide +kernel
    rw [ha]
    exact (canonical33963 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2468 sourceB2468 sourceC2468
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2468, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2469 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2469 + difference 0 1) (sourceB2469 + difference 1 0) sourceC2469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA2469 + difference 0 1) (sourceB2469 + difference 1 0) sourceC2469) = raw33964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2469 sourceB2469 sourceC2469 difference raw33964; decide +kernel
    rw [ha]
    exact (canonical33964 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2469 + difference 1 1) (sourceB2469 + difference 1 1) sourceC2469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA2469 + difference 1 1) (sourceB2469 + difference 1 1) sourceC2469) = raw33965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2469 sourceB2469 sourceC2469 difference raw33965; decide +kernel
    rw [ha]
    exact (canonical33965 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2469 + difference 2 1) (sourceB2469 + difference 1 2) sourceC2469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1805) := by
    have ha : (tripleCharges (sourceA2469 + difference 2 1) (sourceB2469 + difference 1 2) sourceC2469) = raw33966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2469 sourceB2469 sourceC2469 difference raw33966; decide +kernel
    rw [ha]
    exact (canonical33966 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2469 + difference 3 1) (sourceB2469 + difference 1 3) sourceC2469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1792) := by
    have ha : (tripleCharges (sourceA2469 + difference 3 1) (sourceB2469 + difference 1 3) sourceC2469) = raw33967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2469 sourceB2469 sourceC2469 difference raw33967; decide +kernel
    rw [ha]
    exact (canonical33967 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2469 + difference 4 1) (sourceB2469 + difference 1 4) sourceC2469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1794) := by
    have ha : (tripleCharges (sourceA2469 + difference 4 1) (sourceB2469 + difference 1 4) sourceC2469) = raw33968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2469 sourceB2469 sourceC2469 difference raw33968; decide +kernel
    rw [ha]
    exact (canonical33968 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2469 + difference 5 1) (sourceB2469 + difference 1 5) sourceC2469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1790) := by
    have ha : (tripleCharges (sourceA2469 + difference 5 1) (sourceB2469 + difference 1 5) sourceC2469) = raw33969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2469 sourceB2469 sourceC2469 difference raw33969; decide +kernel
    rw [ha]
    exact (canonical33969 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2469 + sourceB2469) sourceC2469) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2469 + sourceB2469) sourceC2469) = raw20196 := by
      apply Matrix.ext; unfold doubleCharges sourceA2469 sourceB2469 sourceC2469 raw20196; decide +kernel
    rw [ha]
    exact (canonical20196 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2469 sourceB2469 sourceC2469
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2469, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2474 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2474 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2474 + difference 0 1) (sourceB2474 + difference 1 0) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA2474 + difference 0 1) (sourceB2474 + difference 1 0) sourceC2474) = raw34049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34049; decide +kernel
    rw [ha]
    exact (canonical34049 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2474 + difference 0 2) (sourceB2474 + difference 2 0) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA2474 + difference 0 2) (sourceB2474 + difference 2 0) sourceC2474) = raw34050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34050; decide +kernel
    rw [ha]
    exact (canonical34050 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2474 + difference 0 3) (sourceB2474 + difference 3 0) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2474 + difference 0 3) (sourceB2474 + difference 3 0) sourceC2474) = raw34051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34051; decide +kernel
    rw [ha]
    exact (canonical34051 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2474 + difference 0 4) (sourceB2474 + difference 4 0) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2474 + difference 0 4) (sourceB2474 + difference 4 0) sourceC2474) = raw34052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34052; decide +kernel
    rw [ha]
    exact (canonical34052 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2474 + difference 0 5) (sourceB2474 + difference 5 0) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA2474 + difference 0 5) (sourceB2474 + difference 5 0) sourceC2474) = raw34053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34053; decide +kernel
    rw [ha]
    exact (canonical34053 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2474 + difference 1 0) (sourceB2474 + difference 0 1) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA2474 + difference 1 0) (sourceB2474 + difference 0 1) sourceC2474) = raw34054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34054; decide +kernel
    rw [ha]
    exact (canonical34054 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2474 + difference 1 2) (sourceB2474 + difference 2 1) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2474 + difference 1 2) (sourceB2474 + difference 2 1) sourceC2474) = raw34055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34055; decide +kernel
    rw [ha]
    exact (canonical34055 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2474 + difference 1 3) (sourceB2474 + difference 3 1) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2474 + difference 1 3) (sourceB2474 + difference 3 1) sourceC2474) = raw34056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34056; decide +kernel
    rw [ha]
    exact (canonical34056 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2474 + difference 1 4) (sourceB2474 + difference 4 1) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2474 + difference 1 4) (sourceB2474 + difference 4 1) sourceC2474) = raw34057 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34057; decide +kernel
    rw [ha]
    exact (canonical34057 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2474 + difference 1 5) (sourceB2474 + difference 5 1) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA2474 + difference 1 5) (sourceB2474 + difference 5 1) sourceC2474) = raw34058 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34058; decide +kernel
    rw [ha]
    exact (canonical34058 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2474 + difference 2 0) (sourceB2474 + difference 0 2) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1664) := by
    have ha : (tripleCharges (sourceA2474 + difference 2 0) (sourceB2474 + difference 0 2) sourceC2474) = raw34059 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34059; decide +kernel
    rw [ha]
    exact (canonical34059 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2474 + difference 2 1) (sourceB2474 + difference 1 2) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2141) := by
    have ha : (tripleCharges (sourceA2474 + difference 2 1) (sourceB2474 + difference 1 2) sourceC2474) = raw34060 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34060; decide +kernel
    rw [ha]
    exact (canonical34060 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2474 + difference 2 3) (sourceB2474 + difference 3 2) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2474 + difference 2 3) (sourceB2474 + difference 3 2) sourceC2474) = raw34061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34061; decide +kernel
    rw [ha]
    exact (canonical34061 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2474 + difference 2 4) (sourceB2474 + difference 4 2) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2474 + difference 2 4) (sourceB2474 + difference 4 2) sourceC2474) = raw34062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34062; decide +kernel
    rw [ha]
    exact (canonical34062 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2474 + difference 2 5) (sourceB2474 + difference 5 2) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA2474 + difference 2 5) (sourceB2474 + difference 5 2) sourceC2474) = raw34063 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34063; decide +kernel
    rw [ha]
    exact (canonical34063 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2474 + difference 3 0) (sourceB2474 + difference 0 3) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA2474 + difference 3 0) (sourceB2474 + difference 0 3) sourceC2474) = raw34064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34064; decide +kernel
    rw [ha]
    exact (canonical34064 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2474 + difference 3 1) (sourceB2474 + difference 1 3) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2144) := by
    have ha : (tripleCharges (sourceA2474 + difference 3 1) (sourceB2474 + difference 1 3) sourceC2474) = raw34065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34065; decide +kernel
    rw [ha]
    exact (canonical34065 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2474 + difference 3 2) (sourceB2474 + difference 2 3) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2474 + difference 3 2) (sourceB2474 + difference 2 3) sourceC2474) = raw34066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34066; decide +kernel
    rw [ha]
    exact (canonical34066 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2474 + difference 3 4) (sourceB2474 + difference 4 3) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2474 + difference 3 4) (sourceB2474 + difference 4 3) sourceC2474) = raw34067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34067; decide +kernel
    rw [ha]
    exact (canonical34067 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2474 + difference 3 5) (sourceB2474 + difference 5 3) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2474 + difference 3 5) (sourceB2474 + difference 5 3) sourceC2474) = raw34068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34068; decide +kernel
    rw [ha]
    exact (canonical34068 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2474 + difference 4 0) (sourceB2474 + difference 0 4) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA2474 + difference 4 0) (sourceB2474 + difference 0 4) sourceC2474) = raw34069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34069; decide +kernel
    rw [ha]
    exact (canonical34069 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2474 + difference 4 1) (sourceB2474 + difference 1 4) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2144) := by
    have ha : (tripleCharges (sourceA2474 + difference 4 1) (sourceB2474 + difference 1 4) sourceC2474) = raw34070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34070; decide +kernel
    rw [ha]
    exact (canonical34070 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2474 + difference 4 2) (sourceB2474 + difference 2 4) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2474 + difference 4 2) (sourceB2474 + difference 2 4) sourceC2474) = raw34071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34071; decide +kernel
    rw [ha]
    exact (canonical34071 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2474 + difference 4 3) (sourceB2474 + difference 3 4) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2474 + difference 4 3) (sourceB2474 + difference 3 4) sourceC2474) = raw34072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34072; decide +kernel
    rw [ha]
    exact (canonical34072 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2474 + difference 4 5) (sourceB2474 + difference 5 4) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2474 + difference 4 5) (sourceB2474 + difference 5 4) sourceC2474) = raw34073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34073; decide +kernel
    rw [ha]
    exact (canonical34073 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2474 + difference 5 0) (sourceB2474 + difference 0 5) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1663) := by
    have ha : (tripleCharges (sourceA2474 + difference 5 0) (sourceB2474 + difference 0 5) sourceC2474) = raw34074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34074; decide +kernel
    rw [ha]
    exact (canonical34074 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2474 + difference 5 1) (sourceB2474 + difference 1 5) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2140) := by
    have ha : (tripleCharges (sourceA2474 + difference 5 1) (sourceB2474 + difference 1 5) sourceC2474) = raw34075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34075; decide +kernel
    rw [ha]
    exact (canonical34075 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2474 + difference 5 2) (sourceB2474 + difference 2 5) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2189) := by
    have ha : (tripleCharges (sourceA2474 + difference 5 2) (sourceB2474 + difference 2 5) sourceC2474) = raw34076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34076; decide +kernel
    rw [ha]
    exact (canonical34076 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2474 + difference 5 3) (sourceB2474 + difference 3 5) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2474 + difference 5 3) (sourceB2474 + difference 3 5) sourceC2474) = raw34077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34077; decide +kernel
    rw [ha]
    exact (canonical34077 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2474 + difference 5 4) (sourceB2474 + difference 4 5) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2474 + difference 5 4) (sourceB2474 + difference 4 5) sourceC2474) = raw34078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34078; decide +kernel
    rw [ha]
    exact (canonical34078 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2474 sourceB2474 sourceC2474
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2474, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2478 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2478 + difference 0 1) (sourceB2478 + difference 1 0) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA2478 + difference 0 1) (sourceB2478 + difference 1 0) sourceC2478) = raw34126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34126; decide +kernel
    rw [ha]
    exact (canonical34126 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2478 + difference 0 2) (sourceB2478 + difference 2 0) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA2478 + difference 0 2) (sourceB2478 + difference 2 0) sourceC2478) = raw34127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34127; decide +kernel
    rw [ha]
    exact (canonical34127 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2478 + difference 0 3) (sourceB2478 + difference 3 0) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA2478 + difference 0 3) (sourceB2478 + difference 3 0) sourceC2478) = raw34128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34128; decide +kernel
    rw [ha]
    exact (canonical34128 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2478 + difference 0 4) (sourceB2478 + difference 4 0) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA2478 + difference 0 4) (sourceB2478 + difference 4 0) sourceC2478) = raw34129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34129; decide +kernel
    rw [ha]
    exact (canonical34129 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2478 + difference 0 5) (sourceB2478 + difference 5 0) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA2478 + difference 0 5) (sourceB2478 + difference 5 0) sourceC2478) = raw34130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34130; decide +kernel
    rw [ha]
    exact (canonical34130 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2478 + difference 1 0) (sourceB2478 + difference 0 1) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA2478 + difference 1 0) (sourceB2478 + difference 0 1) sourceC2478) = raw34131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34131; decide +kernel
    rw [ha]
    exact (canonical34131 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2478 + difference 1 2) (sourceB2478 + difference 2 1) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA2478 + difference 1 2) (sourceB2478 + difference 2 1) sourceC2478) = raw25634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25634; decide +kernel
    rw [ha]
    exact (canonical25634 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2478 + difference 1 3) (sourceB2478 + difference 3 1) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA2478 + difference 1 3) (sourceB2478 + difference 3 1) sourceC2478) = raw25635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25635; decide +kernel
    rw [ha]
    exact (canonical25635 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2478 + difference 1 4) (sourceB2478 + difference 4 1) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA2478 + difference 1 4) (sourceB2478 + difference 4 1) sourceC2478) = raw25636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25636; decide +kernel
    rw [ha]
    exact (canonical25636 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2478 + difference 1 5) (sourceB2478 + difference 5 1) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA2478 + difference 1 5) (sourceB2478 + difference 5 1) sourceC2478) = raw25637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25637; decide +kernel
    rw [ha]
    exact (canonical25637 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2478 + difference 2 0) (sourceB2478 + difference 0 2) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA2478 + difference 2 0) (sourceB2478 + difference 0 2) sourceC2478) = raw25644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25644; decide +kernel
    rw [ha]
    exact (canonical25644 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2478 + difference 2 1) (sourceB2478 + difference 1 2) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2145) := by
    have ha : (tripleCharges (sourceA2478 + difference 2 1) (sourceB2478 + difference 1 2) sourceC2478) = raw34132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34132; decide +kernel
    rw [ha]
    exact (canonical34132 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2478 + difference 2 3) (sourceB2478 + difference 3 2) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA2478 + difference 2 3) (sourceB2478 + difference 3 2) sourceC2478) = raw34133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34133; decide +kernel
    rw [ha]
    exact (canonical34133 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2478 + difference 2 4) (sourceB2478 + difference 4 2) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2478 + difference 2 4) (sourceB2478 + difference 4 2) sourceC2478) = raw34134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34134; decide +kernel
    rw [ha]
    exact (canonical34134 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2478 + difference 2 5) (sourceB2478 + difference 5 2) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA2478 + difference 2 5) (sourceB2478 + difference 5 2) sourceC2478) = raw34135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34135; decide +kernel
    rw [ha]
    exact (canonical34135 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2478 + difference 3 0) (sourceB2478 + difference 0 3) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA2478 + difference 3 0) (sourceB2478 + difference 0 3) sourceC2478) = raw25649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25649; decide +kernel
    rw [ha]
    exact (canonical25649 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2478 + difference 3 1) (sourceB2478 + difference 1 3) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2157) := by
    have ha : (tripleCharges (sourceA2478 + difference 3 1) (sourceB2478 + difference 1 3) sourceC2478) = raw34136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34136; decide +kernel
    rw [ha]
    exact (canonical34136 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2478 + difference 3 2) (sourceB2478 + difference 2 3) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2177) := by
    have ha : (tripleCharges (sourceA2478 + difference 3 2) (sourceB2478 + difference 2 3) sourceC2478) = raw34137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34137; decide +kernel
    rw [ha]
    exact (canonical34137 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2478 + difference 3 4) (sourceB2478 + difference 4 3) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2478 + difference 3 4) (sourceB2478 + difference 4 3) sourceC2478) = raw34138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34138; decide +kernel
    rw [ha]
    exact (canonical34138 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2478 + difference 3 5) (sourceB2478 + difference 5 3) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2478 + difference 3 5) (sourceB2478 + difference 5 3) sourceC2478) = raw34139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34139; decide +kernel
    rw [ha]
    exact (canonical34139 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2478 + difference 4 0) (sourceB2478 + difference 0 4) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA2478 + difference 4 0) (sourceB2478 + difference 0 4) sourceC2478) = raw25654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25654; decide +kernel
    rw [ha]
    exact (canonical25654 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2478 + difference 4 1) (sourceB2478 + difference 1 4) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2158) := by
    have ha : (tripleCharges (sourceA2478 + difference 4 1) (sourceB2478 + difference 1 4) sourceC2478) = raw34140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34140; decide +kernel
    rw [ha]
    exact (canonical34140 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2478 + difference 4 2) (sourceB2478 + difference 2 4) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2178) := by
    have ha : (tripleCharges (sourceA2478 + difference 4 2) (sourceB2478 + difference 2 4) sourceC2478) = raw34141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34141; decide +kernel
    rw [ha]
    exact (canonical34141 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2478 + difference 4 3) (sourceB2478 + difference 3 4) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA2478 + difference 4 3) (sourceB2478 + difference 3 4) sourceC2478) = raw34142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34142; decide +kernel
    rw [ha]
    exact (canonical34142 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2478 + difference 4 5) (sourceB2478 + difference 5 4) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2478 + difference 4 5) (sourceB2478 + difference 5 4) sourceC2478) = raw34143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34143; decide +kernel
    rw [ha]
    exact (canonical34143 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2478 + difference 5 0) (sourceB2478 + difference 0 5) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1686) := by
    have ha : (tripleCharges (sourceA2478 + difference 5 0) (sourceB2478 + difference 0 5) sourceC2478) = raw25659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25659; decide +kernel
    rw [ha]
    exact (canonical25659 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2478 + difference 5 1) (sourceB2478 + difference 1 5) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2162) := by
    have ha : (tripleCharges (sourceA2478 + difference 5 1) (sourceB2478 + difference 1 5) sourceC2478) = raw34144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34144; decide +kernel
    rw [ha]
    exact (canonical34144 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2478 + difference 5 2) (sourceB2478 + difference 2 5) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2179) := by
    have ha : (tripleCharges (sourceA2478 + difference 5 2) (sourceB2478 + difference 2 5) sourceC2478) = raw34145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34145; decide +kernel
    rw [ha]
    exact (canonical34145 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2478 + difference 5 3) (sourceB2478 + difference 3 5) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2221) := by
    have ha : (tripleCharges (sourceA2478 + difference 5 3) (sourceB2478 + difference 3 5) sourceC2478) = raw34146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34146; decide +kernel
    rw [ha]
    exact (canonical34146 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2478 + difference 5 4) (sourceB2478 + difference 4 5) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA2478 + difference 5 4) (sourceB2478 + difference 4 5) sourceC2478) = raw34147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34147; decide +kernel
    rw [ha]
    exact (canonical34147 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2478 sourceB2478 sourceC2478
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2478, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2479 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2479 + difference 0 1) (sourceB2479 + difference 1 0) sourceC2479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA2479 + difference 0 1) (sourceB2479 + difference 1 0) sourceC2479) = raw34148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2479 sourceB2479 sourceC2479 difference raw34148; decide +kernel
    rw [ha]
    exact (canonical34148 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2479 + difference 1 1) (sourceB2479 + difference 1 1) sourceC2479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA2479 + difference 1 1) (sourceB2479 + difference 1 1) sourceC2479) = raw34149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2479 sourceB2479 sourceC2479 difference raw34149; decide +kernel
    rw [ha]
    exact (canonical34149 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2479 + difference 2 1) (sourceB2479 + difference 1 2) sourceC2479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1806) := by
    have ha : (tripleCharges (sourceA2479 + difference 2 1) (sourceB2479 + difference 1 2) sourceC2479) = raw34150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2479 sourceB2479 sourceC2479 difference raw34150; decide +kernel
    rw [ha]
    exact (canonical34150 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2479 + difference 3 1) (sourceB2479 + difference 1 3) sourceC2479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1814) := by
    have ha : (tripleCharges (sourceA2479 + difference 3 1) (sourceB2479 + difference 1 3) sourceC2479) = raw34151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2479 sourceB2479 sourceC2479 difference raw34151; decide +kernel
    rw [ha]
    exact (canonical34151 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2479 + difference 4 1) (sourceB2479 + difference 1 4) sourceC2479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1816) := by
    have ha : (tripleCharges (sourceA2479 + difference 4 1) (sourceB2479 + difference 1 4) sourceC2479) = raw34152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2479 sourceB2479 sourceC2479 difference raw34152; decide +kernel
    rw [ha]
    exact (canonical34152 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2479 + difference 5 1) (sourceB2479 + difference 1 5) sourceC2479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1813) := by
    have ha : (tripleCharges (sourceA2479 + difference 5 1) (sourceB2479 + difference 1 5) sourceC2479) = raw34153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2479 sourceB2479 sourceC2479 difference raw34153; decide +kernel
    rw [ha]
    exact (canonical34153 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2479 + sourceB2479) sourceC2479) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2479 + sourceB2479) sourceC2479) = raw34154 := by
      apply Matrix.ext; unfold doubleCharges sourceA2479 sourceB2479 sourceC2479 raw34154; decide +kernel
    rw [ha]
    exact (canonical34154 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2479 sourceB2479 sourceC2479
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2479, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1986 : Integer.Sparse.reindex keyMap MixedData.row1986 = numericRow1986 := by decide +kernel

theorem numericCheck1986 (x : Master → ℝ) : Integer.Sparse.eval numericRow1986 x =
    (1 : ℝ) * reducedSource1986 x := by
  norm_num [numericRow1986, reducedSource1986, Integer.Sparse.eval, Sparse.eval, nodeValue1670, nodeValue1671, nodeValue1673, nodeValue1678, nodeValue1724, nodeValue2147, nodeValue2148, nodeValue2150, nodeValue2154, nodeValue2198, nodeValue2199, nodeValue2201, nodeValue2202, nodeValue2204, nodeValue2211, nodeValue2213, nodeValue2214, nodeValue2224, nodeValue2225, nodeValue2227, nodeValue2260, nodeValue2262, nodeValue2263, nodeValue2291, nodeValue2669, nodeValue2718, nodeValue2720, nodeValue2721, nodeValue2739]

theorem reindexCheck1987 : Integer.Sparse.reindex keyMap MixedData.row1987 = numericRow1987 := by decide +kernel

theorem numericCheck1987 (x : Master → ℝ) : Integer.Sparse.eval numericRow1987 x =
    (1 : ℝ) * reducedSource1987 x := by
  norm_num [numericRow1987, reducedSource1987, Integer.Sparse.eval, Sparse.eval, nodeValue1790, nodeValue1792, nodeValue1794, nodeValue1805, nodeValue2020, nodeValue3376, nodeValue4083]

theorem reindexCheck1992 : Integer.Sparse.reindex keyMap MixedData.row1992 = numericRow1992 := by decide +kernel

theorem numericCheck1992 (x : Master → ℝ) : Integer.Sparse.eval numericRow1992 x =
    (1 : ℝ) * reducedSource1992 x := by
  norm_num [numericRow1992, reducedSource1992, Integer.Sparse.eval, Sparse.eval, nodeValue1663, nodeValue1664, nodeValue1667, nodeValue1707, nodeValue2140, nodeValue2141, nodeValue2144, nodeValue2189, nodeValue2191, nodeValue2194, nodeValue2195, nodeValue2203, nodeValue2205, nodeValue2215, nodeValue2242, nodeValue2244, nodeValue2264, nodeValue2661, nodeValue2708, nodeValue2709, nodeValue2722]

theorem reindexCheck1996 : Integer.Sparse.reindex keyMap MixedData.row1996 = numericRow1996 := by decide +kernel

theorem numericCheck1996 (x : Master → ℝ) : Integer.Sparse.eval numericRow1996 x =
    (1 : ℝ) * reducedSource1996 x := by
  norm_num [numericRow1996, reducedSource1996, Integer.Sparse.eval, Sparse.eval, nodeValue1668, nodeValue1681, nodeValue1682, nodeValue1686, nodeValue1739, nodeValue2145, nodeValue2157, nodeValue2158, nodeValue2162, nodeValue2177, nodeValue2178, nodeValue2179, nodeValue2191, nodeValue2195, nodeValue2196, nodeValue2205, nodeValue2206, nodeValue2215, nodeValue2216, nodeValue2217, nodeValue2220, nodeValue2221, nodeValue2265, nodeValue2278, nodeValue2279, nodeValue2678, nodeValue2698, nodeValue2723, nodeValue2731, nodeValue2732]

theorem reindexCheck1997 : Integer.Sparse.reindex keyMap MixedData.row1997 = numericRow1997 := by decide +kernel

theorem numericCheck1997 (x : Master → ℝ) : Integer.Sparse.eval numericRow1997 x =
    (1 : ℝ) * reducedSource1997 x := by
  norm_num [numericRow1997, reducedSource1997, Integer.Sparse.eval, Sparse.eval, nodeValue1806, nodeValue1813, nodeValue1814, nodeValue1816, nodeValue2058, nodeValue3395, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1986 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1986 (mixedVector B) = 0 := by
  have h1670 : mixedVector B (Sum.inr 1670) = Sparse.eval nodeValue1670 (mixedVector B) := by
    change mixedMoment B node1670 node1670Labels = _
    exact sound1670 B hB hF
  have h1671 : mixedVector B (Sum.inr 1671) = Sparse.eval nodeValue1671 (mixedVector B) := by
    change mixedMoment B node1671 node1671Labels = _
    exact sound1671 B hB hF
  have h1673 : mixedVector B (Sum.inr 1673) = Sparse.eval nodeValue1673 (mixedVector B) := by
    change mixedMoment B node1673 node1673Labels = _
    exact sound1673 B hB hF
  have h1678 : mixedVector B (Sum.inr 1678) = Sparse.eval nodeValue1678 (mixedVector B) := by
    change mixedMoment B node1678 node1678Labels = _
    exact sound1678 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h2147 : mixedVector B (Sum.inr 2147) = Sparse.eval nodeValue2147 (mixedVector B) := by
    change mixedMoment B node2147 node2147Labels = _
    exact sound2147 B hB hF
  have h2148 : mixedVector B (Sum.inr 2148) = Sparse.eval nodeValue2148 (mixedVector B) := by
    change mixedMoment B node2148 node2148Labels = _
    exact sound2148 B hB hF
  have h2150 : mixedVector B (Sum.inr 2150) = Sparse.eval nodeValue2150 (mixedVector B) := by
    change mixedMoment B node2150 node2150Labels = _
    exact sound2150 B hB hF
  have h2154 : mixedVector B (Sum.inr 2154) = Sparse.eval nodeValue2154 (mixedVector B) := by
    change mixedMoment B node2154 node2154Labels = _
    exact sound2154 B hB hF
  have h2198 : mixedVector B (Sum.inr 2198) = Sparse.eval nodeValue2198 (mixedVector B) := by
    change mixedMoment B node2198 node2198Labels = _
    exact sound2198 B hB hF
  have h2199 : mixedVector B (Sum.inr 2199) = Sparse.eval nodeValue2199 (mixedVector B) := by
    change mixedMoment B node2199 node2199Labels = _
    exact sound2199 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h2211 : mixedVector B (Sum.inr 2211) = Sparse.eval nodeValue2211 (mixedVector B) := by
    change mixedMoment B node2211 node2211Labels = _
    exact sound2211 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  simpa only [sourceForm2468, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1670, h1671, h1673, h1678, h1724, h2147, h2148, h2150, h2154, h2198, h2199, h2201, h2202, h2204, h2211, h2213, h2214, h2224, h2225, h2227, h2260, h2262, h2263, h2291, h2669, h2718, h2720, h2721, h2739, reducedSource1986] using sourceEq2468 B hB

theorem rowSound1986 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1986 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1986, numericCheck1986, reducedZero1986 B hB hF, mul_zero]

theorem reducedZero1987 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1987 (mixedVector B) = 0 := by
  have h1790 : mixedVector B (Sum.inr 1790) = Sparse.eval nodeValue1790 (mixedVector B) := by
    change mixedMoment B node1790 node1790Labels = _
    exact sound1790 B hB hF
  have h1792 : mixedVector B (Sum.inr 1792) = Sparse.eval nodeValue1792 (mixedVector B) := by
    change mixedMoment B node1792 node1792Labels = _
    exact sound1792 B hB hF
  have h1794 : mixedVector B (Sum.inr 1794) = Sparse.eval nodeValue1794 (mixedVector B) := by
    change mixedMoment B node1794 node1794Labels = _
    exact sound1794 B hB hF
  have h1805 : mixedVector B (Sum.inr 1805) = Sparse.eval nodeValue1805 (mixedVector B) := by
    change mixedMoment B node1805 node1805Labels = _
    exact sound1805 B hB hF
  have h2020 : mixedVector B (Sum.inr 2020) = Sparse.eval nodeValue2020 (mixedVector B) := by
    change mixedMoment B node2020 node2020Labels = _
    exact sound2020 B hB hF
  have h3376 : mixedVector B (Sum.inr 3376) = Sparse.eval nodeValue3376 (mixedVector B) := by
    change mixedMoment B node3376 node3376Labels = _
    exact sound3376 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2469, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1790, h1792, h1794, h1805, h2020, h3376, h4083, reducedSource1987] using sourceEq2469 B hB

theorem rowSound1987 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1987 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1987, numericCheck1987, reducedZero1987 B hB hF, mul_zero]

theorem reducedZero1992 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1992 (mixedVector B) = 0 := by
  have h1663 : mixedVector B (Sum.inr 1663) = Sparse.eval nodeValue1663 (mixedVector B) := by
    change mixedMoment B node1663 node1663Labels = _
    exact sound1663 B hB hF
  have h1664 : mixedVector B (Sum.inr 1664) = Sparse.eval nodeValue1664 (mixedVector B) := by
    change mixedMoment B node1664 node1664Labels = _
    exact sound1664 B hB hF
  have h1667 : mixedVector B (Sum.inr 1667) = Sparse.eval nodeValue1667 (mixedVector B) := by
    change mixedMoment B node1667 node1667Labels = _
    exact sound1667 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h2140 : mixedVector B (Sum.inr 2140) = Sparse.eval nodeValue2140 (mixedVector B) := by
    change mixedMoment B node2140 node2140Labels = _
    exact sound2140 B hB hF
  have h2141 : mixedVector B (Sum.inr 2141) = Sparse.eval nodeValue2141 (mixedVector B) := by
    change mixedMoment B node2141 node2141Labels = _
    exact sound2141 B hB hF
  have h2144 : mixedVector B (Sum.inr 2144) = Sparse.eval nodeValue2144 (mixedVector B) := by
    change mixedMoment B node2144 node2144Labels = _
    exact sound2144 B hB hF
  have h2189 : mixedVector B (Sum.inr 2189) = Sparse.eval nodeValue2189 (mixedVector B) := by
    change mixedMoment B node2189 node2189Labels = _
    exact sound2189 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h2194 : mixedVector B (Sum.inr 2194) = Sparse.eval nodeValue2194 (mixedVector B) := by
    change mixedMoment B node2194 node2194Labels = _
    exact sound2194 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  simpa only [sourceForm2474, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1663, h1664, h1667, h1707, h2140, h2141, h2144, h2189, h2191, h2194, h2195, h2203, h2205, h2215, h2242, h2244, h2264, h2661, h2708, h2709, h2722, reducedSource1992] using sourceEq2474 B hB

theorem rowSound1992 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1992 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1992, numericCheck1992, reducedZero1992 B hB hF, mul_zero]

theorem reducedZero1996 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1996 (mixedVector B) = 0 := by
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
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h2145 : mixedVector B (Sum.inr 2145) = Sparse.eval nodeValue2145 (mixedVector B) := by
    change mixedMoment B node2145 node2145Labels = _
    exact sound2145 B hB hF
  have h2157 : mixedVector B (Sum.inr 2157) = Sparse.eval nodeValue2157 (mixedVector B) := by
    change mixedMoment B node2157 node2157Labels = _
    exact sound2157 B hB hF
  have h2158 : mixedVector B (Sum.inr 2158) = Sparse.eval nodeValue2158 (mixedVector B) := by
    change mixedMoment B node2158 node2158Labels = _
    exact sound2158 B hB hF
  have h2162 : mixedVector B (Sum.inr 2162) = Sparse.eval nodeValue2162 (mixedVector B) := by
    change mixedMoment B node2162 node2162Labels = _
    exact sound2162 B hB hF
  have h2177 : mixedVector B (Sum.inr 2177) = Sparse.eval nodeValue2177 (mixedVector B) := by
    change mixedMoment B node2177 node2177Labels = _
    exact sound2177 B hB hF
  have h2178 : mixedVector B (Sum.inr 2178) = Sparse.eval nodeValue2178 (mixedVector B) := by
    change mixedMoment B node2178 node2178Labels = _
    exact sound2178 B hB hF
  have h2179 : mixedVector B (Sum.inr 2179) = Sparse.eval nodeValue2179 (mixedVector B) := by
    change mixedMoment B node2179 node2179Labels = _
    exact sound2179 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
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
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2221 : mixedVector B (Sum.inr 2221) = Sparse.eval nodeValue2221 (mixedVector B) := by
    change mixedMoment B node2221 node2221Labels = _
    exact sound2221 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h2678 : mixedVector B (Sum.inr 2678) = Sparse.eval nodeValue2678 (mixedVector B) := by
    change mixedMoment B node2678 node2678Labels = _
    exact sound2678 B hB hF
  have h2698 : mixedVector B (Sum.inr 2698) = Sparse.eval nodeValue2698 (mixedVector B) := by
    change mixedMoment B node2698 node2698Labels = _
    exact sound2698 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  simpa only [sourceForm2478, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1668, h1681, h1682, h1686, h1739, h2145, h2157, h2158, h2162, h2177, h2178, h2179, h2191, h2195, h2196, h2205, h2206, h2215, h2216, h2217, h2220, h2221, h2265, h2278, h2279, h2678, h2698, h2723, h2731, h2732, reducedSource1996] using sourceEq2478 B hB

theorem rowSound1996 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1996 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1996, numericCheck1996, reducedZero1996 B hB hF, mul_zero]

theorem reducedZero1997 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1997 (mixedVector B) = 0 := by
  have h1806 : mixedVector B (Sum.inr 1806) = Sparse.eval nodeValue1806 (mixedVector B) := by
    change mixedMoment B node1806 node1806Labels = _
    exact sound1806 B hB hF
  have h1813 : mixedVector B (Sum.inr 1813) = Sparse.eval nodeValue1813 (mixedVector B) := by
    change mixedMoment B node1813 node1813Labels = _
    exact sound1813 B hB hF
  have h1814 : mixedVector B (Sum.inr 1814) = Sparse.eval nodeValue1814 (mixedVector B) := by
    change mixedMoment B node1814 node1814Labels = _
    exact sound1814 B hB hF
  have h1816 : mixedVector B (Sum.inr 1816) = Sparse.eval nodeValue1816 (mixedVector B) := by
    change mixedMoment B node1816 node1816Labels = _
    exact sound1816 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2479, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1806, h1813, h1814, h1816, h2058, h3395, h4084, reducedSource1997] using sourceEq2479 B hB

theorem rowSound1997 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1997 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1997, numericCheck1997, reducedZero1997 B hB hF, mul_zero]

theorem sourceRowsAt1984 : MixedData.sourceRows (1984 : Fin 2425) =
    MixedData.row1984 := by decide +kernel

theorem sourceRowsAt1985 : MixedData.sourceRows (1985 : Fin 2425) =
    MixedData.row1985 := by decide +kernel

theorem sourceRowsAt1986 : MixedData.sourceRows (1986 : Fin 2425) =
    MixedData.row1986 := by decide +kernel

theorem sourceRowsAt1987 : MixedData.sourceRows (1987 : Fin 2425) =
    MixedData.row1987 := by decide +kernel

theorem sourceRowsAt1988 : MixedData.sourceRows (1988 : Fin 2425) =
    MixedData.row1988 := by decide +kernel

theorem sourceRowsAt1989 : MixedData.sourceRows (1989 : Fin 2425) =
    MixedData.row1989 := by decide +kernel

theorem sourceRowsAt1990 : MixedData.sourceRows (1990 : Fin 2425) =
    MixedData.row1990 := by decide +kernel

theorem sourceRowsAt1991 : MixedData.sourceRows (1991 : Fin 2425) =
    MixedData.row1991 := by decide +kernel

theorem sourceRowsAt1992 : MixedData.sourceRows (1992 : Fin 2425) =
    MixedData.row1992 := by decide +kernel

theorem sourceRowsAt1993 : MixedData.sourceRows (1993 : Fin 2425) =
    MixedData.row1993 := by decide +kernel

theorem sourceRowsAt1994 : MixedData.sourceRows (1994 : Fin 2425) =
    MixedData.row1994 := by decide +kernel

theorem sourceRowsAt1995 : MixedData.sourceRows (1995 : Fin 2425) =
    MixedData.row1995 := by decide +kernel

theorem sourceRowsAt1996 : MixedData.sourceRows (1996 : Fin 2425) =
    MixedData.row1996 := by decide +kernel

theorem sourceRowsAt1997 : MixedData.sourceRows (1997 : Fin 2425) =
    MixedData.row1997 := by decide +kernel

theorem sourceRowsAt1998 : MixedData.sourceRows (1998 : Fin 2425) =
    MixedData.row1998 := by decide +kernel

theorem sourceRowsAt1999 : MixedData.sourceRows (1999 : Fin 2425) =
    MixedData.row1999 := by decide +kernel

theorem chunkSound124_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 124) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1984 ∨ k.val = 1985 ∨ k.val = 1986 ∨ k.val = 1987 ∨ k.val = 1988 ∨ k.val = 1989 ∨ k.val = 1990 ∨ k.val = 1991 ∨ k.val = 1992 ∨ k.val = 1993 ∨ k.val = 1994 ∨ k.val = 1995 ∨ k.val = 1996 ∨ k.val = 1997 ∨ k.val = 1998 ∨ k.val = 1999 := by omega
  rcases heq with h1984 | h1985 | h1986 | h1987 | h1988 | h1989 | h1990 | h1991 | h1992 | h1993 | h1994 | h1995 | h1996 | h1997 | h1998 | h1999
  · have he : k = (1984 : Fin 2425) := Fin.ext h1984
    subst k
    rw [sourceRowsAt1984]
    exact rowSound1984_e B hB hF
  · have he : k = (1985 : Fin 2425) := Fin.ext h1985
    subst k
    rw [sourceRowsAt1985]
    exact rowSound1985_e B hB hF
  · have he : k = (1986 : Fin 2425) := Fin.ext h1986
    subst k
    rw [sourceRowsAt1986]
    exact rowSound1986 B hB hF
  · have he : k = (1987 : Fin 2425) := Fin.ext h1987
    subst k
    rw [sourceRowsAt1987]
    exact rowSound1987 B hB hF
  · have he : k = (1988 : Fin 2425) := Fin.ext h1988
    subst k
    rw [sourceRowsAt1988]
    exact rowSound1988_e B hB hF
  · have he : k = (1989 : Fin 2425) := Fin.ext h1989
    subst k
    rw [sourceRowsAt1989]
    exact rowSound1989_e B hB hF
  · have he : k = (1990 : Fin 2425) := Fin.ext h1990
    subst k
    rw [sourceRowsAt1990]
    exact rowSound1990_e B hB hF
  · have he : k = (1991 : Fin 2425) := Fin.ext h1991
    subst k
    rw [sourceRowsAt1991]
    exact rowSound1991_e B hB hF
  · have he : k = (1992 : Fin 2425) := Fin.ext h1992
    subst k
    rw [sourceRowsAt1992]
    exact rowSound1992 B hB hF
  · have he : k = (1993 : Fin 2425) := Fin.ext h1993
    subst k
    rw [sourceRowsAt1993]
    exact rowSound1993_e B hB hF
  · have he : k = (1994 : Fin 2425) := Fin.ext h1994
    subst k
    rw [sourceRowsAt1994]
    exact rowSound1994_e B hB hF
  · have he : k = (1995 : Fin 2425) := Fin.ext h1995
    subst k
    rw [sourceRowsAt1995]
    exact rowSound1995_e B hB hF
  · have he : k = (1996 : Fin 2425) := Fin.ext h1996
    subst k
    rw [sourceRowsAt1996]
    exact rowSound1996 B hB hF
  · have he : k = (1997 : Fin 2425) := Fin.ext h1997
    subst k
    rw [sourceRowsAt1997]
    exact rowSound1997 B hB hF
  · have he : k = (1998 : Fin 2425) := Fin.ext h1998
    subst k
    rw [sourceRowsAt1998]
    exact rowSound1998_e B hB hF
  · have he : k = (1999 : Fin 2425) := Fin.ext h1999
    subst k
    rw [sourceRowsAt1999]
    exact rowSound1999_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124_e_oai
