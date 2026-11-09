-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound129_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:46:59.99764+00:00
-- url     : https://prove2.me/submissions/36022076-ca7f-4f1c-a8c5-64a71a5d2748

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2064_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2065_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2066_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2067_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2069_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2071_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2073_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2074_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2075_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2076_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2077_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2078_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32155 raw32155Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw32155 raw32155Labels = mixedMoment B raw32155step0 raw32155step0Labels := by
      have ha : raw32155step0 = (fun i j => raw32155 (permutation658 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32155step0 raw32155; decide +kernel
      have hl : raw32155step0Labels = raw32155Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32155 raw32155Labels permutation658 permutation7
    mixedMoment B raw32155step0 raw32155step0Labels = mixedMoment B raw32155step1 raw32155step1Labels := by
      have ha : raw32155step1 = raw32155step0 := by apply Matrix.ext; unfold raw32155step1 raw32155step0; decide +kernel
      have hl : raw32155step0Labels = labelEmbedding1 ∘ raw32155step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32155step0 raw32155step0Labels raw32155step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical32156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32156 raw32156Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw32156 raw32156Labels = mixedMoment B raw32156step0 raw32156step0Labels := by
      have hz : ∀ j, raw32156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32156step0 = (fun i j => raw32156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32156step0 raw32156; decide +kernel
      have hl : raw32156step0Labels = raw32156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32156 raw32156Labels permutation346 hz
    mixedMoment B raw32156step0 raw32156step0Labels = mixedMoment B raw32156step1 raw32156step1Labels := by
      have ha : raw32156step1 = (fun i j => raw32156step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32156step1 raw32156step0; decide +kernel
      have hl : raw32156step1Labels = raw32156step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32156step0 raw32156step0Labels permutation145 permutation7
    mixedMoment B raw32156step1 raw32156step1Labels = mixedMoment B raw32156step2 raw32156step2Labels := by
      have ha : raw32156step2 = raw32156step1 := by apply Matrix.ext; unfold raw32156step2 raw32156step1; decide +kernel
      have hl : raw32156step1Labels = labelEmbedding1 ∘ raw32156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32156step1 raw32156step1Labels raw32156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical32157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32157 raw32157Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw32157 raw32157Labels = mixedMoment B raw32157step0 raw32157step0Labels := by
      have hz : ∀ j, raw32157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32157step0 = (fun i j => raw32157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32157step0 raw32157; decide +kernel
      have hl : raw32157step0Labels = raw32157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32157 raw32157Labels permutation346 hz
    mixedMoment B raw32157step0 raw32157step0Labels = mixedMoment B raw32157step1 raw32157step1Labels := by
      have ha : raw32157step1 = (fun i j => raw32157step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32157step1 raw32157step0; decide +kernel
      have hl : raw32157step1Labels = raw32157step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32157step0 raw32157step0Labels permutation145 permutation7
    mixedMoment B raw32157step1 raw32157step1Labels = mixedMoment B raw32157step2 raw32157step2Labels := by
      have ha : raw32157step2 = raw32157step1 := by apply Matrix.ext; unfold raw32157step2 raw32157step1; decide +kernel
      have hl : raw32157step1Labels = labelEmbedding1 ∘ raw32157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32157step1 raw32157step1Labels raw32157step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical32158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32158 raw32158Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw32158 raw32158Labels = mixedMoment B raw32158step0 raw32158step0Labels := by
      have hz : ∀ j, raw32158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32158step0 = (fun i j => raw32158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32158step0 raw32158; decide +kernel
      have hl : raw32158step0Labels = raw32158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32158 raw32158Labels permutation346 hz
    mixedMoment B raw32158step0 raw32158step0Labels = mixedMoment B raw32158step1 raw32158step1Labels := by
      have ha : raw32158step1 = (fun i j => raw32158step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32158step1 raw32158step0; decide +kernel
      have hl : raw32158step1Labels = raw32158step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32158step0 raw32158step0Labels permutation145 permutation7
    mixedMoment B raw32158step1 raw32158step1Labels = mixedMoment B raw32158step2 raw32158step2Labels := by
      have ha : raw32158step2 = raw32158step1 := by apply Matrix.ext; unfold raw32158step2 raw32158step1; decide +kernel
      have hl : raw32158step1Labels = labelEmbedding1 ∘ raw32158step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32158step1 raw32158step1Labels raw32158step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical32165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32165 raw32165Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw32165 raw32165Labels = mixedMoment B raw32165step0 raw32165step0Labels := by
      have ha : raw32165step0 = (fun i j => raw32165 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32165step0 raw32165; decide +kernel
      have hl : raw32165step0Labels = raw32165Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32165 raw32165Labels permutation162 permutation5
    mixedMoment B raw32165step0 raw32165step0Labels = mixedMoment B raw32165step1 raw32165step1Labels := by
      have ha : raw32165step1 = -raw32165step0 := by apply Matrix.ext; change ∀ i j, raw32165step1 i j = -(raw32165step0 i j); unfold raw32165step1 raw32165step0; decide +kernel
      have hl : raw32165step1Labels = raw32165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32165step1 raw32165step1Labels = mixedMoment B raw32165step2 raw32165step2Labels := by
      have ha : raw32165step2 = raw32165step1 := by apply Matrix.ext; unfold raw32165step2 raw32165step1; decide +kernel
      have hl : raw32165step1Labels = labelEmbedding1 ∘ raw32165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32165step1 raw32165step1Labels raw32165step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

theorem canonical32170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32170 raw32170Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw32170 raw32170Labels = mixedMoment B raw32170step0 raw32170step0Labels := by
      have hz : ∀ j, raw32170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32170step0 = (fun i j => raw32170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32170step0 raw32170; decide +kernel
      have hl : raw32170step0Labels = raw32170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32170 raw32170Labels permutation346 hz
    mixedMoment B raw32170step0 raw32170step0Labels = mixedMoment B raw32170step1 raw32170step1Labels := by
      have ha : raw32170step1 = (fun i j => raw32170step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32170step1 raw32170step0; decide +kernel
      have hl : raw32170step1Labels = raw32170step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32170step0 raw32170step0Labels permutation36 permutation5
    mixedMoment B raw32170step1 raw32170step1Labels = mixedMoment B raw32170step2 raw32170step2Labels := by
      have ha : raw32170step2 = -raw32170step1 := by apply Matrix.ext; change ∀ i j, raw32170step2 i j = -(raw32170step1 i j); unfold raw32170step2 raw32170step1; decide +kernel
      have hl : raw32170step2Labels = raw32170step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32170step2 raw32170step2Labels = mixedMoment B raw32170step3 raw32170step3Labels := by
      have ha : raw32170step3 = raw32170step2 := by apply Matrix.ext; unfold raw32170step3 raw32170step2; decide +kernel
      have hl : raw32170step2Labels = labelEmbedding1 ∘ raw32170step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32170step2 raw32170step2Labels raw32170step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

theorem canonical32175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32175 raw32175Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw32175 raw32175Labels = mixedMoment B raw32175step0 raw32175step0Labels := by
      have hz : ∀ j, raw32175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32175step0 = (fun i j => raw32175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32175step0 raw32175; decide +kernel
      have hl : raw32175step0Labels = raw32175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32175 raw32175Labels permutation346 hz
    mixedMoment B raw32175step0 raw32175step0Labels = mixedMoment B raw32175step1 raw32175step1Labels := by
      have ha : raw32175step1 = (fun i j => raw32175step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32175step1 raw32175step0; decide +kernel
      have hl : raw32175step1Labels = raw32175step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32175step0 raw32175step0Labels permutation127 permutation5
    mixedMoment B raw32175step1 raw32175step1Labels = mixedMoment B raw32175step2 raw32175step2Labels := by
      have ha : raw32175step2 = raw32175step1 := by apply Matrix.ext; unfold raw32175step2 raw32175step1; decide +kernel
      have hl : raw32175step1Labels = labelEmbedding1 ∘ raw32175step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32175step1 raw32175step1Labels raw32175step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical32180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32180 raw32180Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw32180 raw32180Labels = mixedMoment B raw32180step0 raw32180step0Labels := by
      have hz : ∀ j, raw32180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32180step0 = (fun i j => raw32180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32180step0 raw32180; decide +kernel
      have hl : raw32180step0Labels = raw32180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32180 raw32180Labels permutation346 hz
    mixedMoment B raw32180step0 raw32180step0Labels = mixedMoment B raw32180step1 raw32180step1Labels := by
      have ha : raw32180step1 = (fun i j => raw32180step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32180step1 raw32180step0; decide +kernel
      have hl : raw32180step1Labels = raw32180step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32180step0 raw32180step0Labels permutation33 permutation5
    mixedMoment B raw32180step1 raw32180step1Labels = mixedMoment B raw32180step2 raw32180step2Labels := by
      have ha : raw32180step2 = -raw32180step1 := by apply Matrix.ext; change ∀ i j, raw32180step2 i j = -(raw32180step1 i j); unfold raw32180step2 raw32180step1; decide +kernel
      have hl : raw32180step2Labels = raw32180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32180step2 raw32180step2Labels = mixedMoment B raw32180step3 raw32180step3Labels := by
      have ha : raw32180step3 = raw32180step2 := by apply Matrix.ext; unfold raw32180step3 raw32180step2; decide +kernel
      have hl : raw32180step2Labels = labelEmbedding1 ∘ raw32180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32180step2 raw32180step2Labels raw32180step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35791 raw35791Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw35791 raw35791Labels = mixedMoment B raw35791step0 raw35791step0Labels := by
      have ha : raw35791step0 = (fun i j => raw35791 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35791step0 raw35791; decide +kernel
      have hl : raw35791step0Labels = raw35791Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35791 raw35791Labels permutation289 permutation7
    mixedMoment B raw35791step0 raw35791step0Labels = mixedMoment B raw35791step1 raw35791step1Labels := by
      have ha : raw35791step1 = -raw35791step0 := by apply Matrix.ext; change ∀ i j, raw35791step1 i j = -(raw35791step0 i j); unfold raw35791step1 raw35791step0; decide +kernel
      have hl : raw35791step1Labels = raw35791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35791step1 raw35791step1Labels = mixedMoment B raw35791step2 raw35791step2Labels := by
      have ha : raw35791step2 = raw35791step1 := by apply Matrix.ext; unfold raw35791step2 raw35791step1; decide +kernel
      have hl : raw35791step1Labels = labelEmbedding1 ∘ raw35791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35791step1 raw35791step1Labels raw35791step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

theorem canonical35792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35792 raw35792Labels = mixedMoment B node3798 node3798Labels := by
  calc
    mixedMoment B raw35792 raw35792Labels = mixedMoment B raw35792step0 raw35792step0Labels := by
      have ha : raw35792step0 = (fun i j => raw35792 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35792step0 raw35792; decide +kernel
      have hl : raw35792step0Labels = raw35792Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35792 raw35792Labels permutation289 permutation7
    mixedMoment B raw35792step0 raw35792step0Labels = mixedMoment B raw35792step1 raw35792step1Labels := by
      have ha : raw35792step1 = -raw35792step0 := by apply Matrix.ext; change ∀ i j, raw35792step1 i j = -(raw35792step0 i j); unfold raw35792step1 raw35792step0; decide +kernel
      have hl : raw35792step1Labels = raw35792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35792step1 raw35792step1Labels = mixedMoment B raw35792step2 raw35792step2Labels := by
      have ha : raw35792step2 = raw35792step1 := by apply Matrix.ext; unfold raw35792step2 raw35792step1; decide +kernel
      have hl : raw35792step1Labels = labelEmbedding1 ∘ raw35792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35792step1 raw35792step1Labels raw35792step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3798 node3798Labels := by rfl

theorem canonical35793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35793 raw35793Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw35793 raw35793Labels = mixedMoment B raw35793step0 raw35793step0Labels := by
      have ha : raw35793step0 = (fun i j => raw35793 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35793step0 raw35793; decide +kernel
      have hl : raw35793step0Labels = raw35793Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35793 raw35793Labels permutation289 permutation7
    mixedMoment B raw35793step0 raw35793step0Labels = mixedMoment B raw35793step1 raw35793step1Labels := by
      have ha : raw35793step1 = -raw35793step0 := by apply Matrix.ext; change ∀ i j, raw35793step1 i j = -(raw35793step0 i j); unfold raw35793step1 raw35793step0; decide +kernel
      have hl : raw35793step1Labels = raw35793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35793step1 raw35793step1Labels = mixedMoment B raw35793step2 raw35793step2Labels := by
      have ha : raw35793step2 = raw35793step1 := by apply Matrix.ext; unfold raw35793step2 raw35793step1; decide +kernel
      have hl : raw35793step1Labels = labelEmbedding1 ∘ raw35793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35793step1 raw35793step1Labels raw35793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical35794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35794 raw35794Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw35794 raw35794Labels = mixedMoment B raw35794step0 raw35794step0Labels := by
      have ha : raw35794step0 = (fun i j => raw35794 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35794step0 raw35794; decide +kernel
      have hl : raw35794step0Labels = raw35794Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35794 raw35794Labels permutation291 permutation7
    mixedMoment B raw35794step0 raw35794step0Labels = mixedMoment B raw35794step1 raw35794step1Labels := by
      have ha : raw35794step1 = -raw35794step0 := by apply Matrix.ext; change ∀ i j, raw35794step1 i j = -(raw35794step0 i j); unfold raw35794step1 raw35794step0; decide +kernel
      have hl : raw35794step1Labels = raw35794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35794step1 raw35794step1Labels = mixedMoment B raw35794step2 raw35794step2Labels := by
      have ha : raw35794step2 = raw35794step1 := by apply Matrix.ext; unfold raw35794step2 raw35794step1; decide +kernel
      have hl : raw35794step1Labels = labelEmbedding1 ∘ raw35794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35794step1 raw35794step1Labels raw35794step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical35795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35795 raw35795Labels = mixedMoment B node3844 node3844Labels := by
  calc
    mixedMoment B raw35795 raw35795Labels = mixedMoment B raw35795step0 raw35795step0Labels := by
      have ha : raw35795step0 = (fun i j => raw35795 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35795step0 raw35795; decide +kernel
      have hl : raw35795step0Labels = raw35795Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35795 raw35795Labels permutation289 permutation7
    mixedMoment B raw35795step0 raw35795step0Labels = mixedMoment B raw35795step1 raw35795step1Labels := by
      have ha : raw35795step1 = -raw35795step0 := by apply Matrix.ext; change ∀ i j, raw35795step1 i j = -(raw35795step0 i j); unfold raw35795step1 raw35795step0; decide +kernel
      have hl : raw35795step1Labels = raw35795step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35795step1 raw35795step1Labels = mixedMoment B raw35795step2 raw35795step2Labels := by
      have ha : raw35795step2 = raw35795step1 := by apply Matrix.ext; unfold raw35795step2 raw35795step1; decide +kernel
      have hl : raw35795step1Labels = labelEmbedding1 ∘ raw35795step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35795step1 raw35795step1Labels raw35795step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3844 node3844Labels := by rfl

theorem canonical35796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35796 raw35796Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw35796 raw35796Labels = mixedMoment B raw35796step0 raw35796step0Labels := by
      have ha : raw35796step0 = (fun i j => raw35796 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35796step0 raw35796; decide +kernel
      have hl : raw35796step0Labels = raw35796Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35796 raw35796Labels permutation212 permutation5
    mixedMoment B raw35796step0 raw35796step0Labels = mixedMoment B raw35796step1 raw35796step1Labels := by
      have ha : raw35796step1 = -raw35796step0 := by apply Matrix.ext; change ∀ i j, raw35796step1 i j = -(raw35796step0 i j); unfold raw35796step1 raw35796step0; decide +kernel
      have hl : raw35796step1Labels = raw35796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35796step1 raw35796step1Labels = mixedMoment B raw35796step2 raw35796step2Labels := by
      have ha : raw35796step2 = raw35796step1 := by apply Matrix.ext; unfold raw35796step2 raw35796step1; decide +kernel
      have hl : raw35796step1Labels = labelEmbedding1 ∘ raw35796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35796step1 raw35796step1Labels raw35796step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical35797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35797 raw35797Labels = mixedMoment B node3900 node3900Labels := by
  calc
    mixedMoment B raw35797 raw35797Labels = mixedMoment B raw35797step0 raw35797step0Labels := by
      have ha : raw35797step0 = (fun i j => raw35797 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35797step0 raw35797; decide +kernel
      have hl : raw35797step0Labels = raw35797Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35797 raw35797Labels permutation184 permutation5
    mixedMoment B raw35797step0 raw35797step0Labels = mixedMoment B raw35797step1 raw35797step1Labels := by
      have ha : raw35797step1 = -raw35797step0 := by apply Matrix.ext; change ∀ i j, raw35797step1 i j = -(raw35797step0 i j); unfold raw35797step1 raw35797step0; decide +kernel
      have hl : raw35797step1Labels = raw35797step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35797step1 raw35797step1Labels = mixedMoment B raw35797step2 raw35797step2Labels := by
      have ha : raw35797step2 = raw35797step1 := by apply Matrix.ext; unfold raw35797step2 raw35797step1; decide +kernel
      have hl : raw35797step1Labels = labelEmbedding1 ∘ raw35797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35797step1 raw35797step1Labels raw35797step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3900 node3900Labels := by rfl

theorem canonical35798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35798 raw35798Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw35798 raw35798Labels = mixedMoment B raw35798step0 raw35798step0Labels := by
      have ha : raw35798step0 = (fun i j => raw35798 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35798step0 raw35798; decide +kernel
      have hl : raw35798step0Labels = raw35798Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35798 raw35798Labels permutation212 permutation5
    mixedMoment B raw35798step0 raw35798step0Labels = mixedMoment B raw35798step1 raw35798step1Labels := by
      have ha : raw35798step1 = -raw35798step0 := by apply Matrix.ext; change ∀ i j, raw35798step1 i j = -(raw35798step0 i j); unfold raw35798step1 raw35798step0; decide +kernel
      have hl : raw35798step1Labels = raw35798step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35798step1 raw35798step1Labels = mixedMoment B raw35798step2 raw35798step2Labels := by
      have ha : raw35798step2 = raw35798step1 := by apply Matrix.ext; unfold raw35798step2 raw35798step1; decide +kernel
      have hl : raw35798step1Labels = labelEmbedding1 ∘ raw35798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35798step1 raw35798step1Labels raw35798step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical35799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35799 raw35799Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw35799 raw35799Labels = mixedMoment B raw35799step0 raw35799step0Labels := by
      have ha : raw35799step0 = (fun i j => raw35799 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35799step0 raw35799; decide +kernel
      have hl : raw35799step0Labels = raw35799Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35799 raw35799Labels permutation234 permutation5
    mixedMoment B raw35799step0 raw35799step0Labels = mixedMoment B raw35799step1 raw35799step1Labels := by
      have ha : raw35799step1 = -raw35799step0 := by apply Matrix.ext; change ∀ i j, raw35799step1 i j = -(raw35799step0 i j); unfold raw35799step1 raw35799step0; decide +kernel
      have hl : raw35799step1Labels = raw35799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35799step1 raw35799step1Labels = mixedMoment B raw35799step2 raw35799step2Labels := by
      have ha : raw35799step2 = raw35799step1 := by apply Matrix.ext; unfold raw35799step2 raw35799step1; decide +kernel
      have hl : raw35799step1Labels = labelEmbedding1 ∘ raw35799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35799step1 raw35799step1Labels raw35799step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical35800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35800 raw35800Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw35800 raw35800Labels = mixedMoment B raw35800step0 raw35800step0Labels := by
      have ha : raw35800step0 = (fun i j => raw35800 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35800step0 raw35800; decide +kernel
      have hl : raw35800step0Labels = raw35800Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35800 raw35800Labels permutation216 permutation5
    mixedMoment B raw35800step0 raw35800step0Labels = mixedMoment B raw35800step1 raw35800step1Labels := by
      have ha : raw35800step1 = -raw35800step0 := by apply Matrix.ext; change ∀ i j, raw35800step1 i j = -(raw35800step0 i j); unfold raw35800step1 raw35800step0; decide +kernel
      have hl : raw35800step1Labels = raw35800step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35800step1 raw35800step1Labels = mixedMoment B raw35800step2 raw35800step2Labels := by
      have ha : raw35800step2 = raw35800step1 := by apply Matrix.ext; unfold raw35800step2 raw35800step1; decide +kernel
      have hl : raw35800step1Labels = labelEmbedding1 ∘ raw35800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35800step1 raw35800step1Labels raw35800step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

theorem canonical35801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35801 raw35801Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw35801 raw35801Labels = mixedMoment B raw35801step0 raw35801step0Labels := by
      have ha : raw35801step0 = (fun i j => raw35801 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35801step0 raw35801; decide +kernel
      have hl : raw35801step0Labels = raw35801Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35801 raw35801Labels permutation161 permutation5
    mixedMoment B raw35801step0 raw35801step0Labels = mixedMoment B raw35801step1 raw35801step1Labels := by
      have ha : raw35801step1 = -raw35801step0 := by apply Matrix.ext; change ∀ i j, raw35801step1 i j = -(raw35801step0 i j); unfold raw35801step1 raw35801step0; decide +kernel
      have hl : raw35801step1Labels = raw35801step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35801step1 raw35801step1Labels = mixedMoment B raw35801step2 raw35801step2Labels := by
      have ha : raw35801step2 = raw35801step1 := by apply Matrix.ext; unfold raw35801step2 raw35801step1; decide +kernel
      have hl : raw35801step1Labels = labelEmbedding1 ∘ raw35801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35801step1 raw35801step1Labels raw35801step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

theorem canonical35802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35802 raw35802Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw35802 raw35802Labels = mixedMoment B raw35802step0 raw35802step0Labels := by
      have ha : raw35802step0 = (fun i j => raw35802 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35802step0 raw35802; decide +kernel
      have hl : raw35802step0Labels = raw35802Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35802 raw35802Labels permutation289 permutation7
    mixedMoment B raw35802step0 raw35802step0Labels = mixedMoment B raw35802step1 raw35802step1Labels := by
      have ha : raw35802step1 = -raw35802step0 := by apply Matrix.ext; change ∀ i j, raw35802step1 i j = -(raw35802step0 i j); unfold raw35802step1 raw35802step0; decide +kernel
      have hl : raw35802step1Labels = raw35802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35802step1 raw35802step1Labels = mixedMoment B raw35802step2 raw35802step2Labels := by
      have ha : raw35802step2 = raw35802step1 := by apply Matrix.ext; unfold raw35802step2 raw35802step1; decide +kernel
      have hl : raw35802step1Labels = labelEmbedding1 ∘ raw35802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35802step1 raw35802step1Labels raw35802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

theorem canonical35803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35803 raw35803Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw35803 raw35803Labels = mixedMoment B raw35803step0 raw35803step0Labels := by
      have ha : raw35803step0 = (fun i j => raw35803 (permutation203 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35803step0 raw35803; decide +kernel
      have hl : raw35803step0Labels = raw35803Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35803 raw35803Labels permutation203 permutation5
    mixedMoment B raw35803step0 raw35803step0Labels = mixedMoment B raw35803step1 raw35803step1Labels := by
      have ha : raw35803step1 = -raw35803step0 := by apply Matrix.ext; change ∀ i j, raw35803step1 i j = -(raw35803step0 i j); unfold raw35803step1 raw35803step0; decide +kernel
      have hl : raw35803step1Labels = raw35803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35803step1 raw35803step1Labels = mixedMoment B raw35803step2 raw35803step2Labels := by
      have ha : raw35803step2 = raw35803step1 := by apply Matrix.ext; unfold raw35803step2 raw35803step1; decide +kernel
      have hl : raw35803step1Labels = labelEmbedding1 ∘ raw35803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35803step1 raw35803step1Labels raw35803step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical35804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35804 raw35804Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw35804 raw35804Labels = mixedMoment B raw35804step0 raw35804step0Labels := by
      have ha : raw35804step0 = (fun i j => raw35804 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35804step0 raw35804; decide +kernel
      have hl : raw35804step0Labels = raw35804Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35804 raw35804Labels permutation227 permutation5
    mixedMoment B raw35804step0 raw35804step0Labels = mixedMoment B raw35804step1 raw35804step1Labels := by
      have ha : raw35804step1 = -raw35804step0 := by apply Matrix.ext; change ∀ i j, raw35804step1 i j = -(raw35804step0 i j); unfold raw35804step1 raw35804step0; decide +kernel
      have hl : raw35804step1Labels = raw35804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35804step1 raw35804step1Labels = mixedMoment B raw35804step2 raw35804step2Labels := by
      have ha : raw35804step2 = raw35804step1 := by apply Matrix.ext; unfold raw35804step2 raw35804step1; decide +kernel
      have hl : raw35804step1Labels = labelEmbedding1 ∘ raw35804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35804step1 raw35804step1Labels raw35804step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical35805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35805 raw35805Labels = mixedMoment B node3867 node3867Labels := by
  calc
    mixedMoment B raw35805 raw35805Labels = mixedMoment B raw35805step0 raw35805step0Labels := by
      have ha : raw35805step0 = (fun i j => raw35805 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35805step0 raw35805; decide +kernel
      have hl : raw35805step0Labels = raw35805Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35805 raw35805Labels permutation289 permutation7
    mixedMoment B raw35805step0 raw35805step0Labels = mixedMoment B raw35805step1 raw35805step1Labels := by
      have ha : raw35805step1 = -raw35805step0 := by apply Matrix.ext; change ∀ i j, raw35805step1 i j = -(raw35805step0 i j); unfold raw35805step1 raw35805step0; decide +kernel
      have hl : raw35805step1Labels = raw35805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35805step1 raw35805step1Labels = mixedMoment B raw35805step2 raw35805step2Labels := by
      have ha : raw35805step2 = raw35805step1 := by apply Matrix.ext; unfold raw35805step2 raw35805step1; decide +kernel
      have hl : raw35805step1Labels = labelEmbedding1 ∘ raw35805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35805step1 raw35805step1Labels raw35805step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3867 node3867Labels := by rfl

theorem canonical35806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35806 raw35806Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw35806 raw35806Labels = mixedMoment B raw35806step0 raw35806step0Labels := by
      have ha : raw35806step0 = (fun i j => raw35806 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35806step0 raw35806; decide +kernel
      have hl : raw35806step0Labels = raw35806Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35806 raw35806Labels permutation164 permutation5
    mixedMoment B raw35806step0 raw35806step0Labels = mixedMoment B raw35806step1 raw35806step1Labels := by
      have ha : raw35806step1 = -raw35806step0 := by apply Matrix.ext; change ∀ i j, raw35806step1 i j = -(raw35806step0 i j); unfold raw35806step1 raw35806step0; decide +kernel
      have hl : raw35806step1Labels = raw35806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35806step1 raw35806step1Labels = mixedMoment B raw35806step2 raw35806step2Labels := by
      have ha : raw35806step2 = raw35806step1 := by apply Matrix.ext; unfold raw35806step2 raw35806step1; decide +kernel
      have hl : raw35806step1Labels = labelEmbedding1 ∘ raw35806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35806step1 raw35806step1Labels raw35806step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2148 node2148Labels := by rfl

theorem canonical35807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35807 raw35807Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw35807 raw35807Labels = mixedMoment B raw35807step0 raw35807step0Labels := by
      have ha : raw35807step0 = (fun i j => raw35807 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35807step0 raw35807; decide +kernel
      have hl : raw35807step0Labels = raw35807Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35807 raw35807Labels permutation291 permutation7
    mixedMoment B raw35807step0 raw35807step0Labels = mixedMoment B raw35807step1 raw35807step1Labels := by
      have ha : raw35807step1 = -raw35807step0 := by apply Matrix.ext; change ∀ i j, raw35807step1 i j = -(raw35807step0 i j); unfold raw35807step1 raw35807step0; decide +kernel
      have hl : raw35807step1Labels = raw35807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35807step1 raw35807step1Labels = mixedMoment B raw35807step2 raw35807step2Labels := by
      have ha : raw35807step2 = raw35807step1 := by apply Matrix.ext; unfold raw35807step2 raw35807step1; decide +kernel
      have hl : raw35807step1Labels = labelEmbedding1 ∘ raw35807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35807step1 raw35807step1Labels raw35807step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

theorem canonical35808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35808 raw35808Labels = mixedMoment B node3792 node3792Labels := by
  calc
    mixedMoment B raw35808 raw35808Labels = mixedMoment B raw35808step0 raw35808step0Labels := by
      have ha : raw35808step0 = (fun i j => raw35808 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35808step0 raw35808; decide +kernel
      have hl : raw35808step0Labels = raw35808Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35808 raw35808Labels permutation291 permutation7
    mixedMoment B raw35808step0 raw35808step0Labels = mixedMoment B raw35808step1 raw35808step1Labels := by
      have ha : raw35808step1 = -raw35808step0 := by apply Matrix.ext; change ∀ i j, raw35808step1 i j = -(raw35808step0 i j); unfold raw35808step1 raw35808step0; decide +kernel
      have hl : raw35808step1Labels = raw35808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35808step1 raw35808step1Labels = mixedMoment B raw35808step2 raw35808step2Labels := by
      have ha : raw35808step2 = raw35808step1 := by apply Matrix.ext; unfold raw35808step2 raw35808step1; decide +kernel
      have hl : raw35808step1Labels = labelEmbedding1 ∘ raw35808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35808step1 raw35808step1Labels raw35808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3792 node3792Labels := by rfl

theorem canonical35809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35809 raw35809Labels = mixedMoment B node3835 node3835Labels := by
  calc
    mixedMoment B raw35809 raw35809Labels = mixedMoment B raw35809step0 raw35809step0Labels := by
      have ha : raw35809step0 = (fun i j => raw35809 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35809step0 raw35809; decide +kernel
      have hl : raw35809step0Labels = raw35809Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35809 raw35809Labels permutation224 permutation5
    mixedMoment B raw35809step0 raw35809step0Labels = mixedMoment B raw35809step1 raw35809step1Labels := by
      have ha : raw35809step1 = -raw35809step0 := by apply Matrix.ext; change ∀ i j, raw35809step1 i j = -(raw35809step0 i j); unfold raw35809step1 raw35809step0; decide +kernel
      have hl : raw35809step1Labels = raw35809step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35809step1 raw35809step1Labels = mixedMoment B raw35809step2 raw35809step2Labels := by
      have ha : raw35809step2 = raw35809step1 := by apply Matrix.ext; unfold raw35809step2 raw35809step1; decide +kernel
      have hl : raw35809step1Labels = labelEmbedding1 ∘ raw35809step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35809step1 raw35809step1Labels raw35809step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3835 node3835Labels := by rfl

theorem canonical35810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35810 raw35810Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw35810 raw35810Labels = mixedMoment B raw35810step0 raw35810step0Labels := by
      have ha : raw35810step0 = (fun i j => raw35810 (permutation292 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35810step0 raw35810; decide +kernel
      have hl : raw35810step0Labels = raw35810Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35810 raw35810Labels permutation292 permutation7
    mixedMoment B raw35810step0 raw35810step0Labels = mixedMoment B raw35810step1 raw35810step1Labels := by
      have ha : raw35810step1 = -raw35810step0 := by apply Matrix.ext; change ∀ i j, raw35810step1 i j = -(raw35810step0 i j); unfold raw35810step1 raw35810step0; decide +kernel
      have hl : raw35810step1Labels = raw35810step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35810step1 raw35810step1Labels = mixedMoment B raw35810step2 raw35810step2Labels := by
      have ha : raw35810step2 = raw35810step1 := by apply Matrix.ext; unfold raw35810step2 raw35810step1; decide +kernel
      have hl : raw35810step1Labels = labelEmbedding1 ∘ raw35810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35810step1 raw35810step1Labels raw35810step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

theorem canonical35811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35811 raw35811Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw35811 raw35811Labels = mixedMoment B raw35811step0 raw35811step0Labels := by
      have ha : raw35811step0 = (fun i j => raw35811 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35811step0 raw35811; decide +kernel
      have hl : raw35811step0Labels = raw35811Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35811 raw35811Labels permutation158 permutation5
    mixedMoment B raw35811step0 raw35811step0Labels = mixedMoment B raw35811step1 raw35811step1Labels := by
      have ha : raw35811step1 = -raw35811step0 := by apply Matrix.ext; change ∀ i j, raw35811step1 i j = -(raw35811step0 i j); unfold raw35811step1 raw35811step0; decide +kernel
      have hl : raw35811step1Labels = raw35811step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35811step1 raw35811step1Labels = mixedMoment B raw35811step2 raw35811step2Labels := by
      have ha : raw35811step2 = raw35811step1 := by apply Matrix.ext; unfold raw35811step2 raw35811step1; decide +kernel
      have hl : raw35811step1Labels = labelEmbedding1 ∘ raw35811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35811step1 raw35811step1Labels raw35811step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2148 node2148Labels := by rfl

theorem canonical35812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35812 raw35812Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw35812 raw35812Labels = mixedMoment B raw35812step0 raw35812step0Labels := by
      have ha : raw35812step0 = (fun i j => raw35812 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35812step0 raw35812; decide +kernel
      have hl : raw35812step0Labels = raw35812Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35812 raw35812Labels permutation289 permutation7
    mixedMoment B raw35812step0 raw35812step0Labels = mixedMoment B raw35812step1 raw35812step1Labels := by
      have ha : raw35812step1 = -raw35812step0 := by apply Matrix.ext; change ∀ i j, raw35812step1 i j = -(raw35812step0 i j); unfold raw35812step1 raw35812step0; decide +kernel
      have hl : raw35812step1Labels = raw35812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35812step1 raw35812step1Labels = mixedMoment B raw35812step2 raw35812step2Labels := by
      have ha : raw35812step2 = raw35812step1 := by apply Matrix.ext; unfold raw35812step2 raw35812step1; decide +kernel
      have hl : raw35812step1Labels = labelEmbedding1 ∘ raw35812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35812step1 raw35812step1Labels raw35812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

theorem canonical35813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35813 raw35813Labels = mixedMoment B node3792 node3792Labels := by
  calc
    mixedMoment B raw35813 raw35813Labels = mixedMoment B raw35813step0 raw35813step0Labels := by
      have ha : raw35813step0 = (fun i j => raw35813 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35813step0 raw35813; decide +kernel
      have hl : raw35813step0Labels = raw35813Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35813 raw35813Labels permutation289 permutation7
    mixedMoment B raw35813step0 raw35813step0Labels = mixedMoment B raw35813step1 raw35813step1Labels := by
      have ha : raw35813step1 = -raw35813step0 := by apply Matrix.ext; change ∀ i j, raw35813step1 i j = -(raw35813step0 i j); unfold raw35813step1 raw35813step0; decide +kernel
      have hl : raw35813step1Labels = raw35813step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35813step1 raw35813step1Labels = mixedMoment B raw35813step2 raw35813step2Labels := by
      have ha : raw35813step2 = raw35813step1 := by apply Matrix.ext; unfold raw35813step2 raw35813step1; decide +kernel
      have hl : raw35813step1Labels = labelEmbedding1 ∘ raw35813step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35813step1 raw35813step1Labels raw35813step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3792 node3792Labels := by rfl

theorem canonical35814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35814 raw35814Labels = mixedMoment B node3835 node3835Labels := by
  calc
    mixedMoment B raw35814 raw35814Labels = mixedMoment B raw35814step0 raw35814step0Labels := by
      have ha : raw35814step0 = (fun i j => raw35814 (permutation200 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35814step0 raw35814; decide +kernel
      have hl : raw35814step0Labels = raw35814Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35814 raw35814Labels permutation200 permutation5
    mixedMoment B raw35814step0 raw35814step0Labels = mixedMoment B raw35814step1 raw35814step1Labels := by
      have ha : raw35814step1 = -raw35814step0 := by apply Matrix.ext; change ∀ i j, raw35814step1 i j = -(raw35814step0 i j); unfold raw35814step1 raw35814step0; decide +kernel
      have hl : raw35814step1Labels = raw35814step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35814step1 raw35814step1Labels = mixedMoment B raw35814step2 raw35814step2Labels := by
      have ha : raw35814step2 = raw35814step1 := by apply Matrix.ext; unfold raw35814step2 raw35814step1; decide +kernel
      have hl : raw35814step1Labels = labelEmbedding1 ∘ raw35814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35814step1 raw35814step1Labels raw35814step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3835 node3835Labels := by rfl

theorem canonical35815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35815 raw35815Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw35815 raw35815Labels = mixedMoment B raw35815step0 raw35815step0Labels := by
      have ha : raw35815step0 = (fun i j => raw35815 (permutation290 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35815step0 raw35815; decide +kernel
      have hl : raw35815step0Labels = raw35815Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35815 raw35815Labels permutation290 permutation7
    mixedMoment B raw35815step0 raw35815step0Labels = mixedMoment B raw35815step1 raw35815step1Labels := by
      have ha : raw35815step1 = -raw35815step0 := by apply Matrix.ext; change ∀ i j, raw35815step1 i j = -(raw35815step0 i j); unfold raw35815step1 raw35815step0; decide +kernel
      have hl : raw35815step1Labels = raw35815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35815step1 raw35815step1Labels = mixedMoment B raw35815step2 raw35815step2Labels := by
      have ha : raw35815step2 = raw35815step1 := by apply Matrix.ext; unfold raw35815step2 raw35815step1; decide +kernel
      have hl : raw35815step1Labels = labelEmbedding1 ∘ raw35815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35815step1 raw35815step1Labels raw35815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

theorem canonical35816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35816 raw35816Labels = mixedMoment B node2140 node2140Labels := by
  calc
    mixedMoment B raw35816 raw35816Labels = mixedMoment B raw35816step0 raw35816step0Labels := by
      have ha : raw35816step0 = (fun i j => raw35816 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35816step0 raw35816; decide +kernel
      have hl : raw35816step0Labels = raw35816Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35816 raw35816Labels permutation160 permutation5
    mixedMoment B raw35816step0 raw35816step0Labels = mixedMoment B raw35816step1 raw35816step1Labels := by
      have ha : raw35816step1 = -raw35816step0 := by apply Matrix.ext; change ∀ i j, raw35816step1 i j = -(raw35816step0 i j); unfold raw35816step1 raw35816step0; decide +kernel
      have hl : raw35816step1Labels = raw35816step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35816step1 raw35816step1Labels = mixedMoment B raw35816step2 raw35816step2Labels := by
      have ha : raw35816step2 = raw35816step1 := by apply Matrix.ext; unfold raw35816step2 raw35816step1; decide +kernel
      have hl : raw35816step1Labels = labelEmbedding1 ∘ raw35816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35816step1 raw35816step1Labels raw35816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2140 node2140Labels := by rfl

theorem canonical35817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35817 raw35817Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw35817 raw35817Labels = mixedMoment B raw35817step0 raw35817step0Labels := by
      have ha : raw35817step0 = (fun i j => raw35817 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35817step0 raw35817; decide +kernel
      have hl : raw35817step0Labels = raw35817Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35817 raw35817Labels permutation289 permutation7
    mixedMoment B raw35817step0 raw35817step0Labels = mixedMoment B raw35817step1 raw35817step1Labels := by
      have ha : raw35817step1 = -raw35817step0 := by apply Matrix.ext; change ∀ i j, raw35817step1 i j = -(raw35817step0 i j); unfold raw35817step1 raw35817step0; decide +kernel
      have hl : raw35817step1Labels = raw35817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35817step1 raw35817step1Labels = mixedMoment B raw35817step2 raw35817step2Labels := by
      have ha : raw35817step2 = raw35817step1 := by apply Matrix.ext; unfold raw35817step2 raw35817step1; decide +kernel
      have hl : raw35817step1Labels = labelEmbedding1 ∘ raw35817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35817step1 raw35817step1Labels raw35817step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3510 node3510Labels := by rfl

theorem canonical35818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35818 raw35818Labels = mixedMoment B node3597 node3597Labels := by
  calc
    mixedMoment B raw35818 raw35818Labels = mixedMoment B raw35818step0 raw35818step0Labels := by
      have ha : raw35818step0 = (fun i j => raw35818 (permutation664 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35818step0 raw35818; decide +kernel
      have hl : raw35818step0Labels = raw35818Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35818 raw35818Labels permutation664 permutation5
    mixedMoment B raw35818step0 raw35818step0Labels = mixedMoment B raw35818step1 raw35818step1Labels := by
      have ha : raw35818step1 = raw35818step0 := by apply Matrix.ext; unfold raw35818step1 raw35818step0; decide +kernel
      have hl : raw35818step0Labels = labelEmbedding1 ∘ raw35818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35818step0 raw35818step0Labels raw35818step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3597 node3597Labels := by rfl

theorem canonical35819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35819 raw35819Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw35819 raw35819Labels = mixedMoment B raw35819step0 raw35819step0Labels := by
      have ha : raw35819step0 = (fun i j => raw35819 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35819step0 raw35819; decide +kernel
      have hl : raw35819step0Labels = raw35819Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35819 raw35819Labels permutation644 permutation5
    mixedMoment B raw35819step0 raw35819step0Labels = mixedMoment B raw35819step1 raw35819step1Labels := by
      have ha : raw35819step1 = raw35819step0 := by apply Matrix.ext; unfold raw35819step1 raw35819step0; decide +kernel
      have hl : raw35819step0Labels = labelEmbedding1 ∘ raw35819step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35819step0 raw35819step0Labels raw35819step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical35820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35820 raw35820Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw35820 raw35820Labels = mixedMoment B raw35820step0 raw35820step0Labels := by
      have ha : raw35820step0 = (fun i j => raw35820 (permutation638 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35820step0 raw35820; decide +kernel
      have hl : raw35820step0Labels = raw35820Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35820 raw35820Labels permutation638 permutation5
    mixedMoment B raw35820step0 raw35820step0Labels = mixedMoment B raw35820step1 raw35820step1Labels := by
      have ha : raw35820step1 = raw35820step0 := by apply Matrix.ext; unfold raw35820step1 raw35820step0; decide +kernel
      have hl : raw35820step0Labels = labelEmbedding1 ∘ raw35820step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35820step0 raw35820step0Labels raw35820step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35889 raw35889Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw35889 raw35889Labels = mixedMoment B raw35889step0 raw35889step0Labels := by
      have ha : raw35889step0 = (fun i j => raw35889 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35889step0 raw35889; decide +kernel
      have hl : raw35889step0Labels = raw35889Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35889 raw35889Labels permutation291 permutation7
    mixedMoment B raw35889step0 raw35889step0Labels = mixedMoment B raw35889step1 raw35889step1Labels := by
      have ha : raw35889step1 = -raw35889step0 := by apply Matrix.ext; change ∀ i j, raw35889step1 i j = -(raw35889step0 i j); unfold raw35889step1 raw35889step0; decide +kernel
      have hl : raw35889step1Labels = raw35889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35889step1 raw35889step1Labels = mixedMoment B raw35889step2 raw35889step2Labels := by
      have ha : raw35889step2 = raw35889step1 := by apply Matrix.ext; unfold raw35889step2 raw35889step1; decide +kernel
      have hl : raw35889step1Labels = labelEmbedding1 ∘ raw35889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35889step1 raw35889step1Labels raw35889step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical35890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35890 raw35890Labels = mixedMoment B node3793 node3793Labels := by
  calc
    mixedMoment B raw35890 raw35890Labels = mixedMoment B raw35890step0 raw35890step0Labels := by
      have ha : raw35890step0 = (fun i j => raw35890 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35890step0 raw35890; decide +kernel
      have hl : raw35890step0Labels = raw35890Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35890 raw35890Labels permutation660 permutation7
    mixedMoment B raw35890step0 raw35890step0Labels = mixedMoment B raw35890step1 raw35890step1Labels := by
      have ha : raw35890step1 = raw35890step0 := by apply Matrix.ext; unfold raw35890step1 raw35890step0; decide +kernel
      have hl : raw35890step0Labels = labelEmbedding1 ∘ raw35890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35890step0 raw35890step0Labels raw35890step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3793 node3793Labels := by rfl

theorem canonical35891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35891 raw35891Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw35891 raw35891Labels = mixedMoment B raw35891step0 raw35891step0Labels := by
      have ha : raw35891step0 = (fun i j => raw35891 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35891step0 raw35891; decide +kernel
      have hl : raw35891step0Labels = raw35891Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35891 raw35891Labels permutation660 permutation7
    mixedMoment B raw35891step0 raw35891step0Labels = mixedMoment B raw35891step1 raw35891step1Labels := by
      have ha : raw35891step1 = raw35891step0 := by apply Matrix.ext; unfold raw35891step1 raw35891step0; decide +kernel
      have hl : raw35891step0Labels = labelEmbedding1 ∘ raw35891step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35891step0 raw35891step0Labels raw35891step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical35892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35892 raw35892Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw35892 raw35892Labels = mixedMoment B raw35892step0 raw35892step0Labels := by
      have hz : ∀ j, raw35892 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35892step0 = (fun i j => raw35892 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35892step0 raw35892; decide +kernel
      have hl : raw35892step0Labels = raw35892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35892 raw35892Labels permutation520 hz
    mixedMoment B raw35892step0 raw35892step0Labels = mixedMoment B raw35892step1 raw35892step1Labels := by
      have ha : raw35892step1 = (fun i j => raw35892step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35892step1 raw35892step0; decide +kernel
      have hl : raw35892step1Labels = raw35892step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35892step0 raw35892step0Labels permutation147 permutation7
    mixedMoment B raw35892step1 raw35892step1Labels = mixedMoment B raw35892step2 raw35892step2Labels := by
      have ha : raw35892step2 = raw35892step1 := by apply Matrix.ext; unfold raw35892step2 raw35892step1; decide +kernel
      have hl : raw35892step1Labels = labelEmbedding1 ∘ raw35892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35892step1 raw35892step1Labels raw35892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical35893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35893 raw35893Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw35893 raw35893Labels = mixedMoment B raw35893step0 raw35893step0Labels := by
      have ha : raw35893step0 = (fun i j => raw35893 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35893step0 raw35893; decide +kernel
      have hl : raw35893step0Labels = raw35893Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35893 raw35893Labels permutation291 permutation7
    mixedMoment B raw35893step0 raw35893step0Labels = mixedMoment B raw35893step1 raw35893step1Labels := by
      have ha : raw35893step1 = -raw35893step0 := by apply Matrix.ext; change ∀ i j, raw35893step1 i j = -(raw35893step0 i j); unfold raw35893step1 raw35893step0; decide +kernel
      have hl : raw35893step1Labels = raw35893step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35893step1 raw35893step1Labels = mixedMoment B raw35893step2 raw35893step2Labels := by
      have ha : raw35893step2 = raw35893step1 := by apply Matrix.ext; unfold raw35893step2 raw35893step1; decide +kernel
      have hl : raw35893step1Labels = labelEmbedding1 ∘ raw35893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35893step1 raw35893step1Labels raw35893step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical35894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35894 raw35894Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw35894 raw35894Labels = mixedMoment B raw35894step0 raw35894step0Labels := by
      have ha : raw35894step0 = (fun i j => raw35894 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35894step0 raw35894; decide +kernel
      have hl : raw35894step0Labels = raw35894Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35894 raw35894Labels permutation218 permutation5
    mixedMoment B raw35894step0 raw35894step0Labels = mixedMoment B raw35894step1 raw35894step1Labels := by
      have ha : raw35894step1 = -raw35894step0 := by apply Matrix.ext; change ∀ i j, raw35894step1 i j = -(raw35894step0 i j); unfold raw35894step1 raw35894step0; decide +kernel
      have hl : raw35894step1Labels = raw35894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35894step1 raw35894step1Labels = mixedMoment B raw35894step2 raw35894step2Labels := by
      have ha : raw35894step2 = raw35894step1 := by apply Matrix.ext; unfold raw35894step2 raw35894step1; decide +kernel
      have hl : raw35894step1Labels = labelEmbedding1 ∘ raw35894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35894step1 raw35894step1Labels raw35894step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical35895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35895 raw35895Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw35895 raw35895Labels = mixedMoment B raw35895step0 raw35895step0Labels := by
      have ha : raw35895step0 = (fun i j => raw35895 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35895step0 raw35895; decide +kernel
      have hl : raw35895step0Labels = raw35895Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35895 raw35895Labels permutation660 permutation7
    mixedMoment B raw35895step0 raw35895step0Labels = mixedMoment B raw35895step1 raw35895step1Labels := by
      have ha : raw35895step1 = raw35895step0 := by apply Matrix.ext; unfold raw35895step1 raw35895step0; decide +kernel
      have hl : raw35895step0Labels = labelEmbedding1 ∘ raw35895step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35895step0 raw35895step0Labels raw35895step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3796 node3796Labels := by rfl

theorem canonical35896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35896 raw35896Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw35896 raw35896Labels = mixedMoment B raw35896step0 raw35896step0Labels := by
      have ha : raw35896step0 = (fun i j => raw35896 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35896step0 raw35896; decide +kernel
      have hl : raw35896step0Labels = raw35896Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35896 raw35896Labels permutation660 permutation7
    mixedMoment B raw35896step0 raw35896step0Labels = mixedMoment B raw35896step1 raw35896step1Labels := by
      have ha : raw35896step1 = raw35896step0 := by apply Matrix.ext; unfold raw35896step1 raw35896step0; decide +kernel
      have hl : raw35896step0Labels = labelEmbedding1 ∘ raw35896step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35896step0 raw35896step0Labels raw35896step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical35897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35897 raw35897Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw35897 raw35897Labels = mixedMoment B raw35897step0 raw35897step0Labels := by
      have hz : ∀ j, raw35897 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35897step0 = (fun i j => raw35897 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35897step0 raw35897; decide +kernel
      have hl : raw35897step0Labels = raw35897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35897 raw35897Labels permutation520 hz
    mixedMoment B raw35897step0 raw35897step0Labels = mixedMoment B raw35897step1 raw35897step1Labels := by
      have ha : raw35897step1 = (fun i j => raw35897step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35897step1 raw35897step0; decide +kernel
      have hl : raw35897step1Labels = raw35897step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35897step0 raw35897step0Labels permutation147 permutation7
    mixedMoment B raw35897step1 raw35897step1Labels = mixedMoment B raw35897step2 raw35897step2Labels := by
      have ha : raw35897step2 = raw35897step1 := by apply Matrix.ext; unfold raw35897step2 raw35897step1; decide +kernel
      have hl : raw35897step1Labels = labelEmbedding1 ∘ raw35897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35897step1 raw35897step1Labels raw35897step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical35898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35898 raw35898Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw35898 raw35898Labels = mixedMoment B raw35898step0 raw35898step0Labels := by
      have ha : raw35898step0 = (fun i j => raw35898 (permutation257 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35898step0 raw35898; decide +kernel
      have hl : raw35898step0Labels = raw35898Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35898 raw35898Labels permutation257 permutation5
    mixedMoment B raw35898step0 raw35898step0Labels = mixedMoment B raw35898step1 raw35898step1Labels := by
      have ha : raw35898step1 = -raw35898step0 := by apply Matrix.ext; change ∀ i j, raw35898step1 i j = -(raw35898step0 i j); unfold raw35898step1 raw35898step0; decide +kernel
      have hl : raw35898step1Labels = raw35898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35898step1 raw35898step1Labels = mixedMoment B raw35898step2 raw35898step2Labels := by
      have ha : raw35898step2 = raw35898step1 := by apply Matrix.ext; unfold raw35898step2 raw35898step1; decide +kernel
      have hl : raw35898step1Labels = labelEmbedding1 ∘ raw35898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35898step1 raw35898step1Labels raw35898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical35899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35899 raw35899Labels = mixedMoment B node2145 node2145Labels := by
  calc
    mixedMoment B raw35899 raw35899Labels = mixedMoment B raw35899step0 raw35899step0Labels := by
      have ha : raw35899step0 = (fun i j => raw35899 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35899step0 raw35899; decide +kernel
      have hl : raw35899step0Labels = raw35899Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35899 raw35899Labels permutation163 permutation5
    mixedMoment B raw35899step0 raw35899step0Labels = mixedMoment B raw35899step1 raw35899step1Labels := by
      have ha : raw35899step1 = -raw35899step0 := by apply Matrix.ext; change ∀ i j, raw35899step1 i j = -(raw35899step0 i j); unfold raw35899step1 raw35899step0; decide +kernel
      have hl : raw35899step1Labels = raw35899step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35899step1 raw35899step1Labels = mixedMoment B raw35899step2 raw35899step2Labels := by
      have ha : raw35899step2 = raw35899step1 := by apply Matrix.ext; unfold raw35899step2 raw35899step1; decide +kernel
      have hl : raw35899step1Labels = labelEmbedding1 ∘ raw35899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35899step1 raw35899step1Labels raw35899step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2145 node2145Labels := by rfl

theorem canonical35900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35900 raw35900Labels = mixedMoment B node3553 node3553Labels := by
  calc
    mixedMoment B raw35900 raw35900Labels = mixedMoment B raw35900step0 raw35900step0Labels := by
      have ha : raw35900step0 = (fun i j => raw35900 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35900step0 raw35900; decide +kernel
      have hl : raw35900step0Labels = raw35900Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35900 raw35900Labels permutation291 permutation7
    mixedMoment B raw35900step0 raw35900step0Labels = mixedMoment B raw35900step1 raw35900step1Labels := by
      have ha : raw35900step1 = -raw35900step0 := by apply Matrix.ext; change ∀ i j, raw35900step1 i j = -(raw35900step0 i j); unfold raw35900step1 raw35900step0; decide +kernel
      have hl : raw35900step1Labels = raw35900step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35900step1 raw35900step1Labels = mixedMoment B raw35900step2 raw35900step2Labels := by
      have ha : raw35900step2 = raw35900step1 := by apply Matrix.ext; unfold raw35900step2 raw35900step1; decide +kernel
      have hl : raw35900step1Labels = labelEmbedding1 ∘ raw35900step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35900step1 raw35900step1Labels raw35900step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3553 node3553Labels := by rfl

theorem canonical35901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35901 raw35901Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw35901 raw35901Labels = mixedMoment B raw35901step0 raw35901step0Labels := by
      have ha : raw35901step0 = (fun i j => raw35901 (permutation205 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35901step0 raw35901; decide +kernel
      have hl : raw35901step0Labels = raw35901Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35901 raw35901Labels permutation205 permutation5
    mixedMoment B raw35901step0 raw35901step0Labels = mixedMoment B raw35901step1 raw35901step1Labels := by
      have ha : raw35901step1 = -raw35901step0 := by apply Matrix.ext; change ∀ i j, raw35901step1 i j = -(raw35901step0 i j); unfold raw35901step1 raw35901step0; decide +kernel
      have hl : raw35901step1Labels = raw35901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35901step1 raw35901step1Labels = mixedMoment B raw35901step2 raw35901step2Labels := by
      have ha : raw35901step2 = raw35901step1 := by apply Matrix.ext; unfold raw35901step2 raw35901step1; decide +kernel
      have hl : raw35901step1Labels = labelEmbedding1 ∘ raw35901step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35901step1 raw35901step1Labels raw35901step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

theorem canonical35902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35902 raw35902Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw35902 raw35902Labels = mixedMoment B raw35902step0 raw35902step0Labels := by
      have hz : ∀ j, raw35902 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35902step0 = (fun i j => raw35902 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35902step0 raw35902; decide +kernel
      have hl : raw35902step0Labels = raw35902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35902 raw35902Labels permutation520 hz
    mixedMoment B raw35902step0 raw35902step0Labels = mixedMoment B raw35902step1 raw35902step1Labels := by
      have ha : raw35902step1 = (fun i j => raw35902step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35902step1 raw35902step0; decide +kernel
      have hl : raw35902step1Labels = raw35902step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35902step0 raw35902step0Labels permutation147 permutation7
    mixedMoment B raw35902step1 raw35902step1Labels = mixedMoment B raw35902step2 raw35902step2Labels := by
      have ha : raw35902step2 = raw35902step1 := by apply Matrix.ext; unfold raw35902step2 raw35902step1; decide +kernel
      have hl : raw35902step1Labels = labelEmbedding1 ∘ raw35902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35902step1 raw35902step1Labels raw35902step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

theorem canonical35903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35903 raw35903Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw35903 raw35903Labels = mixedMoment B raw35903step0 raw35903step0Labels := by
      have ha : raw35903step0 = (fun i j => raw35903 (permutation249 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35903step0 raw35903; decide +kernel
      have hl : raw35903step0Labels = raw35903Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35903 raw35903Labels permutation249 permutation5
    mixedMoment B raw35903step0 raw35903step0Labels = mixedMoment B raw35903step1 raw35903step1Labels := by
      have ha : raw35903step1 = -raw35903step0 := by apply Matrix.ext; change ∀ i j, raw35903step1 i j = -(raw35903step0 i j); unfold raw35903step1 raw35903step0; decide +kernel
      have hl : raw35903step1Labels = raw35903step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35903step1 raw35903step1Labels = mixedMoment B raw35903step2 raw35903step2Labels := by
      have ha : raw35903step2 = raw35903step1 := by apply Matrix.ext; unfold raw35903step2 raw35903step1; decide +kernel
      have hl : raw35903step1Labels = labelEmbedding1 ∘ raw35903step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35903step1 raw35903step1Labels raw35903step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3866 node3866Labels := by rfl

theorem canonical35904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35904 raw35904Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw35904 raw35904Labels = mixedMoment B raw35904step0 raw35904step0Labels := by
      have ha : raw35904step0 = (fun i j => raw35904 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35904step0 raw35904; decide +kernel
      have hl : raw35904step0Labels = raw35904Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35904 raw35904Labels permutation171 permutation5
    mixedMoment B raw35904step0 raw35904step0Labels = mixedMoment B raw35904step1 raw35904step1Labels := by
      have ha : raw35904step1 = -raw35904step0 := by apply Matrix.ext; change ∀ i j, raw35904step1 i j = -(raw35904step0 i j); unfold raw35904step1 raw35904step0; decide +kernel
      have hl : raw35904step1Labels = raw35904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35904step1 raw35904step1Labels = mixedMoment B raw35904step2 raw35904step2Labels := by
      have ha : raw35904step2 = raw35904step1 := by apply Matrix.ext; unfold raw35904step2 raw35904step1; decide +kernel
      have hl : raw35904step1Labels = labelEmbedding1 ∘ raw35904step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35904step1 raw35904step1Labels raw35904step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

theorem canonical35905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35905 raw35905Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw35905 raw35905Labels = mixedMoment B raw35905step0 raw35905step0Labels := by
      have ha : raw35905step0 = (fun i j => raw35905 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35905step0 raw35905; decide +kernel
      have hl : raw35905step0Labels = raw35905Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35905 raw35905Labels permutation291 permutation7
    mixedMoment B raw35905step0 raw35905step0Labels = mixedMoment B raw35905step1 raw35905step1Labels := by
      have ha : raw35905step1 = -raw35905step0 := by apply Matrix.ext; change ∀ i j, raw35905step1 i j = -(raw35905step0 i j); unfold raw35905step1 raw35905step0; decide +kernel
      have hl : raw35905step1Labels = raw35905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35905step1 raw35905step1Labels = mixedMoment B raw35905step2 raw35905step2Labels := by
      have ha : raw35905step2 = raw35905step1 := by apply Matrix.ext; unfold raw35905step2 raw35905step1; decide +kernel
      have hl : raw35905step1Labels = labelEmbedding1 ∘ raw35905step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35905step1 raw35905step1Labels raw35905step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

theorem canonical35906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35906 raw35906Labels = mixedMoment B node3754 node3754Labels := by
  calc
    mixedMoment B raw35906 raw35906Labels = mixedMoment B raw35906step0 raw35906step0Labels := by
      have ha : raw35906step0 = (fun i j => raw35906 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35906step0 raw35906; decide +kernel
      have hl : raw35906step0Labels = raw35906Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35906 raw35906Labels permutation660 permutation7
    mixedMoment B raw35906step0 raw35906step0Labels = mixedMoment B raw35906step1 raw35906step1Labels := by
      have ha : raw35906step1 = raw35906step0 := by apply Matrix.ext; unfold raw35906step1 raw35906step0; decide +kernel
      have hl : raw35906step0Labels = labelEmbedding1 ∘ raw35906step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35906step0 raw35906step0Labels raw35906step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3754 node3754Labels := by rfl

theorem canonical35907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35907 raw35907Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw35907 raw35907Labels = mixedMoment B raw35907step0 raw35907step0Labels := by
      have hz : ∀ j, raw35907 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35907step0 = (fun i j => raw35907 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35907step0 raw35907; decide +kernel
      have hl : raw35907step0Labels = raw35907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35907 raw35907Labels permutation520 hz
    mixedMoment B raw35907step0 raw35907step0Labels = mixedMoment B raw35907step1 raw35907step1Labels := by
      have ha : raw35907step1 = (fun i j => raw35907step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35907step1 raw35907step0; decide +kernel
      have hl : raw35907step1Labels = raw35907step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35907step0 raw35907step0Labels permutation147 permutation7
    mixedMoment B raw35907step1 raw35907step1Labels = mixedMoment B raw35907step2 raw35907step2Labels := by
      have ha : raw35907step2 = raw35907step1 := by apply Matrix.ext; unfold raw35907step2 raw35907step1; decide +kernel
      have hl : raw35907step1Labels = labelEmbedding1 ∘ raw35907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35907step1 raw35907step1Labels raw35907step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

theorem canonical35908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35908 raw35908Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw35908 raw35908Labels = mixedMoment B raw35908step0 raw35908step0Labels := by
      have ha : raw35908step0 = (fun i j => raw35908 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35908step0 raw35908; decide +kernel
      have hl : raw35908step0Labels = raw35908Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35908 raw35908Labels permutation291 permutation7
    mixedMoment B raw35908step0 raw35908step0Labels = mixedMoment B raw35908step1 raw35908step1Labels := by
      have ha : raw35908step1 = -raw35908step0 := by apply Matrix.ext; change ∀ i j, raw35908step1 i j = -(raw35908step0 i j); unfold raw35908step1 raw35908step0; decide +kernel
      have hl : raw35908step1Labels = raw35908step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35908step1 raw35908step1Labels = mixedMoment B raw35908step2 raw35908step2Labels := by
      have ha : raw35908step2 = raw35908step1 := by apply Matrix.ext; unfold raw35908step2 raw35908step1; decide +kernel
      have hl : raw35908step1Labels = labelEmbedding1 ∘ raw35908step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35908step1 raw35908step1Labels raw35908step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical35909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35909 raw35909Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw35909 raw35909Labels = mixedMoment B raw35909step0 raw35909step0Labels := by
      have ha : raw35909step0 = (fun i j => raw35909 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35909step0 raw35909; decide +kernel
      have hl : raw35909step0Labels = raw35909Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35909 raw35909Labels permutation162 permutation5
    mixedMoment B raw35909step0 raw35909step0Labels = mixedMoment B raw35909step1 raw35909step1Labels := by
      have ha : raw35909step1 = -raw35909step0 := by apply Matrix.ext; change ∀ i j, raw35909step1 i j = -(raw35909step0 i j); unfold raw35909step1 raw35909step0; decide +kernel
      have hl : raw35909step1Labels = raw35909step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35909step1 raw35909step1Labels = mixedMoment B raw35909step2 raw35909step2Labels := by
      have ha : raw35909step2 = raw35909step1 := by apply Matrix.ext; unfold raw35909step2 raw35909step1; decide +kernel
      have hl : raw35909step1Labels = labelEmbedding1 ∘ raw35909step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35909step1 raw35909step1Labels raw35909step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2144 node2144Labels := by rfl

theorem canonical35910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35910 raw35910Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw35910 raw35910Labels = mixedMoment B raw35910step0 raw35910step0Labels := by
      have ha : raw35910step0 = (fun i j => raw35910 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35910step0 raw35910; decide +kernel
      have hl : raw35910step0Labels = raw35910Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35910 raw35910Labels permutation291 permutation7
    mixedMoment B raw35910step0 raw35910step0Labels = mixedMoment B raw35910step1 raw35910step1Labels := by
      have ha : raw35910step1 = -raw35910step0 := by apply Matrix.ext; change ∀ i j, raw35910step1 i j = -(raw35910step0 i j); unfold raw35910step1 raw35910step0; decide +kernel
      have hl : raw35910step1Labels = raw35910step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35910step1 raw35910step1Labels = mixedMoment B raw35910step2 raw35910step2Labels := by
      have ha : raw35910step2 = raw35910step1 := by apply Matrix.ext; unfold raw35910step2 raw35910step1; decide +kernel
      have hl : raw35910step1Labels = labelEmbedding1 ∘ raw35910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35910step1 raw35910step1Labels raw35910step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

theorem canonical35911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35911 raw35911Labels = mixedMoment B node3791 node3791Labels := by
  calc
    mixedMoment B raw35911 raw35911Labels = mixedMoment B raw35911step0 raw35911step0Labels := by
      have ha : raw35911step0 = (fun i j => raw35911 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35911step0 raw35911; decide +kernel
      have hl : raw35911step0Labels = raw35911Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35911 raw35911Labels permutation660 permutation7
    mixedMoment B raw35911step0 raw35911step0Labels = mixedMoment B raw35911step1 raw35911step1Labels := by
      have ha : raw35911step1 = raw35911step0 := by apply Matrix.ext; unfold raw35911step1 raw35911step0; decide +kernel
      have hl : raw35911step0Labels = labelEmbedding1 ∘ raw35911step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35911step0 raw35911step0Labels raw35911step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3791 node3791Labels := by rfl

theorem canonical35912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35912 raw35912Labels = mixedMoment B node3833 node3833Labels := by
  calc
    mixedMoment B raw35912 raw35912Labels = mixedMoment B raw35912step0 raw35912step0Labels := by
      have ha : raw35912step0 = (fun i j => raw35912 (permutation550 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35912step0 raw35912; decide +kernel
      have hl : raw35912step0Labels = raw35912Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35912 raw35912Labels permutation550 permutation5
    mixedMoment B raw35912step0 raw35912step0Labels = mixedMoment B raw35912step1 raw35912step1Labels := by
      have ha : raw35912step1 = raw35912step0 := by apply Matrix.ext; unfold raw35912step1 raw35912step0; decide +kernel
      have hl : raw35912step0Labels = labelEmbedding1 ∘ raw35912step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35912step0 raw35912step0Labels raw35912step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3833 node3833Labels := by rfl

theorem canonical35913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35913 raw35913Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw35913 raw35913Labels = mixedMoment B raw35913step0 raw35913step0Labels := by
      have ha : raw35913step0 = (fun i j => raw35913 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35913step0 raw35913; decide +kernel
      have hl : raw35913step0Labels = raw35913Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35913 raw35913Labels permutation291 permutation7
    mixedMoment B raw35913step0 raw35913step0Labels = mixedMoment B raw35913step1 raw35913step1Labels := by
      have ha : raw35913step1 = -raw35913step0 := by apply Matrix.ext; change ∀ i j, raw35913step1 i j = -(raw35913step0 i j); unfold raw35913step1 raw35913step0; decide +kernel
      have hl : raw35913step1Labels = raw35913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35913step1 raw35913step1Labels = mixedMoment B raw35913step2 raw35913step2Labels := by
      have ha : raw35913step2 = raw35913step1 := by apply Matrix.ext; unfold raw35913step2 raw35913step1; decide +kernel
      have hl : raw35913step1Labels = labelEmbedding1 ∘ raw35913step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35913step1 raw35913step1Labels raw35913step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

theorem canonical35914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35914 raw35914Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw35914 raw35914Labels = mixedMoment B raw35914step0 raw35914step0Labels := by
      have ha : raw35914step0 = (fun i j => raw35914 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35914step0 raw35914; decide +kernel
      have hl : raw35914step0Labels = raw35914Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35914 raw35914Labels permutation158 permutation5
    mixedMoment B raw35914step0 raw35914step0Labels = mixedMoment B raw35914step1 raw35914step1Labels := by
      have ha : raw35914step1 = -raw35914step0 := by apply Matrix.ext; change ∀ i j, raw35914step1 i j = -(raw35914step0 i j); unfold raw35914step1 raw35914step0; decide +kernel
      have hl : raw35914step1Labels = raw35914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35914step1 raw35914step1Labels = mixedMoment B raw35914step2 raw35914step2Labels := by
      have ha : raw35914step2 = raw35914step1 := by apply Matrix.ext; unfold raw35914step2 raw35914step1; decide +kernel
      have hl : raw35914step1Labels = labelEmbedding1 ∘ raw35914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35914step1 raw35914step1Labels raw35914step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2147 node2147Labels := by rfl

theorem canonical35915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35915 raw35915Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw35915 raw35915Labels = mixedMoment B raw35915step0 raw35915step0Labels := by
      have ha : raw35915step0 = (fun i j => raw35915 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35915step0 raw35915; decide +kernel
      have hl : raw35915step0Labels = raw35915Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35915 raw35915Labels permutation660 permutation7
    mixedMoment B raw35915step0 raw35915step0Labels = mixedMoment B raw35915step1 raw35915step1Labels := by
      have ha : raw35915step1 = raw35915step0 := by apply Matrix.ext; unfold raw35915step1 raw35915step0; decide +kernel
      have hl : raw35915step0Labels = labelEmbedding1 ∘ raw35915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35915step0 raw35915step0Labels raw35915step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

theorem canonical35916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35916 raw35916Labels = mixedMoment B node3453 node3453Labels := by
  calc
    mixedMoment B raw35916 raw35916Labels = mixedMoment B raw35916step0 raw35916step0Labels := by
      have ha : raw35916step0 = (fun i j => raw35916 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35916step0 raw35916; decide +kernel
      have hl : raw35916step0Labels = raw35916Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35916 raw35916Labels permutation660 permutation7
    mixedMoment B raw35916step0 raw35916step0Labels = mixedMoment B raw35916step1 raw35916step1Labels := by
      have ha : raw35916step1 = raw35916step0 := by apply Matrix.ext; unfold raw35916step1 raw35916step0; decide +kernel
      have hl : raw35916step0Labels = labelEmbedding1 ∘ raw35916step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35916step0 raw35916step0Labels raw35916step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3453 node3453Labels := by rfl

theorem canonical35917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35917 raw35917Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw35917 raw35917Labels = mixedMoment B raw35917step0 raw35917step0Labels := by
      have ha : raw35917step0 = (fun i j => raw35917 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35917step0 raw35917; decide +kernel
      have hl : raw35917step0Labels = raw35917Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35917 raw35917Labels permutation660 permutation7
    mixedMoment B raw35917step0 raw35917step0Labels = mixedMoment B raw35917step1 raw35917step1Labels := by
      have ha : raw35917step1 = raw35917step0 := by apply Matrix.ext; unfold raw35917step1 raw35917step0; decide +kernel
      have hl : raw35917step0Labels = labelEmbedding1 ∘ raw35917step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35917step0 raw35917step0Labels raw35917step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical35918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35918 raw35918Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw35918 raw35918Labels = mixedMoment B raw35918step0 raw35918step0Labels := by
      have hz : ∀ j, raw35918 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35918step0 = (fun i j => raw35918 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35918step0 raw35918; decide +kernel
      have hl : raw35918step0Labels = raw35918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35918 raw35918Labels permutation520 hz
    mixedMoment B raw35918step0 raw35918step0Labels = mixedMoment B raw35918step1 raw35918step1Labels := by
      have ha : raw35918step1 = (fun i j => raw35918step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35918step1 raw35918step0; decide +kernel
      have hl : raw35918step1Labels = raw35918step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35918step0 raw35918step0Labels permutation147 permutation7
    mixedMoment B raw35918step1 raw35918step1Labels = mixedMoment B raw35918step2 raw35918step2Labels := by
      have ha : raw35918step2 = raw35918step1 := by apply Matrix.ext; unfold raw35918step2 raw35918step1; decide +kernel
      have hl : raw35918step1Labels = labelEmbedding1 ∘ raw35918step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35918step1 raw35918step1Labels raw35918step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical281
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35975 raw35975Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw35975 raw35975Labels = mixedMoment B raw35975step0 raw35975step0Labels := by
      have hz : ∀ j, raw35975 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35975step0 = (fun i j => raw35975 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35975step0 raw35975; decide +kernel
      have hl : raw35975step0Labels = raw35975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35975 raw35975Labels permutation346 hz
    mixedMoment B raw35975step0 raw35975step0Labels = mixedMoment B raw35975step1 raw35975step1Labels := by
      have ha : raw35975step1 = (fun i j => raw35975step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35975step1 raw35975step0; decide +kernel
      have hl : raw35975step1Labels = raw35975step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35975step0 raw35975step0Labels permutation56 permutation7
    mixedMoment B raw35975step1 raw35975step1Labels = mixedMoment B raw35975step2 raw35975step2Labels := by
      have ha : raw35975step2 = -raw35975step1 := by apply Matrix.ext; change ∀ i j, raw35975step2 i j = -(raw35975step1 i j); unfold raw35975step2 raw35975step1; decide +kernel
      have hl : raw35975step2Labels = raw35975step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35975step2 raw35975step2Labels = mixedMoment B raw35975step3 raw35975step3Labels := by
      have ha : raw35975step3 = raw35975step2 := by apply Matrix.ext; unfold raw35975step3 raw35975step2; decide +kernel
      have hl : raw35975step2Labels = labelEmbedding1 ∘ raw35975step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35975step2 raw35975step2Labels raw35975step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2227 node2227Labels := by rfl

theorem canonical35976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35976 raw35976Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw35976 raw35976Labels = mixedMoment B raw35976step0 raw35976step0Labels := by
      have ha : raw35976step0 = (fun i j => raw35976 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35976step0 raw35976; decide +kernel
      have hl : raw35976step0Labels = raw35976Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35976 raw35976Labels permutation265 permutation7
    mixedMoment B raw35976step0 raw35976step0Labels = mixedMoment B raw35976step1 raw35976step1Labels := by
      have ha : raw35976step1 = -raw35976step0 := by apply Matrix.ext; change ∀ i j, raw35976step1 i j = -(raw35976step0 i j); unfold raw35976step1 raw35976step0; decide +kernel
      have hl : raw35976step1Labels = raw35976step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35976step1 raw35976step1Labels = mixedMoment B raw35976step2 raw35976step2Labels := by
      have ha : raw35976step2 = raw35976step1 := by apply Matrix.ext; unfold raw35976step2 raw35976step1; decide +kernel
      have hl : raw35976step1Labels = labelEmbedding1 ∘ raw35976step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35976step1 raw35976step1Labels raw35976step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2703 node2703Labels := by rfl

theorem canonical35977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35977 raw35977Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw35977 raw35977Labels = mixedMoment B raw35977step0 raw35977step0Labels := by
      have hz : ∀ j, raw35977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35977step0 = (fun i j => raw35977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35977step0 raw35977; decide +kernel
      have hl : raw35977step0Labels = raw35977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35977 raw35977Labels permutation346 hz
    mixedMoment B raw35977step0 raw35977step0Labels = mixedMoment B raw35977step1 raw35977step1Labels := by
      have ha : raw35977step1 = (fun i j => raw35977step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35977step1 raw35977step0; decide +kernel
      have hl : raw35977step1Labels = raw35977step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35977step0 raw35977step0Labels permutation56 permutation7
    mixedMoment B raw35977step1 raw35977step1Labels = mixedMoment B raw35977step2 raw35977step2Labels := by
      have ha : raw35977step2 = -raw35977step1 := by apply Matrix.ext; change ∀ i j, raw35977step2 i j = -(raw35977step1 i j); unfold raw35977step2 raw35977step1; decide +kernel
      have hl : raw35977step2Labels = raw35977step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35977step2 raw35977step2Labels = mixedMoment B raw35977step3 raw35977step3Labels := by
      have ha : raw35977step3 = raw35977step2 := by apply Matrix.ext; unfold raw35977step3 raw35977step2; decide +kernel
      have hl : raw35977step2Labels = labelEmbedding1 ∘ raw35977step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35977step2 raw35977step2Labels raw35977step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical35978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35978 raw35978Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw35978 raw35978Labels = mixedMoment B raw35978step0 raw35978step0Labels := by
      have hz : ∀ j, raw35978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35978step0 = (fun i j => raw35978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35978step0 raw35978; decide +kernel
      have hl : raw35978step0Labels = raw35978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35978 raw35978Labels permutation346 hz
    mixedMoment B raw35978step0 raw35978step0Labels = mixedMoment B raw35978step1 raw35978step1Labels := by
      have ha : raw35978step1 = (fun i j => raw35978step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35978step1 raw35978step0; decide +kernel
      have hl : raw35978step1Labels = raw35978step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35978step0 raw35978step0Labels permutation58 permutation7
    mixedMoment B raw35978step1 raw35978step1Labels = mixedMoment B raw35978step2 raw35978step2Labels := by
      have ha : raw35978step2 = -raw35978step1 := by apply Matrix.ext; change ∀ i j, raw35978step2 i j = -(raw35978step1 i j); unfold raw35978step2 raw35978step1; decide +kernel
      have hl : raw35978step2Labels = raw35978step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35978step2 raw35978step2Labels = mixedMoment B raw35978step3 raw35978step3Labels := by
      have ha : raw35978step3 = raw35978step2 := by apply Matrix.ext; unfold raw35978step3 raw35978step2; decide +kernel
      have hl : raw35978step2Labels = labelEmbedding1 ∘ raw35978step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35978step2 raw35978step2Labels raw35978step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical35979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35979 raw35979Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw35979 raw35979Labels = mixedMoment B raw35979step0 raw35979step0Labels := by
      have hz : ∀ j, raw35979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35979step0 = (fun i j => raw35979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35979step0 raw35979; decide +kernel
      have hl : raw35979step0Labels = raw35979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35979 raw35979Labels permutation346 hz
    mixedMoment B raw35979step0 raw35979step0Labels = mixedMoment B raw35979step1 raw35979step1Labels := by
      have ha : raw35979step1 = (fun i j => raw35979step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35979step1 raw35979step0; decide +kernel
      have hl : raw35979step1Labels = raw35979step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35979step0 raw35979step0Labels permutation56 permutation7
    mixedMoment B raw35979step1 raw35979step1Labels = mixedMoment B raw35979step2 raw35979step2Labels := by
      have ha : raw35979step2 = -raw35979step1 := by apply Matrix.ext; change ∀ i j, raw35979step2 i j = -(raw35979step1 i j); unfold raw35979step2 raw35979step1; decide +kernel
      have hl : raw35979step2Labels = raw35979step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35979step2 raw35979step2Labels = mixedMoment B raw35979step3 raw35979step3Labels := by
      have ha : raw35979step3 = raw35979step2 := by apply Matrix.ext; unfold raw35979step3 raw35979step2; decide +kernel
      have hl : raw35979step2Labels = labelEmbedding1 ∘ raw35979step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35979step2 raw35979step2Labels raw35979step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2741 node2741Labels := by rfl

theorem canonical35980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35980 raw35980Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw35980 raw35980Labels = mixedMoment B raw35980step0 raw35980step0Labels := by
      have hz : ∀ j, raw35980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35980step0 = (fun i j => raw35980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35980step0 raw35980; decide +kernel
      have hl : raw35980step0Labels = raw35980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35980 raw35980Labels permutation346 hz
    mixedMoment B raw35980step0 raw35980step0Labels = mixedMoment B raw35980step1 raw35980step1Labels := by
      have ha : raw35980step1 = (fun i j => raw35980step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35980step1 raw35980step0; decide +kernel
      have hl : raw35980step1Labels = raw35980step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35980step0 raw35980step0Labels permutation41 permutation5
    mixedMoment B raw35980step1 raw35980step1Labels = mixedMoment B raw35980step2 raw35980step2Labels := by
      have ha : raw35980step2 = -raw35980step1 := by apply Matrix.ext; change ∀ i j, raw35980step2 i j = -(raw35980step1 i j); unfold raw35980step2 raw35980step1; decide +kernel
      have hl : raw35980step2Labels = raw35980step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35980step2 raw35980step2Labels = mixedMoment B raw35980step3 raw35980step3Labels := by
      have ha : raw35980step3 = raw35980step2 := by apply Matrix.ext; unfold raw35980step3 raw35980step2; decide +kernel
      have hl : raw35980step2Labels = labelEmbedding1 ∘ raw35980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35980step2 raw35980step2Labels raw35980step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2246 node2246Labels := by rfl

theorem canonical35981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35981 raw35981Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw35981 raw35981Labels = mixedMoment B raw35981step0 raw35981step0Labels := by
      have ha : raw35981step0 = (fun i j => raw35981 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35981step0 raw35981; decide +kernel
      have hl : raw35981step0Labels = raw35981Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35981 raw35981Labels permutation265 permutation7
    mixedMoment B raw35981step0 raw35981step0Labels = mixedMoment B raw35981step1 raw35981step1Labels := by
      have ha : raw35981step1 = -raw35981step0 := by apply Matrix.ext; change ∀ i j, raw35981step1 i j = -(raw35981step0 i j); unfold raw35981step1 raw35981step0; decide +kernel
      have hl : raw35981step1Labels = raw35981step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35981step1 raw35981step1Labels = mixedMoment B raw35981step2 raw35981step2Labels := by
      have ha : raw35981step2 = raw35981step1 := by apply Matrix.ext; unfold raw35981step2 raw35981step1; decide +kernel
      have hl : raw35981step1Labels = labelEmbedding1 ∘ raw35981step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35981step1 raw35981step1Labels raw35981step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical35982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35982 raw35982Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw35982 raw35982Labels = mixedMoment B raw35982step0 raw35982step0Labels := by
      have hz : ∀ j, raw35982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35982step0 = (fun i j => raw35982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35982step0 raw35982; decide +kernel
      have hl : raw35982step0Labels = raw35982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35982 raw35982Labels permutation346 hz
    mixedMoment B raw35982step0 raw35982step0Labels = mixedMoment B raw35982step1 raw35982step1Labels := by
      have ha : raw35982step1 = (fun i j => raw35982step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35982step1 raw35982step0; decide +kernel
      have hl : raw35982step1Labels = raw35982step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35982step0 raw35982step0Labels permutation56 permutation7
    mixedMoment B raw35982step1 raw35982step1Labels = mixedMoment B raw35982step2 raw35982step2Labels := by
      have ha : raw35982step2 = -raw35982step1 := by apply Matrix.ext; change ∀ i j, raw35982step2 i j = -(raw35982step1 i j); unfold raw35982step2 raw35982step1; decide +kernel
      have hl : raw35982step2Labels = raw35982step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35982step2 raw35982step2Labels = mixedMoment B raw35982step3 raw35982step3Labels := by
      have ha : raw35982step3 = raw35982step2 := by apply Matrix.ext; unfold raw35982step3 raw35982step2; decide +kernel
      have hl : raw35982step2Labels = labelEmbedding1 ∘ raw35982step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35982step2 raw35982step2Labels raw35982step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical35983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35983 raw35983Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw35983 raw35983Labels = mixedMoment B raw35983step0 raw35983step0Labels := by
      have hz : ∀ j, raw35983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35983step0 = (fun i j => raw35983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35983step0 raw35983; decide +kernel
      have hl : raw35983step0Labels = raw35983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35983 raw35983Labels permutation346 hz
    mixedMoment B raw35983step0 raw35983step0Labels = mixedMoment B raw35983step1 raw35983step1Labels := by
      have ha : raw35983step1 = (fun i j => raw35983step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35983step1 raw35983step0; decide +kernel
      have hl : raw35983step1Labels = raw35983step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35983step0 raw35983step0Labels permutation58 permutation7
    mixedMoment B raw35983step1 raw35983step1Labels = mixedMoment B raw35983step2 raw35983step2Labels := by
      have ha : raw35983step2 = -raw35983step1 := by apply Matrix.ext; change ∀ i j, raw35983step2 i j = -(raw35983step1 i j); unfold raw35983step2 raw35983step1; decide +kernel
      have hl : raw35983step2Labels = raw35983step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35983step2 raw35983step2Labels = mixedMoment B raw35983step3 raw35983step3Labels := by
      have ha : raw35983step3 = raw35983step2 := by apply Matrix.ext; unfold raw35983step3 raw35983step2; decide +kernel
      have hl : raw35983step2Labels = labelEmbedding1 ∘ raw35983step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35983step2 raw35983step2Labels raw35983step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical35984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35984 raw35984Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw35984 raw35984Labels = mixedMoment B raw35984step0 raw35984step0Labels := by
      have hz : ∀ j, raw35984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35984step0 = (fun i j => raw35984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35984step0 raw35984; decide +kernel
      have hl : raw35984step0Labels = raw35984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35984 raw35984Labels permutation346 hz
    mixedMoment B raw35984step0 raw35984step0Labels = mixedMoment B raw35984step1 raw35984step1Labels := by
      have ha : raw35984step1 = (fun i j => raw35984step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35984step1 raw35984step0; decide +kernel
      have hl : raw35984step1Labels = raw35984step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35984step0 raw35984step0Labels permutation56 permutation7
    mixedMoment B raw35984step1 raw35984step1Labels = mixedMoment B raw35984step2 raw35984step2Labels := by
      have ha : raw35984step2 = -raw35984step1 := by apply Matrix.ext; change ∀ i j, raw35984step2 i j = -(raw35984step1 i j); unfold raw35984step2 raw35984step1; decide +kernel
      have hl : raw35984step2Labels = raw35984step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35984step2 raw35984step2Labels = mixedMoment B raw35984step3 raw35984step3Labels := by
      have ha : raw35984step3 = raw35984step2 := by apply Matrix.ext; unfold raw35984step3 raw35984step2; decide +kernel
      have hl : raw35984step2Labels = labelEmbedding1 ∘ raw35984step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35984step2 raw35984step2Labels raw35984step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical35985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35985 raw35985Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw35985 raw35985Labels = mixedMoment B raw35985step0 raw35985step0Labels := by
      have ha : raw35985step0 = (fun i j => raw35985 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35985step0 raw35985; decide +kernel
      have hl : raw35985step0Labels = raw35985Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35985 raw35985Labels permutation212 permutation5
    mixedMoment B raw35985step0 raw35985step0Labels = mixedMoment B raw35985step1 raw35985step1Labels := by
      have ha : raw35985step1 = -raw35985step0 := by apply Matrix.ext; change ∀ i j, raw35985step1 i j = -(raw35985step0 i j); unfold raw35985step1 raw35985step0; decide +kernel
      have hl : raw35985step1Labels = raw35985step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35985step1 raw35985step1Labels = mixedMoment B raw35985step2 raw35985step2Labels := by
      have ha : raw35985step2 = raw35985step1 := by apply Matrix.ext; unfold raw35985step2 raw35985step1; decide +kernel
      have hl : raw35985step1Labels = labelEmbedding1 ∘ raw35985step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35985step1 raw35985step1Labels raw35985step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

theorem canonical35986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35986 raw35986Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw35986 raw35986Labels = mixedMoment B raw35986step0 raw35986step0Labels := by
      have ha : raw35986step0 = (fun i j => raw35986 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35986step0 raw35986; decide +kernel
      have hl : raw35986step0Labels = raw35986Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35986 raw35986Labels permutation265 permutation7
    mixedMoment B raw35986step0 raw35986step0Labels = mixedMoment B raw35986step1 raw35986step1Labels := by
      have ha : raw35986step1 = -raw35986step0 := by apply Matrix.ext; change ∀ i j, raw35986step1 i j = -(raw35986step0 i j); unfold raw35986step1 raw35986step0; decide +kernel
      have hl : raw35986step1Labels = raw35986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35986step1 raw35986step1Labels = mixedMoment B raw35986step2 raw35986step2Labels := by
      have ha : raw35986step2 = raw35986step1 := by apply Matrix.ext; unfold raw35986step2 raw35986step1; decide +kernel
      have hl : raw35986step1Labels = labelEmbedding1 ∘ raw35986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35986step1 raw35986step1Labels raw35986step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

theorem canonical35987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35987 raw35987Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw35987 raw35987Labels = mixedMoment B raw35987step0 raw35987step0Labels := by
      have ha : raw35987step0 = (fun i j => raw35987 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35987step0 raw35987; decide +kernel
      have hl : raw35987step0Labels = raw35987Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35987 raw35987Labels permutation265 permutation7
    mixedMoment B raw35987step0 raw35987step0Labels = mixedMoment B raw35987step1 raw35987step1Labels := by
      have ha : raw35987step1 = -raw35987step0 := by apply Matrix.ext; change ∀ i j, raw35987step1 i j = -(raw35987step0 i j); unfold raw35987step1 raw35987step0; decide +kernel
      have hl : raw35987step1Labels = raw35987step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35987step1 raw35987step1Labels = mixedMoment B raw35987step2 raw35987step2Labels := by
      have ha : raw35987step2 = raw35987step1 := by apply Matrix.ext; unfold raw35987step2 raw35987step1; decide +kernel
      have hl : raw35987step1Labels = labelEmbedding1 ∘ raw35987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35987step1 raw35987step1Labels raw35987step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical35988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35988 raw35988Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw35988 raw35988Labels = mixedMoment B raw35988step0 raw35988step0Labels := by
      have ha : raw35988step0 = (fun i j => raw35988 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35988step0 raw35988; decide +kernel
      have hl : raw35988step0Labels = raw35988Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35988 raw35988Labels permutation267 permutation7
    mixedMoment B raw35988step0 raw35988step0Labels = mixedMoment B raw35988step1 raw35988step1Labels := by
      have ha : raw35988step1 = -raw35988step0 := by apply Matrix.ext; change ∀ i j, raw35988step1 i j = -(raw35988step0 i j); unfold raw35988step1 raw35988step0; decide +kernel
      have hl : raw35988step1Labels = raw35988step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35988step1 raw35988step1Labels = mixedMoment B raw35988step2 raw35988step2Labels := by
      have ha : raw35988step2 = raw35988step1 := by apply Matrix.ext; unfold raw35988step2 raw35988step1; decide +kernel
      have hl : raw35988step1Labels = labelEmbedding1 ∘ raw35988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35988step1 raw35988step1Labels raw35988step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical35989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35989 raw35989Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw35989 raw35989Labels = mixedMoment B raw35989step0 raw35989step0Labels := by
      have ha : raw35989step0 = (fun i j => raw35989 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35989step0 raw35989; decide +kernel
      have hl : raw35989step0Labels = raw35989Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35989 raw35989Labels permutation265 permutation7
    mixedMoment B raw35989step0 raw35989step0Labels = mixedMoment B raw35989step1 raw35989step1Labels := by
      have ha : raw35989step1 = -raw35989step0 := by apply Matrix.ext; change ∀ i j, raw35989step1 i j = -(raw35989step0 i j); unfold raw35989step1 raw35989step0; decide +kernel
      have hl : raw35989step1Labels = raw35989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35989step1 raw35989step1Labels = mixedMoment B raw35989step2 raw35989step2Labels := by
      have ha : raw35989step2 = raw35989step1 := by apply Matrix.ext; unfold raw35989step2 raw35989step1; decide +kernel
      have hl : raw35989step1Labels = labelEmbedding1 ∘ raw35989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35989step1 raw35989step1Labels raw35989step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical35990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35990 raw35990Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw35990 raw35990Labels = mixedMoment B raw35990step0 raw35990step0Labels := by
      have hz : ∀ j, raw35990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35990step0 = (fun i j => raw35990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35990step0 raw35990; decide +kernel
      have hl : raw35990step0Labels = raw35990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35990 raw35990Labels permutation346 hz
    mixedMoment B raw35990step0 raw35990step0Labels = mixedMoment B raw35990step1 raw35990step1Labels := by
      have ha : raw35990step1 = (fun i j => raw35990step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35990step1 raw35990step0; decide +kernel
      have hl : raw35990step1Labels = raw35990step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35990step0 raw35990step0Labels permutation44 permutation5
    mixedMoment B raw35990step1 raw35990step1Labels = mixedMoment B raw35990step2 raw35990step2Labels := by
      have ha : raw35990step2 = -raw35990step1 := by apply Matrix.ext; change ∀ i j, raw35990step2 i j = -(raw35990step1 i j); unfold raw35990step2 raw35990step1; decide +kernel
      have hl : raw35990step2Labels = raw35990step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35990step2 raw35990step2Labels = mixedMoment B raw35990step3 raw35990step3Labels := by
      have ha : raw35990step3 = raw35990step2 := by apply Matrix.ext; unfold raw35990step3 raw35990step2; decide +kernel
      have hl : raw35990step2Labels = labelEmbedding1 ∘ raw35990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35990step2 raw35990step2Labels raw35990step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2257 node2257Labels := by rfl

theorem canonical35991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35991 raw35991Labels = mixedMoment B node2166 node2166Labels := by
  calc
    mixedMoment B raw35991 raw35991Labels = mixedMoment B raw35991step0 raw35991step0Labels := by
      have hz : ∀ j, raw35991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35991step0 = (fun i j => raw35991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35991step0 raw35991; decide +kernel
      have hl : raw35991step0Labels = raw35991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35991 raw35991Labels permutation346 hz
    mixedMoment B raw35991step0 raw35991step0Labels = mixedMoment B raw35991step1 raw35991step1Labels := by
      have ha : raw35991step1 = (fun i j => raw35991step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35991step1 raw35991step0; decide +kernel
      have hl : raw35991step1Labels = raw35991step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35991step0 raw35991step0Labels permutation58 permutation7
    mixedMoment B raw35991step1 raw35991step1Labels = mixedMoment B raw35991step2 raw35991step2Labels := by
      have ha : raw35991step2 = -raw35991step1 := by apply Matrix.ext; change ∀ i j, raw35991step2 i j = -(raw35991step1 i j); unfold raw35991step2 raw35991step1; decide +kernel
      have hl : raw35991step2Labels = raw35991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35991step2 raw35991step2Labels = mixedMoment B raw35991step3 raw35991step3Labels := by
      have ha : raw35991step3 = raw35991step2 := by apply Matrix.ext; unfold raw35991step3 raw35991step2; decide +kernel
      have hl : raw35991step2Labels = labelEmbedding1 ∘ raw35991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35991step2 raw35991step2Labels raw35991step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2166 node2166Labels := by rfl

theorem canonical35992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35992 raw35992Labels = mixedMoment B node2656 node2656Labels := by
  calc
    mixedMoment B raw35992 raw35992Labels = mixedMoment B raw35992step0 raw35992step0Labels := by
      have ha : raw35992step0 = (fun i j => raw35992 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35992step0 raw35992; decide +kernel
      have hl : raw35992step0Labels = raw35992Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35992 raw35992Labels permutation267 permutation7
    mixedMoment B raw35992step0 raw35992step0Labels = mixedMoment B raw35992step1 raw35992step1Labels := by
      have ha : raw35992step1 = -raw35992step0 := by apply Matrix.ext; change ∀ i j, raw35992step1 i j = -(raw35992step0 i j); unfold raw35992step1 raw35992step0; decide +kernel
      have hl : raw35992step1Labels = raw35992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35992step1 raw35992step1Labels = mixedMoment B raw35992step2 raw35992step2Labels := by
      have ha : raw35992step2 = raw35992step1 := by apply Matrix.ext; unfold raw35992step2 raw35992step1; decide +kernel
      have hl : raw35992step1Labels = labelEmbedding1 ∘ raw35992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35992step1 raw35992step1Labels raw35992step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2656 node2656Labels := by rfl

theorem canonical35993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35993 raw35993Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw35993 raw35993Labels = mixedMoment B raw35993step0 raw35993step0Labels := by
      have hz : ∀ j, raw35993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35993step0 = (fun i j => raw35993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35993step0 raw35993; decide +kernel
      have hl : raw35993step0Labels = raw35993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35993 raw35993Labels permutation346 hz
    mixedMoment B raw35993step0 raw35993step0Labels = mixedMoment B raw35993step1 raw35993step1Labels := by
      have ha : raw35993step1 = (fun i j => raw35993step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35993step1 raw35993step0; decide +kernel
      have hl : raw35993step1Labels = raw35993step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35993step0 raw35993step0Labels permutation58 permutation7
    mixedMoment B raw35993step1 raw35993step1Labels = mixedMoment B raw35993step2 raw35993step2Labels := by
      have ha : raw35993step2 = -raw35993step1 := by apply Matrix.ext; change ∀ i j, raw35993step2 i j = -(raw35993step1 i j); unfold raw35993step2 raw35993step1; decide +kernel
      have hl : raw35993step2Labels = raw35993step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35993step2 raw35993step2Labels = mixedMoment B raw35993step3 raw35993step3Labels := by
      have ha : raw35993step3 = raw35993step2 := by apply Matrix.ext; unfold raw35993step3 raw35993step2; decide +kernel
      have hl : raw35993step2Labels = labelEmbedding1 ∘ raw35993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35993step2 raw35993step2Labels raw35993step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

theorem canonical35994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35994 raw35994Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw35994 raw35994Labels = mixedMoment B raw35994step0 raw35994step0Labels := by
      have hz : ∀ j, raw35994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35994step0 = (fun i j => raw35994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35994step0 raw35994; decide +kernel
      have hl : raw35994step0Labels = raw35994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35994 raw35994Labels permutation346 hz
    mixedMoment B raw35994step0 raw35994step0Labels = mixedMoment B raw35994step1 raw35994step1Labels := by
      have ha : raw35994step1 = (fun i j => raw35994step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35994step1 raw35994step0; decide +kernel
      have hl : raw35994step1Labels = raw35994step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35994step0 raw35994step0Labels permutation59 permutation7
    mixedMoment B raw35994step1 raw35994step1Labels = mixedMoment B raw35994step2 raw35994step2Labels := by
      have ha : raw35994step2 = -raw35994step1 := by apply Matrix.ext; change ∀ i j, raw35994step2 i j = -(raw35994step1 i j); unfold raw35994step2 raw35994step1; decide +kernel
      have hl : raw35994step2Labels = raw35994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35994step2 raw35994step2Labels = mixedMoment B raw35994step3 raw35994step3Labels := by
      have ha : raw35994step3 = raw35994step2 := by apply Matrix.ext; unfold raw35994step3 raw35994step2; decide +kernel
      have hl : raw35994step2Labels = labelEmbedding1 ∘ raw35994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35994step2 raw35994step2Labels raw35994step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical35995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35995 raw35995Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw35995 raw35995Labels = mixedMoment B raw35995step0 raw35995step0Labels := by
      have hz : ∀ j, raw35995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35995step0 = (fun i j => raw35995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35995step0 raw35995; decide +kernel
      have hl : raw35995step0Labels = raw35995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35995 raw35995Labels permutation346 hz
    mixedMoment B raw35995step0 raw35995step0Labels = mixedMoment B raw35995step1 raw35995step1Labels := by
      have ha : raw35995step1 = (fun i j => raw35995step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35995step1 raw35995step0; decide +kernel
      have hl : raw35995step1Labels = raw35995step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35995step0 raw35995step0Labels permutation38 permutation5
    mixedMoment B raw35995step1 raw35995step1Labels = mixedMoment B raw35995step2 raw35995step2Labels := by
      have ha : raw35995step2 = -raw35995step1 := by apply Matrix.ext; change ∀ i j, raw35995step2 i j = -(raw35995step1 i j); unfold raw35995step2 raw35995step1; decide +kernel
      have hl : raw35995step2Labels = raw35995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35995step2 raw35995step2Labels = mixedMoment B raw35995step3 raw35995step3Labels := by
      have ha : raw35995step3 = raw35995step2 := by apply Matrix.ext; unfold raw35995step3 raw35995step2; decide +kernel
      have hl : raw35995step2Labels = labelEmbedding1 ∘ raw35995step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35995step2 raw35995step2Labels raw35995step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2257 node2257Labels := by rfl

theorem canonical35996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35996 raw35996Labels = mixedMoment B node2166 node2166Labels := by
  calc
    mixedMoment B raw35996 raw35996Labels = mixedMoment B raw35996step0 raw35996step0Labels := by
      have hz : ∀ j, raw35996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35996step0 = (fun i j => raw35996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35996step0 raw35996; decide +kernel
      have hl : raw35996step0Labels = raw35996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35996 raw35996Labels permutation346 hz
    mixedMoment B raw35996step0 raw35996step0Labels = mixedMoment B raw35996step1 raw35996step1Labels := by
      have ha : raw35996step1 = (fun i j => raw35996step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35996step1 raw35996step0; decide +kernel
      have hl : raw35996step1Labels = raw35996step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35996step0 raw35996step0Labels permutation56 permutation7
    mixedMoment B raw35996step1 raw35996step1Labels = mixedMoment B raw35996step2 raw35996step2Labels := by
      have ha : raw35996step2 = -raw35996step1 := by apply Matrix.ext; change ∀ i j, raw35996step2 i j = -(raw35996step1 i j); unfold raw35996step2 raw35996step1; decide +kernel
      have hl : raw35996step2Labels = raw35996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35996step2 raw35996step2Labels = mixedMoment B raw35996step3 raw35996step3Labels := by
      have ha : raw35996step3 = raw35996step2 := by apply Matrix.ext; unfold raw35996step3 raw35996step2; decide +kernel
      have hl : raw35996step2Labels = labelEmbedding1 ∘ raw35996step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35996step2 raw35996step2Labels raw35996step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2166 node2166Labels := by rfl

theorem canonical35997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35997 raw35997Labels = mixedMoment B node2656 node2656Labels := by
  calc
    mixedMoment B raw35997 raw35997Labels = mixedMoment B raw35997step0 raw35997step0Labels := by
      have ha : raw35997step0 = (fun i j => raw35997 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35997step0 raw35997; decide +kernel
      have hl : raw35997step0Labels = raw35997Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35997 raw35997Labels permutation265 permutation7
    mixedMoment B raw35997step0 raw35997step0Labels = mixedMoment B raw35997step1 raw35997step1Labels := by
      have ha : raw35997step1 = -raw35997step0 := by apply Matrix.ext; change ∀ i j, raw35997step1 i j = -(raw35997step0 i j); unfold raw35997step1 raw35997step0; decide +kernel
      have hl : raw35997step1Labels = raw35997step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35997step1 raw35997step1Labels = mixedMoment B raw35997step2 raw35997step2Labels := by
      have ha : raw35997step2 = raw35997step1 := by apply Matrix.ext; unfold raw35997step2 raw35997step1; decide +kernel
      have hl : raw35997step1Labels = labelEmbedding1 ∘ raw35997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35997step1 raw35997step1Labels raw35997step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2656 node2656Labels := by rfl

theorem canonical35998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35998 raw35998Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw35998 raw35998Labels = mixedMoment B raw35998step0 raw35998step0Labels := by
      have hz : ∀ j, raw35998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35998step0 = (fun i j => raw35998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35998step0 raw35998; decide +kernel
      have hl : raw35998step0Labels = raw35998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35998 raw35998Labels permutation346 hz
    mixedMoment B raw35998step0 raw35998step0Labels = mixedMoment B raw35998step1 raw35998step1Labels := by
      have ha : raw35998step1 = (fun i j => raw35998step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35998step1 raw35998step0; decide +kernel
      have hl : raw35998step1Labels = raw35998step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35998step0 raw35998step0Labels permutation56 permutation7
    mixedMoment B raw35998step1 raw35998step1Labels = mixedMoment B raw35998step2 raw35998step2Labels := by
      have ha : raw35998step2 = -raw35998step1 := by apply Matrix.ext; change ∀ i j, raw35998step2 i j = -(raw35998step1 i j); unfold raw35998step2 raw35998step1; decide +kernel
      have hl : raw35998step2Labels = raw35998step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35998step2 raw35998step2Labels = mixedMoment B raw35998step3 raw35998step3Labels := by
      have ha : raw35998step3 = raw35998step2 := by apply Matrix.ext; unfold raw35998step3 raw35998step2; decide +kernel
      have hl : raw35998step2Labels = labelEmbedding1 ∘ raw35998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35998step2 raw35998step2Labels raw35998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

theorem canonical35999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35999 raw35999Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw35999 raw35999Labels = mixedMoment B raw35999step0 raw35999step0Labels := by
      have hz : ∀ j, raw35999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35999step0 = (fun i j => raw35999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35999step0 raw35999; decide +kernel
      have hl : raw35999step0Labels = raw35999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35999 raw35999Labels permutation346 hz
    mixedMoment B raw35999step0 raw35999step0Labels = mixedMoment B raw35999step1 raw35999step1Labels := by
      have ha : raw35999step1 = (fun i j => raw35999step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35999step1 raw35999step0; decide +kernel
      have hl : raw35999step1Labels = raw35999step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35999step0 raw35999step0Labels permutation57 permutation7
    mixedMoment B raw35999step1 raw35999step1Labels = mixedMoment B raw35999step2 raw35999step2Labels := by
      have ha : raw35999step2 = -raw35999step1 := by apply Matrix.ext; change ∀ i j, raw35999step2 i j = -(raw35999step1 i j); unfold raw35999step2 raw35999step1; decide +kernel
      have hl : raw35999step2Labels = raw35999step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35999step2 raw35999step2Labels = mixedMoment B raw35999step3 raw35999step3Labels := by
      have ha : raw35999step3 = raw35999step2 := by apply Matrix.ext; unfold raw35999step3 raw35999step2; decide +kernel
      have hl : raw35999step2Labels = labelEmbedding1 ∘ raw35999step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35999step2 raw35999step2Labels raw35999step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical36000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36000 raw36000Labels = mixedMoment B node2239 node2239Labels := by
  calc
    mixedMoment B raw36000 raw36000Labels = mixedMoment B raw36000step0 raw36000step0Labels := by
      have hz : ∀ j, raw36000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36000step0 = (fun i j => raw36000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36000step0 raw36000; decide +kernel
      have hl : raw36000step0Labels = raw36000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36000 raw36000Labels permutation346 hz
    mixedMoment B raw36000step0 raw36000step0Labels = mixedMoment B raw36000step1 raw36000step1Labels := by
      have ha : raw36000step1 = (fun i j => raw36000step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36000step1 raw36000step0; decide +kernel
      have hl : raw36000step1Labels = raw36000step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36000step0 raw36000step0Labels permutation40 permutation5
    mixedMoment B raw36000step1 raw36000step1Labels = mixedMoment B raw36000step2 raw36000step2Labels := by
      have ha : raw36000step2 = -raw36000step1 := by apply Matrix.ext; change ∀ i j, raw36000step2 i j = -(raw36000step1 i j); unfold raw36000step2 raw36000step1; decide +kernel
      have hl : raw36000step2Labels = raw36000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36000step2 raw36000step2Labels = mixedMoment B raw36000step3 raw36000step3Labels := by
      have ha : raw36000step3 = raw36000step2 := by apply Matrix.ext; unfold raw36000step3 raw36000step2; decide +kernel
      have hl : raw36000step2Labels = labelEmbedding1 ∘ raw36000step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36000step2 raw36000step2Labels raw36000step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2239 node2239Labels := by rfl

theorem canonical36001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36001 raw36001Labels = mixedMoment B node2165 node2165Labels := by
  calc
    mixedMoment B raw36001 raw36001Labels = mixedMoment B raw36001step0 raw36001step0Labels := by
      have hz : ∀ j, raw36001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36001step0 = (fun i j => raw36001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36001step0 raw36001; decide +kernel
      have hl : raw36001step0Labels = raw36001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36001 raw36001Labels permutation346 hz
    mixedMoment B raw36001step0 raw36001step0Labels = mixedMoment B raw36001step1 raw36001step1Labels := by
      have ha : raw36001step1 = (fun i j => raw36001step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36001step1 raw36001step0; decide +kernel
      have hl : raw36001step1Labels = raw36001step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36001step0 raw36001step0Labels permutation56 permutation7
    mixedMoment B raw36001step1 raw36001step1Labels = mixedMoment B raw36001step2 raw36001step2Labels := by
      have ha : raw36001step2 = -raw36001step1 := by apply Matrix.ext; change ∀ i j, raw36001step2 i j = -(raw36001step1 i j); unfold raw36001step2 raw36001step1; decide +kernel
      have hl : raw36001step2Labels = raw36001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36001step2 raw36001step2Labels = mixedMoment B raw36001step3 raw36001step3Labels := by
      have ha : raw36001step3 = raw36001step2 := by apply Matrix.ext; unfold raw36001step3 raw36001step2; decide +kernel
      have hl : raw36001step2Labels = labelEmbedding1 ∘ raw36001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36001step2 raw36001step2Labels raw36001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2165 node2165Labels := by rfl

theorem canonical36002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36002 raw36002Labels = mixedMoment B node2655 node2655Labels := by
  calc
    mixedMoment B raw36002 raw36002Labels = mixedMoment B raw36002step0 raw36002step0Labels := by
      have ha : raw36002step0 = (fun i j => raw36002 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36002step0 raw36002; decide +kernel
      have hl : raw36002step0Labels = raw36002Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36002 raw36002Labels permutation265 permutation7
    mixedMoment B raw36002step0 raw36002step0Labels = mixedMoment B raw36002step1 raw36002step1Labels := by
      have ha : raw36002step1 = -raw36002step0 := by apply Matrix.ext; change ∀ i j, raw36002step1 i j = -(raw36002step0 i j); unfold raw36002step1 raw36002step0; decide +kernel
      have hl : raw36002step1Labels = raw36002step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36002step1 raw36002step1Labels = mixedMoment B raw36002step2 raw36002step2Labels := by
      have ha : raw36002step2 = raw36002step1 := by apply Matrix.ext; unfold raw36002step2 raw36002step1; decide +kernel
      have hl : raw36002step1Labels = labelEmbedding1 ∘ raw36002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36002step1 raw36002step1Labels raw36002step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2655 node2655Labels := by rfl

theorem canonical36003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36003 raw36003Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw36003 raw36003Labels = mixedMoment B raw36003step0 raw36003step0Labels := by
      have hz : ∀ j, raw36003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36003step0 = (fun i j => raw36003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36003step0 raw36003; decide +kernel
      have hl : raw36003step0Labels = raw36003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36003 raw36003Labels permutation346 hz
    mixedMoment B raw36003step0 raw36003step0Labels = mixedMoment B raw36003step1 raw36003step1Labels := by
      have ha : raw36003step1 = (fun i j => raw36003step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36003step1 raw36003step0; decide +kernel
      have hl : raw36003step1Labels = raw36003step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36003step0 raw36003step0Labels permutation56 permutation7
    mixedMoment B raw36003step1 raw36003step1Labels = mixedMoment B raw36003step2 raw36003step2Labels := by
      have ha : raw36003step2 = -raw36003step1 := by apply Matrix.ext; change ∀ i j, raw36003step2 i j = -(raw36003step1 i j); unfold raw36003step2 raw36003step1; decide +kernel
      have hl : raw36003step2Labels = raw36003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36003step2 raw36003step2Labels = mixedMoment B raw36003step3 raw36003step3Labels := by
      have ha : raw36003step3 = raw36003step2 := by apply Matrix.ext; unfold raw36003step3 raw36003step2; decide +kernel
      have hl : raw36003step2Labels = labelEmbedding1 ∘ raw36003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36003step2 raw36003step2Labels raw36003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical36004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36004 raw36004Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw36004 raw36004Labels = mixedMoment B raw36004step0 raw36004step0Labels := by
      have hz : ∀ j, raw36004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36004step0 = (fun i j => raw36004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36004step0 raw36004; decide +kernel
      have hl : raw36004step0Labels = raw36004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36004 raw36004Labels permutation346 hz
    mixedMoment B raw36004step0 raw36004step0Labels = mixedMoment B raw36004step1 raw36004step1Labels := by
      have ha : raw36004step1 = (fun i j => raw36004step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36004step1 raw36004step0; decide +kernel
      have hl : raw36004step1Labels = raw36004step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36004step0 raw36004step0Labels permutation58 permutation7
    mixedMoment B raw36004step1 raw36004step1Labels = mixedMoment B raw36004step2 raw36004step2Labels := by
      have ha : raw36004step2 = -raw36004step1 := by apply Matrix.ext; change ∀ i j, raw36004step2 i j = -(raw36004step1 i j); unfold raw36004step2 raw36004step1; decide +kernel
      have hl : raw36004step2Labels = raw36004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36004step2 raw36004step2Labels = mixedMoment B raw36004step3 raw36004step3Labels := by
      have ha : raw36004step3 = raw36004step2 := by apply Matrix.ext; unfold raw36004step3 raw36004step2; decide +kernel
      have hl : raw36004step2Labels = labelEmbedding1 ∘ raw36004step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36004step2 raw36004step2Labels raw36004step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical282
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36203 raw36203Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw36203 raw36203Labels = mixedMoment B raw36203step0 raw36203step0Labels := by
      have hz : ∀ j, raw36203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36203step0 = (fun i j => raw36203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36203step0 raw36203; decide +kernel
      have hl : raw36203step0Labels = raw36203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36203 raw36203Labels permutation346 hz
    mixedMoment B raw36203step0 raw36203step0Labels = mixedMoment B raw36203step1 raw36203step1Labels := by
      have ha : raw36203step1 = (fun i j => raw36203step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36203step1 raw36203step0; decide +kernel
      have hl : raw36203step1Labels = raw36203step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36203step0 raw36203step0Labels permutation57 permutation5
    mixedMoment B raw36203step1 raw36203step1Labels = mixedMoment B raw36203step2 raw36203step2Labels := by
      have ha : raw36203step2 = -raw36203step1 := by apply Matrix.ext; change ∀ i j, raw36203step2 i j = -(raw36203step1 i j); unfold raw36203step2 raw36203step1; decide +kernel
      have hl : raw36203step2Labels = raw36203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36203step2 raw36203step2Labels = mixedMoment B raw36203step3 raw36203step3Labels := by
      have ha : raw36203step3 = raw36203step2 := by apply Matrix.ext; unfold raw36203step3 raw36203step2; decide +kernel
      have hl : raw36203step2Labels = labelEmbedding1 ∘ raw36203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36203step2 raw36203step2Labels raw36203step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

theorem canonical36204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36204 raw36204Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw36204 raw36204Labels = mixedMoment B raw36204step0 raw36204step0Labels := by
      have ha : raw36204step0 = (fun i j => raw36204 (permutation657 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36204step0 raw36204; decide +kernel
      have hl : raw36204step0Labels = raw36204Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36204 raw36204Labels permutation657 permutation7
    mixedMoment B raw36204step0 raw36204step0Labels = mixedMoment B raw36204step1 raw36204step1Labels := by
      have ha : raw36204step1 = raw36204step0 := by apply Matrix.ext; unfold raw36204step1 raw36204step0; decide +kernel
      have hl : raw36204step0Labels = labelEmbedding1 ∘ raw36204step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36204step0 raw36204step0Labels raw36204step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical36205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36205 raw36205Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw36205 raw36205Labels = mixedMoment B raw36205step0 raw36205step0Labels := by
      have hz : ∀ j, raw36205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36205step0 = (fun i j => raw36205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36205step0 raw36205; decide +kernel
      have hl : raw36205step0Labels = raw36205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36205 raw36205Labels permutation346 hz
    mixedMoment B raw36205step0 raw36205step0Labels = mixedMoment B raw36205step1 raw36205step1Labels := by
      have ha : raw36205step1 = (fun i j => raw36205step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36205step1 raw36205step0; decide +kernel
      have hl : raw36205step1Labels = raw36205step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36205step0 raw36205step0Labels permutation144 permutation7
    mixedMoment B raw36205step1 raw36205step1Labels = mixedMoment B raw36205step2 raw36205step2Labels := by
      have ha : raw36205step2 = raw36205step1 := by apply Matrix.ext; unfold raw36205step2 raw36205step1; decide +kernel
      have hl : raw36205step1Labels = labelEmbedding1 ∘ raw36205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36205step1 raw36205step1Labels raw36205step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical36206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36206 raw36206Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw36206 raw36206Labels = mixedMoment B raw36206step0 raw36206step0Labels := by
      have hz : ∀ j, raw36206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36206step0 = (fun i j => raw36206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36206step0 raw36206; decide +kernel
      have hl : raw36206step0Labels = raw36206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36206 raw36206Labels permutation346 hz
    mixedMoment B raw36206step0 raw36206step0Labels = mixedMoment B raw36206step1 raw36206step1Labels := by
      have ha : raw36206step1 = (fun i j => raw36206step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36206step1 raw36206step0; decide +kernel
      have hl : raw36206step1Labels = raw36206step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36206step0 raw36206step0Labels permutation144 permutation7
    mixedMoment B raw36206step1 raw36206step1Labels = mixedMoment B raw36206step2 raw36206step2Labels := by
      have ha : raw36206step2 = raw36206step1 := by apply Matrix.ext; unfold raw36206step2 raw36206step1; decide +kernel
      have hl : raw36206step1Labels = labelEmbedding1 ∘ raw36206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36206step1 raw36206step1Labels raw36206step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical36207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36207 raw36207Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw36207 raw36207Labels = mixedMoment B raw36207step0 raw36207step0Labels := by
      have hz : ∀ j, raw36207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36207step0 = (fun i j => raw36207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36207step0 raw36207; decide +kernel
      have hl : raw36207step0Labels = raw36207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36207 raw36207Labels permutation346 hz
    mixedMoment B raw36207step0 raw36207step0Labels = mixedMoment B raw36207step1 raw36207step1Labels := by
      have ha : raw36207step1 = (fun i j => raw36207step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36207step1 raw36207step0; decide +kernel
      have hl : raw36207step1Labels = raw36207step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36207step0 raw36207step0Labels permutation144 permutation7
    mixedMoment B raw36207step1 raw36207step1Labels = mixedMoment B raw36207step2 raw36207step2Labels := by
      have ha : raw36207step2 = raw36207step1 := by apply Matrix.ext; unfold raw36207step2 raw36207step1; decide +kernel
      have hl : raw36207step1Labels = labelEmbedding1 ∘ raw36207step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36207step1 raw36207step1Labels raw36207step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical36208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36208 raw36208Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw36208 raw36208Labels = mixedMoment B raw36208step0 raw36208step0Labels := by
      have hz : ∀ j, raw36208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36208step0 = (fun i j => raw36208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36208step0 raw36208; decide +kernel
      have hl : raw36208step0Labels = raw36208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36208 raw36208Labels permutation346 hz
    mixedMoment B raw36208step0 raw36208step0Labels = mixedMoment B raw36208step1 raw36208step1Labels := by
      have ha : raw36208step1 = (fun i j => raw36208step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36208step1 raw36208step0; decide +kernel
      have hl : raw36208step1Labels = raw36208step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36208step0 raw36208step0Labels permutation33 permutation5
    mixedMoment B raw36208step1 raw36208step1Labels = mixedMoment B raw36208step2 raw36208step2Labels := by
      have ha : raw36208step2 = -raw36208step1 := by apply Matrix.ext; change ∀ i j, raw36208step2 i j = -(raw36208step1 i j); unfold raw36208step2 raw36208step1; decide +kernel
      have hl : raw36208step2Labels = raw36208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36208step2 raw36208step2Labels = mixedMoment B raw36208step3 raw36208step3Labels := by
      have ha : raw36208step3 = raw36208step2 := by apply Matrix.ext; unfold raw36208step3 raw36208step2; decide +kernel
      have hl : raw36208step2Labels = labelEmbedding1 ∘ raw36208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36208step2 raw36208step2Labels raw36208step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

theorem canonical36209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36209 raw36209Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw36209 raw36209Labels = mixedMoment B raw36209step0 raw36209step0Labels := by
      have ha : raw36209step0 = (fun i j => raw36209 (permutation275 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36209step0 raw36209; decide +kernel
      have hl : raw36209step0Labels = raw36209Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36209 raw36209Labels permutation275 permutation5
    mixedMoment B raw36209step0 raw36209step0Labels = mixedMoment B raw36209step1 raw36209step1Labels := by
      have ha : raw36209step1 = -raw36209step0 := by apply Matrix.ext; change ∀ i j, raw36209step1 i j = -(raw36209step0 i j); unfold raw36209step1 raw36209step0; decide +kernel
      have hl : raw36209step1Labels = raw36209step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36209step1 raw36209step1Labels = mixedMoment B raw36209step2 raw36209step2Labels := by
      have ha : raw36209step2 = raw36209step1 := by apply Matrix.ext; unfold raw36209step2 raw36209step1; decide +kernel
      have hl : raw36209step1Labels = labelEmbedding1 ∘ raw36209step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36209step1 raw36209step1Labels raw36209step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

theorem canonical36210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36210 raw36210Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw36210 raw36210Labels = mixedMoment B raw36210step0 raw36210step0Labels := by
      have ha : raw36210step0 = (fun i j => raw36210 (permutation657 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36210step0 raw36210; decide +kernel
      have hl : raw36210step0Labels = raw36210Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36210 raw36210Labels permutation657 permutation7
    mixedMoment B raw36210step0 raw36210step0Labels = mixedMoment B raw36210step1 raw36210step1Labels := by
      have ha : raw36210step1 = raw36210step0 := by apply Matrix.ext; unfold raw36210step1 raw36210step0; decide +kernel
      have hl : raw36210step0Labels = labelEmbedding1 ∘ raw36210step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36210step0 raw36210step0Labels raw36210step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

theorem canonical36211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36211 raw36211Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw36211 raw36211Labels = mixedMoment B raw36211step0 raw36211step0Labels := by
      have ha : raw36211step0 = (fun i j => raw36211 (permutation657 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36211step0 raw36211; decide +kernel
      have hl : raw36211step0Labels = raw36211Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36211 raw36211Labels permutation657 permutation7
    mixedMoment B raw36211step0 raw36211step0Labels = mixedMoment B raw36211step1 raw36211step1Labels := by
      have ha : raw36211step1 = raw36211step0 := by apply Matrix.ext; unfold raw36211step1 raw36211step0; decide +kernel
      have hl : raw36211step0Labels = labelEmbedding1 ∘ raw36211step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36211step0 raw36211step0Labels raw36211step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

theorem canonical36212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36212 raw36212Labels = mixedMoment B node3973 node3973Labels := by
  calc
    mixedMoment B raw36212 raw36212Labels = mixedMoment B raw36212step0 raw36212step0Labels := by
      have ha : raw36212step0 = (fun i j => raw36212 (permutation545 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36212step0 raw36212; decide +kernel
      have hl : raw36212step0Labels = raw36212Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36212 raw36212Labels permutation545 permutation5
    mixedMoment B raw36212step0 raw36212step0Labels = mixedMoment B raw36212step1 raw36212step1Labels := by
      have ha : raw36212step1 = raw36212step0 := by apply Matrix.ext; unfold raw36212step1 raw36212step0; decide +kernel
      have hl : raw36212step0Labels = labelEmbedding1 ∘ raw36212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36212step0 raw36212step0Labels raw36212step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3973 node3973Labels := by rfl

theorem canonical36213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36213 raw36213Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw36213 raw36213Labels = mixedMoment B raw36213step0 raw36213step0Labels := by
      have hz : ∀ j, raw36213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36213step0 = (fun i j => raw36213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36213step0 raw36213; decide +kernel
      have hl : raw36213step0Labels = raw36213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36213 raw36213Labels permutation346 hz
    mixedMoment B raw36213step0 raw36213step0Labels = mixedMoment B raw36213step1 raw36213step1Labels := by
      have ha : raw36213step1 = (fun i j => raw36213step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36213step1 raw36213step0; decide +kernel
      have hl : raw36213step1Labels = raw36213step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36213step0 raw36213step0Labels permutation60 permutation5
    mixedMoment B raw36213step1 raw36213step1Labels = mixedMoment B raw36213step2 raw36213step2Labels := by
      have ha : raw36213step2 = -raw36213step1 := by apply Matrix.ext; change ∀ i j, raw36213step2 i j = -(raw36213step1 i j); unfold raw36213step2 raw36213step1; decide +kernel
      have hl : raw36213step2Labels = raw36213step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36213step2 raw36213step2Labels = mixedMoment B raw36213step3 raw36213step3Labels := by
      have ha : raw36213step3 = raw36213step2 := by apply Matrix.ext; unfold raw36213step3 raw36213step2; decide +kernel
      have hl : raw36213step2Labels = labelEmbedding1 ∘ raw36213step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36213step2 raw36213step2Labels raw36213step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

theorem canonical36214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36214 raw36214Labels = mixedMoment B node3763 node3763Labels := by
  calc
    mixedMoment B raw36214 raw36214Labels = mixedMoment B raw36214step0 raw36214step0Labels := by
      have ha : raw36214step0 = (fun i j => raw36214 (permutation657 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36214step0 raw36214; decide +kernel
      have hl : raw36214step0Labels = raw36214Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36214 raw36214Labels permutation657 permutation7
    mixedMoment B raw36214step0 raw36214step0Labels = mixedMoment B raw36214step1 raw36214step1Labels := by
      have ha : raw36214step1 = raw36214step0 := by apply Matrix.ext; unfold raw36214step1 raw36214step0; decide +kernel
      have hl : raw36214step0Labels = labelEmbedding1 ∘ raw36214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36214step0 raw36214step0Labels raw36214step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3763 node3763Labels := by rfl

theorem canonical36215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36215 raw36215Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw36215 raw36215Labels = mixedMoment B raw36215step0 raw36215step0Labels := by
      have hz : ∀ j, raw36215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36215step0 = (fun i j => raw36215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36215step0 raw36215; decide +kernel
      have hl : raw36215step0Labels = raw36215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36215 raw36215Labels permutation346 hz
    mixedMoment B raw36215step0 raw36215step0Labels = mixedMoment B raw36215step1 raw36215step1Labels := by
      have ha : raw36215step1 = (fun i j => raw36215step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36215step1 raw36215step0; decide +kernel
      have hl : raw36215step1Labels = raw36215step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36215step0 raw36215step0Labels permutation144 permutation7
    mixedMoment B raw36215step1 raw36215step1Labels = mixedMoment B raw36215step2 raw36215step2Labels := by
      have ha : raw36215step2 = raw36215step1 := by apply Matrix.ext; unfold raw36215step2 raw36215step1; decide +kernel
      have hl : raw36215step1Labels = labelEmbedding1 ∘ raw36215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36215step1 raw36215step1Labels raw36215step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

theorem canonical36216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36216 raw36216Labels = mixedMoment B node3960 node3960Labels := by
  calc
    mixedMoment B raw36216 raw36216Labels = mixedMoment B raw36216step0 raw36216step0Labels := by
      have hz : ∀ j, raw36216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36216step0 = (fun i j => raw36216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36216step0 raw36216; decide +kernel
      have hl : raw36216step0Labels = raw36216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36216 raw36216Labels permutation346 hz
    mixedMoment B raw36216step0 raw36216step0Labels = mixedMoment B raw36216step1 raw36216step1Labels := by
      have ha : raw36216step1 = (fun i j => raw36216step0 (permutation120 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36216step1 raw36216step0; decide +kernel
      have hl : raw36216step1Labels = raw36216step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36216step0 raw36216step0Labels permutation120 permutation5
    mixedMoment B raw36216step1 raw36216step1Labels = mixedMoment B raw36216step2 raw36216step2Labels := by
      have ha : raw36216step2 = raw36216step1 := by apply Matrix.ext; unfold raw36216step2 raw36216step1; decide +kernel
      have hl : raw36216step1Labels = labelEmbedding1 ∘ raw36216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36216step1 raw36216step1Labels raw36216step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3960 node3960Labels := by rfl

theorem canonical36217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36217 raw36217Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw36217 raw36217Labels = mixedMoment B raw36217step0 raw36217step0Labels := by
      have hz : ∀ j, raw36217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36217step0 = (fun i j => raw36217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36217step0 raw36217; decide +kernel
      have hl : raw36217step0Labels = raw36217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36217 raw36217Labels permutation346 hz
    mixedMoment B raw36217step0 raw36217step0Labels = mixedMoment B raw36217step1 raw36217step1Labels := by
      have ha : raw36217step1 = (fun i j => raw36217step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36217step1 raw36217step0; decide +kernel
      have hl : raw36217step1Labels = raw36217step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36217step0 raw36217step0Labels permutation126 permutation5
    mixedMoment B raw36217step1 raw36217step1Labels = mixedMoment B raw36217step2 raw36217step2Labels := by
      have ha : raw36217step2 = raw36217step1 := by apply Matrix.ext; unfold raw36217step2 raw36217step1; decide +kernel
      have hl : raw36217step1Labels = labelEmbedding1 ∘ raw36217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36217step1 raw36217step1Labels raw36217step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical36218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36218 raw36218Labels = mixedMoment B node2656 node2656Labels := by
  calc
    mixedMoment B raw36218 raw36218Labels = mixedMoment B raw36218step0 raw36218step0Labels := by
      have ha : raw36218step0 = (fun i j => raw36218 (permutation588 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36218step0 raw36218; decide +kernel
      have hl : raw36218step0Labels = raw36218Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36218 raw36218Labels permutation588 permutation5
    mixedMoment B raw36218step0 raw36218step0Labels = mixedMoment B raw36218step1 raw36218step1Labels := by
      have ha : raw36218step1 = raw36218step0 := by apply Matrix.ext; unfold raw36218step1 raw36218step0; decide +kernel
      have hl : raw36218step0Labels = labelEmbedding1 ∘ raw36218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36218step0 raw36218step0Labels raw36218step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2656 node2656Labels := by rfl

theorem canonical36219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36219 raw36219Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw36219 raw36219Labels = mixedMoment B raw36219step0 raw36219step0Labels := by
      have hz : ∀ j, raw36219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36219step0 = (fun i j => raw36219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36219step0 raw36219; decide +kernel
      have hl : raw36219step0Labels = raw36219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36219 raw36219Labels permutation346 hz
    mixedMoment B raw36219step0 raw36219step0Labels = mixedMoment B raw36219step1 raw36219step1Labels := by
      have ha : raw36219step1 = (fun i j => raw36219step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36219step1 raw36219step0; decide +kernel
      have hl : raw36219step1Labels = raw36219step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36219step0 raw36219step0Labels permutation126 permutation5
    mixedMoment B raw36219step1 raw36219step1Labels = mixedMoment B raw36219step2 raw36219step2Labels := by
      have ha : raw36219step2 = raw36219step1 := by apply Matrix.ext; unfold raw36219step2 raw36219step1; decide +kernel
      have hl : raw36219step1Labels = labelEmbedding1 ∘ raw36219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36219step1 raw36219step1Labels raw36219step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

theorem canonical36220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36220 raw36220Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw36220 raw36220Labels = mixedMoment B raw36220step0 raw36220step0Labels := by
      have hz : ∀ j, raw36220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36220step0 = (fun i j => raw36220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36220step0 raw36220; decide +kernel
      have hl : raw36220step0Labels = raw36220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36220 raw36220Labels permutation346 hz
    mixedMoment B raw36220step0 raw36220step0Labels = mixedMoment B raw36220step1 raw36220step1Labels := by
      have ha : raw36220step1 = (fun i j => raw36220step0 (permutation120 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36220step1 raw36220step0; decide +kernel
      have hl : raw36220step1Labels = raw36220step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36220step0 raw36220step0Labels permutation120 permutation5
    mixedMoment B raw36220step1 raw36220step1Labels = mixedMoment B raw36220step2 raw36220step2Labels := by
      have ha : raw36220step2 = raw36220step1 := by apply Matrix.ext; unfold raw36220step2 raw36220step1; decide +kernel
      have hl : raw36220step1Labels = labelEmbedding1 ∘ raw36220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36220step1 raw36220step1Labels raw36220step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

theorem canonical36221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36221 raw36221Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw36221 raw36221Labels = mixedMoment B raw36221step0 raw36221step0Labels := by
      have hz : ∀ j, raw36221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36221step0 = (fun i j => raw36221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36221step0 raw36221; decide +kernel
      have hl : raw36221step0Labels = raw36221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36221 raw36221Labels permutation346 hz
    mixedMoment B raw36221step0 raw36221step0Labels = mixedMoment B raw36221step1 raw36221step1Labels := by
      have ha : raw36221step1 = (fun i j => raw36221step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36221step1 raw36221step0; decide +kernel
      have hl : raw36221step1Labels = raw36221step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36221step0 raw36221step0Labels permutation57 permutation5
    mixedMoment B raw36221step1 raw36221step1Labels = mixedMoment B raw36221step2 raw36221step2Labels := by
      have ha : raw36221step2 = -raw36221step1 := by apply Matrix.ext; change ∀ i j, raw36221step2 i j = -(raw36221step1 i j); unfold raw36221step2 raw36221step1; decide +kernel
      have hl : raw36221step2Labels = raw36221step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36221step2 raw36221step2Labels = mixedMoment B raw36221step3 raw36221step3Labels := by
      have ha : raw36221step3 = raw36221step2 := by apply Matrix.ext; unfold raw36221step3 raw36221step2; decide +kernel
      have hl : raw36221step2Labels = labelEmbedding1 ∘ raw36221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36221step2 raw36221step2Labels raw36221step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

theorem canonical36222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36222 raw36222Labels = mixedMoment B node3465 node3465Labels := by
  calc
    mixedMoment B raw36222 raw36222Labels = mixedMoment B raw36222step0 raw36222step0Labels := by
      have ha : raw36222step0 = (fun i j => raw36222 (permutation657 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36222step0 raw36222; decide +kernel
      have hl : raw36222step0Labels = raw36222Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36222 raw36222Labels permutation657 permutation7
    mixedMoment B raw36222step0 raw36222step0Labels = mixedMoment B raw36222step1 raw36222step1Labels := by
      have ha : raw36222step1 = raw36222step0 := by apply Matrix.ext; unfold raw36222step1 raw36222step0; decide +kernel
      have hl : raw36222step0Labels = labelEmbedding1 ∘ raw36222step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36222step0 raw36222step0Labels raw36222step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3465 node3465Labels := by rfl

theorem canonical36223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36223 raw36223Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw36223 raw36223Labels = mixedMoment B raw36223step0 raw36223step0Labels := by
      have hz : ∀ j, raw36223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36223step0 = (fun i j => raw36223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36223step0 raw36223; decide +kernel
      have hl : raw36223step0Labels = raw36223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36223 raw36223Labels permutation346 hz
    mixedMoment B raw36223step0 raw36223step0Labels = mixedMoment B raw36223step1 raw36223step1Labels := by
      have ha : raw36223step1 = (fun i j => raw36223step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36223step1 raw36223step0; decide +kernel
      have hl : raw36223step1Labels = raw36223step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36223step0 raw36223step0Labels permutation144 permutation7
    mixedMoment B raw36223step1 raw36223step1Labels = mixedMoment B raw36223step2 raw36223step2Labels := by
      have ha : raw36223step2 = raw36223step1 := by apply Matrix.ext; unfold raw36223step2 raw36223step1; decide +kernel
      have hl : raw36223step1Labels = labelEmbedding1 ∘ raw36223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36223step1 raw36223step1Labels raw36223step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical283
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36224 raw36224Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw36224 raw36224Labels = mixedMoment B raw36224step0 raw36224step0Labels := by
      have hz : ∀ j, raw36224 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36224step0 = (fun i j => raw36224 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36224step0 raw36224; decide +kernel
      have hl : raw36224step0Labels = raw36224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36224 raw36224Labels permutation346 hz
    mixedMoment B raw36224step0 raw36224step0Labels = mixedMoment B raw36224step1 raw36224step1Labels := by
      have ha : raw36224step1 = (fun i j => raw36224step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36224step1 raw36224step0; decide +kernel
      have hl : raw36224step1Labels = raw36224step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36224step0 raw36224step0Labels permutation144 permutation7
    mixedMoment B raw36224step1 raw36224step1Labels = mixedMoment B raw36224step2 raw36224step2Labels := by
      have ha : raw36224step2 = raw36224step1 := by apply Matrix.ext; unfold raw36224step2 raw36224step1; decide +kernel
      have hl : raw36224step1Labels = labelEmbedding1 ∘ raw36224step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36224step1 raw36224step1Labels raw36224step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

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

theorem sound2142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2142 node2142Labels = Sparse.eval nodeValue2142 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2142) = mixedMoment B node2142 node2142Labels := rfl
  simpa [nodeValue2142, Sparse.eval] using hc.symm

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

theorem sound2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2165 node2165Labels = Sparse.eval nodeValue2165 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2165) = mixedMoment B node2165 node2165Labels := rfl
  simpa [nodeValue2165, Sparse.eval] using hc.symm

theorem sound2166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2166 node2166Labels = Sparse.eval nodeValue2166 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2166) = mixedMoment B node2166 node2166Labels := rfl
  simpa [nodeValue2166, Sparse.eval] using hc.symm

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

theorem sound2227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2227 node2227Labels = Sparse.eval nodeValue2227 (mixedVector B) := by
  simpa only [nodeValue2227, Sparse.eval_nil] using zero2227 B _hB _hF

theorem sound2238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2238 node2238Labels = Sparse.eval nodeValue2238 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2238) = mixedMoment B node2238 node2238Labels := rfl
  simpa [nodeValue2238, Sparse.eval] using hc.symm

theorem sound2239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2239 node2239Labels = Sparse.eval nodeValue2239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2239) = mixedMoment B node2239 node2239Labels := rfl
  simpa [nodeValue2239, Sparse.eval] using hc.symm

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

theorem sound2246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2246 node2246Labels = Sparse.eval nodeValue2246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2246) = mixedMoment B node2246 node2246Labels := rfl
  simpa [nodeValue2246, Sparse.eval] using hc.symm

theorem sound2250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2250 node2250Labels = Sparse.eval nodeValue2250 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2250) = mixedMoment B node2250 node2250Labels := rfl
  simpa [nodeValue2250, Sparse.eval] using hc.symm

theorem sound2257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2257 node2257Labels = Sparse.eval nodeValue2257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2257) = mixedMoment B node2257 node2257Labels := rfl
  simpa [nodeValue2257, Sparse.eval] using hc.symm

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

theorem sound2655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2655 node2655Labels = Sparse.eval nodeValue2655 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2655) = mixedMoment B node2655 node2655Labels := rfl
  simpa [nodeValue2655, Sparse.eval] using hc.symm

theorem sound2656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2656 node2656Labels = Sparse.eval nodeValue2656 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2656) = mixedMoment B node2656 node2656Labels := rfl
  simpa [nodeValue2656, Sparse.eval] using hc.symm

theorem sound2658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2658 node2658Labels = Sparse.eval nodeValue2658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2658) = mixedMoment B node2658 node2658Labels := rfl
  simpa [nodeValue2658, Sparse.eval] using hc.symm

theorem sound2669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2669 node2669Labels = Sparse.eval nodeValue2669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2669) = mixedMoment B node2669 node2669Labels := rfl
  simpa [nodeValue2669, Sparse.eval] using hc.symm

theorem sound2671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2671 node2671Labels = Sparse.eval nodeValue2671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2671) = mixedMoment B node2671 node2671Labels := rfl
  simpa [nodeValue2671, Sparse.eval] using hc.symm

theorem sound2681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2681 node2681Labels = Sparse.eval nodeValue2681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2681) = mixedMoment B node2681 node2681Labels := rfl
  simpa [nodeValue2681, Sparse.eval] using hc.symm

theorem sound2682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2682 node2682Labels = Sparse.eval nodeValue2682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2682) = mixedMoment B node2682 node2682Labels := rfl
  simpa [nodeValue2682, Sparse.eval] using hc.symm

theorem sound2684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2684 node2684Labels = Sparse.eval nodeValue2684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2684) = mixedMoment B node2684 node2684Labels := rfl
  simpa [nodeValue2684, Sparse.eval] using hc.symm

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

theorem zero2741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2741 node2741Labels = 0 := by
  exact mixedMoment_order_one B hB node2741 node2741Labels 1
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

theorem sound2703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2703 node2703Labels = Sparse.eval nodeValue2703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2703) = mixedMoment B node2703 node2703Labels := rfl
  simpa [nodeValue2703, Sparse.eval] using hc.symm

theorem sound2736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2736 node2736Labels = Sparse.eval nodeValue2736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2736) = mixedMoment B node2736 node2736Labels := rfl
  simpa [nodeValue2736, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

theorem sound2741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2741 node2741Labels = Sparse.eval nodeValue2741 (mixedVector B) := by
  simpa only [nodeValue2741, Sparse.eval_nil] using zero2741 B _hB _hF

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

theorem sound3023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3023 node3023Labels = Sparse.eval nodeValue3023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3023) = mixedMoment B node3023 node3023Labels := rfl
  simpa [nodeValue3023, Sparse.eval] using hc.symm

theorem sound3051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3051 node3051Labels = Sparse.eval nodeValue3051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3051) = mixedMoment B node3051 node3051Labels := rfl
  simpa [nodeValue3051, Sparse.eval] using hc.symm

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

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

theorem sound3407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3407 node3407Labels = Sparse.eval nodeValue3407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3407) = mixedMoment B node3407 node3407Labels := rfl
  simpa [nodeValue3407, Sparse.eval] using hc.symm

theorem sound3413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3413 node3413Labels = Sparse.eval nodeValue3413 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3413) = mixedMoment B node3413 node3413Labels := rfl
  simpa [nodeValue3413, Sparse.eval] using hc.symm

theorem sound3418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3418 node3418Labels = Sparse.eval nodeValue3418 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3418) = mixedMoment B node3418 node3418Labels := rfl
  simpa [nodeValue3418, Sparse.eval] using hc.symm

theorem sound3452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3452 node3452Labels = Sparse.eval nodeValue3452 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3452) = mixedMoment B node3452 node3452Labels := rfl
  simpa [nodeValue3452, Sparse.eval] using hc.symm

theorem sound3453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3453 node3453Labels = Sparse.eval nodeValue3453 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3453) = mixedMoment B node3453 node3453Labels := rfl
  simpa [nodeValue3453, Sparse.eval] using hc.symm

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

theorem sound3465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3465 node3465Labels = Sparse.eval nodeValue3465 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3465) = mixedMoment B node3465 node3465Labels := rfl
  simpa [nodeValue3465, Sparse.eval] using hc.symm

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

theorem sound3482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3482 node3482Labels = Sparse.eval nodeValue3482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3482) = mixedMoment B node3482 node3482Labels := rfl
  simpa [nodeValue3482, Sparse.eval] using hc.symm

theorem sound3508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3508 node3508Labels = Sparse.eval nodeValue3508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3508) = mixedMoment B node3508 node3508Labels := rfl
  simpa [nodeValue3508, Sparse.eval] using hc.symm

theorem sound3509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3509 node3509Labels = Sparse.eval nodeValue3509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3509) = mixedMoment B node3509 node3509Labels := rfl
  simpa [nodeValue3509, Sparse.eval] using hc.symm

theorem sound3510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3510 node3510Labels = Sparse.eval nodeValue3510 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3510) = mixedMoment B node3510 node3510Labels := rfl
  simpa [nodeValue3510, Sparse.eval] using hc.symm

theorem sound3511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3511 node3511Labels = Sparse.eval nodeValue3511 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3511) = mixedMoment B node3511 node3511Labels := rfl
  simpa [nodeValue3511, Sparse.eval] using hc.symm

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

theorem sound3516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3516 node3516Labels = Sparse.eval nodeValue3516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3516) = mixedMoment B node3516 node3516Labels := rfl
  simpa [nodeValue3516, Sparse.eval] using hc.symm

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

theorem sound3542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3542 node3542Labels = Sparse.eval nodeValue3542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3542) = mixedMoment B node3542 node3542Labels := rfl
  simpa [nodeValue3542, Sparse.eval] using hc.symm

theorem sound3553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3553 node3553Labels = Sparse.eval nodeValue3553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3553) = mixedMoment B node3553 node3553Labels := rfl
  simpa [nodeValue3553, Sparse.eval] using hc.symm

theorem sound3554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3554 node3554Labels = Sparse.eval nodeValue3554 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3554) = mixedMoment B node3554 node3554Labels := rfl
  simpa [nodeValue3554, Sparse.eval] using hc.symm

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

theorem sound3597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3597 node3597Labels = Sparse.eval nodeValue3597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3597) = mixedMoment B node3597 node3597Labels := rfl
  simpa [nodeValue3597, Sparse.eval] using hc.symm

theorem sound3606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3606 node3606Labels = Sparse.eval nodeValue3606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3606) = mixedMoment B node3606 node3606Labels := rfl
  simpa [nodeValue3606, Sparse.eval] using hc.symm

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

theorem sound3754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3754 node3754Labels = Sparse.eval nodeValue3754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3754) = mixedMoment B node3754 node3754Labels := rfl
  simpa [nodeValue3754, Sparse.eval] using hc.symm

theorem sound3763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3763 node3763Labels = Sparse.eval nodeValue3763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3763) = mixedMoment B node3763 node3763Labels := rfl
  simpa [nodeValue3763, Sparse.eval] using hc.symm

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

theorem sound3773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3773 node3773Labels = Sparse.eval nodeValue3773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3773) = mixedMoment B node3773 node3773Labels := rfl
  simpa [nodeValue3773, Sparse.eval] using hc.symm

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

theorem zero3798 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3798 node3798Labels = 0 := by
  exact mixedMoment_order_one B hB node3798 node3798Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = 0 := by
  exact mixedMoment_order_one B hB node3807 node3807Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = 0 := by
  exact mixedMoment_order_one B hB node3816 node3816Labels 1
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

theorem sound3791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3791 node3791Labels = Sparse.eval nodeValue3791 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3791) = mixedMoment B node3791 node3791Labels := rfl
  simpa [nodeValue3791, Sparse.eval] using hc.symm

theorem sound3792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3792 node3792Labels = Sparse.eval nodeValue3792 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3792) = mixedMoment B node3792 node3792Labels := rfl
  simpa [nodeValue3792, Sparse.eval] using hc.symm

theorem sound3793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3793 node3793Labels = Sparse.eval nodeValue3793 (mixedVector B) := by
  simpa only [nodeValue3793, Sparse.eval_nil] using zero3793 B _hB _hF

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

theorem sound3798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3798 node3798Labels = Sparse.eval nodeValue3798 (mixedVector B) := by
  simpa only [nodeValue3798, Sparse.eval_nil] using zero3798 B _hB _hF

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

theorem sound3811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3811 node3811Labels = Sparse.eval nodeValue3811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3811) = mixedMoment B node3811 node3811Labels := rfl
  simpa [nodeValue3811, Sparse.eval] using hc.symm

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

theorem sound3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = Sparse.eval nodeValue3816 (mixedVector B) := by
  simpa only [nodeValue3816, Sparse.eval_nil] using zero3816 B _hB _hF

theorem sound3832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3832 node3832Labels = Sparse.eval nodeValue3832 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3832) = mixedMoment B node3832 node3832Labels := rfl
  simpa [nodeValue3832, Sparse.eval] using hc.symm

theorem sound3833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3833 node3833Labels = Sparse.eval nodeValue3833 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3833) = mixedMoment B node3833 node3833Labels := rfl
  simpa [nodeValue3833, Sparse.eval] using hc.symm

theorem sound3834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3834 node3834Labels = Sparse.eval nodeValue3834 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3834) = mixedMoment B node3834 node3834Labels := rfl
  simpa [nodeValue3834, Sparse.eval] using hc.symm

theorem sound3835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3835 node3835Labels = Sparse.eval nodeValue3835 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3835) = mixedMoment B node3835 node3835Labels := rfl
  simpa [nodeValue3835, Sparse.eval] using hc.symm

theorem sound3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3836 node3836Labels = Sparse.eval nodeValue3836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3836) = mixedMoment B node3836 node3836Labels := rfl
  simpa [nodeValue3836, Sparse.eval] using hc.symm

theorem sound3837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3837 node3837Labels = Sparse.eval nodeValue3837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3837) = mixedMoment B node3837 node3837Labels := rfl
  simpa [nodeValue3837, Sparse.eval] using hc.symm

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

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

theorem sound3840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3840 node3840Labels = Sparse.eval nodeValue3840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3840) = mixedMoment B node3840 node3840Labels := rfl
  simpa [nodeValue3840, Sparse.eval] using hc.symm

theorem sound3842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3842 node3842Labels = Sparse.eval nodeValue3842 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3842) = mixedMoment B node3842 node3842Labels := rfl
  simpa [nodeValue3842, Sparse.eval] using hc.symm

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3844 node3844Labels = Sparse.eval nodeValue3844 (mixedVector B) := by
  simpa only [nodeValue3844, Sparse.eval_nil] using zero3844 B _hB _hF

theorem sound3848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3848 node3848Labels = Sparse.eval nodeValue3848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3848) = mixedMoment B node3848 node3848Labels := rfl
  simpa [nodeValue3848, Sparse.eval] using hc.symm

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3866 node3866Labels = Sparse.eval nodeValue3866 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3866) = mixedMoment B node3866 node3866Labels := rfl
  simpa [nodeValue3866, Sparse.eval] using hc.symm

theorem sound3867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3867 node3867Labels = Sparse.eval nodeValue3867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3867) = mixedMoment B node3867 node3867Labels := rfl
  simpa [nodeValue3867, Sparse.eval] using hc.symm

theorem sound3880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3880 node3880Labels = Sparse.eval nodeValue3880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3880) = mixedMoment B node3880 node3880Labels := rfl
  simpa [nodeValue3880, Sparse.eval] using hc.symm

theorem sound3900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3900 node3900Labels = Sparse.eval nodeValue3900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3900) = mixedMoment B node3900 node3900Labels := rfl
  simpa [nodeValue3900, Sparse.eval] using hc.symm

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

theorem sound3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3909 node3909Labels = Sparse.eval nodeValue3909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3909) = mixedMoment B node3909 node3909Labels := rfl
  simpa [nodeValue3909, Sparse.eval] using hc.symm

theorem sound3960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3960 node3960Labels = Sparse.eval nodeValue3960 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3960) = mixedMoment B node3960 node3960Labels := rfl
  simpa [nodeValue3960, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3973 node3973Labels = Sparse.eval nodeValue3973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3973) = mixedMoment B node3973 node3973Labels := rfl
  simpa [nodeValue3973, Sparse.eval] using hc.symm

theorem sound3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3983 node3983Labels = Sparse.eval nodeValue3983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3983) = mixedMoment B node3983 node3983Labels := rfl
  simpa [nodeValue3983, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources80
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2584 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2584 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2584 + difference 0 1) (sourceB2584 + difference 1 0) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA2584 + difference 0 1) (sourceB2584 + difference 1 0) sourceC2584) = raw35791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35791; decide +kernel
    rw [ha]
    exact (canonical35791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2584 + difference 0 2) (sourceB2584 + difference 2 0) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3798) := by
    have ha : (tripleCharges (sourceA2584 + difference 0 2) (sourceB2584 + difference 2 0) sourceC2584) = raw35792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35792; decide +kernel
    rw [ha]
    exact (canonical35792 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2584 + difference 0 3) (sourceB2584 + difference 3 0) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2584 + difference 0 3) (sourceB2584 + difference 3 0) sourceC2584) = raw35793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35793; decide +kernel
    rw [ha]
    exact (canonical35793 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2584 + difference 0 4) (sourceB2584 + difference 4 0) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2584 + difference 0 4) (sourceB2584 + difference 4 0) sourceC2584) = raw35794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35794; decide +kernel
    rw [ha]
    exact (canonical35794 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2584 + difference 0 5) (sourceB2584 + difference 5 0) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3844) := by
    have ha : (tripleCharges (sourceA2584 + difference 0 5) (sourceB2584 + difference 5 0) sourceC2584) = raw35795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35795; decide +kernel
    rw [ha]
    exact (canonical35795 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2584 + difference 1 0) (sourceB2584 + difference 0 1) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA2584 + difference 1 0) (sourceB2584 + difference 0 1) sourceC2584) = raw35796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35796; decide +kernel
    rw [ha]
    exact (canonical35796 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2584 + difference 1 2) (sourceB2584 + difference 2 1) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3900) := by
    have ha : (tripleCharges (sourceA2584 + difference 1 2) (sourceB2584 + difference 2 1) sourceC2584) = raw35797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35797; decide +kernel
    rw [ha]
    exact (canonical35797 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2584 + difference 1 3) (sourceB2584 + difference 3 1) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA2584 + difference 1 3) (sourceB2584 + difference 3 1) sourceC2584) = raw35798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35798; decide +kernel
    rw [ha]
    exact (canonical35798 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2584 + difference 1 4) (sourceB2584 + difference 4 1) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA2584 + difference 1 4) (sourceB2584 + difference 4 1) sourceC2584) = raw35799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35799; decide +kernel
    rw [ha]
    exact (canonical35799 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2584 + difference 1 5) (sourceB2584 + difference 5 1) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA2584 + difference 1 5) (sourceB2584 + difference 5 1) sourceC2584) = raw35800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35800; decide +kernel
    rw [ha]
    exact (canonical35800 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2584 + difference 2 0) (sourceB2584 + difference 0 2) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2142) := by
    have ha : (tripleCharges (sourceA2584 + difference 2 0) (sourceB2584 + difference 0 2) sourceC2584) = raw35801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35801; decide +kernel
    rw [ha]
    exact (canonical35801 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2584 + difference 2 1) (sourceB2584 + difference 1 2) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2584 + difference 2 1) (sourceB2584 + difference 1 2) sourceC2584) = raw35802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35802; decide +kernel
    rw [ha]
    exact (canonical35802 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2584 + difference 2 3) (sourceB2584 + difference 3 2) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2584 + difference 2 3) (sourceB2584 + difference 3 2) sourceC2584) = raw35803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35803; decide +kernel
    rw [ha]
    exact (canonical35803 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2584 + difference 2 4) (sourceB2584 + difference 4 2) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2584 + difference 2 4) (sourceB2584 + difference 4 2) sourceC2584) = raw35804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35804; decide +kernel
    rw [ha]
    exact (canonical35804 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2584 + difference 2 5) (sourceB2584 + difference 5 2) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3867) := by
    have ha : (tripleCharges (sourceA2584 + difference 2 5) (sourceB2584 + difference 5 2) sourceC2584) = raw35805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35805; decide +kernel
    rw [ha]
    exact (canonical35805 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2584 + difference 3 0) (sourceB2584 + difference 0 3) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2148) := by
    have ha : (tripleCharges (sourceA2584 + difference 3 0) (sourceB2584 + difference 0 3) sourceC2584) = raw35806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35806; decide +kernel
    rw [ha]
    exact (canonical35806 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2584 + difference 3 1) (sourceB2584 + difference 1 3) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3511) := by
    have ha : (tripleCharges (sourceA2584 + difference 3 1) (sourceB2584 + difference 1 3) sourceC2584) = raw35807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35807; decide +kernel
    rw [ha]
    exact (canonical35807 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2584 + difference 3 2) (sourceB2584 + difference 2 3) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3792) := by
    have ha : (tripleCharges (sourceA2584 + difference 3 2) (sourceB2584 + difference 2 3) sourceC2584) = raw35808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35808; decide +kernel
    rw [ha]
    exact (canonical35808 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2584 + difference 3 4) (sourceB2584 + difference 4 3) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3835) := by
    have ha : (tripleCharges (sourceA2584 + difference 3 4) (sourceB2584 + difference 4 3) sourceC2584) = raw35809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35809; decide +kernel
    rw [ha]
    exact (canonical35809 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2584 + difference 3 5) (sourceB2584 + difference 5 3) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA2584 + difference 3 5) (sourceB2584 + difference 5 3) sourceC2584) = raw35810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35810; decide +kernel
    rw [ha]
    exact (canonical35810 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2584 + difference 4 0) (sourceB2584 + difference 0 4) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2148) := by
    have ha : (tripleCharges (sourceA2584 + difference 4 0) (sourceB2584 + difference 0 4) sourceC2584) = raw35811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35811; decide +kernel
    rw [ha]
    exact (canonical35811 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2584 + difference 4 1) (sourceB2584 + difference 1 4) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3511) := by
    have ha : (tripleCharges (sourceA2584 + difference 4 1) (sourceB2584 + difference 1 4) sourceC2584) = raw35812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35812; decide +kernel
    rw [ha]
    exact (canonical35812 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2584 + difference 4 2) (sourceB2584 + difference 2 4) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3792) := by
    have ha : (tripleCharges (sourceA2584 + difference 4 2) (sourceB2584 + difference 2 4) sourceC2584) = raw35813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35813; decide +kernel
    rw [ha]
    exact (canonical35813 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2584 + difference 4 3) (sourceB2584 + difference 3 4) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3835) := by
    have ha : (tripleCharges (sourceA2584 + difference 4 3) (sourceB2584 + difference 3 4) sourceC2584) = raw35814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35814; decide +kernel
    rw [ha]
    exact (canonical35814 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2584 + difference 4 5) (sourceB2584 + difference 5 4) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA2584 + difference 4 5) (sourceB2584 + difference 5 4) sourceC2584) = raw35815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35815; decide +kernel
    rw [ha]
    exact (canonical35815 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2584 + difference 5 0) (sourceB2584 + difference 0 5) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2140) := by
    have ha : (tripleCharges (sourceA2584 + difference 5 0) (sourceB2584 + difference 0 5) sourceC2584) = raw35816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35816; decide +kernel
    rw [ha]
    exact (canonical35816 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2584 + difference 5 1) (sourceB2584 + difference 1 5) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3510) := by
    have ha : (tripleCharges (sourceA2584 + difference 5 1) (sourceB2584 + difference 1 5) sourceC2584) = raw35817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35817; decide +kernel
    rw [ha]
    exact (canonical35817 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2584 + difference 5 2) (sourceB2584 + difference 2 5) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3597) := by
    have ha : (tripleCharges (sourceA2584 + difference 5 2) (sourceB2584 + difference 2 5) sourceC2584) = raw35818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35818; decide +kernel
    rw [ha]
    exact (canonical35818 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2584 + difference 5 3) (sourceB2584 + difference 3 5) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2584 + difference 5 3) (sourceB2584 + difference 3 5) sourceC2584) = raw35819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35819; decide +kernel
    rw [ha]
    exact (canonical35819 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2584 + difference 5 4) (sourceB2584 + difference 4 5) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2584 + difference 5 4) (sourceB2584 + difference 4 5) sourceC2584) = raw35820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35820; decide +kernel
    rw [ha]
    exact (canonical35820 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2584 sourceB2584 sourceC2584
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2584, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2588 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2588 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2588 + difference 0 1) (sourceB2588 + difference 1 0) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA2588 + difference 0 1) (sourceB2588 + difference 1 0) sourceC2588) = raw35889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35889; decide +kernel
    rw [ha]
    exact (canonical35889 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2588 + difference 0 2) (sourceB2588 + difference 2 0) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3793) := by
    have ha : (tripleCharges (sourceA2588 + difference 0 2) (sourceB2588 + difference 2 0) sourceC2588) = raw35890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35890; decide +kernel
    rw [ha]
    exact (canonical35890 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2588 + difference 0 3) (sourceB2588 + difference 3 0) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA2588 + difference 0 3) (sourceB2588 + difference 3 0) sourceC2588) = raw35891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35891; decide +kernel
    rw [ha]
    exact (canonical35891 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2588 + difference 0 4) (sourceB2588 + difference 4 0) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2588 + difference 0 4) (sourceB2588 + difference 4 0) sourceC2588) = raw35892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35892; decide +kernel
    rw [ha]
    exact (canonical35892 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2588 + difference 0 5) (sourceB2588 + difference 5 0) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA2588 + difference 0 5) (sourceB2588 + difference 5 0) sourceC2588) = raw35893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35893; decide +kernel
    rw [ha]
    exact (canonical35893 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2588 + difference 1 0) (sourceB2588 + difference 0 1) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA2588 + difference 1 0) (sourceB2588 + difference 0 1) sourceC2588) = raw35894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35894; decide +kernel
    rw [ha]
    exact (canonical35894 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2588 + difference 1 2) (sourceB2588 + difference 2 1) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA2588 + difference 1 2) (sourceB2588 + difference 2 1) sourceC2588) = raw35895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35895; decide +kernel
    rw [ha]
    exact (canonical35895 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2588 + difference 1 3) (sourceB2588 + difference 3 1) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA2588 + difference 1 3) (sourceB2588 + difference 3 1) sourceC2588) = raw35896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35896; decide +kernel
    rw [ha]
    exact (canonical35896 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2588 + difference 1 4) (sourceB2588 + difference 4 1) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2588 + difference 1 4) (sourceB2588 + difference 4 1) sourceC2588) = raw35897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35897; decide +kernel
    rw [ha]
    exact (canonical35897 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2588 + difference 1 5) (sourceB2588 + difference 5 1) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA2588 + difference 1 5) (sourceB2588 + difference 5 1) sourceC2588) = raw35898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35898; decide +kernel
    rw [ha]
    exact (canonical35898 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2588 + difference 2 0) (sourceB2588 + difference 0 2) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2145) := by
    have ha : (tripleCharges (sourceA2588 + difference 2 0) (sourceB2588 + difference 0 2) sourceC2588) = raw35899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35899; decide +kernel
    rw [ha]
    exact (canonical35899 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2588 + difference 2 1) (sourceB2588 + difference 1 2) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3553) := by
    have ha : (tripleCharges (sourceA2588 + difference 2 1) (sourceB2588 + difference 1 2) sourceC2588) = raw35900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35900; decide +kernel
    rw [ha]
    exact (canonical35900 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2588 + difference 2 3) (sourceB2588 + difference 3 2) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA2588 + difference 2 3) (sourceB2588 + difference 3 2) sourceC2588) = raw35901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35901; decide +kernel
    rw [ha]
    exact (canonical35901 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2588 + difference 2 4) (sourceB2588 + difference 4 2) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2588 + difference 2 4) (sourceB2588 + difference 4 2) sourceC2588) = raw35902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35902; decide +kernel
    rw [ha]
    exact (canonical35902 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2588 + difference 2 5) (sourceB2588 + difference 5 2) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA2588 + difference 2 5) (sourceB2588 + difference 5 2) sourceC2588) = raw35903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35903; decide +kernel
    rw [ha]
    exact (canonical35903 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2588 + difference 3 0) (sourceB2588 + difference 0 3) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2154) := by
    have ha : (tripleCharges (sourceA2588 + difference 3 0) (sourceB2588 + difference 0 3) sourceC2588) = raw35904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35904; decide +kernel
    rw [ha]
    exact (canonical35904 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2588 + difference 3 1) (sourceB2588 + difference 1 3) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2588 + difference 3 1) (sourceB2588 + difference 1 3) sourceC2588) = raw35905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35905; decide +kernel
    rw [ha]
    exact (canonical35905 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2588 + difference 3 2) (sourceB2588 + difference 2 3) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3754) := by
    have ha : (tripleCharges (sourceA2588 + difference 3 2) (sourceB2588 + difference 2 3) sourceC2588) = raw35906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35906; decide +kernel
    rw [ha]
    exact (canonical35906 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2588 + difference 3 4) (sourceB2588 + difference 4 3) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2588 + difference 3 4) (sourceB2588 + difference 4 3) sourceC2588) = raw35907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35907; decide +kernel
    rw [ha]
    exact (canonical35907 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2588 + difference 3 5) (sourceB2588 + difference 5 3) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2588 + difference 3 5) (sourceB2588 + difference 5 3) sourceC2588) = raw35908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35908; decide +kernel
    rw [ha]
    exact (canonical35908 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2588 + difference 4 0) (sourceB2588 + difference 0 4) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2144) := by
    have ha : (tripleCharges (sourceA2588 + difference 4 0) (sourceB2588 + difference 0 4) sourceC2588) = raw35909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35909; decide +kernel
    rw [ha]
    exact (canonical35909 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2588 + difference 4 1) (sourceB2588 + difference 1 4) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3509) := by
    have ha : (tripleCharges (sourceA2588 + difference 4 1) (sourceB2588 + difference 1 4) sourceC2588) = raw35910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35910; decide +kernel
    rw [ha]
    exact (canonical35910 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2588 + difference 4 2) (sourceB2588 + difference 2 4) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3791) := by
    have ha : (tripleCharges (sourceA2588 + difference 4 2) (sourceB2588 + difference 2 4) sourceC2588) = raw35911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35911; decide +kernel
    rw [ha]
    exact (canonical35911 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2588 + difference 4 3) (sourceB2588 + difference 3 4) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3833) := by
    have ha : (tripleCharges (sourceA2588 + difference 4 3) (sourceB2588 + difference 3 4) sourceC2588) = raw35912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35912; decide +kernel
    rw [ha]
    exact (canonical35912 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2588 + difference 4 5) (sourceB2588 + difference 5 4) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA2588 + difference 4 5) (sourceB2588 + difference 5 4) sourceC2588) = raw35913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35913; decide +kernel
    rw [ha]
    exact (canonical35913 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2588 + difference 5 0) (sourceB2588 + difference 0 5) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2147) := by
    have ha : (tripleCharges (sourceA2588 + difference 5 0) (sourceB2588 + difference 0 5) sourceC2588) = raw35914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35914; decide +kernel
    rw [ha]
    exact (canonical35914 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2588 + difference 5 1) (sourceB2588 + difference 1 5) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3452) := by
    have ha : (tripleCharges (sourceA2588 + difference 5 1) (sourceB2588 + difference 1 5) sourceC2588) = raw35915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35915; decide +kernel
    rw [ha]
    exact (canonical35915 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2588 + difference 5 2) (sourceB2588 + difference 2 5) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3453) := by
    have ha : (tripleCharges (sourceA2588 + difference 5 2) (sourceB2588 + difference 2 5) sourceC2588) = raw35916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35916; decide +kernel
    rw [ha]
    exact (canonical35916 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2588 + difference 5 3) (sourceB2588 + difference 3 5) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2588 + difference 5 3) (sourceB2588 + difference 3 5) sourceC2588) = raw35917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35917; decide +kernel
    rw [ha]
    exact (canonical35917 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2588 + difference 5 4) (sourceB2588 + difference 4 5) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2588 + difference 5 4) (sourceB2588 + difference 4 5) sourceC2588) = raw35918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35918; decide +kernel
    rw [ha]
    exact (canonical35918 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2588 sourceB2588 sourceC2588
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2588, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources81
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2592 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2592 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2592 + difference 0 1) (sourceB2592 + difference 1 0) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA2592 + difference 0 1) (sourceB2592 + difference 1 0) sourceC2592) = raw35975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35975; decide +kernel
    rw [ha]
    exact (canonical35975 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2592 + difference 0 2) (sourceB2592 + difference 2 0) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA2592 + difference 0 2) (sourceB2592 + difference 2 0) sourceC2592) = raw35976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35976; decide +kernel
    rw [ha]
    exact (canonical35976 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2592 + difference 0 3) (sourceB2592 + difference 3 0) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA2592 + difference 0 3) (sourceB2592 + difference 3 0) sourceC2592) = raw35977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35977; decide +kernel
    rw [ha]
    exact (canonical35977 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2592 + difference 0 4) (sourceB2592 + difference 4 0) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA2592 + difference 0 4) (sourceB2592 + difference 4 0) sourceC2592) = raw35978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35978; decide +kernel
    rw [ha]
    exact (canonical35978 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2592 + difference 0 5) (sourceB2592 + difference 5 0) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA2592 + difference 0 5) (sourceB2592 + difference 5 0) sourceC2592) = raw35979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35979; decide +kernel
    rw [ha]
    exact (canonical35979 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2592 + difference 1 0) (sourceB2592 + difference 0 1) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA2592 + difference 1 0) (sourceB2592 + difference 0 1) sourceC2592) = raw35980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35980; decide +kernel
    rw [ha]
    exact (canonical35980 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2592 + difference 1 2) (sourceB2592 + difference 2 1) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA2592 + difference 1 2) (sourceB2592 + difference 2 1) sourceC2592) = raw35981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35981; decide +kernel
    rw [ha]
    exact (canonical35981 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2592 + difference 1 3) (sourceB2592 + difference 3 1) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA2592 + difference 1 3) (sourceB2592 + difference 3 1) sourceC2592) = raw35982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35982; decide +kernel
    rw [ha]
    exact (canonical35982 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2592 + difference 1 4) (sourceB2592 + difference 4 1) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA2592 + difference 1 4) (sourceB2592 + difference 4 1) sourceC2592) = raw35983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35983; decide +kernel
    rw [ha]
    exact (canonical35983 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2592 + difference 1 5) (sourceB2592 + difference 5 1) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA2592 + difference 1 5) (sourceB2592 + difference 5 1) sourceC2592) = raw35984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35984; decide +kernel
    rw [ha]
    exact (canonical35984 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2592 + difference 2 0) (sourceB2592 + difference 0 2) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2238) := by
    have ha : (tripleCharges (sourceA2592 + difference 2 0) (sourceB2592 + difference 0 2) sourceC2592) = raw35985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35985; decide +kernel
    rw [ha]
    exact (canonical35985 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2592 + difference 2 1) (sourceB2592 + difference 1 2) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2150) := by
    have ha : (tripleCharges (sourceA2592 + difference 2 1) (sourceB2592 + difference 1 2) sourceC2592) = raw35986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35986; decide +kernel
    rw [ha]
    exact (canonical35986 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2592 + difference 2 3) (sourceB2592 + difference 3 2) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2592 + difference 2 3) (sourceB2592 + difference 3 2) sourceC2592) = raw35987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35987; decide +kernel
    rw [ha]
    exact (canonical35987 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2592 + difference 2 4) (sourceB2592 + difference 4 2) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2592 + difference 2 4) (sourceB2592 + difference 4 2) sourceC2592) = raw35988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35988; decide +kernel
    rw [ha]
    exact (canonical35988 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2592 + difference 2 5) (sourceB2592 + difference 5 2) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA2592 + difference 2 5) (sourceB2592 + difference 5 2) sourceC2592) = raw35989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35989; decide +kernel
    rw [ha]
    exact (canonical35989 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2592 + difference 3 0) (sourceB2592 + difference 0 3) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2257) := by
    have ha : (tripleCharges (sourceA2592 + difference 3 0) (sourceB2592 + difference 0 3) sourceC2592) = raw35990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35990; decide +kernel
    rw [ha]
    exact (canonical35990 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2592 + difference 3 1) (sourceB2592 + difference 1 3) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2166) := by
    have ha : (tripleCharges (sourceA2592 + difference 3 1) (sourceB2592 + difference 1 3) sourceC2592) = raw35991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35991; decide +kernel
    rw [ha]
    exact (canonical35991 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2592 + difference 3 2) (sourceB2592 + difference 2 3) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2656) := by
    have ha : (tripleCharges (sourceA2592 + difference 3 2) (sourceB2592 + difference 2 3) sourceC2592) = raw35992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35992; decide +kernel
    rw [ha]
    exact (canonical35992 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2592 + difference 3 4) (sourceB2592 + difference 4 3) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA2592 + difference 3 4) (sourceB2592 + difference 4 3) sourceC2592) = raw35993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35993; decide +kernel
    rw [ha]
    exact (canonical35993 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2592 + difference 3 5) (sourceB2592 + difference 5 3) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA2592 + difference 3 5) (sourceB2592 + difference 5 3) sourceC2592) = raw35994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35994; decide +kernel
    rw [ha]
    exact (canonical35994 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2592 + difference 4 0) (sourceB2592 + difference 0 4) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2257) := by
    have ha : (tripleCharges (sourceA2592 + difference 4 0) (sourceB2592 + difference 0 4) sourceC2592) = raw35995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35995; decide +kernel
    rw [ha]
    exact (canonical35995 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2592 + difference 4 1) (sourceB2592 + difference 1 4) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2166) := by
    have ha : (tripleCharges (sourceA2592 + difference 4 1) (sourceB2592 + difference 1 4) sourceC2592) = raw35996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35996; decide +kernel
    rw [ha]
    exact (canonical35996 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2592 + difference 4 2) (sourceB2592 + difference 2 4) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2656) := by
    have ha : (tripleCharges (sourceA2592 + difference 4 2) (sourceB2592 + difference 2 4) sourceC2592) = raw35997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35997; decide +kernel
    rw [ha]
    exact (canonical35997 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2592 + difference 4 3) (sourceB2592 + difference 3 4) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA2592 + difference 4 3) (sourceB2592 + difference 3 4) sourceC2592) = raw35998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35998; decide +kernel
    rw [ha]
    exact (canonical35998 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2592 + difference 4 5) (sourceB2592 + difference 5 4) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA2592 + difference 4 5) (sourceB2592 + difference 5 4) sourceC2592) = raw35999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35999; decide +kernel
    rw [ha]
    exact (canonical35999 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2592 + difference 5 0) (sourceB2592 + difference 0 5) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2239) := by
    have ha : (tripleCharges (sourceA2592 + difference 5 0) (sourceB2592 + difference 0 5) sourceC2592) = raw36000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw36000; decide +kernel
    rw [ha]
    exact (canonical36000 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2592 + difference 5 1) (sourceB2592 + difference 1 5) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2165) := by
    have ha : (tripleCharges (sourceA2592 + difference 5 1) (sourceB2592 + difference 1 5) sourceC2592) = raw36001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw36001; decide +kernel
    rw [ha]
    exact (canonical36001 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2592 + difference 5 2) (sourceB2592 + difference 2 5) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2655) := by
    have ha : (tripleCharges (sourceA2592 + difference 5 2) (sourceB2592 + difference 2 5) sourceC2592) = raw36002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw36002; decide +kernel
    rw [ha]
    exact (canonical36002 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2592 + difference 5 3) (sourceB2592 + difference 3 5) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA2592 + difference 5 3) (sourceB2592 + difference 3 5) sourceC2592) = raw36003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw36003; decide +kernel
    rw [ha]
    exact (canonical36003 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2592 + difference 5 4) (sourceB2592 + difference 4 5) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA2592 + difference 5 4) (sourceB2592 + difference 4 5) sourceC2592) = raw36004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw36004; decide +kernel
    rw [ha]
    exact (canonical36004 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2592 sourceB2592 sourceC2592
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2592, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2603 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2603 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2603 + difference 0 1) (sourceB2603 + difference 1 0) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA2603 + difference 0 1) (sourceB2603 + difference 1 0) sourceC2603) = raw36203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36203; decide +kernel
    rw [ha]
    exact (canonical36203 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2603 + difference 0 2) (sourceB2603 + difference 2 0) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2603 + difference 0 2) (sourceB2603 + difference 2 0) sourceC2603) = raw36204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36204; decide +kernel
    rw [ha]
    exact (canonical36204 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2603 + difference 0 3) (sourceB2603 + difference 3 0) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA2603 + difference 0 3) (sourceB2603 + difference 3 0) sourceC2603) = raw36205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36205; decide +kernel
    rw [ha]
    exact (canonical36205 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2603 + difference 0 4) (sourceB2603 + difference 4 0) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2603 + difference 0 4) (sourceB2603 + difference 4 0) sourceC2603) = raw36206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36206; decide +kernel
    rw [ha]
    exact (canonical36206 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2603 + difference 0 5) (sourceB2603 + difference 5 0) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA2603 + difference 0 5) (sourceB2603 + difference 5 0) sourceC2603) = raw36207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36207; decide +kernel
    rw [ha]
    exact (canonical36207 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2603 + difference 1 0) (sourceB2603 + difference 0 1) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA2603 + difference 1 0) (sourceB2603 + difference 0 1) sourceC2603) = raw36208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36208; decide +kernel
    rw [ha]
    exact (canonical36208 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2603 + difference 1 2) (sourceB2603 + difference 2 1) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2603 + difference 1 2) (sourceB2603 + difference 2 1) sourceC2603) = raw32155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32155; decide +kernel
    rw [ha]
    exact (canonical32155 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2603 + difference 1 3) (sourceB2603 + difference 3 1) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA2603 + difference 1 3) (sourceB2603 + difference 3 1) sourceC2603) = raw32156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32156; decide +kernel
    rw [ha]
    exact (canonical32156 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2603 + difference 1 4) (sourceB2603 + difference 4 1) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2603 + difference 1 4) (sourceB2603 + difference 4 1) sourceC2603) = raw32157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32157; decide +kernel
    rw [ha]
    exact (canonical32157 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2603 + difference 1 5) (sourceB2603 + difference 5 1) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA2603 + difference 1 5) (sourceB2603 + difference 5 1) sourceC2603) = raw32158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32158; decide +kernel
    rw [ha]
    exact (canonical32158 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2603 + difference 2 0) (sourceB2603 + difference 0 2) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2603 + difference 2 0) (sourceB2603 + difference 0 2) sourceC2603) = raw32165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32165; decide +kernel
    rw [ha]
    exact (canonical32165 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2603 + difference 2 1) (sourceB2603 + difference 1 2) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2603 + difference 2 1) (sourceB2603 + difference 1 2) sourceC2603) = raw36209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36209; decide +kernel
    rw [ha]
    exact (canonical36209 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2603 + difference 2 3) (sourceB2603 + difference 3 2) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3842) := by
    have ha : (tripleCharges (sourceA2603 + difference 2 3) (sourceB2603 + difference 3 2) sourceC2603) = raw36210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36210; decide +kernel
    rw [ha]
    exact (canonical36210 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2603 + difference 2 4) (sourceB2603 + difference 4 2) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3797) := by
    have ha : (tripleCharges (sourceA2603 + difference 2 4) (sourceB2603 + difference 4 2) sourceC2603) = raw36211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36211; decide +kernel
    rw [ha]
    exact (canonical36211 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2603 + difference 2 5) (sourceB2603 + difference 5 2) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3973) := by
    have ha : (tripleCharges (sourceA2603 + difference 2 5) (sourceB2603 + difference 5 2) sourceC2603) = raw36212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36212; decide +kernel
    rw [ha]
    exact (canonical36212 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2603 + difference 3 0) (sourceB2603 + difference 0 3) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2603 + difference 3 0) (sourceB2603 + difference 0 3) sourceC2603) = raw32170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32170; decide +kernel
    rw [ha]
    exact (canonical32170 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2603 + difference 3 1) (sourceB2603 + difference 1 3) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2603 + difference 3 1) (sourceB2603 + difference 1 3) sourceC2603) = raw36213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36213; decide +kernel
    rw [ha]
    exact (canonical36213 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2603 + difference 3 2) (sourceB2603 + difference 2 3) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3763) := by
    have ha : (tripleCharges (sourceA2603 + difference 3 2) (sourceB2603 + difference 2 3) sourceC2603) = raw36214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36214; decide +kernel
    rw [ha]
    exact (canonical36214 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2603 + difference 3 4) (sourceB2603 + difference 4 3) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3773) := by
    have ha : (tripleCharges (sourceA2603 + difference 3 4) (sourceB2603 + difference 4 3) sourceC2603) = raw36215 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36215; decide +kernel
    rw [ha]
    exact (canonical36215 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2603 + difference 3 5) (sourceB2603 + difference 5 3) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3960) := by
    have ha : (tripleCharges (sourceA2603 + difference 3 5) (sourceB2603 + difference 5 3) sourceC2603) = raw36216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36216; decide +kernel
    rw [ha]
    exact (canonical36216 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2603 + difference 4 0) (sourceB2603 + difference 0 4) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2603 + difference 4 0) (sourceB2603 + difference 0 4) sourceC2603) = raw32175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32175; decide +kernel
    rw [ha]
    exact (canonical32175 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2603 + difference 4 1) (sourceB2603 + difference 1 4) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2603 + difference 4 1) (sourceB2603 + difference 1 4) sourceC2603) = raw36217 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36217; decide +kernel
    rw [ha]
    exact (canonical36217 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2603 + difference 4 2) (sourceB2603 + difference 2 4) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2656) := by
    have ha : (tripleCharges (sourceA2603 + difference 4 2) (sourceB2603 + difference 2 4) sourceC2603) = raw36218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36218; decide +kernel
    rw [ha]
    exact (canonical36218 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2603 + difference 4 3) (sourceB2603 + difference 3 4) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA2603 + difference 4 3) (sourceB2603 + difference 3 4) sourceC2603) = raw36219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36219; decide +kernel
    rw [ha]
    exact (canonical36219 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2603 + difference 4 5) (sourceB2603 + difference 5 4) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA2603 + difference 4 5) (sourceB2603 + difference 5 4) sourceC2603) = raw36220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36220; decide +kernel
    rw [ha]
    exact (canonical36220 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2603 + difference 5 0) (sourceB2603 + difference 0 5) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2603 + difference 5 0) (sourceB2603 + difference 0 5) sourceC2603) = raw32180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32180; decide +kernel
    rw [ha]
    exact (canonical32180 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2603 + difference 5 1) (sourceB2603 + difference 1 5) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2603 + difference 5 1) (sourceB2603 + difference 1 5) sourceC2603) = raw36221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36221; decide +kernel
    rw [ha]
    exact (canonical36221 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2603 + difference 5 2) (sourceB2603 + difference 2 5) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3465) := by
    have ha : (tripleCharges (sourceA2603 + difference 5 2) (sourceB2603 + difference 2 5) sourceC2603) = raw36222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36222; decide +kernel
    rw [ha]
    exact (canonical36222 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2603 + difference 5 3) (sourceB2603 + difference 3 5) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2603 + difference 5 3) (sourceB2603 + difference 3 5) sourceC2603) = raw36223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36223; decide +kernel
    rw [ha]
    exact (canonical36223 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2603 + difference 5 4) (sourceB2603 + difference 4 5) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2603 + difference 5 4) (sourceB2603 + difference 4 5) sourceC2603) = raw36224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36224; decide +kernel
    rw [ha]
    exact (canonical36224 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2603 sourceB2603 sourceC2603
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2603, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2068 : Integer.Sparse.reindex keyMap MixedData.row2068 = numericRow2068 := by decide +kernel

theorem numericCheck2068 (x : Master → ℝ) : Integer.Sparse.eval numericRow2068 x =
    (1 : ℝ) * reducedSource2068 x := by
  norm_num [numericRow2068, reducedSource2068, Integer.Sparse.eval, Sparse.eval, nodeValue2140, nodeValue2142, nodeValue2148, nodeValue2240, nodeValue3510, nodeValue3511, nodeValue3516, nodeValue3521, nodeValue3554, nodeValue3597, nodeValue3792, nodeValue3798, nodeValue3832, nodeValue3835, nodeValue3836, nodeValue3843, nodeValue3844, nodeValue3848, nodeValue3867, nodeValue3900, nodeValue3909]

theorem reindexCheck2070 : Integer.Sparse.reindex keyMap MixedData.row2070 = numericRow2070 := by decide +kernel

theorem numericCheck2070 (x : Master → ℝ) : Integer.Sparse.eval numericRow2070 x =
    (1 : ℝ) * reducedSource2070 x := by
  norm_num [numericRow2070, reducedSource2070, Integer.Sparse.eval, Sparse.eval, nodeValue2144, nodeValue2145, nodeValue2147, nodeValue2154, nodeValue2250, nodeValue3452, nodeValue3453, nodeValue3478, nodeValue3508, nodeValue3509, nodeValue3514, nodeValue3516, nodeValue3553, nodeValue3754, nodeValue3770, nodeValue3791, nodeValue3793, nodeValue3796, nodeValue3807, nodeValue3811, nodeValue3813, nodeValue3832, nodeValue3833, nodeValue3834, nodeValue3837, nodeValue3838, nodeValue3840, nodeValue3866, nodeValue3880]

theorem reindexCheck2072 : Integer.Sparse.reindex keyMap MixedData.row2072 = numericRow2072 := by decide +kernel

theorem numericCheck2072 (x : Master → ℝ) : Integer.Sparse.eval numericRow2072 x =
    (1 : ℝ) * reducedSource2072 x := by
  norm_num [numericRow2072, reducedSource2072, Integer.Sparse.eval, Sparse.eval, nodeValue2150, nodeValue2165, nodeValue2166, nodeValue2227, nodeValue2238, nodeValue2239, nodeValue2246, nodeValue2257, nodeValue2655, nodeValue2656, nodeValue2669, nodeValue2671, nodeValue2681, nodeValue2682, nodeValue2684, nodeValue2703, nodeValue2739, nodeValue2741, nodeValue3023, nodeValue3051, nodeValue3053]

theorem reindexCheck2079 : Integer.Sparse.reindex keyMap MixedData.row2079 = numericRow2079 := by decide +kernel

theorem numericCheck2079 (x : Master → ℝ) : Integer.Sparse.eval numericRow2079 x =
    (1 : ℝ) * reducedSource2079 x := by
  norm_num [numericRow2079, reducedSource2079, Integer.Sparse.eval, Sparse.eval, nodeValue2656, nodeValue2658, nodeValue2682, nodeValue2736, nodeValue3407, nodeValue3413, nodeValue3418, nodeValue3465, nodeValue3482, nodeValue3542, nodeValue3606, nodeValue3763, nodeValue3773, nodeValue3797, nodeValue3804, nodeValue3816, nodeValue3842, nodeValue3857, nodeValue3960, nodeValue3973, nodeValue3983]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2068 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2068 (mixedVector B) = 0 := by
  have h2140 : mixedVector B (Sum.inr 2140) = Sparse.eval nodeValue2140 (mixedVector B) := by
    change mixedMoment B node2140 node2140Labels = _
    exact sound2140 B hB hF
  have h2142 : mixedVector B (Sum.inr 2142) = Sparse.eval nodeValue2142 (mixedVector B) := by
    change mixedMoment B node2142 node2142Labels = _
    exact sound2142 B hB hF
  have h2148 : mixedVector B (Sum.inr 2148) = Sparse.eval nodeValue2148 (mixedVector B) := by
    change mixedMoment B node2148 node2148Labels = _
    exact sound2148 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h3510 : mixedVector B (Sum.inr 3510) = Sparse.eval nodeValue3510 (mixedVector B) := by
    change mixedMoment B node3510 node3510Labels = _
    exact sound3510 B hB hF
  have h3511 : mixedVector B (Sum.inr 3511) = Sparse.eval nodeValue3511 (mixedVector B) := by
    change mixedMoment B node3511 node3511Labels = _
    exact sound3511 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3521 : mixedVector B (Sum.inr 3521) = Sparse.eval nodeValue3521 (mixedVector B) := by
    change mixedMoment B node3521 node3521Labels = _
    exact sound3521 B hB hF
  have h3554 : mixedVector B (Sum.inr 3554) = Sparse.eval nodeValue3554 (mixedVector B) := by
    change mixedMoment B node3554 node3554Labels = _
    exact sound3554 B hB hF
  have h3597 : mixedVector B (Sum.inr 3597) = Sparse.eval nodeValue3597 (mixedVector B) := by
    change mixedMoment B node3597 node3597Labels = _
    exact sound3597 B hB hF
  have h3792 : mixedVector B (Sum.inr 3792) = Sparse.eval nodeValue3792 (mixedVector B) := by
    change mixedMoment B node3792 node3792Labels = _
    exact sound3792 B hB hF
  have h3798 : mixedVector B (Sum.inr 3798) = Sparse.eval nodeValue3798 (mixedVector B) := by
    change mixedMoment B node3798 node3798Labels = _
    exact sound3798 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h3835 : mixedVector B (Sum.inr 3835) = Sparse.eval nodeValue3835 (mixedVector B) := by
    change mixedMoment B node3835 node3835Labels = _
    exact sound3835 B hB hF
  have h3836 : mixedVector B (Sum.inr 3836) = Sparse.eval nodeValue3836 (mixedVector B) := by
    change mixedMoment B node3836 node3836Labels = _
    exact sound3836 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3844 : mixedVector B (Sum.inr 3844) = Sparse.eval nodeValue3844 (mixedVector B) := by
    change mixedMoment B node3844 node3844Labels = _
    exact sound3844 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3867 : mixedVector B (Sum.inr 3867) = Sparse.eval nodeValue3867 (mixedVector B) := by
    change mixedMoment B node3867 node3867Labels = _
    exact sound3867 B hB hF
  have h3900 : mixedVector B (Sum.inr 3900) = Sparse.eval nodeValue3900 (mixedVector B) := by
    change mixedMoment B node3900 node3900Labels = _
    exact sound3900 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  simpa only [sourceForm2584, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2140, h2142, h2148, h2240, h3510, h3511, h3516, h3521, h3554, h3597, h3792, h3798, h3832, h3835, h3836, h3843, h3844, h3848, h3867, h3900, h3909, reducedSource2068] using sourceEq2584 B hB

theorem rowSound2068 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2068 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2068, numericCheck2068, reducedZero2068 B hB hF, mul_zero]

theorem reducedZero2070 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2070 (mixedVector B) = 0 := by
  have h2144 : mixedVector B (Sum.inr 2144) = Sparse.eval nodeValue2144 (mixedVector B) := by
    change mixedMoment B node2144 node2144Labels = _
    exact sound2144 B hB hF
  have h2145 : mixedVector B (Sum.inr 2145) = Sparse.eval nodeValue2145 (mixedVector B) := by
    change mixedMoment B node2145 node2145Labels = _
    exact sound2145 B hB hF
  have h2147 : mixedVector B (Sum.inr 2147) = Sparse.eval nodeValue2147 (mixedVector B) := by
    change mixedMoment B node2147 node2147Labels = _
    exact sound2147 B hB hF
  have h2154 : mixedVector B (Sum.inr 2154) = Sparse.eval nodeValue2154 (mixedVector B) := by
    change mixedMoment B node2154 node2154Labels = _
    exact sound2154 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h3452 : mixedVector B (Sum.inr 3452) = Sparse.eval nodeValue3452 (mixedVector B) := by
    change mixedMoment B node3452 node3452Labels = _
    exact sound3452 B hB hF
  have h3453 : mixedVector B (Sum.inr 3453) = Sparse.eval nodeValue3453 (mixedVector B) := by
    change mixedMoment B node3453 node3453Labels = _
    exact sound3453 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3508 : mixedVector B (Sum.inr 3508) = Sparse.eval nodeValue3508 (mixedVector B) := by
    change mixedMoment B node3508 node3508Labels = _
    exact sound3508 B hB hF
  have h3509 : mixedVector B (Sum.inr 3509) = Sparse.eval nodeValue3509 (mixedVector B) := by
    change mixedMoment B node3509 node3509Labels = _
    exact sound3509 B hB hF
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3553 : mixedVector B (Sum.inr 3553) = Sparse.eval nodeValue3553 (mixedVector B) := by
    change mixedMoment B node3553 node3553Labels = _
    exact sound3553 B hB hF
  have h3754 : mixedVector B (Sum.inr 3754) = Sparse.eval nodeValue3754 (mixedVector B) := by
    change mixedMoment B node3754 node3754Labels = _
    exact sound3754 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h3791 : mixedVector B (Sum.inr 3791) = Sparse.eval nodeValue3791 (mixedVector B) := by
    change mixedMoment B node3791 node3791Labels = _
    exact sound3791 B hB hF
  have h3793 : mixedVector B (Sum.inr 3793) = Sparse.eval nodeValue3793 (mixedVector B) := by
    change mixedMoment B node3793 node3793Labels = _
    exact sound3793 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3811 : mixedVector B (Sum.inr 3811) = Sparse.eval nodeValue3811 (mixedVector B) := by
    change mixedMoment B node3811 node3811Labels = _
    exact sound3811 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h3833 : mixedVector B (Sum.inr 3833) = Sparse.eval nodeValue3833 (mixedVector B) := by
    change mixedMoment B node3833 node3833Labels = _
    exact sound3833 B hB hF
  have h3834 : mixedVector B (Sum.inr 3834) = Sparse.eval nodeValue3834 (mixedVector B) := by
    change mixedMoment B node3834 node3834Labels = _
    exact sound3834 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3866 : mixedVector B (Sum.inr 3866) = Sparse.eval nodeValue3866 (mixedVector B) := by
    change mixedMoment B node3866 node3866Labels = _
    exact sound3866 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  simpa only [sourceForm2588, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2144, h2145, h2147, h2154, h2250, h3452, h3453, h3478, h3508, h3509, h3514, h3516, h3553, h3754, h3770, h3791, h3793, h3796, h3807, h3811, h3813, h3832, h3833, h3834, h3837, h3838, h3840, h3866, h3880, reducedSource2070] using sourceEq2588 B hB

theorem rowSound2070 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2070 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2070, numericCheck2070, reducedZero2070 B hB hF, mul_zero]

theorem reducedZero2072 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2072 (mixedVector B) = 0 := by
  have h2150 : mixedVector B (Sum.inr 2150) = Sparse.eval nodeValue2150 (mixedVector B) := by
    change mixedMoment B node2150 node2150Labels = _
    exact sound2150 B hB hF
  have h2165 : mixedVector B (Sum.inr 2165) = Sparse.eval nodeValue2165 (mixedVector B) := by
    change mixedMoment B node2165 node2165Labels = _
    exact sound2165 B hB hF
  have h2166 : mixedVector B (Sum.inr 2166) = Sparse.eval nodeValue2166 (mixedVector B) := by
    change mixedMoment B node2166 node2166Labels = _
    exact sound2166 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h2238 : mixedVector B (Sum.inr 2238) = Sparse.eval nodeValue2238 (mixedVector B) := by
    change mixedMoment B node2238 node2238Labels = _
    exact sound2238 B hB hF
  have h2239 : mixedVector B (Sum.inr 2239) = Sparse.eval nodeValue2239 (mixedVector B) := by
    change mixedMoment B node2239 node2239Labels = _
    exact sound2239 B hB hF
  have h2246 : mixedVector B (Sum.inr 2246) = Sparse.eval nodeValue2246 (mixedVector B) := by
    change mixedMoment B node2246 node2246Labels = _
    exact sound2246 B hB hF
  have h2257 : mixedVector B (Sum.inr 2257) = Sparse.eval nodeValue2257 (mixedVector B) := by
    change mixedMoment B node2257 node2257Labels = _
    exact sound2257 B hB hF
  have h2655 : mixedVector B (Sum.inr 2655) = Sparse.eval nodeValue2655 (mixedVector B) := by
    change mixedMoment B node2655 node2655Labels = _
    exact sound2655 B hB hF
  have h2656 : mixedVector B (Sum.inr 2656) = Sparse.eval nodeValue2656 (mixedVector B) := by
    change mixedMoment B node2656 node2656Labels = _
    exact sound2656 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2682 : mixedVector B (Sum.inr 2682) = Sparse.eval nodeValue2682 (mixedVector B) := by
    change mixedMoment B node2682 node2682Labels = _
    exact sound2682 B hB hF
  have h2684 : mixedVector B (Sum.inr 2684) = Sparse.eval nodeValue2684 (mixedVector B) := by
    change mixedMoment B node2684 node2684Labels = _
    exact sound2684 B hB hF
  have h2703 : mixedVector B (Sum.inr 2703) = Sparse.eval nodeValue2703 (mixedVector B) := by
    change mixedMoment B node2703 node2703Labels = _
    exact sound2703 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2741 : mixedVector B (Sum.inr 2741) = Sparse.eval nodeValue2741 (mixedVector B) := by
    change mixedMoment B node2741 node2741Labels = _
    exact sound2741 B hB hF
  have h3023 : mixedVector B (Sum.inr 3023) = Sparse.eval nodeValue3023 (mixedVector B) := by
    change mixedMoment B node3023 node3023Labels = _
    exact sound3023 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  simpa only [sourceForm2592, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2150, h2165, h2166, h2227, h2238, h2239, h2246, h2257, h2655, h2656, h2669, h2671, h2681, h2682, h2684, h2703, h2739, h2741, h3023, h3051, h3053, reducedSource2072] using sourceEq2592 B hB

theorem rowSound2072 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2072 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2072, numericCheck2072, reducedZero2072 B hB hF, mul_zero]

theorem reducedZero2079 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2079 (mixedVector B) = 0 := by
  have h2656 : mixedVector B (Sum.inr 2656) = Sparse.eval nodeValue2656 (mixedVector B) := by
    change mixedMoment B node2656 node2656Labels = _
    exact sound2656 B hB hF
  have h2658 : mixedVector B (Sum.inr 2658) = Sparse.eval nodeValue2658 (mixedVector B) := by
    change mixedMoment B node2658 node2658Labels = _
    exact sound2658 B hB hF
  have h2682 : mixedVector B (Sum.inr 2682) = Sparse.eval nodeValue2682 (mixedVector B) := by
    change mixedMoment B node2682 node2682Labels = _
    exact sound2682 B hB hF
  have h2736 : mixedVector B (Sum.inr 2736) = Sparse.eval nodeValue2736 (mixedVector B) := by
    change mixedMoment B node2736 node2736Labels = _
    exact sound2736 B hB hF
  have h3407 : mixedVector B (Sum.inr 3407) = Sparse.eval nodeValue3407 (mixedVector B) := by
    change mixedMoment B node3407 node3407Labels = _
    exact sound3407 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3418 : mixedVector B (Sum.inr 3418) = Sparse.eval nodeValue3418 (mixedVector B) := by
    change mixedMoment B node3418 node3418Labels = _
    exact sound3418 B hB hF
  have h3465 : mixedVector B (Sum.inr 3465) = Sparse.eval nodeValue3465 (mixedVector B) := by
    change mixedMoment B node3465 node3465Labels = _
    exact sound3465 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3542 : mixedVector B (Sum.inr 3542) = Sparse.eval nodeValue3542 (mixedVector B) := by
    change mixedMoment B node3542 node3542Labels = _
    exact sound3542 B hB hF
  have h3606 : mixedVector B (Sum.inr 3606) = Sparse.eval nodeValue3606 (mixedVector B) := by
    change mixedMoment B node3606 node3606Labels = _
    exact sound3606 B hB hF
  have h3763 : mixedVector B (Sum.inr 3763) = Sparse.eval nodeValue3763 (mixedVector B) := by
    change mixedMoment B node3763 node3763Labels = _
    exact sound3763 B hB hF
  have h3773 : mixedVector B (Sum.inr 3773) = Sparse.eval nodeValue3773 (mixedVector B) := by
    change mixedMoment B node3773 node3773Labels = _
    exact sound3773 B hB hF
  have h3797 : mixedVector B (Sum.inr 3797) = Sparse.eval nodeValue3797 (mixedVector B) := by
    change mixedMoment B node3797 node3797Labels = _
    exact sound3797 B hB hF
  have h3804 : mixedVector B (Sum.inr 3804) = Sparse.eval nodeValue3804 (mixedVector B) := by
    change mixedMoment B node3804 node3804Labels = _
    exact sound3804 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3842 : mixedVector B (Sum.inr 3842) = Sparse.eval nodeValue3842 (mixedVector B) := by
    change mixedMoment B node3842 node3842Labels = _
    exact sound3842 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3960 : mixedVector B (Sum.inr 3960) = Sparse.eval nodeValue3960 (mixedVector B) := by
    change mixedMoment B node3960 node3960Labels = _
    exact sound3960 B hB hF
  have h3973 : mixedVector B (Sum.inr 3973) = Sparse.eval nodeValue3973 (mixedVector B) := by
    change mixedMoment B node3973 node3973Labels = _
    exact sound3973 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  simpa only [sourceForm2603, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2656, h2658, h2682, h2736, h3407, h3413, h3418, h3465, h3482, h3542, h3606, h3763, h3773, h3797, h3804, h3816, h3842, h3857, h3960, h3973, h3983, reducedSource2079] using sourceEq2603 B hB

theorem rowSound2079 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2079 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2079, numericCheck2079, reducedZero2079 B hB hF, mul_zero]

theorem sourceRowsAt2064 : MixedData.sourceRows (2064 : Fin 2425) =
    MixedData.row2064 := by decide +kernel

theorem sourceRowsAt2065 : MixedData.sourceRows (2065 : Fin 2425) =
    MixedData.row2065 := by decide +kernel

theorem sourceRowsAt2066 : MixedData.sourceRows (2066 : Fin 2425) =
    MixedData.row2066 := by decide +kernel

theorem sourceRowsAt2067 : MixedData.sourceRows (2067 : Fin 2425) =
    MixedData.row2067 := by decide +kernel

theorem sourceRowsAt2068 : MixedData.sourceRows (2068 : Fin 2425) =
    MixedData.row2068 := by decide +kernel

theorem sourceRowsAt2069 : MixedData.sourceRows (2069 : Fin 2425) =
    MixedData.row2069 := by decide +kernel

theorem sourceRowsAt2070 : MixedData.sourceRows (2070 : Fin 2425) =
    MixedData.row2070 := by decide +kernel

theorem sourceRowsAt2071 : MixedData.sourceRows (2071 : Fin 2425) =
    MixedData.row2071 := by decide +kernel

theorem sourceRowsAt2072 : MixedData.sourceRows (2072 : Fin 2425) =
    MixedData.row2072 := by decide +kernel

theorem sourceRowsAt2073 : MixedData.sourceRows (2073 : Fin 2425) =
    MixedData.row2073 := by decide +kernel

theorem sourceRowsAt2074 : MixedData.sourceRows (2074 : Fin 2425) =
    MixedData.row2074 := by decide +kernel

theorem sourceRowsAt2075 : MixedData.sourceRows (2075 : Fin 2425) =
    MixedData.row2075 := by decide +kernel

theorem sourceRowsAt2076 : MixedData.sourceRows (2076 : Fin 2425) =
    MixedData.row2076 := by decide +kernel

theorem sourceRowsAt2077 : MixedData.sourceRows (2077 : Fin 2425) =
    MixedData.row2077 := by decide +kernel

theorem sourceRowsAt2078 : MixedData.sourceRows (2078 : Fin 2425) =
    MixedData.row2078 := by decide +kernel

theorem sourceRowsAt2079 : MixedData.sourceRows (2079 : Fin 2425) =
    MixedData.row2079 := by decide +kernel

theorem chunkSound129_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 129) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2064 ∨ k.val = 2065 ∨ k.val = 2066 ∨ k.val = 2067 ∨ k.val = 2068 ∨ k.val = 2069 ∨ k.val = 2070 ∨ k.val = 2071 ∨ k.val = 2072 ∨ k.val = 2073 ∨ k.val = 2074 ∨ k.val = 2075 ∨ k.val = 2076 ∨ k.val = 2077 ∨ k.val = 2078 ∨ k.val = 2079 := by omega
  rcases heq with h2064 | h2065 | h2066 | h2067 | h2068 | h2069 | h2070 | h2071 | h2072 | h2073 | h2074 | h2075 | h2076 | h2077 | h2078 | h2079
  · have he : k = (2064 : Fin 2425) := Fin.ext h2064
    subst k
    rw [sourceRowsAt2064]
    exact rowSound2064_e B hB hF
  · have he : k = (2065 : Fin 2425) := Fin.ext h2065
    subst k
    rw [sourceRowsAt2065]
    exact rowSound2065_e B hB hF
  · have he : k = (2066 : Fin 2425) := Fin.ext h2066
    subst k
    rw [sourceRowsAt2066]
    exact rowSound2066_e B hB hF
  · have he : k = (2067 : Fin 2425) := Fin.ext h2067
    subst k
    rw [sourceRowsAt2067]
    exact rowSound2067_e B hB hF
  · have he : k = (2068 : Fin 2425) := Fin.ext h2068
    subst k
    rw [sourceRowsAt2068]
    exact rowSound2068 B hB hF
  · have he : k = (2069 : Fin 2425) := Fin.ext h2069
    subst k
    rw [sourceRowsAt2069]
    exact rowSound2069_e B hB hF
  · have he : k = (2070 : Fin 2425) := Fin.ext h2070
    subst k
    rw [sourceRowsAt2070]
    exact rowSound2070 B hB hF
  · have he : k = (2071 : Fin 2425) := Fin.ext h2071
    subst k
    rw [sourceRowsAt2071]
    exact rowSound2071_e B hB hF
  · have he : k = (2072 : Fin 2425) := Fin.ext h2072
    subst k
    rw [sourceRowsAt2072]
    exact rowSound2072 B hB hF
  · have he : k = (2073 : Fin 2425) := Fin.ext h2073
    subst k
    rw [sourceRowsAt2073]
    exact rowSound2073_e B hB hF
  · have he : k = (2074 : Fin 2425) := Fin.ext h2074
    subst k
    rw [sourceRowsAt2074]
    exact rowSound2074_e B hB hF
  · have he : k = (2075 : Fin 2425) := Fin.ext h2075
    subst k
    rw [sourceRowsAt2075]
    exact rowSound2075_e B hB hF
  · have he : k = (2076 : Fin 2425) := Fin.ext h2076
    subst k
    rw [sourceRowsAt2076]
    exact rowSound2076_e B hB hF
  · have he : k = (2077 : Fin 2425) := Fin.ext h2077
    subst k
    rw [sourceRowsAt2077]
    exact rowSound2077_e B hB hF
  · have he : k = (2078 : Fin 2425) := Fin.ext h2078
    subst k
    rw [sourceRowsAt2078]
    exact rowSound2078_e B hB hF
  · have he : k = (2079 : Fin 2425) := Fin.ext h2079
    subst k
    rw [sourceRowsAt2079]
    exact rowSound2079 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound129_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound129_e_oai
