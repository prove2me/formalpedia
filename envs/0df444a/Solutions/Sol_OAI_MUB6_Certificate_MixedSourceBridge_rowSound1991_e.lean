-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:38:54.423197+00:00
-- url     : https://prove2.me/submissions/a0c38434-7c67-4ad7-892f-4588d05f79ad

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1341_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1414_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2941_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3089_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3140_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3185_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3206_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3209_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3227_e

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

end MUB6.Certificate.MixedSemantics

end

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

theorem canonical34019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34019 raw34019Labels = mixedMoment B node3069 node3069Labels := by
  calc
    mixedMoment B raw34019 raw34019Labels = mixedMoment B raw34019step0 raw34019step0Labels := by
      have ha : raw34019step0 = (fun i j => raw34019 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34019step0 raw34019; decide +kernel
      have hl : raw34019step0Labels = raw34019Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34019 raw34019Labels permutation212 permutation6
    mixedMoment B raw34019step0 raw34019step0Labels = mixedMoment B raw34019step1 raw34019step1Labels := by
      have ha : raw34019step1 = -raw34019step0 := by apply Matrix.ext; change ∀ i j, raw34019step1 i j = -(raw34019step0 i j); unfold raw34019step1 raw34019step0; decide +kernel
      have hl : raw34019step1Labels = raw34019step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3069 node3069Labels := by rfl

theorem canonical34020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34020 raw34020Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw34020 raw34020Labels = mixedMoment B raw34020step0 raw34020step0Labels := by
      have ha : raw34020step0 = (fun i j => raw34020 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34020step0 raw34020; decide +kernel
      have hl : raw34020step0Labels = raw34020Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34020 raw34020Labels permutation212 permutation6
    mixedMoment B raw34020step0 raw34020step0Labels = mixedMoment B raw34020step1 raw34020step1Labels := by
      have ha : raw34020step1 = -raw34020step0 := by apply Matrix.ext; change ∀ i j, raw34020step1 i j = -(raw34020step0 i j); unfold raw34020step1 raw34020step0; decide +kernel
      have hl : raw34020step1Labels = raw34020step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3066 node3066Labels := by rfl

theorem canonical34021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34021 raw34021Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw34021 raw34021Labels = mixedMoment B raw34021step0 raw34021step0Labels := by
      have hz : ∀ j, raw34021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34021step0 = (fun i j => raw34021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34021step0 raw34021; decide +kernel
      have hl : raw34021step0Labels = raw34021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34021 raw34021Labels permutation434 hz
    mixedMoment B raw34021step0 raw34021step0Labels = mixedMoment B raw34021step1 raw34021step1Labels := by
      have ha : raw34021step1 = (fun i j => raw34021step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34021step1 raw34021step0; decide +kernel
      have hl : raw34021step1Labels = raw34021step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34021step0 raw34021step0Labels permutation44 permutation6
    mixedMoment B raw34021step1 raw34021step1Labels = mixedMoment B raw34021step2 raw34021step2Labels := by
      have ha : raw34021step2 = -raw34021step1 := by apply Matrix.ext; change ∀ i j, raw34021step2 i j = -(raw34021step1 i j); unfold raw34021step2 raw34021step1; decide +kernel
      have hl : raw34021step2Labels = raw34021step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3089 node3089Labels := by rfl

theorem canonical34022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34022 raw34022Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw34022 raw34022Labels = mixedMoment B raw34022step0 raw34022step0Labels := by
      have hz : ∀ j, raw34022 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34022step0 = (fun i j => raw34022 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34022step0 raw34022; decide +kernel
      have hl : raw34022step0Labels = raw34022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34022 raw34022Labels permutation520 hz
    mixedMoment B raw34022step0 raw34022step0Labels = mixedMoment B raw34022step1 raw34022step1Labels := by
      have ha : raw34022step1 = (fun i j => raw34022step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34022step1 raw34022step0; decide +kernel
      have hl : raw34022step1Labels = raw34022step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34022step0 raw34022step0Labels permutation44 permutation6
    mixedMoment B raw34022step1 raw34022step1Labels = mixedMoment B raw34022step2 raw34022step2Labels := by
      have ha : raw34022step2 = -raw34022step1 := by apply Matrix.ext; change ∀ i j, raw34022step2 i j = -(raw34022step1 i j); unfold raw34022step2 raw34022step1; decide +kernel
      have hl : raw34022step2Labels = raw34022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3089 node3089Labels := by rfl

theorem canonical34023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34023 raw34023Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw34023 raw34023Labels = mixedMoment B raw34023step0 raw34023step0Labels := by
      have ha : raw34023step0 = (fun i j => raw34023 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34023step0 raw34023; decide +kernel
      have hl : raw34023step0Labels = raw34023Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34023 raw34023Labels permutation212 permutation6
    mixedMoment B raw34023step0 raw34023step0Labels = mixedMoment B raw34023step1 raw34023step1Labels := by
      have ha : raw34023step1 = -raw34023step0 := by apply Matrix.ext; change ∀ i j, raw34023step1 i j = -(raw34023step0 i j); unfold raw34023step1 raw34023step0; decide +kernel
      have hl : raw34023step1Labels = raw34023step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3065 node3065Labels := by rfl

theorem canonical34024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34024 raw34024Labels = mixedMoment B node1414 node1414Labels := by
  calc
    mixedMoment B raw34024 raw34024Labels = mixedMoment B raw34024step0 raw34024step0Labels := by
      have hz : ∀ j, raw34024 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34024step0 = (fun i j => raw34024 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34024step0 raw34024; decide +kernel
      have hl : raw34024step0Labels = raw34024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34024 raw34024Labels permutation265 hz
    mixedMoment B raw34024step0 raw34024step0Labels = mixedMoment B raw34024step1 raw34024step1Labels := by
      have ha : raw34024step1 = (fun i j => raw34024step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34024step1 raw34024step0; decide +kernel
      have hl : raw34024step1Labels = raw34024step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34024step0 raw34024step0Labels permutation32 permutation3
    _ = mixedMoment B node1414 node1414Labels := by rfl

theorem canonical34025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34025 raw34025Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw34025 raw34025Labels = mixedMoment B raw34025step0 raw34025step0Labels := by
      have hz : ∀ j, raw34025 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34025step0 = (fun i j => raw34025 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34025step0 raw34025; decide +kernel
      have hl : raw34025step0Labels = raw34025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34025 raw34025Labels permutation265 hz
    mixedMoment B raw34025step0 raw34025step0Labels = mixedMoment B raw34025step1 raw34025step1Labels := by
      have ha : raw34025step1 = (fun i j => raw34025step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34025step1 raw34025step0; decide +kernel
      have hl : raw34025step1Labels = raw34025step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34025step0 raw34025step0Labels permutation32 permutation3
    _ = mixedMoment B node3185 node3185Labels := by rfl

theorem canonical34026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34026 raw34026Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw34026 raw34026Labels = mixedMoment B raw34026step0 raw34026step0Labels := by
      have hz : ∀ j, raw34026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34026step0 = (fun i j => raw34026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34026step0 raw34026; decide +kernel
      have hl : raw34026step0Labels = raw34026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34026 raw34026Labels permutation434 hz
    mixedMoment B raw34026step0 raw34026step0Labels = mixedMoment B raw34026step1 raw34026step1Labels := by
      have hz : ∀ j, raw34026step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34026step1 = (fun i j => raw34026step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34026step1 raw34026step0; decide +kernel
      have hl : raw34026step1Labels = raw34026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34026step0 raw34026step0Labels permutation56 hz
    mixedMoment B raw34026step1 raw34026step1Labels = mixedMoment B raw34026step2 raw34026step2Labels := by
      have ha : raw34026step2 = (fun i j => raw34026step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34026step2 raw34026step1; decide +kernel
      have hl : raw34026step2Labels = raw34026step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34026step1 raw34026step1Labels permutation8 permutation3
    _ = mixedMoment B node3230 node3230Labels := by rfl

theorem canonical34027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34027 raw34027Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw34027 raw34027Labels = mixedMoment B raw34027step0 raw34027step0Labels := by
      have hz : ∀ j, raw34027 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34027step0 = (fun i j => raw34027 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34027step0 raw34027; decide +kernel
      have hl : raw34027step0Labels = raw34027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34027 raw34027Labels permutation520 hz
    mixedMoment B raw34027step0 raw34027step0Labels = mixedMoment B raw34027step1 raw34027step1Labels := by
      have hz : ∀ j, raw34027step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34027step1 = (fun i j => raw34027step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34027step1 raw34027step0; decide +kernel
      have hl : raw34027step1Labels = raw34027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34027step0 raw34027step0Labels permutation56 hz
    mixedMoment B raw34027step1 raw34027step1Labels = mixedMoment B raw34027step2 raw34027step2Labels := by
      have ha : raw34027step2 = (fun i j => raw34027step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34027step2 raw34027step1; decide +kernel
      have hl : raw34027step2Labels = raw34027step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34027step1 raw34027step1Labels permutation8 permutation3
    _ = mixedMoment B node3230 node3230Labels := by rfl

theorem canonical34028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34028 raw34028Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw34028 raw34028Labels = mixedMoment B raw34028step0 raw34028step0Labels := by
      have hz : ∀ j, raw34028 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34028step0 = (fun i j => raw34028 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34028step0 raw34028; decide +kernel
      have hl : raw34028step0Labels = raw34028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34028 raw34028Labels permutation265 hz
    mixedMoment B raw34028step0 raw34028step0Labels = mixedMoment B raw34028step1 raw34028step1Labels := by
      have ha : raw34028step1 = (fun i j => raw34028step0 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34028step1 raw34028step0; decide +kernel
      have hl : raw34028step1Labels = raw34028step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34028step0 raw34028step0Labels permutation40 permutation6
    mixedMoment B raw34028step1 raw34028step1Labels = mixedMoment B raw34028step2 raw34028step2Labels := by
      have ha : raw34028step2 = -raw34028step1 := by apply Matrix.ext; change ∀ i j, raw34028step2 i j = -(raw34028step1 i j); unfold raw34028step2 raw34028step1; decide +kernel
      have hl : raw34028step2Labels = raw34028step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3227 node3227Labels := by rfl

theorem canonical34029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34029 raw34029Labels = mixedMoment B node1341 node1341Labels := by
  calc
    mixedMoment B raw34029 raw34029Labels = mixedMoment B raw34029step0 raw34029step0Labels := by
      have ha : raw34029step0 = (fun i j => raw34029 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34029step0 raw34029; decide +kernel
      have hl : raw34029step0Labels = raw34029Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34029 raw34029Labels permutation152 permutation3
    _ = mixedMoment B node1341 node1341Labels := by rfl

theorem canonical34030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34030 raw34030Labels = mixedMoment B node3140 node3140Labels := by
  calc
    mixedMoment B raw34030 raw34030Labels = mixedMoment B raw34030step0 raw34030step0Labels := by
      have ha : raw34030step0 = (fun i j => raw34030 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34030step0 raw34030; decide +kernel
      have hl : raw34030step0Labels = raw34030Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34030 raw34030Labels permutation152 permutation3
    _ = mixedMoment B node3140 node3140Labels := by rfl

theorem canonical34031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34031 raw34031Labels = mixedMoment B node3214 node3214Labels := by
  calc
    mixedMoment B raw34031 raw34031Labels = mixedMoment B raw34031step0 raw34031step0Labels := by
      have hz : ∀ j, raw34031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34031step0 = (fun i j => raw34031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34031step0 raw34031; decide +kernel
      have hl : raw34031step0Labels = raw34031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34031 raw34031Labels permutation434 hz
    mixedMoment B raw34031step0 raw34031step0Labels = mixedMoment B raw34031step1 raw34031step1Labels := by
      have ha : raw34031step1 = (fun i j => raw34031step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34031step1 raw34031step0; decide +kernel
      have hl : raw34031step1Labels = raw34031step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34031step0 raw34031step0Labels permutation32 permutation3
    _ = mixedMoment B node3214 node3214Labels := by rfl

theorem canonical34032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34032 raw34032Labels = mixedMoment B node3214 node3214Labels := by
  calc
    mixedMoment B raw34032 raw34032Labels = mixedMoment B raw34032step0 raw34032step0Labels := by
      have hz : ∀ j, raw34032 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34032step0 = (fun i j => raw34032 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34032step0 raw34032; decide +kernel
      have hl : raw34032step0Labels = raw34032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34032 raw34032Labels permutation520 hz
    mixedMoment B raw34032step0 raw34032step0Labels = mixedMoment B raw34032step1 raw34032step1Labels := by
      have ha : raw34032step1 = (fun i j => raw34032step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34032step1 raw34032step0; decide +kernel
      have hl : raw34032step1Labels = raw34032step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34032step0 raw34032step0Labels permutation32 permutation3
    _ = mixedMoment B node3214 node3214Labels := by rfl

theorem canonical34033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34033 raw34033Labels = mixedMoment B node3209 node3209Labels := by
  calc
    mixedMoment B raw34033 raw34033Labels = mixedMoment B raw34033step0 raw34033step0Labels := by
      have ha : raw34033step0 = (fun i j => raw34033 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34033step0 raw34033; decide +kernel
      have hl : raw34033step0Labels = raw34033Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34033 raw34033Labels permutation170 permutation3
    _ = mixedMoment B node3209 node3209Labels := by rfl

theorem canonical34034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34034 raw34034Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw34034 raw34034Labels = mixedMoment B raw34034step0 raw34034step0Labels := by
      have ha : raw34034step0 = (fun i j => raw34034 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34034step0 raw34034; decide +kernel
      have hl : raw34034step0Labels = raw34034Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34034 raw34034Labels permutation155 permutation3
    _ = mixedMoment B node1330 node1330Labels := by rfl

theorem canonical34035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34035 raw34035Labels = mixedMoment B node3134 node3134Labels := by
  calc
    mixedMoment B raw34035 raw34035Labels = mixedMoment B raw34035step0 raw34035step0Labels := by
      have ha : raw34035step0 = (fun i j => raw34035 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34035step0 raw34035; decide +kernel
      have hl : raw34035step0Labels = raw34035Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34035 raw34035Labels permutation155 permutation3
    _ = mixedMoment B node3134 node3134Labels := by rfl

theorem canonical34036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34036 raw34036Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw34036 raw34036Labels = mixedMoment B raw34036step0 raw34036step0Labels := by
      have ha : raw34036step0 = (fun i j => raw34036 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34036step0 raw34036; decide +kernel
      have hl : raw34036step0Labels = raw34036Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34036 raw34036Labels permutation179 permutation3
    _ = mixedMoment B node3163 node3163Labels := by rfl

theorem canonical34037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34037 raw34037Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw34037 raw34037Labels = mixedMoment B raw34037step0 raw34037step0Labels := by
      have hz : ∀ j, raw34037 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34037step0 = (fun i j => raw34037 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34037step0 raw34037; decide +kernel
      have hl : raw34037step0Labels = raw34037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34037 raw34037Labels permutation520 hz
    mixedMoment B raw34037step0 raw34037step0Labels = mixedMoment B raw34037step1 raw34037step1Labels := by
      have ha : raw34037step1 = (fun i j => raw34037step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34037step1 raw34037step0; decide +kernel
      have hl : raw34037step1Labels = raw34037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34037step0 raw34037step0Labels permutation33 permutation3
    _ = mixedMoment B node3206 node3206Labels := by rfl

theorem canonical34038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34038 raw34038Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw34038 raw34038Labels = mixedMoment B raw34038step0 raw34038step0Labels := by
      have ha : raw34038step0 = (fun i j => raw34038 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34038step0 raw34038; decide +kernel
      have hl : raw34038step0Labels = raw34038Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34038 raw34038Labels permutation157 permutation3
    _ = mixedMoment B node3202 node3202Labels := by rfl

theorem canonical34039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34039 raw34039Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw34039 raw34039Labels = mixedMoment B raw34039step0 raw34039step0Labels := by
      have ha : raw34039step0 = (fun i j => raw34039 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34039step0 raw34039; decide +kernel
      have hl : raw34039step0Labels = raw34039Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34039 raw34039Labels permutation153 permutation3
    _ = mixedMoment B node1330 node1330Labels := by rfl

theorem canonical34040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34040 raw34040Labels = mixedMoment B node3134 node3134Labels := by
  calc
    mixedMoment B raw34040 raw34040Labels = mixedMoment B raw34040step0 raw34040step0Labels := by
      have ha : raw34040step0 = (fun i j => raw34040 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34040step0 raw34040; decide +kernel
      have hl : raw34040step0Labels = raw34040Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34040 raw34040Labels permutation153 permutation3
    _ = mixedMoment B node3134 node3134Labels := by rfl

theorem canonical34041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34041 raw34041Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw34041 raw34041Labels = mixedMoment B raw34041step0 raw34041step0Labels := by
      have ha : raw34041step0 = (fun i j => raw34041 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34041step0 raw34041; decide +kernel
      have hl : raw34041step0Labels = raw34041Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34041 raw34041Labels permutation177 permutation3
    _ = mixedMoment B node3163 node3163Labels := by rfl

theorem canonical34042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34042 raw34042Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw34042 raw34042Labels = mixedMoment B raw34042step0 raw34042step0Labels := by
      have hz : ∀ j, raw34042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34042step0 = (fun i j => raw34042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34042step0 raw34042; decide +kernel
      have hl : raw34042step0Labels = raw34042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34042 raw34042Labels permutation434 hz
    mixedMoment B raw34042step0 raw34042step0Labels = mixedMoment B raw34042step1 raw34042step1Labels := by
      have ha : raw34042step1 = (fun i j => raw34042step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34042step1 raw34042step0; decide +kernel
      have hl : raw34042step1Labels = raw34042step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34042step0 raw34042step0Labels permutation33 permutation3
    _ = mixedMoment B node3206 node3206Labels := by rfl

theorem canonical34043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34043 raw34043Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw34043 raw34043Labels = mixedMoment B raw34043step0 raw34043step0Labels := by
      have ha : raw34043step0 = (fun i j => raw34043 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34043step0 raw34043; decide +kernel
      have hl : raw34043step0Labels = raw34043Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34043 raw34043Labels permutation156 permutation3
    _ = mixedMoment B node3202 node3202Labels := by rfl

theorem canonical34044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34044 raw34044Labels = mixedMoment B node1329 node1329Labels := by
  calc
    mixedMoment B raw34044 raw34044Labels = mixedMoment B raw34044step0 raw34044step0Labels := by
      have ha : raw34044step0 = (fun i j => raw34044 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34044step0 raw34044; decide +kernel
      have hl : raw34044step0Labels = raw34044Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34044 raw34044Labels permutation152 permutation3
    _ = mixedMoment B node1329 node1329Labels := by rfl

theorem canonical34045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34045 raw34045Labels = mixedMoment B node2890 node2890Labels := by
  calc
    mixedMoment B raw34045 raw34045Labels = mixedMoment B raw34045step0 raw34045step0Labels := by
      have ha : raw34045step0 = (fun i j => raw34045 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34045step0 raw34045; decide +kernel
      have hl : raw34045step0Labels = raw34045Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34045 raw34045Labels permutation664 permutation3
    mixedMoment B raw34045step0 raw34045step0Labels = mixedMoment B raw34045step1 raw34045step1Labels := by
      have ha : raw34045step1 = -raw34045step0 := by apply Matrix.ext; change ∀ i j, raw34045step1 i j = -(raw34045step0 i j); unfold raw34045step1 raw34045step0; decide +kernel
      have hl : raw34045step1Labels = raw34045step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2890 node2890Labels := by rfl

theorem canonical34046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34046 raw34046Labels = mixedMoment B node2895 node2895Labels := by
  calc
    mixedMoment B raw34046 raw34046Labels = mixedMoment B raw34046step0 raw34046step0Labels := by
      have ha : raw34046step0 = (fun i j => raw34046 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34046step0 raw34046; decide +kernel
      have hl : raw34046step0Labels = raw34046Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34046 raw34046Labels permutation662 permutation3
    mixedMoment B raw34046step0 raw34046step0Labels = mixedMoment B raw34046step1 raw34046step1Labels := by
      have ha : raw34046step1 = -raw34046step0 := by apply Matrix.ext; change ∀ i j, raw34046step1 i j = -(raw34046step0 i j); unfold raw34046step1 raw34046step0; decide +kernel
      have hl : raw34046step1Labels = raw34046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2895 node2895Labels := by rfl

theorem canonical34047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34047 raw34047Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw34047 raw34047Labels = mixedMoment B raw34047step0 raw34047step0Labels := by
      have hz : ∀ j, raw34047 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34047step0 = (fun i j => raw34047 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34047step0 raw34047; decide +kernel
      have hl : raw34047step0Labels = raw34047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34047 raw34047Labels permutation434 hz
    mixedMoment B raw34047step0 raw34047step0Labels = mixedMoment B raw34047step1 raw34047step1Labels := by
      have ha : raw34047step1 = (fun i j => raw34047step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34047step1 raw34047step0; decide +kernel
      have hl : raw34047step1Labels = raw34047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34047step0 raw34047step0Labels permutation151 permutation3
    mixedMoment B raw34047step1 raw34047step1Labels = mixedMoment B raw34047step2 raw34047step2Labels := by
      have ha : raw34047step2 = -raw34047step1 := by apply Matrix.ext; change ∀ i j, raw34047step2 i j = -(raw34047step1 i j); unfold raw34047step2 raw34047step1; decide +kernel
      have hl : raw34047step2Labels = raw34047step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2941 node2941Labels := by rfl

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

theorem canonical34048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34048 raw34048Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw34048 raw34048Labels = mixedMoment B raw34048step0 raw34048step0Labels := by
      have hz : ∀ j, raw34048 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34048step0 = (fun i j => raw34048 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34048step0 raw34048; decide +kernel
      have hl : raw34048step0Labels = raw34048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34048 raw34048Labels permutation520 hz
    mixedMoment B raw34048step0 raw34048step0Labels = mixedMoment B raw34048step1 raw34048step1Labels := by
      have ha : raw34048step1 = (fun i j => raw34048step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34048step1 raw34048step0; decide +kernel
      have hl : raw34048step1Labels = raw34048step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34048step0 raw34048step0Labels permutation151 permutation3
    mixedMoment B raw34048step1 raw34048step1Labels = mixedMoment B raw34048step2 raw34048step2Labels := by
      have ha : raw34048step2 = -raw34048step1 := by apply Matrix.ext; change ∀ i j, raw34048step2 i j = -(raw34048step1 i j); unfold raw34048step2 raw34048step1; decide +kernel
      have hl : raw34048step2Labels = raw34048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2941 node2941Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1329 node1329Labels = 0 := by
  exact mixedMoment_alpha B hF node1329 node1329Labels 2 permutation152
    (by decide +kernel)

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

theorem sound1329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1329 node1329Labels = Sparse.eval nodeValue1329 (mixedVector B) := by
  simpa only [nodeValue1329, Sparse.eval_nil] using zero1329 B _hB _hF

theorem sound1330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1330 node1330Labels = Sparse.eval nodeValue1330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1330) = mixedMoment B node1330 node1330Labels := rfl
  simpa [nodeValue1330, Sparse.eval] using hc.symm

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

theorem sound2890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2890 node2890Labels = Sparse.eval nodeValue2890 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2890) = mixedMoment B node2890 node2890Labels := rfl
  simpa [nodeValue2890, Sparse.eval] using hc.symm

theorem sound2895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2895 node2895Labels = Sparse.eval nodeValue2895 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2895) = mixedMoment B node2895 node2895Labels := rfl
  simpa [nodeValue2895, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3065 node3065Labels = 0 := by
  exact mixedMoment_alpha B hF node3065 node3065Labels 2 permutation152
    (by decide +kernel)

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

theorem sound3065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3065 node3065Labels = Sparse.eval nodeValue3065 (mixedVector B) := by
  simpa only [nodeValue3065, Sparse.eval_nil] using zero3065 B _hB _hF

theorem sound3066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3066 node3066Labels = Sparse.eval nodeValue3066 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3066) = mixedMoment B node3066 node3066Labels := rfl
  simpa [nodeValue3066, Sparse.eval] using hc.symm

theorem sound3069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3069 node3069Labels = Sparse.eval nodeValue3069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3069) = mixedMoment B node3069 node3069Labels := rfl
  simpa [nodeValue3069, Sparse.eval] using hc.symm

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

theorem sound3134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3134 node3134Labels = Sparse.eval nodeValue3134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3134) = mixedMoment B node3134 node3134Labels := rfl
  simpa [nodeValue3134, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3163 node3163Labels = Sparse.eval nodeValue3163 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3163) = mixedMoment B node3163 node3163Labels := rfl
  simpa [nodeValue3163, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3214 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3214 node3214Labels = 0 := by
  exact mixedMoment_order_one B hB node3214 node3214Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3230 node3230Labels = 0 := by
  exact mixedMoment_order_one B hB node3230 node3230Labels 2
    (by decide +kernel) (by decide +kernel)

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

theorem sound3202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3202 node3202Labels = Sparse.eval nodeValue3202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3202) = mixedMoment B node3202 node3202Labels := rfl
  simpa [nodeValue3202, Sparse.eval] using hc.symm

theorem sound3214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3214 node3214Labels = Sparse.eval nodeValue3214 (mixedVector B) := by
  simpa only [nodeValue3214, Sparse.eval_nil] using zero3214 B _hB _hF

theorem sound3230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3230 node3230Labels = Sparse.eval nodeValue3230 (mixedVector B) := by
  simpa only [nodeValue3230, Sparse.eval_nil] using zero3230 B _hB _hF

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

theorem sourceEq2473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2473 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2473 + difference 0 1) (sourceB2473 + difference 1 0) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3069) := by
    have ha : (tripleCharges (sourceA2473 + difference 0 1) (sourceB2473 + difference 1 0) sourceC2473) = raw34019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34019; decide +kernel
    rw [ha]
    exact (canonical34019 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2473 + difference 0 2) (sourceB2473 + difference 2 0) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA2473 + difference 0 2) (sourceB2473 + difference 2 0) sourceC2473) = raw34020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34020; decide +kernel
    rw [ha]
    exact (canonical34020 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2473 + difference 0 3) (sourceB2473 + difference 3 0) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA2473 + difference 0 3) (sourceB2473 + difference 3 0) sourceC2473) = raw34021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34021; decide +kernel
    rw [ha]
    exact (canonical34021 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2473 + difference 0 4) (sourceB2473 + difference 4 0) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA2473 + difference 0 4) (sourceB2473 + difference 4 0) sourceC2473) = raw34022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34022; decide +kernel
    rw [ha]
    exact (canonical34022 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2473 + difference 0 5) (sourceB2473 + difference 5 0) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA2473 + difference 0 5) (sourceB2473 + difference 5 0) sourceC2473) = raw34023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34023; decide +kernel
    rw [ha]
    exact (canonical34023 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2473 + difference 1 0) (sourceB2473 + difference 0 1) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA2473 + difference 1 0) (sourceB2473 + difference 0 1) sourceC2473) = raw34024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34024; decide +kernel
    rw [ha]
    exact (canonical34024 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2473 + difference 1 2) (sourceB2473 + difference 2 1) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA2473 + difference 1 2) (sourceB2473 + difference 2 1) sourceC2473) = raw34025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34025; decide +kernel
    rw [ha]
    exact (canonical34025 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2473 + difference 1 3) (sourceB2473 + difference 3 1) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA2473 + difference 1 3) (sourceB2473 + difference 3 1) sourceC2473) = raw34026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34026; decide +kernel
    rw [ha]
    exact (canonical34026 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2473 + difference 1 4) (sourceB2473 + difference 4 1) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA2473 + difference 1 4) (sourceB2473 + difference 4 1) sourceC2473) = raw34027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34027; decide +kernel
    rw [ha]
    exact (canonical34027 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2473 + difference 1 5) (sourceB2473 + difference 5 1) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA2473 + difference 1 5) (sourceB2473 + difference 5 1) sourceC2473) = raw34028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34028; decide +kernel
    rw [ha]
    exact (canonical34028 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2473 + difference 2 0) (sourceB2473 + difference 0 2) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1341) := by
    have ha : (tripleCharges (sourceA2473 + difference 2 0) (sourceB2473 + difference 0 2) sourceC2473) = raw34029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34029; decide +kernel
    rw [ha]
    exact (canonical34029 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2473 + difference 2 1) (sourceB2473 + difference 1 2) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3140) := by
    have ha : (tripleCharges (sourceA2473 + difference 2 1) (sourceB2473 + difference 1 2) sourceC2473) = raw34030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34030; decide +kernel
    rw [ha]
    exact (canonical34030 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2473 + difference 2 3) (sourceB2473 + difference 3 2) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3214) := by
    have ha : (tripleCharges (sourceA2473 + difference 2 3) (sourceB2473 + difference 3 2) sourceC2473) = raw34031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34031; decide +kernel
    rw [ha]
    exact (canonical34031 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2473 + difference 2 4) (sourceB2473 + difference 4 2) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3214) := by
    have ha : (tripleCharges (sourceA2473 + difference 2 4) (sourceB2473 + difference 4 2) sourceC2473) = raw34032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34032; decide +kernel
    rw [ha]
    exact (canonical34032 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2473 + difference 2 5) (sourceB2473 + difference 5 2) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3209) := by
    have ha : (tripleCharges (sourceA2473 + difference 2 5) (sourceB2473 + difference 5 2) sourceC2473) = raw34033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34033; decide +kernel
    rw [ha]
    exact (canonical34033 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2473 + difference 3 0) (sourceB2473 + difference 0 3) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA2473 + difference 3 0) (sourceB2473 + difference 0 3) sourceC2473) = raw34034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34034; decide +kernel
    rw [ha]
    exact (canonical34034 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2473 + difference 3 1) (sourceB2473 + difference 1 3) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3134) := by
    have ha : (tripleCharges (sourceA2473 + difference 3 1) (sourceB2473 + difference 1 3) sourceC2473) = raw34035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34035; decide +kernel
    rw [ha]
    exact (canonical34035 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2473 + difference 3 2) (sourceB2473 + difference 2 3) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3163) := by
    have ha : (tripleCharges (sourceA2473 + difference 3 2) (sourceB2473 + difference 2 3) sourceC2473) = raw34036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34036; decide +kernel
    rw [ha]
    exact (canonical34036 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2473 + difference 3 4) (sourceB2473 + difference 4 3) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2473 + difference 3 4) (sourceB2473 + difference 4 3) sourceC2473) = raw34037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34037; decide +kernel
    rw [ha]
    exact (canonical34037 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2473 + difference 3 5) (sourceB2473 + difference 5 3) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA2473 + difference 3 5) (sourceB2473 + difference 5 3) sourceC2473) = raw34038 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34038; decide +kernel
    rw [ha]
    exact (canonical34038 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2473 + difference 4 0) (sourceB2473 + difference 0 4) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA2473 + difference 4 0) (sourceB2473 + difference 0 4) sourceC2473) = raw34039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34039; decide +kernel
    rw [ha]
    exact (canonical34039 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2473 + difference 4 1) (sourceB2473 + difference 1 4) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3134) := by
    have ha : (tripleCharges (sourceA2473 + difference 4 1) (sourceB2473 + difference 1 4) sourceC2473) = raw34040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34040; decide +kernel
    rw [ha]
    exact (canonical34040 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2473 + difference 4 2) (sourceB2473 + difference 2 4) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3163) := by
    have ha : (tripleCharges (sourceA2473 + difference 4 2) (sourceB2473 + difference 2 4) sourceC2473) = raw34041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34041; decide +kernel
    rw [ha]
    exact (canonical34041 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2473 + difference 4 3) (sourceB2473 + difference 3 4) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2473 + difference 4 3) (sourceB2473 + difference 3 4) sourceC2473) = raw34042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34042; decide +kernel
    rw [ha]
    exact (canonical34042 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2473 + difference 4 5) (sourceB2473 + difference 5 4) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA2473 + difference 4 5) (sourceB2473 + difference 5 4) sourceC2473) = raw34043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34043; decide +kernel
    rw [ha]
    exact (canonical34043 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2473 + difference 5 0) (sourceB2473 + difference 0 5) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1329) := by
    have ha : (tripleCharges (sourceA2473 + difference 5 0) (sourceB2473 + difference 0 5) sourceC2473) = raw34044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34044; decide +kernel
    rw [ha]
    exact (canonical34044 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2473 + difference 5 1) (sourceB2473 + difference 1 5) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2890) := by
    have ha : (tripleCharges (sourceA2473 + difference 5 1) (sourceB2473 + difference 1 5) sourceC2473) = raw34045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34045; decide +kernel
    rw [ha]
    exact (canonical34045 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2473 + difference 5 2) (sourceB2473 + difference 2 5) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2895) := by
    have ha : (tripleCharges (sourceA2473 + difference 5 2) (sourceB2473 + difference 2 5) sourceC2473) = raw34046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34046; decide +kernel
    rw [ha]
    exact (canonical34046 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2473 + difference 5 3) (sourceB2473 + difference 3 5) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA2473 + difference 5 3) (sourceB2473 + difference 3 5) sourceC2473) = raw34047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34047; decide +kernel
    rw [ha]
    exact (canonical34047 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2473 + difference 5 4) (sourceB2473 + difference 4 5) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA2473 + difference 5 4) (sourceB2473 + difference 4 5) sourceC2473) = raw34048 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34048; decide +kernel
    rw [ha]
    exact (canonical34048 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2473 sourceB2473 sourceC2473
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2473, Integer.Sparse.eval]
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

theorem reindexCheck1991 : Integer.Sparse.reindex keyMap MixedData.row1991 = numericRow1991 := by decide +kernel

theorem numericCheck1991 (x : Master → ℝ) : Integer.Sparse.eval numericRow1991 x =
    (4320 : ℝ) * reducedSource1991 x := by
  norm_num [numericRow1991, reducedSource1991, Integer.Sparse.eval, Sparse.eval, nodeValue1329, nodeValue1330, nodeValue1341, nodeValue1414, nodeValue2890, nodeValue2895, nodeValue2941, nodeValue3065, nodeValue3066, nodeValue3069, nodeValue3089, nodeValue3134, nodeValue3140, nodeValue3163, nodeValue3185, nodeValue3202, nodeValue3206, nodeValue3209, nodeValue3214, nodeValue3227, nodeValue3230]
  ring

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

theorem reducedZero1991 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1991 (mixedVector B) = 0 := by
  have h1329 : mixedVector B (Sum.inr 1329) = Sparse.eval nodeValue1329 (mixedVector B) := by
    change mixedMoment B node1329 node1329Labels = _
    exact sound1329 B hB hF
  have h1330 : mixedVector B (Sum.inr 1330) = Sparse.eval nodeValue1330 (mixedVector B) := by
    change mixedMoment B node1330 node1330Labels = _
    exact sound1330 B hB hF
  have h1341 : mixedVector B (Sum.inr 1341) = Sparse.eval nodeValue1341 (mixedVector B) := by
    change mixedMoment B node1341 node1341Labels = _
    exact sound1341_e B hB hF
  have h1414 : mixedVector B (Sum.inr 1414) = Sparse.eval nodeValue1414 (mixedVector B) := by
    change mixedMoment B node1414 node1414Labels = _
    exact sound1414_e B hB hF
  have h2890 : mixedVector B (Sum.inr 2890) = Sparse.eval nodeValue2890 (mixedVector B) := by
    change mixedMoment B node2890 node2890Labels = _
    exact sound2890 B hB hF
  have h2895 : mixedVector B (Sum.inr 2895) = Sparse.eval nodeValue2895 (mixedVector B) := by
    change mixedMoment B node2895 node2895Labels = _
    exact sound2895 B hB hF
  have h2941 : mixedVector B (Sum.inr 2941) = Sparse.eval nodeValue2941 (mixedVector B) := by
    change mixedMoment B node2941 node2941Labels = _
    exact sound2941_e B hB hF
  have h3065 : mixedVector B (Sum.inr 3065) = Sparse.eval nodeValue3065 (mixedVector B) := by
    change mixedMoment B node3065 node3065Labels = _
    exact sound3065 B hB hF
  have h3066 : mixedVector B (Sum.inr 3066) = Sparse.eval nodeValue3066 (mixedVector B) := by
    change mixedMoment B node3066 node3066Labels = _
    exact sound3066 B hB hF
  have h3069 : mixedVector B (Sum.inr 3069) = Sparse.eval nodeValue3069 (mixedVector B) := by
    change mixedMoment B node3069 node3069Labels = _
    exact sound3069 B hB hF
  have h3089 : mixedVector B (Sum.inr 3089) = Sparse.eval nodeValue3089 (mixedVector B) := by
    change mixedMoment B node3089 node3089Labels = _
    exact sound3089_e B hB hF
  have h3134 : mixedVector B (Sum.inr 3134) = Sparse.eval nodeValue3134 (mixedVector B) := by
    change mixedMoment B node3134 node3134Labels = _
    exact sound3134 B hB hF
  have h3140 : mixedVector B (Sum.inr 3140) = Sparse.eval nodeValue3140 (mixedVector B) := by
    change mixedMoment B node3140 node3140Labels = _
    exact sound3140_e B hB hF
  have h3163 : mixedVector B (Sum.inr 3163) = Sparse.eval nodeValue3163 (mixedVector B) := by
    change mixedMoment B node3163 node3163Labels = _
    exact sound3163 B hB hF
  have h3185 : mixedVector B (Sum.inr 3185) = Sparse.eval nodeValue3185 (mixedVector B) := by
    change mixedMoment B node3185 node3185Labels = _
    exact sound3185_e B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3206 : mixedVector B (Sum.inr 3206) = Sparse.eval nodeValue3206 (mixedVector B) := by
    change mixedMoment B node3206 node3206Labels = _
    exact sound3206_e B hB hF
  have h3209 : mixedVector B (Sum.inr 3209) = Sparse.eval nodeValue3209 (mixedVector B) := by
    change mixedMoment B node3209 node3209Labels = _
    exact sound3209_e B hB hF
  have h3214 : mixedVector B (Sum.inr 3214) = Sparse.eval nodeValue3214 (mixedVector B) := by
    change mixedMoment B node3214 node3214Labels = _
    exact sound3214 B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227_e B hB hF
  have h3230 : mixedVector B (Sum.inr 3230) = Sparse.eval nodeValue3230 (mixedVector B) := by
    change mixedMoment B node3230 node3230Labels = _
    exact sound3230 B hB hF
  simpa only [sourceForm2473, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1329, h1330, h1341, h1414, h2890, h2895, h2941, h3065, h3066, h3069, h3089, h3134, h3140, h3163, h3185, h3202, h3206, h3209, h3214, h3227, h3230, reducedSource1991] using sourceEq2473 B hB

theorem rowSound1991_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1991 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1991, numericCheck1991, reducedZero1991 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991_e_oai
