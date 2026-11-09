-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:34:05.834554+00:00
-- url     : https://prove2.me/submissions/fdf6d908-3924-452e-be0f-f0a5ae99da1e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1684_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1686_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1687_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19488 raw19488Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw19488 raw19488Labels = mixedMoment B raw19488step0 raw19488step0Labels := by
      have hz : ∀ j, raw19488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19488step0 = (fun i j => raw19488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19488step0 raw19488; decide +kernel
      have hl : raw19488step0Labels = raw19488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19488 raw19488Labels permutation434 hz
    mixedMoment B raw19488step0 raw19488step0Labels = mixedMoment B raw19488step1 raw19488step1Labels := by
      have hz : ∀ j, raw19488step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19488step1 = (fun i j => raw19488step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19488step1 raw19488step0; decide +kernel
      have hl : raw19488step1Labels = raw19488step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19488step0 raw19488step0Labels permutation80 hz
    mixedMoment B raw19488step1 raw19488step1Labels = mixedMoment B raw19488step2 raw19488step2Labels := by
      have ha : raw19488step2 = (fun i j => raw19488step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19488step2 raw19488step1; decide +kernel
      have hl : raw19488step2Labels = raw19488step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19488step1 raw19488step1Labels permutation28 permutation0
    mixedMoment B raw19488step2 raw19488step2Labels = mixedMoment B raw19488step3 raw19488step3Labels := by
      have ha : raw19488step3 = -raw19488step2 := by apply Matrix.ext; change ∀ i j, raw19488step3 i j = -(raw19488step2 i j); unfold raw19488step3 raw19488step2; decide +kernel
      have hl : raw19488step3Labels = raw19488step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical19499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19499 raw19499Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw19499 raw19499Labels = mixedMoment B raw19499step0 raw19499step0Labels := by
      have hz : ∀ j, raw19499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19499step0 = (fun i j => raw19499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19499step0 raw19499; decide +kernel
      have hl : raw19499step0Labels = raw19499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19499 raw19499Labels permutation346 hz
    mixedMoment B raw19499step0 raw19499step0Labels = mixedMoment B raw19499step1 raw19499step1Labels := by
      have ha : raw19499step1 = (fun i j => raw19499step0 (permutation137 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19499step1 raw19499step0; decide +kernel
      have hl : raw19499step1Labels = raw19499step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19499step0 raw19499step0Labels permutation137 permutation0
    mixedMoment B raw19499step1 raw19499step1Labels = mixedMoment B raw19499step2 raw19499step2Labels := by
      have ha : raw19499step2 = -raw19499step1 := by apply Matrix.ext; change ∀ i j, raw19499step2 i j = -(raw19499step1 i j); unfold raw19499step2 raw19499step1; decide +kernel
      have hl : raw19499step2Labels = raw19499step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20238 raw20238Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw20238 raw20238Labels = mixedMoment B raw20238step0 raw20238step0Labels := by
      have ha : raw20238step0 = (fun i j => raw20238 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20238step0 raw20238; decide +kernel
      have hl : raw20238step0Labels = raw20238Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20238 raw20238Labels permutation682 permutation2
    mixedMoment B raw20238step0 raw20238step0Labels = mixedMoment B raw20238step1 raw20238step1Labels := by
      have ha : raw20238step1 = -raw20238step0 := by apply Matrix.ext; change ∀ i j, raw20238step1 i j = -(raw20238step0 i j); unfold raw20238step1 raw20238step0; decide +kernel
      have hl : raw20238step1Labels = raw20238step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1898 node1898Labels := by rfl

theorem canonical20243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20243 raw20243Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw20243 raw20243Labels = mixedMoment B raw20243step0 raw20243step0Labels := by
      have ha : raw20243step0 = (fun i j => raw20243 (permutation665 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20243step0 raw20243; decide +kernel
      have hl : raw20243step0Labels = raw20243Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20243 raw20243Labels permutation665 permutation0
    mixedMoment B raw20243step0 raw20243step0Labels = mixedMoment B raw20243step1 raw20243step1Labels := by
      have ha : raw20243step1 = -raw20243step0 := by apply Matrix.ext; change ∀ i j, raw20243step1 i j = -(raw20243step0 i j); unfold raw20243step1 raw20243step0; decide +kernel
      have hl : raw20243step1Labels = raw20243step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4079 node4079Labels := by rfl

theorem canonical20273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20273 raw20273Labels = mixedMoment B node2130 node2130Labels := by
  calc
    mixedMoment B raw20273 raw20273Labels = mixedMoment B raw20273step0 raw20273step0Labels := by
      have hz : ∀ j, raw20273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20273step0 = (fun i j => raw20273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20273step0 raw20273; decide +kernel
      have hl : raw20273step0Labels = raw20273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20273 raw20273Labels permutation434 hz
    mixedMoment B raw20273step0 raw20273step0Labels = mixedMoment B raw20273step1 raw20273step1Labels := by
      have hz : ∀ j, raw20273step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20273step1 = (fun i j => raw20273step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20273step1 raw20273step0; decide +kernel
      have hl : raw20273step1Labels = raw20273step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20273step0 raw20273step0Labels permutation80 hz
    mixedMoment B raw20273step1 raw20273step1Labels = mixedMoment B raw20273step2 raw20273step2Labels := by
      have ha : raw20273step2 = (fun i j => raw20273step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20273step2 raw20273step1; decide +kernel
      have hl : raw20273step2Labels = raw20273step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20273step1 raw20273step1Labels permutation31 permutation2
    mixedMoment B raw20273step2 raw20273step2Labels = mixedMoment B raw20273step3 raw20273step3Labels := by
      have ha : raw20273step3 = -raw20273step2 := by apply Matrix.ext; change ∀ i j, raw20273step3 i j = -(raw20273step2 i j); unfold raw20273step3 raw20273step2; decide +kernel
      have hl : raw20273step3Labels = raw20273step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2130 node2130Labels := by rfl

theorem canonical20311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20311 raw20311Labels = mixedMoment B node2087 node2087Labels := by
  calc
    mixedMoment B raw20311 raw20311Labels = mixedMoment B raw20311step0 raw20311step0Labels := by
      have hz : ∀ j, raw20311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20311step0 = (fun i j => raw20311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20311step0 raw20311; decide +kernel
      have hl : raw20311step0Labels = raw20311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20311 raw20311Labels permutation346 hz
    mixedMoment B raw20311step0 raw20311step0Labels = mixedMoment B raw20311step1 raw20311step1Labels := by
      have ha : raw20311step1 = (fun i j => raw20311step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20311step1 raw20311step0; decide +kernel
      have hl : raw20311step1Labels = raw20311step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20311step0 raw20311step0Labels permutation151 permutation2
    mixedMoment B raw20311step1 raw20311step1Labels = mixedMoment B raw20311step2 raw20311step2Labels := by
      have ha : raw20311step2 = -raw20311step1 := by apply Matrix.ext; change ∀ i j, raw20311step2 i j = -(raw20311step1 i j); unfold raw20311step2 raw20311step1; decide +kernel
      have hl : raw20311step2Labels = raw20311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2087 node2087Labels := by rfl

theorem canonical20316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20316 raw20316Labels = mixedMoment B node2492 node2492Labels := by
  calc
    mixedMoment B raw20316 raw20316Labels = mixedMoment B raw20316step0 raw20316step0Labels := by
      have hz : ∀ j, raw20316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20316step0 = (fun i j => raw20316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20316step0 raw20316; decide +kernel
      have hl : raw20316step0Labels = raw20316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20316 raw20316Labels permutation346 hz
    mixedMoment B raw20316step0 raw20316step0Labels = mixedMoment B raw20316step1 raw20316step1Labels := by
      have ha : raw20316step1 = (fun i j => raw20316step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20316step1 raw20316step0; decide +kernel
      have hl : raw20316step1Labels = raw20316step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20316step0 raw20316step0Labels permutation151 permutation2
    mixedMoment B raw20316step1 raw20316step1Labels = mixedMoment B raw20316step2 raw20316step2Labels := by
      have ha : raw20316step2 = -raw20316step1 := by apply Matrix.ext; change ∀ i j, raw20316step2 i j = -(raw20316step1 i j); unfold raw20316step2 raw20316step1; decide +kernel
      have hl : raw20316step2Labels = raw20316step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2492 node2492Labels := by rfl

theorem canonical20320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20320 raw20320Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw20320 raw20320Labels = mixedMoment B raw20320step0 raw20320step0Labels := by
      have hz : ∀ j, raw20320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20320step0 = (fun i j => raw20320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20320step0 raw20320; decide +kernel
      have hl : raw20320step0Labels = raw20320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20320 raw20320Labels permutation346 hz
    mixedMoment B raw20320step0 raw20320step0Labels = mixedMoment B raw20320step1 raw20320step1Labels := by
      have ha : raw20320step1 = (fun i j => raw20320step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20320step1 raw20320step0; decide +kernel
      have hl : raw20320step1Labels = raw20320step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20320step0 raw20320step0Labels permutation38 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical20321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20321 raw20321Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw20321 raw20321Labels = mixedMoment B raw20321step0 raw20321step0Labels := by
      have hz : ∀ j, raw20321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20321step0 = (fun i j => raw20321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20321step0 raw20321; decide +kernel
      have hl : raw20321step0Labels = raw20321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20321 raw20321Labels permutation346 hz
    mixedMoment B raw20321step0 raw20321step0Labels = mixedMoment B raw20321step1 raw20321step1Labels := by
      have ha : raw20321step1 = (fun i j => raw20321step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20321step1 raw20321step0; decide +kernel
      have hl : raw20321step1Labels = raw20321step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20321step0 raw20321step0Labels permutation38 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical20327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20327 raw20327Labels = mixedMoment B node2032 node2032Labels := by
  calc
    mixedMoment B raw20327 raw20327Labels = mixedMoment B raw20327step0 raw20327step0Labels := by
      have hz : ∀ j, raw20327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20327step0 = (fun i j => raw20327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20327step0 raw20327; decide +kernel
      have hl : raw20327step0Labels = raw20327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20327 raw20327Labels permutation346 hz
    mixedMoment B raw20327step0 raw20327step0Labels = mixedMoment B raw20327step1 raw20327step1Labels := by
      have ha : raw20327step1 = (fun i j => raw20327step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20327step1 raw20327step0; decide +kernel
      have hl : raw20327step1Labels = raw20327step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20327step0 raw20327step0Labels permutation151 permutation2
    mixedMoment B raw20327step1 raw20327step1Labels = mixedMoment B raw20327step2 raw20327step2Labels := by
      have ha : raw20327step2 = -raw20327step1 := by apply Matrix.ext; change ∀ i j, raw20327step2 i j = -(raw20327step1 i j); unfold raw20327step2 raw20327step1; decide +kernel
      have hl : raw20327step2Labels = raw20327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2032 node2032Labels := by rfl

theorem canonical20332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20332 raw20332Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw20332 raw20332Labels = mixedMoment B raw20332step0 raw20332step0Labels := by
      have hz : ∀ j, raw20332 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20332step0 = (fun i j => raw20332 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20332step0 raw20332; decide +kernel
      have hl : raw20332step0Labels = raw20332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20332 raw20332Labels permutation520 hz
    mixedMoment B raw20332step0 raw20332step0Labels = mixedMoment B raw20332step1 raw20332step1Labels := by
      have hz : ∀ j, raw20332step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20332step1 = (fun i j => raw20332step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20332step1 raw20332step0; decide +kernel
      have hl : raw20332step1Labels = raw20332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20332step0 raw20332step0Labels permutation80 hz
    mixedMoment B raw20332step1 raw20332step1Labels = mixedMoment B raw20332step2 raw20332step2Labels := by
      have ha : raw20332step2 = (fun i j => raw20332step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20332step2 raw20332step1; decide +kernel
      have hl : raw20332step2Labels = raw20332step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20332step1 raw20332step1Labels permutation28 permutation0
    mixedMoment B raw20332step2 raw20332step2Labels = mixedMoment B raw20332step3 raw20332step3Labels := by
      have ha : raw20332step3 = -raw20332step2 := by apply Matrix.ext; change ∀ i j, raw20332step3 i j = -(raw20332step2 i j); unfold raw20332step3 raw20332step2; decide +kernel
      have hl : raw20332step3Labels = raw20332step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical20334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20334 raw20334Labels = mixedMoment B node2469 node2469Labels := by
  calc
    mixedMoment B raw20334 raw20334Labels = mixedMoment B raw20334step0 raw20334step0Labels := by
      have ha : raw20334step0 = (fun i j => raw20334 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20334step0 raw20334; decide +kernel
      have hl : raw20334step0Labels = raw20334Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20334 raw20334Labels permutation682 permutation2
    mixedMoment B raw20334step0 raw20334step0Labels = mixedMoment B raw20334step1 raw20334step1Labels := by
      have ha : raw20334step1 = -raw20334step0 := by apply Matrix.ext; change ∀ i j, raw20334step1 i j = -(raw20334step0 i j); unfold raw20334step1 raw20334step0; decide +kernel
      have hl : raw20334step1Labels = raw20334step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2469 node2469Labels := by rfl

theorem canonical20338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20338 raw20338Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw20338 raw20338Labels = mixedMoment B raw20338step0 raw20338step0Labels := by
      have ha : raw20338step0 = (fun i j => raw20338 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20338step0 raw20338; decide +kernel
      have hl : raw20338step0Labels = raw20338Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20338 raw20338Labels permutation182 permutation2
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical20339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20339 raw20339Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw20339 raw20339Labels = mixedMoment B raw20339step0 raw20339step0Labels := by
      have ha : raw20339step0 = (fun i j => raw20339 (permutation182 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20339step0 raw20339; decide +kernel
      have hl : raw20339step0Labels = raw20339Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20339 raw20339Labels permutation182 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

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

theorem canonical28168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28168 raw28168Labels = mixedMoment B node2393 node2393Labels := by
  calc
    mixedMoment B raw28168 raw28168Labels = mixedMoment B raw28168step0 raw28168step0Labels := by
      have hz : ∀ j, raw28168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28168step0 = (fun i j => raw28168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28168step0 raw28168; decide +kernel
      have hl : raw28168step0Labels = raw28168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28168 raw28168Labels permutation346 hz
    mixedMoment B raw28168step0 raw28168step0Labels = mixedMoment B raw28168step1 raw28168step1Labels := by
      have ha : raw28168step1 = (fun i j => raw28168step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28168step1 raw28168step0; decide +kernel
      have hl : raw28168step1Labels = raw28168step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28168step0 raw28168step0Labels permutation151 permutation2
    mixedMoment B raw28168step1 raw28168step1Labels = mixedMoment B raw28168step2 raw28168step2Labels := by
      have ha : raw28168step2 = -raw28168step1 := by apply Matrix.ext; change ∀ i j, raw28168step2 i j = -(raw28168step1 i j); unfold raw28168step2 raw28168step1; decide +kernel
      have hl : raw28168step2Labels = raw28168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2393 node2393Labels := by rfl

theorem canonical28169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28169 raw28169Labels = mixedMoment B node2395 node2395Labels := by
  calc
    mixedMoment B raw28169 raw28169Labels = mixedMoment B raw28169step0 raw28169step0Labels := by
      have hz : ∀ j, raw28169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28169step0 = (fun i j => raw28169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28169step0 raw28169; decide +kernel
      have hl : raw28169step0Labels = raw28169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28169 raw28169Labels permutation346 hz
    mixedMoment B raw28169step0 raw28169step0Labels = mixedMoment B raw28169step1 raw28169step1Labels := by
      have ha : raw28169step1 = (fun i j => raw28169step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28169step1 raw28169step0; decide +kernel
      have hl : raw28169step1Labels = raw28169step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28169step0 raw28169step0Labels permutation150 permutation2
    mixedMoment B raw28169step1 raw28169step1Labels = mixedMoment B raw28169step2 raw28169step2Labels := by
      have ha : raw28169step2 = -raw28169step1 := by apply Matrix.ext; change ∀ i j, raw28169step2 i j = -(raw28169step1 i j); unfold raw28169step2 raw28169step1; decide +kernel
      have hl : raw28169step2Labels = raw28169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2395 node2395Labels := by rfl

theorem canonical28170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28170 raw28170Labels = mixedMoment B node2390 node2390Labels := by
  calc
    mixedMoment B raw28170 raw28170Labels = mixedMoment B raw28170step0 raw28170step0Labels := by
      have ha : raw28170step0 = (fun i j => raw28170 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28170step0 raw28170; decide +kernel
      have hl : raw28170step0Labels = raw28170Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28170 raw28170Labels permutation688 permutation2
    mixedMoment B raw28170step0 raw28170step0Labels = mixedMoment B raw28170step1 raw28170step1Labels := by
      have ha : raw28170step1 = -raw28170step0 := by apply Matrix.ext; change ∀ i j, raw28170step1 i j = -(raw28170step0 i j); unfold raw28170step1 raw28170step0; decide +kernel
      have hl : raw28170step1Labels = raw28170step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2390 node2390Labels := by rfl

theorem canonical28171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28171 raw28171Labels = mixedMoment B node2404 node2404Labels := by
  calc
    mixedMoment B raw28171 raw28171Labels = mixedMoment B raw28171step0 raw28171step0Labels := by
      have hz : ∀ j, raw28171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28171step0 = (fun i j => raw28171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28171step0 raw28171; decide +kernel
      have hl : raw28171step0Labels = raw28171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28171 raw28171Labels permutation346 hz
    mixedMoment B raw28171step0 raw28171step0Labels = mixedMoment B raw28171step1 raw28171step1Labels := by
      have ha : raw28171step1 = (fun i j => raw28171step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28171step1 raw28171step0; decide +kernel
      have hl : raw28171step1Labels = raw28171step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28171step0 raw28171step0Labels permutation149 permutation2
    mixedMoment B raw28171step1 raw28171step1Labels = mixedMoment B raw28171step2 raw28171step2Labels := by
      have ha : raw28171step2 = -raw28171step1 := by apply Matrix.ext; change ∀ i j, raw28171step2 i j = -(raw28171step1 i j); unfold raw28171step2 raw28171step1; decide +kernel
      have hl : raw28171step2Labels = raw28171step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2404 node2404Labels := by rfl

theorem canonical28172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28172 raw28172Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw28172 raw28172Labels = mixedMoment B raw28172step0 raw28172step0Labels := by
      have hz : ∀ j, raw28172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28172step0 = (fun i j => raw28172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28172step0 raw28172; decide +kernel
      have hl : raw28172step0Labels = raw28172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28172 raw28172Labels permutation346 hz
    mixedMoment B raw28172step0 raw28172step0Labels = mixedMoment B raw28172step1 raw28172step1Labels := by
      have ha : raw28172step1 = (fun i j => raw28172step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28172step1 raw28172step0; decide +kernel
      have hl : raw28172step1Labels = raw28172step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28172step0 raw28172step0Labels permutation151 permutation2
    mixedMoment B raw28172step1 raw28172step1Labels = mixedMoment B raw28172step2 raw28172step2Labels := by
      have ha : raw28172step2 = -raw28172step1 := by apply Matrix.ext; change ∀ i j, raw28172step2 i j = -(raw28172step1 i j); unfold raw28172step2 raw28172step1; decide +kernel
      have hl : raw28172step2Labels = raw28172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2678 node2678Labels := by rfl

theorem canonical28173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28173 raw28173Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw28173 raw28173Labels = mixedMoment B raw28173step0 raw28173step0Labels := by
      have hz : ∀ j, raw28173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28173step0 = (fun i j => raw28173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28173step0 raw28173; decide +kernel
      have hl : raw28173step0Labels = raw28173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28173 raw28173Labels permutation346 hz
    mixedMoment B raw28173step0 raw28173step0Labels = mixedMoment B raw28173step1 raw28173step1Labels := by
      have ha : raw28173step1 = (fun i j => raw28173step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28173step1 raw28173step0; decide +kernel
      have hl : raw28173step1Labels = raw28173step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28173step0 raw28173step0Labels permutation151 permutation2
    mixedMoment B raw28173step1 raw28173step1Labels = mixedMoment B raw28173step2 raw28173step2Labels := by
      have ha : raw28173step2 = -raw28173step1 := by apply Matrix.ext; change ∀ i j, raw28173step2 i j = -(raw28173step1 i j); unfold raw28173step2 raw28173step1; decide +kernel
      have hl : raw28173step2Labels = raw28173step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3771 node3771Labels := by rfl

theorem canonical28174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28174 raw28174Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw28174 raw28174Labels = mixedMoment B raw28174step0 raw28174step0Labels := by
      have hz : ∀ j, raw28174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28174step0 = (fun i j => raw28174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28174step0 raw28174; decide +kernel
      have hl : raw28174step0Labels = raw28174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28174 raw28174Labels permutation346 hz
    mixedMoment B raw28174step0 raw28174step0Labels = mixedMoment B raw28174step1 raw28174step1Labels := by
      have ha : raw28174step1 = (fun i j => raw28174step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28174step1 raw28174step0; decide +kernel
      have hl : raw28174step1Labels = raw28174step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28174step0 raw28174step0Labels permutation122 permutation0
    mixedMoment B raw28174step1 raw28174step1Labels = mixedMoment B raw28174step2 raw28174step2Labels := by
      have ha : raw28174step2 = -raw28174step1 := by apply Matrix.ext; change ∀ i j, raw28174step2 i j = -(raw28174step1 i j); unfold raw28174step2 raw28174step1; decide +kernel
      have hl : raw28174step2Labels = raw28174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical28198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28198 raw28198Labels = mixedMoment B node1901 node1901Labels := by
  calc
    mixedMoment B raw28198 raw28198Labels = mixedMoment B raw28198step0 raw28198step0Labels := by
      have ha : raw28198step0 = (fun i j => raw28198 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28198step0 raw28198; decide +kernel
      have hl : raw28198step0Labels = raw28198Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28198 raw28198Labels permutation681 permutation2
    mixedMoment B raw28198step0 raw28198step0Labels = mixedMoment B raw28198step1 raw28198step1Labels := by
      have ha : raw28198step1 = -raw28198step0 := by apply Matrix.ext; change ∀ i j, raw28198step1 i j = -(raw28198step0 i j); unfold raw28198step1 raw28198step0; decide +kernel
      have hl : raw28198step1Labels = raw28198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1901 node1901Labels := by rfl

theorem canonical28199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28199 raw28199Labels = mixedMoment B node1912 node1912Labels := by
  calc
    mixedMoment B raw28199 raw28199Labels = mixedMoment B raw28199step0 raw28199step0Labels := by
      have ha : raw28199step0 = (fun i j => raw28199 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28199step0 raw28199; decide +kernel
      have hl : raw28199step0Labels = raw28199Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28199 raw28199Labels permutation686 permutation2
    mixedMoment B raw28199step0 raw28199step0Labels = mixedMoment B raw28199step1 raw28199step1Labels := by
      have ha : raw28199step1 = -raw28199step0 := by apply Matrix.ext; change ∀ i j, raw28199step1 i j = -(raw28199step0 i j); unfold raw28199step1 raw28199step0; decide +kernel
      have hl : raw28199step1Labels = raw28199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1912 node1912Labels := by rfl

theorem canonical28200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28200 raw28200Labels = mixedMoment B node1912 node1912Labels := by
  calc
    mixedMoment B raw28200 raw28200Labels = mixedMoment B raw28200step0 raw28200step0Labels := by
      have ha : raw28200step0 = (fun i j => raw28200 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28200step0 raw28200; decide +kernel
      have hl : raw28200step0Labels = raw28200Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28200 raw28200Labels permutation680 permutation2
    mixedMoment B raw28200step0 raw28200step0Labels = mixedMoment B raw28200step1 raw28200step1Labels := by
      have ha : raw28200step1 = -raw28200step0 := by apply Matrix.ext; change ∀ i j, raw28200step1 i j = -(raw28200step0 i j); unfold raw28200step1 raw28200step0; decide +kernel
      have hl : raw28200step1Labels = raw28200step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1912 node1912Labels := by rfl

theorem canonical28201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28201 raw28201Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw28201 raw28201Labels = mixedMoment B raw28201step0 raw28201step0Labels := by
      have ha : raw28201step0 = (fun i j => raw28201 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28201step0 raw28201; decide +kernel
      have hl : raw28201step0Labels = raw28201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28201 raw28201Labels permutation682 permutation2
    mixedMoment B raw28201step0 raw28201step0Labels = mixedMoment B raw28201step1 raw28201step1Labels := by
      have ha : raw28201step1 = -raw28201step0 := by apply Matrix.ext; change ∀ i j, raw28201step1 i j = -(raw28201step0 i j); unfold raw28201step1 raw28201step0; decide +kernel
      have hl : raw28201step1Labels = raw28201step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical28202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28202 raw28202Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw28202 raw28202Labels = mixedMoment B raw28202step0 raw28202step0Labels := by
      have ha : raw28202step0 = (fun i j => raw28202 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28202step0 raw28202; decide +kernel
      have hl : raw28202step0Labels = raw28202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28202 raw28202Labels permutation682 permutation2
    mixedMoment B raw28202step0 raw28202step0Labels = mixedMoment B raw28202step1 raw28202step1Labels := by
      have ha : raw28202step1 = -raw28202step0 := by apply Matrix.ext; change ∀ i j, raw28202step1 i j = -(raw28202step0 i j); unfold raw28202step1 raw28202step0; decide +kernel
      have hl : raw28202step1Labels = raw28202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3460 node3460Labels := by rfl

theorem canonical28212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28212 raw28212Labels = mixedMoment B node2080 node2080Labels := by
  calc
    mixedMoment B raw28212 raw28212Labels = mixedMoment B raw28212step0 raw28212step0Labels := by
      have hz : ∀ j, raw28212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28212step0 = (fun i j => raw28212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28212step0 raw28212; decide +kernel
      have hl : raw28212step0Labels = raw28212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28212 raw28212Labels permutation434 hz
    mixedMoment B raw28212step0 raw28212step0Labels = mixedMoment B raw28212step1 raw28212step1Labels := by
      have ha : raw28212step1 = (fun i j => raw28212step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28212step1 raw28212step0; decide +kernel
      have hl : raw28212step1Labels = raw28212step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28212step0 raw28212step0Labels permutation151 permutation2
    mixedMoment B raw28212step1 raw28212step1Labels = mixedMoment B raw28212step2 raw28212step2Labels := by
      have ha : raw28212step2 = -raw28212step1 := by apply Matrix.ext; change ∀ i j, raw28212step2 i j = -(raw28212step1 i j); unfold raw28212step2 raw28212step1; decide +kernel
      have hl : raw28212step2Labels = raw28212step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2080 node2080Labels := by rfl

theorem canonical28213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28213 raw28213Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw28213 raw28213Labels = mixedMoment B raw28213step0 raw28213step0Labels := by
      have hz : ∀ j, raw28213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28213step0 = (fun i j => raw28213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28213step0 raw28213; decide +kernel
      have hl : raw28213step0Labels = raw28213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28213 raw28213Labels permutation434 hz
    mixedMoment B raw28213step0 raw28213step0Labels = mixedMoment B raw28213step1 raw28213step1Labels := by
      have ha : raw28213step1 = (fun i j => raw28213step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28213step1 raw28213step0; decide +kernel
      have hl : raw28213step1Labels = raw28213step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28213step0 raw28213step0Labels permutation150 permutation2
    mixedMoment B raw28213step1 raw28213step1Labels = mixedMoment B raw28213step2 raw28213step2Labels := by
      have ha : raw28213step2 = -raw28213step1 := by apply Matrix.ext; change ∀ i j, raw28213step2 i j = -(raw28213step1 i j); unfold raw28213step2 raw28213step1; decide +kernel
      have hl : raw28213step2Labels = raw28213step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2082 node2082Labels := by rfl

theorem canonical28214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28214 raw28214Labels = mixedMoment B node2102 node2102Labels := by
  calc
    mixedMoment B raw28214 raw28214Labels = mixedMoment B raw28214step0 raw28214step0Labels := by
      have hz : ∀ j, raw28214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28214step0 = (fun i j => raw28214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28214step0 raw28214; decide +kernel
      have hl : raw28214step0Labels = raw28214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28214 raw28214Labels permutation434 hz
    mixedMoment B raw28214step0 raw28214step0Labels = mixedMoment B raw28214step1 raw28214step1Labels := by
      have ha : raw28214step1 = (fun i j => raw28214step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28214step1 raw28214step0; decide +kernel
      have hl : raw28214step1Labels = raw28214step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28214step0 raw28214step0Labels permutation151 permutation2
    mixedMoment B raw28214step1 raw28214step1Labels = mixedMoment B raw28214step2 raw28214step2Labels := by
      have ha : raw28214step2 = -raw28214step1 := by apply Matrix.ext; change ∀ i j, raw28214step2 i j = -(raw28214step1 i j); unfold raw28214step2 raw28214step1; decide +kernel
      have hl : raw28214step2Labels = raw28214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2102 node2102Labels := by rfl

theorem canonical28215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28215 raw28215Labels = mixedMoment B node2076 node2076Labels := by
  calc
    mixedMoment B raw28215 raw28215Labels = mixedMoment B raw28215step0 raw28215step0Labels := by
      have ha : raw28215step0 = (fun i j => raw28215 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28215step0 raw28215; decide +kernel
      have hl : raw28215step0Labels = raw28215Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28215 raw28215Labels permutation682 permutation2
    mixedMoment B raw28215step0 raw28215step0Labels = mixedMoment B raw28215step1 raw28215step1Labels := by
      have ha : raw28215step1 = -raw28215step0 := by apply Matrix.ext; change ∀ i j, raw28215step1 i j = -(raw28215step0 i j); unfold raw28215step1 raw28215step0; decide +kernel
      have hl : raw28215step1Labels = raw28215step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2076 node2076Labels := by rfl

theorem canonical28216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28216 raw28216Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw28216 raw28216Labels = mixedMoment B raw28216step0 raw28216step0Labels := by
      have hz : ∀ j, raw28216 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28216step0 = (fun i j => raw28216 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28216step0 raw28216; decide +kernel
      have hl : raw28216step0Labels = raw28216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28216 raw28216Labels permutation434 hz
    mixedMoment B raw28216step0 raw28216step0Labels = mixedMoment B raw28216step1 raw28216step1Labels := by
      have ha : raw28216step1 = (fun i j => raw28216step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28216step1 raw28216step0; decide +kernel
      have hl : raw28216step1Labels = raw28216step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28216step0 raw28216step0Labels permutation145 permutation2
    mixedMoment B raw28216step1 raw28216step1Labels = mixedMoment B raw28216step2 raw28216step2Labels := by
      have ha : raw28216step2 = -raw28216step1 := by apply Matrix.ext; change ∀ i j, raw28216step2 i j = -(raw28216step1 i j); unfold raw28216step2 raw28216step1; decide +kernel
      have hl : raw28216step2Labels = raw28216step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical28217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28217 raw28217Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw28217 raw28217Labels = mixedMoment B raw28217step0 raw28217step0Labels := by
      have hz : ∀ j, raw28217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28217step0 = (fun i j => raw28217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28217step0 raw28217; decide +kernel
      have hl : raw28217step0Labels = raw28217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28217 raw28217Labels permutation434 hz
    mixedMoment B raw28217step0 raw28217step0Labels = mixedMoment B raw28217step1 raw28217step1Labels := by
      have ha : raw28217step1 = (fun i j => raw28217step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28217step1 raw28217step0; decide +kernel
      have hl : raw28217step1Labels = raw28217step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28217step0 raw28217step0Labels permutation151 permutation2
    mixedMoment B raw28217step1 raw28217step1Labels = mixedMoment B raw28217step2 raw28217step2Labels := by
      have ha : raw28217step2 = -raw28217step1 := by apply Matrix.ext; change ∀ i j, raw28217step2 i j = -(raw28217step1 i j); unfold raw28217step2 raw28217step1; decide +kernel
      have hl : raw28217step2Labels = raw28217step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3565 node3565Labels := by rfl

theorem canonical28218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28218 raw28218Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw28218 raw28218Labels = mixedMoment B raw28218step0 raw28218step0Labels := by
      have hz : ∀ j, raw28218 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28218step0 = (fun i j => raw28218 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28218step0 raw28218; decide +kernel
      have hl : raw28218step0Labels = raw28218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28218 raw28218Labels permutation434 hz
    mixedMoment B raw28218step0 raw28218step0Labels = mixedMoment B raw28218step1 raw28218step1Labels := by
      have ha : raw28218step1 = (fun i j => raw28218step0 (permutation141 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28218step1 raw28218step0; decide +kernel
      have hl : raw28218step1Labels = raw28218step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28218step0 raw28218step0Labels permutation141 permutation0
    mixedMoment B raw28218step1 raw28218step1Labels = mixedMoment B raw28218step2 raw28218step2Labels := by
      have ha : raw28218step2 = -raw28218step1 := by apply Matrix.ext; change ∀ i j, raw28218step2 i j = -(raw28218step1 i j); unfold raw28218step2 raw28218step1; decide +kernel
      have hl : raw28218step2Labels = raw28218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical28226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28226 raw28226Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw28226 raw28226Labels = mixedMoment B raw28226step0 raw28226step0Labels := by
      have hz : ∀ j, raw28226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28226step0 = (fun i j => raw28226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28226step0 raw28226; decide +kernel
      have hl : raw28226step0Labels = raw28226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28226 raw28226Labels permutation434 hz
    mixedMoment B raw28226step0 raw28226step0Labels = mixedMoment B raw28226step1 raw28226step1Labels := by
      have hz : ∀ j, raw28226step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28226step1 = (fun i j => raw28226step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28226step1 raw28226step0; decide +kernel
      have hl : raw28226step1Labels = raw28226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28226step0 raw28226step0Labels permutation80 hz
    mixedMoment B raw28226step1 raw28226step1Labels = mixedMoment B raw28226step2 raw28226step2Labels := by
      have ha : raw28226step2 = (fun i j => raw28226step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28226step2 raw28226step1; decide +kernel
      have hl : raw28226step2Labels = raw28226step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28226step1 raw28226step1Labels permutation30 permutation2
    mixedMoment B raw28226step2 raw28226step2Labels = mixedMoment B raw28226step3 raw28226step3Labels := by
      have ha : raw28226step3 = -raw28226step2 := by apply Matrix.ext; change ∀ i j, raw28226step3 i j = -(raw28226step2 i j); unfold raw28226step3 raw28226step2; decide +kernel
      have hl : raw28226step3Labels = raw28226step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2889 node2889Labels := by rfl

theorem canonical28227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28227 raw28227Labels = mixedMoment B node2886 node2886Labels := by
  calc
    mixedMoment B raw28227 raw28227Labels = mixedMoment B raw28227step0 raw28227step0Labels := by
      have hz : ∀ j, raw28227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28227step0 = (fun i j => raw28227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28227step0 raw28227; decide +kernel
      have hl : raw28227step0Labels = raw28227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28227 raw28227Labels permutation434 hz
    mixedMoment B raw28227step0 raw28227step0Labels = mixedMoment B raw28227step1 raw28227step1Labels := by
      have hz : ∀ j, raw28227step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28227step1 = (fun i j => raw28227step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28227step1 raw28227step0; decide +kernel
      have hl : raw28227step1Labels = raw28227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28227step0 raw28227step0Labels permutation80 hz
    _ = mixedMoment B node2886 node2886Labels := by rfl

theorem canonical28228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28228 raw28228Labels = mixedMoment B node2811 node2811Labels := by
  calc
    mixedMoment B raw28228 raw28228Labels = mixedMoment B raw28228step0 raw28228step0Labels := by
      have hz : ∀ j, raw28228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28228step0 = (fun i j => raw28228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28228step0 raw28228; decide +kernel
      have hl : raw28228step0Labels = raw28228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28228 raw28228Labels permutation434 hz
    _ = mixedMoment B node2811 node2811Labels := by rfl

theorem canonical28229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28229 raw28229Labels = mixedMoment B node2811 node2811Labels := by
  calc
    mixedMoment B raw28229 raw28229Labels = mixedMoment B raw28229step0 raw28229step0Labels := by
      have hz : ∀ j, raw28229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28229step0 = (fun i j => raw28229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28229step0 raw28229; decide +kernel
      have hl : raw28229step0Labels = raw28229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28229 raw28229Labels permutation346 hz
    _ = mixedMoment B node2811 node2811Labels := by rfl

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

theorem canonical28231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28231 raw28231Labels = mixedMoment B node1325 node1325Labels := by
  calc
    mixedMoment B raw28231 raw28231Labels = mixedMoment B raw28231step0 raw28231step0Labels := by
      have hz : ∀ j, raw28231 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28231step0 = (fun i j => raw28231 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28231step0 raw28231; decide +kernel
      have hl : raw28231step0Labels = raw28231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28231 raw28231Labels permutation434 hz
    mixedMoment B raw28231step0 raw28231step0Labels = mixedMoment B raw28231step1 raw28231step1Labels := by
      have hz : ∀ j, raw28231step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28231step1 = (fun i j => raw28231step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28231step1 raw28231step0; decide +kernel
      have hl : raw28231step1Labels = raw28231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28231step0 raw28231step0Labels permutation80 hz
    mixedMoment B raw28231step1 raw28231step1Labels = mixedMoment B raw28231step2 raw28231step2Labels := by
      have ha : raw28231step2 = (fun i j => raw28231step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28231step2 raw28231step1; decide +kernel
      have hl : raw28231step2Labels = raw28231step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28231step1 raw28231step1Labels permutation31 permutation2
    mixedMoment B raw28231step2 raw28231step2Labels = mixedMoment B raw28231step3 raw28231step3Labels := by
      have ha : raw28231step3 = -raw28231step2 := by apply Matrix.ext; change ∀ i j, raw28231step3 i j = -(raw28231step2 i j); unfold raw28231step3 raw28231step2; decide +kernel
      have hl : raw28231step3Labels = raw28231step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1325 node1325Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical221
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28307 raw28307Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw28307 raw28307Labels = mixedMoment B raw28307step0 raw28307step0Labels := by
      have hz : ∀ j, raw28307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28307step0 = (fun i j => raw28307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28307step0 raw28307; decide +kernel
      have hl : raw28307step0Labels = raw28307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28307 raw28307Labels permutation434 hz
    mixedMoment B raw28307step0 raw28307step0Labels = mixedMoment B raw28307step1 raw28307step1Labels := by
      have hz : ∀ j, raw28307step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28307step1 = (fun i j => raw28307step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28307step1 raw28307step0; decide +kernel
      have hl : raw28307step1Labels = raw28307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28307step0 raw28307step0Labels permutation80 hz
    mixedMoment B raw28307step1 raw28307step1Labels = mixedMoment B raw28307step2 raw28307step2Labels := by
      have ha : raw28307step2 = (fun i j => raw28307step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28307step2 raw28307step1; decide +kernel
      have hl : raw28307step2Labels = raw28307step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28307step1 raw28307step1Labels permutation30 permutation7
    mixedMoment B raw28307step2 raw28307step2Labels = mixedMoment B raw28307step3 raw28307step3Labels := by
      have ha : raw28307step3 = raw28307step2 := by apply Matrix.ext; unfold raw28307step3 raw28307step2; decide +kernel
      have hl : raw28307step2Labels = labelEmbedding1 ∘ raw28307step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28307step2 raw28307step2Labels raw28307step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3485 node3485Labels := by rfl

theorem canonical28308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28308 raw28308Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw28308 raw28308Labels = mixedMoment B raw28308step0 raw28308step0Labels := by
      have hz : ∀ j, raw28308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28308step0 = (fun i j => raw28308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28308step0 raw28308; decide +kernel
      have hl : raw28308step0Labels = raw28308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28308 raw28308Labels permutation434 hz
    mixedMoment B raw28308step0 raw28308step0Labels = mixedMoment B raw28308step1 raw28308step1Labels := by
      have ha : raw28308step1 = (fun i j => raw28308step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28308step1 raw28308step0; decide +kernel
      have hl : raw28308step1Labels = raw28308step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28308step0 raw28308step0Labels permutation150 permutation7
    mixedMoment B raw28308step1 raw28308step1Labels = mixedMoment B raw28308step2 raw28308step2Labels := by
      have ha : raw28308step2 = raw28308step1 := by apply Matrix.ext; unfold raw28308step2 raw28308step1; decide +kernel
      have hl : raw28308step1Labels = labelEmbedding1 ∘ raw28308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28308step1 raw28308step1Labels raw28308step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

theorem canonical28309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28309 raw28309Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw28309 raw28309Labels = mixedMoment B raw28309step0 raw28309step0Labels := by
      have hz : ∀ j, raw28309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28309step0 = (fun i j => raw28309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28309step0 raw28309; decide +kernel
      have hl : raw28309step0Labels = raw28309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28309 raw28309Labels permutation346 hz
    mixedMoment B raw28309step0 raw28309step0Labels = mixedMoment B raw28309step1 raw28309step1Labels := by
      have ha : raw28309step1 = (fun i j => raw28309step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28309step1 raw28309step0; decide +kernel
      have hl : raw28309step1Labels = raw28309step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28309step0 raw28309step0Labels permutation150 permutation7
    mixedMoment B raw28309step1 raw28309step1Labels = mixedMoment B raw28309step2 raw28309step2Labels := by
      have ha : raw28309step2 = raw28309step1 := by apply Matrix.ext; unfold raw28309step2 raw28309step1; decide +kernel
      have hl : raw28309step1Labels = labelEmbedding1 ∘ raw28309step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28309step1 raw28309step1Labels raw28309step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

theorem canonical28310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28310 raw28310Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw28310 raw28310Labels = mixedMoment B raw28310step0 raw28310step0Labels := by
      have hz : ∀ j, raw28310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28310step0 = (fun i j => raw28310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28310step0 raw28310; decide +kernel
      have hl : raw28310step0Labels = raw28310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28310 raw28310Labels permutation434 hz
    mixedMoment B raw28310step0 raw28310step0Labels = mixedMoment B raw28310step1 raw28310step1Labels := by
      have hz : ∀ j, raw28310step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28310step1 = (fun i j => raw28310step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28310step1 raw28310step0; decide +kernel
      have hl : raw28310step1Labels = raw28310step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28310step0 raw28310step0Labels permutation80 hz
    mixedMoment B raw28310step1 raw28310step1Labels = mixedMoment B raw28310step2 raw28310step2Labels := by
      have ha : raw28310step2 = (fun i j => raw28310step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28310step2 raw28310step1; decide +kernel
      have hl : raw28310step2Labels = raw28310step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28310step1 raw28310step1Labels permutation30 permutation7
    mixedMoment B raw28310step2 raw28310step2Labels = mixedMoment B raw28310step3 raw28310step3Labels := by
      have ha : raw28310step3 = raw28310step2 := by apply Matrix.ext; unfold raw28310step3 raw28310step2; decide +kernel
      have hl : raw28310step2Labels = labelEmbedding1 ∘ raw28310step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28310step2 raw28310step2Labels raw28310step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical28311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28311 raw28311Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw28311 raw28311Labels = mixedMoment B raw28311step0 raw28311step0Labels := by
      have hz : ∀ j, raw28311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28311step0 = (fun i j => raw28311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28311step0 raw28311; decide +kernel
      have hl : raw28311step0Labels = raw28311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28311 raw28311Labels permutation434 hz
    mixedMoment B raw28311step0 raw28311step0Labels = mixedMoment B raw28311step1 raw28311step1Labels := by
      have hz : ∀ j, raw28311step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28311step1 = (fun i j => raw28311step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28311step1 raw28311step0; decide +kernel
      have hl : raw28311step1Labels = raw28311step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28311step0 raw28311step0Labels permutation80 hz
    mixedMoment B raw28311step1 raw28311step1Labels = mixedMoment B raw28311step2 raw28311step2Labels := by
      have ha : raw28311step2 = (fun i j => raw28311step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28311step2 raw28311step1; decide +kernel
      have hl : raw28311step2Labels = raw28311step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28311step1 raw28311step1Labels permutation30 permutation7
    mixedMoment B raw28311step2 raw28311step2Labels = mixedMoment B raw28311step3 raw28311step3Labels := by
      have ha : raw28311step3 = raw28311step2 := by apply Matrix.ext; unfold raw28311step3 raw28311step2; decide +kernel
      have hl : raw28311step2Labels = labelEmbedding1 ∘ raw28311step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28311step2 raw28311step2Labels raw28311step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

theorem canonical28312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28312 raw28312Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw28312 raw28312Labels = mixedMoment B raw28312step0 raw28312step0Labels := by
      have hz : ∀ j, raw28312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28312step0 = (fun i j => raw28312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28312step0 raw28312; decide +kernel
      have hl : raw28312step0Labels = raw28312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28312 raw28312Labels permutation434 hz
    mixedMoment B raw28312step0 raw28312step0Labels = mixedMoment B raw28312step1 raw28312step1Labels := by
      have hz : ∀ j, raw28312step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28312step1 = (fun i j => raw28312step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28312step1 raw28312step0; decide +kernel
      have hl : raw28312step1Labels = raw28312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28312step0 raw28312step0Labels permutation80 hz
    mixedMoment B raw28312step1 raw28312step1Labels = mixedMoment B raw28312step2 raw28312step2Labels := by
      have ha : raw28312step2 = (fun i j => raw28312step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28312step2 raw28312step1; decide +kernel
      have hl : raw28312step2Labels = raw28312step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28312step1 raw28312step1Labels permutation11 permutation5
    mixedMoment B raw28312step2 raw28312step2Labels = mixedMoment B raw28312step3 raw28312step3Labels := by
      have ha : raw28312step3 = -raw28312step2 := by apply Matrix.ext; change ∀ i j, raw28312step3 i j = -(raw28312step2 i j); unfold raw28312step3 raw28312step2; decide +kernel
      have hl : raw28312step3Labels = raw28312step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28312step3 raw28312step3Labels = mixedMoment B raw28312step4 raw28312step4Labels := by
      have ha : raw28312step4 = raw28312step3 := by apply Matrix.ext; unfold raw28312step4 raw28312step3; decide +kernel
      have hl : raw28312step3Labels = labelEmbedding1 ∘ raw28312step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28312step3 raw28312step3Labels raw28312step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

theorem canonical28313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28313 raw28313Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw28313 raw28313Labels = mixedMoment B raw28313step0 raw28313step0Labels := by
      have hz : ∀ j, raw28313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28313step0 = (fun i j => raw28313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28313step0 raw28313; decide +kernel
      have hl : raw28313step0Labels = raw28313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28313 raw28313Labels permutation434 hz
    mixedMoment B raw28313step0 raw28313step0Labels = mixedMoment B raw28313step1 raw28313step1Labels := by
      have ha : raw28313step1 = (fun i j => raw28313step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28313step1 raw28313step0; decide +kernel
      have hl : raw28313step1Labels = raw28313step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28313step0 raw28313step0Labels permutation41 permutation5
    mixedMoment B raw28313step1 raw28313step1Labels = mixedMoment B raw28313step2 raw28313step2Labels := by
      have ha : raw28313step2 = -raw28313step1 := by apply Matrix.ext; change ∀ i j, raw28313step2 i j = -(raw28313step1 i j); unfold raw28313step2 raw28313step1; decide +kernel
      have hl : raw28313step2Labels = raw28313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28313step2 raw28313step2Labels = mixedMoment B raw28313step3 raw28313step3Labels := by
      have ha : raw28313step3 = raw28313step2 := by apply Matrix.ext; unfold raw28313step3 raw28313step2; decide +kernel
      have hl : raw28313step2Labels = labelEmbedding1 ∘ raw28313step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28313step2 raw28313step2Labels raw28313step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

theorem canonical28314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28314 raw28314Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw28314 raw28314Labels = mixedMoment B raw28314step0 raw28314step0Labels := by
      have hz : ∀ j, raw28314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28314step0 = (fun i j => raw28314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28314step0 raw28314; decide +kernel
      have hl : raw28314step0Labels = raw28314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28314 raw28314Labels permutation346 hz
    mixedMoment B raw28314step0 raw28314step0Labels = mixedMoment B raw28314step1 raw28314step1Labels := by
      have ha : raw28314step1 = (fun i j => raw28314step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28314step1 raw28314step0; decide +kernel
      have hl : raw28314step1Labels = raw28314step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28314step0 raw28314step0Labels permutation41 permutation5
    mixedMoment B raw28314step1 raw28314step1Labels = mixedMoment B raw28314step2 raw28314step2Labels := by
      have ha : raw28314step2 = -raw28314step1 := by apply Matrix.ext; change ∀ i j, raw28314step2 i j = -(raw28314step1 i j); unfold raw28314step2 raw28314step1; decide +kernel
      have hl : raw28314step2Labels = raw28314step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28314step2 raw28314step2Labels = mixedMoment B raw28314step3 raw28314step3Labels := by
      have ha : raw28314step3 = raw28314step2 := by apply Matrix.ext; unfold raw28314step3 raw28314step2; decide +kernel
      have hl : raw28314step2Labels = labelEmbedding1 ∘ raw28314step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28314step2 raw28314step2Labels raw28314step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

theorem canonical28315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28315 raw28315Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw28315 raw28315Labels = mixedMoment B raw28315step0 raw28315step0Labels := by
      have hz : ∀ j, raw28315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28315step0 = (fun i j => raw28315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28315step0 raw28315; decide +kernel
      have hl : raw28315step0Labels = raw28315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28315 raw28315Labels permutation434 hz
    mixedMoment B raw28315step0 raw28315step0Labels = mixedMoment B raw28315step1 raw28315step1Labels := by
      have hz : ∀ j, raw28315step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28315step1 = (fun i j => raw28315step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28315step1 raw28315step0; decide +kernel
      have hl : raw28315step1Labels = raw28315step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28315step0 raw28315step0Labels permutation80 hz
    mixedMoment B raw28315step1 raw28315step1Labels = mixedMoment B raw28315step2 raw28315step2Labels := by
      have ha : raw28315step2 = (fun i j => raw28315step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28315step2 raw28315step1; decide +kernel
      have hl : raw28315step2Labels = raw28315step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28315step1 raw28315step1Labels permutation11 permutation5
    mixedMoment B raw28315step2 raw28315step2Labels = mixedMoment B raw28315step3 raw28315step3Labels := by
      have ha : raw28315step3 = -raw28315step2 := by apply Matrix.ext; change ∀ i j, raw28315step3 i j = -(raw28315step2 i j); unfold raw28315step3 raw28315step2; decide +kernel
      have hl : raw28315step3Labels = raw28315step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28315step3 raw28315step3Labels = mixedMoment B raw28315step4 raw28315step4Labels := by
      have ha : raw28315step4 = raw28315step3 := by apply Matrix.ext; unfold raw28315step4 raw28315step3; decide +kernel
      have hl : raw28315step3Labels = labelEmbedding1 ∘ raw28315step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28315step3 raw28315step3Labels raw28315step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3549 node3549Labels := by rfl

theorem canonical28316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28316 raw28316Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw28316 raw28316Labels = mixedMoment B raw28316step0 raw28316step0Labels := by
      have hz : ∀ j, raw28316 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28316step0 = (fun i j => raw28316 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28316step0 raw28316; decide +kernel
      have hl : raw28316step0Labels = raw28316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28316 raw28316Labels permutation434 hz
    mixedMoment B raw28316step0 raw28316step0Labels = mixedMoment B raw28316step1 raw28316step1Labels := by
      have hz : ∀ j, raw28316step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28316step1 = (fun i j => raw28316step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28316step1 raw28316step0; decide +kernel
      have hl : raw28316step1Labels = raw28316step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28316step0 raw28316step0Labels permutation80 hz
    mixedMoment B raw28316step1 raw28316step1Labels = mixedMoment B raw28316step2 raw28316step2Labels := by
      have ha : raw28316step2 = (fun i j => raw28316step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28316step2 raw28316step1; decide +kernel
      have hl : raw28316step2Labels = raw28316step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28316step1 raw28316step1Labels permutation11 permutation5
    mixedMoment B raw28316step2 raw28316step2Labels = mixedMoment B raw28316step3 raw28316step3Labels := by
      have ha : raw28316step3 = -raw28316step2 := by apply Matrix.ext; change ∀ i j, raw28316step3 i j = -(raw28316step2 i j); unfold raw28316step3 raw28316step2; decide +kernel
      have hl : raw28316step3Labels = raw28316step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28316step3 raw28316step3Labels = mixedMoment B raw28316step4 raw28316step4Labels := by
      have ha : raw28316step4 = raw28316step3 := by apply Matrix.ext; unfold raw28316step4 raw28316step3; decide +kernel
      have hl : raw28316step3Labels = labelEmbedding1 ∘ raw28316step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28316step3 raw28316step3Labels raw28316step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical28317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28317 raw28317Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw28317 raw28317Labels = mixedMoment B raw28317step0 raw28317step0Labels := by
      have hz : ∀ j, raw28317 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28317step0 = (fun i j => raw28317 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28317step0 raw28317; decide +kernel
      have hl : raw28317step0Labels = raw28317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28317 raw28317Labels permutation434 hz
    mixedMoment B raw28317step0 raw28317step0Labels = mixedMoment B raw28317step1 raw28317step1Labels := by
      have ha : raw28317step1 = (fun i j => raw28317step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28317step1 raw28317step0; decide +kernel
      have hl : raw28317step1Labels = raw28317step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28317step0 raw28317step0Labels permutation44 permutation5
    mixedMoment B raw28317step1 raw28317step1Labels = mixedMoment B raw28317step2 raw28317step2Labels := by
      have ha : raw28317step2 = -raw28317step1 := by apply Matrix.ext; change ∀ i j, raw28317step2 i j = -(raw28317step1 i j); unfold raw28317step2 raw28317step1; decide +kernel
      have hl : raw28317step2Labels = raw28317step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28317step2 raw28317step2Labels = mixedMoment B raw28317step3 raw28317step3Labels := by
      have ha : raw28317step3 = raw28317step2 := by apply Matrix.ext; unfold raw28317step3 raw28317step2; decide +kernel
      have hl : raw28317step2Labels = labelEmbedding1 ∘ raw28317step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28317step2 raw28317step2Labels raw28317step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

theorem canonical28318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28318 raw28318Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw28318 raw28318Labels = mixedMoment B raw28318step0 raw28318step0Labels := by
      have hz : ∀ j, raw28318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28318step0 = (fun i j => raw28318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28318step0 raw28318; decide +kernel
      have hl : raw28318step0Labels = raw28318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28318 raw28318Labels permutation434 hz
    mixedMoment B raw28318step0 raw28318step0Labels = mixedMoment B raw28318step1 raw28318step1Labels := by
      have ha : raw28318step1 = (fun i j => raw28318step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28318step1 raw28318step0; decide +kernel
      have hl : raw28318step1Labels = raw28318step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28318step0 raw28318step0Labels permutation150 permutation7
    mixedMoment B raw28318step1 raw28318step1Labels = mixedMoment B raw28318step2 raw28318step2Labels := by
      have ha : raw28318step2 = raw28318step1 := by apply Matrix.ext; unfold raw28318step2 raw28318step1; decide +kernel
      have hl : raw28318step1Labels = labelEmbedding1 ∘ raw28318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28318step1 raw28318step1Labels raw28318step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

theorem canonical28319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28319 raw28319Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw28319 raw28319Labels = mixedMoment B raw28319step0 raw28319step0Labels := by
      have ha : raw28319step0 = (fun i j => raw28319 (permutation681 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28319step0 raw28319; decide +kernel
      have hl : raw28319step0Labels = raw28319Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28319 raw28319Labels permutation681 permutation7
    mixedMoment B raw28319step0 raw28319step0Labels = mixedMoment B raw28319step1 raw28319step1Labels := by
      have ha : raw28319step1 = raw28319step0 := by apply Matrix.ext; unfold raw28319step1 raw28319step0; decide +kernel
      have hl : raw28319step0Labels = labelEmbedding1 ∘ raw28319step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28319step0 raw28319step0Labels raw28319step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

theorem canonical28320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28320 raw28320Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw28320 raw28320Labels = mixedMoment B raw28320step0 raw28320step0Labels := by
      have hz : ∀ j, raw28320 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28320step0 = (fun i j => raw28320 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28320step0 raw28320; decide +kernel
      have hl : raw28320step0Labels = raw28320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28320 raw28320Labels permutation434 hz
    mixedMoment B raw28320step0 raw28320step0Labels = mixedMoment B raw28320step1 raw28320step1Labels := by
      have ha : raw28320step1 = (fun i j => raw28320step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28320step1 raw28320step0; decide +kernel
      have hl : raw28320step1Labels = raw28320step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28320step0 raw28320step0Labels permutation150 permutation7
    mixedMoment B raw28320step1 raw28320step1Labels = mixedMoment B raw28320step2 raw28320step2Labels := by
      have ha : raw28320step2 = raw28320step1 := by apply Matrix.ext; unfold raw28320step2 raw28320step1; decide +kernel
      have hl : raw28320step1Labels = labelEmbedding1 ∘ raw28320step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28320step1 raw28320step1Labels raw28320step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical28321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28321 raw28321Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw28321 raw28321Labels = mixedMoment B raw28321step0 raw28321step0Labels := by
      have hz : ∀ j, raw28321 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28321step0 = (fun i j => raw28321 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28321step0 raw28321; decide +kernel
      have hl : raw28321step0Labels = raw28321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28321 raw28321Labels permutation434 hz
    mixedMoment B raw28321step0 raw28321step0Labels = mixedMoment B raw28321step1 raw28321step1Labels := by
      have ha : raw28321step1 = (fun i j => raw28321step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28321step1 raw28321step0; decide +kernel
      have hl : raw28321step1Labels = raw28321step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28321step0 raw28321step0Labels permutation48 permutation5
    mixedMoment B raw28321step1 raw28321step1Labels = mixedMoment B raw28321step2 raw28321step2Labels := by
      have ha : raw28321step2 = -raw28321step1 := by apply Matrix.ext; change ∀ i j, raw28321step2 i j = -(raw28321step1 i j); unfold raw28321step2 raw28321step1; decide +kernel
      have hl : raw28321step2Labels = raw28321step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28321step2 raw28321step2Labels = mixedMoment B raw28321step3 raw28321step3Labels := by
      have ha : raw28321step3 = raw28321step2 := by apply Matrix.ext; unfold raw28321step3 raw28321step2; decide +kernel
      have hl : raw28321step2Labels = labelEmbedding1 ∘ raw28321step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28321step2 raw28321step2Labels raw28321step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

theorem canonical28322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28322 raw28322Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw28322 raw28322Labels = mixedMoment B raw28322step0 raw28322step0Labels := by
      have hz : ∀ j, raw28322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28322step0 = (fun i j => raw28322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28322step0 raw28322; decide +kernel
      have hl : raw28322step0Labels = raw28322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28322 raw28322Labels permutation346 hz
    mixedMoment B raw28322step0 raw28322step0Labels = mixedMoment B raw28322step1 raw28322step1Labels := by
      have ha : raw28322step1 = (fun i j => raw28322step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28322step1 raw28322step0; decide +kernel
      have hl : raw28322step1Labels = raw28322step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28322step0 raw28322step0Labels permutation44 permutation5
    mixedMoment B raw28322step1 raw28322step1Labels = mixedMoment B raw28322step2 raw28322step2Labels := by
      have ha : raw28322step2 = -raw28322step1 := by apply Matrix.ext; change ∀ i j, raw28322step2 i j = -(raw28322step1 i j); unfold raw28322step2 raw28322step1; decide +kernel
      have hl : raw28322step2Labels = raw28322step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28322step2 raw28322step2Labels = mixedMoment B raw28322step3 raw28322step3Labels := by
      have ha : raw28322step3 = raw28322step2 := by apply Matrix.ext; unfold raw28322step3 raw28322step2; decide +kernel
      have hl : raw28322step2Labels = labelEmbedding1 ∘ raw28322step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28322step2 raw28322step2Labels raw28322step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

theorem canonical28323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28323 raw28323Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw28323 raw28323Labels = mixedMoment B raw28323step0 raw28323step0Labels := by
      have hz : ∀ j, raw28323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28323step0 = (fun i j => raw28323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28323step0 raw28323; decide +kernel
      have hl : raw28323step0Labels = raw28323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28323 raw28323Labels permutation346 hz
    mixedMoment B raw28323step0 raw28323step0Labels = mixedMoment B raw28323step1 raw28323step1Labels := by
      have ha : raw28323step1 = (fun i j => raw28323step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28323step1 raw28323step0; decide +kernel
      have hl : raw28323step1Labels = raw28323step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28323step0 raw28323step0Labels permutation150 permutation7
    mixedMoment B raw28323step1 raw28323step1Labels = mixedMoment B raw28323step2 raw28323step2Labels := by
      have ha : raw28323step2 = raw28323step1 := by apply Matrix.ext; unfold raw28323step2 raw28323step1; decide +kernel
      have hl : raw28323step1Labels = labelEmbedding1 ∘ raw28323step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28323step1 raw28323step1Labels raw28323step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

theorem canonical28324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28324 raw28324Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw28324 raw28324Labels = mixedMoment B raw28324step0 raw28324step0Labels := by
      have ha : raw28324step0 = (fun i j => raw28324 (permutation687 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28324step0 raw28324; decide +kernel
      have hl : raw28324step0Labels = raw28324Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28324 raw28324Labels permutation687 permutation7
    mixedMoment B raw28324step0 raw28324step0Labels = mixedMoment B raw28324step1 raw28324step1Labels := by
      have ha : raw28324step1 = raw28324step0 := by apply Matrix.ext; unfold raw28324step1 raw28324step0; decide +kernel
      have hl : raw28324step0Labels = labelEmbedding1 ∘ raw28324step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28324step0 raw28324step0Labels raw28324step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

theorem canonical28325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28325 raw28325Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw28325 raw28325Labels = mixedMoment B raw28325step0 raw28325step0Labels := by
      have hz : ∀ j, raw28325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28325step0 = (fun i j => raw28325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28325step0 raw28325; decide +kernel
      have hl : raw28325step0Labels = raw28325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28325 raw28325Labels permutation346 hz
    mixedMoment B raw28325step0 raw28325step0Labels = mixedMoment B raw28325step1 raw28325step1Labels := by
      have ha : raw28325step1 = (fun i j => raw28325step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28325step1 raw28325step0; decide +kernel
      have hl : raw28325step1Labels = raw28325step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28325step0 raw28325step0Labels permutation150 permutation7
    mixedMoment B raw28325step1 raw28325step1Labels = mixedMoment B raw28325step2 raw28325step2Labels := by
      have ha : raw28325step2 = raw28325step1 := by apply Matrix.ext; unfold raw28325step2 raw28325step1; decide +kernel
      have hl : raw28325step1Labels = labelEmbedding1 ∘ raw28325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28325step1 raw28325step1Labels raw28325step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical28326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28326 raw28326Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw28326 raw28326Labels = mixedMoment B raw28326step0 raw28326step0Labels := by
      have hz : ∀ j, raw28326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28326step0 = (fun i j => raw28326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28326step0 raw28326; decide +kernel
      have hl : raw28326step0Labels = raw28326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28326 raw28326Labels permutation346 hz
    mixedMoment B raw28326step0 raw28326step0Labels = mixedMoment B raw28326step1 raw28326step1Labels := by
      have ha : raw28326step1 = (fun i j => raw28326step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28326step1 raw28326step0; decide +kernel
      have hl : raw28326step1Labels = raw28326step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28326step0 raw28326step0Labels permutation48 permutation5
    mixedMoment B raw28326step1 raw28326step1Labels = mixedMoment B raw28326step2 raw28326step2Labels := by
      have ha : raw28326step2 = -raw28326step1 := by apply Matrix.ext; change ∀ i j, raw28326step2 i j = -(raw28326step1 i j); unfold raw28326step2 raw28326step1; decide +kernel
      have hl : raw28326step2Labels = raw28326step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28326step2 raw28326step2Labels = mixedMoment B raw28326step3 raw28326step3Labels := by
      have ha : raw28326step3 = raw28326step2 := by apply Matrix.ext; unfold raw28326step3 raw28326step2; decide +kernel
      have hl : raw28326step2Labels = labelEmbedding1 ∘ raw28326step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28326step2 raw28326step2Labels raw28326step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

theorem canonical28327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28327 raw28327Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw28327 raw28327Labels = mixedMoment B raw28327step0 raw28327step0Labels := by
      have hz : ∀ j, raw28327 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28327step0 = (fun i j => raw28327 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28327step0 raw28327; decide +kernel
      have hl : raw28327step0Labels = raw28327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28327 raw28327Labels permutation434 hz
    mixedMoment B raw28327step0 raw28327step0Labels = mixedMoment B raw28327step1 raw28327step1Labels := by
      have hz : ∀ j, raw28327step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28327step1 = (fun i j => raw28327step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28327step1 raw28327step0; decide +kernel
      have hl : raw28327step1Labels = raw28327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28327step0 raw28327step0Labels permutation80 hz
    mixedMoment B raw28327step1 raw28327step1Labels = mixedMoment B raw28327step2 raw28327step2Labels := by
      have ha : raw28327step2 = (fun i j => raw28327step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28327step2 raw28327step1; decide +kernel
      have hl : raw28327step2Labels = raw28327step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28327step1 raw28327step1Labels permutation8 permutation5
    mixedMoment B raw28327step2 raw28327step2Labels = mixedMoment B raw28327step3 raw28327step3Labels := by
      have ha : raw28327step3 = -raw28327step2 := by apply Matrix.ext; change ∀ i j, raw28327step3 i j = -(raw28327step2 i j); unfold raw28327step3 raw28327step2; decide +kernel
      have hl : raw28327step3Labels = raw28327step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28327step3 raw28327step3Labels = mixedMoment B raw28327step4 raw28327step4Labels := by
      have ha : raw28327step4 = raw28327step3 := by apply Matrix.ext; unfold raw28327step4 raw28327step3; decide +kernel
      have hl : raw28327step3Labels = labelEmbedding1 ∘ raw28327step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28327step3 raw28327step3Labels raw28327step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

theorem canonical28328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28328 raw28328Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw28328 raw28328Labels = mixedMoment B raw28328step0 raw28328step0Labels := by
      have hz : ∀ j, raw28328 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28328step0 = (fun i j => raw28328 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28328step0 raw28328; decide +kernel
      have hl : raw28328step0Labels = raw28328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28328 raw28328Labels permutation434 hz
    mixedMoment B raw28328step0 raw28328step0Labels = mixedMoment B raw28328step1 raw28328step1Labels := by
      have hz : ∀ j, raw28328step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28328step1 = (fun i j => raw28328step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28328step1 raw28328step0; decide +kernel
      have hl : raw28328step1Labels = raw28328step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28328step0 raw28328step0Labels permutation80 hz
    mixedMoment B raw28328step1 raw28328step1Labels = mixedMoment B raw28328step2 raw28328step2Labels := by
      have ha : raw28328step2 = (fun i j => raw28328step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28328step2 raw28328step1; decide +kernel
      have hl : raw28328step2Labels = raw28328step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28328step1 raw28328step1Labels permutation30 permutation7
    mixedMoment B raw28328step2 raw28328step2Labels = mixedMoment B raw28328step3 raw28328step3Labels := by
      have ha : raw28328step3 = raw28328step2 := by apply Matrix.ext; unfold raw28328step3 raw28328step2; decide +kernel
      have hl : raw28328step2Labels = labelEmbedding1 ∘ raw28328step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28328step2 raw28328step2Labels raw28328step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3423 node3423Labels := by rfl

theorem canonical28329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28329 raw28329Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw28329 raw28329Labels = mixedMoment B raw28329step0 raw28329step0Labels := by
      have hz : ∀ j, raw28329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28329step0 = (fun i j => raw28329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28329step0 raw28329; decide +kernel
      have hl : raw28329step0Labels = raw28329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28329 raw28329Labels permutation434 hz
    mixedMoment B raw28329step0 raw28329step0Labels = mixedMoment B raw28329step1 raw28329step1Labels := by
      have ha : raw28329step1 = (fun i j => raw28329step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28329step1 raw28329step0; decide +kernel
      have hl : raw28329step1Labels = raw28329step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28329step0 raw28329step0Labels permutation150 permutation7
    mixedMoment B raw28329step1 raw28329step1Labels = mixedMoment B raw28329step2 raw28329step2Labels := by
      have ha : raw28329step2 = raw28329step1 := by apply Matrix.ext; unfold raw28329step2 raw28329step1; decide +kernel
      have hl : raw28329step1Labels = labelEmbedding1 ∘ raw28329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28329step1 raw28329step1Labels raw28329step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

theorem canonical28330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28330 raw28330Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw28330 raw28330Labels = mixedMoment B raw28330step0 raw28330step0Labels := by
      have hz : ∀ j, raw28330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28330step0 = (fun i j => raw28330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28330step0 raw28330; decide +kernel
      have hl : raw28330step0Labels = raw28330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28330 raw28330Labels permutation346 hz
    mixedMoment B raw28330step0 raw28330step0Labels = mixedMoment B raw28330step1 raw28330step1Labels := by
      have ha : raw28330step1 = (fun i j => raw28330step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28330step1 raw28330step0; decide +kernel
      have hl : raw28330step1Labels = raw28330step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28330step0 raw28330step0Labels permutation150 permutation7
    mixedMoment B raw28330step1 raw28330step1Labels = mixedMoment B raw28330step2 raw28330step2Labels := by
      have ha : raw28330step2 = raw28330step1 := by apply Matrix.ext; unfold raw28330step2 raw28330step1; decide +kernel
      have hl : raw28330step1Labels = labelEmbedding1 ∘ raw28330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28330step1 raw28330step1Labels raw28330step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

theorem canonical28331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28331 raw28331Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw28331 raw28331Labels = mixedMoment B raw28331step0 raw28331step0Labels := by
      have hz : ∀ j, raw28331 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28331step0 = (fun i j => raw28331 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28331step0 raw28331; decide +kernel
      have hl : raw28331step0Labels = raw28331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28331 raw28331Labels permutation434 hz
    mixedMoment B raw28331step0 raw28331step0Labels = mixedMoment B raw28331step1 raw28331step1Labels := by
      have hz : ∀ j, raw28331step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28331step1 = (fun i j => raw28331step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28331step1 raw28331step0; decide +kernel
      have hl : raw28331step1Labels = raw28331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28331step0 raw28331step0Labels permutation80 hz
    mixedMoment B raw28331step1 raw28331step1Labels = mixedMoment B raw28331step2 raw28331step2Labels := by
      have ha : raw28331step2 = (fun i j => raw28331step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28331step2 raw28331step1; decide +kernel
      have hl : raw28331step2Labels = raw28331step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28331step1 raw28331step1Labels permutation12 permutation5
    mixedMoment B raw28331step2 raw28331step2Labels = mixedMoment B raw28331step3 raw28331step3Labels := by
      have ha : raw28331step3 = -raw28331step2 := by apply Matrix.ext; change ∀ i j, raw28331step3 i j = -(raw28331step2 i j); unfold raw28331step3 raw28331step2; decide +kernel
      have hl : raw28331step3Labels = raw28331step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28331step3 raw28331step3Labels = mixedMoment B raw28331step4 raw28331step4Labels := by
      have ha : raw28331step4 = raw28331step3 := by apply Matrix.ext; unfold raw28331step4 raw28331step3; decide +kernel
      have hl : raw28331step3Labels = labelEmbedding1 ∘ raw28331step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28331step3 raw28331step3Labels raw28331step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

theorem canonical28332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28332 raw28332Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw28332 raw28332Labels = mixedMoment B raw28332step0 raw28332step0Labels := by
      have hz : ∀ j, raw28332 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28332step0 = (fun i j => raw28332 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28332step0 raw28332; decide +kernel
      have hl : raw28332step0Labels = raw28332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28332 raw28332Labels permutation434 hz
    mixedMoment B raw28332step0 raw28332step0Labels = mixedMoment B raw28332step1 raw28332step1Labels := by
      have hz : ∀ j, raw28332step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28332step1 = (fun i j => raw28332step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28332step1 raw28332step0; decide +kernel
      have hl : raw28332step1Labels = raw28332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28332step0 raw28332step0Labels permutation80 hz
    mixedMoment B raw28332step1 raw28332step1Labels = mixedMoment B raw28332step2 raw28332step2Labels := by
      have ha : raw28332step2 = (fun i j => raw28332step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28332step2 raw28332step1; decide +kernel
      have hl : raw28332step2Labels = raw28332step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28332step1 raw28332step1Labels permutation10 permutation5
    mixedMoment B raw28332step2 raw28332step2Labels = mixedMoment B raw28332step3 raw28332step3Labels := by
      have ha : raw28332step3 = -raw28332step2 := by apply Matrix.ext; change ∀ i j, raw28332step3 i j = -(raw28332step2 i j); unfold raw28332step3 raw28332step2; decide +kernel
      have hl : raw28332step3Labels = raw28332step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28332step3 raw28332step3Labels = mixedMoment B raw28332step4 raw28332step4Labels := by
      have ha : raw28332step4 = raw28332step3 := by apply Matrix.ext; unfold raw28332step4 raw28332step3; decide +kernel
      have hl : raw28332step3Labels = labelEmbedding1 ∘ raw28332step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28332step3 raw28332step3Labels raw28332step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

theorem canonical28333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28333 raw28333Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw28333 raw28333Labels = mixedMoment B raw28333step0 raw28333step0Labels := by
      have hz : ∀ j, raw28333 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28333step0 = (fun i j => raw28333 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28333step0 raw28333; decide +kernel
      have hl : raw28333step0Labels = raw28333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28333 raw28333Labels permutation434 hz
    mixedMoment B raw28333step0 raw28333step0Labels = mixedMoment B raw28333step1 raw28333step1Labels := by
      have hz : ∀ j, raw28333step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28333step1 = (fun i j => raw28333step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28333step1 raw28333step0; decide +kernel
      have hl : raw28333step1Labels = raw28333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28333step0 raw28333step0Labels permutation80 hz
    mixedMoment B raw28333step1 raw28333step1Labels = mixedMoment B raw28333step2 raw28333step2Labels := by
      have ha : raw28333step2 = (fun i j => raw28333step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28333step2 raw28333step1; decide +kernel
      have hl : raw28333step2Labels = raw28333step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28333step1 raw28333step1Labels permutation30 permutation7
    mixedMoment B raw28333step2 raw28333step2Labels = mixedMoment B raw28333step3 raw28333step3Labels := by
      have ha : raw28333step3 = raw28333step2 := by apply Matrix.ext; unfold raw28333step3 raw28333step2; decide +kernel
      have hl : raw28333step2Labels = labelEmbedding1 ∘ raw28333step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28333step2 raw28333step2Labels raw28333step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3277 node3277Labels := by rfl

theorem canonical28334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28334 raw28334Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw28334 raw28334Labels = mixedMoment B raw28334step0 raw28334step0Labels := by
      have hz : ∀ j, raw28334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28334step0 = (fun i j => raw28334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28334step0 raw28334; decide +kernel
      have hl : raw28334step0Labels = raw28334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28334 raw28334Labels permutation434 hz
    mixedMoment B raw28334step0 raw28334step0Labels = mixedMoment B raw28334step1 raw28334step1Labels := by
      have ha : raw28334step1 = (fun i j => raw28334step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28334step1 raw28334step0; decide +kernel
      have hl : raw28334step1Labels = raw28334step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28334step0 raw28334step0Labels permutation150 permutation7
    mixedMoment B raw28334step1 raw28334step1Labels = mixedMoment B raw28334step2 raw28334step2Labels := by
      have ha : raw28334step2 = raw28334step1 := by apply Matrix.ext; unfold raw28334step2 raw28334step1; decide +kernel
      have hl : raw28334step1Labels = labelEmbedding1 ∘ raw28334step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28334step1 raw28334step1Labels raw28334step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

theorem canonical28335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28335 raw28335Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw28335 raw28335Labels = mixedMoment B raw28335step0 raw28335step0Labels := by
      have hz : ∀ j, raw28335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28335step0 = (fun i j => raw28335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28335step0 raw28335; decide +kernel
      have hl : raw28335step0Labels = raw28335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28335 raw28335Labels permutation346 hz
    mixedMoment B raw28335step0 raw28335step0Labels = mixedMoment B raw28335step1 raw28335step1Labels := by
      have ha : raw28335step1 = (fun i j => raw28335step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28335step1 raw28335step0; decide +kernel
      have hl : raw28335step1Labels = raw28335step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28335step0 raw28335step0Labels permutation150 permutation7
    mixedMoment B raw28335step1 raw28335step1Labels = mixedMoment B raw28335step2 raw28335step2Labels := by
      have ha : raw28335step2 = raw28335step1 := by apply Matrix.ext; unfold raw28335step2 raw28335step1; decide +kernel
      have hl : raw28335step1Labels = labelEmbedding1 ∘ raw28335step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28335step1 raw28335step1Labels raw28335step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

theorem canonical28336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28336 raw28336Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw28336 raw28336Labels = mixedMoment B raw28336step0 raw28336step0Labels := by
      have hz : ∀ j, raw28336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28336step0 = (fun i j => raw28336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28336step0 raw28336; decide +kernel
      have hl : raw28336step0Labels = raw28336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28336 raw28336Labels permutation434 hz
    mixedMoment B raw28336step0 raw28336step0Labels = mixedMoment B raw28336step1 raw28336step1Labels := by
      have hz : ∀ j, raw28336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28336step1 = (fun i j => raw28336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28336step1 raw28336step0; decide +kernel
      have hl : raw28336step1Labels = raw28336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28336step0 raw28336step0Labels permutation80 hz
    mixedMoment B raw28336step1 raw28336step1Labels = mixedMoment B raw28336step2 raw28336step2Labels := by
      have ha : raw28336step2 = (fun i j => raw28336step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28336step2 raw28336step1; decide +kernel
      have hl : raw28336step2Labels = raw28336step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28336step1 raw28336step1Labels permutation30 permutation7
    mixedMoment B raw28336step2 raw28336step2Labels = mixedMoment B raw28336step3 raw28336step3Labels := by
      have ha : raw28336step3 = raw28336step2 := by apply Matrix.ext; unfold raw28336step3 raw28336step2; decide +kernel
      have hl : raw28336step2Labels = labelEmbedding1 ∘ raw28336step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28336step2 raw28336step2Labels raw28336step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical222
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28425 raw28425Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw28425 raw28425Labels = mixedMoment B raw28425step0 raw28425step0Labels := by
      have hz : ∀ j, raw28425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28425step0 = (fun i j => raw28425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28425step0 raw28425; decide +kernel
      have hl : raw28425step0Labels = raw28425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28425 raw28425Labels permutation434 hz
    mixedMoment B raw28425step0 raw28425step0Labels = mixedMoment B raw28425step1 raw28425step1Labels := by
      have hz : ∀ j, raw28425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28425step1 = (fun i j => raw28425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28425step1 raw28425step0; decide +kernel
      have hl : raw28425step1Labels = raw28425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28425step0 raw28425step0Labels permutation80 hz
    mixedMoment B raw28425step1 raw28425step1Labels = mixedMoment B raw28425step2 raw28425step2Labels := by
      have ha : raw28425step2 = (fun i j => raw28425step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28425step2 raw28425step1; decide +kernel
      have hl : raw28425step2Labels = raw28425step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28425step1 raw28425step1Labels permutation30 permutation7
    mixedMoment B raw28425step2 raw28425step2Labels = mixedMoment B raw28425step3 raw28425step3Labels := by
      have ha : raw28425step3 = raw28425step2 := by apply Matrix.ext; unfold raw28425step3 raw28425step2; decide +kernel
      have hl : raw28425step2Labels = labelEmbedding1 ∘ raw28425step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28425step2 raw28425step2Labels raw28425step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical28426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28426 raw28426Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw28426 raw28426Labels = mixedMoment B raw28426step0 raw28426step0Labels := by
      have hz : ∀ j, raw28426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28426step0 = (fun i j => raw28426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28426step0 raw28426; decide +kernel
      have hl : raw28426step0Labels = raw28426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28426 raw28426Labels permutation434 hz
    mixedMoment B raw28426step0 raw28426step0Labels = mixedMoment B raw28426step1 raw28426step1Labels := by
      have ha : raw28426step1 = (fun i j => raw28426step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28426step1 raw28426step0; decide +kernel
      have hl : raw28426step1Labels = raw28426step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28426step0 raw28426step0Labels permutation150 permutation7
    mixedMoment B raw28426step1 raw28426step1Labels = mixedMoment B raw28426step2 raw28426step2Labels := by
      have ha : raw28426step2 = raw28426step1 := by apply Matrix.ext; unfold raw28426step2 raw28426step1; decide +kernel
      have hl : raw28426step1Labels = labelEmbedding1 ∘ raw28426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28426step1 raw28426step1Labels raw28426step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical28427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28427 raw28427Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw28427 raw28427Labels = mixedMoment B raw28427step0 raw28427step0Labels := by
      have hz : ∀ j, raw28427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28427step0 = (fun i j => raw28427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28427step0 raw28427; decide +kernel
      have hl : raw28427step0Labels = raw28427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28427 raw28427Labels permutation346 hz
    mixedMoment B raw28427step0 raw28427step0Labels = mixedMoment B raw28427step1 raw28427step1Labels := by
      have ha : raw28427step1 = (fun i j => raw28427step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28427step1 raw28427step0; decide +kernel
      have hl : raw28427step1Labels = raw28427step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28427step0 raw28427step0Labels permutation150 permutation7
    mixedMoment B raw28427step1 raw28427step1Labels = mixedMoment B raw28427step2 raw28427step2Labels := by
      have ha : raw28427step2 = raw28427step1 := by apply Matrix.ext; unfold raw28427step2 raw28427step1; decide +kernel
      have hl : raw28427step1Labels = labelEmbedding1 ∘ raw28427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28427step1 raw28427step1Labels raw28427step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical28428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28428 raw28428Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw28428 raw28428Labels = mixedMoment B raw28428step0 raw28428step0Labels := by
      have hz : ∀ j, raw28428 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28428step0 = (fun i j => raw28428 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28428step0 raw28428; decide +kernel
      have hl : raw28428step0Labels = raw28428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28428 raw28428Labels permutation520 hz
    mixedMoment B raw28428step0 raw28428step0Labels = mixedMoment B raw28428step1 raw28428step1Labels := by
      have hz : ∀ j, raw28428step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28428step1 = (fun i j => raw28428step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28428step1 raw28428step0; decide +kernel
      have hl : raw28428step1Labels = raw28428step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28428step0 raw28428step0Labels permutation104 hz
    mixedMoment B raw28428step1 raw28428step1Labels = mixedMoment B raw28428step2 raw28428step2Labels := by
      have hz : ∀ j, raw28428step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28428step2 = (fun i j => raw28428step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28428step2 raw28428step1; decide +kernel
      have hl : raw28428step2Labels = raw28428step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28428step1 raw28428step1Labels permutation20 hz
    mixedMoment B raw28428step2 raw28428step2Labels = mixedMoment B raw28428step3 raw28428step3Labels := by
      have ha : raw28428step3 = (fun i j => raw28428step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28428step3 raw28428step2; decide +kernel
      have hl : raw28428step3Labels = raw28428step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28428step2 raw28428step2Labels permutation6 permutation7
    mixedMoment B raw28428step3 raw28428step3Labels = mixedMoment B raw28428step4 raw28428step4Labels := by
      have ha : raw28428step4 = raw28428step3 := by apply Matrix.ext; unfold raw28428step4 raw28428step3; decide +kernel
      have hl : raw28428step3Labels = labelEmbedding1 ∘ raw28428step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28428step3 raw28428step3Labels raw28428step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2293 node2293Labels := by rfl

theorem canonical28429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28429 raw28429Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw28429 raw28429Labels = mixedMoment B raw28429step0 raw28429step0Labels := by
      have hz : ∀ j, raw28429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28429step0 = (fun i j => raw28429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28429step0 raw28429; decide +kernel
      have hl : raw28429step0Labels = raw28429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28429 raw28429Labels permutation434 hz
    mixedMoment B raw28429step0 raw28429step0Labels = mixedMoment B raw28429step1 raw28429step1Labels := by
      have hz : ∀ j, raw28429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28429step1 = (fun i j => raw28429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28429step1 raw28429step0; decide +kernel
      have hl : raw28429step1Labels = raw28429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28429step0 raw28429step0Labels permutation80 hz
    mixedMoment B raw28429step1 raw28429step1Labels = mixedMoment B raw28429step2 raw28429step2Labels := by
      have ha : raw28429step2 = (fun i j => raw28429step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28429step2 raw28429step1; decide +kernel
      have hl : raw28429step2Labels = raw28429step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28429step1 raw28429step1Labels permutation30 permutation7
    mixedMoment B raw28429step2 raw28429step2Labels = mixedMoment B raw28429step3 raw28429step3Labels := by
      have ha : raw28429step3 = raw28429step2 := by apply Matrix.ext; unfold raw28429step3 raw28429step2; decide +kernel
      have hl : raw28429step2Labels = labelEmbedding1 ∘ raw28429step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28429step2 raw28429step2Labels raw28429step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical28430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28430 raw28430Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw28430 raw28430Labels = mixedMoment B raw28430step0 raw28430step0Labels := by
      have hz : ∀ j, raw28430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28430step0 = (fun i j => raw28430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28430step0 raw28430; decide +kernel
      have hl : raw28430step0Labels = raw28430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28430 raw28430Labels permutation434 hz
    mixedMoment B raw28430step0 raw28430step0Labels = mixedMoment B raw28430step1 raw28430step1Labels := by
      have hz : ∀ j, raw28430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28430step1 = (fun i j => raw28430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28430step1 raw28430step0; decide +kernel
      have hl : raw28430step1Labels = raw28430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28430step0 raw28430step0Labels permutation80 hz
    mixedMoment B raw28430step1 raw28430step1Labels = mixedMoment B raw28430step2 raw28430step2Labels := by
      have ha : raw28430step2 = (fun i j => raw28430step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28430step2 raw28430step1; decide +kernel
      have hl : raw28430step2Labels = raw28430step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28430step1 raw28430step1Labels permutation13 permutation5
    mixedMoment B raw28430step2 raw28430step2Labels = mixedMoment B raw28430step3 raw28430step3Labels := by
      have ha : raw28430step3 = -raw28430step2 := by apply Matrix.ext; change ∀ i j, raw28430step3 i j = -(raw28430step2 i j); unfold raw28430step3 raw28430step2; decide +kernel
      have hl : raw28430step3Labels = raw28430step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28430step3 raw28430step3Labels = mixedMoment B raw28430step4 raw28430step4Labels := by
      have ha : raw28430step4 = raw28430step3 := by apply Matrix.ext; unfold raw28430step4 raw28430step3; decide +kernel
      have hl : raw28430step3Labels = labelEmbedding1 ∘ raw28430step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28430step3 raw28430step3Labels raw28430step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

theorem canonical28431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28431 raw28431Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw28431 raw28431Labels = mixedMoment B raw28431step0 raw28431step0Labels := by
      have hz : ∀ j, raw28431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28431step0 = (fun i j => raw28431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28431step0 raw28431; decide +kernel
      have hl : raw28431step0Labels = raw28431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28431 raw28431Labels permutation434 hz
    mixedMoment B raw28431step0 raw28431step0Labels = mixedMoment B raw28431step1 raw28431step1Labels := by
      have ha : raw28431step1 = (fun i j => raw28431step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28431step1 raw28431step0; decide +kernel
      have hl : raw28431step1Labels = raw28431step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28431step0 raw28431step0Labels permutation150 permutation7
    mixedMoment B raw28431step1 raw28431step1Labels = mixedMoment B raw28431step2 raw28431step2Labels := by
      have ha : raw28431step2 = raw28431step1 := by apply Matrix.ext; unfold raw28431step2 raw28431step1; decide +kernel
      have hl : raw28431step1Labels = labelEmbedding1 ∘ raw28431step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28431step1 raw28431step1Labels raw28431step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical28432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28432 raw28432Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw28432 raw28432Labels = mixedMoment B raw28432step0 raw28432step0Labels := by
      have hz : ∀ j, raw28432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28432step0 = (fun i j => raw28432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28432step0 raw28432; decide +kernel
      have hl : raw28432step0Labels = raw28432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28432 raw28432Labels permutation346 hz
    mixedMoment B raw28432step0 raw28432step0Labels = mixedMoment B raw28432step1 raw28432step1Labels := by
      have ha : raw28432step1 = (fun i j => raw28432step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28432step1 raw28432step0; decide +kernel
      have hl : raw28432step1Labels = raw28432step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28432step0 raw28432step0Labels permutation150 permutation7
    mixedMoment B raw28432step1 raw28432step1Labels = mixedMoment B raw28432step2 raw28432step2Labels := by
      have ha : raw28432step2 = raw28432step1 := by apply Matrix.ext; unfold raw28432step2 raw28432step1; decide +kernel
      have hl : raw28432step1Labels = labelEmbedding1 ∘ raw28432step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28432step1 raw28432step1Labels raw28432step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical28433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28433 raw28433Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw28433 raw28433Labels = mixedMoment B raw28433step0 raw28433step0Labels := by
      have hz : ∀ j, raw28433 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28433step0 = (fun i j => raw28433 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28433step0 raw28433; decide +kernel
      have hl : raw28433step0Labels = raw28433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28433 raw28433Labels permutation520 hz
    mixedMoment B raw28433step0 raw28433step0Labels = mixedMoment B raw28433step1 raw28433step1Labels := by
      have hz : ∀ j, raw28433step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28433step1 = (fun i j => raw28433step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28433step1 raw28433step0; decide +kernel
      have hl : raw28433step1Labels = raw28433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28433step0 raw28433step0Labels permutation104 hz
    mixedMoment B raw28433step1 raw28433step1Labels = mixedMoment B raw28433step2 raw28433step2Labels := by
      have hz : ∀ j, raw28433step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28433step2 = (fun i j => raw28433step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28433step2 raw28433step1; decide +kernel
      have hl : raw28433step2Labels = raw28433step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28433step1 raw28433step1Labels permutation20 hz
    mixedMoment B raw28433step2 raw28433step2Labels = mixedMoment B raw28433step3 raw28433step3Labels := by
      have ha : raw28433step3 = (fun i j => raw28433step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28433step3 raw28433step2; decide +kernel
      have hl : raw28433step3Labels = raw28433step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28433step2 raw28433step2Labels permutation6 permutation7
    mixedMoment B raw28433step3 raw28433step3Labels = mixedMoment B raw28433step4 raw28433step4Labels := by
      have ha : raw28433step4 = raw28433step3 := by apply Matrix.ext; unfold raw28433step4 raw28433step3; decide +kernel
      have hl : raw28433step3Labels = labelEmbedding1 ∘ raw28433step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28433step3 raw28433step3Labels raw28433step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2294 node2294Labels := by rfl

theorem canonical28434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28434 raw28434Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw28434 raw28434Labels = mixedMoment B raw28434step0 raw28434step0Labels := by
      have hz : ∀ j, raw28434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28434step0 = (fun i j => raw28434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28434step0 raw28434; decide +kernel
      have hl : raw28434step0Labels = raw28434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28434 raw28434Labels permutation434 hz
    mixedMoment B raw28434step0 raw28434step0Labels = mixedMoment B raw28434step1 raw28434step1Labels := by
      have hz : ∀ j, raw28434step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28434step1 = (fun i j => raw28434step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28434step1 raw28434step0; decide +kernel
      have hl : raw28434step1Labels = raw28434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28434step0 raw28434step0Labels permutation80 hz
    mixedMoment B raw28434step1 raw28434step1Labels = mixedMoment B raw28434step2 raw28434step2Labels := by
      have ha : raw28434step2 = (fun i j => raw28434step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28434step2 raw28434step1; decide +kernel
      have hl : raw28434step2Labels = raw28434step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28434step1 raw28434step1Labels permutation30 permutation7
    mixedMoment B raw28434step2 raw28434step2Labels = mixedMoment B raw28434step3 raw28434step3Labels := by
      have ha : raw28434step3 = raw28434step2 := by apply Matrix.ext; unfold raw28434step3 raw28434step2; decide +kernel
      have hl : raw28434step2Labels = labelEmbedding1 ∘ raw28434step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28434step2 raw28434step2Labels raw28434step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical28435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28435 raw28435Labels = mixedMoment B node1742 node1742Labels := by
  calc
    mixedMoment B raw28435 raw28435Labels = mixedMoment B raw28435step0 raw28435step0Labels := by
      have hz : ∀ j, raw28435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28435step0 = (fun i j => raw28435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28435step0 raw28435; decide +kernel
      have hl : raw28435step0Labels = raw28435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28435 raw28435Labels permutation434 hz
    mixedMoment B raw28435step0 raw28435step0Labels = mixedMoment B raw28435step1 raw28435step1Labels := by
      have ha : raw28435step1 = (fun i j => raw28435step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28435step1 raw28435step0; decide +kernel
      have hl : raw28435step1Labels = raw28435step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28435step0 raw28435step0Labels permutation50 permutation5
    mixedMoment B raw28435step1 raw28435step1Labels = mixedMoment B raw28435step2 raw28435step2Labels := by
      have ha : raw28435step2 = -raw28435step1 := by apply Matrix.ext; change ∀ i j, raw28435step2 i j = -(raw28435step1 i j); unfold raw28435step2 raw28435step1; decide +kernel
      have hl : raw28435step2Labels = raw28435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28435step2 raw28435step2Labels = mixedMoment B raw28435step3 raw28435step3Labels := by
      have ha : raw28435step3 = raw28435step2 := by apply Matrix.ext; unfold raw28435step3 raw28435step2; decide +kernel
      have hl : raw28435step2Labels = labelEmbedding1 ∘ raw28435step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28435step2 raw28435step2Labels raw28435step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1742 node1742Labels := by rfl

theorem canonical28436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28436 raw28436Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw28436 raw28436Labels = mixedMoment B raw28436step0 raw28436step0Labels := by
      have hz : ∀ j, raw28436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28436step0 = (fun i j => raw28436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28436step0 raw28436; decide +kernel
      have hl : raw28436step0Labels = raw28436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28436 raw28436Labels permutation434 hz
    mixedMoment B raw28436step0 raw28436step0Labels = mixedMoment B raw28436step1 raw28436step1Labels := by
      have ha : raw28436step1 = (fun i j => raw28436step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28436step1 raw28436step0; decide +kernel
      have hl : raw28436step1Labels = raw28436step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28436step0 raw28436step0Labels permutation144 permutation7
    mixedMoment B raw28436step1 raw28436step1Labels = mixedMoment B raw28436step2 raw28436step2Labels := by
      have ha : raw28436step2 = raw28436step1 := by apply Matrix.ext; unfold raw28436step2 raw28436step1; decide +kernel
      have hl : raw28436step1Labels = labelEmbedding1 ∘ raw28436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28436step1 raw28436step1Labels raw28436step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

theorem canonical28437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28437 raw28437Labels = mixedMoment B node2175 node2175Labels := by
  calc
    mixedMoment B raw28437 raw28437Labels = mixedMoment B raw28437step0 raw28437step0Labels := by
      have ha : raw28437step0 = (fun i j => raw28437 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28437step0 raw28437; decide +kernel
      have hl : raw28437step0Labels = raw28437Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28437 raw28437Labels permutation645 permutation7
    mixedMoment B raw28437step0 raw28437step0Labels = mixedMoment B raw28437step1 raw28437step1Labels := by
      have ha : raw28437step1 = raw28437step0 := by apply Matrix.ext; unfold raw28437step1 raw28437step0; decide +kernel
      have hl : raw28437step0Labels = labelEmbedding1 ∘ raw28437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28437step0 raw28437step0Labels raw28437step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2175 node2175Labels := by rfl

theorem canonical28438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28438 raw28438Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw28438 raw28438Labels = mixedMoment B raw28438step0 raw28438step0Labels := by
      have hz : ∀ j, raw28438 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28438step0 = (fun i j => raw28438 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28438step0 raw28438; decide +kernel
      have hl : raw28438step0Labels = raw28438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28438 raw28438Labels permutation520 hz
    mixedMoment B raw28438step0 raw28438step0Labels = mixedMoment B raw28438step1 raw28438step1Labels := by
      have hz : ∀ j, raw28438step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28438step1 = (fun i j => raw28438step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28438step1 raw28438step0; decide +kernel
      have hl : raw28438step1Labels = raw28438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28438step0 raw28438step0Labels permutation104 hz
    mixedMoment B raw28438step1 raw28438step1Labels = mixedMoment B raw28438step2 raw28438step2Labels := by
      have ha : raw28438step2 = (fun i j => raw28438step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28438step2 raw28438step1; decide +kernel
      have hl : raw28438step2Labels = raw28438step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28438step1 raw28438step1Labels permutation30 permutation7
    mixedMoment B raw28438step2 raw28438step2Labels = mixedMoment B raw28438step3 raw28438step3Labels := by
      have ha : raw28438step3 = raw28438step2 := by apply Matrix.ext; unfold raw28438step3 raw28438step2; decide +kernel
      have hl : raw28438step2Labels = labelEmbedding1 ∘ raw28438step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28438step2 raw28438step2Labels raw28438step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical28439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28439 raw28439Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw28439 raw28439Labels = mixedMoment B raw28439step0 raw28439step0Labels := by
      have hz : ∀ j, raw28439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28439step0 = (fun i j => raw28439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28439step0 raw28439; decide +kernel
      have hl : raw28439step0Labels = raw28439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28439 raw28439Labels permutation434 hz
    mixedMoment B raw28439step0 raw28439step0Labels = mixedMoment B raw28439step1 raw28439step1Labels := by
      have ha : raw28439step1 = (fun i j => raw28439step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28439step1 raw28439step0; decide +kernel
      have hl : raw28439step1Labels = raw28439step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28439step0 raw28439step0Labels permutation144 permutation7
    mixedMoment B raw28439step1 raw28439step1Labels = mixedMoment B raw28439step2 raw28439step2Labels := by
      have ha : raw28439step2 = raw28439step1 := by apply Matrix.ext; unfold raw28439step2 raw28439step1; decide +kernel
      have hl : raw28439step1Labels = labelEmbedding1 ∘ raw28439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28439step1 raw28439step1Labels raw28439step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

theorem canonical28440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28440 raw28440Labels = mixedMoment B node1742 node1742Labels := by
  calc
    mixedMoment B raw28440 raw28440Labels = mixedMoment B raw28440step0 raw28440step0Labels := by
      have hz : ∀ j, raw28440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28440step0 = (fun i j => raw28440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28440step0 raw28440; decide +kernel
      have hl : raw28440step0Labels = raw28440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28440 raw28440Labels permutation346 hz
    mixedMoment B raw28440step0 raw28440step0Labels = mixedMoment B raw28440step1 raw28440step1Labels := by
      have ha : raw28440step1 = (fun i j => raw28440step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28440step1 raw28440step0; decide +kernel
      have hl : raw28440step1Labels = raw28440step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28440step0 raw28440step0Labels permutation50 permutation5
    mixedMoment B raw28440step1 raw28440step1Labels = mixedMoment B raw28440step2 raw28440step2Labels := by
      have ha : raw28440step2 = -raw28440step1 := by apply Matrix.ext; change ∀ i j, raw28440step2 i j = -(raw28440step1 i j); unfold raw28440step2 raw28440step1; decide +kernel
      have hl : raw28440step2Labels = raw28440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28440step2 raw28440step2Labels = mixedMoment B raw28440step3 raw28440step3Labels := by
      have ha : raw28440step3 = raw28440step2 := by apply Matrix.ext; unfold raw28440step3 raw28440step2; decide +kernel
      have hl : raw28440step2Labels = labelEmbedding1 ∘ raw28440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28440step2 raw28440step2Labels raw28440step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1742 node1742Labels := by rfl

theorem canonical28441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28441 raw28441Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw28441 raw28441Labels = mixedMoment B raw28441step0 raw28441step0Labels := by
      have hz : ∀ j, raw28441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28441step0 = (fun i j => raw28441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28441step0 raw28441; decide +kernel
      have hl : raw28441step0Labels = raw28441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28441 raw28441Labels permutation346 hz
    mixedMoment B raw28441step0 raw28441step0Labels = mixedMoment B raw28441step1 raw28441step1Labels := by
      have ha : raw28441step1 = (fun i j => raw28441step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28441step1 raw28441step0; decide +kernel
      have hl : raw28441step1Labels = raw28441step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28441step0 raw28441step0Labels permutation144 permutation7
    mixedMoment B raw28441step1 raw28441step1Labels = mixedMoment B raw28441step2 raw28441step2Labels := by
      have ha : raw28441step2 = raw28441step1 := by apply Matrix.ext; unfold raw28441step2 raw28441step1; decide +kernel
      have hl : raw28441step1Labels = labelEmbedding1 ∘ raw28441step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28441step1 raw28441step1Labels raw28441step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

theorem canonical28442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28442 raw28442Labels = mixedMoment B node2175 node2175Labels := by
  calc
    mixedMoment B raw28442 raw28442Labels = mixedMoment B raw28442step0 raw28442step0Labels := by
      have ha : raw28442step0 = (fun i j => raw28442 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28442step0 raw28442; decide +kernel
      have hl : raw28442step0Labels = raw28442Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28442 raw28442Labels permutation663 permutation7
    mixedMoment B raw28442step0 raw28442step0Labels = mixedMoment B raw28442step1 raw28442step1Labels := by
      have ha : raw28442step1 = raw28442step0 := by apply Matrix.ext; unfold raw28442step1 raw28442step0; decide +kernel
      have hl : raw28442step0Labels = labelEmbedding1 ∘ raw28442step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28442step0 raw28442step0Labels raw28442step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2175 node2175Labels := by rfl

theorem canonical28443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28443 raw28443Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw28443 raw28443Labels = mixedMoment B raw28443step0 raw28443step0Labels := by
      have hz : ∀ j, raw28443 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28443step0 = (fun i j => raw28443 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28443step0 raw28443; decide +kernel
      have hl : raw28443step0Labels = raw28443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28443 raw28443Labels permutation520 hz
    mixedMoment B raw28443step0 raw28443step0Labels = mixedMoment B raw28443step1 raw28443step1Labels := by
      have hz : ∀ j, raw28443step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28443step1 = (fun i j => raw28443step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28443step1 raw28443step0; decide +kernel
      have hl : raw28443step1Labels = raw28443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28443step0 raw28443step0Labels permutation80 hz
    mixedMoment B raw28443step1 raw28443step1Labels = mixedMoment B raw28443step2 raw28443step2Labels := by
      have ha : raw28443step2 = (fun i j => raw28443step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28443step2 raw28443step1; decide +kernel
      have hl : raw28443step2Labels = raw28443step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28443step1 raw28443step1Labels permutation30 permutation7
    mixedMoment B raw28443step2 raw28443step2Labels = mixedMoment B raw28443step3 raw28443step3Labels := by
      have ha : raw28443step3 = raw28443step2 := by apply Matrix.ext; unfold raw28443step3 raw28443step2; decide +kernel
      have hl : raw28443step2Labels = labelEmbedding1 ∘ raw28443step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28443step2 raw28443step2Labels raw28443step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical28444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28444 raw28444Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw28444 raw28444Labels = mixedMoment B raw28444step0 raw28444step0Labels := by
      have hz : ∀ j, raw28444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28444step0 = (fun i j => raw28444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28444step0 raw28444; decide +kernel
      have hl : raw28444step0Labels = raw28444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28444 raw28444Labels permutation346 hz
    mixedMoment B raw28444step0 raw28444step0Labels = mixedMoment B raw28444step1 raw28444step1Labels := by
      have ha : raw28444step1 = (fun i j => raw28444step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28444step1 raw28444step0; decide +kernel
      have hl : raw28444step1Labels = raw28444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28444step0 raw28444step0Labels permutation144 permutation7
    mixedMoment B raw28444step1 raw28444step1Labels = mixedMoment B raw28444step2 raw28444step2Labels := by
      have ha : raw28444step2 = raw28444step1 := by apply Matrix.ext; unfold raw28444step2 raw28444step1; decide +kernel
      have hl : raw28444step1Labels = labelEmbedding1 ∘ raw28444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28444step1 raw28444step1Labels raw28444step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

theorem canonical28445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28445 raw28445Labels = mixedMoment B node1743 node1743Labels := by
  calc
    mixedMoment B raw28445 raw28445Labels = mixedMoment B raw28445step0 raw28445step0Labels := by
      have hz : ∀ j, raw28445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28445step0 = (fun i j => raw28445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28445step0 raw28445; decide +kernel
      have hl : raw28445step0Labels = raw28445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28445 raw28445Labels permutation434 hz
    mixedMoment B raw28445step0 raw28445step0Labels = mixedMoment B raw28445step1 raw28445step1Labels := by
      have hz : ∀ j, raw28445step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28445step1 = (fun i j => raw28445step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28445step1 raw28445step0; decide +kernel
      have hl : raw28445step1Labels = raw28445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28445step0 raw28445step0Labels permutation80 hz
    mixedMoment B raw28445step1 raw28445step1Labels = mixedMoment B raw28445step2 raw28445step2Labels := by
      have ha : raw28445step2 = (fun i j => raw28445step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28445step2 raw28445step1; decide +kernel
      have hl : raw28445step2Labels = raw28445step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28445step1 raw28445step1Labels permutation12 permutation5
    mixedMoment B raw28445step2 raw28445step2Labels = mixedMoment B raw28445step3 raw28445step3Labels := by
      have ha : raw28445step3 = -raw28445step2 := by apply Matrix.ext; change ∀ i j, raw28445step3 i j = -(raw28445step2 i j); unfold raw28445step3 raw28445step2; decide +kernel
      have hl : raw28445step3Labels = raw28445step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28445step3 raw28445step3Labels = mixedMoment B raw28445step4 raw28445step4Labels := by
      have ha : raw28445step4 = raw28445step3 := by apply Matrix.ext; unfold raw28445step4 raw28445step3; decide +kernel
      have hl : raw28445step3Labels = labelEmbedding1 ∘ raw28445step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28445step3 raw28445step3Labels raw28445step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1743 node1743Labels := by rfl

theorem canonical28446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28446 raw28446Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw28446 raw28446Labels = mixedMoment B raw28446step0 raw28446step0Labels := by
      have hz : ∀ j, raw28446 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28446step0 = (fun i j => raw28446 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28446step0 raw28446; decide +kernel
      have hl : raw28446step0Labels = raw28446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28446 raw28446Labels permutation434 hz
    mixedMoment B raw28446step0 raw28446step0Labels = mixedMoment B raw28446step1 raw28446step1Labels := by
      have hz : ∀ j, raw28446step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28446step1 = (fun i j => raw28446step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28446step1 raw28446step0; decide +kernel
      have hl : raw28446step1Labels = raw28446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28446step0 raw28446step0Labels permutation80 hz
    mixedMoment B raw28446step1 raw28446step1Labels = mixedMoment B raw28446step2 raw28446step2Labels := by
      have ha : raw28446step2 = (fun i j => raw28446step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28446step2 raw28446step1; decide +kernel
      have hl : raw28446step2Labels = raw28446step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28446step1 raw28446step1Labels permutation30 permutation7
    mixedMoment B raw28446step2 raw28446step2Labels = mixedMoment B raw28446step3 raw28446step3Labels := by
      have ha : raw28446step3 = raw28446step2 := by apply Matrix.ext; unfold raw28446step3 raw28446step2; decide +kernel
      have hl : raw28446step2Labels = labelEmbedding1 ∘ raw28446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28446step2 raw28446step2Labels raw28446step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2169 node2169Labels := by rfl

theorem canonical28447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28447 raw28447Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw28447 raw28447Labels = mixedMoment B raw28447step0 raw28447step0Labels := by
      have hz : ∀ j, raw28447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28447step0 = (fun i j => raw28447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28447step0 raw28447; decide +kernel
      have hl : raw28447step0Labels = raw28447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28447 raw28447Labels permutation434 hz
    mixedMoment B raw28447step0 raw28447step0Labels = mixedMoment B raw28447step1 raw28447step1Labels := by
      have ha : raw28447step1 = (fun i j => raw28447step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28447step1 raw28447step0; decide +kernel
      have hl : raw28447step1Labels = raw28447step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28447step0 raw28447step0Labels permutation150 permutation7
    mixedMoment B raw28447step1 raw28447step1Labels = mixedMoment B raw28447step2 raw28447step2Labels := by
      have ha : raw28447step2 = raw28447step1 := by apply Matrix.ext; unfold raw28447step2 raw28447step1; decide +kernel
      have hl : raw28447step1Labels = labelEmbedding1 ∘ raw28447step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28447step1 raw28447step1Labels raw28447step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2153 node2153Labels := by rfl

theorem canonical28448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28448 raw28448Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw28448 raw28448Labels = mixedMoment B raw28448step0 raw28448step0Labels := by
      have hz : ∀ j, raw28448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28448step0 = (fun i j => raw28448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28448step0 raw28448; decide +kernel
      have hl : raw28448step0Labels = raw28448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28448 raw28448Labels permutation346 hz
    mixedMoment B raw28448step0 raw28448step0Labels = mixedMoment B raw28448step1 raw28448step1Labels := by
      have ha : raw28448step1 = (fun i j => raw28448step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28448step1 raw28448step0; decide +kernel
      have hl : raw28448step1Labels = raw28448step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28448step0 raw28448step0Labels permutation150 permutation7
    mixedMoment B raw28448step1 raw28448step1Labels = mixedMoment B raw28448step2 raw28448step2Labels := by
      have ha : raw28448step2 = raw28448step1 := by apply Matrix.ext; unfold raw28448step2 raw28448step1; decide +kernel
      have hl : raw28448step1Labels = labelEmbedding1 ∘ raw28448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28448step1 raw28448step1Labels raw28448step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2153 node2153Labels := by rfl

theorem canonical28449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28449 raw28449Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw28449 raw28449Labels = mixedMoment B raw28449step0 raw28449step0Labels := by
      have hz : ∀ j, raw28449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28449step0 = (fun i j => raw28449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28449step0 raw28449; decide +kernel
      have hl : raw28449step0Labels = raw28449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28449 raw28449Labels permutation434 hz
    mixedMoment B raw28449step0 raw28449step0Labels = mixedMoment B raw28449step1 raw28449step1Labels := by
      have hz : ∀ j, raw28449step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28449step1 = (fun i j => raw28449step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28449step1 raw28449step0; decide +kernel
      have hl : raw28449step1Labels = raw28449step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28449step0 raw28449step0Labels permutation80 hz
    mixedMoment B raw28449step1 raw28449step1Labels = mixedMoment B raw28449step2 raw28449step2Labels := by
      have ha : raw28449step2 = (fun i j => raw28449step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28449step2 raw28449step1; decide +kernel
      have hl : raw28449step2Labels = raw28449step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28449step1 raw28449step1Labels permutation30 permutation7
    mixedMoment B raw28449step2 raw28449step2Labels = mixedMoment B raw28449step3 raw28449step3Labels := by
      have ha : raw28449step3 = raw28449step2 := by apply Matrix.ext; unfold raw28449step3 raw28449step2; decide +kernel
      have hl : raw28449step2Labels = labelEmbedding1 ∘ raw28449step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28449step2 raw28449step2Labels raw28449step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

theorem canonical28450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28450 raw28450Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw28450 raw28450Labels = mixedMoment B raw28450step0 raw28450step0Labels := by
      have hz : ∀ j, raw28450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28450step0 = (fun i j => raw28450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28450step0 raw28450; decide +kernel
      have hl : raw28450step0Labels = raw28450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28450 raw28450Labels permutation434 hz
    mixedMoment B raw28450step0 raw28450step0Labels = mixedMoment B raw28450step1 raw28450step1Labels := by
      have hz : ∀ j, raw28450step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28450step1 = (fun i j => raw28450step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28450step1 raw28450step0; decide +kernel
      have hl : raw28450step1Labels = raw28450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28450step0 raw28450step0Labels permutation80 hz
    mixedMoment B raw28450step1 raw28450step1Labels = mixedMoment B raw28450step2 raw28450step2Labels := by
      have ha : raw28450step2 = (fun i j => raw28450step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28450step2 raw28450step1; decide +kernel
      have hl : raw28450step2Labels = raw28450step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28450step1 raw28450step1Labels permutation30 permutation7
    mixedMoment B raw28450step2 raw28450step2Labels = mixedMoment B raw28450step3 raw28450step3Labels := by
      have ha : raw28450step3 = raw28450step2 := by apply Matrix.ext; unfold raw28450step3 raw28450step2; decide +kernel
      have hl : raw28450step2Labels = labelEmbedding1 ∘ raw28450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28450step2 raw28450step2Labels raw28450step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

theorem canonical28451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28451 raw28451Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw28451 raw28451Labels = mixedMoment B raw28451step0 raw28451step0Labels := by
      have hz : ∀ j, raw28451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28451step0 = (fun i j => raw28451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28451step0 raw28451; decide +kernel
      have hl : raw28451step0Labels = raw28451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28451 raw28451Labels permutation434 hz
    mixedMoment B raw28451step0 raw28451step0Labels = mixedMoment B raw28451step1 raw28451step1Labels := by
      have hz : ∀ j, raw28451step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28451step1 = (fun i j => raw28451step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28451step1 raw28451step0; decide +kernel
      have hl : raw28451step1Labels = raw28451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28451step0 raw28451step0Labels permutation80 hz
    mixedMoment B raw28451step1 raw28451step1Labels = mixedMoment B raw28451step2 raw28451step2Labels := by
      have ha : raw28451step2 = (fun i j => raw28451step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28451step2 raw28451step1; decide +kernel
      have hl : raw28451step2Labels = raw28451step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28451step1 raw28451step1Labels permutation30 permutation7
    mixedMoment B raw28451step2 raw28451step2Labels = mixedMoment B raw28451step3 raw28451step3Labels := by
      have ha : raw28451step3 = raw28451step2 := by apply Matrix.ext; unfold raw28451step3 raw28451step2; decide +kernel
      have hl : raw28451step2Labels = labelEmbedding1 ∘ raw28451step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28451step2 raw28451step2Labels raw28451step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

theorem canonical28452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28452 raw28452Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw28452 raw28452Labels = mixedMoment B raw28452step0 raw28452step0Labels := by
      have hz : ∀ j, raw28452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28452step0 = (fun i j => raw28452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28452step0 raw28452; decide +kernel
      have hl : raw28452step0Labels = raw28452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28452 raw28452Labels permutation434 hz
    mixedMoment B raw28452step0 raw28452step0Labels = mixedMoment B raw28452step1 raw28452step1Labels := by
      have ha : raw28452step1 = (fun i j => raw28452step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28452step1 raw28452step0; decide +kernel
      have hl : raw28452step1Labels = raw28452step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28452step0 raw28452step0Labels permutation150 permutation7
    mixedMoment B raw28452step1 raw28452step1Labels = mixedMoment B raw28452step2 raw28452step2Labels := by
      have ha : raw28452step2 = raw28452step1 := by apply Matrix.ext; unfold raw28452step2 raw28452step1; decide +kernel
      have hl : raw28452step1Labels = labelEmbedding1 ∘ raw28452step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28452step1 raw28452step1Labels raw28452step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

theorem canonical28453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28453 raw28453Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw28453 raw28453Labels = mixedMoment B raw28453step0 raw28453step0Labels := by
      have hz : ∀ j, raw28453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28453step0 = (fun i j => raw28453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28453step0 raw28453; decide +kernel
      have hl : raw28453step0Labels = raw28453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28453 raw28453Labels permutation346 hz
    mixedMoment B raw28453step0 raw28453step0Labels = mixedMoment B raw28453step1 raw28453step1Labels := by
      have ha : raw28453step1 = (fun i j => raw28453step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28453step1 raw28453step0; decide +kernel
      have hl : raw28453step1Labels = raw28453step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28453step0 raw28453step0Labels permutation150 permutation7
    mixedMoment B raw28453step1 raw28453step1Labels = mixedMoment B raw28453step2 raw28453step2Labels := by
      have ha : raw28453step2 = raw28453step1 := by apply Matrix.ext; unfold raw28453step2 raw28453step1; decide +kernel
      have hl : raw28453step1Labels = labelEmbedding1 ∘ raw28453step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28453step1 raw28453step1Labels raw28453step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

theorem canonical28454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28454 raw28454Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw28454 raw28454Labels = mixedMoment B raw28454step0 raw28454step0Labels := by
      have hz : ∀ j, raw28454 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28454step0 = (fun i j => raw28454 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28454step0 raw28454; decide +kernel
      have hl : raw28454step0Labels = raw28454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28454 raw28454Labels permutation520 hz
    mixedMoment B raw28454step0 raw28454step0Labels = mixedMoment B raw28454step1 raw28454step1Labels := by
      have hz : ∀ j, raw28454step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28454step1 = (fun i j => raw28454step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28454step1 raw28454step0; decide +kernel
      have hl : raw28454step1Labels = raw28454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28454step0 raw28454step0Labels permutation104 hz
    mixedMoment B raw28454step1 raw28454step1Labels = mixedMoment B raw28454step2 raw28454step2Labels := by
      have hz : ∀ j, raw28454step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28454step2 = (fun i j => raw28454step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28454step2 raw28454step1; decide +kernel
      have hl : raw28454step2Labels = raw28454step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28454step1 raw28454step1Labels permutation20 hz
    mixedMoment B raw28454step2 raw28454step2Labels = mixedMoment B raw28454step3 raw28454step3Labels := by
      have ha : raw28454step3 = (fun i j => raw28454step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28454step3 raw28454step2; decide +kernel
      have hl : raw28454step3Labels = raw28454step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28454step2 raw28454step2Labels permutation6 permutation7
    mixedMoment B raw28454step3 raw28454step3Labels = mixedMoment B raw28454step4 raw28454step4Labels := by
      have ha : raw28454step4 = raw28454step3 := by apply Matrix.ext; unfold raw28454step4 raw28454step3; decide +kernel
      have hl : raw28454step3Labels = labelEmbedding1 ∘ raw28454step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28454step3 raw28454step3Labels raw28454step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

theorem canonical28455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28455 raw28455Labels = mixedMoment B node2066 node2066Labels := by
  calc
    mixedMoment B raw28455 raw28455Labels = mixedMoment B raw28455step0 raw28455step0Labels := by
      have hz : ∀ j, raw28455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28455step0 = (fun i j => raw28455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28455step0 raw28455; decide +kernel
      have hl : raw28455step0Labels = raw28455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28455 raw28455Labels permutation434 hz
    mixedMoment B raw28455step0 raw28455step0Labels = mixedMoment B raw28455step1 raw28455step1Labels := by
      have hz : ∀ j, raw28455step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28455step1 = (fun i j => raw28455step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28455step1 raw28455step0; decide +kernel
      have hl : raw28455step1Labels = raw28455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28455step0 raw28455step0Labels permutation80 hz
    mixedMoment B raw28455step1 raw28455step1Labels = mixedMoment B raw28455step2 raw28455step2Labels := by
      have ha : raw28455step2 = (fun i j => raw28455step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28455step2 raw28455step1; decide +kernel
      have hl : raw28455step2Labels = raw28455step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28455step1 raw28455step1Labels permutation30 permutation2
    mixedMoment B raw28455step2 raw28455step2Labels = mixedMoment B raw28455step3 raw28455step3Labels := by
      have ha : raw28455step3 = -raw28455step2 := by apply Matrix.ext; change ∀ i j, raw28455step3 i j = -(raw28455step2 i j); unfold raw28455step3 raw28455step2; decide +kernel
      have hl : raw28455step3Labels = raw28455step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2066 node2066Labels := by rfl

theorem canonical28456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28456 raw28456Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw28456 raw28456Labels = mixedMoment B raw28456step0 raw28456step0Labels := by
      have hz : ∀ j, raw28456 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28456step0 = (fun i j => raw28456 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28456step0 raw28456; decide +kernel
      have hl : raw28456step0Labels = raw28456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28456 raw28456Labels permutation434 hz
    mixedMoment B raw28456step0 raw28456step0Labels = mixedMoment B raw28456step1 raw28456step1Labels := by
      have hz : ∀ j, raw28456step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28456step1 = (fun i j => raw28456step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28456step1 raw28456step0; decide +kernel
      have hl : raw28456step1Labels = raw28456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28456step0 raw28456step0Labels permutation80 hz
    mixedMoment B raw28456step1 raw28456step1Labels = mixedMoment B raw28456step2 raw28456step2Labels := by
      have ha : raw28456step2 = (fun i j => raw28456step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28456step2 raw28456step1; decide +kernel
      have hl : raw28456step2Labels = raw28456step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28456step1 raw28456step1Labels permutation31 permutation2
    mixedMoment B raw28456step2 raw28456step2Labels = mixedMoment B raw28456step3 raw28456step3Labels := by
      have ha : raw28456step3 = -raw28456step2 := by apply Matrix.ext; change ∀ i j, raw28456step3 i j = -(raw28456step2 i j); unfold raw28456step3 raw28456step2; decide +kernel
      have hl : raw28456step3Labels = raw28456step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical28457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28457 raw28457Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw28457 raw28457Labels = mixedMoment B raw28457step0 raw28457step0Labels := by
      have hz : ∀ j, raw28457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28457step0 = (fun i j => raw28457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28457step0 raw28457; decide +kernel
      have hl : raw28457step0Labels = raw28457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28457 raw28457Labels permutation434 hz
    mixedMoment B raw28457step0 raw28457step0Labels = mixedMoment B raw28457step1 raw28457step1Labels := by
      have ha : raw28457step1 = (fun i j => raw28457step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28457step1 raw28457step0; decide +kernel
      have hl : raw28457step1Labels = raw28457step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28457step0 raw28457step0Labels permutation145 permutation2
    mixedMoment B raw28457step1 raw28457step1Labels = mixedMoment B raw28457step2 raw28457step2Labels := by
      have ha : raw28457step2 = -raw28457step1 := by apply Matrix.ext; change ∀ i j, raw28457step2 i j = -(raw28457step1 i j); unfold raw28457step2 raw28457step1; decide +kernel
      have hl : raw28457step2Labels = raw28457step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1970 node1970Labels := by rfl

theorem canonical28458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28458 raw28458Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw28458 raw28458Labels = mixedMoment B raw28458step0 raw28458step0Labels := by
      have hz : ∀ j, raw28458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28458step0 = (fun i j => raw28458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28458step0 raw28458; decide +kernel
      have hl : raw28458step0Labels = raw28458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28458 raw28458Labels permutation346 hz
    mixedMoment B raw28458step0 raw28458step0Labels = mixedMoment B raw28458step1 raw28458step1Labels := by
      have ha : raw28458step1 = (fun i j => raw28458step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28458step1 raw28458step0; decide +kernel
      have hl : raw28458step1Labels = raw28458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28458step0 raw28458step0Labels permutation145 permutation2
    mixedMoment B raw28458step1 raw28458step1Labels = mixedMoment B raw28458step2 raw28458step2Labels := by
      have ha : raw28458step2 = -raw28458step1 := by apply Matrix.ext; change ∀ i j, raw28458step2 i j = -(raw28458step1 i j); unfold raw28458step2 raw28458step1; decide +kernel
      have hl : raw28458step2Labels = raw28458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1970 node1970Labels := by rfl

theorem canonical28459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28459 raw28459Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw28459 raw28459Labels = mixedMoment B raw28459step0 raw28459step0Labels := by
      have hz : ∀ j, raw28459 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28459step0 = (fun i j => raw28459 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28459step0 raw28459; decide +kernel
      have hl : raw28459step0Labels = raw28459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28459 raw28459Labels permutation434 hz
    mixedMoment B raw28459step0 raw28459step0Labels = mixedMoment B raw28459step1 raw28459step1Labels := by
      have hz : ∀ j, raw28459step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28459step1 = (fun i j => raw28459step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28459step1 raw28459step0; decide +kernel
      have hl : raw28459step1Labels = raw28459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28459step0 raw28459step0Labels permutation80 hz
    mixedMoment B raw28459step1 raw28459step1Labels = mixedMoment B raw28459step2 raw28459step2Labels := by
      have ha : raw28459step2 = (fun i j => raw28459step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28459step2 raw28459step1; decide +kernel
      have hl : raw28459step2Labels = raw28459step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28459step1 raw28459step1Labels permutation31 permutation2
    mixedMoment B raw28459step2 raw28459step2Labels = mixedMoment B raw28459step3 raw28459step3Labels := by
      have ha : raw28459step3 = -raw28459step2 := by apply Matrix.ext; change ∀ i j, raw28459step3 i j = -(raw28459step2 i j); unfold raw28459step3 raw28459step2; decide +kernel
      have hl : raw28459step3Labels = raw28459step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1819 node1819Labels := by rfl

theorem canonical28460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28460 raw28460Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw28460 raw28460Labels = mixedMoment B raw28460step0 raw28460step0Labels := by
      have hz : ∀ j, raw28460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28460step0 = (fun i j => raw28460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28460step0 raw28460; decide +kernel
      have hl : raw28460step0Labels = raw28460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28460 raw28460Labels permutation434 hz
    mixedMoment B raw28460step0 raw28460step0Labels = mixedMoment B raw28460step1 raw28460step1Labels := by
      have hz : ∀ j, raw28460step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28460step1 = (fun i j => raw28460step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28460step1 raw28460step0; decide +kernel
      have hl : raw28460step1Labels = raw28460step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28460step0 raw28460step0Labels permutation80 hz
    mixedMoment B raw28460step1 raw28460step1Labels = mixedMoment B raw28460step2 raw28460step2Labels := by
      have ha : raw28460step2 = (fun i j => raw28460step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28460step2 raw28460step1; decide +kernel
      have hl : raw28460step2Labels = raw28460step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28460step1 raw28460step1Labels permutation31 permutation2
    mixedMoment B raw28460step2 raw28460step2Labels = mixedMoment B raw28460step3 raw28460step3Labels := by
      have ha : raw28460step3 = -raw28460step2 := by apply Matrix.ext; change ∀ i j, raw28460step3 i j = -(raw28460step2 i j); unfold raw28460step3 raw28460step2; decide +kernel
      have hl : raw28460step3Labels = raw28460step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node939 node939Labels := by rfl

theorem canonical28461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28461 raw28461Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw28461 raw28461Labels = mixedMoment B raw28461step0 raw28461step0Labels := by
      have hz : ∀ j, raw28461 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28461step0 = (fun i j => raw28461 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28461step0 raw28461; decide +kernel
      have hl : raw28461step0Labels = raw28461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28461 raw28461Labels permutation520 hz
    mixedMoment B raw28461step0 raw28461step0Labels = mixedMoment B raw28461step1 raw28461step1Labels := by
      have hz : ∀ j, raw28461step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28461step1 = (fun i j => raw28461step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28461step1 raw28461step0; decide +kernel
      have hl : raw28461step1Labels = raw28461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28461step0 raw28461step0Labels permutation104 hz
    mixedMoment B raw28461step1 raw28461step1Labels = mixedMoment B raw28461step2 raw28461step2Labels := by
      have hz : ∀ j, raw28461step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28461step2 = (fun i j => raw28461step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28461step2 raw28461step1; decide +kernel
      have hl : raw28461step2Labels = raw28461step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28461step1 raw28461step1Labels permutation20 hz
    mixedMoment B raw28461step2 raw28461step2Labels = mixedMoment B raw28461step3 raw28461step3Labels := by
      have ha : raw28461step3 = (fun i j => raw28461step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28461step3 raw28461step2; decide +kernel
      have hl : raw28461step3Labels = raw28461step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28461step2 raw28461step2Labels permutation6 permutation0
    mixedMoment B raw28461step3 raw28461step3Labels = mixedMoment B raw28461step4 raw28461step4Labels := by
      have ha : raw28461step4 = -raw28461step3 := by apply Matrix.ext; change ∀ i j, raw28461step4 i j = -(raw28461step3 i j); unfold raw28461step4 raw28461step3; decide +kernel
      have hl : raw28461step4Labels = raw28461step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical28462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28462 raw28462Labels = mixedMoment B node1315 node1315Labels := by
  calc
    mixedMoment B raw28462 raw28462Labels = mixedMoment B raw28462step0 raw28462step0Labels := by
      have hz : ∀ j, raw28462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28462step0 = (fun i j => raw28462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28462step0 raw28462; decide +kernel
      have hl : raw28462step0Labels = raw28462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28462 raw28462Labels permutation434 hz
    _ = mixedMoment B node1315 node1315Labels := by rfl

theorem canonical28463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28463 raw28463Labels = mixedMoment B node1961 node1961Labels := by
  calc
    mixedMoment B raw28463 raw28463Labels = mixedMoment B raw28463step0 raw28463step0Labels := by
      have ha : raw28463step0 = (fun i j => raw28463 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28463step0 raw28463; decide +kernel
      have hl : raw28463step0Labels = raw28463Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28463 raw28463Labels permutation646 permutation2
    mixedMoment B raw28463step0 raw28463step0Labels = mixedMoment B raw28463step1 raw28463step1Labels := by
      have ha : raw28463step1 = -raw28463step0 := by apply Matrix.ext; change ∀ i j, raw28463step1 i j = -(raw28463step0 i j); unfold raw28463step1 raw28463step0; decide +kernel
      have hl : raw28463step1Labels = raw28463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1961 node1961Labels := by rfl

theorem canonical28464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28464 raw28464Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw28464 raw28464Labels = mixedMoment B raw28464step0 raw28464step0Labels := by
      have hz : ∀ j, raw28464 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28464step0 = (fun i j => raw28464 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28464step0 raw28464; decide +kernel
      have hl : raw28464step0Labels = raw28464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28464 raw28464Labels permutation520 hz
    mixedMoment B raw28464step0 raw28464step0Labels = mixedMoment B raw28464step1 raw28464step1Labels := by
      have hz : ∀ j, raw28464step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28464step1 = (fun i j => raw28464step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28464step1 raw28464step0; decide +kernel
      have hl : raw28464step1Labels = raw28464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28464step0 raw28464step0Labels permutation104 hz
    mixedMoment B raw28464step1 raw28464step1Labels = mixedMoment B raw28464step2 raw28464step2Labels := by
      have ha : raw28464step2 = (fun i j => raw28464step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28464step2 raw28464step1; decide +kernel
      have hl : raw28464step2Labels = raw28464step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28464step1 raw28464step1Labels permutation31 permutation2
    mixedMoment B raw28464step2 raw28464step2Labels = mixedMoment B raw28464step3 raw28464step3Labels := by
      have ha : raw28464step3 = -raw28464step2 := by apply Matrix.ext; change ∀ i j, raw28464step3 i j = -(raw28464step2 i j); unfold raw28464step3 raw28464step2; decide +kernel
      have hl : raw28464step3Labels = raw28464step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical28465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28465 raw28465Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw28465 raw28465Labels = mixedMoment B raw28465step0 raw28465step0Labels := by
      have hz : ∀ j, raw28465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28465step0 = (fun i j => raw28465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28465step0 raw28465; decide +kernel
      have hl : raw28465step0Labels = raw28465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28465 raw28465Labels permutation434 hz
    _ = mixedMoment B node2879 node2879Labels := by rfl

theorem canonical28494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28494 raw28494Labels = mixedMoment B node2137 node2137Labels := by
  calc
    mixedMoment B raw28494 raw28494Labels = mixedMoment B raw28494step0 raw28494step0Labels := by
      have hz : ∀ j, raw28494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28494step0 = (fun i j => raw28494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28494step0 raw28494; decide +kernel
      have hl : raw28494step0Labels = raw28494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28494 raw28494Labels permutation434 hz
    mixedMoment B raw28494step0 raw28494step0Labels = mixedMoment B raw28494step1 raw28494step1Labels := by
      have hz : ∀ j, raw28494step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28494step1 = (fun i j => raw28494step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28494step1 raw28494step0; decide +kernel
      have hl : raw28494step1Labels = raw28494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28494step0 raw28494step0Labels permutation80 hz
    mixedMoment B raw28494step1 raw28494step1Labels = mixedMoment B raw28494step2 raw28494step2Labels := by
      have ha : raw28494step2 = (fun i j => raw28494step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28494step2 raw28494step1; decide +kernel
      have hl : raw28494step2Labels = raw28494step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28494step1 raw28494step1Labels permutation31 permutation2
    mixedMoment B raw28494step2 raw28494step2Labels = mixedMoment B raw28494step3 raw28494step3Labels := by
      have ha : raw28494step3 = -raw28494step2 := by apply Matrix.ext; change ∀ i j, raw28494step3 i j = -(raw28494step2 i j); unfold raw28494step3 raw28494step2; decide +kernel
      have hl : raw28494step3Labels = raw28494step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2137 node2137Labels := by rfl

theorem canonical28495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28495 raw28495Labels = mixedMoment B node2128 node2128Labels := by
  calc
    mixedMoment B raw28495 raw28495Labels = mixedMoment B raw28495step0 raw28495step0Labels := by
      have hz : ∀ j, raw28495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28495step0 = (fun i j => raw28495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28495step0 raw28495; decide +kernel
      have hl : raw28495step0Labels = raw28495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28495 raw28495Labels permutation434 hz
    mixedMoment B raw28495step0 raw28495step0Labels = mixedMoment B raw28495step1 raw28495step1Labels := by
      have ha : raw28495step1 = (fun i j => raw28495step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28495step1 raw28495step0; decide +kernel
      have hl : raw28495step1Labels = raw28495step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28495step0 raw28495step0Labels permutation149 permutation2
    mixedMoment B raw28495step1 raw28495step1Labels = mixedMoment B raw28495step2 raw28495step2Labels := by
      have ha : raw28495step2 = -raw28495step1 := by apply Matrix.ext; change ∀ i j, raw28495step2 i j = -(raw28495step1 i j); unfold raw28495step2 raw28495step1; decide +kernel
      have hl : raw28495step2Labels = raw28495step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2128 node2128Labels := by rfl

theorem canonical28496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28496 raw28496Labels = mixedMoment B node2128 node2128Labels := by
  calc
    mixedMoment B raw28496 raw28496Labels = mixedMoment B raw28496step0 raw28496step0Labels := by
      have hz : ∀ j, raw28496 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28496step0 = (fun i j => raw28496 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28496step0 raw28496; decide +kernel
      have hl : raw28496step0Labels = raw28496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28496 raw28496Labels permutation346 hz
    mixedMoment B raw28496step0 raw28496step0Labels = mixedMoment B raw28496step1 raw28496step1Labels := by
      have ha : raw28496step1 = (fun i j => raw28496step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28496step1 raw28496step0; decide +kernel
      have hl : raw28496step1Labels = raw28496step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28496step0 raw28496step0Labels permutation149 permutation2
    mixedMoment B raw28496step1 raw28496step1Labels = mixedMoment B raw28496step2 raw28496step2Labels := by
      have ha : raw28496step2 = -raw28496step1 := by apply Matrix.ext; change ∀ i j, raw28496step2 i j = -(raw28496step1 i j); unfold raw28496step2 raw28496step1; decide +kernel
      have hl : raw28496step2Labels = raw28496step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2128 node2128Labels := by rfl

theorem canonical28497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28497 raw28497Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw28497 raw28497Labels = mixedMoment B raw28497step0 raw28497step0Labels := by
      have hz : ∀ j, raw28497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28497step0 = (fun i j => raw28497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28497step0 raw28497; decide +kernel
      have hl : raw28497step0Labels = raw28497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28497 raw28497Labels permutation434 hz
    mixedMoment B raw28497step0 raw28497step0Labels = mixedMoment B raw28497step1 raw28497step1Labels := by
      have hz : ∀ j, raw28497step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28497step1 = (fun i j => raw28497step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28497step1 raw28497step0; decide +kernel
      have hl : raw28497step1Labels = raw28497step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28497step0 raw28497step0Labels permutation80 hz
    mixedMoment B raw28497step1 raw28497step1Labels = mixedMoment B raw28497step2 raw28497step2Labels := by
      have ha : raw28497step2 = (fun i j => raw28497step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28497step2 raw28497step1; decide +kernel
      have hl : raw28497step2Labels = raw28497step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28497step1 raw28497step1Labels permutation31 permutation2
    mixedMoment B raw28497step2 raw28497step2Labels = mixedMoment B raw28497step3 raw28497step3Labels := by
      have ha : raw28497step3 = -raw28497step2 := by apply Matrix.ext; change ∀ i j, raw28497step3 i j = -(raw28497step2 i j); unfold raw28497step3 raw28497step2; decide +kernel
      have hl : raw28497step3Labels = raw28497step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical28498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28498 raw28498Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw28498 raw28498Labels = mixedMoment B raw28498step0 raw28498step0Labels := by
      have hz : ∀ j, raw28498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28498step0 = (fun i j => raw28498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28498step0 raw28498; decide +kernel
      have hl : raw28498step0Labels = raw28498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28498 raw28498Labels permutation434 hz
    mixedMoment B raw28498step0 raw28498step0Labels = mixedMoment B raw28498step1 raw28498step1Labels := by
      have hz : ∀ j, raw28498step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28498step1 = (fun i j => raw28498step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28498step1 raw28498step0; decide +kernel
      have hl : raw28498step1Labels = raw28498step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28498step0 raw28498step0Labels permutation80 hz
    mixedMoment B raw28498step1 raw28498step1Labels = mixedMoment B raw28498step2 raw28498step2Labels := by
      have ha : raw28498step2 = (fun i j => raw28498step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28498step2 raw28498step1; decide +kernel
      have hl : raw28498step2Labels = raw28498step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28498step1 raw28498step1Labels permutation21 permutation4
    _ = mixedMoment B node2687 node2687Labels := by rfl

theorem canonical28499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28499 raw28499Labels = mixedMoment B node2093 node2093Labels := by
  calc
    mixedMoment B raw28499 raw28499Labels = mixedMoment B raw28499step0 raw28499step0Labels := by
      have hz : ∀ j, raw28499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28499step0 = (fun i j => raw28499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28499step0 raw28499; decide +kernel
      have hl : raw28499step0Labels = raw28499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28499 raw28499Labels permutation346 hz
    mixedMoment B raw28499step0 raw28499step0Labels = mixedMoment B raw28499step1 raw28499step1Labels := by
      have ha : raw28499step1 = (fun i j => raw28499step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28499step1 raw28499step0; decide +kernel
      have hl : raw28499step1Labels = raw28499step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28499step0 raw28499step0Labels permutation151 permutation2
    mixedMoment B raw28499step1 raw28499step1Labels = mixedMoment B raw28499step2 raw28499step2Labels := by
      have ha : raw28499step2 = -raw28499step1 := by apply Matrix.ext; change ∀ i j, raw28499step2 i j = -(raw28499step1 i j); unfold raw28499step2 raw28499step1; decide +kernel
      have hl : raw28499step2Labels = raw28499step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2093 node2093Labels := by rfl

theorem canonical28500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28500 raw28500Labels = mixedMoment B node2085 node2085Labels := by
  calc
    mixedMoment B raw28500 raw28500Labels = mixedMoment B raw28500step0 raw28500step0Labels := by
      have ha : raw28500step0 = (fun i j => raw28500 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28500step0 raw28500; decide +kernel
      have hl : raw28500step0Labels = raw28500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28500 raw28500Labels permutation686 permutation2
    mixedMoment B raw28500step0 raw28500step0Labels = mixedMoment B raw28500step1 raw28500step1Labels := by
      have ha : raw28500step1 = -raw28500step0 := by apply Matrix.ext; change ∀ i j, raw28500step1 i j = -(raw28500step0 i j); unfold raw28500step1 raw28500step0; decide +kernel
      have hl : raw28500step1Labels = raw28500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2085 node2085Labels := by rfl

theorem canonical28501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28501 raw28501Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw28501 raw28501Labels = mixedMoment B raw28501step0 raw28501step0Labels := by
      have hz : ∀ j, raw28501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28501step0 = (fun i j => raw28501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28501step0 raw28501; decide +kernel
      have hl : raw28501step0Labels = raw28501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28501 raw28501Labels permutation346 hz
    mixedMoment B raw28501step0 raw28501step0Labels = mixedMoment B raw28501step1 raw28501step1Labels := by
      have ha : raw28501step1 = (fun i j => raw28501step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28501step1 raw28501step0; decide +kernel
      have hl : raw28501step1Labels = raw28501step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28501step0 raw28501step0Labels permutation149 permutation2
    mixedMoment B raw28501step1 raw28501step1Labels = mixedMoment B raw28501step2 raw28501step2Labels := by
      have ha : raw28501step2 = -raw28501step1 := by apply Matrix.ext; change ∀ i j, raw28501step2 i j = -(raw28501step1 i j); unfold raw28501step2 raw28501step1; decide +kernel
      have hl : raw28501step2Labels = raw28501step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2101 node2101Labels := by rfl

theorem canonical28502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28502 raw28502Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw28502 raw28502Labels = mixedMoment B raw28502step0 raw28502step0Labels := by
      have hz : ∀ j, raw28502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28502step0 = (fun i j => raw28502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28502step0 raw28502; decide +kernel
      have hl : raw28502step0Labels = raw28502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28502 raw28502Labels permutation346 hz
    mixedMoment B raw28502step0 raw28502step0Labels = mixedMoment B raw28502step1 raw28502step1Labels := by
      have ha : raw28502step1 = (fun i j => raw28502step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28502step1 raw28502step0; decide +kernel
      have hl : raw28502step1Labels = raw28502step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28502step0 raw28502step0Labels permutation145 permutation2
    mixedMoment B raw28502step1 raw28502step1Labels = mixedMoment B raw28502step2 raw28502step2Labels := by
      have ha : raw28502step2 = -raw28502step1 := by apply Matrix.ext; change ∀ i j, raw28502step2 i j = -(raw28502step1 i j); unfold raw28502step2 raw28502step1; decide +kernel
      have hl : raw28502step2Labels = raw28502step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical28503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28503 raw28503Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw28503 raw28503Labels = mixedMoment B raw28503step0 raw28503step0Labels := by
      have hz : ∀ j, raw28503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28503step0 = (fun i j => raw28503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28503step0 raw28503; decide +kernel
      have hl : raw28503step0Labels = raw28503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28503 raw28503Labels permutation346 hz
    mixedMoment B raw28503step0 raw28503step0Labels = mixedMoment B raw28503step1 raw28503step1Labels := by
      have ha : raw28503step1 = (fun i j => raw28503step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28503step1 raw28503step0; decide +kernel
      have hl : raw28503step1Labels = raw28503step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28503step0 raw28503step0Labels permutation151 permutation2
    mixedMoment B raw28503step1 raw28503step1Labels = mixedMoment B raw28503step2 raw28503step2Labels := by
      have ha : raw28503step2 = -raw28503step1 := by apply Matrix.ext; change ∀ i j, raw28503step2 i j = -(raw28503step1 i j); unfold raw28503step2 raw28503step1; decide +kernel
      have hl : raw28503step2Labels = raw28503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3570 node3570Labels := by rfl

theorem canonical28508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28508 raw28508Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw28508 raw28508Labels = mixedMoment B raw28508step0 raw28508step0Labels := by
      have hz : ∀ j, raw28508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28508step0 = (fun i j => raw28508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28508step0 raw28508; decide +kernel
      have hl : raw28508step0Labels = raw28508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28508 raw28508Labels permutation346 hz
    mixedMoment B raw28508step0 raw28508step0Labels = mixedMoment B raw28508step1 raw28508step1Labels := by
      have ha : raw28508step1 = (fun i j => raw28508step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28508step1 raw28508step0; decide +kernel
      have hl : raw28508step1Labels = raw28508step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28508step0 raw28508step0Labels permutation151 permutation2
    mixedMoment B raw28508step1 raw28508step1Labels = mixedMoment B raw28508step2 raw28508step2Labels := by
      have ha : raw28508step2 = -raw28508step1 := by apply Matrix.ext; change ∀ i j, raw28508step2 i j = -(raw28508step1 i j); unfold raw28508step2 raw28508step1; decide +kernel
      have hl : raw28508step2Labels = raw28508step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3811 node3811Labels := by rfl

theorem canonical28509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28509 raw28509Labels = mixedMoment B node2606 node2606Labels := by
  calc
    mixedMoment B raw28509 raw28509Labels = mixedMoment B raw28509step0 raw28509step0Labels := by
      have ha : raw28509step0 = (fun i j => raw28509 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28509step0 raw28509; decide +kernel
      have hl : raw28509step0Labels = raw28509Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28509 raw28509Labels permutation158 permutation2
    _ = mixedMoment B node2606 node2606Labels := by rfl

theorem canonical28510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28510 raw28510Labels = mixedMoment B node2629 node2629Labels := by
  calc
    mixedMoment B raw28510 raw28510Labels = mixedMoment B raw28510step0 raw28510step0Labels := by
      have hz : ∀ j, raw28510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28510step0 = (fun i j => raw28510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28510step0 raw28510; decide +kernel
      have hl : raw28510step0Labels = raw28510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28510 raw28510Labels permutation346 hz
    _ = mixedMoment B node2629 node2629Labels := by rfl

theorem canonical28511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28511 raw28511Labels = mixedMoment B node2608 node2608Labels := by
  calc
    mixedMoment B raw28511 raw28511Labels = mixedMoment B raw28511step0 raw28511step0Labels := by
      have hz : ∀ j, raw28511 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28511step0 = (fun i j => raw28511 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28511step0 raw28511; decide +kernel
      have hl : raw28511step0Labels = raw28511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28511 raw28511Labels permutation346 hz
    _ = mixedMoment B node2608 node2608Labels := by rfl

theorem canonical28512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28512 raw28512Labels = mixedMoment B node2038 node2038Labels := by
  calc
    mixedMoment B raw28512 raw28512Labels = mixedMoment B raw28512step0 raw28512step0Labels := by
      have hz : ∀ j, raw28512 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28512step0 = (fun i j => raw28512 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28512step0 raw28512; decide +kernel
      have hl : raw28512step0Labels = raw28512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28512 raw28512Labels permutation346 hz
    mixedMoment B raw28512step0 raw28512step0Labels = mixedMoment B raw28512step1 raw28512step1Labels := by
      have ha : raw28512step1 = (fun i j => raw28512step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28512step1 raw28512step0; decide +kernel
      have hl : raw28512step1Labels = raw28512step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28512step0 raw28512step0Labels permutation151 permutation2
    mixedMoment B raw28512step1 raw28512step1Labels = mixedMoment B raw28512step2 raw28512step2Labels := by
      have ha : raw28512step2 = -raw28512step1 := by apply Matrix.ext; change ∀ i j, raw28512step2 i j = -(raw28512step1 i j); unfold raw28512step2 raw28512step1; decide +kernel
      have hl : raw28512step2Labels = raw28512step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2038 node2038Labels := by rfl

theorem canonical28513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28513 raw28513Labels = mixedMoment B node2030 node2030Labels := by
  calc
    mixedMoment B raw28513 raw28513Labels = mixedMoment B raw28513step0 raw28513step0Labels := by
      have ha : raw28513step0 = (fun i j => raw28513 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28513step0 raw28513; decide +kernel
      have hl : raw28513step0Labels = raw28513Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28513 raw28513Labels permutation686 permutation2
    mixedMoment B raw28513step0 raw28513step0Labels = mixedMoment B raw28513step1 raw28513step1Labels := by
      have ha : raw28513step1 = -raw28513step0 := by apply Matrix.ext; change ∀ i j, raw28513step1 i j = -(raw28513step0 i j); unfold raw28513step1 raw28513step0; decide +kernel
      have hl : raw28513step1Labels = raw28513step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2030 node2030Labels := by rfl

theorem canonical28514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28514 raw28514Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw28514 raw28514Labels = mixedMoment B raw28514step0 raw28514step0Labels := by
      have hz : ∀ j, raw28514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28514step0 = (fun i j => raw28514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28514step0 raw28514; decide +kernel
      have hl : raw28514step0Labels = raw28514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28514 raw28514Labels permutation346 hz
    mixedMoment B raw28514step0 raw28514step0Labels = mixedMoment B raw28514step1 raw28514step1Labels := by
      have ha : raw28514step1 = (fun i j => raw28514step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28514step1 raw28514step0; decide +kernel
      have hl : raw28514step1Labels = raw28514step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28514step0 raw28514step0Labels permutation149 permutation2
    mixedMoment B raw28514step1 raw28514step1Labels = mixedMoment B raw28514step2 raw28514step2Labels := by
      have ha : raw28514step2 = -raw28514step1 := by apply Matrix.ext; change ∀ i j, raw28514step2 i j = -(raw28514step1 i j); unfold raw28514step2 raw28514step1; decide +kernel
      have hl : raw28514step2Labels = raw28514step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2048 node2048Labels := by rfl

theorem canonical28515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28515 raw28515Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw28515 raw28515Labels = mixedMoment B raw28515step0 raw28515step0Labels := by
      have hz : ∀ j, raw28515 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28515step0 = (fun i j => raw28515 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28515step0 raw28515; decide +kernel
      have hl : raw28515step0Labels = raw28515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28515 raw28515Labels permutation520 hz
    mixedMoment B raw28515step0 raw28515step0Labels = mixedMoment B raw28515step1 raw28515step1Labels := by
      have hz : ∀ j, raw28515step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28515step1 = (fun i j => raw28515step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28515step1 raw28515step0; decide +kernel
      have hl : raw28515step1Labels = raw28515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28515step0 raw28515step0Labels permutation80 hz
    mixedMoment B raw28515step1 raw28515step1Labels = mixedMoment B raw28515step2 raw28515step2Labels := by
      have ha : raw28515step2 = (fun i j => raw28515step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28515step2 raw28515step1; decide +kernel
      have hl : raw28515step2Labels = raw28515step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28515step1 raw28515step1Labels permutation31 permutation2
    mixedMoment B raw28515step2 raw28515step2Labels = mixedMoment B raw28515step3 raw28515step3Labels := by
      have ha : raw28515step3 = -raw28515step2 := by apply Matrix.ext; change ∀ i j, raw28515step3 i j = -(raw28515step2 i j); unfold raw28515step3 raw28515step2; decide +kernel
      have hl : raw28515step3Labels = raw28515step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical28516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28516 raw28516Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw28516 raw28516Labels = mixedMoment B raw28516step0 raw28516step0Labels := by
      have hz : ∀ j, raw28516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28516step0 = (fun i j => raw28516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28516step0 raw28516; decide +kernel
      have hl : raw28516step0Labels = raw28516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28516 raw28516Labels permutation346 hz
    mixedMoment B raw28516step0 raw28516step0Labels = mixedMoment B raw28516step1 raw28516step1Labels := by
      have ha : raw28516step1 = (fun i j => raw28516step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28516step1 raw28516step0; decide +kernel
      have hl : raw28516step1Labels = raw28516step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28516step0 raw28516step0Labels permutation151 permutation2
    mixedMoment B raw28516step1 raw28516step1Labels = mixedMoment B raw28516step2 raw28516step2Labels := by
      have ha : raw28516step2 = -raw28516step1 := by apply Matrix.ext; change ∀ i j, raw28516step2 i j = -(raw28516step1 i j); unfold raw28516step2 raw28516step1; decide +kernel
      have hl : raw28516step2Labels = raw28516step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3538 node3538Labels := by rfl

theorem canonical28521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28521 raw28521Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw28521 raw28521Labels = mixedMoment B raw28521step0 raw28521step0Labels := by
      have ha : raw28521step0 = (fun i j => raw28521 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28521step0 raw28521; decide +kernel
      have hl : raw28521step0Labels = raw28521Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28521 raw28521Labels permutation682 permutation2
    mixedMoment B raw28521step0 raw28521step0Labels = mixedMoment B raw28521step1 raw28521step1Labels := by
      have ha : raw28521step1 = -raw28521step0 := by apply Matrix.ext; change ∀ i j, raw28521step1 i j = -(raw28521step0 i j); unfold raw28521step1 raw28521step0; decide +kernel
      have hl : raw28521step1Labels = raw28521step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3799 node3799Labels := by rfl

theorem canonical28522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28522 raw28522Labels = mixedMoment B node2613 node2613Labels := by
  calc
    mixedMoment B raw28522 raw28522Labels = mixedMoment B raw28522step0 raw28522step0Labels := by
      have ha : raw28522step0 = (fun i j => raw28522 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28522step0 raw28522; decide +kernel
      have hl : raw28522step0Labels = raw28522Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28522 raw28522Labels permutation158 permutation2
    _ = mixedMoment B node2613 node2613Labels := by rfl

theorem canonical28523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28523 raw28523Labels = mixedMoment B node2613 node2613Labels := by
  calc
    _ = mixedMoment B node2613 node2613Labels := by rfl

theorem canonical28524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28524 raw28524Labels = mixedMoment B node2609 node2609Labels := by
  calc
    _ = mixedMoment B node2609 node2609Labels := by rfl

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

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

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

theorem sound939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node939 node939Labels = Sparse.eval nodeValue939 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 939) = mixedMoment B node939 node939Labels := rfl
  simpa [nodeValue939, Sparse.eval] using hc.symm

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

theorem sound1315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1315 node1315Labels = Sparse.eval nodeValue1315 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1315) = mixedMoment B node1315 node1315Labels := rfl
  simpa [nodeValue1315, Sparse.eval] using hc.symm

theorem sound1325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1325 node1325Labels = Sparse.eval nodeValue1325 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1325) = mixedMoment B node1325 node1325Labels := rfl
  simpa [nodeValue1325, Sparse.eval] using hc.symm

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

theorem sound1676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1676 node1676Labels = Sparse.eval nodeValue1676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1676) = mixedMoment B node1676 node1676Labels := rfl
  simpa [nodeValue1676, Sparse.eval] using hc.symm

theorem sound1694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1694 node1694Labels = Sparse.eval nodeValue1694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1694) = mixedMoment B node1694 node1694Labels := rfl
  simpa [nodeValue1694, Sparse.eval] using hc.symm

theorem sound1695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1695 node1695Labels = Sparse.eval nodeValue1695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1695) = mixedMoment B node1695 node1695Labels := rfl
  simpa [nodeValue1695, Sparse.eval] using hc.symm

theorem sound1720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1720 node1720Labels = Sparse.eval nodeValue1720 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1720) = mixedMoment B node1720 node1720Labels := rfl
  simpa [nodeValue1720, Sparse.eval] using hc.symm

theorem sound1722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1722 node1722Labels = Sparse.eval nodeValue1722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1722) = mixedMoment B node1722 node1722Labels := rfl
  simpa [nodeValue1722, Sparse.eval] using hc.symm

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

theorem sound1729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1729 node1729Labels = Sparse.eval nodeValue1729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1729) = mixedMoment B node1729 node1729Labels := rfl
  simpa [nodeValue1729, Sparse.eval] using hc.symm

theorem sound1742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1742 node1742Labels = Sparse.eval nodeValue1742 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1742) = mixedMoment B node1742 node1742Labels := rfl
  simpa [nodeValue1742, Sparse.eval] using hc.symm

theorem sound1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1743 node1743Labels = Sparse.eval nodeValue1743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1743) = mixedMoment B node1743 node1743Labels := rfl
  simpa [nodeValue1743, Sparse.eval] using hc.symm

theorem sound1746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1746 node1746Labels = Sparse.eval nodeValue1746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1746) = mixedMoment B node1746 node1746Labels := rfl
  simpa [nodeValue1746, Sparse.eval] using hc.symm

theorem sound1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1748 node1748Labels = Sparse.eval nodeValue1748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1748) = mixedMoment B node1748 node1748Labels := rfl
  simpa [nodeValue1748, Sparse.eval] using hc.symm

theorem sound1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1756 node1756Labels = Sparse.eval nodeValue1756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1756) = mixedMoment B node1756 node1756Labels := rfl
  simpa [nodeValue1756, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1912 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1912 node1912Labels = 0 := by
  exact mixedMoment_order_one B hB node1912 node1912Labels 1
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

theorem sound1898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1898 node1898Labels = Sparse.eval nodeValue1898 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1898) = mixedMoment B node1898 node1898Labels := rfl
  simpa [nodeValue1898, Sparse.eval] using hc.symm

theorem sound1901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1901 node1901Labels = Sparse.eval nodeValue1901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1901) = mixedMoment B node1901 node1901Labels := rfl
  simpa [nodeValue1901, Sparse.eval] using hc.symm

theorem sound1912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1912 node1912Labels = Sparse.eval nodeValue1912 (mixedVector B) := by
  simpa only [nodeValue1912, Sparse.eval_nil] using zero1912 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1961 node1961Labels = Sparse.eval nodeValue1961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1961) = mixedMoment B node1961 node1961Labels := rfl
  simpa [nodeValue1961, Sparse.eval] using hc.symm

theorem sound1970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1970 node1970Labels = Sparse.eval nodeValue1970 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1970) = mixedMoment B node1970 node1970Labels := rfl
  simpa [nodeValue1970, Sparse.eval] using hc.symm

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

theorem sound2030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2030 node2030Labels = Sparse.eval nodeValue2030 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2030) = mixedMoment B node2030 node2030Labels := rfl
  simpa [nodeValue2030, Sparse.eval] using hc.symm

theorem sound2032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2032 node2032Labels = Sparse.eval nodeValue2032 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2032) = mixedMoment B node2032 node2032Labels := rfl
  simpa [nodeValue2032, Sparse.eval] using hc.symm

theorem sound2038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2038 node2038Labels = Sparse.eval nodeValue2038 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2038) = mixedMoment B node2038 node2038Labels := rfl
  simpa [nodeValue2038, Sparse.eval] using hc.symm

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

theorem zero2066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2066 node2066Labels = 0 := by
  exact mixedMoment_order_one B hB node2066 node2066Labels 1
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

theorem sound2048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2048 node2048Labels = Sparse.eval nodeValue2048 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2048) = mixedMoment B node2048 node2048Labels := rfl
  simpa [nodeValue2048, Sparse.eval] using hc.symm

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

theorem sound2066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2066 node2066Labels = Sparse.eval nodeValue2066 (mixedVector B) := by
  simpa only [nodeValue2066, Sparse.eval_nil] using zero2066 B _hB _hF

theorem sound2076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2076 node2076Labels = Sparse.eval nodeValue2076 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2076) = mixedMoment B node2076 node2076Labels := rfl
  simpa [nodeValue2076, Sparse.eval] using hc.symm

theorem sound2080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2080 node2080Labels = Sparse.eval nodeValue2080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2080) = mixedMoment B node2080 node2080Labels := rfl
  simpa [nodeValue2080, Sparse.eval] using hc.symm

theorem sound2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2082 node2082Labels = Sparse.eval nodeValue2082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2082) = mixedMoment B node2082 node2082Labels := rfl
  simpa [nodeValue2082, Sparse.eval] using hc.symm

theorem sound2085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2085 node2085Labels = Sparse.eval nodeValue2085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2085) = mixedMoment B node2085 node2085Labels := rfl
  simpa [nodeValue2085, Sparse.eval] using hc.symm

theorem sound2087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2087 node2087Labels = Sparse.eval nodeValue2087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2087) = mixedMoment B node2087 node2087Labels := rfl
  simpa [nodeValue2087, Sparse.eval] using hc.symm

theorem sound2093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2093 node2093Labels = Sparse.eval nodeValue2093 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2093) = mixedMoment B node2093 node2093Labels := rfl
  simpa [nodeValue2093, Sparse.eval] using hc.symm

theorem sound2101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2101 node2101Labels = Sparse.eval nodeValue2101 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2101) = mixedMoment B node2101 node2101Labels := rfl
  simpa [nodeValue2101, Sparse.eval] using hc.symm

theorem sound2102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2102 node2102Labels = Sparse.eval nodeValue2102 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2102) = mixedMoment B node2102 node2102Labels := rfl
  simpa [nodeValue2102, Sparse.eval] using hc.symm

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

theorem sound2128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2128 node2128Labels = Sparse.eval nodeValue2128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2128) = mixedMoment B node2128 node2128Labels := rfl
  simpa [nodeValue2128, Sparse.eval] using hc.symm

theorem sound2130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2130 node2130Labels = Sparse.eval nodeValue2130 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2130) = mixedMoment B node2130 node2130Labels := rfl
  simpa [nodeValue2130, Sparse.eval] using hc.symm

theorem sound2137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2137 node2137Labels = Sparse.eval nodeValue2137 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2137) = mixedMoment B node2137 node2137Labels := rfl
  simpa [nodeValue2137, Sparse.eval] using hc.symm

theorem sound2153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2153 node2153Labels = Sparse.eval nodeValue2153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2153) = mixedMoment B node2153 node2153Labels := rfl
  simpa [nodeValue2153, Sparse.eval] using hc.symm

theorem sound2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2169 node2169Labels = Sparse.eval nodeValue2169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2169) = mixedMoment B node2169 node2169Labels := rfl
  simpa [nodeValue2169, Sparse.eval] using hc.symm

theorem sound2175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2175 node2175Labels = Sparse.eval nodeValue2175 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2175) = mixedMoment B node2175 node2175Labels := rfl
  simpa [nodeValue2175, Sparse.eval] using hc.symm

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

theorem sound2186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2186 node2186Labels = Sparse.eval nodeValue2186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2186) = mixedMoment B node2186 node2186Labels := rfl
  simpa [nodeValue2186, Sparse.eval] using hc.symm

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2207 node2207Labels = Sparse.eval nodeValue2207 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2207) = mixedMoment B node2207 node2207Labels := rfl
  simpa [nodeValue2207, Sparse.eval] using hc.symm

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

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

theorem sound2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2276 node2276Labels = Sparse.eval nodeValue2276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2276) = mixedMoment B node2276 node2276Labels := rfl
  simpa [nodeValue2276, Sparse.eval] using hc.symm

theorem sound2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = Sparse.eval nodeValue2293 (mixedVector B) := by
  simpa only [nodeValue2293, Sparse.eval_nil] using zero2293 B _hB _hF

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

theorem sound2390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2390 node2390Labels = Sparse.eval nodeValue2390 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2390) = mixedMoment B node2390 node2390Labels := rfl
  simpa [nodeValue2390, Sparse.eval] using hc.symm

theorem sound2393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2393 node2393Labels = Sparse.eval nodeValue2393 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2393) = mixedMoment B node2393 node2393Labels := rfl
  simpa [nodeValue2393, Sparse.eval] using hc.symm

theorem sound2395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2395 node2395Labels = Sparse.eval nodeValue2395 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2395) = mixedMoment B node2395 node2395Labels := rfl
  simpa [nodeValue2395, Sparse.eval] using hc.symm

theorem sound2404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2404 node2404Labels = Sparse.eval nodeValue2404 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2404) = mixedMoment B node2404 node2404Labels := rfl
  simpa [nodeValue2404, Sparse.eval] using hc.symm

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

theorem sound2469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2469 node2469Labels = Sparse.eval nodeValue2469 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2469) = mixedMoment B node2469 node2469Labels := rfl
  simpa [nodeValue2469, Sparse.eval] using hc.symm

theorem sound2492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2492 node2492Labels = Sparse.eval nodeValue2492 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2492) = mixedMoment B node2492 node2492Labels := rfl
  simpa [nodeValue2492, Sparse.eval] using hc.symm

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

theorem sound2606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2606 node2606Labels = Sparse.eval nodeValue2606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2606) = mixedMoment B node2606 node2606Labels := rfl
  simpa [nodeValue2606, Sparse.eval] using hc.symm

theorem sound2608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2608 node2608Labels = Sparse.eval nodeValue2608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2608) = mixedMoment B node2608 node2608Labels := rfl
  simpa [nodeValue2608, Sparse.eval] using hc.symm

theorem sound2609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2609 node2609Labels = Sparse.eval nodeValue2609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2609) = mixedMoment B node2609 node2609Labels := rfl
  simpa [nodeValue2609, Sparse.eval] using hc.symm

theorem sound2613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2613 node2613Labels = Sparse.eval nodeValue2613 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2613) = mixedMoment B node2613 node2613Labels := rfl
  simpa [nodeValue2613, Sparse.eval] using hc.symm

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

theorem sound2629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2629 node2629Labels = Sparse.eval nodeValue2629 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2629) = mixedMoment B node2629 node2629Labels := rfl
  simpa [nodeValue2629, Sparse.eval] using hc.symm

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

theorem sound2678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2678 node2678Labels = Sparse.eval nodeValue2678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2678) = mixedMoment B node2678 node2678Labels := rfl
  simpa [nodeValue2678, Sparse.eval] using hc.symm

theorem sound2687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2687 node2687Labels = Sparse.eval nodeValue2687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2687) = mixedMoment B node2687 node2687Labels := rfl
  simpa [nodeValue2687, Sparse.eval] using hc.symm

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

theorem sound2706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2706 node2706Labels = Sparse.eval nodeValue2706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2706) = mixedMoment B node2706 node2706Labels := rfl
  simpa [nodeValue2706, Sparse.eval] using hc.symm

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

theorem sound2744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2744 node2744Labels = Sparse.eval nodeValue2744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2744) = mixedMoment B node2744 node2744Labels := rfl
  simpa [nodeValue2744, Sparse.eval] using hc.symm

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

theorem sound2811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2811 node2811Labels = Sparse.eval nodeValue2811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2811) = mixedMoment B node2811 node2811Labels := rfl
  simpa [nodeValue2811, Sparse.eval] using hc.symm

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

theorem sound2820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2820 node2820Labels = Sparse.eval nodeValue2820 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2820) = mixedMoment B node2820 node2820Labels := rfl
  simpa [nodeValue2820, Sparse.eval] using hc.symm

theorem sound2879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2879 node2879Labels = Sparse.eval nodeValue2879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2879) = mixedMoment B node2879 node2879Labels := rfl
  simpa [nodeValue2879, Sparse.eval] using hc.symm

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

theorem sound2886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2886 node2886Labels = Sparse.eval nodeValue2886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2886) = mixedMoment B node2886 node2886Labels := rfl
  simpa [nodeValue2886, Sparse.eval] using hc.symm

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

theorem sound3266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3266 node3266Labels = Sparse.eval nodeValue3266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3266) = mixedMoment B node3266 node3266Labels := rfl
  simpa [nodeValue3266, Sparse.eval] using hc.symm

theorem sound3277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3277 node3277Labels = Sparse.eval nodeValue3277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3277) = mixedMoment B node3277 node3277Labels := rfl
  simpa [nodeValue3277, Sparse.eval] using hc.symm

theorem sound3302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3302 node3302Labels = Sparse.eval nodeValue3302 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3302) = mixedMoment B node3302 node3302Labels := rfl
  simpa [nodeValue3302, Sparse.eval] using hc.symm

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

theorem sound3413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3413 node3413Labels = Sparse.eval nodeValue3413 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3413) = mixedMoment B node3413 node3413Labels := rfl
  simpa [nodeValue3413, Sparse.eval] using hc.symm

theorem sound3423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3423 node3423Labels = Sparse.eval nodeValue3423 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3423) = mixedMoment B node3423 node3423Labels := rfl
  simpa [nodeValue3423, Sparse.eval] using hc.symm

theorem sound3451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3451 node3451Labels = Sparse.eval nodeValue3451 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3451) = mixedMoment B node3451 node3451Labels := rfl
  simpa [nodeValue3451, Sparse.eval] using hc.symm

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

theorem sound3460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3460 node3460Labels = Sparse.eval nodeValue3460 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3460) = mixedMoment B node3460 node3460Labels := rfl
  simpa [nodeValue3460, Sparse.eval] using hc.symm

theorem sound3471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3471 node3471Labels = Sparse.eval nodeValue3471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3471) = mixedMoment B node3471 node3471Labels := rfl
  simpa [nodeValue3471, Sparse.eval] using hc.symm

theorem sound3472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3472 node3472Labels = Sparse.eval nodeValue3472 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3472) = mixedMoment B node3472 node3472Labels := rfl
  simpa [nodeValue3472, Sparse.eval] using hc.symm

theorem sound3485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3485 node3485Labels = Sparse.eval nodeValue3485 (mixedVector B) := by
  simpa only [nodeValue3485, Sparse.eval_nil] using zero3485 B _hB _hF

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

theorem sound3523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3523 node3523Labels = Sparse.eval nodeValue3523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3523) = mixedMoment B node3523 node3523Labels := rfl
  simpa [nodeValue3523, Sparse.eval] using hc.symm

theorem sound3538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3538 node3538Labels = Sparse.eval nodeValue3538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3538) = mixedMoment B node3538 node3538Labels := rfl
  simpa [nodeValue3538, Sparse.eval] using hc.symm

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3549 node3549Labels = Sparse.eval nodeValue3549 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3549) = mixedMoment B node3549 node3549Labels := rfl
  simpa [nodeValue3549, Sparse.eval] using hc.symm

theorem sound3565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3565 node3565Labels = Sparse.eval nodeValue3565 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3565) = mixedMoment B node3565 node3565Labels := rfl
  simpa [nodeValue3565, Sparse.eval] using hc.symm

theorem sound3570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3570 node3570Labels = Sparse.eval nodeValue3570 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3570) = mixedMoment B node3570 node3570Labels := rfl
  simpa [nodeValue3570, Sparse.eval] using hc.symm

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

theorem sound3624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3624 node3624Labels = Sparse.eval nodeValue3624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3624) = mixedMoment B node3624 node3624Labels := rfl
  simpa [nodeValue3624, Sparse.eval] using hc.symm

theorem sound3631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3631 node3631Labels = Sparse.eval nodeValue3631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3631) = mixedMoment B node3631 node3631Labels := rfl
  simpa [nodeValue3631, Sparse.eval] using hc.symm

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

theorem sound3771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3771 node3771Labels = Sparse.eval nodeValue3771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3771) = mixedMoment B node3771 node3771Labels := rfl
  simpa [nodeValue3771, Sparse.eval] using hc.symm

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

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

theorem sound3811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3811 node3811Labels = Sparse.eval nodeValue3811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3811) = mixedMoment B node3811 node3811Labels := rfl
  simpa [nodeValue3811, Sparse.eval] using hc.symm

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

theorem sound4079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4079 node4079Labels = Sparse.eval nodeValue4079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4079) = mixedMoment B node4079 node4079Labels := rfl
  simpa [nodeValue4079, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

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

theorem sound4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4090 node4090Labels = Sparse.eval nodeValue4090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4090) = mixedMoment B node4090 node4090Labels := rfl
  simpa [nodeValue4090, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources61
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1981 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1981 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1981 + difference 0 0) (sourceB1981 + difference 0 0) sourceC1981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2393) := by
    have ha : (tripleCharges (sourceA1981 + difference 0 0) (sourceB1981 + difference 0 0) sourceC1981) = raw28168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1981 sourceB1981 sourceC1981 difference raw28168; decide +kernel
    rw [ha]
    exact (canonical28168 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1981 + difference 0 1) (sourceB1981 + difference 1 0) sourceC1981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2395) := by
    have ha : (tripleCharges (sourceA1981 + difference 0 1) (sourceB1981 + difference 1 0) sourceC1981) = raw28169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1981 sourceB1981 sourceC1981 difference raw28169; decide +kernel
    rw [ha]
    exact (canonical28169 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1981 + difference 0 2) (sourceB1981 + difference 2 0) sourceC1981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2390) := by
    have ha : (tripleCharges (sourceA1981 + difference 0 2) (sourceB1981 + difference 2 0) sourceC1981) = raw28170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1981 sourceB1981 sourceC1981 difference raw28170; decide +kernel
    rw [ha]
    exact (canonical28170 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1981 + difference 0 3) (sourceB1981 + difference 3 0) sourceC1981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2404) := by
    have ha : (tripleCharges (sourceA1981 + difference 0 3) (sourceB1981 + difference 3 0) sourceC1981) = raw28171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1981 sourceB1981 sourceC1981 difference raw28171; decide +kernel
    rw [ha]
    exact (canonical28171 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1981 + difference 0 4) (sourceB1981 + difference 4 0) sourceC1981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA1981 + difference 0 4) (sourceB1981 + difference 4 0) sourceC1981) = raw28172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1981 sourceB1981 sourceC1981 difference raw28172; decide +kernel
    rw [ha]
    exact (canonical28172 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1981 + difference 0 5) (sourceB1981 + difference 5 0) sourceC1981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA1981 + difference 0 5) (sourceB1981 + difference 5 0) sourceC1981) = raw28173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1981 sourceB1981 sourceC1981 difference raw28173; decide +kernel
    rw [ha]
    exact (canonical28173 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1981 + sourceB1981) sourceC1981) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1981 + sourceB1981) sourceC1981) = raw28174 := by
      apply Matrix.ext; unfold doubleCharges sourceA1981 sourceB1981 sourceC1981 raw28174; decide +kernel
    rw [ha]
    exact (canonical28174 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1981 sourceB1981 sourceC1981
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1981, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources62
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1987 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1987 + difference 0 0) (sourceB1987 + difference 0 0) sourceC1987) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA1987 + difference 0 0) (sourceB1987 + difference 0 0) sourceC1987) = raw20238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1987 sourceB1987 sourceC1987 difference raw20238; decide +kernel
    rw [ha]
    exact (canonical20238 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1987 + difference 0 1) (sourceB1987 + difference 1 0) sourceC1987) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1901) := by
    have ha : (tripleCharges (sourceA1987 + difference 0 1) (sourceB1987 + difference 1 0) sourceC1987) = raw28198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1987 sourceB1987 sourceC1987 difference raw28198; decide +kernel
    rw [ha]
    exact (canonical28198 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1987 + difference 0 2) (sourceB1987 + difference 2 0) sourceC1987) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1912) := by
    have ha : (tripleCharges (sourceA1987 + difference 0 2) (sourceB1987 + difference 2 0) sourceC1987) = raw28199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1987 sourceB1987 sourceC1987 difference raw28199; decide +kernel
    rw [ha]
    exact (canonical28199 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1987 + difference 0 3) (sourceB1987 + difference 3 0) sourceC1987) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1912) := by
    have ha : (tripleCharges (sourceA1987 + difference 0 3) (sourceB1987 + difference 3 0) sourceC1987) = raw28200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1987 sourceB1987 sourceC1987 difference raw28200; decide +kernel
    rw [ha]
    exact (canonical28200 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1987 + difference 0 4) (sourceB1987 + difference 4 0) sourceC1987) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1987 + difference 0 4) (sourceB1987 + difference 4 0) sourceC1987) = raw28201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1987 sourceB1987 sourceC1987 difference raw28201; decide +kernel
    rw [ha]
    exact (canonical28201 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1987 + difference 0 5) (sourceB1987 + difference 5 0) sourceC1987) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA1987 + difference 0 5) (sourceB1987 + difference 5 0) sourceC1987) = raw28202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1987 sourceB1987 sourceC1987 difference raw28202; decide +kernel
    rw [ha]
    exact (canonical28202 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1987 + sourceB1987) sourceC1987) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1987 + sourceB1987) sourceC1987) = raw20243 := by
      apply Matrix.ext; unfold doubleCharges sourceA1987 sourceB1987 sourceC1987 raw20243; decide +kernel
    rw [ha]
    exact (canonical20243 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1987 sourceB1987 sourceC1987
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1987, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1991 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1991 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1991 + difference 0 0) (sourceB1991 + difference 0 0) sourceC1991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2080) := by
    have ha : (tripleCharges (sourceA1991 + difference 0 0) (sourceB1991 + difference 0 0) sourceC1991) = raw28212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1991 sourceB1991 sourceC1991 difference raw28212; decide +kernel
    rw [ha]
    exact (canonical28212 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1991 + difference 0 1) (sourceB1991 + difference 1 0) sourceC1991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA1991 + difference 0 1) (sourceB1991 + difference 1 0) sourceC1991) = raw28213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1991 sourceB1991 sourceC1991 difference raw28213; decide +kernel
    rw [ha]
    exact (canonical28213 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1991 + difference 0 2) (sourceB1991 + difference 2 0) sourceC1991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2102) := by
    have ha : (tripleCharges (sourceA1991 + difference 0 2) (sourceB1991 + difference 2 0) sourceC1991) = raw28214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1991 sourceB1991 sourceC1991 difference raw28214; decide +kernel
    rw [ha]
    exact (canonical28214 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1991 + difference 0 3) (sourceB1991 + difference 3 0) sourceC1991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2076) := by
    have ha : (tripleCharges (sourceA1991 + difference 0 3) (sourceB1991 + difference 3 0) sourceC1991) = raw28215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1991 sourceB1991 sourceC1991 difference raw28215; decide +kernel
    rw [ha]
    exact (canonical28215 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1991 + difference 0 4) (sourceB1991 + difference 4 0) sourceC1991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1991 + difference 0 4) (sourceB1991 + difference 4 0) sourceC1991) = raw28216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1991 sourceB1991 sourceC1991 difference raw28216; decide +kernel
    rw [ha]
    exact (canonical28216 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1991 + difference 0 5) (sourceB1991 + difference 5 0) sourceC1991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA1991 + difference 0 5) (sourceB1991 + difference 5 0) sourceC1991) = raw28217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1991 sourceB1991 sourceC1991 difference raw28217; decide +kernel
    rw [ha]
    exact (canonical28217 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1991 + sourceB1991) sourceC1991) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1991 + sourceB1991) sourceC1991) = raw28218 := by
      apply Matrix.ext; unfold doubleCharges sourceA1991 sourceB1991 sourceC1991 raw28218; decide +kernel
    rw [ha]
    exact (canonical28218 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1991 sourceB1991 sourceC1991
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1991, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1993 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1993 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1993 + difference 0 1) (sourceB1993 + difference 1 0) sourceC1993) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA1993 + difference 0 1) (sourceB1993 + difference 1 0) sourceC1993) = raw28226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1993 sourceB1993 sourceC1993 difference raw28226; decide +kernel
    rw [ha]
    exact (canonical28226 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1993 + difference 1 1) (sourceB1993 + difference 1 1) sourceC1993) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2886) := by
    have ha : (tripleCharges (sourceA1993 + difference 1 1) (sourceB1993 + difference 1 1) sourceC1993) = raw28227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1993 sourceB1993 sourceC1993 difference raw28227; decide +kernel
    rw [ha]
    exact (canonical28227 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1993 + difference 2 1) (sourceB1993 + difference 1 2) sourceC1993) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2811) := by
    have ha : (tripleCharges (sourceA1993 + difference 2 1) (sourceB1993 + difference 1 2) sourceC1993) = raw28228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1993 sourceB1993 sourceC1993 difference raw28228; decide +kernel
    rw [ha]
    exact (canonical28228 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1993 + difference 3 1) (sourceB1993 + difference 1 3) sourceC1993) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2811) := by
    have ha : (tripleCharges (sourceA1993 + difference 3 1) (sourceB1993 + difference 1 3) sourceC1993) = raw28229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1993 sourceB1993 sourceC1993 difference raw28229; decide +kernel
    rw [ha]
    exact (canonical28229 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1993 + difference 4 1) (sourceB1993 + difference 1 4) sourceC1993) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2820) := by
    have ha : (tripleCharges (sourceA1993 + difference 4 1) (sourceB1993 + difference 1 4) sourceC1993) = raw28230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1993 sourceB1993 sourceC1993 difference raw28230; decide +kernel
    rw [ha]
    exact (canonical28230 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1993 + difference 5 1) (sourceB1993 + difference 1 5) sourceC1993) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1325) := by
    have ha : (tripleCharges (sourceA1993 + difference 5 1) (sourceB1993 + difference 1 5) sourceC1993) = raw28231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1993 sourceB1993 sourceC1993 difference raw28231; decide +kernel
    rw [ha]
    exact (canonical28231 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1993 + sourceB1993) sourceC1993) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1993 + sourceB1993) sourceC1993) = raw28232 := by
      apply Matrix.ext; unfold doubleCharges sourceA1993 sourceB1993 sourceC1993 raw28232; decide +kernel
    rw [ha]
    exact (canonical28232 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1993 sourceB1993 sourceC1993
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1993, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1997 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1997 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1997 + difference 0 1) (sourceB1997 + difference 1 0) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA1997 + difference 0 1) (sourceB1997 + difference 1 0) sourceC1997) = raw28307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28307; decide +kernel
    rw [ha]
    exact (canonical28307 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1997 + difference 0 2) (sourceB1997 + difference 2 0) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA1997 + difference 0 2) (sourceB1997 + difference 2 0) sourceC1997) = raw28308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28308; decide +kernel
    rw [ha]
    exact (canonical28308 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1997 + difference 0 3) (sourceB1997 + difference 3 0) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA1997 + difference 0 3) (sourceB1997 + difference 3 0) sourceC1997) = raw28309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28309; decide +kernel
    rw [ha]
    exact (canonical28309 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1997 + difference 0 4) (sourceB1997 + difference 4 0) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA1997 + difference 0 4) (sourceB1997 + difference 4 0) sourceC1997) = raw28310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28310; decide +kernel
    rw [ha]
    exact (canonical28310 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1997 + difference 0 5) (sourceB1997 + difference 5 0) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA1997 + difference 0 5) (sourceB1997 + difference 5 0) sourceC1997) = raw28311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28311; decide +kernel
    rw [ha]
    exact (canonical28311 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1997 + difference 1 0) (sourceB1997 + difference 0 1) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1997 + difference 1 0) (sourceB1997 + difference 0 1) sourceC1997) = raw28312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28312; decide +kernel
    rw [ha]
    exact (canonical28312 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1997 + difference 1 2) (sourceB1997 + difference 2 1) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1997 + difference 1 2) (sourceB1997 + difference 2 1) sourceC1997) = raw28313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28313; decide +kernel
    rw [ha]
    exact (canonical28313 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1997 + difference 1 3) (sourceB1997 + difference 3 1) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1997 + difference 1 3) (sourceB1997 + difference 3 1) sourceC1997) = raw28314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28314; decide +kernel
    rw [ha]
    exact (canonical28314 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1997 + difference 1 4) (sourceB1997 + difference 4 1) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA1997 + difference 1 4) (sourceB1997 + difference 4 1) sourceC1997) = raw28315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28315; decide +kernel
    rw [ha]
    exact (canonical28315 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1997 + difference 1 5) (sourceB1997 + difference 5 1) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA1997 + difference 1 5) (sourceB1997 + difference 5 1) sourceC1997) = raw28316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28316; decide +kernel
    rw [ha]
    exact (canonical28316 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1997 + difference 2 0) (sourceB1997 + difference 0 2) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1997 + difference 2 0) (sourceB1997 + difference 0 2) sourceC1997) = raw28317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28317; decide +kernel
    rw [ha]
    exact (canonical28317 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1997 + difference 2 1) (sourceB1997 + difference 1 2) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA1997 + difference 2 1) (sourceB1997 + difference 1 2) sourceC1997) = raw28318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28318; decide +kernel
    rw [ha]
    exact (canonical28318 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1997 + difference 2 3) (sourceB1997 + difference 3 2) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3451) := by
    have ha : (tripleCharges (sourceA1997 + difference 2 3) (sourceB1997 + difference 3 2) sourceC1997) = raw28319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28319; decide +kernel
    rw [ha]
    exact (canonical28319 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1997 + difference 2 4) (sourceB1997 + difference 4 2) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1997 + difference 2 4) (sourceB1997 + difference 4 2) sourceC1997) = raw28320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28320; decide +kernel
    rw [ha]
    exact (canonical28320 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1997 + difference 2 5) (sourceB1997 + difference 5 2) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA1997 + difference 2 5) (sourceB1997 + difference 5 2) sourceC1997) = raw28321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28321; decide +kernel
    rw [ha]
    exact (canonical28321 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1997 + difference 3 0) (sourceB1997 + difference 0 3) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1997 + difference 3 0) (sourceB1997 + difference 0 3) sourceC1997) = raw28322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28322; decide +kernel
    rw [ha]
    exact (canonical28322 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1997 + difference 3 1) (sourceB1997 + difference 1 3) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA1997 + difference 3 1) (sourceB1997 + difference 1 3) sourceC1997) = raw28323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28323; decide +kernel
    rw [ha]
    exact (canonical28323 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1997 + difference 3 2) (sourceB1997 + difference 2 3) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3451) := by
    have ha : (tripleCharges (sourceA1997 + difference 3 2) (sourceB1997 + difference 2 3) sourceC1997) = raw28324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28324; decide +kernel
    rw [ha]
    exact (canonical28324 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1997 + difference 3 4) (sourceB1997 + difference 4 3) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1997 + difference 3 4) (sourceB1997 + difference 4 3) sourceC1997) = raw28325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28325; decide +kernel
    rw [ha]
    exact (canonical28325 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1997 + difference 3 5) (sourceB1997 + difference 5 3) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA1997 + difference 3 5) (sourceB1997 + difference 5 3) sourceC1997) = raw28326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28326; decide +kernel
    rw [ha]
    exact (canonical28326 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1997 + difference 4 0) (sourceB1997 + difference 0 4) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA1997 + difference 4 0) (sourceB1997 + difference 0 4) sourceC1997) = raw28327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28327; decide +kernel
    rw [ha]
    exact (canonical28327 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1997 + difference 4 1) (sourceB1997 + difference 1 4) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA1997 + difference 4 1) (sourceB1997 + difference 1 4) sourceC1997) = raw28328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28328; decide +kernel
    rw [ha]
    exact (canonical28328 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1997 + difference 4 2) (sourceB1997 + difference 2 4) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA1997 + difference 4 2) (sourceB1997 + difference 2 4) sourceC1997) = raw28329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28329; decide +kernel
    rw [ha]
    exact (canonical28329 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1997 + difference 4 3) (sourceB1997 + difference 3 4) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA1997 + difference 4 3) (sourceB1997 + difference 3 4) sourceC1997) = raw28330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28330; decide +kernel
    rw [ha]
    exact (canonical28330 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1997 + difference 4 5) (sourceB1997 + difference 5 4) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA1997 + difference 4 5) (sourceB1997 + difference 5 4) sourceC1997) = raw28331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28331; decide +kernel
    rw [ha]
    exact (canonical28331 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1997 + difference 5 0) (sourceB1997 + difference 0 5) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1997 + difference 5 0) (sourceB1997 + difference 0 5) sourceC1997) = raw28332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28332; decide +kernel
    rw [ha]
    exact (canonical28332 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1997 + difference 5 1) (sourceB1997 + difference 1 5) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA1997 + difference 5 1) (sourceB1997 + difference 1 5) sourceC1997) = raw28333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28333; decide +kernel
    rw [ha]
    exact (canonical28333 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1997 + difference 5 2) (sourceB1997 + difference 2 5) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA1997 + difference 5 2) (sourceB1997 + difference 2 5) sourceC1997) = raw28334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28334; decide +kernel
    rw [ha]
    exact (canonical28334 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1997 + difference 5 3) (sourceB1997 + difference 3 5) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA1997 + difference 5 3) (sourceB1997 + difference 3 5) sourceC1997) = raw28335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28335; decide +kernel
    rw [ha]
    exact (canonical28335 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1997 + difference 5 4) (sourceB1997 + difference 4 5) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1997 + difference 5 4) (sourceB1997 + difference 4 5) sourceC1997) = raw28336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28336; decide +kernel
    rw [ha]
    exact (canonical28336 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1997 sourceB1997 sourceC1997
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1997, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2001 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2001 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2001 + difference 0 1) (sourceB2001 + difference 1 0) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2001 + difference 0 1) (sourceB2001 + difference 1 0) sourceC2001) = raw28425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28425; decide +kernel
    rw [ha]
    exact (canonical28425 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2001 + difference 0 2) (sourceB2001 + difference 2 0) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2001 + difference 0 2) (sourceB2001 + difference 2 0) sourceC2001) = raw28426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28426; decide +kernel
    rw [ha]
    exact (canonical28426 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2001 + difference 0 3) (sourceB2001 + difference 3 0) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2001 + difference 0 3) (sourceB2001 + difference 3 0) sourceC2001) = raw28427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28427; decide +kernel
    rw [ha]
    exact (canonical28427 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2001 + difference 0 4) (sourceB2001 + difference 4 0) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA2001 + difference 0 4) (sourceB2001 + difference 4 0) sourceC2001) = raw28428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28428; decide +kernel
    rw [ha]
    exact (canonical28428 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2001 + difference 0 5) (sourceB2001 + difference 5 0) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2001 + difference 0 5) (sourceB2001 + difference 5 0) sourceC2001) = raw28429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28429; decide +kernel
    rw [ha]
    exact (canonical28429 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2001 + difference 1 0) (sourceB2001 + difference 0 1) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA2001 + difference 1 0) (sourceB2001 + difference 0 1) sourceC2001) = raw28430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28430; decide +kernel
    rw [ha]
    exact (canonical28430 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2001 + difference 1 2) (sourceB2001 + difference 2 1) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA2001 + difference 1 2) (sourceB2001 + difference 2 1) sourceC2001) = raw28431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28431; decide +kernel
    rw [ha]
    exact (canonical28431 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2001 + difference 1 3) (sourceB2001 + difference 3 1) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA2001 + difference 1 3) (sourceB2001 + difference 3 1) sourceC2001) = raw28432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28432; decide +kernel
    rw [ha]
    exact (canonical28432 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2001 + difference 1 4) (sourceB2001 + difference 4 1) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA2001 + difference 1 4) (sourceB2001 + difference 4 1) sourceC2001) = raw28433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28433; decide +kernel
    rw [ha]
    exact (canonical28433 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2001 + difference 1 5) (sourceB2001 + difference 5 1) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA2001 + difference 1 5) (sourceB2001 + difference 5 1) sourceC2001) = raw28434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28434; decide +kernel
    rw [ha]
    exact (canonical28434 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2001 + difference 2 0) (sourceB2001 + difference 0 2) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1742) := by
    have ha : (tripleCharges (sourceA2001 + difference 2 0) (sourceB2001 + difference 0 2) sourceC2001) = raw28435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28435; decide +kernel
    rw [ha]
    exact (canonical28435 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2001 + difference 2 1) (sourceB2001 + difference 1 2) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2001 + difference 2 1) (sourceB2001 + difference 1 2) sourceC2001) = raw28436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28436; decide +kernel
    rw [ha]
    exact (canonical28436 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2001 + difference 2 3) (sourceB2001 + difference 3 2) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2175) := by
    have ha : (tripleCharges (sourceA2001 + difference 2 3) (sourceB2001 + difference 3 2) sourceC2001) = raw28437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28437; decide +kernel
    rw [ha]
    exact (canonical28437 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2001 + difference 2 4) (sourceB2001 + difference 4 2) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA2001 + difference 2 4) (sourceB2001 + difference 4 2) sourceC2001) = raw28438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28438; decide +kernel
    rw [ha]
    exact (canonical28438 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2001 + difference 2 5) (sourceB2001 + difference 5 2) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA2001 + difference 2 5) (sourceB2001 + difference 5 2) sourceC2001) = raw28439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28439; decide +kernel
    rw [ha]
    exact (canonical28439 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2001 + difference 3 0) (sourceB2001 + difference 0 3) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1742) := by
    have ha : (tripleCharges (sourceA2001 + difference 3 0) (sourceB2001 + difference 0 3) sourceC2001) = raw28440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28440; decide +kernel
    rw [ha]
    exact (canonical28440 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2001 + difference 3 1) (sourceB2001 + difference 1 3) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2001 + difference 3 1) (sourceB2001 + difference 1 3) sourceC2001) = raw28441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28441; decide +kernel
    rw [ha]
    exact (canonical28441 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2001 + difference 3 2) (sourceB2001 + difference 2 3) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2175) := by
    have ha : (tripleCharges (sourceA2001 + difference 3 2) (sourceB2001 + difference 2 3) sourceC2001) = raw28442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28442; decide +kernel
    rw [ha]
    exact (canonical28442 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2001 + difference 3 4) (sourceB2001 + difference 4 3) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA2001 + difference 3 4) (sourceB2001 + difference 4 3) sourceC2001) = raw28443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28443; decide +kernel
    rw [ha]
    exact (canonical28443 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2001 + difference 3 5) (sourceB2001 + difference 5 3) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA2001 + difference 3 5) (sourceB2001 + difference 5 3) sourceC2001) = raw28444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28444; decide +kernel
    rw [ha]
    exact (canonical28444 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2001 + difference 4 0) (sourceB2001 + difference 0 4) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1743) := by
    have ha : (tripleCharges (sourceA2001 + difference 4 0) (sourceB2001 + difference 0 4) sourceC2001) = raw28445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28445; decide +kernel
    rw [ha]
    exact (canonical28445 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2001 + difference 4 1) (sourceB2001 + difference 1 4) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2001 + difference 4 1) (sourceB2001 + difference 1 4) sourceC2001) = raw28446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28446; decide +kernel
    rw [ha]
    exact (canonical28446 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2001 + difference 4 2) (sourceB2001 + difference 2 4) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2153) := by
    have ha : (tripleCharges (sourceA2001 + difference 4 2) (sourceB2001 + difference 2 4) sourceC2001) = raw28447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28447; decide +kernel
    rw [ha]
    exact (canonical28447 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2001 + difference 4 3) (sourceB2001 + difference 3 4) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2153) := by
    have ha : (tripleCharges (sourceA2001 + difference 4 3) (sourceB2001 + difference 3 4) sourceC2001) = raw28448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28448; decide +kernel
    rw [ha]
    exact (canonical28448 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2001 + difference 4 5) (sourceB2001 + difference 5 4) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA2001 + difference 4 5) (sourceB2001 + difference 5 4) sourceC2001) = raw28449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28449; decide +kernel
    rw [ha]
    exact (canonical28449 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2001 + difference 5 0) (sourceB2001 + difference 0 5) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA2001 + difference 5 0) (sourceB2001 + difference 0 5) sourceC2001) = raw28450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28450; decide +kernel
    rw [ha]
    exact (canonical28450 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2001 + difference 5 1) (sourceB2001 + difference 1 5) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2001 + difference 5 1) (sourceB2001 + difference 1 5) sourceC2001) = raw28451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28451; decide +kernel
    rw [ha]
    exact (canonical28451 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2001 + difference 5 2) (sourceB2001 + difference 2 5) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA2001 + difference 5 2) (sourceB2001 + difference 2 5) sourceC2001) = raw28452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28452; decide +kernel
    rw [ha]
    exact (canonical28452 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2001 + difference 5 3) (sourceB2001 + difference 3 5) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA2001 + difference 5 3) (sourceB2001 + difference 3 5) sourceC2001) = raw28453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28453; decide +kernel
    rw [ha]
    exact (canonical28453 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2001 + difference 5 4) (sourceB2001 + difference 4 5) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA2001 + difference 5 4) (sourceB2001 + difference 4 5) sourceC2001) = raw28454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28454; decide +kernel
    rw [ha]
    exact (canonical28454 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2001 sourceB2001 sourceC2001
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2001, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2002 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2002 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2002 + difference 0 1) (sourceB2002 + difference 1 0) sourceC2002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2066) := by
    have ha : (tripleCharges (sourceA2002 + difference 0 1) (sourceB2002 + difference 1 0) sourceC2002) = raw28455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2002 sourceB2002 sourceC2002 difference raw28455; decide +kernel
    rw [ha]
    exact (canonical28455 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2002 + difference 1 1) (sourceB2002 + difference 1 1) sourceC2002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA2002 + difference 1 1) (sourceB2002 + difference 1 1) sourceC2002) = raw28456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2002 sourceB2002 sourceC2002 difference raw28456; decide +kernel
    rw [ha]
    exact (canonical28456 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2002 + difference 2 1) (sourceB2002 + difference 1 2) sourceC2002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1970) := by
    have ha : (tripleCharges (sourceA2002 + difference 2 1) (sourceB2002 + difference 1 2) sourceC2002) = raw28457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2002 sourceB2002 sourceC2002 difference raw28457; decide +kernel
    rw [ha]
    exact (canonical28457 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2002 + difference 3 1) (sourceB2002 + difference 1 3) sourceC2002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1970) := by
    have ha : (tripleCharges (sourceA2002 + difference 3 1) (sourceB2002 + difference 1 3) sourceC2002) = raw28458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2002 sourceB2002 sourceC2002 difference raw28458; decide +kernel
    rw [ha]
    exact (canonical28458 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2002 + difference 4 1) (sourceB2002 + difference 1 4) sourceC2002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1819) := by
    have ha : (tripleCharges (sourceA2002 + difference 4 1) (sourceB2002 + difference 1 4) sourceC2002) = raw28459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2002 sourceB2002 sourceC2002 difference raw28459; decide +kernel
    rw [ha]
    exact (canonical28459 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2002 + difference 5 1) (sourceB2002 + difference 1 5) sourceC2002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 939) := by
    have ha : (tripleCharges (sourceA2002 + difference 5 1) (sourceB2002 + difference 1 5) sourceC2002) = raw28460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2002 sourceB2002 sourceC2002 difference raw28460; decide +kernel
    rw [ha]
    exact (canonical28460 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2002 + sourceB2002) sourceC2002) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2002 + sourceB2002) sourceC2002) = raw28461 := by
      apply Matrix.ext; unfold doubleCharges sourceA2002 sourceB2002 sourceC2002 raw28461; decide +kernel
    rw [ha]
    exact (canonical28461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2002 sourceB2002 sourceC2002
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2002, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2003 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2003 + difference 2 0) (sourceB2003 + difference 0 2) sourceC2003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1315) := by
    have ha : (tripleCharges (sourceA2003 + difference 2 0) (sourceB2003 + difference 0 2) sourceC2003) = raw28462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2003 sourceB2003 sourceC2003 difference raw28462; decide +kernel
    rw [ha]
    exact (canonical28462 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2003 + difference 2 1) (sourceB2003 + difference 1 2) sourceC2003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1970) := by
    have ha : (tripleCharges (sourceA2003 + difference 2 1) (sourceB2003 + difference 1 2) sourceC2003) = raw28457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2003 sourceB2003 sourceC2003 difference raw28457; decide +kernel
    rw [ha]
    exact (canonical28457 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2003 + difference 2 2) (sourceB2003 + difference 2 2) sourceC2003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA2003 + difference 2 2) (sourceB2003 + difference 2 2) sourceC2003) = raw28456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2003 sourceB2003 sourceC2003 difference raw28456; decide +kernel
    rw [ha]
    exact (canonical28456 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2003 + difference 2 3) (sourceB2003 + difference 3 2) sourceC2003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1961) := by
    have ha : (tripleCharges (sourceA2003 + difference 2 3) (sourceB2003 + difference 3 2) sourceC2003) = raw28463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2003 sourceB2003 sourceC2003 difference raw28463; decide +kernel
    rw [ha]
    exact (canonical28463 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2003 + difference 2 4) (sourceB2003 + difference 4 2) sourceC2003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA2003 + difference 2 4) (sourceB2003 + difference 4 2) sourceC2003) = raw28464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2003 sourceB2003 sourceC2003 difference raw28464; decide +kernel
    rw [ha]
    exact (canonical28464 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2003 + difference 2 5) (sourceB2003 + difference 5 2) sourceC2003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA2003 + difference 2 5) (sourceB2003 + difference 5 2) sourceC2003) = raw28465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2003 sourceB2003 sourceC2003 difference raw28465; decide +kernel
    rw [ha]
    exact (canonical28465 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2003 + sourceB2003) sourceC2003) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2003 + sourceB2003) sourceC2003) = raw28461 := by
      apply Matrix.ext; unfold doubleCharges sourceA2003 sourceB2003 sourceC2003 raw28461; decide +kernel
    rw [ha]
    exact (canonical28461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2003 sourceB2003 sourceC2003
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2003, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2008 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2008 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2008 + difference 0 0) (sourceB2008 + difference 0 0) sourceC2008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2130) := by
    have ha : (tripleCharges (sourceA2008 + difference 0 0) (sourceB2008 + difference 0 0) sourceC2008) = raw20273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2008 sourceB2008 sourceC2008 difference raw20273; decide +kernel
    rw [ha]
    exact (canonical20273 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2008 + difference 0 1) (sourceB2008 + difference 1 0) sourceC2008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2137) := by
    have ha : (tripleCharges (sourceA2008 + difference 0 1) (sourceB2008 + difference 1 0) sourceC2008) = raw28494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2008 sourceB2008 sourceC2008 difference raw28494; decide +kernel
    rw [ha]
    exact (canonical28494 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2008 + difference 0 2) (sourceB2008 + difference 2 0) sourceC2008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2128) := by
    have ha : (tripleCharges (sourceA2008 + difference 0 2) (sourceB2008 + difference 2 0) sourceC2008) = raw28495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2008 sourceB2008 sourceC2008 difference raw28495; decide +kernel
    rw [ha]
    exact (canonical28495 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2008 + difference 0 3) (sourceB2008 + difference 3 0) sourceC2008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2128) := by
    have ha : (tripleCharges (sourceA2008 + difference 0 3) (sourceB2008 + difference 3 0) sourceC2008) = raw28496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2008 sourceB2008 sourceC2008 difference raw28496; decide +kernel
    rw [ha]
    exact (canonical28496 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2008 + difference 0 4) (sourceB2008 + difference 4 0) sourceC2008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2008 + difference 0 4) (sourceB2008 + difference 4 0) sourceC2008) = raw28497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2008 sourceB2008 sourceC2008 difference raw28497; decide +kernel
    rw [ha]
    exact (canonical28497 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2008 + difference 0 5) (sourceB2008 + difference 5 0) sourceC2008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA2008 + difference 0 5) (sourceB2008 + difference 5 0) sourceC2008) = raw28498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2008 sourceB2008 sourceC2008 difference raw28498; decide +kernel
    rw [ha]
    exact (canonical28498 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2008 + sourceB2008) sourceC2008) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2008 + sourceB2008) sourceC2008) = raw19488 := by
      apply Matrix.ext; unfold doubleCharges sourceA2008 sourceB2008 sourceC2008 raw19488; decide +kernel
    rw [ha]
    exact (canonical19488 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2008 sourceB2008 sourceC2008
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2008, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2009 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2009 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2009 + difference 0 0) (sourceB2009 + difference 0 0) sourceC2009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2087) := by
    have ha : (tripleCharges (sourceA2009 + difference 0 0) (sourceB2009 + difference 0 0) sourceC2009) = raw20311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2009 sourceB2009 sourceC2009 difference raw20311; decide +kernel
    rw [ha]
    exact (canonical20311 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2009 + difference 0 1) (sourceB2009 + difference 1 0) sourceC2009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2093) := by
    have ha : (tripleCharges (sourceA2009 + difference 0 1) (sourceB2009 + difference 1 0) sourceC2009) = raw28499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2009 sourceB2009 sourceC2009 difference raw28499; decide +kernel
    rw [ha]
    exact (canonical28499 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2009 + difference 0 2) (sourceB2009 + difference 2 0) sourceC2009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2085) := by
    have ha : (tripleCharges (sourceA2009 + difference 0 2) (sourceB2009 + difference 2 0) sourceC2009) = raw28500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2009 sourceB2009 sourceC2009 difference raw28500; decide +kernel
    rw [ha]
    exact (canonical28500 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2009 + difference 0 3) (sourceB2009 + difference 3 0) sourceC2009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2101) := by
    have ha : (tripleCharges (sourceA2009 + difference 0 3) (sourceB2009 + difference 3 0) sourceC2009) = raw28501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2009 sourceB2009 sourceC2009 difference raw28501; decide +kernel
    rw [ha]
    exact (canonical28501 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2009 + difference 0 4) (sourceB2009 + difference 4 0) sourceC2009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2009 + difference 0 4) (sourceB2009 + difference 4 0) sourceC2009) = raw28502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2009 sourceB2009 sourceC2009 difference raw28502; decide +kernel
    rw [ha]
    exact (canonical28502 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2009 + difference 0 5) (sourceB2009 + difference 5 0) sourceC2009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA2009 + difference 0 5) (sourceB2009 + difference 5 0) sourceC2009) = raw28503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2009 sourceB2009 sourceC2009 difference raw28503; decide +kernel
    rw [ha]
    exact (canonical28503 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2009 + sourceB2009) sourceC2009) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2009 + sourceB2009) sourceC2009) = raw19499 := by
      apply Matrix.ext; unfold doubleCharges sourceA2009 sourceB2009 sourceC2009 raw19499; decide +kernel
    rw [ha]
    exact (canonical19499 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2009 sourceB2009 sourceC2009
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2009, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2011 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2011 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2011 + difference 0 5) (sourceB2011 + difference 5 0) sourceC2011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2011 + difference 0 5) (sourceB2011 + difference 5 0) sourceC2011) = raw28508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2011 sourceB2011 sourceC2011 difference raw28508; decide +kernel
    rw [ha]
    exact (canonical28508 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2011 + difference 1 5) (sourceB2011 + difference 5 1) sourceC2011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2011 + difference 1 5) (sourceB2011 + difference 5 1) sourceC2011) = raw20320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2011 sourceB2011 sourceC2011 difference raw20320; decide +kernel
    rw [ha]
    exact (canonical20320 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2011 + difference 2 5) (sourceB2011 + difference 5 2) sourceC2011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2606) := by
    have ha : (tripleCharges (sourceA2011 + difference 2 5) (sourceB2011 + difference 5 2) sourceC2011) = raw28509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2011 sourceB2011 sourceC2011 difference raw28509; decide +kernel
    rw [ha]
    exact (canonical28509 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2011 + difference 3 5) (sourceB2011 + difference 5 3) sourceC2011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2629) := by
    have ha : (tripleCharges (sourceA2011 + difference 3 5) (sourceB2011 + difference 5 3) sourceC2011) = raw28510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2011 sourceB2011 sourceC2011 difference raw28510; decide +kernel
    rw [ha]
    exact (canonical28510 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2011 + difference 4 5) (sourceB2011 + difference 5 4) sourceC2011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2608) := by
    have ha : (tripleCharges (sourceA2011 + difference 4 5) (sourceB2011 + difference 5 4) sourceC2011) = raw28511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2011 sourceB2011 sourceC2011 difference raw28511; decide +kernel
    rw [ha]
    exact (canonical28511 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2011 + difference 5 5) (sourceB2011 + difference 5 5) sourceC2011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2492) := by
    have ha : (tripleCharges (sourceA2011 + difference 5 5) (sourceB2011 + difference 5 5) sourceC2011) = raw20316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2011 sourceB2011 sourceC2011 difference raw20316; decide +kernel
    rw [ha]
    exact (canonical20316 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2011 + sourceB2011) sourceC2011) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2011 + sourceB2011) sourceC2011) = raw20321 := by
      apply Matrix.ext; unfold doubleCharges sourceA2011 sourceB2011 sourceC2011 raw20321; decide +kernel
    rw [ha]
    exact (canonical20321 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2011 sourceB2011 sourceC2011
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2011, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2012 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2012 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2012 + difference 0 0) (sourceB2012 + difference 0 0) sourceC2012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2032) := by
    have ha : (tripleCharges (sourceA2012 + difference 0 0) (sourceB2012 + difference 0 0) sourceC2012) = raw20327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2012 sourceB2012 sourceC2012 difference raw20327; decide +kernel
    rw [ha]
    exact (canonical20327 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2012 + difference 0 1) (sourceB2012 + difference 1 0) sourceC2012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2038) := by
    have ha : (tripleCharges (sourceA2012 + difference 0 1) (sourceB2012 + difference 1 0) sourceC2012) = raw28512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2012 sourceB2012 sourceC2012 difference raw28512; decide +kernel
    rw [ha]
    exact (canonical28512 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2012 + difference 0 2) (sourceB2012 + difference 2 0) sourceC2012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2030) := by
    have ha : (tripleCharges (sourceA2012 + difference 0 2) (sourceB2012 + difference 2 0) sourceC2012) = raw28513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2012 sourceB2012 sourceC2012 difference raw28513; decide +kernel
    rw [ha]
    exact (canonical28513 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2012 + difference 0 3) (sourceB2012 + difference 3 0) sourceC2012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2048) := by
    have ha : (tripleCharges (sourceA2012 + difference 0 3) (sourceB2012 + difference 3 0) sourceC2012) = raw28514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2012 sourceB2012 sourceC2012 difference raw28514; decide +kernel
    rw [ha]
    exact (canonical28514 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2012 + difference 0 4) (sourceB2012 + difference 4 0) sourceC2012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2012 + difference 0 4) (sourceB2012 + difference 4 0) sourceC2012) = raw28515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2012 sourceB2012 sourceC2012 difference raw28515; decide +kernel
    rw [ha]
    exact (canonical28515 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2012 + difference 0 5) (sourceB2012 + difference 5 0) sourceC2012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2012 + difference 0 5) (sourceB2012 + difference 5 0) sourceC2012) = raw28516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2012 sourceB2012 sourceC2012 difference raw28516; decide +kernel
    rw [ha]
    exact (canonical28516 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2012 + sourceB2012) sourceC2012) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2012 + sourceB2012) sourceC2012) = raw20332 := by
      apply Matrix.ext; unfold doubleCharges sourceA2012 sourceB2012 sourceC2012 raw20332; decide +kernel
    rw [ha]
    exact (canonical20332 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2012 sourceB2012 sourceC2012
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2012, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2014 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2014 + difference 0 5) (sourceB2014 + difference 5 0) sourceC2014) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2014 + difference 0 5) (sourceB2014 + difference 5 0) sourceC2014) = raw28521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2014 sourceB2014 sourceC2014 difference raw28521; decide +kernel
    rw [ha]
    exact (canonical28521 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2014 + difference 1 5) (sourceB2014 + difference 5 1) sourceC2014) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA2014 + difference 1 5) (sourceB2014 + difference 5 1) sourceC2014) = raw20338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2014 sourceB2014 sourceC2014 difference raw20338; decide +kernel
    rw [ha]
    exact (canonical20338 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2014 + difference 2 5) (sourceB2014 + difference 5 2) sourceC2014) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2613) := by
    have ha : (tripleCharges (sourceA2014 + difference 2 5) (sourceB2014 + difference 5 2) sourceC2014) = raw28522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2014 sourceB2014 sourceC2014 difference raw28522; decide +kernel
    rw [ha]
    exact (canonical28522 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2014 + difference 3 5) (sourceB2014 + difference 5 3) sourceC2014) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2613) := by
    have ha : (tripleCharges (sourceA2014 + difference 3 5) (sourceB2014 + difference 5 3) sourceC2014) = raw28523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2014 sourceB2014 sourceC2014 difference raw28523; decide +kernel
    rw [ha]
    exact (canonical28523 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2014 + difference 4 5) (sourceB2014 + difference 5 4) sourceC2014) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2609) := by
    have ha : (tripleCharges (sourceA2014 + difference 4 5) (sourceB2014 + difference 5 4) sourceC2014) = raw28524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2014 sourceB2014 sourceC2014 difference raw28524; decide +kernel
    rw [ha]
    exact (canonical28524 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2014 + difference 5 5) (sourceB2014 + difference 5 5) sourceC2014) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2469) := by
    have ha : (tripleCharges (sourceA2014 + difference 5 5) (sourceB2014 + difference 5 5) sourceC2014) = raw20334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2014 sourceB2014 sourceC2014 difference raw20334; decide +kernel
    rw [ha]
    exact (canonical20334 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2014 + sourceB2014) sourceC2014) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2014 + sourceB2014) sourceC2014) = raw20339 := by
      apply Matrix.ext; unfold doubleCharges sourceA2014 sourceB2014 sourceC2014 raw20339; decide +kernel
    rw [ha]
    exact (canonical20339 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2014 sourceB2014 sourceC2014
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2014, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1680 : Integer.Sparse.reindex keyMap MixedData.row1680 = numericRow1680 := by decide +kernel

theorem numericCheck1680 (x : Master → ℝ) : Integer.Sparse.eval numericRow1680 x =
    (1 : ℝ) * reducedSource1680 x := by
  norm_num [numericRow1680, reducedSource1680, Integer.Sparse.eval, Sparse.eval, nodeValue2390, nodeValue2393, nodeValue2395, nodeValue2404, nodeValue2678, nodeValue3771, nodeValue4088]

theorem reindexCheck1681 : Integer.Sparse.reindex keyMap MixedData.row1681 = numericRow1681 := by decide +kernel

theorem numericCheck1681 (x : Master → ℝ) : Integer.Sparse.eval numericRow1681 x =
    (1 : ℝ) * reducedSource1681 x := by
  norm_num [numericRow1681, reducedSource1681, Integer.Sparse.eval, Sparse.eval, nodeValue1898, nodeValue1901, nodeValue1912, nodeValue2191, nodeValue3460, nodeValue4079]

theorem reindexCheck1682 : Integer.Sparse.reindex keyMap MixedData.row1682 = numericRow1682 := by decide +kernel

theorem numericCheck1682 (x : Master → ℝ) : Integer.Sparse.eval numericRow1682 x =
    (1 : ℝ) * reducedSource1682 x := by
  norm_num [numericRow1682, reducedSource1682, Integer.Sparse.eval, Sparse.eval, nodeValue2076, nodeValue2080, nodeValue2082, nodeValue2102, nodeValue2206, nodeValue3565, nodeValue4080]

theorem reindexCheck1683 : Integer.Sparse.reindex keyMap MixedData.row1683 = numericRow1683 := by decide +kernel

theorem numericCheck1683 (x : Master → ℝ) : Integer.Sparse.eval numericRow1683 x =
    (1 : ℝ) * reducedSource1683 x := by
  norm_num [numericRow1683, reducedSource1683, Integer.Sparse.eval, Sparse.eval, nodeValue1325, nodeValue2811, nodeValue2820, nodeValue2886, nodeValue2889, nodeValue4092]

theorem reindexCheck1685 : Integer.Sparse.reindex keyMap MixedData.row1685 = numericRow1685 := by decide +kernel

theorem numericCheck1685 (x : Master → ℝ) : Integer.Sparse.eval numericRow1685 x =
    (1 : ℝ) * reducedSource1685 x := by
  norm_num [numericRow1685, reducedSource1685, Integer.Sparse.eval, Sparse.eval, nodeValue1720, nodeValue1722, nodeValue1729, nodeValue1748, nodeValue3266, nodeValue3277, nodeValue3302, nodeValue3413, nodeValue3423, nodeValue3451, nodeValue3457, nodeValue3471, nodeValue3472, nodeValue3485, nodeValue3523, nodeValue3548, nodeValue3549, nodeValue3624, nodeValue3626, nodeValue3631, nodeValue3817]

theorem reindexCheck1688 : Integer.Sparse.reindex keyMap MixedData.row1688 = numericRow1688 := by decide +kernel

theorem numericCheck1688 (x : Master → ℝ) : Integer.Sparse.eval numericRow1688 x =
    (1 : ℝ) * reducedSource1688 x := by
  norm_num [numericRow1688, reducedSource1688, Integer.Sparse.eval, Sparse.eval, nodeValue1676, nodeValue1694, nodeValue1695, nodeValue1742, nodeValue1743, nodeValue1746, nodeValue1756, nodeValue2153, nodeValue2169, nodeValue2175, nodeValue2186, nodeValue2206, nodeValue2207, nodeValue2229, nodeValue2230, nodeValue2293, nodeValue2294, nodeValue2687, nodeValue2706, nodeValue2743, nodeValue2744]

theorem reindexCheck1689 : Integer.Sparse.reindex keyMap MixedData.row1689 = numericRow1689 := by decide +kernel

theorem numericCheck1689 (x : Master → ℝ) : Integer.Sparse.eval numericRow1689 x =
    (1 : ℝ) * reducedSource1689 x := by
  norm_num [numericRow1689, reducedSource1689, Integer.Sparse.eval, Sparse.eval, nodeValue939, nodeValue1819, nodeValue1970, nodeValue2062, nodeValue2066, nodeValue4084]

theorem reindexCheck1690 : Integer.Sparse.reindex keyMap MixedData.row1690 = numericRow1690 := by decide +kernel

theorem numericCheck1690 (x : Master → ℝ) : Integer.Sparse.eval numericRow1690 x =
    (1 : ℝ) * reducedSource1690 x := by
  norm_num [numericRow1690, reducedSource1690, Integer.Sparse.eval, Sparse.eval, nodeValue1315, nodeValue1961, nodeValue1970, nodeValue2062, nodeValue2879, nodeValue4084]

theorem reindexCheck1691 : Integer.Sparse.reindex keyMap MixedData.row1691 = numericRow1691 := by decide +kernel

theorem numericCheck1691 (x : Master → ℝ) : Integer.Sparse.eval numericRow1691 x =
    (1 : ℝ) * reducedSource1691 x := by
  norm_num [numericRow1691, reducedSource1691, Integer.Sparse.eval, Sparse.eval, nodeValue2128, nodeValue2130, nodeValue2137, nodeValue2276, nodeValue2687, nodeValue4082]

theorem reindexCheck1692 : Integer.Sparse.reindex keyMap MixedData.row1692 = numericRow1692 := by decide +kernel

theorem numericCheck1692 (x : Master → ℝ) : Integer.Sparse.eval numericRow1692 x =
    (1 : ℝ) * reducedSource1692 x := by
  norm_num [numericRow1692, reducedSource1692, Integer.Sparse.eval, Sparse.eval, nodeValue2085, nodeValue2087, nodeValue2093, nodeValue2101, nodeValue2242, nodeValue3570, nodeValue4080]

theorem reindexCheck1693 : Integer.Sparse.reindex keyMap MixedData.row1693 = numericRow1693 := by decide +kernel

theorem numericCheck1693 (x : Master → ℝ) : Integer.Sparse.eval numericRow1693 x =
    (1 : ℝ) * reducedSource1693 x := by
  norm_num [numericRow1693, reducedSource1693, Integer.Sparse.eval, Sparse.eval, nodeValue2492, nodeValue2606, nodeValue2608, nodeValue2629, nodeValue2672, nodeValue3811, nodeValue4088]

theorem reindexCheck1694 : Integer.Sparse.reindex keyMap MixedData.row1694 = numericRow1694 := by decide +kernel

theorem numericCheck1694 (x : Master → ℝ) : Integer.Sparse.eval numericRow1694 x =
    (1 : ℝ) * reducedSource1694 x := by
  norm_num [numericRow1694, reducedSource1694, Integer.Sparse.eval, Sparse.eval, nodeValue2030, nodeValue2032, nodeValue2038, nodeValue2048, nodeValue2276, nodeValue3538, nodeValue4082]

theorem reindexCheck1695 : Integer.Sparse.reindex keyMap MixedData.row1695 = numericRow1695 := by decide +kernel

theorem numericCheck1695 (x : Master → ℝ) : Integer.Sparse.eval numericRow1695 x =
    (1 : ℝ) * reducedSource1695 x := by
  norm_num [numericRow1695, reducedSource1695, Integer.Sparse.eval, Sparse.eval, nodeValue2469, nodeValue2609, nodeValue2613, nodeValue2694, nodeValue3799, nodeValue4090]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1680 (mixedVector B) = 0 := by
  have h2390 : mixedVector B (Sum.inr 2390) = Sparse.eval nodeValue2390 (mixedVector B) := by
    change mixedMoment B node2390 node2390Labels = _
    exact sound2390 B hB hF
  have h2393 : mixedVector B (Sum.inr 2393) = Sparse.eval nodeValue2393 (mixedVector B) := by
    change mixedMoment B node2393 node2393Labels = _
    exact sound2393 B hB hF
  have h2395 : mixedVector B (Sum.inr 2395) = Sparse.eval nodeValue2395 (mixedVector B) := by
    change mixedMoment B node2395 node2395Labels = _
    exact sound2395 B hB hF
  have h2404 : mixedVector B (Sum.inr 2404) = Sparse.eval nodeValue2404 (mixedVector B) := by
    change mixedMoment B node2404 node2404Labels = _
    exact sound2404 B hB hF
  have h2678 : mixedVector B (Sum.inr 2678) = Sparse.eval nodeValue2678 (mixedVector B) := by
    change mixedMoment B node2678 node2678Labels = _
    exact sound2678 B hB hF
  have h3771 : mixedVector B (Sum.inr 3771) = Sparse.eval nodeValue3771 (mixedVector B) := by
    change mixedMoment B node3771 node3771Labels = _
    exact sound3771 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1981, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2390, h2393, h2395, h2404, h2678, h3771, h4088, reducedSource1680] using sourceEq1981 B hB

theorem rowSound1680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1680 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1680, numericCheck1680, reducedZero1680 B hB hF, mul_zero]

theorem reducedZero1681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1681 (mixedVector B) = 0 := by
  have h1898 : mixedVector B (Sum.inr 1898) = Sparse.eval nodeValue1898 (mixedVector B) := by
    change mixedMoment B node1898 node1898Labels = _
    exact sound1898 B hB hF
  have h1901 : mixedVector B (Sum.inr 1901) = Sparse.eval nodeValue1901 (mixedVector B) := by
    change mixedMoment B node1901 node1901Labels = _
    exact sound1901 B hB hF
  have h1912 : mixedVector B (Sum.inr 1912) = Sparse.eval nodeValue1912 (mixedVector B) := by
    change mixedMoment B node1912 node1912Labels = _
    exact sound1912 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h3460 : mixedVector B (Sum.inr 3460) = Sparse.eval nodeValue3460 (mixedVector B) := by
    change mixedMoment B node3460 node3460Labels = _
    exact sound3460 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1987, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1898, h1901, h1912, h2191, h3460, h4079, reducedSource1681] using sourceEq1987 B hB

theorem rowSound1681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1681 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1681, numericCheck1681, reducedZero1681 B hB hF, mul_zero]

theorem reducedZero1682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1682 (mixedVector B) = 0 := by
  have h2076 : mixedVector B (Sum.inr 2076) = Sparse.eval nodeValue2076 (mixedVector B) := by
    change mixedMoment B node2076 node2076Labels = _
    exact sound2076 B hB hF
  have h2080 : mixedVector B (Sum.inr 2080) = Sparse.eval nodeValue2080 (mixedVector B) := by
    change mixedMoment B node2080 node2080Labels = _
    exact sound2080 B hB hF
  have h2082 : mixedVector B (Sum.inr 2082) = Sparse.eval nodeValue2082 (mixedVector B) := by
    change mixedMoment B node2082 node2082Labels = _
    exact sound2082 B hB hF
  have h2102 : mixedVector B (Sum.inr 2102) = Sparse.eval nodeValue2102 (mixedVector B) := by
    change mixedMoment B node2102 node2102Labels = _
    exact sound2102 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1991, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2076, h2080, h2082, h2102, h2206, h3565, h4080, reducedSource1682] using sourceEq1991 B hB

theorem rowSound1682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1682 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1682, numericCheck1682, reducedZero1682 B hB hF, mul_zero]

theorem reducedZero1683 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1683 (mixedVector B) = 0 := by
  have h1325 : mixedVector B (Sum.inr 1325) = Sparse.eval nodeValue1325 (mixedVector B) := by
    change mixedMoment B node1325 node1325Labels = _
    exact sound1325 B hB hF
  have h2811 : mixedVector B (Sum.inr 2811) = Sparse.eval nodeValue2811 (mixedVector B) := by
    change mixedMoment B node2811 node2811Labels = _
    exact sound2811 B hB hF
  have h2820 : mixedVector B (Sum.inr 2820) = Sparse.eval nodeValue2820 (mixedVector B) := by
    change mixedMoment B node2820 node2820Labels = _
    exact sound2820 B hB hF
  have h2886 : mixedVector B (Sum.inr 2886) = Sparse.eval nodeValue2886 (mixedVector B) := by
    change mixedMoment B node2886 node2886Labels = _
    exact sound2886 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1993, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1325, h2811, h2820, h2886, h2889, h4092, reducedSource1683] using sourceEq1993 B hB

theorem rowSound1683 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1683 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1683, numericCheck1683, reducedZero1683 B hB hF, mul_zero]

theorem reducedZero1685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1685 (mixedVector B) = 0 := by
  have h1720 : mixedVector B (Sum.inr 1720) = Sparse.eval nodeValue1720 (mixedVector B) := by
    change mixedMoment B node1720 node1720Labels = _
    exact sound1720 B hB hF
  have h1722 : mixedVector B (Sum.inr 1722) = Sparse.eval nodeValue1722 (mixedVector B) := by
    change mixedMoment B node1722 node1722Labels = _
    exact sound1722 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h3266 : mixedVector B (Sum.inr 3266) = Sparse.eval nodeValue3266 (mixedVector B) := by
    change mixedMoment B node3266 node3266Labels = _
    exact sound3266 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h3451 : mixedVector B (Sum.inr 3451) = Sparse.eval nodeValue3451 (mixedVector B) := by
    change mixedMoment B node3451 node3451Labels = _
    exact sound3451 B hB hF
  have h3457 : mixedVector B (Sum.inr 3457) = Sparse.eval nodeValue3457 (mixedVector B) := by
    change mixedMoment B node3457 node3457Labels = _
    exact sound3457 B hB hF
  have h3471 : mixedVector B (Sum.inr 3471) = Sparse.eval nodeValue3471 (mixedVector B) := by
    change mixedMoment B node3471 node3471Labels = _
    exact sound3471 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h3485 : mixedVector B (Sum.inr 3485) = Sparse.eval nodeValue3485 (mixedVector B) := by
    change mixedMoment B node3485 node3485Labels = _
    exact sound3485 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h3624 : mixedVector B (Sum.inr 3624) = Sparse.eval nodeValue3624 (mixedVector B) := by
    change mixedMoment B node3624 node3624Labels = _
    exact sound3624 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3631 : mixedVector B (Sum.inr 3631) = Sparse.eval nodeValue3631 (mixedVector B) := by
    change mixedMoment B node3631 node3631Labels = _
    exact sound3631 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  simpa only [sourceForm1997, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1720, h1722, h1729, h1748, h3266, h3277, h3302, h3413, h3423, h3451, h3457, h3471, h3472, h3485, h3523, h3548, h3549, h3624, h3626, h3631, h3817, reducedSource1685] using sourceEq1997 B hB

theorem rowSound1685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1685 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1685, numericCheck1685, reducedZero1685 B hB hF, mul_zero]

theorem reducedZero1688 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1688 (mixedVector B) = 0 := by
  have h1676 : mixedVector B (Sum.inr 1676) = Sparse.eval nodeValue1676 (mixedVector B) := by
    change mixedMoment B node1676 node1676Labels = _
    exact sound1676 B hB hF
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h1695 : mixedVector B (Sum.inr 1695) = Sparse.eval nodeValue1695 (mixedVector B) := by
    change mixedMoment B node1695 node1695Labels = _
    exact sound1695 B hB hF
  have h1742 : mixedVector B (Sum.inr 1742) = Sparse.eval nodeValue1742 (mixedVector B) := by
    change mixedMoment B node1742 node1742Labels = _
    exact sound1742 B hB hF
  have h1743 : mixedVector B (Sum.inr 1743) = Sparse.eval nodeValue1743 (mixedVector B) := by
    change mixedMoment B node1743 node1743Labels = _
    exact sound1743 B hB hF
  have h1746 : mixedVector B (Sum.inr 1746) = Sparse.eval nodeValue1746 (mixedVector B) := by
    change mixedMoment B node1746 node1746Labels = _
    exact sound1746 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h2153 : mixedVector B (Sum.inr 2153) = Sparse.eval nodeValue2153 (mixedVector B) := by
    change mixedMoment B node2153 node2153Labels = _
    exact sound2153 B hB hF
  have h2169 : mixedVector B (Sum.inr 2169) = Sparse.eval nodeValue2169 (mixedVector B) := by
    change mixedMoment B node2169 node2169Labels = _
    exact sound2169 B hB hF
  have h2175 : mixedVector B (Sum.inr 2175) = Sparse.eval nodeValue2175 (mixedVector B) := by
    change mixedMoment B node2175 node2175Labels = _
    exact sound2175 B hB hF
  have h2186 : mixedVector B (Sum.inr 2186) = Sparse.eval nodeValue2186 (mixedVector B) := by
    change mixedMoment B node2186 node2186Labels = _
    exact sound2186 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h2706 : mixedVector B (Sum.inr 2706) = Sparse.eval nodeValue2706 (mixedVector B) := by
    change mixedMoment B node2706 node2706Labels = _
    exact sound2706 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  simpa only [sourceForm2001, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1676, h1694, h1695, h1742, h1743, h1746, h1756, h2153, h2169, h2175, h2186, h2206, h2207, h2229, h2230, h2293, h2294, h2687, h2706, h2743, h2744, reducedSource1688] using sourceEq2001 B hB

theorem rowSound1688 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1688 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1688, numericCheck1688, reducedZero1688 B hB hF, mul_zero]

theorem reducedZero1689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1689 (mixedVector B) = 0 := by
  have h939 : mixedVector B (Sum.inr 939) = Sparse.eval nodeValue939 (mixedVector B) := by
    change mixedMoment B node939 node939Labels = _
    exact sound939 B hB hF
  have h1819 : mixedVector B (Sum.inr 1819) = Sparse.eval nodeValue1819 (mixedVector B) := by
    change mixedMoment B node1819 node1819Labels = _
    exact sound1819 B hB hF
  have h1970 : mixedVector B (Sum.inr 1970) = Sparse.eval nodeValue1970 (mixedVector B) := by
    change mixedMoment B node1970 node1970Labels = _
    exact sound1970 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2066 : mixedVector B (Sum.inr 2066) = Sparse.eval nodeValue2066 (mixedVector B) := by
    change mixedMoment B node2066 node2066Labels = _
    exact sound2066 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2002, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h939, h1819, h1970, h2062, h2066, h4084, reducedSource1689] using sourceEq2002 B hB

theorem rowSound1689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1689 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1689, numericCheck1689, reducedZero1689 B hB hF, mul_zero]

theorem reducedZero1690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1690 (mixedVector B) = 0 := by
  have h1315 : mixedVector B (Sum.inr 1315) = Sparse.eval nodeValue1315 (mixedVector B) := by
    change mixedMoment B node1315 node1315Labels = _
    exact sound1315 B hB hF
  have h1961 : mixedVector B (Sum.inr 1961) = Sparse.eval nodeValue1961 (mixedVector B) := by
    change mixedMoment B node1961 node1961Labels = _
    exact sound1961 B hB hF
  have h1970 : mixedVector B (Sum.inr 1970) = Sparse.eval nodeValue1970 (mixedVector B) := by
    change mixedMoment B node1970 node1970Labels = _
    exact sound1970 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2879 : mixedVector B (Sum.inr 2879) = Sparse.eval nodeValue2879 (mixedVector B) := by
    change mixedMoment B node2879 node2879Labels = _
    exact sound2879 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2003, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1315, h1961, h1970, h2062, h2879, h4084, reducedSource1690] using sourceEq2003 B hB

theorem rowSound1690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1690 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1690, numericCheck1690, reducedZero1690 B hB hF, mul_zero]

theorem reducedZero1691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1691 (mixedVector B) = 0 := by
  have h2128 : mixedVector B (Sum.inr 2128) = Sparse.eval nodeValue2128 (mixedVector B) := by
    change mixedMoment B node2128 node2128Labels = _
    exact sound2128 B hB hF
  have h2130 : mixedVector B (Sum.inr 2130) = Sparse.eval nodeValue2130 (mixedVector B) := by
    change mixedMoment B node2130 node2130Labels = _
    exact sound2130 B hB hF
  have h2137 : mixedVector B (Sum.inr 2137) = Sparse.eval nodeValue2137 (mixedVector B) := by
    change mixedMoment B node2137 node2137Labels = _
    exact sound2137 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2008, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2128, h2130, h2137, h2276, h2687, h4082, reducedSource1691] using sourceEq2008 B hB

theorem rowSound1691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1691 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1691, numericCheck1691, reducedZero1691 B hB hF, mul_zero]

theorem reducedZero1692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1692 (mixedVector B) = 0 := by
  have h2085 : mixedVector B (Sum.inr 2085) = Sparse.eval nodeValue2085 (mixedVector B) := by
    change mixedMoment B node2085 node2085Labels = _
    exact sound2085 B hB hF
  have h2087 : mixedVector B (Sum.inr 2087) = Sparse.eval nodeValue2087 (mixedVector B) := by
    change mixedMoment B node2087 node2087Labels = _
    exact sound2087 B hB hF
  have h2093 : mixedVector B (Sum.inr 2093) = Sparse.eval nodeValue2093 (mixedVector B) := by
    change mixedMoment B node2093 node2093Labels = _
    exact sound2093 B hB hF
  have h2101 : mixedVector B (Sum.inr 2101) = Sparse.eval nodeValue2101 (mixedVector B) := by
    change mixedMoment B node2101 node2101Labels = _
    exact sound2101 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2009, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2085, h2087, h2093, h2101, h2242, h3570, h4080, reducedSource1692] using sourceEq2009 B hB

theorem rowSound1692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1692 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1692, numericCheck1692, reducedZero1692 B hB hF, mul_zero]

theorem reducedZero1693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1693 (mixedVector B) = 0 := by
  have h2492 : mixedVector B (Sum.inr 2492) = Sparse.eval nodeValue2492 (mixedVector B) := by
    change mixedMoment B node2492 node2492Labels = _
    exact sound2492 B hB hF
  have h2606 : mixedVector B (Sum.inr 2606) = Sparse.eval nodeValue2606 (mixedVector B) := by
    change mixedMoment B node2606 node2606Labels = _
    exact sound2606 B hB hF
  have h2608 : mixedVector B (Sum.inr 2608) = Sparse.eval nodeValue2608 (mixedVector B) := by
    change mixedMoment B node2608 node2608Labels = _
    exact sound2608 B hB hF
  have h2629 : mixedVector B (Sum.inr 2629) = Sparse.eval nodeValue2629 (mixedVector B) := by
    change mixedMoment B node2629 node2629Labels = _
    exact sound2629 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h3811 : mixedVector B (Sum.inr 3811) = Sparse.eval nodeValue3811 (mixedVector B) := by
    change mixedMoment B node3811 node3811Labels = _
    exact sound3811 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2011, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2492, h2606, h2608, h2629, h2672, h3811, h4088, reducedSource1693] using sourceEq2011 B hB

theorem rowSound1693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1693 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1693, numericCheck1693, reducedZero1693 B hB hF, mul_zero]

theorem reducedZero1694 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1694 (mixedVector B) = 0 := by
  have h2030 : mixedVector B (Sum.inr 2030) = Sparse.eval nodeValue2030 (mixedVector B) := by
    change mixedMoment B node2030 node2030Labels = _
    exact sound2030 B hB hF
  have h2032 : mixedVector B (Sum.inr 2032) = Sparse.eval nodeValue2032 (mixedVector B) := by
    change mixedMoment B node2032 node2032Labels = _
    exact sound2032 B hB hF
  have h2038 : mixedVector B (Sum.inr 2038) = Sparse.eval nodeValue2038 (mixedVector B) := by
    change mixedMoment B node2038 node2038Labels = _
    exact sound2038 B hB hF
  have h2048 : mixedVector B (Sum.inr 2048) = Sparse.eval nodeValue2048 (mixedVector B) := by
    change mixedMoment B node2048 node2048Labels = _
    exact sound2048 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2012, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2030, h2032, h2038, h2048, h2276, h3538, h4082, reducedSource1694] using sourceEq2012 B hB

theorem rowSound1694 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1694 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1694, numericCheck1694, reducedZero1694 B hB hF, mul_zero]

theorem reducedZero1695 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1695 (mixedVector B) = 0 := by
  have h2469 : mixedVector B (Sum.inr 2469) = Sparse.eval nodeValue2469 (mixedVector B) := by
    change mixedMoment B node2469 node2469Labels = _
    exact sound2469 B hB hF
  have h2609 : mixedVector B (Sum.inr 2609) = Sparse.eval nodeValue2609 (mixedVector B) := by
    change mixedMoment B node2609 node2609Labels = _
    exact sound2609 B hB hF
  have h2613 : mixedVector B (Sum.inr 2613) = Sparse.eval nodeValue2613 (mixedVector B) := by
    change mixedMoment B node2613 node2613Labels = _
    exact sound2613 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h3799 : mixedVector B (Sum.inr 3799) = Sparse.eval nodeValue3799 (mixedVector B) := by
    change mixedMoment B node3799 node3799Labels = _
    exact sound3799 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm2014, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2469, h2609, h2613, h2694, h3799, h4090, reducedSource1695] using sourceEq2014 B hB

theorem rowSound1695 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1695 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1695, numericCheck1695, reducedZero1695 B hB hF, mul_zero]

theorem sourceRowsAt1680 : MixedData.sourceRows (1680 : Fin 2425) =
    MixedData.row1680 := by decide +kernel

theorem sourceRowsAt1681 : MixedData.sourceRows (1681 : Fin 2425) =
    MixedData.row1681 := by decide +kernel

theorem sourceRowsAt1682 : MixedData.sourceRows (1682 : Fin 2425) =
    MixedData.row1682 := by decide +kernel

theorem sourceRowsAt1683 : MixedData.sourceRows (1683 : Fin 2425) =
    MixedData.row1683 := by decide +kernel

theorem sourceRowsAt1684 : MixedData.sourceRows (1684 : Fin 2425) =
    MixedData.row1684 := by decide +kernel

theorem sourceRowsAt1685 : MixedData.sourceRows (1685 : Fin 2425) =
    MixedData.row1685 := by decide +kernel

theorem sourceRowsAt1686 : MixedData.sourceRows (1686 : Fin 2425) =
    MixedData.row1686 := by decide +kernel

theorem sourceRowsAt1687 : MixedData.sourceRows (1687 : Fin 2425) =
    MixedData.row1687 := by decide +kernel

theorem sourceRowsAt1688 : MixedData.sourceRows (1688 : Fin 2425) =
    MixedData.row1688 := by decide +kernel

theorem sourceRowsAt1689 : MixedData.sourceRows (1689 : Fin 2425) =
    MixedData.row1689 := by decide +kernel

theorem sourceRowsAt1690 : MixedData.sourceRows (1690 : Fin 2425) =
    MixedData.row1690 := by decide +kernel

theorem sourceRowsAt1691 : MixedData.sourceRows (1691 : Fin 2425) =
    MixedData.row1691 := by decide +kernel

theorem sourceRowsAt1692 : MixedData.sourceRows (1692 : Fin 2425) =
    MixedData.row1692 := by decide +kernel

theorem sourceRowsAt1693 : MixedData.sourceRows (1693 : Fin 2425) =
    MixedData.row1693 := by decide +kernel

theorem sourceRowsAt1694 : MixedData.sourceRows (1694 : Fin 2425) =
    MixedData.row1694 := by decide +kernel

theorem sourceRowsAt1695 : MixedData.sourceRows (1695 : Fin 2425) =
    MixedData.row1695 := by decide +kernel

theorem chunkSound105_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 105) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1680 ∨ k.val = 1681 ∨ k.val = 1682 ∨ k.val = 1683 ∨ k.val = 1684 ∨ k.val = 1685 ∨ k.val = 1686 ∨ k.val = 1687 ∨ k.val = 1688 ∨ k.val = 1689 ∨ k.val = 1690 ∨ k.val = 1691 ∨ k.val = 1692 ∨ k.val = 1693 ∨ k.val = 1694 ∨ k.val = 1695 := by omega
  rcases heq with h1680 | h1681 | h1682 | h1683 | h1684 | h1685 | h1686 | h1687 | h1688 | h1689 | h1690 | h1691 | h1692 | h1693 | h1694 | h1695
  · have he : k = (1680 : Fin 2425) := Fin.ext h1680
    subst k
    rw [sourceRowsAt1680]
    exact rowSound1680 B hB hF
  · have he : k = (1681 : Fin 2425) := Fin.ext h1681
    subst k
    rw [sourceRowsAt1681]
    exact rowSound1681 B hB hF
  · have he : k = (1682 : Fin 2425) := Fin.ext h1682
    subst k
    rw [sourceRowsAt1682]
    exact rowSound1682 B hB hF
  · have he : k = (1683 : Fin 2425) := Fin.ext h1683
    subst k
    rw [sourceRowsAt1683]
    exact rowSound1683 B hB hF
  · have he : k = (1684 : Fin 2425) := Fin.ext h1684
    subst k
    rw [sourceRowsAt1684]
    exact rowSound1684_e B hB hF
  · have he : k = (1685 : Fin 2425) := Fin.ext h1685
    subst k
    rw [sourceRowsAt1685]
    exact rowSound1685 B hB hF
  · have he : k = (1686 : Fin 2425) := Fin.ext h1686
    subst k
    rw [sourceRowsAt1686]
    exact rowSound1686_e B hB hF
  · have he : k = (1687 : Fin 2425) := Fin.ext h1687
    subst k
    rw [sourceRowsAt1687]
    exact rowSound1687_e B hB hF
  · have he : k = (1688 : Fin 2425) := Fin.ext h1688
    subst k
    rw [sourceRowsAt1688]
    exact rowSound1688 B hB hF
  · have he : k = (1689 : Fin 2425) := Fin.ext h1689
    subst k
    rw [sourceRowsAt1689]
    exact rowSound1689 B hB hF
  · have he : k = (1690 : Fin 2425) := Fin.ext h1690
    subst k
    rw [sourceRowsAt1690]
    exact rowSound1690 B hB hF
  · have he : k = (1691 : Fin 2425) := Fin.ext h1691
    subst k
    rw [sourceRowsAt1691]
    exact rowSound1691 B hB hF
  · have he : k = (1692 : Fin 2425) := Fin.ext h1692
    subst k
    rw [sourceRowsAt1692]
    exact rowSound1692 B hB hF
  · have he : k = (1693 : Fin 2425) := Fin.ext h1693
    subst k
    rw [sourceRowsAt1693]
    exact rowSound1693 B hB hF
  · have he : k = (1694 : Fin 2425) := Fin.ext h1694
    subst k
    rw [sourceRowsAt1694]
    exact rowSound1694 B hB hF
  · have he : k = (1695 : Fin 2425) := Fin.ext h1695
    subst k
    rw [sourceRowsAt1695]
    exact rowSound1695 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105_e_oai
