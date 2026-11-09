-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2074_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:59:20.775096+00:00
-- url     : https://prove2.me/submissions/02c4fe5a-f3db-4f4f-8056-5db1f2ca07a3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical281
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36068 raw36068Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw36068 raw36068Labels = mixedMoment B raw36068step0 raw36068step0Labels := by
      have hz : ∀ j, raw36068 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36068step0 = (fun i j => raw36068 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36068step0 raw36068; decide +kernel
      have hl : raw36068step0Labels = raw36068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36068 raw36068Labels permutation346 hz
    mixedMoment B raw36068step0 raw36068step0Labels = mixedMoment B raw36068step1 raw36068step1Labels := by
      have ha : raw36068step1 = (fun i j => raw36068step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36068step1 raw36068step0; decide +kernel
      have hl : raw36068step1Labels = raw36068step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36068step0 raw36068step0Labels permutation58 permutation7
    mixedMoment B raw36068step1 raw36068step1Labels = mixedMoment B raw36068step2 raw36068step2Labels := by
      have ha : raw36068step2 = -raw36068step1 := by apply Matrix.ext; change ∀ i j, raw36068step2 i j = -(raw36068step1 i j); unfold raw36068step2 raw36068step1; decide +kernel
      have hl : raw36068step2Labels = raw36068step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36068step2 raw36068step2Labels = mixedMoment B raw36068step3 raw36068step3Labels := by
      have ha : raw36068step3 = raw36068step2 := by apply Matrix.ext; unfold raw36068step3 raw36068step2; decide +kernel
      have hl : raw36068step2Labels = labelEmbedding1 ∘ raw36068step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36068step2 raw36068step2Labels raw36068step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical36069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36069 raw36069Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw36069 raw36069Labels = mixedMoment B raw36069step0 raw36069step0Labels := by
      have ha : raw36069step0 = (fun i j => raw36069 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36069step0 raw36069; decide +kernel
      have hl : raw36069step0Labels = raw36069Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36069 raw36069Labels permutation267 permutation7
    mixedMoment B raw36069step0 raw36069step0Labels = mixedMoment B raw36069step1 raw36069step1Labels := by
      have ha : raw36069step1 = -raw36069step0 := by apply Matrix.ext; change ∀ i j, raw36069step1 i j = -(raw36069step0 i j); unfold raw36069step1 raw36069step0; decide +kernel
      have hl : raw36069step1Labels = raw36069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36069step1 raw36069step1Labels = mixedMoment B raw36069step2 raw36069step2Labels := by
      have ha : raw36069step2 = raw36069step1 := by apply Matrix.ext; unfold raw36069step2 raw36069step1; decide +kernel
      have hl : raw36069step1Labels = labelEmbedding1 ∘ raw36069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36069step1 raw36069step1Labels raw36069step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical36070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36070 raw36070Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw36070 raw36070Labels = mixedMoment B raw36070step0 raw36070step0Labels := by
      have hz : ∀ j, raw36070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36070step0 = (fun i j => raw36070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36070step0 raw36070; decide +kernel
      have hl : raw36070step0Labels = raw36070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36070 raw36070Labels permutation346 hz
    mixedMoment B raw36070step0 raw36070step0Labels = mixedMoment B raw36070step1 raw36070step1Labels := by
      have ha : raw36070step1 = (fun i j => raw36070step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36070step1 raw36070step0; decide +kernel
      have hl : raw36070step1Labels = raw36070step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36070step0 raw36070step0Labels permutation58 permutation7
    mixedMoment B raw36070step1 raw36070step1Labels = mixedMoment B raw36070step2 raw36070step2Labels := by
      have ha : raw36070step2 = -raw36070step1 := by apply Matrix.ext; change ∀ i j, raw36070step2 i j = -(raw36070step1 i j); unfold raw36070step2 raw36070step1; decide +kernel
      have hl : raw36070step2Labels = raw36070step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36070step2 raw36070step2Labels = mixedMoment B raw36070step3 raw36070step3Labels := by
      have ha : raw36070step3 = raw36070step2 := by apply Matrix.ext; unfold raw36070step3 raw36070step2; decide +kernel
      have hl : raw36070step2Labels = labelEmbedding1 ∘ raw36070step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36070step2 raw36070step2Labels raw36070step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical36071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36071 raw36071Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw36071 raw36071Labels = mixedMoment B raw36071step0 raw36071step0Labels := by
      have hz : ∀ j, raw36071 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36071step0 = (fun i j => raw36071 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36071step0 raw36071; decide +kernel
      have hl : raw36071step0Labels = raw36071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36071 raw36071Labels permutation520 hz
    mixedMoment B raw36071step0 raw36071step0Labels = mixedMoment B raw36071step1 raw36071step1Labels := by
      have hz : ∀ j, raw36071step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36071step1 = (fun i j => raw36071step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36071step1 raw36071step0; decide +kernel
      have hl : raw36071step1Labels = raw36071step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36071step0 raw36071step0Labels permutation80 hz
    mixedMoment B raw36071step1 raw36071step1Labels = mixedMoment B raw36071step2 raw36071step2Labels := by
      have ha : raw36071step2 = (fun i j => raw36071step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36071step2 raw36071step1; decide +kernel
      have hl : raw36071step2Labels = raw36071step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36071step1 raw36071step1Labels permutation14 permutation7
    mixedMoment B raw36071step2 raw36071step2Labels = mixedMoment B raw36071step3 raw36071step3Labels := by
      have ha : raw36071step3 = -raw36071step2 := by apply Matrix.ext; change ∀ i j, raw36071step3 i j = -(raw36071step2 i j); unfold raw36071step3 raw36071step2; decide +kernel
      have hl : raw36071step3Labels = raw36071step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36071step3 raw36071step3Labels = mixedMoment B raw36071step4 raw36071step4Labels := by
      have ha : raw36071step4 = raw36071step3 := by apply Matrix.ext; unfold raw36071step4 raw36071step3; decide +kernel
      have hl : raw36071step3Labels = labelEmbedding1 ∘ raw36071step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36071step3 raw36071step3Labels raw36071step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical36072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36072 raw36072Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw36072 raw36072Labels = mixedMoment B raw36072step0 raw36072step0Labels := by
      have hz : ∀ j, raw36072 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36072step0 = (fun i j => raw36072 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36072step0 raw36072; decide +kernel
      have hl : raw36072step0Labels = raw36072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36072 raw36072Labels permutation346 hz
    mixedMoment B raw36072step0 raw36072step0Labels = mixedMoment B raw36072step1 raw36072step1Labels := by
      have ha : raw36072step1 = (fun i j => raw36072step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36072step1 raw36072step0; decide +kernel
      have hl : raw36072step1Labels = raw36072step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36072step0 raw36072step0Labels permutation58 permutation7
    mixedMoment B raw36072step1 raw36072step1Labels = mixedMoment B raw36072step2 raw36072step2Labels := by
      have ha : raw36072step2 = -raw36072step1 := by apply Matrix.ext; change ∀ i j, raw36072step2 i j = -(raw36072step1 i j); unfold raw36072step2 raw36072step1; decide +kernel
      have hl : raw36072step2Labels = raw36072step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36072step2 raw36072step2Labels = mixedMoment B raw36072step3 raw36072step3Labels := by
      have ha : raw36072step3 = raw36072step2 := by apply Matrix.ext; unfold raw36072step3 raw36072step2; decide +kernel
      have hl : raw36072step2Labels = labelEmbedding1 ∘ raw36072step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36072step2 raw36072step2Labels raw36072step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical36073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36073 raw36073Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw36073 raw36073Labels = mixedMoment B raw36073step0 raw36073step0Labels := by
      have hz : ∀ j, raw36073 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36073step0 = (fun i j => raw36073 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36073step0 raw36073; decide +kernel
      have hl : raw36073step0Labels = raw36073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36073 raw36073Labels permutation346 hz
    mixedMoment B raw36073step0 raw36073step0Labels = mixedMoment B raw36073step1 raw36073step1Labels := by
      have ha : raw36073step1 = (fun i j => raw36073step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36073step1 raw36073step0; decide +kernel
      have hl : raw36073step1Labels = raw36073step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36073step0 raw36073step0Labels permutation43 permutation5
    mixedMoment B raw36073step1 raw36073step1Labels = mixedMoment B raw36073step2 raw36073step2Labels := by
      have ha : raw36073step2 = -raw36073step1 := by apply Matrix.ext; change ∀ i j, raw36073step2 i j = -(raw36073step1 i j); unfold raw36073step2 raw36073step1; decide +kernel
      have hl : raw36073step2Labels = raw36073step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36073step2 raw36073step2Labels = mixedMoment B raw36073step3 raw36073step3Labels := by
      have ha : raw36073step3 = raw36073step2 := by apply Matrix.ext; unfold raw36073step3 raw36073step2; decide +kernel
      have hl : raw36073step2Labels = labelEmbedding1 ∘ raw36073step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36073step2 raw36073step2Labels raw36073step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2254 node2254Labels := by rfl

theorem canonical36074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36074 raw36074Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw36074 raw36074Labels = mixedMoment B raw36074step0 raw36074step0Labels := by
      have ha : raw36074step0 = (fun i j => raw36074 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36074step0 raw36074; decide +kernel
      have hl : raw36074step0Labels = raw36074Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36074 raw36074Labels permutation267 permutation7
    mixedMoment B raw36074step0 raw36074step0Labels = mixedMoment B raw36074step1 raw36074step1Labels := by
      have ha : raw36074step1 = -raw36074step0 := by apply Matrix.ext; change ∀ i j, raw36074step1 i j = -(raw36074step0 i j); unfold raw36074step1 raw36074step0; decide +kernel
      have hl : raw36074step1Labels = raw36074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36074step1 raw36074step1Labels = mixedMoment B raw36074step2 raw36074step2Labels := by
      have ha : raw36074step2 = raw36074step1 := by apply Matrix.ext; unfold raw36074step2 raw36074step1; decide +kernel
      have hl : raw36074step1Labels = labelEmbedding1 ∘ raw36074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36074step1 raw36074step1Labels raw36074step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3016 node3016Labels := by rfl

theorem canonical36075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36075 raw36075Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw36075 raw36075Labels = mixedMoment B raw36075step0 raw36075step0Labels := by
      have hz : ∀ j, raw36075 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36075step0 = (fun i j => raw36075 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36075step0 raw36075; decide +kernel
      have hl : raw36075step0Labels = raw36075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36075 raw36075Labels permutation346 hz
    mixedMoment B raw36075step0 raw36075step0Labels = mixedMoment B raw36075step1 raw36075step1Labels := by
      have ha : raw36075step1 = (fun i j => raw36075step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36075step1 raw36075step0; decide +kernel
      have hl : raw36075step1Labels = raw36075step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36075step0 raw36075step0Labels permutation58 permutation7
    mixedMoment B raw36075step1 raw36075step1Labels = mixedMoment B raw36075step2 raw36075step2Labels := by
      have ha : raw36075step2 = -raw36075step1 := by apply Matrix.ext; change ∀ i j, raw36075step2 i j = -(raw36075step1 i j); unfold raw36075step2 raw36075step1; decide +kernel
      have hl : raw36075step2Labels = raw36075step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36075step2 raw36075step2Labels = mixedMoment B raw36075step3 raw36075step3Labels := by
      have ha : raw36075step3 = raw36075step2 := by apply Matrix.ext; unfold raw36075step3 raw36075step2; decide +kernel
      have hl : raw36075step2Labels = labelEmbedding1 ∘ raw36075step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36075step2 raw36075step2Labels raw36075step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical36076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36076 raw36076Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw36076 raw36076Labels = mixedMoment B raw36076step0 raw36076step0Labels := by
      have hz : ∀ j, raw36076 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36076step0 = (fun i j => raw36076 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36076step0 raw36076; decide +kernel
      have hl : raw36076step0Labels = raw36076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36076 raw36076Labels permutation520 hz
    mixedMoment B raw36076step0 raw36076step0Labels = mixedMoment B raw36076step1 raw36076step1Labels := by
      have hz : ∀ j, raw36076step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36076step1 = (fun i j => raw36076step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36076step1 raw36076step0; decide +kernel
      have hl : raw36076step1Labels = raw36076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36076step0 raw36076step0Labels permutation80 hz
    mixedMoment B raw36076step1 raw36076step1Labels = mixedMoment B raw36076step2 raw36076step2Labels := by
      have ha : raw36076step2 = (fun i j => raw36076step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36076step2 raw36076step1; decide +kernel
      have hl : raw36076step2Labels = raw36076step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36076step1 raw36076step1Labels permutation14 permutation7
    mixedMoment B raw36076step2 raw36076step2Labels = mixedMoment B raw36076step3 raw36076step3Labels := by
      have ha : raw36076step3 = -raw36076step2 := by apply Matrix.ext; change ∀ i j, raw36076step3 i j = -(raw36076step2 i j); unfold raw36076step3 raw36076step2; decide +kernel
      have hl : raw36076step3Labels = raw36076step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36076step3 raw36076step3Labels = mixedMoment B raw36076step4 raw36076step4Labels := by
      have ha : raw36076step4 = raw36076step3 := by apply Matrix.ext; unfold raw36076step4 raw36076step3; decide +kernel
      have hl : raw36076step3Labels = labelEmbedding1 ∘ raw36076step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36076step3 raw36076step3Labels raw36076step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical36077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36077 raw36077Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw36077 raw36077Labels = mixedMoment B raw36077step0 raw36077step0Labels := by
      have hz : ∀ j, raw36077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36077step0 = (fun i j => raw36077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36077step0 raw36077; decide +kernel
      have hl : raw36077step0Labels = raw36077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36077 raw36077Labels permutation346 hz
    mixedMoment B raw36077step0 raw36077step0Labels = mixedMoment B raw36077step1 raw36077step1Labels := by
      have ha : raw36077step1 = (fun i j => raw36077step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36077step1 raw36077step0; decide +kernel
      have hl : raw36077step1Labels = raw36077step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36077step0 raw36077step0Labels permutation58 permutation7
    mixedMoment B raw36077step1 raw36077step1Labels = mixedMoment B raw36077step2 raw36077step2Labels := by
      have ha : raw36077step2 = -raw36077step1 := by apply Matrix.ext; change ∀ i j, raw36077step2 i j = -(raw36077step1 i j); unfold raw36077step2 raw36077step1; decide +kernel
      have hl : raw36077step2Labels = raw36077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36077step2 raw36077step2Labels = mixedMoment B raw36077step3 raw36077step3Labels := by
      have ha : raw36077step3 = raw36077step2 := by apply Matrix.ext; unfold raw36077step3 raw36077step2; decide +kernel
      have hl : raw36077step2Labels = labelEmbedding1 ∘ raw36077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36077step2 raw36077step2Labels raw36077step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical36078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36078 raw36078Labels = mixedMoment B node2248 node2248Labels := by
  calc
    mixedMoment B raw36078 raw36078Labels = mixedMoment B raw36078step0 raw36078step0Labels := by
      have ha : raw36078step0 = (fun i j => raw36078 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36078step0 raw36078; decide +kernel
      have hl : raw36078step0Labels = raw36078Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36078 raw36078Labels permutation218 permutation5
    mixedMoment B raw36078step0 raw36078step0Labels = mixedMoment B raw36078step1 raw36078step1Labels := by
      have ha : raw36078step1 = -raw36078step0 := by apply Matrix.ext; change ∀ i j, raw36078step1 i j = -(raw36078step0 i j); unfold raw36078step1 raw36078step0; decide +kernel
      have hl : raw36078step1Labels = raw36078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36078step1 raw36078step1Labels = mixedMoment B raw36078step2 raw36078step2Labels := by
      have ha : raw36078step2 = raw36078step1 := by apply Matrix.ext; unfold raw36078step2 raw36078step1; decide +kernel
      have hl : raw36078step1Labels = labelEmbedding1 ∘ raw36078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36078step1 raw36078step1Labels raw36078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2248 node2248Labels := by rfl

theorem canonical36079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36079 raw36079Labels = mixedMoment B node2141 node2141Labels := by
  calc
    mixedMoment B raw36079 raw36079Labels = mixedMoment B raw36079step0 raw36079step0Labels := by
      have ha : raw36079step0 = (fun i j => raw36079 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36079step0 raw36079; decide +kernel
      have hl : raw36079step0Labels = raw36079Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36079 raw36079Labels permutation267 permutation7
    mixedMoment B raw36079step0 raw36079step0Labels = mixedMoment B raw36079step1 raw36079step1Labels := by
      have ha : raw36079step1 = -raw36079step0 := by apply Matrix.ext; change ∀ i j, raw36079step1 i j = -(raw36079step0 i j); unfold raw36079step1 raw36079step0; decide +kernel
      have hl : raw36079step1Labels = raw36079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36079step1 raw36079step1Labels = mixedMoment B raw36079step2 raw36079step2Labels := by
      have ha : raw36079step2 = raw36079step1 := by apply Matrix.ext; unfold raw36079step2 raw36079step1; decide +kernel
      have hl : raw36079step1Labels = labelEmbedding1 ∘ raw36079step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36079step1 raw36079step1Labels raw36079step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2141 node2141Labels := by rfl

theorem canonical36080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36080 raw36080Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw36080 raw36080Labels = mixedMoment B raw36080step0 raw36080step0Labels := by
      have ha : raw36080step0 = (fun i j => raw36080 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36080step0 raw36080; decide +kernel
      have hl : raw36080step0Labels = raw36080Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36080 raw36080Labels permutation267 permutation7
    mixedMoment B raw36080step0 raw36080step0Labels = mixedMoment B raw36080step1 raw36080step1Labels := by
      have ha : raw36080step1 = -raw36080step0 := by apply Matrix.ext; change ∀ i j, raw36080step1 i j = -(raw36080step0 i j); unfold raw36080step1 raw36080step0; decide +kernel
      have hl : raw36080step1Labels = raw36080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36080step1 raw36080step1Labels = mixedMoment B raw36080step2 raw36080step2Labels := by
      have ha : raw36080step2 = raw36080step1 := by apply Matrix.ext; unfold raw36080step2 raw36080step1; decide +kernel
      have hl : raw36080step1Labels = labelEmbedding1 ∘ raw36080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36080step1 raw36080step1Labels raw36080step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

theorem canonical36081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36081 raw36081Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw36081 raw36081Labels = mixedMoment B raw36081step0 raw36081step0Labels := by
      have hz : ∀ j, raw36081 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36081step0 = (fun i j => raw36081 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36081step0 raw36081; decide +kernel
      have hl : raw36081step0Labels = raw36081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36081 raw36081Labels permutation520 hz
    mixedMoment B raw36081step0 raw36081step0Labels = mixedMoment B raw36081step1 raw36081step1Labels := by
      have ha : raw36081step1 = (fun i j => raw36081step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36081step1 raw36081step0; decide +kernel
      have hl : raw36081step1Labels = raw36081step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36081step0 raw36081step0Labels permutation56 permutation7
    mixedMoment B raw36081step1 raw36081step1Labels = mixedMoment B raw36081step2 raw36081step2Labels := by
      have ha : raw36081step2 = -raw36081step1 := by apply Matrix.ext; change ∀ i j, raw36081step2 i j = -(raw36081step1 i j); unfold raw36081step2 raw36081step1; decide +kernel
      have hl : raw36081step2Labels = raw36081step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36081step2 raw36081step2Labels = mixedMoment B raw36081step3 raw36081step3Labels := by
      have ha : raw36081step3 = raw36081step2 := by apply Matrix.ext; unfold raw36081step3 raw36081step2; decide +kernel
      have hl : raw36081step2Labels = labelEmbedding1 ∘ raw36081step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36081step2 raw36081step2Labels raw36081step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical36082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36082 raw36082Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw36082 raw36082Labels = mixedMoment B raw36082step0 raw36082step0Labels := by
      have ha : raw36082step0 = (fun i j => raw36082 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36082step0 raw36082; decide +kernel
      have hl : raw36082step0Labels = raw36082Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36082 raw36082Labels permutation267 permutation7
    mixedMoment B raw36082step0 raw36082step0Labels = mixedMoment B raw36082step1 raw36082step1Labels := by
      have ha : raw36082step1 = -raw36082step0 := by apply Matrix.ext; change ∀ i j, raw36082step1 i j = -(raw36082step0 i j); unfold raw36082step1 raw36082step0; decide +kernel
      have hl : raw36082step1Labels = raw36082step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36082step1 raw36082step1Labels = mixedMoment B raw36082step2 raw36082step2Labels := by
      have ha : raw36082step2 = raw36082step1 := by apply Matrix.ext; unfold raw36082step2 raw36082step1; decide +kernel
      have hl : raw36082step1Labels = labelEmbedding1 ∘ raw36082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36082step1 raw36082step1Labels raw36082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2662 node2662Labels := by rfl

theorem canonical36083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36083 raw36083Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw36083 raw36083Labels = mixedMoment B raw36083step0 raw36083step0Labels := by
      have hz : ∀ j, raw36083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36083step0 = (fun i j => raw36083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36083step0 raw36083; decide +kernel
      have hl : raw36083step0Labels = raw36083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36083 raw36083Labels permutation346 hz
    mixedMoment B raw36083step0 raw36083step0Labels = mixedMoment B raw36083step1 raw36083step1Labels := by
      have ha : raw36083step1 = (fun i j => raw36083step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36083step1 raw36083step0; decide +kernel
      have hl : raw36083step1Labels = raw36083step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36083step0 raw36083step0Labels permutation51 permutation5
    mixedMoment B raw36083step1 raw36083step1Labels = mixedMoment B raw36083step2 raw36083step2Labels := by
      have ha : raw36083step2 = -raw36083step1 := by apply Matrix.ext; change ∀ i j, raw36083step2 i j = -(raw36083step1 i j); unfold raw36083step2 raw36083step1; decide +kernel
      have hl : raw36083step2Labels = raw36083step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36083step2 raw36083step2Labels = mixedMoment B raw36083step3 raw36083step3Labels := by
      have ha : raw36083step3 = raw36083step2 := by apply Matrix.ext; unfold raw36083step3 raw36083step2; decide +kernel
      have hl : raw36083step2Labels = labelEmbedding1 ∘ raw36083step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36083step2 raw36083step2Labels raw36083step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

theorem canonical36084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36084 raw36084Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw36084 raw36084Labels = mixedMoment B raw36084step0 raw36084step0Labels := by
      have hz : ∀ j, raw36084 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36084step0 = (fun i j => raw36084 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36084step0 raw36084; decide +kernel
      have hl : raw36084step0Labels = raw36084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36084 raw36084Labels permutation346 hz
    mixedMoment B raw36084step0 raw36084step0Labels = mixedMoment B raw36084step1 raw36084step1Labels := by
      have ha : raw36084step1 = (fun i j => raw36084step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36084step1 raw36084step0; decide +kernel
      have hl : raw36084step1Labels = raw36084step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36084step0 raw36084step0Labels permutation58 permutation7
    mixedMoment B raw36084step1 raw36084step1Labels = mixedMoment B raw36084step2 raw36084step2Labels := by
      have ha : raw36084step2 = -raw36084step1 := by apply Matrix.ext; change ∀ i j, raw36084step2 i j = -(raw36084step1 i j); unfold raw36084step2 raw36084step1; decide +kernel
      have hl : raw36084step2Labels = raw36084step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36084step2 raw36084step2Labels = mixedMoment B raw36084step3 raw36084step3Labels := by
      have ha : raw36084step3 = raw36084step2 := by apply Matrix.ext; unfold raw36084step3 raw36084step2; decide +kernel
      have hl : raw36084step2Labels = labelEmbedding1 ∘ raw36084step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36084step2 raw36084step2Labels raw36084step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

theorem canonical36085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36085 raw36085Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw36085 raw36085Labels = mixedMoment B raw36085step0 raw36085step0Labels := by
      have ha : raw36085step0 = (fun i j => raw36085 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36085step0 raw36085; decide +kernel
      have hl : raw36085step0Labels = raw36085Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36085 raw36085Labels permutation267 permutation7
    mixedMoment B raw36085step0 raw36085step0Labels = mixedMoment B raw36085step1 raw36085step1Labels := by
      have ha : raw36085step1 = -raw36085step0 := by apply Matrix.ext; change ∀ i j, raw36085step1 i j = -(raw36085step0 i j); unfold raw36085step1 raw36085step0; decide +kernel
      have hl : raw36085step1Labels = raw36085step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36085step1 raw36085step1Labels = mixedMoment B raw36085step2 raw36085step2Labels := by
      have ha : raw36085step2 = raw36085step1 := by apply Matrix.ext; unfold raw36085step2 raw36085step1; decide +kernel
      have hl : raw36085step1Labels = labelEmbedding1 ∘ raw36085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36085step1 raw36085step1Labels raw36085step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

theorem canonical36086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36086 raw36086Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw36086 raw36086Labels = mixedMoment B raw36086step0 raw36086step0Labels := by
      have hz : ∀ j, raw36086 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36086step0 = (fun i j => raw36086 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36086step0 raw36086; decide +kernel
      have hl : raw36086step0Labels = raw36086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36086 raw36086Labels permutation520 hz
    mixedMoment B raw36086step0 raw36086step0Labels = mixedMoment B raw36086step1 raw36086step1Labels := by
      have hz : ∀ j, raw36086step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36086step1 = (fun i j => raw36086step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36086step1 raw36086step0; decide +kernel
      have hl : raw36086step1Labels = raw36086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36086step0 raw36086step0Labels permutation80 hz
    mixedMoment B raw36086step1 raw36086step1Labels = mixedMoment B raw36086step2 raw36086step2Labels := by
      have ha : raw36086step2 = (fun i j => raw36086step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36086step2 raw36086step1; decide +kernel
      have hl : raw36086step2Labels = raw36086step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36086step1 raw36086step1Labels permutation14 permutation7
    mixedMoment B raw36086step2 raw36086step2Labels = mixedMoment B raw36086step3 raw36086step3Labels := by
      have ha : raw36086step3 = -raw36086step2 := by apply Matrix.ext; change ∀ i j, raw36086step3 i j = -(raw36086step2 i j); unfold raw36086step3 raw36086step2; decide +kernel
      have hl : raw36086step3Labels = raw36086step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36086step3 raw36086step3Labels = mixedMoment B raw36086step4 raw36086step4Labels := by
      have ha : raw36086step4 = raw36086step3 := by apply Matrix.ext; unfold raw36086step4 raw36086step3; decide +kernel
      have hl : raw36086step3Labels = labelEmbedding1 ∘ raw36086step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36086step3 raw36086step3Labels raw36086step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical36087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36087 raw36087Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw36087 raw36087Labels = mixedMoment B raw36087step0 raw36087step0Labels := by
      have hz : ∀ j, raw36087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36087step0 = (fun i j => raw36087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36087step0 raw36087; decide +kernel
      have hl : raw36087step0Labels = raw36087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36087 raw36087Labels permutation346 hz
    mixedMoment B raw36087step0 raw36087step0Labels = mixedMoment B raw36087step1 raw36087step1Labels := by
      have ha : raw36087step1 = (fun i j => raw36087step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36087step1 raw36087step0; decide +kernel
      have hl : raw36087step1Labels = raw36087step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36087step0 raw36087step0Labels permutation58 permutation7
    mixedMoment B raw36087step1 raw36087step1Labels = mixedMoment B raw36087step2 raw36087step2Labels := by
      have ha : raw36087step2 = -raw36087step1 := by apply Matrix.ext; change ∀ i j, raw36087step2 i j = -(raw36087step1 i j); unfold raw36087step2 raw36087step1; decide +kernel
      have hl : raw36087step2Labels = raw36087step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36087step2 raw36087step2Labels = mixedMoment B raw36087step3 raw36087step3Labels := by
      have ha : raw36087step3 = raw36087step2 := by apply Matrix.ext; unfold raw36087step3 raw36087step2; decide +kernel
      have hl : raw36087step2Labels = labelEmbedding1 ∘ raw36087step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36087step2 raw36087step2Labels raw36087step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

theorem canonical36088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36088 raw36088Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw36088 raw36088Labels = mixedMoment B raw36088step0 raw36088step0Labels := by
      have hz : ∀ j, raw36088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36088step0 = (fun i j => raw36088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36088step0 raw36088; decide +kernel
      have hl : raw36088step0Labels = raw36088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36088 raw36088Labels permutation346 hz
    mixedMoment B raw36088step0 raw36088step0Labels = mixedMoment B raw36088step1 raw36088step1Labels := by
      have ha : raw36088step1 = (fun i j => raw36088step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36088step1 raw36088step0; decide +kernel
      have hl : raw36088step1Labels = raw36088step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36088step0 raw36088step0Labels permutation42 permutation5
    mixedMoment B raw36088step1 raw36088step1Labels = mixedMoment B raw36088step2 raw36088step2Labels := by
      have ha : raw36088step2 = -raw36088step1 := by apply Matrix.ext; change ∀ i j, raw36088step2 i j = -(raw36088step1 i j); unfold raw36088step2 raw36088step1; decide +kernel
      have hl : raw36088step2Labels = raw36088step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36088step2 raw36088step2Labels = mixedMoment B raw36088step3 raw36088step3Labels := by
      have ha : raw36088step3 = raw36088step2 := by apply Matrix.ext; unfold raw36088step3 raw36088step2; decide +kernel
      have hl : raw36088step2Labels = labelEmbedding1 ∘ raw36088step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36088step2 raw36088step2Labels raw36088step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2249 node2249Labels := by rfl

theorem canonical36089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36089 raw36089Labels = mixedMoment B node2157 node2157Labels := by
  calc
    mixedMoment B raw36089 raw36089Labels = mixedMoment B raw36089step0 raw36089step0Labels := by
      have hz : ∀ j, raw36089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36089step0 = (fun i j => raw36089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36089step0 raw36089; decide +kernel
      have hl : raw36089step0Labels = raw36089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36089 raw36089Labels permutation346 hz
    mixedMoment B raw36089step0 raw36089step0Labels = mixedMoment B raw36089step1 raw36089step1Labels := by
      have ha : raw36089step1 = (fun i j => raw36089step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36089step1 raw36089step0; decide +kernel
      have hl : raw36089step1Labels = raw36089step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36089step0 raw36089step0Labels permutation58 permutation7
    mixedMoment B raw36089step1 raw36089step1Labels = mixedMoment B raw36089step2 raw36089step2Labels := by
      have ha : raw36089step2 = -raw36089step1 := by apply Matrix.ext; change ∀ i j, raw36089step2 i j = -(raw36089step1 i j); unfold raw36089step2 raw36089step1; decide +kernel
      have hl : raw36089step2Labels = raw36089step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36089step2 raw36089step2Labels = mixedMoment B raw36089step3 raw36089step3Labels := by
      have ha : raw36089step3 = raw36089step2 := by apply Matrix.ext; unfold raw36089step3 raw36089step2; decide +kernel
      have hl : raw36089step2Labels = labelEmbedding1 ∘ raw36089step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36089step2 raw36089step2Labels raw36089step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2157 node2157Labels := by rfl

theorem canonical36090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36090 raw36090Labels = mixedMoment B node2654 node2654Labels := by
  calc
    mixedMoment B raw36090 raw36090Labels = mixedMoment B raw36090step0 raw36090step0Labels := by
      have ha : raw36090step0 = (fun i j => raw36090 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36090step0 raw36090; decide +kernel
      have hl : raw36090step0Labels = raw36090Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36090 raw36090Labels permutation267 permutation7
    mixedMoment B raw36090step0 raw36090step0Labels = mixedMoment B raw36090step1 raw36090step1Labels := by
      have ha : raw36090step1 = -raw36090step0 := by apply Matrix.ext; change ∀ i j, raw36090step1 i j = -(raw36090step0 i j); unfold raw36090step1 raw36090step0; decide +kernel
      have hl : raw36090step1Labels = raw36090step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36090step1 raw36090step1Labels = mixedMoment B raw36090step2 raw36090step2Labels := by
      have ha : raw36090step2 = raw36090step1 := by apply Matrix.ext; unfold raw36090step2 raw36090step1; decide +kernel
      have hl : raw36090step1Labels = labelEmbedding1 ∘ raw36090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36090step1 raw36090step1Labels raw36090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2654 node2654Labels := by rfl

theorem canonical36091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36091 raw36091Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw36091 raw36091Labels = mixedMoment B raw36091step0 raw36091step0Labels := by
      have hz : ∀ j, raw36091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36091step0 = (fun i j => raw36091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36091step0 raw36091; decide +kernel
      have hl : raw36091step0Labels = raw36091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36091 raw36091Labels permutation346 hz
    mixedMoment B raw36091step0 raw36091step0Labels = mixedMoment B raw36091step1 raw36091step1Labels := by
      have ha : raw36091step1 = (fun i j => raw36091step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36091step1 raw36091step0; decide +kernel
      have hl : raw36091step1Labels = raw36091step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36091step0 raw36091step0Labels permutation58 permutation7
    mixedMoment B raw36091step1 raw36091step1Labels = mixedMoment B raw36091step2 raw36091step2Labels := by
      have ha : raw36091step2 = -raw36091step1 := by apply Matrix.ext; change ∀ i j, raw36091step2 i j = -(raw36091step1 i j); unfold raw36091step2 raw36091step1; decide +kernel
      have hl : raw36091step2Labels = raw36091step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36091step2 raw36091step2Labels = mixedMoment B raw36091step3 raw36091step3Labels := by
      have ha : raw36091step3 = raw36091step2 := by apply Matrix.ext; unfold raw36091step3 raw36091step2; decide +kernel
      have hl : raw36091step2Labels = labelEmbedding1 ∘ raw36091step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36091step2 raw36091step2Labels raw36091step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

theorem canonical36092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36092 raw36092Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw36092 raw36092Labels = mixedMoment B raw36092step0 raw36092step0Labels := by
      have hz : ∀ j, raw36092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36092step0 = (fun i j => raw36092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36092step0 raw36092; decide +kernel
      have hl : raw36092step0Labels = raw36092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36092 raw36092Labels permutation346 hz
    mixedMoment B raw36092step0 raw36092step0Labels = mixedMoment B raw36092step1 raw36092step1Labels := by
      have ha : raw36092step1 = (fun i j => raw36092step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36092step1 raw36092step0; decide +kernel
      have hl : raw36092step1Labels = raw36092step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36092step0 raw36092step0Labels permutation58 permutation7
    mixedMoment B raw36092step1 raw36092step1Labels = mixedMoment B raw36092step2 raw36092step2Labels := by
      have ha : raw36092step2 = -raw36092step1 := by apply Matrix.ext; change ∀ i j, raw36092step2 i j = -(raw36092step1 i j); unfold raw36092step2 raw36092step1; decide +kernel
      have hl : raw36092step2Labels = raw36092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36092step2 raw36092step2Labels = mixedMoment B raw36092step3 raw36092step3Labels := by
      have ha : raw36092step3 = raw36092step2 := by apply Matrix.ext; unfold raw36092step3 raw36092step2; decide +kernel
      have hl : raw36092step2Labels = labelEmbedding1 ∘ raw36092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36092step2 raw36092step2Labels raw36092step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

theorem canonical36093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36093 raw36093Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw36093 raw36093Labels = mixedMoment B raw36093step0 raw36093step0Labels := by
      have hz : ∀ j, raw36093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36093step0 = (fun i j => raw36093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36093step0 raw36093; decide +kernel
      have hl : raw36093step0Labels = raw36093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36093 raw36093Labels permutation346 hz
    mixedMoment B raw36093step0 raw36093step0Labels = mixedMoment B raw36093step1 raw36093step1Labels := by
      have ha : raw36093step1 = (fun i j => raw36093step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36093step1 raw36093step0; decide +kernel
      have hl : raw36093step1Labels = raw36093step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36093step0 raw36093step0Labels permutation38 permutation5
    mixedMoment B raw36093step1 raw36093step1Labels = mixedMoment B raw36093step2 raw36093step2Labels := by
      have ha : raw36093step2 = -raw36093step1 := by apply Matrix.ext; change ∀ i j, raw36093step2 i j = -(raw36093step1 i j); unfold raw36093step2 raw36093step1; decide +kernel
      have hl : raw36093step2Labels = raw36093step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36093step2 raw36093step2Labels = mixedMoment B raw36093step3 raw36093step3Labels := by
      have ha : raw36093step3 = raw36093step2 := by apply Matrix.ext; unfold raw36093step3 raw36093step2; decide +kernel
      have hl : raw36093step2Labels = labelEmbedding1 ∘ raw36093step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36093step2 raw36093step2Labels raw36093step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

theorem canonical36094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36094 raw36094Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw36094 raw36094Labels = mixedMoment B raw36094step0 raw36094step0Labels := by
      have hz : ∀ j, raw36094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36094step0 = (fun i j => raw36094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36094step0 raw36094; decide +kernel
      have hl : raw36094step0Labels = raw36094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36094 raw36094Labels permutation346 hz
    mixedMoment B raw36094step0 raw36094step0Labels = mixedMoment B raw36094step1 raw36094step1Labels := by
      have ha : raw36094step1 = (fun i j => raw36094step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36094step1 raw36094step0; decide +kernel
      have hl : raw36094step1Labels = raw36094step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36094step0 raw36094step0Labels permutation58 permutation7
    mixedMoment B raw36094step1 raw36094step1Labels = mixedMoment B raw36094step2 raw36094step2Labels := by
      have ha : raw36094step2 = -raw36094step1 := by apply Matrix.ext; change ∀ i j, raw36094step2 i j = -(raw36094step1 i j); unfold raw36094step2 raw36094step1; decide +kernel
      have hl : raw36094step2Labels = raw36094step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36094step2 raw36094step2Labels = mixedMoment B raw36094step3 raw36094step3Labels := by
      have ha : raw36094step3 = raw36094step2 := by apply Matrix.ext; unfold raw36094step3 raw36094step2; decide +kernel
      have hl : raw36094step2Labels = labelEmbedding1 ∘ raw36094step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36094step2 raw36094step2Labels raw36094step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

theorem canonical36095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36095 raw36095Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw36095 raw36095Labels = mixedMoment B raw36095step0 raw36095step0Labels := by
      have ha : raw36095step0 = (fun i j => raw36095 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36095step0 raw36095; decide +kernel
      have hl : raw36095step0Labels = raw36095Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36095 raw36095Labels permutation267 permutation7
    mixedMoment B raw36095step0 raw36095step0Labels = mixedMoment B raw36095step1 raw36095step1Labels := by
      have ha : raw36095step1 = -raw36095step0 := by apply Matrix.ext; change ∀ i j, raw36095step1 i j = -(raw36095step0 i j); unfold raw36095step1 raw36095step0; decide +kernel
      have hl : raw36095step1Labels = raw36095step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36095step1 raw36095step1Labels = mixedMoment B raw36095step2 raw36095step2Labels := by
      have ha : raw36095step2 = raw36095step1 := by apply Matrix.ext; unfold raw36095step2 raw36095step1; decide +kernel
      have hl : raw36095step1Labels = labelEmbedding1 ∘ raw36095step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36095step1 raw36095step1Labels raw36095step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

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

theorem canonical36096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36096 raw36096Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw36096 raw36096Labels = mixedMoment B raw36096step0 raw36096step0Labels := by
      have hz : ∀ j, raw36096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36096step0 = (fun i j => raw36096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36096step0 raw36096; decide +kernel
      have hl : raw36096step0Labels = raw36096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36096 raw36096Labels permutation346 hz
    mixedMoment B raw36096step0 raw36096step0Labels = mixedMoment B raw36096step1 raw36096step1Labels := by
      have ha : raw36096step1 = (fun i j => raw36096step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36096step1 raw36096step0; decide +kernel
      have hl : raw36096step1Labels = raw36096step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36096step0 raw36096step0Labels permutation58 permutation7
    mixedMoment B raw36096step1 raw36096step1Labels = mixedMoment B raw36096step2 raw36096step2Labels := by
      have ha : raw36096step2 = -raw36096step1 := by apply Matrix.ext; change ∀ i j, raw36096step2 i j = -(raw36096step1 i j); unfold raw36096step2 raw36096step1; decide +kernel
      have hl : raw36096step2Labels = raw36096step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36096step2 raw36096step2Labels = mixedMoment B raw36096step3 raw36096step3Labels := by
      have ha : raw36096step3 = raw36096step2 := by apply Matrix.ext; unfold raw36096step3 raw36096step2; decide +kernel
      have hl : raw36096step2Labels = labelEmbedding1 ∘ raw36096step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36096step2 raw36096step2Labels raw36096step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical36097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36097 raw36097Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw36097 raw36097Labels = mixedMoment B raw36097step0 raw36097step0Labels := by
      have hz : ∀ j, raw36097 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36097step0 = (fun i j => raw36097 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36097step0 raw36097; decide +kernel
      have hl : raw36097step0Labels = raw36097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36097 raw36097Labels permutation520 hz
    mixedMoment B raw36097step0 raw36097step0Labels = mixedMoment B raw36097step1 raw36097step1Labels := by
      have hz : ∀ j, raw36097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36097step1 = (fun i j => raw36097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36097step1 raw36097step0; decide +kernel
      have hl : raw36097step1Labels = raw36097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36097step0 raw36097step0Labels permutation80 hz
    mixedMoment B raw36097step1 raw36097step1Labels = mixedMoment B raw36097step2 raw36097step2Labels := by
      have ha : raw36097step2 = (fun i j => raw36097step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36097step2 raw36097step1; decide +kernel
      have hl : raw36097step2Labels = raw36097step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36097step1 raw36097step1Labels permutation14 permutation7
    mixedMoment B raw36097step2 raw36097step2Labels = mixedMoment B raw36097step3 raw36097step3Labels := by
      have ha : raw36097step3 = -raw36097step2 := by apply Matrix.ext; change ∀ i j, raw36097step3 i j = -(raw36097step2 i j); unfold raw36097step3 raw36097step2; decide +kernel
      have hl : raw36097step3Labels = raw36097step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36097step3 raw36097step3Labels = mixedMoment B raw36097step4 raw36097step4Labels := by
      have ha : raw36097step4 = raw36097step3 := by apply Matrix.ext; unfold raw36097step4 raw36097step3; decide +kernel
      have hl : raw36097step3Labels = labelEmbedding1 ∘ raw36097step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36097step3 raw36097step3Labels raw36097step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

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

theorem sound2141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2141 node2141Labels = Sparse.eval nodeValue2141 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2141) = mixedMoment B node2141 node2141Labels := rfl
  simpa [nodeValue2141, Sparse.eval] using hc.symm

theorem sound2151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2151 node2151Labels = Sparse.eval nodeValue2151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2151) = mixedMoment B node2151 node2151Labels := rfl
  simpa [nodeValue2151, Sparse.eval] using hc.symm

theorem sound2152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2152 node2152Labels = Sparse.eval nodeValue2152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2152) = mixedMoment B node2152 node2152Labels := rfl
  simpa [nodeValue2152, Sparse.eval] using hc.symm

theorem sound2157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2157 node2157Labels = Sparse.eval nodeValue2157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2157) = mixedMoment B node2157 node2157Labels := rfl
  simpa [nodeValue2157, Sparse.eval] using hc.symm

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

theorem sound2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = Sparse.eval nodeValue2205 (mixedVector B) := by
  simpa only [nodeValue2205, Sparse.eval_nil] using zero2205 B _hB _hF

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

theorem sound2248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2248 node2248Labels = Sparse.eval nodeValue2248 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2248) = mixedMoment B node2248 node2248Labels := rfl
  simpa [nodeValue2248, Sparse.eval] using hc.symm

theorem sound2249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2249 node2249Labels = Sparse.eval nodeValue2249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2249) = mixedMoment B node2249 node2249Labels := rfl
  simpa [nodeValue2249, Sparse.eval] using hc.symm

theorem sound2254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2254 node2254Labels = Sparse.eval nodeValue2254 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2254) = mixedMoment B node2254 node2254Labels := rfl
  simpa [nodeValue2254, Sparse.eval] using hc.symm

theorem sound2256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2256 node2256Labels = Sparse.eval nodeValue2256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2256) = mixedMoment B node2256 node2256Labels := rfl
  simpa [nodeValue2256, Sparse.eval] using hc.symm

theorem sound2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2272 node2272Labels = Sparse.eval nodeValue2272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2272) = mixedMoment B node2272 node2272Labels := rfl
  simpa [nodeValue2272, Sparse.eval] using hc.symm

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

theorem sound2653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2653 node2653Labels = Sparse.eval nodeValue2653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2653) = mixedMoment B node2653 node2653Labels := rfl
  simpa [nodeValue2653, Sparse.eval] using hc.symm

theorem sound2654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2654 node2654Labels = Sparse.eval nodeValue2654 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2654) = mixedMoment B node2654 node2654Labels := rfl
  simpa [nodeValue2654, Sparse.eval] using hc.symm

theorem sound2661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2661 node2661Labels = Sparse.eval nodeValue2661 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2661) = mixedMoment B node2661 node2661Labels := rfl
  simpa [nodeValue2661, Sparse.eval] using hc.symm

theorem sound2662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2662 node2662Labels = Sparse.eval nodeValue2662 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2662) = mixedMoment B node2662 node2662Labels := rfl
  simpa [nodeValue2662, Sparse.eval] using hc.symm

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

theorem sound2673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2673 node2673Labels = Sparse.eval nodeValue2673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2673) = mixedMoment B node2673 node2673Labels := rfl
  simpa [nodeValue2673, Sparse.eval] using hc.symm

theorem sound2677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2677 node2677Labels = Sparse.eval nodeValue2677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2677) = mixedMoment B node2677 node2677Labels := rfl
  simpa [nodeValue2677, Sparse.eval] using hc.symm

theorem sound2678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2678 node2678Labels = Sparse.eval nodeValue2678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2678) = mixedMoment B node2678 node2678Labels := rfl
  simpa [nodeValue2678, Sparse.eval] using hc.symm

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

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

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

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

theorem sound2742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = Sparse.eval nodeValue2742 (mixedVector B) := by
  simpa only [nodeValue2742, Sparse.eval_nil] using zero2742 B _hB _hF

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

theorem sound3016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3016 node3016Labels = Sparse.eval nodeValue3016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3016) = mixedMoment B node3016 node3016Labels := rfl
  simpa [nodeValue3016, Sparse.eval] using hc.symm

theorem sound3038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3038 node3038Labels = Sparse.eval nodeValue3038 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3038) = mixedMoment B node3038 node3038Labels := rfl
  simpa [nodeValue3038, Sparse.eval] using hc.symm

theorem sound3039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3039 node3039Labels = Sparse.eval nodeValue3039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3039) = mixedMoment B node3039 node3039Labels := rfl
  simpa [nodeValue3039, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources81
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2596 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2596 + difference 0 1) (sourceB2596 + difference 1 0) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2596 + difference 0 1) (sourceB2596 + difference 1 0) sourceC2596) = raw36068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36068; decide +kernel
    rw [ha]
    exact (canonical36068 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2596 + difference 0 2) (sourceB2596 + difference 2 0) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA2596 + difference 0 2) (sourceB2596 + difference 2 0) sourceC2596) = raw36069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36069; decide +kernel
    rw [ha]
    exact (canonical36069 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2596 + difference 0 3) (sourceB2596 + difference 3 0) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2596 + difference 0 3) (sourceB2596 + difference 3 0) sourceC2596) = raw36070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36070; decide +kernel
    rw [ha]
    exact (canonical36070 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2596 + difference 0 4) (sourceB2596 + difference 4 0) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2596 + difference 0 4) (sourceB2596 + difference 4 0) sourceC2596) = raw36071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36071; decide +kernel
    rw [ha]
    exact (canonical36071 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2596 + difference 0 5) (sourceB2596 + difference 5 0) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA2596 + difference 0 5) (sourceB2596 + difference 5 0) sourceC2596) = raw36072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36072; decide +kernel
    rw [ha]
    exact (canonical36072 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2596 + difference 1 0) (sourceB2596 + difference 0 1) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA2596 + difference 1 0) (sourceB2596 + difference 0 1) sourceC2596) = raw36073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36073; decide +kernel
    rw [ha]
    exact (canonical36073 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2596 + difference 1 2) (sourceB2596 + difference 2 1) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA2596 + difference 1 2) (sourceB2596 + difference 2 1) sourceC2596) = raw36074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36074; decide +kernel
    rw [ha]
    exact (canonical36074 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2596 + difference 1 3) (sourceB2596 + difference 3 1) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA2596 + difference 1 3) (sourceB2596 + difference 3 1) sourceC2596) = raw36075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36075; decide +kernel
    rw [ha]
    exact (canonical36075 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2596 + difference 1 4) (sourceB2596 + difference 4 1) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA2596 + difference 1 4) (sourceB2596 + difference 4 1) sourceC2596) = raw36076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36076; decide +kernel
    rw [ha]
    exact (canonical36076 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2596 + difference 1 5) (sourceB2596 + difference 5 1) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA2596 + difference 1 5) (sourceB2596 + difference 5 1) sourceC2596) = raw36077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36077; decide +kernel
    rw [ha]
    exact (canonical36077 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2596 + difference 2 0) (sourceB2596 + difference 0 2) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2248) := by
    have ha : (tripleCharges (sourceA2596 + difference 2 0) (sourceB2596 + difference 0 2) sourceC2596) = raw36078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36078; decide +kernel
    rw [ha]
    exact (canonical36078 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2596 + difference 2 1) (sourceB2596 + difference 1 2) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2141) := by
    have ha : (tripleCharges (sourceA2596 + difference 2 1) (sourceB2596 + difference 1 2) sourceC2596) = raw36079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36079; decide +kernel
    rw [ha]
    exact (canonical36079 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2596 + difference 2 3) (sourceB2596 + difference 3 2) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA2596 + difference 2 3) (sourceB2596 + difference 3 2) sourceC2596) = raw36080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36080; decide +kernel
    rw [ha]
    exact (canonical36080 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2596 + difference 2 4) (sourceB2596 + difference 4 2) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2596 + difference 2 4) (sourceB2596 + difference 4 2) sourceC2596) = raw36081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36081; decide +kernel
    rw [ha]
    exact (canonical36081 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2596 + difference 2 5) (sourceB2596 + difference 5 2) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA2596 + difference 2 5) (sourceB2596 + difference 5 2) sourceC2596) = raw36082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36082; decide +kernel
    rw [ha]
    exact (canonical36082 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2596 + difference 3 0) (sourceB2596 + difference 0 3) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2596 + difference 3 0) (sourceB2596 + difference 0 3) sourceC2596) = raw36083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36083; decide +kernel
    rw [ha]
    exact (canonical36083 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2596 + difference 3 1) (sourceB2596 + difference 1 3) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2596 + difference 3 1) (sourceB2596 + difference 1 3) sourceC2596) = raw36084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36084; decide +kernel
    rw [ha]
    exact (canonical36084 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2596 + difference 3 2) (sourceB2596 + difference 2 3) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2596 + difference 3 2) (sourceB2596 + difference 2 3) sourceC2596) = raw36085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36085; decide +kernel
    rw [ha]
    exact (canonical36085 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2596 + difference 3 4) (sourceB2596 + difference 4 3) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA2596 + difference 3 4) (sourceB2596 + difference 4 3) sourceC2596) = raw36086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36086; decide +kernel
    rw [ha]
    exact (canonical36086 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2596 + difference 3 5) (sourceB2596 + difference 5 3) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA2596 + difference 3 5) (sourceB2596 + difference 5 3) sourceC2596) = raw36087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36087; decide +kernel
    rw [ha]
    exact (canonical36087 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2596 + difference 4 0) (sourceB2596 + difference 0 4) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2249) := by
    have ha : (tripleCharges (sourceA2596 + difference 4 0) (sourceB2596 + difference 0 4) sourceC2596) = raw36088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36088; decide +kernel
    rw [ha]
    exact (canonical36088 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2596 + difference 4 1) (sourceB2596 + difference 1 4) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2157) := by
    have ha : (tripleCharges (sourceA2596 + difference 4 1) (sourceB2596 + difference 1 4) sourceC2596) = raw36089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36089; decide +kernel
    rw [ha]
    exact (canonical36089 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2596 + difference 4 2) (sourceB2596 + difference 2 4) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2654) := by
    have ha : (tripleCharges (sourceA2596 + difference 4 2) (sourceB2596 + difference 2 4) sourceC2596) = raw36090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36090; decide +kernel
    rw [ha]
    exact (canonical36090 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2596 + difference 4 3) (sourceB2596 + difference 3 4) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA2596 + difference 4 3) (sourceB2596 + difference 3 4) sourceC2596) = raw36091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36091; decide +kernel
    rw [ha]
    exact (canonical36091 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2596 + difference 4 5) (sourceB2596 + difference 5 4) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA2596 + difference 4 5) (sourceB2596 + difference 5 4) sourceC2596) = raw36092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36092; decide +kernel
    rw [ha]
    exact (canonical36092 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2596 + difference 5 0) (sourceB2596 + difference 0 5) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA2596 + difference 5 0) (sourceB2596 + difference 0 5) sourceC2596) = raw36093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36093; decide +kernel
    rw [ha]
    exact (canonical36093 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2596 + difference 5 1) (sourceB2596 + difference 1 5) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2596 + difference 5 1) (sourceB2596 + difference 1 5) sourceC2596) = raw36094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36094; decide +kernel
    rw [ha]
    exact (canonical36094 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2596 + difference 5 2) (sourceB2596 + difference 2 5) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2652) := by
    have ha : (tripleCharges (sourceA2596 + difference 5 2) (sourceB2596 + difference 2 5) sourceC2596) = raw36095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36095; decide +kernel
    rw [ha]
    exact (canonical36095 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2596 + difference 5 3) (sourceB2596 + difference 3 5) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2596 + difference 5 3) (sourceB2596 + difference 3 5) sourceC2596) = raw36096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36096; decide +kernel
    rw [ha]
    exact (canonical36096 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2596 + difference 5 4) (sourceB2596 + difference 4 5) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA2596 + difference 5 4) (sourceB2596 + difference 4 5) sourceC2596) = raw36097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36097; decide +kernel
    rw [ha]
    exact (canonical36097 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2596 sourceB2596 sourceC2596
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2596, Integer.Sparse.eval]
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

theorem reindexCheck2074 : Integer.Sparse.reindex keyMap MixedData.row2074 = numericRow2074 := by decide +kernel

theorem numericCheck2074 (x : Master → ℝ) : Integer.Sparse.eval numericRow2074 x =
    (1 : ℝ) * reducedSource2074 x := by
  norm_num [numericRow2074, reducedSource2074, Integer.Sparse.eval, Sparse.eval, nodeValue2141, nodeValue2151, nodeValue2152, nodeValue2157, nodeValue2205, nodeValue2248, nodeValue2249, nodeValue2254, nodeValue2256, nodeValue2272, nodeValue2652, nodeValue2653, nodeValue2654, nodeValue2661, nodeValue2662, nodeValue2670, nodeValue2672, nodeValue2673, nodeValue2677, nodeValue2678, nodeValue2685, nodeValue2686, nodeValue2694, nodeValue2722, nodeValue2723, nodeValue2742, nodeValue3016, nodeValue3038, nodeValue3039, nodeValue3054]

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

theorem reducedZero2074 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2074 (mixedVector B) = 0 := by
  have h2141 : mixedVector B (Sum.inr 2141) = Sparse.eval nodeValue2141 (mixedVector B) := by
    change mixedMoment B node2141 node2141Labels = _
    exact sound2141 B hB hF
  have h2151 : mixedVector B (Sum.inr 2151) = Sparse.eval nodeValue2151 (mixedVector B) := by
    change mixedMoment B node2151 node2151Labels = _
    exact sound2151 B hB hF
  have h2152 : mixedVector B (Sum.inr 2152) = Sparse.eval nodeValue2152 (mixedVector B) := by
    change mixedMoment B node2152 node2152Labels = _
    exact sound2152 B hB hF
  have h2157 : mixedVector B (Sum.inr 2157) = Sparse.eval nodeValue2157 (mixedVector B) := by
    change mixedMoment B node2157 node2157Labels = _
    exact sound2157 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2248 : mixedVector B (Sum.inr 2248) = Sparse.eval nodeValue2248 (mixedVector B) := by
    change mixedMoment B node2248 node2248Labels = _
    exact sound2248 B hB hF
  have h2249 : mixedVector B (Sum.inr 2249) = Sparse.eval nodeValue2249 (mixedVector B) := by
    change mixedMoment B node2249 node2249Labels = _
    exact sound2249 B hB hF
  have h2254 : mixedVector B (Sum.inr 2254) = Sparse.eval nodeValue2254 (mixedVector B) := by
    change mixedMoment B node2254 node2254Labels = _
    exact sound2254 B hB hF
  have h2256 : mixedVector B (Sum.inr 2256) = Sparse.eval nodeValue2256 (mixedVector B) := by
    change mixedMoment B node2256 node2256Labels = _
    exact sound2256 B hB hF
  have h2272 : mixedVector B (Sum.inr 2272) = Sparse.eval nodeValue2272 (mixedVector B) := by
    change mixedMoment B node2272 node2272Labels = _
    exact sound2272 B hB hF
  have h2652 : mixedVector B (Sum.inr 2652) = Sparse.eval nodeValue2652 (mixedVector B) := by
    change mixedMoment B node2652 node2652Labels = _
    exact sound2652 B hB hF
  have h2653 : mixedVector B (Sum.inr 2653) = Sparse.eval nodeValue2653 (mixedVector B) := by
    change mixedMoment B node2653 node2653Labels = _
    exact sound2653 B hB hF
  have h2654 : mixedVector B (Sum.inr 2654) = Sparse.eval nodeValue2654 (mixedVector B) := by
    change mixedMoment B node2654 node2654Labels = _
    exact sound2654 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h2662 : mixedVector B (Sum.inr 2662) = Sparse.eval nodeValue2662 (mixedVector B) := by
    change mixedMoment B node2662 node2662Labels = _
    exact sound2662 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2673 : mixedVector B (Sum.inr 2673) = Sparse.eval nodeValue2673 (mixedVector B) := by
    change mixedMoment B node2673 node2673Labels = _
    exact sound2673 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h2678 : mixedVector B (Sum.inr 2678) = Sparse.eval nodeValue2678 (mixedVector B) := by
    change mixedMoment B node2678 node2678Labels = _
    exact sound2678 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  simpa only [sourceForm2596, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2141, h2151, h2152, h2157, h2205, h2248, h2249, h2254, h2256, h2272, h2652, h2653, h2654, h2661, h2662, h2670, h2672, h2673, h2677, h2678, h2685, h2686, h2694, h2722, h2723, h2742, h3016, h3038, h3039, h3054, reducedSource2074] using sourceEq2596 B hB

theorem rowSound2074_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2074 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2074, numericCheck2074, reducedZero2074 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2074_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2074_e_oai
