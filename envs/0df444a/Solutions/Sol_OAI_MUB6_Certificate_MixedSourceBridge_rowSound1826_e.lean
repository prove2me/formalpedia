-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:50:57.550047+00:00
-- url     : https://prove2.me/submissions/2e6f2060-905e-40a8-8cf5-6018c5631464

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical236
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30269 raw30269Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw30269 raw30269Labels = mixedMoment B raw30269step0 raw30269step0Labels := by
      have hz : ∀ j, raw30269 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30269step0 = (fun i j => raw30269 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30269step0 raw30269; decide +kernel
      have hl : raw30269step0Labels = raw30269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30269 raw30269Labels permutation434 hz
    mixedMoment B raw30269step0 raw30269step0Labels = mixedMoment B raw30269step1 raw30269step1Labels := by
      have ha : raw30269step1 = (fun i j => raw30269step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30269step1 raw30269step0; decide +kernel
      have hl : raw30269step1Labels = raw30269step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30269step0 raw30269step0Labels permutation36 permutation7
    mixedMoment B raw30269step1 raw30269step1Labels = mixedMoment B raw30269step2 raw30269step2Labels := by
      have ha : raw30269step2 = -raw30269step1 := by apply Matrix.ext; change ∀ i j, raw30269step2 i j = -(raw30269step1 i j); unfold raw30269step2 raw30269step1; decide +kernel
      have hl : raw30269step2Labels = raw30269step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30269step2 raw30269step2Labels = mixedMoment B raw30269step3 raw30269step3Labels := by
      have ha : raw30269step3 = raw30269step2 := by apply Matrix.ext; unfold raw30269step3 raw30269step2; decide +kernel
      have hl : raw30269step2Labels = labelEmbedding1 ∘ raw30269step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30269step2 raw30269step2Labels raw30269step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

theorem canonical30270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30270 raw30270Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw30270 raw30270Labels = mixedMoment B raw30270step0 raw30270step0Labels := by
      have hz : ∀ j, raw30270 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30270step0 = (fun i j => raw30270 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30270step0 raw30270; decide +kernel
      have hl : raw30270step0Labels = raw30270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30270 raw30270Labels permutation434 hz
    mixedMoment B raw30270step0 raw30270step0Labels = mixedMoment B raw30270step1 raw30270step1Labels := by
      have ha : raw30270step1 = (fun i j => raw30270step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30270step1 raw30270step0; decide +kernel
      have hl : raw30270step1Labels = raw30270step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30270step0 raw30270step0Labels permutation36 permutation7
    mixedMoment B raw30270step1 raw30270step1Labels = mixedMoment B raw30270step2 raw30270step2Labels := by
      have ha : raw30270step2 = -raw30270step1 := by apply Matrix.ext; change ∀ i j, raw30270step2 i j = -(raw30270step1 i j); unfold raw30270step2 raw30270step1; decide +kernel
      have hl : raw30270step2Labels = raw30270step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30270step2 raw30270step2Labels = mixedMoment B raw30270step3 raw30270step3Labels := by
      have ha : raw30270step3 = raw30270step2 := by apply Matrix.ext; unfold raw30270step3 raw30270step2; decide +kernel
      have hl : raw30270step2Labels = labelEmbedding1 ∘ raw30270step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30270step2 raw30270step2Labels raw30270step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

theorem canonical30271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30271 raw30271Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw30271 raw30271Labels = mixedMoment B raw30271step0 raw30271step0Labels := by
      have ha : raw30271step0 = (fun i j => raw30271 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30271step0 raw30271; decide +kernel
      have hl : raw30271step0Labels = raw30271Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30271 raw30271Labels permutation162 permutation7
    mixedMoment B raw30271step0 raw30271step0Labels = mixedMoment B raw30271step1 raw30271step1Labels := by
      have ha : raw30271step1 = -raw30271step0 := by apply Matrix.ext; change ∀ i j, raw30271step1 i j = -(raw30271step0 i j); unfold raw30271step1 raw30271step0; decide +kernel
      have hl : raw30271step1Labels = raw30271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30271step1 raw30271step1Labels = mixedMoment B raw30271step2 raw30271step2Labels := by
      have ha : raw30271step2 = raw30271step1 := by apply Matrix.ext; unfold raw30271step2 raw30271step1; decide +kernel
      have hl : raw30271step1Labels = labelEmbedding1 ∘ raw30271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30271step1 raw30271step1Labels raw30271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical30272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30272 raw30272Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw30272 raw30272Labels = mixedMoment B raw30272step0 raw30272step0Labels := by
      have hz : ∀ j, raw30272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30272step0 = (fun i j => raw30272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30272step0 raw30272; decide +kernel
      have hl : raw30272step0Labels = raw30272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30272 raw30272Labels permutation434 hz
    mixedMoment B raw30272step0 raw30272step0Labels = mixedMoment B raw30272step1 raw30272step1Labels := by
      have ha : raw30272step1 = (fun i j => raw30272step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30272step1 raw30272step0; decide +kernel
      have hl : raw30272step1Labels = raw30272step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30272step0 raw30272step0Labels permutation36 permutation7
    mixedMoment B raw30272step1 raw30272step1Labels = mixedMoment B raw30272step2 raw30272step2Labels := by
      have ha : raw30272step2 = -raw30272step1 := by apply Matrix.ext; change ∀ i j, raw30272step2 i j = -(raw30272step1 i j); unfold raw30272step2 raw30272step1; decide +kernel
      have hl : raw30272step2Labels = raw30272step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30272step2 raw30272step2Labels = mixedMoment B raw30272step3 raw30272step3Labels := by
      have ha : raw30272step3 = raw30272step2 := by apply Matrix.ext; unfold raw30272step3 raw30272step2; decide +kernel
      have hl : raw30272step2Labels = labelEmbedding1 ∘ raw30272step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30272step2 raw30272step2Labels raw30272step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical30273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30273 raw30273Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw30273 raw30273Labels = mixedMoment B raw30273step0 raw30273step0Labels := by
      have hz : ∀ j, raw30273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30273step0 = (fun i j => raw30273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30273step0 raw30273; decide +kernel
      have hl : raw30273step0Labels = raw30273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30273 raw30273Labels permutation434 hz
    mixedMoment B raw30273step0 raw30273step0Labels = mixedMoment B raw30273step1 raw30273step1Labels := by
      have ha : raw30273step1 = (fun i j => raw30273step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30273step1 raw30273step0; decide +kernel
      have hl : raw30273step1Labels = raw30273step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30273step0 raw30273step0Labels permutation36 permutation7
    mixedMoment B raw30273step1 raw30273step1Labels = mixedMoment B raw30273step2 raw30273step2Labels := by
      have ha : raw30273step2 = -raw30273step1 := by apply Matrix.ext; change ∀ i j, raw30273step2 i j = -(raw30273step1 i j); unfold raw30273step2 raw30273step1; decide +kernel
      have hl : raw30273step2Labels = raw30273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30273step2 raw30273step2Labels = mixedMoment B raw30273step3 raw30273step3Labels := by
      have ha : raw30273step3 = raw30273step2 := by apply Matrix.ext; unfold raw30273step3 raw30273step2; decide +kernel
      have hl : raw30273step2Labels = labelEmbedding1 ∘ raw30273step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30273step2 raw30273step2Labels raw30273step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical30274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30274 raw30274Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw30274 raw30274Labels = mixedMoment B raw30274step0 raw30274step0Labels := by
      have hz : ∀ j, raw30274 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30274step0 = (fun i j => raw30274 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30274step0 raw30274; decide +kernel
      have hl : raw30274step0Labels = raw30274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30274 raw30274Labels permutation434 hz
    mixedMoment B raw30274step0 raw30274step0Labels = mixedMoment B raw30274step1 raw30274step1Labels := by
      have ha : raw30274step1 = (fun i j => raw30274step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30274step1 raw30274step0; decide +kernel
      have hl : raw30274step1Labels = raw30274step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30274step0 raw30274step0Labels permutation40 permutation5
    mixedMoment B raw30274step1 raw30274step1Labels = mixedMoment B raw30274step2 raw30274step2Labels := by
      have ha : raw30274step2 = -raw30274step1 := by apply Matrix.ext; change ∀ i j, raw30274step2 i j = -(raw30274step1 i j); unfold raw30274step2 raw30274step1; decide +kernel
      have hl : raw30274step2Labels = raw30274step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30274step2 raw30274step2Labels = mixedMoment B raw30274step3 raw30274step3Labels := by
      have ha : raw30274step3 = raw30274step2 := by apply Matrix.ext; unfold raw30274step3 raw30274step2; decide +kernel
      have hl : raw30274step2Labels = labelEmbedding1 ∘ raw30274step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30274step2 raw30274step2Labels raw30274step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3295 node3295Labels := by rfl

theorem canonical30275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30275 raw30275Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw30275 raw30275Labels = mixedMoment B raw30275step0 raw30275step0Labels := by
      have hz : ∀ j, raw30275 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30275step0 = (fun i j => raw30275 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30275step0 raw30275; decide +kernel
      have hl : raw30275step0Labels = raw30275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30275 raw30275Labels permutation434 hz
    mixedMoment B raw30275step0 raw30275step0Labels = mixedMoment B raw30275step1 raw30275step1Labels := by
      have ha : raw30275step1 = (fun i j => raw30275step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30275step1 raw30275step0; decide +kernel
      have hl : raw30275step1Labels = raw30275step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30275step0 raw30275step0Labels permutation36 permutation7
    mixedMoment B raw30275step1 raw30275step1Labels = mixedMoment B raw30275step2 raw30275step2Labels := by
      have ha : raw30275step2 = -raw30275step1 := by apply Matrix.ext; change ∀ i j, raw30275step2 i j = -(raw30275step1 i j); unfold raw30275step2 raw30275step1; decide +kernel
      have hl : raw30275step2Labels = raw30275step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30275step2 raw30275step2Labels = mixedMoment B raw30275step3 raw30275step3Labels := by
      have ha : raw30275step3 = raw30275step2 := by apply Matrix.ext; unfold raw30275step3 raw30275step2; decide +kernel
      have hl : raw30275step2Labels = labelEmbedding1 ∘ raw30275step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30275step2 raw30275step2Labels raw30275step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

theorem canonical30276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30276 raw30276Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw30276 raw30276Labels = mixedMoment B raw30276step0 raw30276step0Labels := by
      have ha : raw30276step0 = (fun i j => raw30276 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30276step0 raw30276; decide +kernel
      have hl : raw30276step0Labels = raw30276Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30276 raw30276Labels permutation162 permutation7
    mixedMoment B raw30276step0 raw30276step0Labels = mixedMoment B raw30276step1 raw30276step1Labels := by
      have ha : raw30276step1 = -raw30276step0 := by apply Matrix.ext; change ∀ i j, raw30276step1 i j = -(raw30276step0 i j); unfold raw30276step1 raw30276step0; decide +kernel
      have hl : raw30276step1Labels = raw30276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30276step1 raw30276step1Labels = mixedMoment B raw30276step2 raw30276step2Labels := by
      have ha : raw30276step2 = raw30276step1 := by apply Matrix.ext; unfold raw30276step2 raw30276step1; decide +kernel
      have hl : raw30276step1Labels = labelEmbedding1 ∘ raw30276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30276step1 raw30276step1Labels raw30276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical30277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30277 raw30277Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw30277 raw30277Labels = mixedMoment B raw30277step0 raw30277step0Labels := by
      have hz : ∀ j, raw30277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30277step0 = (fun i j => raw30277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30277step0 raw30277; decide +kernel
      have hl : raw30277step0Labels = raw30277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30277 raw30277Labels permutation434 hz
    mixedMoment B raw30277step0 raw30277step0Labels = mixedMoment B raw30277step1 raw30277step1Labels := by
      have ha : raw30277step1 = (fun i j => raw30277step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30277step1 raw30277step0; decide +kernel
      have hl : raw30277step1Labels = raw30277step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30277step0 raw30277step0Labels permutation36 permutation7
    mixedMoment B raw30277step1 raw30277step1Labels = mixedMoment B raw30277step2 raw30277step2Labels := by
      have ha : raw30277step2 = -raw30277step1 := by apply Matrix.ext; change ∀ i j, raw30277step2 i j = -(raw30277step1 i j); unfold raw30277step2 raw30277step1; decide +kernel
      have hl : raw30277step2Labels = raw30277step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30277step2 raw30277step2Labels = mixedMoment B raw30277step3 raw30277step3Labels := by
      have ha : raw30277step3 = raw30277step2 := by apply Matrix.ext; unfold raw30277step3 raw30277step2; decide +kernel
      have hl : raw30277step2Labels = labelEmbedding1 ∘ raw30277step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30277step2 raw30277step2Labels raw30277step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical30278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30278 raw30278Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw30278 raw30278Labels = mixedMoment B raw30278step0 raw30278step0Labels := by
      have hz : ∀ j, raw30278 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30278step0 = (fun i j => raw30278 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30278step0 raw30278; decide +kernel
      have hl : raw30278step0Labels = raw30278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30278 raw30278Labels permutation434 hz
    mixedMoment B raw30278step0 raw30278step0Labels = mixedMoment B raw30278step1 raw30278step1Labels := by
      have ha : raw30278step1 = (fun i j => raw30278step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30278step1 raw30278step0; decide +kernel
      have hl : raw30278step1Labels = raw30278step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30278step0 raw30278step0Labels permutation36 permutation7
    mixedMoment B raw30278step1 raw30278step1Labels = mixedMoment B raw30278step2 raw30278step2Labels := by
      have ha : raw30278step2 = -raw30278step1 := by apply Matrix.ext; change ∀ i j, raw30278step2 i j = -(raw30278step1 i j); unfold raw30278step2 raw30278step1; decide +kernel
      have hl : raw30278step2Labels = raw30278step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30278step2 raw30278step2Labels = mixedMoment B raw30278step3 raw30278step3Labels := by
      have ha : raw30278step3 = raw30278step2 := by apply Matrix.ext; unfold raw30278step3 raw30278step2; decide +kernel
      have hl : raw30278step2Labels = labelEmbedding1 ∘ raw30278step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30278step2 raw30278step2Labels raw30278step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical30279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30279 raw30279Labels = mixedMoment B node3270 node3270Labels := by
  calc
    mixedMoment B raw30279 raw30279Labels = mixedMoment B raw30279step0 raw30279step0Labels := by
      have hz : ∀ j, raw30279 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30279step0 = (fun i j => raw30279 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30279step0 raw30279; decide +kernel
      have hl : raw30279step0Labels = raw30279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30279 raw30279Labels permutation434 hz
    mixedMoment B raw30279step0 raw30279step0Labels = mixedMoment B raw30279step1 raw30279step1Labels := by
      have ha : raw30279step1 = (fun i j => raw30279step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30279step1 raw30279step0; decide +kernel
      have hl : raw30279step1Labels = raw30279step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30279step0 raw30279step0Labels permutation36 permutation7
    mixedMoment B raw30279step1 raw30279step1Labels = mixedMoment B raw30279step2 raw30279step2Labels := by
      have ha : raw30279step2 = -raw30279step1 := by apply Matrix.ext; change ∀ i j, raw30279step2 i j = -(raw30279step1 i j); unfold raw30279step2 raw30279step1; decide +kernel
      have hl : raw30279step2Labels = raw30279step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30279step2 raw30279step2Labels = mixedMoment B raw30279step3 raw30279step3Labels := by
      have ha : raw30279step3 = raw30279step2 := by apply Matrix.ext; unfold raw30279step3 raw30279step2; decide +kernel
      have hl : raw30279step2Labels = labelEmbedding1 ∘ raw30279step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30279step2 raw30279step2Labels raw30279step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3270 node3270Labels := by rfl

theorem canonical30280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30280 raw30280Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw30280 raw30280Labels = mixedMoment B raw30280step0 raw30280step0Labels := by
      have hz : ∀ j, raw30280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30280step0 = (fun i j => raw30280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30280step0 raw30280; decide +kernel
      have hl : raw30280step0Labels = raw30280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30280 raw30280Labels permutation434 hz
    mixedMoment B raw30280step0 raw30280step0Labels = mixedMoment B raw30280step1 raw30280step1Labels := by
      have ha : raw30280step1 = (fun i j => raw30280step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30280step1 raw30280step0; decide +kernel
      have hl : raw30280step1Labels = raw30280step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30280step0 raw30280step0Labels permutation36 permutation7
    mixedMoment B raw30280step1 raw30280step1Labels = mixedMoment B raw30280step2 raw30280step2Labels := by
      have ha : raw30280step2 = -raw30280step1 := by apply Matrix.ext; change ∀ i j, raw30280step2 i j = -(raw30280step1 i j); unfold raw30280step2 raw30280step1; decide +kernel
      have hl : raw30280step2Labels = raw30280step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30280step2 raw30280step2Labels = mixedMoment B raw30280step3 raw30280step3Labels := by
      have ha : raw30280step3 = raw30280step2 := by apply Matrix.ext; unfold raw30280step3 raw30280step2; decide +kernel
      have hl : raw30280step2Labels = labelEmbedding1 ∘ raw30280step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30280step2 raw30280step2Labels raw30280step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3417 node3417Labels := by rfl

theorem canonical30281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30281 raw30281Labels = mixedMoment B node3453 node3453Labels := by
  calc
    mixedMoment B raw30281 raw30281Labels = mixedMoment B raw30281step0 raw30281step0Labels := by
      have ha : raw30281step0 = (fun i j => raw30281 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30281step0 raw30281; decide +kernel
      have hl : raw30281step0Labels = raw30281Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30281 raw30281Labels permutation162 permutation7
    mixedMoment B raw30281step0 raw30281step0Labels = mixedMoment B raw30281step1 raw30281step1Labels := by
      have ha : raw30281step1 = -raw30281step0 := by apply Matrix.ext; change ∀ i j, raw30281step1 i j = -(raw30281step0 i j); unfold raw30281step1 raw30281step0; decide +kernel
      have hl : raw30281step1Labels = raw30281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30281step1 raw30281step1Labels = mixedMoment B raw30281step2 raw30281step2Labels := by
      have ha : raw30281step2 = raw30281step1 := by apply Matrix.ext; unfold raw30281step2 raw30281step1; decide +kernel
      have hl : raw30281step1Labels = labelEmbedding1 ∘ raw30281step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30281step1 raw30281step1Labels raw30281step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3453 node3453Labels := by rfl

theorem canonical30282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30282 raw30282Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw30282 raw30282Labels = mixedMoment B raw30282step0 raw30282step0Labels := by
      have hz : ∀ j, raw30282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30282step0 = (fun i j => raw30282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30282step0 raw30282; decide +kernel
      have hl : raw30282step0Labels = raw30282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30282 raw30282Labels permutation434 hz
    mixedMoment B raw30282step0 raw30282step0Labels = mixedMoment B raw30282step1 raw30282step1Labels := by
      have ha : raw30282step1 = (fun i j => raw30282step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30282step1 raw30282step0; decide +kernel
      have hl : raw30282step1Labels = raw30282step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30282step0 raw30282step0Labels permutation36 permutation7
    mixedMoment B raw30282step1 raw30282step1Labels = mixedMoment B raw30282step2 raw30282step2Labels := by
      have ha : raw30282step2 = -raw30282step1 := by apply Matrix.ext; change ∀ i j, raw30282step2 i j = -(raw30282step1 i j); unfold raw30282step2 raw30282step1; decide +kernel
      have hl : raw30282step2Labels = raw30282step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30282step2 raw30282step2Labels = mixedMoment B raw30282step3 raw30282step3Labels := by
      have ha : raw30282step3 = raw30282step2 := by apply Matrix.ext; unfold raw30282step3 raw30282step2; decide +kernel
      have hl : raw30282step2Labels = labelEmbedding1 ∘ raw30282step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30282step2 raw30282step2Labels raw30282step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

theorem canonical30283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30283 raw30283Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw30283 raw30283Labels = mixedMoment B raw30283step0 raw30283step0Labels := by
      have hz : ∀ j, raw30283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30283step0 = (fun i j => raw30283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30283step0 raw30283; decide +kernel
      have hl : raw30283step0Labels = raw30283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30283 raw30283Labels permutation434 hz
    mixedMoment B raw30283step0 raw30283step0Labels = mixedMoment B raw30283step1 raw30283step1Labels := by
      have ha : raw30283step1 = (fun i j => raw30283step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30283step1 raw30283step0; decide +kernel
      have hl : raw30283step1Labels = raw30283step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30283step0 raw30283step0Labels permutation36 permutation7
    mixedMoment B raw30283step1 raw30283step1Labels = mixedMoment B raw30283step2 raw30283step2Labels := by
      have ha : raw30283step2 = -raw30283step1 := by apply Matrix.ext; change ∀ i j, raw30283step2 i j = -(raw30283step1 i j); unfold raw30283step2 raw30283step1; decide +kernel
      have hl : raw30283step2Labels = raw30283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30283step2 raw30283step2Labels = mixedMoment B raw30283step3 raw30283step3Labels := by
      have ha : raw30283step3 = raw30283step2 := by apply Matrix.ext; unfold raw30283step3 raw30283step2; decide +kernel
      have hl : raw30283step2Labels = labelEmbedding1 ∘ raw30283step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30283step2 raw30283step2Labels raw30283step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

theorem canonical30284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30284 raw30284Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw30284 raw30284Labels = mixedMoment B raw30284step0 raw30284step0Labels := by
      have ha : raw30284step0 = (fun i j => raw30284 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30284step0 raw30284; decide +kernel
      have hl : raw30284step0Labels = raw30284Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30284 raw30284Labels permutation162 permutation7
    mixedMoment B raw30284step0 raw30284step0Labels = mixedMoment B raw30284step1 raw30284step1Labels := by
      have ha : raw30284step1 = -raw30284step0 := by apply Matrix.ext; change ∀ i j, raw30284step1 i j = -(raw30284step0 i j); unfold raw30284step1 raw30284step0; decide +kernel
      have hl : raw30284step1Labels = raw30284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30284step1 raw30284step1Labels = mixedMoment B raw30284step2 raw30284step2Labels := by
      have ha : raw30284step2 = raw30284step1 := by apply Matrix.ext; unfold raw30284step2 raw30284step1; decide +kernel
      have hl : raw30284step1Labels = labelEmbedding1 ∘ raw30284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30284step1 raw30284step1Labels raw30284step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3258 node3258Labels := by rfl

theorem canonical30285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30285 raw30285Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw30285 raw30285Labels = mixedMoment B raw30285step0 raw30285step0Labels := by
      have ha : raw30285step0 = (fun i j => raw30285 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30285step0 raw30285; decide +kernel
      have hl : raw30285step0Labels = raw30285Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30285 raw30285Labels permutation162 permutation7
    mixedMoment B raw30285step0 raw30285step0Labels = mixedMoment B raw30285step1 raw30285step1Labels := by
      have ha : raw30285step1 = -raw30285step0 := by apply Matrix.ext; change ∀ i j, raw30285step1 i j = -(raw30285step0 i j); unfold raw30285step1 raw30285step0; decide +kernel
      have hl : raw30285step1Labels = raw30285step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30285step1 raw30285step1Labels = mixedMoment B raw30285step2 raw30285step2Labels := by
      have ha : raw30285step2 = raw30285step1 := by apply Matrix.ext; unfold raw30285step2 raw30285step1; decide +kernel
      have hl : raw30285step1Labels = labelEmbedding1 ∘ raw30285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30285step1 raw30285step1Labels raw30285step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

theorem canonical30286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30286 raw30286Labels = mixedMoment B node3462 node3462Labels := by
  calc
    mixedMoment B raw30286 raw30286Labels = mixedMoment B raw30286step0 raw30286step0Labels := by
      have ha : raw30286step0 = (fun i j => raw30286 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30286step0 raw30286; decide +kernel
      have hl : raw30286step0Labels = raw30286Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30286 raw30286Labels permutation162 permutation7
    mixedMoment B raw30286step0 raw30286step0Labels = mixedMoment B raw30286step1 raw30286step1Labels := by
      have ha : raw30286step1 = -raw30286step0 := by apply Matrix.ext; change ∀ i j, raw30286step1 i j = -(raw30286step0 i j); unfold raw30286step1 raw30286step0; decide +kernel
      have hl : raw30286step1Labels = raw30286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30286step1 raw30286step1Labels = mixedMoment B raw30286step2 raw30286step2Labels := by
      have ha : raw30286step2 = raw30286step1 := by apply Matrix.ext; unfold raw30286step2 raw30286step1; decide +kernel
      have hl : raw30286step1Labels = labelEmbedding1 ∘ raw30286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30286step1 raw30286step1Labels raw30286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3462 node3462Labels := by rfl

theorem canonical30287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30287 raw30287Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw30287 raw30287Labels = mixedMoment B raw30287step0 raw30287step0Labels := by
      have ha : raw30287step0 = (fun i j => raw30287 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30287step0 raw30287; decide +kernel
      have hl : raw30287step0Labels = raw30287Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30287 raw30287Labels permutation162 permutation7
    mixedMoment B raw30287step0 raw30287step0Labels = mixedMoment B raw30287step1 raw30287step1Labels := by
      have ha : raw30287step1 = -raw30287step0 := by apply Matrix.ext; change ∀ i j, raw30287step1 i j = -(raw30287step0 i j); unfold raw30287step1 raw30287step0; decide +kernel
      have hl : raw30287step1Labels = raw30287step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30287step1 raw30287step1Labels = mixedMoment B raw30287step2 raw30287step2Labels := by
      have ha : raw30287step2 = raw30287step1 := by apply Matrix.ext; unfold raw30287step2 raw30287step1; decide +kernel
      have hl : raw30287step1Labels = labelEmbedding1 ∘ raw30287step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30287step1 raw30287step1Labels raw30287step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

theorem canonical30288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30288 raw30288Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw30288 raw30288Labels = mixedMoment B raw30288step0 raw30288step0Labels := by
      have ha : raw30288step0 = (fun i j => raw30288 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30288step0 raw30288; decide +kernel
      have hl : raw30288step0Labels = raw30288Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30288 raw30288Labels permutation162 permutation7
    mixedMoment B raw30288step0 raw30288step0Labels = mixedMoment B raw30288step1 raw30288step1Labels := by
      have ha : raw30288step1 = -raw30288step0 := by apply Matrix.ext; change ∀ i j, raw30288step1 i j = -(raw30288step0 i j); unfold raw30288step1 raw30288step0; decide +kernel
      have hl : raw30288step1Labels = raw30288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30288step1 raw30288step1Labels = mixedMoment B raw30288step2 raw30288step2Labels := by
      have ha : raw30288step2 = raw30288step1 := by apply Matrix.ext; unfold raw30288step2 raw30288step1; decide +kernel
      have hl : raw30288step1Labels = labelEmbedding1 ∘ raw30288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30288step1 raw30288step1Labels raw30288step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

theorem canonical30289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30289 raw30289Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw30289 raw30289Labels = mixedMoment B raw30289step0 raw30289step0Labels := by
      have hz : ∀ j, raw30289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30289step0 = (fun i j => raw30289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30289step0 raw30289; decide +kernel
      have hl : raw30289step0Labels = raw30289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30289 raw30289Labels permutation434 hz
    mixedMoment B raw30289step0 raw30289step0Labels = mixedMoment B raw30289step1 raw30289step1Labels := by
      have ha : raw30289step1 = (fun i j => raw30289step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30289step1 raw30289step0; decide +kernel
      have hl : raw30289step1Labels = raw30289step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30289step0 raw30289step0Labels permutation36 permutation7
    mixedMoment B raw30289step1 raw30289step1Labels = mixedMoment B raw30289step2 raw30289step2Labels := by
      have ha : raw30289step2 = -raw30289step1 := by apply Matrix.ext; change ∀ i j, raw30289step2 i j = -(raw30289step1 i j); unfold raw30289step2 raw30289step1; decide +kernel
      have hl : raw30289step2Labels = raw30289step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30289step2 raw30289step2Labels = mixedMoment B raw30289step3 raw30289step3Labels := by
      have ha : raw30289step3 = raw30289step2 := by apply Matrix.ext; unfold raw30289step3 raw30289step2; decide +kernel
      have hl : raw30289step2Labels = labelEmbedding1 ∘ raw30289step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30289step2 raw30289step2Labels raw30289step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

theorem canonical30290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30290 raw30290Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw30290 raw30290Labels = mixedMoment B raw30290step0 raw30290step0Labels := by
      have hz : ∀ j, raw30290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30290step0 = (fun i j => raw30290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30290step0 raw30290; decide +kernel
      have hl : raw30290step0Labels = raw30290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30290 raw30290Labels permutation434 hz
    mixedMoment B raw30290step0 raw30290step0Labels = mixedMoment B raw30290step1 raw30290step1Labels := by
      have ha : raw30290step1 = (fun i j => raw30290step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30290step1 raw30290step0; decide +kernel
      have hl : raw30290step1Labels = raw30290step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30290step0 raw30290step0Labels permutation36 permutation7
    mixedMoment B raw30290step1 raw30290step1Labels = mixedMoment B raw30290step2 raw30290step2Labels := by
      have ha : raw30290step2 = -raw30290step1 := by apply Matrix.ext; change ∀ i j, raw30290step2 i j = -(raw30290step1 i j); unfold raw30290step2 raw30290step1; decide +kernel
      have hl : raw30290step2Labels = raw30290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30290step2 raw30290step2Labels = mixedMoment B raw30290step3 raw30290step3Labels := by
      have ha : raw30290step3 = raw30290step2 := by apply Matrix.ext; unfold raw30290step3 raw30290step2; decide +kernel
      have hl : raw30290step2Labels = labelEmbedding1 ∘ raw30290step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30290step2 raw30290step2Labels raw30290step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

theorem canonical30291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30291 raw30291Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw30291 raw30291Labels = mixedMoment B raw30291step0 raw30291step0Labels := by
      have hz : ∀ j, raw30291 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30291step0 = (fun i j => raw30291 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30291step0 raw30291; decide +kernel
      have hl : raw30291step0Labels = raw30291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30291 raw30291Labels permutation434 hz
    mixedMoment B raw30291step0 raw30291step0Labels = mixedMoment B raw30291step1 raw30291step1Labels := by
      have ha : raw30291step1 = (fun i j => raw30291step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30291step1 raw30291step0; decide +kernel
      have hl : raw30291step1Labels = raw30291step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30291step0 raw30291step0Labels permutation36 permutation7
    mixedMoment B raw30291step1 raw30291step1Labels = mixedMoment B raw30291step2 raw30291step2Labels := by
      have ha : raw30291step2 = -raw30291step1 := by apply Matrix.ext; change ∀ i j, raw30291step2 i j = -(raw30291step1 i j); unfold raw30291step2 raw30291step1; decide +kernel
      have hl : raw30291step2Labels = raw30291step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30291step2 raw30291step2Labels = mixedMoment B raw30291step3 raw30291step3Labels := by
      have ha : raw30291step3 = raw30291step2 := by apply Matrix.ext; unfold raw30291step3 raw30291step2; decide +kernel
      have hl : raw30291step2Labels = labelEmbedding1 ∘ raw30291step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30291step2 raw30291step2Labels raw30291step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

theorem canonical30292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30292 raw30292Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw30292 raw30292Labels = mixedMoment B raw30292step0 raw30292step0Labels := by
      have ha : raw30292step0 = (fun i j => raw30292 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30292step0 raw30292; decide +kernel
      have hl : raw30292step0Labels = raw30292Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30292 raw30292Labels permutation162 permutation7
    mixedMoment B raw30292step0 raw30292step0Labels = mixedMoment B raw30292step1 raw30292step1Labels := by
      have ha : raw30292step1 = -raw30292step0 := by apply Matrix.ext; change ∀ i j, raw30292step1 i j = -(raw30292step0 i j); unfold raw30292step1 raw30292step0; decide +kernel
      have hl : raw30292step1Labels = raw30292step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30292step1 raw30292step1Labels = mixedMoment B raw30292step2 raw30292step2Labels := by
      have ha : raw30292step2 = raw30292step1 := by apply Matrix.ext; unfold raw30292step2 raw30292step1; decide +kernel
      have hl : raw30292step1Labels = labelEmbedding1 ∘ raw30292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30292step1 raw30292step1Labels raw30292step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

theorem canonical30293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30293 raw30293Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw30293 raw30293Labels = mixedMoment B raw30293step0 raw30293step0Labels := by
      have hz : ∀ j, raw30293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30293step0 = (fun i j => raw30293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30293step0 raw30293; decide +kernel
      have hl : raw30293step0Labels = raw30293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30293 raw30293Labels permutation434 hz
    mixedMoment B raw30293step0 raw30293step0Labels = mixedMoment B raw30293step1 raw30293step1Labels := by
      have ha : raw30293step1 = (fun i j => raw30293step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30293step1 raw30293step0; decide +kernel
      have hl : raw30293step1Labels = raw30293step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30293step0 raw30293step0Labels permutation36 permutation7
    mixedMoment B raw30293step1 raw30293step1Labels = mixedMoment B raw30293step2 raw30293step2Labels := by
      have ha : raw30293step2 = -raw30293step1 := by apply Matrix.ext; change ∀ i j, raw30293step2 i j = -(raw30293step1 i j); unfold raw30293step2 raw30293step1; decide +kernel
      have hl : raw30293step2Labels = raw30293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30293step2 raw30293step2Labels = mixedMoment B raw30293step3 raw30293step3Labels := by
      have ha : raw30293step3 = raw30293step2 := by apply Matrix.ext; unfold raw30293step3 raw30293step2; decide +kernel
      have hl : raw30293step2Labels = labelEmbedding1 ∘ raw30293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30293step2 raw30293step2Labels raw30293step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical30294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30294 raw30294Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw30294 raw30294Labels = mixedMoment B raw30294step0 raw30294step0Labels := by
      have hz : ∀ j, raw30294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30294step0 = (fun i j => raw30294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30294step0 raw30294; decide +kernel
      have hl : raw30294step0Labels = raw30294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30294 raw30294Labels permutation434 hz
    mixedMoment B raw30294step0 raw30294step0Labels = mixedMoment B raw30294step1 raw30294step1Labels := by
      have ha : raw30294step1 = (fun i j => raw30294step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30294step1 raw30294step0; decide +kernel
      have hl : raw30294step1Labels = raw30294step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30294step0 raw30294step0Labels permutation149 permutation5
    mixedMoment B raw30294step1 raw30294step1Labels = mixedMoment B raw30294step2 raw30294step2Labels := by
      have ha : raw30294step2 = raw30294step1 := by apply Matrix.ext; unfold raw30294step2 raw30294step1; decide +kernel
      have hl : raw30294step1Labels = labelEmbedding1 ∘ raw30294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30294step1 raw30294step1Labels raw30294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2149 node2149Labels := by rfl

theorem canonical30295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30295 raw30295Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw30295 raw30295Labels = mixedMoment B raw30295step0 raw30295step0Labels := by
      have hz : ∀ j, raw30295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30295step0 = (fun i j => raw30295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30295step0 raw30295; decide +kernel
      have hl : raw30295step0Labels = raw30295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30295 raw30295Labels permutation434 hz
    mixedMoment B raw30295step0 raw30295step0Labels = mixedMoment B raw30295step1 raw30295step1Labels := by
      have ha : raw30295step1 = (fun i j => raw30295step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30295step1 raw30295step0; decide +kernel
      have hl : raw30295step1Labels = raw30295step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30295step0 raw30295step0Labels permutation151 permutation5
    mixedMoment B raw30295step1 raw30295step1Labels = mixedMoment B raw30295step2 raw30295step2Labels := by
      have ha : raw30295step2 = raw30295step1 := by apply Matrix.ext; unfold raw30295step2 raw30295step1; decide +kernel
      have hl : raw30295step1Labels = labelEmbedding1 ∘ raw30295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30295step1 raw30295step1Labels raw30295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

theorem canonical30296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30296 raw30296Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw30296 raw30296Labels = mixedMoment B raw30296step0 raw30296step0Labels := by
      have hz : ∀ j, raw30296 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30296step0 = (fun i j => raw30296 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30296step0 raw30296; decide +kernel
      have hl : raw30296step0Labels = raw30296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30296 raw30296Labels permutation434 hz
    mixedMoment B raw30296step0 raw30296step0Labels = mixedMoment B raw30296step1 raw30296step1Labels := by
      have ha : raw30296step1 = (fun i j => raw30296step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30296step1 raw30296step0; decide +kernel
      have hl : raw30296step1Labels = raw30296step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30296step0 raw30296step0Labels permutation148 permutation5
    mixedMoment B raw30296step1 raw30296step1Labels = mixedMoment B raw30296step2 raw30296step2Labels := by
      have ha : raw30296step2 = raw30296step1 := by apply Matrix.ext; unfold raw30296step2 raw30296step1; decide +kernel
      have hl : raw30296step1Labels = labelEmbedding1 ∘ raw30296step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30296step1 raw30296step1Labels raw30296step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2153 node2153Labels := by rfl

theorem canonical30297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30297 raw30297Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw30297 raw30297Labels = mixedMoment B raw30297step0 raw30297step0Labels := by
      have ha : raw30297step0 = (fun i j => raw30297 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30297step0 raw30297; decide +kernel
      have hl : raw30297step0Labels = raw30297Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30297 raw30297Labels permutation674 permutation5
    mixedMoment B raw30297step0 raw30297step0Labels = mixedMoment B raw30297step1 raw30297step1Labels := by
      have ha : raw30297step1 = raw30297step0 := by apply Matrix.ext; unfold raw30297step1 raw30297step0; decide +kernel
      have hl : raw30297step0Labels = labelEmbedding1 ∘ raw30297step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30297step0 raw30297step0Labels raw30297step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2147 node2147Labels := by rfl

theorem canonical30298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30298 raw30298Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw30298 raw30298Labels = mixedMoment B raw30298step0 raw30298step0Labels := by
      have hz : ∀ j, raw30298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30298step0 = (fun i j => raw30298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30298step0 raw30298; decide +kernel
      have hl : raw30298step0Labels = raw30298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30298 raw30298Labels permutation434 hz
    mixedMoment B raw30298step0 raw30298step0Labels = mixedMoment B raw30298step1 raw30298step1Labels := by
      have ha : raw30298step1 = (fun i j => raw30298step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30298step1 raw30298step0; decide +kernel
      have hl : raw30298step1Labels = raw30298step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30298step0 raw30298step0Labels permutation139 permutation5
    mixedMoment B raw30298step1 raw30298step1Labels = mixedMoment B raw30298step2 raw30298step2Labels := by
      have ha : raw30298step2 = raw30298step1 := by apply Matrix.ext; unfold raw30298step2 raw30298step1; decide +kernel
      have hl : raw30298step1Labels = labelEmbedding1 ∘ raw30298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30298step1 raw30298step1Labels raw30298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

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

theorem sound2147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2147 node2147Labels = Sparse.eval nodeValue2147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2147) = mixedMoment B node2147 node2147Labels := rfl
  simpa [nodeValue2147, Sparse.eval] using hc.symm

theorem sound2149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2149 node2149Labels = Sparse.eval nodeValue2149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2149) = mixedMoment B node2149 node2149Labels := rfl
  simpa [nodeValue2149, Sparse.eval] using hc.symm

theorem sound2153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2153 node2153Labels = Sparse.eval nodeValue2153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2153) = mixedMoment B node2153 node2153Labels := rfl
  simpa [nodeValue2153, Sparse.eval] using hc.symm

theorem sound2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2164 node2164Labels = Sparse.eval nodeValue2164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2164) = mixedMoment B node2164 node2164Labels := rfl
  simpa [nodeValue2164, Sparse.eval] using hc.symm

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

theorem sound2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2259 node2259Labels = Sparse.eval nodeValue2259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2259) = mixedMoment B node2259 node2259Labels := rfl
  simpa [nodeValue2259, Sparse.eval] using hc.symm

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

theorem sound3258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3258 node3258Labels = Sparse.eval nodeValue3258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3258) = mixedMoment B node3258 node3258Labels := rfl
  simpa [nodeValue3258, Sparse.eval] using hc.symm

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

theorem sound3268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3268 node3268Labels = Sparse.eval nodeValue3268 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3268) = mixedMoment B node3268 node3268Labels := rfl
  simpa [nodeValue3268, Sparse.eval] using hc.symm

theorem sound3270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3270 node3270Labels = Sparse.eval nodeValue3270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3270) = mixedMoment B node3270 node3270Labels := rfl
  simpa [nodeValue3270, Sparse.eval] using hc.symm

theorem sound3295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3295 node3295Labels = Sparse.eval nodeValue3295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3295) = mixedMoment B node3295 node3295Labels := rfl
  simpa [nodeValue3295, Sparse.eval] using hc.symm

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

theorem sound3406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3406 node3406Labels = Sparse.eval nodeValue3406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3406) = mixedMoment B node3406 node3406Labels := rfl
  simpa [nodeValue3406, Sparse.eval] using hc.symm

theorem sound3415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3415 node3415Labels = Sparse.eval nodeValue3415 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3415) = mixedMoment B node3415 node3415Labels := rfl
  simpa [nodeValue3415, Sparse.eval] using hc.symm

theorem sound3417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3417 node3417Labels = Sparse.eval nodeValue3417 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3417) = mixedMoment B node3417 node3417Labels := rfl
  simpa [nodeValue3417, Sparse.eval] using hc.symm

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

theorem sound3459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3459 node3459Labels = Sparse.eval nodeValue3459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3459) = mixedMoment B node3459 node3459Labels := rfl
  simpa [nodeValue3459, Sparse.eval] using hc.symm

theorem sound3462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3462 node3462Labels = Sparse.eval nodeValue3462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3462) = mixedMoment B node3462 node3462Labels := rfl
  simpa [nodeValue3462, Sparse.eval] using hc.symm

theorem sound3463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3463 node3463Labels = Sparse.eval nodeValue3463 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3463) = mixedMoment B node3463 node3463Labels := rfl
  simpa [nodeValue3463, Sparse.eval] using hc.symm

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3470 node3470Labels = Sparse.eval nodeValue3470 (mixedVector B) := by
  simpa only [nodeValue3470, Sparse.eval_nil] using zero3470 B _hB _hF

theorem sound3475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3475 node3475Labels = Sparse.eval nodeValue3475 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3475) = mixedMoment B node3475 node3475Labels := rfl
  simpa [nodeValue3475, Sparse.eval] using hc.symm

theorem sound3479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3479 node3479Labels = Sparse.eval nodeValue3479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3479) = mixedMoment B node3479 node3479Labels := rfl
  simpa [nodeValue3479, Sparse.eval] using hc.symm

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

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3538 node3538Labels = Sparse.eval nodeValue3538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3538) = mixedMoment B node3538 node3538Labels := rfl
  simpa [nodeValue3538, Sparse.eval] using hc.symm

theorem sound3540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3540 node3540Labels = Sparse.eval nodeValue3540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3540) = mixedMoment B node3540 node3540Labels := rfl
  simpa [nodeValue3540, Sparse.eval] using hc.symm

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

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources69
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2211 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2211 + difference 0 1) (sourceB2211 + difference 1 0) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2211 + difference 0 1) (sourceB2211 + difference 1 0) sourceC2211) = raw30269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30269; decide +kernel
    rw [ha]
    exact (canonical30269 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2211 + difference 0 2) (sourceB2211 + difference 2 0) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2211 + difference 0 2) (sourceB2211 + difference 2 0) sourceC2211) = raw30270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30270; decide +kernel
    rw [ha]
    exact (canonical30270 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2211 + difference 0 3) (sourceB2211 + difference 3 0) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2211 + difference 0 3) (sourceB2211 + difference 3 0) sourceC2211) = raw30271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30271; decide +kernel
    rw [ha]
    exact (canonical30271 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2211 + difference 0 4) (sourceB2211 + difference 4 0) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2211 + difference 0 4) (sourceB2211 + difference 4 0) sourceC2211) = raw30272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30272; decide +kernel
    rw [ha]
    exact (canonical30272 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2211 + difference 0 5) (sourceB2211 + difference 5 0) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2211 + difference 0 5) (sourceB2211 + difference 5 0) sourceC2211) = raw30273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30273; decide +kernel
    rw [ha]
    exact (canonical30273 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2211 + difference 1 0) (sourceB2211 + difference 0 1) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA2211 + difference 1 0) (sourceB2211 + difference 0 1) sourceC2211) = raw30274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30274; decide +kernel
    rw [ha]
    exact (canonical30274 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2211 + difference 1 2) (sourceB2211 + difference 2 1) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2211 + difference 1 2) (sourceB2211 + difference 2 1) sourceC2211) = raw30275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30275; decide +kernel
    rw [ha]
    exact (canonical30275 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2211 + difference 1 3) (sourceB2211 + difference 3 1) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2211 + difference 1 3) (sourceB2211 + difference 3 1) sourceC2211) = raw30276 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30276; decide +kernel
    rw [ha]
    exact (canonical30276 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2211 + difference 1 4) (sourceB2211 + difference 4 1) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA2211 + difference 1 4) (sourceB2211 + difference 4 1) sourceC2211) = raw30277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30277; decide +kernel
    rw [ha]
    exact (canonical30277 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2211 + difference 1 5) (sourceB2211 + difference 5 1) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA2211 + difference 1 5) (sourceB2211 + difference 5 1) sourceC2211) = raw30278 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30278; decide +kernel
    rw [ha]
    exact (canonical30278 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2211 + difference 2 0) (sourceB2211 + difference 0 2) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3270) := by
    have ha : (tripleCharges (sourceA2211 + difference 2 0) (sourceB2211 + difference 0 2) sourceC2211) = raw30279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30279; decide +kernel
    rw [ha]
    exact (canonical30279 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2211 + difference 2 1) (sourceB2211 + difference 1 2) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3417) := by
    have ha : (tripleCharges (sourceA2211 + difference 2 1) (sourceB2211 + difference 1 2) sourceC2211) = raw30280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30280; decide +kernel
    rw [ha]
    exact (canonical30280 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2211 + difference 2 3) (sourceB2211 + difference 3 2) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3453) := by
    have ha : (tripleCharges (sourceA2211 + difference 2 3) (sourceB2211 + difference 3 2) sourceC2211) = raw30281 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30281; decide +kernel
    rw [ha]
    exact (canonical30281 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2211 + difference 2 4) (sourceB2211 + difference 4 2) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA2211 + difference 2 4) (sourceB2211 + difference 4 2) sourceC2211) = raw30282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30282; decide +kernel
    rw [ha]
    exact (canonical30282 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2211 + difference 2 5) (sourceB2211 + difference 5 2) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2211 + difference 2 5) (sourceB2211 + difference 5 2) sourceC2211) = raw30283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30283; decide +kernel
    rw [ha]
    exact (canonical30283 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2211 + difference 3 0) (sourceB2211 + difference 0 3) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3258) := by
    have ha : (tripleCharges (sourceA2211 + difference 3 0) (sourceB2211 + difference 0 3) sourceC2211) = raw30284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30284; decide +kernel
    rw [ha]
    exact (canonical30284 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2211 + difference 3 1) (sourceB2211 + difference 1 3) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2211 + difference 3 1) (sourceB2211 + difference 1 3) sourceC2211) = raw30285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30285; decide +kernel
    rw [ha]
    exact (canonical30285 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2211 + difference 3 2) (sourceB2211 + difference 2 3) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3462) := by
    have ha : (tripleCharges (sourceA2211 + difference 3 2) (sourceB2211 + difference 2 3) sourceC2211) = raw30286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30286; decide +kernel
    rw [ha]
    exact (canonical30286 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2211 + difference 3 4) (sourceB2211 + difference 4 3) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA2211 + difference 3 4) (sourceB2211 + difference 4 3) sourceC2211) = raw30287 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30287; decide +kernel
    rw [ha]
    exact (canonical30287 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2211 + difference 3 5) (sourceB2211 + difference 5 3) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA2211 + difference 3 5) (sourceB2211 + difference 5 3) sourceC2211) = raw30288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30288; decide +kernel
    rw [ha]
    exact (canonical30288 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2211 + difference 4 0) (sourceB2211 + difference 0 4) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA2211 + difference 4 0) (sourceB2211 + difference 0 4) sourceC2211) = raw30289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30289; decide +kernel
    rw [ha]
    exact (canonical30289 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2211 + difference 4 1) (sourceB2211 + difference 1 4) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2211 + difference 4 1) (sourceB2211 + difference 1 4) sourceC2211) = raw30290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30290; decide +kernel
    rw [ha]
    exact (canonical30290 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2211 + difference 4 2) (sourceB2211 + difference 2 4) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2211 + difference 4 2) (sourceB2211 + difference 2 4) sourceC2211) = raw30291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30291; decide +kernel
    rw [ha]
    exact (canonical30291 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2211 + difference 4 3) (sourceB2211 + difference 3 4) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3452) := by
    have ha : (tripleCharges (sourceA2211 + difference 4 3) (sourceB2211 + difference 3 4) sourceC2211) = raw30292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30292; decide +kernel
    rw [ha]
    exact (canonical30292 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2211 + difference 4 5) (sourceB2211 + difference 5 4) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2211 + difference 4 5) (sourceB2211 + difference 5 4) sourceC2211) = raw30293 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30293; decide +kernel
    rw [ha]
    exact (canonical30293 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2211 + difference 5 0) (sourceB2211 + difference 0 5) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2149) := by
    have ha : (tripleCharges (sourceA2211 + difference 5 0) (sourceB2211 + difference 0 5) sourceC2211) = raw30294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30294; decide +kernel
    rw [ha]
    exact (canonical30294 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2211 + difference 5 1) (sourceB2211 + difference 1 5) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA2211 + difference 5 1) (sourceB2211 + difference 1 5) sourceC2211) = raw30295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30295; decide +kernel
    rw [ha]
    exact (canonical30295 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2211 + difference 5 2) (sourceB2211 + difference 2 5) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2153) := by
    have ha : (tripleCharges (sourceA2211 + difference 5 2) (sourceB2211 + difference 2 5) sourceC2211) = raw30296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30296; decide +kernel
    rw [ha]
    exact (canonical30296 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2211 + difference 5 3) (sourceB2211 + difference 3 5) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2147) := by
    have ha : (tripleCharges (sourceA2211 + difference 5 3) (sourceB2211 + difference 3 5) sourceC2211) = raw30297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30297; decide +kernel
    rw [ha]
    exact (canonical30297 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2211 + difference 5 4) (sourceB2211 + difference 4 5) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA2211 + difference 5 4) (sourceB2211 + difference 4 5) sourceC2211) = raw30298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30298; decide +kernel
    rw [ha]
    exact (canonical30298 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2211 sourceB2211 sourceC2211
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2211, Integer.Sparse.eval]
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

theorem reindexCheck1826 : Integer.Sparse.reindex keyMap MixedData.row1826 = numericRow1826 := by decide +kernel

theorem numericCheck1826 (x : Master → ℝ) : Integer.Sparse.eval numericRow1826 x =
    (1 : ℝ) * reducedSource1826 x := by
  norm_num [numericRow1826, reducedSource1826, Integer.Sparse.eval, Sparse.eval, nodeValue2147, nodeValue2149, nodeValue2153, nodeValue2164, nodeValue2259, nodeValue3258, nodeValue3268, nodeValue3270, nodeValue3295, nodeValue3406, nodeValue3415, nodeValue3417, nodeValue3452, nodeValue3453, nodeValue3459, nodeValue3462, nodeValue3463, nodeValue3468, nodeValue3470, nodeValue3475, nodeValue3479, nodeValue3516, nodeValue3533, nodeValue3538, nodeValue3540, nodeValue3770, nodeValue3795, nodeValue3807, nodeValue3811, nodeValue3813]

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

theorem reducedZero1826 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1826 (mixedVector B) = 0 := by
  have h2147 : mixedVector B (Sum.inr 2147) = Sparse.eval nodeValue2147 (mixedVector B) := by
    change mixedMoment B node2147 node2147Labels = _
    exact sound2147 B hB hF
  have h2149 : mixedVector B (Sum.inr 2149) = Sparse.eval nodeValue2149 (mixedVector B) := by
    change mixedMoment B node2149 node2149Labels = _
    exact sound2149 B hB hF
  have h2153 : mixedVector B (Sum.inr 2153) = Sparse.eval nodeValue2153 (mixedVector B) := by
    change mixedMoment B node2153 node2153Labels = _
    exact sound2153 B hB hF
  have h2164 : mixedVector B (Sum.inr 2164) = Sparse.eval nodeValue2164 (mixedVector B) := by
    change mixedMoment B node2164 node2164Labels = _
    exact sound2164 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h3258 : mixedVector B (Sum.inr 3258) = Sparse.eval nodeValue3258 (mixedVector B) := by
    change mixedMoment B node3258 node3258Labels = _
    exact sound3258 B hB hF
  have h3268 : mixedVector B (Sum.inr 3268) = Sparse.eval nodeValue3268 (mixedVector B) := by
    change mixedMoment B node3268 node3268Labels = _
    exact sound3268 B hB hF
  have h3270 : mixedVector B (Sum.inr 3270) = Sparse.eval nodeValue3270 (mixedVector B) := by
    change mixedMoment B node3270 node3270Labels = _
    exact sound3270 B hB hF
  have h3295 : mixedVector B (Sum.inr 3295) = Sparse.eval nodeValue3295 (mixedVector B) := by
    change mixedMoment B node3295 node3295Labels = _
    exact sound3295 B hB hF
  have h3406 : mixedVector B (Sum.inr 3406) = Sparse.eval nodeValue3406 (mixedVector B) := by
    change mixedMoment B node3406 node3406Labels = _
    exact sound3406 B hB hF
  have h3415 : mixedVector B (Sum.inr 3415) = Sparse.eval nodeValue3415 (mixedVector B) := by
    change mixedMoment B node3415 node3415Labels = _
    exact sound3415 B hB hF
  have h3417 : mixedVector B (Sum.inr 3417) = Sparse.eval nodeValue3417 (mixedVector B) := by
    change mixedMoment B node3417 node3417Labels = _
    exact sound3417 B hB hF
  have h3452 : mixedVector B (Sum.inr 3452) = Sparse.eval nodeValue3452 (mixedVector B) := by
    change mixedMoment B node3452 node3452Labels = _
    exact sound3452 B hB hF
  have h3453 : mixedVector B (Sum.inr 3453) = Sparse.eval nodeValue3453 (mixedVector B) := by
    change mixedMoment B node3453 node3453Labels = _
    exact sound3453 B hB hF
  have h3459 : mixedVector B (Sum.inr 3459) = Sparse.eval nodeValue3459 (mixedVector B) := by
    change mixedMoment B node3459 node3459Labels = _
    exact sound3459 B hB hF
  have h3462 : mixedVector B (Sum.inr 3462) = Sparse.eval nodeValue3462 (mixedVector B) := by
    change mixedMoment B node3462 node3462Labels = _
    exact sound3462 B hB hF
  have h3463 : mixedVector B (Sum.inr 3463) = Sparse.eval nodeValue3463 (mixedVector B) := by
    change mixedMoment B node3463 node3463Labels = _
    exact sound3463 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3470 : mixedVector B (Sum.inr 3470) = Sparse.eval nodeValue3470 (mixedVector B) := by
    change mixedMoment B node3470 node3470Labels = _
    exact sound3470 B hB hF
  have h3475 : mixedVector B (Sum.inr 3475) = Sparse.eval nodeValue3475 (mixedVector B) := by
    change mixedMoment B node3475 node3475Labels = _
    exact sound3475 B hB hF
  have h3479 : mixedVector B (Sum.inr 3479) = Sparse.eval nodeValue3479 (mixedVector B) := by
    change mixedMoment B node3479 node3479Labels = _
    exact sound3479 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3811 : mixedVector B (Sum.inr 3811) = Sparse.eval nodeValue3811 (mixedVector B) := by
    change mixedMoment B node3811 node3811Labels = _
    exact sound3811 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  simpa only [sourceForm2211, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2147, h2149, h2153, h2164, h2259, h3258, h3268, h3270, h3295, h3406, h3415, h3417, h3452, h3453, h3459, h3462, h3463, h3468, h3470, h3475, h3479, h3516, h3533, h3538, h3540, h3770, h3795, h3807, h3811, h3813, reducedSource1826] using sourceEq2211 B hB

theorem rowSound1826_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1826 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1826, numericCheck1826, reducedZero1826 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826_e_oai
