-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:25:11.199026+00:00
-- url     : https://prove2.me/submissions/3006739f-06d4-4a8b-be9e-ea94dc95d99f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E107
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical193
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32940 raw32940Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw32940 raw32940Labels = mixedMoment B raw32940step0 raw32940step0Labels := by
      have ha : raw32940step0 = (fun i j => raw32940 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32940step0 raw32940; decide +kernel
      have hl : raw32940step0Labels = raw32940Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32940 raw32940Labels permutation662 permutation7
    mixedMoment B raw32940step0 raw32940step0Labels = mixedMoment B raw32940step1 raw32940step1Labels := by
      have ha : raw32940step1 = raw32940step0 := by apply Matrix.ext; unfold raw32940step1 raw32940step0; decide +kernel
      have hl : raw32940step0Labels = labelEmbedding1 ∘ raw32940step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32940step0 raw32940step0Labels raw32940step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical32941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32941 raw32941Labels = mixedMoment B node3793 node3793Labels := by
  calc
    mixedMoment B raw32941 raw32941Labels = mixedMoment B raw32941step0 raw32941step0Labels := by
      have ha : raw32941step0 = (fun i j => raw32941 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32941step0 raw32941; decide +kernel
      have hl : raw32941step0Labels = raw32941Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32941 raw32941Labels permutation662 permutation7
    mixedMoment B raw32941step0 raw32941step0Labels = mixedMoment B raw32941step1 raw32941step1Labels := by
      have ha : raw32941step1 = raw32941step0 := by apply Matrix.ext; unfold raw32941step1 raw32941step0; decide +kernel
      have hl : raw32941step0Labels = labelEmbedding1 ∘ raw32941step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32941step0 raw32941step0Labels raw32941step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3793 node3793Labels := by rfl

theorem canonical32942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32942 raw32942Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw32942 raw32942Labels = mixedMoment B raw32942step0 raw32942step0Labels := by
      have ha : raw32942step0 = (fun i j => raw32942 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32942step0 raw32942; decide +kernel
      have hl : raw32942step0Labels = raw32942Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32942 raw32942Labels permutation662 permutation7
    mixedMoment B raw32942step0 raw32942step0Labels = mixedMoment B raw32942step1 raw32942step1Labels := by
      have ha : raw32942step1 = raw32942step0 := by apply Matrix.ext; unfold raw32942step1 raw32942step0; decide +kernel
      have hl : raw32942step0Labels = labelEmbedding1 ∘ raw32942step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32942step0 raw32942step0Labels raw32942step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical32943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32943 raw32943Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw32943 raw32943Labels = mixedMoment B raw32943step0 raw32943step0Labels := by
      have hz : ∀ j, raw32943 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32943step0 = (fun i j => raw32943 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32943step0 raw32943; decide +kernel
      have hl : raw32943step0Labels = raw32943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32943 raw32943Labels permutation520 hz
    mixedMoment B raw32943step0 raw32943step0Labels = mixedMoment B raw32943step1 raw32943step1Labels := by
      have ha : raw32943step1 = (fun i j => raw32943step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32943step1 raw32943step0; decide +kernel
      have hl : raw32943step1Labels = raw32943step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32943step0 raw32943step0Labels permutation149 permutation7
    mixedMoment B raw32943step1 raw32943step1Labels = mixedMoment B raw32943step2 raw32943step2Labels := by
      have ha : raw32943step2 = raw32943step1 := by apply Matrix.ext; unfold raw32943step2 raw32943step1; decide +kernel
      have hl : raw32943step1Labels = labelEmbedding1 ∘ raw32943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32943step1 raw32943step1Labels raw32943step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical32944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32944 raw32944Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw32944 raw32944Labels = mixedMoment B raw32944step0 raw32944step0Labels := by
      have ha : raw32944step0 = (fun i j => raw32944 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32944step0 raw32944; decide +kernel
      have hl : raw32944step0Labels = raw32944Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32944 raw32944Labels permutation178 permutation7
    mixedMoment B raw32944step0 raw32944step0Labels = mixedMoment B raw32944step1 raw32944step1Labels := by
      have ha : raw32944step1 = -raw32944step0 := by apply Matrix.ext; change ∀ i j, raw32944step1 i j = -(raw32944step0 i j); unfold raw32944step1 raw32944step0; decide +kernel
      have hl : raw32944step1Labels = raw32944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32944step1 raw32944step1Labels = mixedMoment B raw32944step2 raw32944step2Labels := by
      have ha : raw32944step2 = raw32944step1 := by apply Matrix.ext; unfold raw32944step2 raw32944step1; decide +kernel
      have hl : raw32944step1Labels = labelEmbedding1 ∘ raw32944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32944step1 raw32944step1Labels raw32944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical32945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32945 raw32945Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw32945 raw32945Labels = mixedMoment B raw32945step0 raw32945step0Labels := by
      have hz : ∀ j, raw32945 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32945step0 = (fun i j => raw32945 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32945step0 raw32945; decide +kernel
      have hl : raw32945step0Labels = raw32945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32945 raw32945Labels permutation265 hz
    mixedMoment B raw32945step0 raw32945step0Labels = mixedMoment B raw32945step1 raw32945step1Labels := by
      have ha : raw32945step1 = (fun i j => raw32945step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32945step1 raw32945step0; decide +kernel
      have hl : raw32945step1Labels = raw32945step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32945step0 raw32945step0Labels permutation34 permutation7
    mixedMoment B raw32945step1 raw32945step1Labels = mixedMoment B raw32945step2 raw32945step2Labels := by
      have ha : raw32945step2 = -raw32945step1 := by apply Matrix.ext; change ∀ i j, raw32945step2 i j = -(raw32945step1 i j); unfold raw32945step2 raw32945step1; decide +kernel
      have hl : raw32945step2Labels = raw32945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32945step2 raw32945step2Labels = mixedMoment B raw32945step3 raw32945step3Labels := by
      have ha : raw32945step3 = raw32945step2 := by apply Matrix.ext; unfold raw32945step3 raw32945step2; decide +kernel
      have hl : raw32945step2Labels = labelEmbedding1 ∘ raw32945step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32945step2 raw32945step2Labels raw32945step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical32946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32946 raw32946Labels = mixedMoment B node3553 node3553Labels := by
  calc
    mixedMoment B raw32946 raw32946Labels = mixedMoment B raw32946step0 raw32946step0Labels := by
      have ha : raw32946step0 = (fun i j => raw32946 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32946step0 raw32946; decide +kernel
      have hl : raw32946step0Labels = raw32946Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32946 raw32946Labels permutation178 permutation7
    mixedMoment B raw32946step0 raw32946step0Labels = mixedMoment B raw32946step1 raw32946step1Labels := by
      have ha : raw32946step1 = -raw32946step0 := by apply Matrix.ext; change ∀ i j, raw32946step1 i j = -(raw32946step0 i j); unfold raw32946step1 raw32946step0; decide +kernel
      have hl : raw32946step1Labels = raw32946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32946step1 raw32946step1Labels = mixedMoment B raw32946step2 raw32946step2Labels := by
      have ha : raw32946step2 = raw32946step1 := by apply Matrix.ext; unfold raw32946step2 raw32946step1; decide +kernel
      have hl : raw32946step1Labels = labelEmbedding1 ∘ raw32946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32946step1 raw32946step1Labels raw32946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3553 node3553Labels := by rfl

theorem canonical32947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32947 raw32947Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw32947 raw32947Labels = mixedMoment B raw32947step0 raw32947step0Labels := by
      have ha : raw32947step0 = (fun i j => raw32947 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32947step0 raw32947; decide +kernel
      have hl : raw32947step0Labels = raw32947Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32947 raw32947Labels permutation178 permutation7
    mixedMoment B raw32947step0 raw32947step0Labels = mixedMoment B raw32947step1 raw32947step1Labels := by
      have ha : raw32947step1 = -raw32947step0 := by apply Matrix.ext; change ∀ i j, raw32947step1 i j = -(raw32947step0 i j); unfold raw32947step1 raw32947step0; decide +kernel
      have hl : raw32947step1Labels = raw32947step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32947step1 raw32947step1Labels = mixedMoment B raw32947step2 raw32947step2Labels := by
      have ha : raw32947step2 = raw32947step1 := by apply Matrix.ext; unfold raw32947step2 raw32947step1; decide +kernel
      have hl : raw32947step1Labels = labelEmbedding1 ∘ raw32947step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32947step1 raw32947step1Labels raw32947step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical32948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32948 raw32948Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw32948 raw32948Labels = mixedMoment B raw32948step0 raw32948step0Labels := by
      have hz : ∀ j, raw32948 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32948step0 = (fun i j => raw32948 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32948step0 raw32948; decide +kernel
      have hl : raw32948step0Labels = raw32948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32948 raw32948Labels permutation520 hz
    mixedMoment B raw32948step0 raw32948step0Labels = mixedMoment B raw32948step1 raw32948step1Labels := by
      have ha : raw32948step1 = (fun i j => raw32948step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32948step1 raw32948step0; decide +kernel
      have hl : raw32948step1Labels = raw32948step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32948step0 raw32948step0Labels permutation38 permutation7
    mixedMoment B raw32948step1 raw32948step1Labels = mixedMoment B raw32948step2 raw32948step2Labels := by
      have ha : raw32948step2 = -raw32948step1 := by apply Matrix.ext; change ∀ i j, raw32948step2 i j = -(raw32948step1 i j); unfold raw32948step2 raw32948step1; decide +kernel
      have hl : raw32948step2Labels = raw32948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32948step2 raw32948step2Labels = mixedMoment B raw32948step3 raw32948step3Labels := by
      have ha : raw32948step3 = raw32948step2 := by apply Matrix.ext; unfold raw32948step3 raw32948step2; decide +kernel
      have hl : raw32948step2Labels = labelEmbedding1 ∘ raw32948step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32948step2 raw32948step2Labels raw32948step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical32949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32949 raw32949Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw32949 raw32949Labels = mixedMoment B raw32949step0 raw32949step0Labels := by
      have ha : raw32949step0 = (fun i j => raw32949 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32949step0 raw32949; decide +kernel
      have hl : raw32949step0Labels = raw32949Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32949 raw32949Labels permutation178 permutation7
    mixedMoment B raw32949step0 raw32949step0Labels = mixedMoment B raw32949step1 raw32949step1Labels := by
      have ha : raw32949step1 = -raw32949step0 := by apply Matrix.ext; change ∀ i j, raw32949step1 i j = -(raw32949step0 i j); unfold raw32949step1 raw32949step0; decide +kernel
      have hl : raw32949step1Labels = raw32949step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32949step1 raw32949step1Labels = mixedMoment B raw32949step2 raw32949step2Labels := by
      have ha : raw32949step2 = raw32949step1 := by apply Matrix.ext; unfold raw32949step2 raw32949step1; decide +kernel
      have hl : raw32949step1Labels = labelEmbedding1 ∘ raw32949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32949step1 raw32949step1Labels raw32949step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

theorem canonical32950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32950 raw32950Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw32950 raw32950Labels = mixedMoment B raw32950step0 raw32950step0Labels := by
      have ha : raw32950step0 = (fun i j => raw32950 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32950step0 raw32950; decide +kernel
      have hl : raw32950step0Labels = raw32950Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32950 raw32950Labels permutation178 permutation7
    mixedMoment B raw32950step0 raw32950step0Labels = mixedMoment B raw32950step1 raw32950step1Labels := by
      have ha : raw32950step1 = -raw32950step0 := by apply Matrix.ext; change ∀ i j, raw32950step1 i j = -(raw32950step0 i j); unfold raw32950step1 raw32950step0; decide +kernel
      have hl : raw32950step1Labels = raw32950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32950step1 raw32950step1Labels = mixedMoment B raw32950step2 raw32950step2Labels := by
      have ha : raw32950step2 = raw32950step1 := by apply Matrix.ext; unfold raw32950step2 raw32950step1; decide +kernel
      have hl : raw32950step1Labels = labelEmbedding1 ∘ raw32950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32950step1 raw32950step1Labels raw32950step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

theorem canonical32951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32951 raw32951Labels = mixedMoment B node3450 node3450Labels := by
  calc
    mixedMoment B raw32951 raw32951Labels = mixedMoment B raw32951step0 raw32951step0Labels := by
      have ha : raw32951step0 = (fun i j => raw32951 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32951step0 raw32951; decide +kernel
      have hl : raw32951step0Labels = raw32951Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32951 raw32951Labels permutation178 permutation7
    mixedMoment B raw32951step0 raw32951step0Labels = mixedMoment B raw32951step1 raw32951step1Labels := by
      have ha : raw32951step1 = -raw32951step0 := by apply Matrix.ext; change ∀ i j, raw32951step1 i j = -(raw32951step0 i j); unfold raw32951step1 raw32951step0; decide +kernel
      have hl : raw32951step1Labels = raw32951step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32951step1 raw32951step1Labels = mixedMoment B raw32951step2 raw32951step2Labels := by
      have ha : raw32951step2 = raw32951step1 := by apply Matrix.ext; unfold raw32951step2 raw32951step1; decide +kernel
      have hl : raw32951step1Labels = labelEmbedding1 ∘ raw32951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32951step1 raw32951step1Labels raw32951step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3450 node3450Labels := by rfl

theorem canonical32952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32952 raw32952Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw32952 raw32952Labels = mixedMoment B raw32952step0 raw32952step0Labels := by
      have hz : ∀ j, raw32952 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32952step0 = (fun i j => raw32952 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32952step0 raw32952; decide +kernel
      have hl : raw32952step0Labels = raw32952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32952 raw32952Labels permutation520 hz
    mixedMoment B raw32952step0 raw32952step0Labels = mixedMoment B raw32952step1 raw32952step1Labels := by
      have ha : raw32952step1 = (fun i j => raw32952step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32952step1 raw32952step0; decide +kernel
      have hl : raw32952step1Labels = raw32952step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32952step0 raw32952step0Labels permutation38 permutation7
    mixedMoment B raw32952step1 raw32952step1Labels = mixedMoment B raw32952step2 raw32952step2Labels := by
      have ha : raw32952step2 = -raw32952step1 := by apply Matrix.ext; change ∀ i j, raw32952step2 i j = -(raw32952step1 i j); unfold raw32952step2 raw32952step1; decide +kernel
      have hl : raw32952step2Labels = raw32952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32952step2 raw32952step2Labels = mixedMoment B raw32952step3 raw32952step3Labels := by
      have ha : raw32952step3 = raw32952step2 := by apply Matrix.ext; unfold raw32952step3 raw32952step2; decide +kernel
      have hl : raw32952step2Labels = labelEmbedding1 ∘ raw32952step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32952step2 raw32952step2Labels raw32952step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical32953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32953 raw32953Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw32953 raw32953Labels = mixedMoment B raw32953step0 raw32953step0Labels := by
      have ha : raw32953step0 = (fun i j => raw32953 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32953step0 raw32953; decide +kernel
      have hl : raw32953step0Labels = raw32953Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32953 raw32953Labels permutation178 permutation7
    mixedMoment B raw32953step0 raw32953step0Labels = mixedMoment B raw32953step1 raw32953step1Labels := by
      have ha : raw32953step1 = -raw32953step0 := by apply Matrix.ext; change ∀ i j, raw32953step1 i j = -(raw32953step0 i j); unfold raw32953step1 raw32953step0; decide +kernel
      have hl : raw32953step1Labels = raw32953step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32953step1 raw32953step1Labels = mixedMoment B raw32953step2 raw32953step2Labels := by
      have ha : raw32953step2 = raw32953step1 := by apply Matrix.ext; unfold raw32953step2 raw32953step1; decide +kernel
      have hl : raw32953step1Labels = labelEmbedding1 ∘ raw32953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32953step1 raw32953step1Labels raw32953step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3515 node3515Labels := by rfl

theorem canonical32954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32954 raw32954Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw32954 raw32954Labels = mixedMoment B raw32954step0 raw32954step0Labels := by
      have ha : raw32954step0 = (fun i j => raw32954 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32954step0 raw32954; decide +kernel
      have hl : raw32954step0Labels = raw32954Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32954 raw32954Labels permutation178 permutation7
    mixedMoment B raw32954step0 raw32954step0Labels = mixedMoment B raw32954step1 raw32954step1Labels := by
      have ha : raw32954step1 = -raw32954step0 := by apply Matrix.ext; change ∀ i j, raw32954step1 i j = -(raw32954step0 i j); unfold raw32954step1 raw32954step0; decide +kernel
      have hl : raw32954step1Labels = raw32954step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32954step1 raw32954step1Labels = mixedMoment B raw32954step2 raw32954step2Labels := by
      have ha : raw32954step2 = raw32954step1 := by apply Matrix.ext; unfold raw32954step2 raw32954step1; decide +kernel
      have hl : raw32954step1Labels = labelEmbedding1 ∘ raw32954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32954step1 raw32954step1Labels raw32954step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

theorem canonical32955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32955 raw32955Labels = mixedMoment B node3453 node3453Labels := by
  calc
    mixedMoment B raw32955 raw32955Labels = mixedMoment B raw32955step0 raw32955step0Labels := by
      have ha : raw32955step0 = (fun i j => raw32955 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32955step0 raw32955; decide +kernel
      have hl : raw32955step0Labels = raw32955Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32955 raw32955Labels permutation178 permutation7
    mixedMoment B raw32955step0 raw32955step0Labels = mixedMoment B raw32955step1 raw32955step1Labels := by
      have ha : raw32955step1 = -raw32955step0 := by apply Matrix.ext; change ∀ i j, raw32955step1 i j = -(raw32955step0 i j); unfold raw32955step1 raw32955step0; decide +kernel
      have hl : raw32955step1Labels = raw32955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32955step1 raw32955step1Labels = mixedMoment B raw32955step2 raw32955step2Labels := by
      have ha : raw32955step2 = raw32955step1 := by apply Matrix.ext; unfold raw32955step2 raw32955step1; decide +kernel
      have hl : raw32955step1Labels = labelEmbedding1 ∘ raw32955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32955step1 raw32955step1Labels raw32955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3453 node3453Labels := by rfl

theorem canonical32956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32956 raw32956Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw32956 raw32956Labels = mixedMoment B raw32956step0 raw32956step0Labels := by
      have ha : raw32956step0 = (fun i j => raw32956 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32956step0 raw32956; decide +kernel
      have hl : raw32956step0Labels = raw32956Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32956 raw32956Labels permutation178 permutation7
    mixedMoment B raw32956step0 raw32956step0Labels = mixedMoment B raw32956step1 raw32956step1Labels := by
      have ha : raw32956step1 = -raw32956step0 := by apply Matrix.ext; change ∀ i j, raw32956step1 i j = -(raw32956step0 i j); unfold raw32956step1 raw32956step0; decide +kernel
      have hl : raw32956step1Labels = raw32956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32956step1 raw32956step1Labels = mixedMoment B raw32956step2 raw32956step2Labels := by
      have ha : raw32956step2 = raw32956step1 := by apply Matrix.ext; unfold raw32956step2 raw32956step1; decide +kernel
      have hl : raw32956step1Labels = labelEmbedding1 ∘ raw32956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32956step1 raw32956step1Labels raw32956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical32957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32957 raw32957Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw32957 raw32957Labels = mixedMoment B raw32957step0 raw32957step0Labels := by
      have ha : raw32957step0 = (fun i j => raw32957 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32957step0 raw32957; decide +kernel
      have hl : raw32957step0Labels = raw32957Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32957 raw32957Labels permutation178 permutation7
    mixedMoment B raw32957step0 raw32957step0Labels = mixedMoment B raw32957step1 raw32957step1Labels := by
      have ha : raw32957step1 = -raw32957step0 := by apply Matrix.ext; change ∀ i j, raw32957step1 i j = -(raw32957step0 i j); unfold raw32957step1 raw32957step0; decide +kernel
      have hl : raw32957step1Labels = raw32957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32957step1 raw32957step1Labels = mixedMoment B raw32957step2 raw32957step2Labels := by
      have ha : raw32957step2 = raw32957step1 := by apply Matrix.ext; unfold raw32957step2 raw32957step1; decide +kernel
      have hl : raw32957step1Labels = labelEmbedding1 ∘ raw32957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32957step1 raw32957step1Labels raw32957step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

theorem canonical32958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32958 raw32958Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw32958 raw32958Labels = mixedMoment B raw32958step0 raw32958step0Labels := by
      have ha : raw32958step0 = (fun i j => raw32958 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32958step0 raw32958; decide +kernel
      have hl : raw32958step0Labels = raw32958Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32958 raw32958Labels permutation662 permutation7
    mixedMoment B raw32958step0 raw32958step0Labels = mixedMoment B raw32958step1 raw32958step1Labels := by
      have ha : raw32958step1 = raw32958step0 := by apply Matrix.ext; unfold raw32958step1 raw32958step0; decide +kernel
      have hl : raw32958step0Labels = labelEmbedding1 ∘ raw32958step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32958step0 raw32958step0Labels raw32958step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

theorem canonical32959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32959 raw32959Labels = mixedMoment B node3449 node3449Labels := by
  calc
    mixedMoment B raw32959 raw32959Labels = mixedMoment B raw32959step0 raw32959step0Labels := by
      have ha : raw32959step0 = (fun i j => raw32959 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32959step0 raw32959; decide +kernel
      have hl : raw32959step0Labels = raw32959Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32959 raw32959Labels permutation662 permutation7
    mixedMoment B raw32959step0 raw32959step0Labels = mixedMoment B raw32959step1 raw32959step1Labels := by
      have ha : raw32959step1 = raw32959step0 := by apply Matrix.ext; unfold raw32959step1 raw32959step0; decide +kernel
      have hl : raw32959step0Labels = labelEmbedding1 ∘ raw32959step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32959step0 raw32959step0Labels raw32959step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3449 node3449Labels := by rfl

theorem canonical32960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32960 raw32960Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw32960 raw32960Labels = mixedMoment B raw32960step0 raw32960step0Labels := by
      have ha : raw32960step0 = (fun i j => raw32960 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32960step0 raw32960; decide +kernel
      have hl : raw32960step0Labels = raw32960Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32960 raw32960Labels permutation662 permutation7
    mixedMoment B raw32960step0 raw32960step0Labels = mixedMoment B raw32960step1 raw32960step1Labels := by
      have ha : raw32960step1 = raw32960step0 := by apply Matrix.ext; unfold raw32960step1 raw32960step0; decide +kernel
      have hl : raw32960step0Labels = labelEmbedding1 ∘ raw32960step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32960step0 raw32960step0Labels raw32960step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3513 node3513Labels := by rfl

theorem canonical32961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32961 raw32961Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw32961 raw32961Labels = mixedMoment B raw32961step0 raw32961step0Labels := by
      have hz : ∀ j, raw32961 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32961step0 = (fun i j => raw32961 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32961step0 raw32961; decide +kernel
      have hl : raw32961step0Labels = raw32961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32961 raw32961Labels permutation520 hz
    mixedMoment B raw32961step0 raw32961step0Labels = mixedMoment B raw32961step1 raw32961step1Labels := by
      have ha : raw32961step1 = (fun i j => raw32961step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32961step1 raw32961step0; decide +kernel
      have hl : raw32961step1Labels = raw32961step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32961step0 raw32961step0Labels permutation149 permutation7
    mixedMoment B raw32961step1 raw32961step1Labels = mixedMoment B raw32961step2 raw32961step2Labels := by
      have ha : raw32961step2 = raw32961step1 := by apply Matrix.ext; unfold raw32961step2 raw32961step1; decide +kernel
      have hl : raw32961step1Labels = labelEmbedding1 ∘ raw32961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32961step1 raw32961step1Labels raw32961step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

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

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

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

theorem sound3449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3449 node3449Labels = Sparse.eval nodeValue3449 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3449) = mixedMoment B node3449 node3449Labels := rfl
  simpa [nodeValue3449, Sparse.eval] using hc.symm

theorem sound3450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3450 node3450Labels = Sparse.eval nodeValue3450 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3450) = mixedMoment B node3450 node3450Labels := rfl
  simpa [nodeValue3450, Sparse.eval] using hc.symm

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

theorem zero3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3513 node3513Labels = 0 := by
  exact mixedMoment_alpha B hF node3513 node3513Labels 1 permutation444
    (by decide +kernel)

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

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3470 node3470Labels = Sparse.eval nodeValue3470 (mixedVector B) := by
  simpa only [nodeValue3470, Sparse.eval_nil] using zero3470 B _hB _hF

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

theorem sound3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3513 node3513Labels = Sparse.eval nodeValue3513 (mixedVector B) := by
  simpa only [nodeValue3513, Sparse.eval_nil] using zero3513 B _hB _hF

theorem sound3515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3515 node3515Labels = Sparse.eval nodeValue3515 (mixedVector B) := by
  simpa only [nodeValue3515, Sparse.eval_nil] using zero3515 B _hB _hF

theorem sound3516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3516 node3516Labels = Sparse.eval nodeValue3516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3516) = mixedMoment B node3516 node3516Labels := rfl
  simpa [nodeValue3516, Sparse.eval] using hc.symm

theorem sound3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3517 node3517Labels = Sparse.eval nodeValue3517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3517) = mixedMoment B node3517 node3517Labels := rfl
  simpa [nodeValue3517, Sparse.eval] using hc.symm

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

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

theorem sound3553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3553 node3553Labels = Sparse.eval nodeValue3553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3553) = mixedMoment B node3553 node3553Labels := rfl
  simpa [nodeValue3553, Sparse.eval] using hc.symm

theorem sound3557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3557 node3557Labels = Sparse.eval nodeValue3557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3557) = mixedMoment B node3557 node3557Labels := rfl
  simpa [nodeValue3557, Sparse.eval] using hc.symm

theorem sound3558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3558 node3558Labels = Sparse.eval nodeValue3558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3558) = mixedMoment B node3558 node3558Labels := rfl
  simpa [nodeValue3558, Sparse.eval] using hc.symm

theorem sound3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3564 node3564Labels = Sparse.eval nodeValue3564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3564) = mixedMoment B node3564 node3564Labels := rfl
  simpa [nodeValue3564, Sparse.eval] using hc.symm

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

theorem sound3793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3793 node3793Labels = Sparse.eval nodeValue3793 (mixedVector B) := by
  simpa only [nodeValue3793, Sparse.eval_nil] using zero3793 B _hB _hF

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources75
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2403 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2403 + difference 0 1) (sourceB2403 + difference 1 0) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2403 + difference 0 1) (sourceB2403 + difference 1 0) sourceC2403) = raw32940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32940; decide +kernel
    rw [ha]
    exact (canonical32940 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2403 + difference 0 2) (sourceB2403 + difference 2 0) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3793) := by
    have ha : (tripleCharges (sourceA2403 + difference 0 2) (sourceB2403 + difference 2 0) sourceC2403) = raw32941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32941; decide +kernel
    rw [ha]
    exact (canonical32941 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2403 + difference 0 3) (sourceB2403 + difference 3 0) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA2403 + difference 0 3) (sourceB2403 + difference 3 0) sourceC2403) = raw32942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32942; decide +kernel
    rw [ha]
    exact (canonical32942 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2403 + difference 0 4) (sourceB2403 + difference 4 0) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2403 + difference 0 4) (sourceB2403 + difference 4 0) sourceC2403) = raw32943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32943; decide +kernel
    rw [ha]
    exact (canonical32943 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2403 + difference 0 5) (sourceB2403 + difference 5 0) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA2403 + difference 0 5) (sourceB2403 + difference 5 0) sourceC2403) = raw32944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32944; decide +kernel
    rw [ha]
    exact (canonical32944 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2403 + difference 1 0) (sourceB2403 + difference 0 1) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA2403 + difference 1 0) (sourceB2403 + difference 0 1) sourceC2403) = raw32945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32945; decide +kernel
    rw [ha]
    exact (canonical32945 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2403 + difference 1 2) (sourceB2403 + difference 2 1) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2403 + difference 1 2) (sourceB2403 + difference 2 1) sourceC2403) = raw24711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24711; decide +kernel
    rw [ha]
    exact (canonical24711 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2403 + difference 1 3) (sourceB2403 + difference 3 1) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA2403 + difference 1 3) (sourceB2403 + difference 3 1) sourceC2403) = raw24712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24712; decide +kernel
    rw [ha]
    exact (canonical24712 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2403 + difference 1 4) (sourceB2403 + difference 4 1) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA2403 + difference 1 4) (sourceB2403 + difference 4 1) sourceC2403) = raw24713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24713; decide +kernel
    rw [ha]
    exact (canonical24713 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2403 + difference 1 5) (sourceB2403 + difference 5 1) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA2403 + difference 1 5) (sourceB2403 + difference 5 1) sourceC2403) = raw24714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24714; decide +kernel
    rw [ha]
    exact (canonical24714 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2403 + difference 2 0) (sourceB2403 + difference 0 2) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3259) := by
    have ha : (tripleCharges (sourceA2403 + difference 2 0) (sourceB2403 + difference 0 2) sourceC2403) = raw24721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24721; decide +kernel
    rw [ha]
    exact (canonical24721 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2403 + difference 2 1) (sourceB2403 + difference 1 2) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3553) := by
    have ha : (tripleCharges (sourceA2403 + difference 2 1) (sourceB2403 + difference 1 2) sourceC2403) = raw32946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32946; decide +kernel
    rw [ha]
    exact (canonical32946 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2403 + difference 2 3) (sourceB2403 + difference 3 2) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA2403 + difference 2 3) (sourceB2403 + difference 3 2) sourceC2403) = raw32947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32947; decide +kernel
    rw [ha]
    exact (canonical32947 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2403 + difference 2 4) (sourceB2403 + difference 4 2) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2403 + difference 2 4) (sourceB2403 + difference 4 2) sourceC2403) = raw32948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32948; decide +kernel
    rw [ha]
    exact (canonical32948 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2403 + difference 2 5) (sourceB2403 + difference 5 2) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA2403 + difference 2 5) (sourceB2403 + difference 5 2) sourceC2403) = raw32949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32949; decide +kernel
    rw [ha]
    exact (canonical32949 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2403 + difference 3 0) (sourceB2403 + difference 0 3) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3267) := by
    have ha : (tripleCharges (sourceA2403 + difference 3 0) (sourceB2403 + difference 0 3) sourceC2403) = raw24726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24726; decide +kernel
    rw [ha]
    exact (canonical24726 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2403 + difference 3 1) (sourceB2403 + difference 1 3) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2403 + difference 3 1) (sourceB2403 + difference 1 3) sourceC2403) = raw32950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32950; decide +kernel
    rw [ha]
    exact (canonical32950 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2403 + difference 3 2) (sourceB2403 + difference 2 3) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3450) := by
    have ha : (tripleCharges (sourceA2403 + difference 3 2) (sourceB2403 + difference 2 3) sourceC2403) = raw32951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32951; decide +kernel
    rw [ha]
    exact (canonical32951 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2403 + difference 3 4) (sourceB2403 + difference 4 3) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2403 + difference 3 4) (sourceB2403 + difference 4 3) sourceC2403) = raw32952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32952; decide +kernel
    rw [ha]
    exact (canonical32952 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2403 + difference 3 5) (sourceB2403 + difference 5 3) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA2403 + difference 3 5) (sourceB2403 + difference 5 3) sourceC2403) = raw32953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32953; decide +kernel
    rw [ha]
    exact (canonical32953 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2403 + difference 4 0) (sourceB2403 + difference 0 4) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3258) := by
    have ha : (tripleCharges (sourceA2403 + difference 4 0) (sourceB2403 + difference 0 4) sourceC2403) = raw24731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24731; decide +kernel
    rw [ha]
    exact (canonical24731 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2403 + difference 4 1) (sourceB2403 + difference 1 4) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3509) := by
    have ha : (tripleCharges (sourceA2403 + difference 4 1) (sourceB2403 + difference 1 4) sourceC2403) = raw32954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32954; decide +kernel
    rw [ha]
    exact (canonical32954 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2403 + difference 4 2) (sourceB2403 + difference 2 4) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3453) := by
    have ha : (tripleCharges (sourceA2403 + difference 4 2) (sourceB2403 + difference 2 4) sourceC2403) = raw32955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32955; decide +kernel
    rw [ha]
    exact (canonical32955 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2403 + difference 4 3) (sourceB2403 + difference 3 4) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2403 + difference 4 3) (sourceB2403 + difference 3 4) sourceC2403) = raw32956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32956; decide +kernel
    rw [ha]
    exact (canonical32956 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2403 + difference 4 5) (sourceB2403 + difference 5 4) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA2403 + difference 4 5) (sourceB2403 + difference 5 4) sourceC2403) = raw32957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32957; decide +kernel
    rw [ha]
    exact (canonical32957 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2403 + difference 5 0) (sourceB2403 + difference 0 5) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA2403 + difference 5 0) (sourceB2403 + difference 0 5) sourceC2403) = raw24736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24736; decide +kernel
    rw [ha]
    exact (canonical24736 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2403 + difference 5 1) (sourceB2403 + difference 1 5) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3452) := by
    have ha : (tripleCharges (sourceA2403 + difference 5 1) (sourceB2403 + difference 1 5) sourceC2403) = raw32958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32958; decide +kernel
    rw [ha]
    exact (canonical32958 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2403 + difference 5 2) (sourceB2403 + difference 2 5) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3449) := by
    have ha : (tripleCharges (sourceA2403 + difference 5 2) (sourceB2403 + difference 2 5) sourceC2403) = raw32959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32959; decide +kernel
    rw [ha]
    exact (canonical32959 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2403 + difference 5 3) (sourceB2403 + difference 3 5) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA2403 + difference 5 3) (sourceB2403 + difference 3 5) sourceC2403) = raw32960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32960; decide +kernel
    rw [ha]
    exact (canonical32960 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2403 + difference 5 4) (sourceB2403 + difference 4 5) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2403 + difference 5 4) (sourceB2403 + difference 4 5) sourceC2403) = raw32961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32961; decide +kernel
    rw [ha]
    exact (canonical32961 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2403 sourceB2403 sourceC2403
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2403, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1950 : Integer.Sparse.reindex keyMap MixedData.row1950 = numericRow1950 := by decide +kernel

theorem numericCheck1950 (x : Master → ℝ) : Integer.Sparse.eval numericRow1950 x =
    (1 : ℝ) * reducedSource1950 x := by
  norm_num [numericRow1950, reducedSource1950, Integer.Sparse.eval, Sparse.eval, nodeValue3258, nodeValue3259, nodeValue3260, nodeValue3267, nodeValue3293, nodeValue3449, nodeValue3450, nodeValue3452, nodeValue3453, nodeValue3468, nodeValue3470, nodeValue3508, nodeValue3509, nodeValue3513, nodeValue3515, nodeValue3516, nodeValue3517, nodeValue3522, nodeValue3533, nodeValue3534, nodeValue3547, nodeValue3553, nodeValue3557, nodeValue3558, nodeValue3564, nodeValue3793, nodeValue3795, nodeValue3807, nodeValue3837, nodeValue3838]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1950 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1950 (mixedVector B) = 0 := by
  have h3258 : mixedVector B (Sum.inr 3258) = Sparse.eval nodeValue3258 (mixedVector B) := by
    change mixedMoment B node3258 node3258Labels = _
    exact sound3258 B hB hF
  have h3259 : mixedVector B (Sum.inr 3259) = Sparse.eval nodeValue3259 (mixedVector B) := by
    change mixedMoment B node3259 node3259Labels = _
    exact sound3259 B hB hF
  have h3260 : mixedVector B (Sum.inr 3260) = Sparse.eval nodeValue3260 (mixedVector B) := by
    change mixedMoment B node3260 node3260Labels = _
    exact sound3260 B hB hF
  have h3267 : mixedVector B (Sum.inr 3267) = Sparse.eval nodeValue3267 (mixedVector B) := by
    change mixedMoment B node3267 node3267Labels = _
    exact sound3267 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3449 : mixedVector B (Sum.inr 3449) = Sparse.eval nodeValue3449 (mixedVector B) := by
    change mixedMoment B node3449 node3449Labels = _
    exact sound3449 B hB hF
  have h3450 : mixedVector B (Sum.inr 3450) = Sparse.eval nodeValue3450 (mixedVector B) := by
    change mixedMoment B node3450 node3450Labels = _
    exact sound3450 B hB hF
  have h3452 : mixedVector B (Sum.inr 3452) = Sparse.eval nodeValue3452 (mixedVector B) := by
    change mixedMoment B node3452 node3452Labels = _
    exact sound3452 B hB hF
  have h3453 : mixedVector B (Sum.inr 3453) = Sparse.eval nodeValue3453 (mixedVector B) := by
    change mixedMoment B node3453 node3453Labels = _
    exact sound3453 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3470 : mixedVector B (Sum.inr 3470) = Sparse.eval nodeValue3470 (mixedVector B) := by
    change mixedMoment B node3470 node3470Labels = _
    exact sound3470 B hB hF
  have h3508 : mixedVector B (Sum.inr 3508) = Sparse.eval nodeValue3508 (mixedVector B) := by
    change mixedMoment B node3508 node3508Labels = _
    exact sound3508 B hB hF
  have h3509 : mixedVector B (Sum.inr 3509) = Sparse.eval nodeValue3509 (mixedVector B) := by
    change mixedMoment B node3509 node3509Labels = _
    exact sound3509 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3515 : mixedVector B (Sum.inr 3515) = Sparse.eval nodeValue3515 (mixedVector B) := by
    change mixedMoment B node3515 node3515Labels = _
    exact sound3515 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3553 : mixedVector B (Sum.inr 3553) = Sparse.eval nodeValue3553 (mixedVector B) := by
    change mixedMoment B node3553 node3553Labels = _
    exact sound3553 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h3793 : mixedVector B (Sum.inr 3793) = Sparse.eval nodeValue3793 (mixedVector B) := by
    change mixedMoment B node3793 node3793Labels = _
    exact sound3793 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  simpa only [sourceForm2403, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3258, h3259, h3260, h3267, h3293, h3449, h3450, h3452, h3453, h3468, h3470, h3508, h3509, h3513, h3515, h3516, h3517, h3522, h3533, h3534, h3547, h3553, h3557, h3558, h3564, h3793, h3795, h3807, h3837, h3838, reducedSource1950] using sourceEq2403 B hB

theorem rowSound1950_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1950 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1950, numericCheck1950, reducedZero1950 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e_oai
