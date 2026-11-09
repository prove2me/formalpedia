-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2089_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:03:55.780202+00:00
-- url     : https://prove2.me/submissions/6c3fb9d6-5603-4d51-8c70-92648b0498b5

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical286
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36617 raw36617Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw36617 raw36617Labels = mixedMoment B raw36617step0 raw36617step0Labels := by
      have hz : ∀ j, raw36617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36617step0 = (fun i j => raw36617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36617step0 raw36617; decide +kernel
      have hl : raw36617step0Labels = raw36617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36617 raw36617Labels permutation346 hz
    mixedMoment B raw36617step0 raw36617step0Labels = mixedMoment B raw36617step1 raw36617step1Labels := by
      have ha : raw36617step1 = (fun i j => raw36617step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36617step1 raw36617step0; decide +kernel
      have hl : raw36617step1Labels = raw36617step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36617step0 raw36617step0Labels permutation61 permutation7
    mixedMoment B raw36617step1 raw36617step1Labels = mixedMoment B raw36617step2 raw36617step2Labels := by
      have ha : raw36617step2 = -raw36617step1 := by apply Matrix.ext; change ∀ i j, raw36617step2 i j = -(raw36617step1 i j); unfold raw36617step2 raw36617step1; decide +kernel
      have hl : raw36617step2Labels = raw36617step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36617step2 raw36617step2Labels = mixedMoment B raw36617step3 raw36617step3Labels := by
      have ha : raw36617step3 = raw36617step2 := by apply Matrix.ext; unfold raw36617step3 raw36617step2; decide +kernel
      have hl : raw36617step2Labels = labelEmbedding1 ∘ raw36617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36617step2 raw36617step2Labels raw36617step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

theorem canonical36618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36618 raw36618Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw36618 raw36618Labels = mixedMoment B raw36618step0 raw36618step0Labels := by
      have ha : raw36618step0 = (fun i j => raw36618 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36618step0 raw36618; decide +kernel
      have hl : raw36618step0Labels = raw36618Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36618 raw36618Labels permutation270 permutation7
    mixedMoment B raw36618step0 raw36618step0Labels = mixedMoment B raw36618step1 raw36618step1Labels := by
      have ha : raw36618step1 = -raw36618step0 := by apply Matrix.ext; change ∀ i j, raw36618step1 i j = -(raw36618step0 i j); unfold raw36618step1 raw36618step0; decide +kernel
      have hl : raw36618step1Labels = raw36618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36618step1 raw36618step1Labels = mixedMoment B raw36618step2 raw36618step2Labels := by
      have ha : raw36618step2 = raw36618step1 := by apply Matrix.ext; unfold raw36618step2 raw36618step1; decide +kernel
      have hl : raw36618step1Labels = labelEmbedding1 ∘ raw36618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36618step1 raw36618step1Labels raw36618step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3796 node3796Labels := by rfl

theorem canonical36619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36619 raw36619Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw36619 raw36619Labels = mixedMoment B raw36619step0 raw36619step0Labels := by
      have hz : ∀ j, raw36619 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36619step0 = (fun i j => raw36619 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36619step0 raw36619; decide +kernel
      have hl : raw36619step0Labels = raw36619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36619 raw36619Labels permutation346 hz
    mixedMoment B raw36619step0 raw36619step0Labels = mixedMoment B raw36619step1 raw36619step1Labels := by
      have ha : raw36619step1 = (fun i j => raw36619step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36619step1 raw36619step0; decide +kernel
      have hl : raw36619step1Labels = raw36619step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36619step0 raw36619step0Labels permutation61 permutation7
    mixedMoment B raw36619step1 raw36619step1Labels = mixedMoment B raw36619step2 raw36619step2Labels := by
      have ha : raw36619step2 = -raw36619step1 := by apply Matrix.ext; change ∀ i j, raw36619step2 i j = -(raw36619step1 i j); unfold raw36619step2 raw36619step1; decide +kernel
      have hl : raw36619step2Labels = raw36619step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36619step2 raw36619step2Labels = mixedMoment B raw36619step3 raw36619step3Labels := by
      have ha : raw36619step3 = raw36619step2 := by apply Matrix.ext; unfold raw36619step3 raw36619step2; decide +kernel
      have hl : raw36619step2Labels = labelEmbedding1 ∘ raw36619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36619step2 raw36619step2Labels raw36619step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical36620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36620 raw36620Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw36620 raw36620Labels = mixedMoment B raw36620step0 raw36620step0Labels := by
      have hz : ∀ j, raw36620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36620step0 = (fun i j => raw36620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36620step0 raw36620; decide +kernel
      have hl : raw36620step0Labels = raw36620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36620 raw36620Labels permutation346 hz
    mixedMoment B raw36620step0 raw36620step0Labels = mixedMoment B raw36620step1 raw36620step1Labels := by
      have ha : raw36620step1 = (fun i j => raw36620step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36620step1 raw36620step0; decide +kernel
      have hl : raw36620step1Labels = raw36620step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36620step0 raw36620step0Labels permutation61 permutation7
    mixedMoment B raw36620step1 raw36620step1Labels = mixedMoment B raw36620step2 raw36620step2Labels := by
      have ha : raw36620step2 = -raw36620step1 := by apply Matrix.ext; change ∀ i j, raw36620step2 i j = -(raw36620step1 i j); unfold raw36620step2 raw36620step1; decide +kernel
      have hl : raw36620step2Labels = raw36620step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36620step2 raw36620step2Labels = mixedMoment B raw36620step3 raw36620step3Labels := by
      have ha : raw36620step3 = raw36620step2 := by apply Matrix.ext; unfold raw36620step3 raw36620step2; decide +kernel
      have hl : raw36620step2Labels = labelEmbedding1 ∘ raw36620step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36620step2 raw36620step2Labels raw36620step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical36621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36621 raw36621Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw36621 raw36621Labels = mixedMoment B raw36621step0 raw36621step0Labels := by
      have hz : ∀ j, raw36621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36621step0 = (fun i j => raw36621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36621step0 raw36621; decide +kernel
      have hl : raw36621step0Labels = raw36621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36621 raw36621Labels permutation346 hz
    mixedMoment B raw36621step0 raw36621step0Labels = mixedMoment B raw36621step1 raw36621step1Labels := by
      have ha : raw36621step1 = (fun i j => raw36621step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36621step1 raw36621step0; decide +kernel
      have hl : raw36621step1Labels = raw36621step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36621step0 raw36621step0Labels permutation61 permutation7
    mixedMoment B raw36621step1 raw36621step1Labels = mixedMoment B raw36621step2 raw36621step2Labels := by
      have ha : raw36621step2 = -raw36621step1 := by apply Matrix.ext; change ∀ i j, raw36621step2 i j = -(raw36621step1 i j); unfold raw36621step2 raw36621step1; decide +kernel
      have hl : raw36621step2Labels = raw36621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36621step2 raw36621step2Labels = mixedMoment B raw36621step3 raw36621step3Labels := by
      have ha : raw36621step3 = raw36621step2 := by apply Matrix.ext; unfold raw36621step3 raw36621step2; decide +kernel
      have hl : raw36621step2Labels = labelEmbedding1 ∘ raw36621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36621step2 raw36621step2Labels raw36621step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical36622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36622 raw36622Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw36622 raw36622Labels = mixedMoment B raw36622step0 raw36622step0Labels := by
      have hz : ∀ j, raw36622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36622step0 = (fun i j => raw36622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36622step0 raw36622; decide +kernel
      have hl : raw36622step0Labels = raw36622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36622 raw36622Labels permutation346 hz
    mixedMoment B raw36622step0 raw36622step0Labels = mixedMoment B raw36622step1 raw36622step1Labels := by
      have ha : raw36622step1 = (fun i j => raw36622step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36622step1 raw36622step0; decide +kernel
      have hl : raw36622step1Labels = raw36622step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36622step0 raw36622step0Labels permutation40 permutation5
    mixedMoment B raw36622step1 raw36622step1Labels = mixedMoment B raw36622step2 raw36622step2Labels := by
      have ha : raw36622step2 = -raw36622step1 := by apply Matrix.ext; change ∀ i j, raw36622step2 i j = -(raw36622step1 i j); unfold raw36622step2 raw36622step1; decide +kernel
      have hl : raw36622step2Labels = raw36622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36622step2 raw36622step2Labels = mixedMoment B raw36622step3 raw36622step3Labels := by
      have ha : raw36622step3 = raw36622step2 := by apply Matrix.ext; unfold raw36622step3 raw36622step2; decide +kernel
      have hl : raw36622step2Labels = labelEmbedding1 ∘ raw36622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36622step2 raw36622step2Labels raw36622step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

theorem canonical36623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36623 raw36623Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw36623 raw36623Labels = mixedMoment B raw36623step0 raw36623step0Labels := by
      have ha : raw36623step0 = (fun i j => raw36623 (permutation622 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36623step0 raw36623; decide +kernel
      have hl : raw36623step0Labels = raw36623Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36623 raw36623Labels permutation622 permutation5
    mixedMoment B raw36623step0 raw36623step0Labels = mixedMoment B raw36623step1 raw36623step1Labels := by
      have ha : raw36623step1 = raw36623step0 := by apply Matrix.ext; unfold raw36623step1 raw36623step0; decide +kernel
      have hl : raw36623step0Labels = labelEmbedding1 ∘ raw36623step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36623step0 raw36623step0Labels raw36623step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

theorem canonical36624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36624 raw36624Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw36624 raw36624Labels = mixedMoment B raw36624step0 raw36624step0Labels := by
      have hz : ∀ j, raw36624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36624step0 = (fun i j => raw36624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36624step0 raw36624; decide +kernel
      have hl : raw36624step0Labels = raw36624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36624 raw36624Labels permutation346 hz
    mixedMoment B raw36624step0 raw36624step0Labels = mixedMoment B raw36624step1 raw36624step1Labels := by
      have ha : raw36624step1 = (fun i j => raw36624step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36624step1 raw36624step0; decide +kernel
      have hl : raw36624step1Labels = raw36624step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36624step0 raw36624step0Labels permutation138 permutation5
    mixedMoment B raw36624step1 raw36624step1Labels = mixedMoment B raw36624step2 raw36624step2Labels := by
      have ha : raw36624step2 = raw36624step1 := by apply Matrix.ext; unfold raw36624step2 raw36624step1; decide +kernel
      have hl : raw36624step1Labels = labelEmbedding1 ∘ raw36624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36624step1 raw36624step1Labels raw36624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

theorem canonical36625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36625 raw36625Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw36625 raw36625Labels = mixedMoment B raw36625step0 raw36625step0Labels := by
      have hz : ∀ j, raw36625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36625step0 = (fun i j => raw36625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36625step0 raw36625; decide +kernel
      have hl : raw36625step0Labels = raw36625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36625 raw36625Labels permutation346 hz
    mixedMoment B raw36625step0 raw36625step0Labels = mixedMoment B raw36625step1 raw36625step1Labels := by
      have ha : raw36625step1 = (fun i j => raw36625step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36625step1 raw36625step0; decide +kernel
      have hl : raw36625step1Labels = raw36625step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36625step0 raw36625step0Labels permutation137 permutation5
    mixedMoment B raw36625step1 raw36625step1Labels = mixedMoment B raw36625step2 raw36625step2Labels := by
      have ha : raw36625step2 = raw36625step1 := by apply Matrix.ext; unfold raw36625step2 raw36625step1; decide +kernel
      have hl : raw36625step1Labels = labelEmbedding1 ∘ raw36625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36625step1 raw36625step1Labels raw36625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical36626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36626 raw36626Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw36626 raw36626Labels = mixedMoment B raw36626step0 raw36626step0Labels := by
      have hz : ∀ j, raw36626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36626step0 = (fun i j => raw36626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36626step0 raw36626; decide +kernel
      have hl : raw36626step0Labels = raw36626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36626 raw36626Labels permutation346 hz
    mixedMoment B raw36626step0 raw36626step0Labels = mixedMoment B raw36626step1 raw36626step1Labels := by
      have ha : raw36626step1 = (fun i j => raw36626step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36626step1 raw36626step0; decide +kernel
      have hl : raw36626step1Labels = raw36626step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36626step0 raw36626step0Labels permutation61 permutation7
    mixedMoment B raw36626step1 raw36626step1Labels = mixedMoment B raw36626step2 raw36626step2Labels := by
      have ha : raw36626step2 = -raw36626step1 := by apply Matrix.ext; change ∀ i j, raw36626step2 i j = -(raw36626step1 i j); unfold raw36626step2 raw36626step1; decide +kernel
      have hl : raw36626step2Labels = raw36626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36626step2 raw36626step2Labels = mixedMoment B raw36626step3 raw36626step3Labels := by
      have ha : raw36626step3 = raw36626step2 := by apply Matrix.ext; unfold raw36626step3 raw36626step2; decide +kernel
      have hl : raw36626step2Labels = labelEmbedding1 ∘ raw36626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36626step2 raw36626step2Labels raw36626step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical36627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36627 raw36627Labels = mixedMoment B node3553 node3553Labels := by
  calc
    mixedMoment B raw36627 raw36627Labels = mixedMoment B raw36627step0 raw36627step0Labels := by
      have ha : raw36627step0 = (fun i j => raw36627 (permutation202 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36627step0 raw36627; decide +kernel
      have hl : raw36627step0Labels = raw36627Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36627 raw36627Labels permutation202 permutation5
    mixedMoment B raw36627step0 raw36627step0Labels = mixedMoment B raw36627step1 raw36627step1Labels := by
      have ha : raw36627step1 = -raw36627step0 := by apply Matrix.ext; change ∀ i j, raw36627step1 i j = -(raw36627step0 i j); unfold raw36627step1 raw36627step0; decide +kernel
      have hl : raw36627step1Labels = raw36627step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36627step1 raw36627step1Labels = mixedMoment B raw36627step2 raw36627step2Labels := by
      have ha : raw36627step2 = raw36627step1 := by apply Matrix.ext; unfold raw36627step2 raw36627step1; decide +kernel
      have hl : raw36627step1Labels = labelEmbedding1 ∘ raw36627step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36627step1 raw36627step1Labels raw36627step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3553 node3553Labels := by rfl

theorem canonical36628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36628 raw36628Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw36628 raw36628Labels = mixedMoment B raw36628step0 raw36628step0Labels := by
      have ha : raw36628step0 = (fun i j => raw36628 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36628step0 raw36628; decide +kernel
      have hl : raw36628step0Labels = raw36628Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36628 raw36628Labels permutation270 permutation7
    mixedMoment B raw36628step0 raw36628step0Labels = mixedMoment B raw36628step1 raw36628step1Labels := by
      have ha : raw36628step1 = -raw36628step0 := by apply Matrix.ext; change ∀ i j, raw36628step1 i j = -(raw36628step0 i j); unfold raw36628step1 raw36628step0; decide +kernel
      have hl : raw36628step1Labels = raw36628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36628step1 raw36628step1Labels = mixedMoment B raw36628step2 raw36628step2Labels := by
      have ha : raw36628step2 = raw36628step1 := by apply Matrix.ext; unfold raw36628step2 raw36628step1; decide +kernel
      have hl : raw36628step1Labels = labelEmbedding1 ∘ raw36628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36628step1 raw36628step1Labels raw36628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

theorem canonical36629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36629 raw36629Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw36629 raw36629Labels = mixedMoment B raw36629step0 raw36629step0Labels := by
      have ha : raw36629step0 = (fun i j => raw36629 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36629step0 raw36629; decide +kernel
      have hl : raw36629step0Labels = raw36629Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36629 raw36629Labels permutation270 permutation7
    mixedMoment B raw36629step0 raw36629step0Labels = mixedMoment B raw36629step1 raw36629step1Labels := by
      have ha : raw36629step1 = -raw36629step0 := by apply Matrix.ext; change ∀ i j, raw36629step1 i j = -(raw36629step0 i j); unfold raw36629step1 raw36629step0; decide +kernel
      have hl : raw36629step1Labels = raw36629step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36629step1 raw36629step1Labels = mixedMoment B raw36629step2 raw36629step2Labels := by
      have ha : raw36629step2 = raw36629step1 := by apply Matrix.ext; unfold raw36629step2 raw36629step1; decide +kernel
      have hl : raw36629step1Labels = labelEmbedding1 ∘ raw36629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36629step1 raw36629step1Labels raw36629step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

theorem canonical36630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36630 raw36630Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw36630 raw36630Labels = mixedMoment B raw36630step0 raw36630step0Labels := by
      have ha : raw36630step0 = (fun i j => raw36630 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36630step0 raw36630; decide +kernel
      have hl : raw36630step0Labels = raw36630Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36630 raw36630Labels permutation270 permutation7
    mixedMoment B raw36630step0 raw36630step0Labels = mixedMoment B raw36630step1 raw36630step1Labels := by
      have ha : raw36630step1 = -raw36630step0 := by apply Matrix.ext; change ∀ i j, raw36630step1 i j = -(raw36630step0 i j); unfold raw36630step1 raw36630step0; decide +kernel
      have hl : raw36630step1Labels = raw36630step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36630step1 raw36630step1Labels = mixedMoment B raw36630step2 raw36630step2Labels := by
      have ha : raw36630step2 = raw36630step1 := by apply Matrix.ext; unfold raw36630step2 raw36630step1; decide +kernel
      have hl : raw36630step1Labels = labelEmbedding1 ∘ raw36630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36630step1 raw36630step1Labels raw36630step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

theorem canonical36631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36631 raw36631Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw36631 raw36631Labels = mixedMoment B raw36631step0 raw36631step0Labels := by
      have ha : raw36631step0 = (fun i j => raw36631 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36631step0 raw36631; decide +kernel
      have hl : raw36631step0Labels = raw36631Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36631 raw36631Labels permutation270 permutation7
    mixedMoment B raw36631step0 raw36631step0Labels = mixedMoment B raw36631step1 raw36631step1Labels := by
      have ha : raw36631step1 = -raw36631step0 := by apply Matrix.ext; change ∀ i j, raw36631step1 i j = -(raw36631step0 i j); unfold raw36631step1 raw36631step0; decide +kernel
      have hl : raw36631step1Labels = raw36631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36631step1 raw36631step1Labels = mixedMoment B raw36631step2 raw36631step2Labels := by
      have ha : raw36631step2 = raw36631step1 := by apply Matrix.ext; unfold raw36631step2 raw36631step1; decide +kernel
      have hl : raw36631step1Labels = labelEmbedding1 ∘ raw36631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36631step1 raw36631step1Labels raw36631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

theorem canonical36632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36632 raw36632Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw36632 raw36632Labels = mixedMoment B raw36632step0 raw36632step0Labels := by
      have hz : ∀ j, raw36632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36632step0 = (fun i j => raw36632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36632step0 raw36632; decide +kernel
      have hl : raw36632step0Labels = raw36632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36632 raw36632Labels permutation346 hz
    mixedMoment B raw36632step0 raw36632step0Labels = mixedMoment B raw36632step1 raw36632step1Labels := by
      have ha : raw36632step1 = (fun i j => raw36632step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36632step1 raw36632step0; decide +kernel
      have hl : raw36632step1Labels = raw36632step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36632step0 raw36632step0Labels permutation34 permutation5
    mixedMoment B raw36632step1 raw36632step1Labels = mixedMoment B raw36632step2 raw36632step2Labels := by
      have ha : raw36632step2 = -raw36632step1 := by apply Matrix.ext; change ∀ i j, raw36632step2 i j = -(raw36632step1 i j); unfold raw36632step2 raw36632step1; decide +kernel
      have hl : raw36632step2Labels = raw36632step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36632step2 raw36632step2Labels = mixedMoment B raw36632step3 raw36632step3Labels := by
      have ha : raw36632step3 = raw36632step2 := by apply Matrix.ext; unfold raw36632step3 raw36632step2; decide +kernel
      have hl : raw36632step2Labels = labelEmbedding1 ∘ raw36632step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36632step2 raw36632step2Labels raw36632step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3591 node3591Labels := by rfl

theorem canonical36633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36633 raw36633Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw36633 raw36633Labels = mixedMoment B raw36633step0 raw36633step0Labels := by
      have hz : ∀ j, raw36633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36633step0 = (fun i j => raw36633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36633step0 raw36633; decide +kernel
      have hl : raw36633step0Labels = raw36633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36633 raw36633Labels permutation346 hz
    mixedMoment B raw36633step0 raw36633step0Labels = mixedMoment B raw36633step1 raw36633step1Labels := by
      have ha : raw36633step1 = (fun i j => raw36633step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36633step1 raw36633step0; decide +kernel
      have hl : raw36633step1Labels = raw36633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36633step0 raw36633step0Labels permutation61 permutation7
    mixedMoment B raw36633step1 raw36633step1Labels = mixedMoment B raw36633step2 raw36633step2Labels := by
      have ha : raw36633step2 = -raw36633step1 := by apply Matrix.ext; change ∀ i j, raw36633step2 i j = -(raw36633step1 i j); unfold raw36633step2 raw36633step1; decide +kernel
      have hl : raw36633step2Labels = raw36633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36633step2 raw36633step2Labels = mixedMoment B raw36633step3 raw36633step3Labels := by
      have ha : raw36633step3 = raw36633step2 := by apply Matrix.ext; unfold raw36633step3 raw36633step2; decide +kernel
      have hl : raw36633step2Labels = labelEmbedding1 ∘ raw36633step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36633step2 raw36633step2Labels raw36633step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3417 node3417Labels := by rfl

theorem canonical36634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36634 raw36634Labels = mixedMoment B node3754 node3754Labels := by
  calc
    mixedMoment B raw36634 raw36634Labels = mixedMoment B raw36634step0 raw36634step0Labels := by
      have ha : raw36634step0 = (fun i j => raw36634 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36634step0 raw36634; decide +kernel
      have hl : raw36634step0Labels = raw36634Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36634 raw36634Labels permutation270 permutation7
    mixedMoment B raw36634step0 raw36634step0Labels = mixedMoment B raw36634step1 raw36634step1Labels := by
      have ha : raw36634step1 = -raw36634step0 := by apply Matrix.ext; change ∀ i j, raw36634step1 i j = -(raw36634step0 i j); unfold raw36634step1 raw36634step0; decide +kernel
      have hl : raw36634step1Labels = raw36634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36634step1 raw36634step1Labels = mixedMoment B raw36634step2 raw36634step2Labels := by
      have ha : raw36634step2 = raw36634step1 := by apply Matrix.ext; unfold raw36634step2 raw36634step1; decide +kernel
      have hl : raw36634step1Labels = labelEmbedding1 ∘ raw36634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36634step1 raw36634step1Labels raw36634step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3754 node3754Labels := by rfl

theorem canonical36635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36635 raw36635Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw36635 raw36635Labels = mixedMoment B raw36635step0 raw36635step0Labels := by
      have hz : ∀ j, raw36635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36635step0 = (fun i j => raw36635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36635step0 raw36635; decide +kernel
      have hl : raw36635step0Labels = raw36635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36635 raw36635Labels permutation346 hz
    mixedMoment B raw36635step0 raw36635step0Labels = mixedMoment B raw36635step1 raw36635step1Labels := by
      have ha : raw36635step1 = (fun i j => raw36635step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36635step1 raw36635step0; decide +kernel
      have hl : raw36635step1Labels = raw36635step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36635step0 raw36635step0Labels permutation61 permutation7
    mixedMoment B raw36635step1 raw36635step1Labels = mixedMoment B raw36635step2 raw36635step2Labels := by
      have ha : raw36635step2 = -raw36635step1 := by apply Matrix.ext; change ∀ i j, raw36635step2 i j = -(raw36635step1 i j); unfold raw36635step2 raw36635step1; decide +kernel
      have hl : raw36635step2Labels = raw36635step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36635step2 raw36635step2Labels = mixedMoment B raw36635step3 raw36635step3Labels := by
      have ha : raw36635step3 = raw36635step2 := by apply Matrix.ext; unfold raw36635step3 raw36635step2; decide +kernel
      have hl : raw36635step2Labels = labelEmbedding1 ∘ raw36635step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36635step2 raw36635step2Labels raw36635step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

theorem canonical36636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36636 raw36636Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw36636 raw36636Labels = mixedMoment B raw36636step0 raw36636step0Labels := by
      have hz : ∀ j, raw36636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36636step0 = (fun i j => raw36636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36636step0 raw36636; decide +kernel
      have hl : raw36636step0Labels = raw36636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36636 raw36636Labels permutation346 hz
    mixedMoment B raw36636step0 raw36636step0Labels = mixedMoment B raw36636step1 raw36636step1Labels := by
      have ha : raw36636step1 = (fun i j => raw36636step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36636step1 raw36636step0; decide +kernel
      have hl : raw36636step1Labels = raw36636step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36636step0 raw36636step0Labels permutation61 permutation7
    mixedMoment B raw36636step1 raw36636step1Labels = mixedMoment B raw36636step2 raw36636step2Labels := by
      have ha : raw36636step2 = -raw36636step1 := by apply Matrix.ext; change ∀ i j, raw36636step2 i j = -(raw36636step1 i j); unfold raw36636step2 raw36636step1; decide +kernel
      have hl : raw36636step2Labels = raw36636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36636step2 raw36636step2Labels = mixedMoment B raw36636step3 raw36636step3Labels := by
      have ha : raw36636step3 = raw36636step2 := by apply Matrix.ext; unfold raw36636step3 raw36636step2; decide +kernel
      have hl : raw36636step2Labels = labelEmbedding1 ∘ raw36636step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36636step2 raw36636step2Labels raw36636step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical36637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36637 raw36637Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw36637 raw36637Labels = mixedMoment B raw36637step0 raw36637step0Labels := by
      have hz : ∀ j, raw36637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36637step0 = (fun i j => raw36637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36637step0 raw36637; decide +kernel
      have hl : raw36637step0Labels = raw36637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36637 raw36637Labels permutation346 hz
    mixedMoment B raw36637step0 raw36637step0Labels = mixedMoment B raw36637step1 raw36637step1Labels := by
      have ha : raw36637step1 = (fun i j => raw36637step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36637step1 raw36637step0; decide +kernel
      have hl : raw36637step1Labels = raw36637step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36637step0 raw36637step0Labels permutation38 permutation5
    mixedMoment B raw36637step1 raw36637step1Labels = mixedMoment B raw36637step2 raw36637step2Labels := by
      have ha : raw36637step2 = -raw36637step1 := by apply Matrix.ext; change ∀ i j, raw36637step2 i j = -(raw36637step1 i j); unfold raw36637step2 raw36637step1; decide +kernel
      have hl : raw36637step2Labels = raw36637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36637step2 raw36637step2Labels = mixedMoment B raw36637step3 raw36637step3Labels := by
      have ha : raw36637step3 = raw36637step2 := by apply Matrix.ext; unfold raw36637step3 raw36637step2; decide +kernel
      have hl : raw36637step2Labels = labelEmbedding1 ∘ raw36637step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36637step2 raw36637step2Labels raw36637step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

theorem canonical36638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36638 raw36638Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw36638 raw36638Labels = mixedMoment B raw36638step0 raw36638step0Labels := by
      have hz : ∀ j, raw36638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36638step0 = (fun i j => raw36638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36638step0 raw36638; decide +kernel
      have hl : raw36638step0Labels = raw36638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36638 raw36638Labels permutation346 hz
    mixedMoment B raw36638step0 raw36638step0Labels = mixedMoment B raw36638step1 raw36638step1Labels := by
      have ha : raw36638step1 = (fun i j => raw36638step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36638step1 raw36638step0; decide +kernel
      have hl : raw36638step1Labels = raw36638step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36638step0 raw36638step0Labels permutation61 permutation7
    mixedMoment B raw36638step1 raw36638step1Labels = mixedMoment B raw36638step2 raw36638step2Labels := by
      have ha : raw36638step2 = -raw36638step1 := by apply Matrix.ext; change ∀ i j, raw36638step2 i j = -(raw36638step1 i j); unfold raw36638step2 raw36638step1; decide +kernel
      have hl : raw36638step2Labels = raw36638step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36638step2 raw36638step2Labels = mixedMoment B raw36638step3 raw36638step3Labels := by
      have ha : raw36638step3 = raw36638step2 := by apply Matrix.ext; unfold raw36638step3 raw36638step2; decide +kernel
      have hl : raw36638step2Labels = labelEmbedding1 ∘ raw36638step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36638step2 raw36638step2Labels raw36638step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

theorem canonical36639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36639 raw36639Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw36639 raw36639Labels = mixedMoment B raw36639step0 raw36639step0Labels := by
      have ha : raw36639step0 = (fun i j => raw36639 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36639step0 raw36639; decide +kernel
      have hl : raw36639step0Labels = raw36639Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36639 raw36639Labels permutation270 permutation7
    mixedMoment B raw36639step0 raw36639step0Labels = mixedMoment B raw36639step1 raw36639step1Labels := by
      have ha : raw36639step1 = -raw36639step0 := by apply Matrix.ext; change ∀ i j, raw36639step1 i j = -(raw36639step0 i j); unfold raw36639step1 raw36639step0; decide +kernel
      have hl : raw36639step1Labels = raw36639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36639step1 raw36639step1Labels = mixedMoment B raw36639step2 raw36639step2Labels := by
      have ha : raw36639step2 = raw36639step1 := by apply Matrix.ext; unfold raw36639step2 raw36639step1; decide +kernel
      have hl : raw36639step1Labels = labelEmbedding1 ∘ raw36639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36639step1 raw36639step1Labels raw36639step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

theorem canonical36640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36640 raw36640Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw36640 raw36640Labels = mixedMoment B raw36640step0 raw36640step0Labels := by
      have hz : ∀ j, raw36640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36640step0 = (fun i j => raw36640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36640step0 raw36640; decide +kernel
      have hl : raw36640step0Labels = raw36640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36640 raw36640Labels permutation346 hz
    mixedMoment B raw36640step0 raw36640step0Labels = mixedMoment B raw36640step1 raw36640step1Labels := by
      have ha : raw36640step1 = (fun i j => raw36640step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36640step1 raw36640step0; decide +kernel
      have hl : raw36640step1Labels = raw36640step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36640step0 raw36640step0Labels permutation148 permutation5
    mixedMoment B raw36640step1 raw36640step1Labels = mixedMoment B raw36640step2 raw36640step2Labels := by
      have ha : raw36640step2 = raw36640step1 := by apply Matrix.ext; unfold raw36640step2 raw36640step1; decide +kernel
      have hl : raw36640step1Labels = labelEmbedding1 ∘ raw36640step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36640step1 raw36640step1Labels raw36640step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3772 node3772Labels := by rfl

theorem canonical36641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36641 raw36641Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw36641 raw36641Labels = mixedMoment B raw36641step0 raw36641step0Labels := by
      have hz : ∀ j, raw36641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36641step0 = (fun i j => raw36641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36641step0 raw36641; decide +kernel
      have hl : raw36641step0Labels = raw36641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36641 raw36641Labels permutation346 hz
    mixedMoment B raw36641step0 raw36641step0Labels = mixedMoment B raw36641step1 raw36641step1Labels := by
      have ha : raw36641step1 = (fun i j => raw36641step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36641step1 raw36641step0; decide +kernel
      have hl : raw36641step1Labels = raw36641step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36641step0 raw36641step0Labels permutation61 permutation7
    mixedMoment B raw36641step1 raw36641step1Labels = mixedMoment B raw36641step2 raw36641step2Labels := by
      have ha : raw36641step2 = -raw36641step1 := by apply Matrix.ext; change ∀ i j, raw36641step2 i j = -(raw36641step1 i j); unfold raw36641step2 raw36641step1; decide +kernel
      have hl : raw36641step2Labels = raw36641step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36641step2 raw36641step2Labels = mixedMoment B raw36641step3 raw36641step3Labels := by
      have ha : raw36641step3 = raw36641step2 := by apply Matrix.ext; unfold raw36641step3 raw36641step2; decide +kernel
      have hl : raw36641step2Labels = labelEmbedding1 ∘ raw36641step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36641step2 raw36641step2Labels raw36641step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

theorem canonical36642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36642 raw36642Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw36642 raw36642Labels = mixedMoment B raw36642step0 raw36642step0Labels := by
      have hz : ∀ j, raw36642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36642step0 = (fun i j => raw36642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36642step0 raw36642; decide +kernel
      have hl : raw36642step0Labels = raw36642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36642 raw36642Labels permutation346 hz
    mixedMoment B raw36642step0 raw36642step0Labels = mixedMoment B raw36642step1 raw36642step1Labels := by
      have ha : raw36642step1 = (fun i j => raw36642step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36642step1 raw36642step0; decide +kernel
      have hl : raw36642step1Labels = raw36642step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36642step0 raw36642step0Labels permutation149 permutation5
    mixedMoment B raw36642step1 raw36642step1Labels = mixedMoment B raw36642step2 raw36642step2Labels := by
      have ha : raw36642step2 = raw36642step1 := by apply Matrix.ext; unfold raw36642step2 raw36642step1; decide +kernel
      have hl : raw36642step1Labels = labelEmbedding1 ∘ raw36642step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36642step1 raw36642step1Labels raw36642step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

theorem canonical36643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36643 raw36643Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw36643 raw36643Labels = mixedMoment B raw36643step0 raw36643step0Labels := by
      have hz : ∀ j, raw36643 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36643step0 = (fun i j => raw36643 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36643step0 raw36643; decide +kernel
      have hl : raw36643step0Labels = raw36643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36643 raw36643Labels permutation346 hz
    mixedMoment B raw36643step0 raw36643step0Labels = mixedMoment B raw36643step1 raw36643step1Labels := by
      have ha : raw36643step1 = (fun i j => raw36643step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36643step1 raw36643step0; decide +kernel
      have hl : raw36643step1Labels = raw36643step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36643step0 raw36643step0Labels permutation150 permutation5
    mixedMoment B raw36643step1 raw36643step1Labels = mixedMoment B raw36643step2 raw36643step2Labels := by
      have ha : raw36643step2 = raw36643step1 := by apply Matrix.ext; unfold raw36643step2 raw36643step1; decide +kernel
      have hl : raw36643step1Labels = labelEmbedding1 ∘ raw36643step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36643step1 raw36643step1Labels raw36643step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical36644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36644 raw36644Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw36644 raw36644Labels = mixedMoment B raw36644step0 raw36644step0Labels := by
      have ha : raw36644step0 = (fun i j => raw36644 (permutation676 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36644step0 raw36644; decide +kernel
      have hl : raw36644step0Labels = raw36644Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36644 raw36644Labels permutation676 permutation5
    mixedMoment B raw36644step0 raw36644step0Labels = mixedMoment B raw36644step1 raw36644step1Labels := by
      have ha : raw36644step1 = raw36644step0 := by apply Matrix.ext; unfold raw36644step1 raw36644step0; decide +kernel
      have hl : raw36644step0Labels = labelEmbedding1 ∘ raw36644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36644step0 raw36644step0Labels raw36644step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

theorem canonical36645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36645 raw36645Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw36645 raw36645Labels = mixedMoment B raw36645step0 raw36645step0Labels := by
      have hz : ∀ j, raw36645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36645step0 = (fun i j => raw36645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36645step0 raw36645; decide +kernel
      have hl : raw36645step0Labels = raw36645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36645 raw36645Labels permutation346 hz
    mixedMoment B raw36645step0 raw36645step0Labels = mixedMoment B raw36645step1 raw36645step1Labels := by
      have ha : raw36645step1 = (fun i j => raw36645step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36645step1 raw36645step0; decide +kernel
      have hl : raw36645step1Labels = raw36645step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36645step0 raw36645step0Labels permutation148 permutation5
    mixedMoment B raw36645step1 raw36645step1Labels = mixedMoment B raw36645step2 raw36645step2Labels := by
      have ha : raw36645step2 = raw36645step1 := by apply Matrix.ext; unfold raw36645step2 raw36645step1; decide +kernel
      have hl : raw36645step1Labels = labelEmbedding1 ∘ raw36645step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36645step1 raw36645step1Labels raw36645step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

theorem canonical36646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36646 raw36646Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw36646 raw36646Labels = mixedMoment B raw36646step0 raw36646step0Labels := by
      have hz : ∀ j, raw36646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36646step0 = (fun i j => raw36646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36646step0 raw36646; decide +kernel
      have hl : raw36646step0Labels = raw36646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36646 raw36646Labels permutation346 hz
    mixedMoment B raw36646step0 raw36646step0Labels = mixedMoment B raw36646step1 raw36646step1Labels := by
      have ha : raw36646step1 = (fun i j => raw36646step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36646step1 raw36646step0; decide +kernel
      have hl : raw36646step1Labels = raw36646step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36646step0 raw36646step0Labels permutation137 permutation5
    mixedMoment B raw36646step1 raw36646step1Labels = mixedMoment B raw36646step2 raw36646step2Labels := by
      have ha : raw36646step2 = raw36646step1 := by apply Matrix.ext; unfold raw36646step2 raw36646step1; decide +kernel
      have hl : raw36646step1Labels = labelEmbedding1 ∘ raw36646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36646step1 raw36646step1Labels raw36646step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

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

theorem sound3814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3814 node3814Labels = Sparse.eval nodeValue3814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3814) = mixedMoment B node3814 node3814Labels := rfl
  simpa [nodeValue3814, Sparse.eval] using hc.symm

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

theorem sound2211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2211 node2211Labels = Sparse.eval nodeValue2211 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2211) = mixedMoment B node2211 node2211Labels := rfl
  simpa [nodeValue2211, Sparse.eval] using hc.symm

theorem sound2212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2212 node2212Labels = Sparse.eval nodeValue2212 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2212) = mixedMoment B node2212 node2212Labels := rfl
  simpa [nodeValue2212, Sparse.eval] using hc.symm

theorem sound2217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2217 node2217Labels = Sparse.eval nodeValue2217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2217) = mixedMoment B node2217 node2217Labels := rfl
  simpa [nodeValue2217, Sparse.eval] using hc.symm

theorem sound2223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2223 node2223Labels = Sparse.eval nodeValue2223 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2223) = mixedMoment B node2223 node2223Labels := rfl
  simpa [nodeValue2223, Sparse.eval] using hc.symm

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

theorem sound2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2274 node2274Labels = Sparse.eval nodeValue2274 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2274) = mixedMoment B node2274 node2274Labels := rfl
  simpa [nodeValue2274, Sparse.eval] using hc.symm

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

theorem sound3417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3417 node3417Labels = Sparse.eval nodeValue3417 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3417) = mixedMoment B node3417 node3417Labels := rfl
  simpa [nodeValue3417, Sparse.eval] using hc.symm

theorem sound3418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3418 node3418Labels = Sparse.eval nodeValue3418 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3418) = mixedMoment B node3418 node3418Labels := rfl
  simpa [nodeValue3418, Sparse.eval] using hc.symm

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

theorem sound3479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3479 node3479Labels = Sparse.eval nodeValue3479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3479) = mixedMoment B node3479 node3479Labels := rfl
  simpa [nodeValue3479, Sparse.eval] using hc.symm

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

theorem sound3553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3553 node3553Labels = Sparse.eval nodeValue3553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3553) = mixedMoment B node3553 node3553Labels := rfl
  simpa [nodeValue3553, Sparse.eval] using hc.symm

theorem sound3555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3555 node3555Labels = Sparse.eval nodeValue3555 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3555) = mixedMoment B node3555 node3555Labels := rfl
  simpa [nodeValue3555, Sparse.eval] using hc.symm

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

theorem sound3591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3591 node3591Labels = Sparse.eval nodeValue3591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3591) = mixedMoment B node3591 node3591Labels := rfl
  simpa [nodeValue3591, Sparse.eval] using hc.symm

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

theorem sound3755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3755 node3755Labels = Sparse.eval nodeValue3755 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3755) = mixedMoment B node3755 node3755Labels := rfl
  simpa [nodeValue3755, Sparse.eval] using hc.symm

theorem sound3758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3758 node3758Labels = Sparse.eval nodeValue3758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3758) = mixedMoment B node3758 node3758Labels := rfl
  simpa [nodeValue3758, Sparse.eval] using hc.symm

theorem sound3761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3761 node3761Labels = Sparse.eval nodeValue3761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3761) = mixedMoment B node3761 node3761Labels := rfl
  simpa [nodeValue3761, Sparse.eval] using hc.symm

theorem sound3762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3762 node3762Labels = Sparse.eval nodeValue3762 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3762) = mixedMoment B node3762 node3762Labels := rfl
  simpa [nodeValue3762, Sparse.eval] using hc.symm

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

theorem sound3772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3772 node3772Labels = Sparse.eval nodeValue3772 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3772) = mixedMoment B node3772 node3772Labels := rfl
  simpa [nodeValue3772, Sparse.eval] using hc.symm

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

theorem zero3808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = 0 := by
  exact mixedMoment_order_one B hB node3808 node3808Labels 1
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

theorem sound3796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3796 node3796Labels = Sparse.eval nodeValue3796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3796) = mixedMoment B node3796 node3796Labels := rfl
  simpa [nodeValue3796, Sparse.eval] using hc.symm

theorem sound3808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = Sparse.eval nodeValue3808 (mixedVector B) := by
  simpa only [nodeValue3808, Sparse.eval_nil] using zero3808 B _hB _hF

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

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

theorem sound3873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3873 node3873Labels = Sparse.eval nodeValue3873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3873) = mixedMoment B node3873 node3873Labels := rfl
  simpa [nodeValue3873, Sparse.eval] using hc.symm

theorem sound3877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3877 node3877Labels = Sparse.eval nodeValue3877 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3877) = mixedMoment B node3877 node3877Labels := rfl
  simpa [nodeValue3877, Sparse.eval] using hc.symm

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

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

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

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

theorem sourceEq2622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2622 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2622 + difference 0 1) (sourceB2622 + difference 1 0) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA2622 + difference 0 1) (sourceB2622 + difference 1 0) sourceC2622) = raw36617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36617; decide +kernel
    rw [ha]
    exact (canonical36617 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2622 + difference 0 2) (sourceB2622 + difference 2 0) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA2622 + difference 0 2) (sourceB2622 + difference 2 0) sourceC2622) = raw36618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36618; decide +kernel
    rw [ha]
    exact (canonical36618 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2622 + difference 0 3) (sourceB2622 + difference 3 0) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA2622 + difference 0 3) (sourceB2622 + difference 3 0) sourceC2622) = raw36619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36619; decide +kernel
    rw [ha]
    exact (canonical36619 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2622 + difference 0 4) (sourceB2622 + difference 4 0) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2622 + difference 0 4) (sourceB2622 + difference 4 0) sourceC2622) = raw36620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36620; decide +kernel
    rw [ha]
    exact (canonical36620 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2622 + difference 0 5) (sourceB2622 + difference 5 0) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA2622 + difference 0 5) (sourceB2622 + difference 5 0) sourceC2622) = raw36621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36621; decide +kernel
    rw [ha]
    exact (canonical36621 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2622 + difference 1 0) (sourceB2622 + difference 0 1) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA2622 + difference 1 0) (sourceB2622 + difference 0 1) sourceC2622) = raw36622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36622; decide +kernel
    rw [ha]
    exact (canonical36622 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2622 + difference 1 2) (sourceB2622 + difference 2 1) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA2622 + difference 1 2) (sourceB2622 + difference 2 1) sourceC2622) = raw36623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36623; decide +kernel
    rw [ha]
    exact (canonical36623 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2622 + difference 1 3) (sourceB2622 + difference 3 1) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA2622 + difference 1 3) (sourceB2622 + difference 3 1) sourceC2622) = raw36624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36624; decide +kernel
    rw [ha]
    exact (canonical36624 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2622 + difference 1 4) (sourceB2622 + difference 4 1) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA2622 + difference 1 4) (sourceB2622 + difference 4 1) sourceC2622) = raw36625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36625; decide +kernel
    rw [ha]
    exact (canonical36625 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2622 + difference 1 5) (sourceB2622 + difference 5 1) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA2622 + difference 1 5) (sourceB2622 + difference 5 1) sourceC2622) = raw36626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36626; decide +kernel
    rw [ha]
    exact (canonical36626 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2622 + difference 2 0) (sourceB2622 + difference 0 2) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3553) := by
    have ha : (tripleCharges (sourceA2622 + difference 2 0) (sourceB2622 + difference 0 2) sourceC2622) = raw36627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36627; decide +kernel
    rw [ha]
    exact (canonical36627 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2622 + difference 2 1) (sourceB2622 + difference 1 2) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2622 + difference 2 1) (sourceB2622 + difference 1 2) sourceC2622) = raw36628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36628; decide +kernel
    rw [ha]
    exact (canonical36628 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2622 + difference 2 3) (sourceB2622 + difference 3 2) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA2622 + difference 2 3) (sourceB2622 + difference 3 2) sourceC2622) = raw36629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36629; decide +kernel
    rw [ha]
    exact (canonical36629 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2622 + difference 2 4) (sourceB2622 + difference 4 2) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2622 + difference 2 4) (sourceB2622 + difference 4 2) sourceC2622) = raw36630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36630; decide +kernel
    rw [ha]
    exact (canonical36630 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2622 + difference 2 5) (sourceB2622 + difference 5 2) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA2622 + difference 2 5) (sourceB2622 + difference 5 2) sourceC2622) = raw36631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36631; decide +kernel
    rw [ha]
    exact (canonical36631 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2622 + difference 3 0) (sourceB2622 + difference 0 3) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3591) := by
    have ha : (tripleCharges (sourceA2622 + difference 3 0) (sourceB2622 + difference 0 3) sourceC2622) = raw36632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36632; decide +kernel
    rw [ha]
    exact (canonical36632 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2622 + difference 3 1) (sourceB2622 + difference 1 3) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3417) := by
    have ha : (tripleCharges (sourceA2622 + difference 3 1) (sourceB2622 + difference 1 3) sourceC2622) = raw36633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36633; decide +kernel
    rw [ha]
    exact (canonical36633 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2622 + difference 3 2) (sourceB2622 + difference 2 3) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3754) := by
    have ha : (tripleCharges (sourceA2622 + difference 3 2) (sourceB2622 + difference 2 3) sourceC2622) = raw36634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36634; decide +kernel
    rw [ha]
    exact (canonical36634 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2622 + difference 3 4) (sourceB2622 + difference 4 3) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2622 + difference 3 4) (sourceB2622 + difference 4 3) sourceC2622) = raw36635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36635; decide +kernel
    rw [ha]
    exact (canonical36635 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2622 + difference 3 5) (sourceB2622 + difference 5 3) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2622 + difference 3 5) (sourceB2622 + difference 5 3) sourceC2622) = raw36636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36636; decide +kernel
    rw [ha]
    exact (canonical36636 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2622 + difference 4 0) (sourceB2622 + difference 0 4) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3555) := by
    have ha : (tripleCharges (sourceA2622 + difference 4 0) (sourceB2622 + difference 0 4) sourceC2622) = raw36637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36637; decide +kernel
    rw [ha]
    exact (canonical36637 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2622 + difference 4 1) (sourceB2622 + difference 1 4) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2622 + difference 4 1) (sourceB2622 + difference 1 4) sourceC2622) = raw36638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36638; decide +kernel
    rw [ha]
    exact (canonical36638 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2622 + difference 4 2) (sourceB2622 + difference 2 4) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2622 + difference 4 2) (sourceB2622 + difference 2 4) sourceC2622) = raw36639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36639; decide +kernel
    rw [ha]
    exact (canonical36639 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2622 + difference 4 3) (sourceB2622 + difference 3 4) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA2622 + difference 4 3) (sourceB2622 + difference 3 4) sourceC2622) = raw36640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36640; decide +kernel
    rw [ha]
    exact (canonical36640 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2622 + difference 4 5) (sourceB2622 + difference 5 4) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2622 + difference 4 5) (sourceB2622 + difference 5 4) sourceC2622) = raw36641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36641; decide +kernel
    rw [ha]
    exact (canonical36641 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2622 + difference 5 0) (sourceB2622 + difference 0 5) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2622 + difference 5 0) (sourceB2622 + difference 0 5) sourceC2622) = raw36642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36642; decide +kernel
    rw [ha]
    exact (canonical36642 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2622 + difference 5 1) (sourceB2622 + difference 1 5) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2622 + difference 5 1) (sourceB2622 + difference 1 5) sourceC2622) = raw36643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36643; decide +kernel
    rw [ha]
    exact (canonical36643 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2622 + difference 5 2) (sourceB2622 + difference 2 5) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2622 + difference 5 2) (sourceB2622 + difference 2 5) sourceC2622) = raw36644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36644; decide +kernel
    rw [ha]
    exact (canonical36644 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2622 + difference 5 3) (sourceB2622 + difference 3 5) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA2622 + difference 5 3) (sourceB2622 + difference 3 5) sourceC2622) = raw36645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36645; decide +kernel
    rw [ha]
    exact (canonical36645 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2622 + difference 5 4) (sourceB2622 + difference 4 5) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2622 + difference 5 4) (sourceB2622 + difference 4 5) sourceC2622) = raw36646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36646; decide +kernel
    rw [ha]
    exact (canonical36646 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2622 sourceB2622 sourceC2622
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2622, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2089 : Integer.Sparse.reindex keyMap MixedData.row2089 = numericRow2089 := by decide +kernel

theorem numericCheck2089 (x : Master → ℝ) : Integer.Sparse.eval numericRow2089 x =
    (1 : ℝ) * reducedSource2089 x := by
  norm_num [numericRow2089, reducedSource2089, Integer.Sparse.eval, Sparse.eval, nodeValue2211, nodeValue2212, nodeValue2217, nodeValue2223, nodeValue2274, nodeValue3407, nodeValue3417, nodeValue3418, nodeValue3479, nodeValue3553, nodeValue3555, nodeValue3570, nodeValue3591, nodeValue3754, nodeValue3755, nodeValue3758, nodeValue3761, nodeValue3762, nodeValue3766, nodeValue3767, nodeValue3770, nodeValue3772, nodeValue3796, nodeValue3808, nodeValue3813, nodeValue3814, nodeValue3873, nodeValue3877, nodeValue3884, nodeValue3958]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2089 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2089 (mixedVector B) = 0 := by
  have h2211 : mixedVector B (Sum.inr 2211) = Sparse.eval nodeValue2211 (mixedVector B) := by
    change mixedMoment B node2211 node2211Labels = _
    exact sound2211 B hB hF
  have h2212 : mixedVector B (Sum.inr 2212) = Sparse.eval nodeValue2212 (mixedVector B) := by
    change mixedMoment B node2212 node2212Labels = _
    exact sound2212 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2223 : mixedVector B (Sum.inr 2223) = Sparse.eval nodeValue2223 (mixedVector B) := by
    change mixedMoment B node2223 node2223Labels = _
    exact sound2223 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h3407 : mixedVector B (Sum.inr 3407) = Sparse.eval nodeValue3407 (mixedVector B) := by
    change mixedMoment B node3407 node3407Labels = _
    exact sound3407 B hB hF
  have h3417 : mixedVector B (Sum.inr 3417) = Sparse.eval nodeValue3417 (mixedVector B) := by
    change mixedMoment B node3417 node3417Labels = _
    exact sound3417 B hB hF
  have h3418 : mixedVector B (Sum.inr 3418) = Sparse.eval nodeValue3418 (mixedVector B) := by
    change mixedMoment B node3418 node3418Labels = _
    exact sound3418 B hB hF
  have h3479 : mixedVector B (Sum.inr 3479) = Sparse.eval nodeValue3479 (mixedVector B) := by
    change mixedMoment B node3479 node3479Labels = _
    exact sound3479 B hB hF
  have h3553 : mixedVector B (Sum.inr 3553) = Sparse.eval nodeValue3553 (mixedVector B) := by
    change mixedMoment B node3553 node3553Labels = _
    exact sound3553 B hB hF
  have h3555 : mixedVector B (Sum.inr 3555) = Sparse.eval nodeValue3555 (mixedVector B) := by
    change mixedMoment B node3555 node3555Labels = _
    exact sound3555 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h3591 : mixedVector B (Sum.inr 3591) = Sparse.eval nodeValue3591 (mixedVector B) := by
    change mixedMoment B node3591 node3591Labels = _
    exact sound3591 B hB hF
  have h3754 : mixedVector B (Sum.inr 3754) = Sparse.eval nodeValue3754 (mixedVector B) := by
    change mixedMoment B node3754 node3754Labels = _
    exact sound3754 B hB hF
  have h3755 : mixedVector B (Sum.inr 3755) = Sparse.eval nodeValue3755 (mixedVector B) := by
    change mixedMoment B node3755 node3755Labels = _
    exact sound3755 B hB hF
  have h3758 : mixedVector B (Sum.inr 3758) = Sparse.eval nodeValue3758 (mixedVector B) := by
    change mixedMoment B node3758 node3758Labels = _
    exact sound3758 B hB hF
  have h3761 : mixedVector B (Sum.inr 3761) = Sparse.eval nodeValue3761 (mixedVector B) := by
    change mixedMoment B node3761 node3761Labels = _
    exact sound3761 B hB hF
  have h3762 : mixedVector B (Sum.inr 3762) = Sparse.eval nodeValue3762 (mixedVector B) := by
    change mixedMoment B node3762 node3762Labels = _
    exact sound3762 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3767 : mixedVector B (Sum.inr 3767) = Sparse.eval nodeValue3767 (mixedVector B) := by
    change mixedMoment B node3767 node3767Labels = _
    exact sound3767 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h3772 : mixedVector B (Sum.inr 3772) = Sparse.eval nodeValue3772 (mixedVector B) := by
    change mixedMoment B node3772 node3772Labels = _
    exact sound3772 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3873 : mixedVector B (Sum.inr 3873) = Sparse.eval nodeValue3873 (mixedVector B) := by
    change mixedMoment B node3873 node3873Labels = _
    exact sound3873 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  simpa only [sourceForm2622, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2211, h2212, h2217, h2223, h2274, h3407, h3417, h3418, h3479, h3553, h3555, h3570, h3591, h3754, h3755, h3758, h3761, h3762, h3766, h3767, h3770, h3772, h3796, h3808, h3813, h3814, h3873, h3877, h3884, h3958, reducedSource2089] using sourceEq2622 B hB

theorem rowSound2089_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2089 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2089, numericCheck2089, reducedZero2089 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2089_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2089_e_oai
