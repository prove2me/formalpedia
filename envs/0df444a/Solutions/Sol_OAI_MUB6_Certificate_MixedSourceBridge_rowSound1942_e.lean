-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:21:14.121367+00:00
-- url     : https://prove2.me/submissions/47c45407-ce8c-4691-9d03-c940c8345b9b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E106
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical190
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical255
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32766 raw32766Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw32766 raw32766Labels = mixedMoment B raw32766step0 raw32766step0Labels := by
      have hz : ∀ j, raw32766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32766step0 = (fun i j => raw32766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32766step0 raw32766; decide +kernel
      have hl : raw32766step0Labels = raw32766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32766 raw32766Labels permutation346 hz
    mixedMoment B raw32766step0 raw32766step0Labels = mixedMoment B raw32766step1 raw32766step1Labels := by
      have ha : raw32766step1 = (fun i j => raw32766step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32766step1 raw32766step0; decide +kernel
      have hl : raw32766step1Labels = raw32766step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32766step0 raw32766step0Labels permutation143 permutation7
    mixedMoment B raw32766step1 raw32766step1Labels = mixedMoment B raw32766step2 raw32766step2Labels := by
      have ha : raw32766step2 = raw32766step1 := by apply Matrix.ext; unfold raw32766step2 raw32766step1; decide +kernel
      have hl : raw32766step1Labels = labelEmbedding1 ∘ raw32766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32766step1 raw32766step1Labels raw32766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

theorem canonical32767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32767 raw32767Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw32767 raw32767Labels = mixedMoment B raw32767step0 raw32767step0Labels := by
      have ha : raw32767step0 = (fun i j => raw32767 (permutation653 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32767step0 raw32767; decide +kernel
      have hl : raw32767step0Labels = raw32767Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32767 raw32767Labels permutation653 permutation7
    mixedMoment B raw32767step0 raw32767step0Labels = mixedMoment B raw32767step1 raw32767step1Labels := by
      have ha : raw32767step1 = raw32767step0 := by apply Matrix.ext; unfold raw32767step1 raw32767step0; decide +kernel
      have hl : raw32767step0Labels = labelEmbedding1 ∘ raw32767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32767step0 raw32767step0Labels raw32767step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32768 raw32768Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw32768 raw32768Labels = mixedMoment B raw32768step0 raw32768step0Labels := by
      have hz : ∀ j, raw32768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32768step0 = (fun i j => raw32768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32768step0 raw32768; decide +kernel
      have hl : raw32768step0Labels = raw32768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32768 raw32768Labels permutation346 hz
    mixedMoment B raw32768step0 raw32768step0Labels = mixedMoment B raw32768step1 raw32768step1Labels := by
      have ha : raw32768step1 = (fun i j => raw32768step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32768step1 raw32768step0; decide +kernel
      have hl : raw32768step1Labels = raw32768step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32768step0 raw32768step0Labels permutation143 permutation7
    mixedMoment B raw32768step1 raw32768step1Labels = mixedMoment B raw32768step2 raw32768step2Labels := by
      have ha : raw32768step2 = raw32768step1 := by apply Matrix.ext; unfold raw32768step2 raw32768step1; decide +kernel
      have hl : raw32768step1Labels = labelEmbedding1 ∘ raw32768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32768step1 raw32768step1Labels raw32768step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical32769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32769 raw32769Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw32769 raw32769Labels = mixedMoment B raw32769step0 raw32769step0Labels := by
      have hz : ∀ j, raw32769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32769step0 = (fun i j => raw32769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32769step0 raw32769; decide +kernel
      have hl : raw32769step0Labels = raw32769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32769 raw32769Labels permutation346 hz
    mixedMoment B raw32769step0 raw32769step0Labels = mixedMoment B raw32769step1 raw32769step1Labels := by
      have ha : raw32769step1 = (fun i j => raw32769step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32769step1 raw32769step0; decide +kernel
      have hl : raw32769step1Labels = raw32769step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32769step0 raw32769step0Labels permutation143 permutation7
    mixedMoment B raw32769step1 raw32769step1Labels = mixedMoment B raw32769step2 raw32769step2Labels := by
      have ha : raw32769step2 = raw32769step1 := by apply Matrix.ext; unfold raw32769step2 raw32769step1; decide +kernel
      have hl : raw32769step1Labels = labelEmbedding1 ∘ raw32769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32769step1 raw32769step1Labels raw32769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical32770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32770 raw32770Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw32770 raw32770Labels = mixedMoment B raw32770step0 raw32770step0Labels := by
      have hz : ∀ j, raw32770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32770step0 = (fun i j => raw32770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32770step0 raw32770; decide +kernel
      have hl : raw32770step0Labels = raw32770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32770 raw32770Labels permutation346 hz
    mixedMoment B raw32770step0 raw32770step0Labels = mixedMoment B raw32770step1 raw32770step1Labels := by
      have ha : raw32770step1 = (fun i j => raw32770step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32770step1 raw32770step0; decide +kernel
      have hl : raw32770step1Labels = raw32770step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32770step0 raw32770step0Labels permutation44 permutation7
    mixedMoment B raw32770step1 raw32770step1Labels = mixedMoment B raw32770step2 raw32770step2Labels := by
      have ha : raw32770step2 = -raw32770step1 := by apply Matrix.ext; change ∀ i j, raw32770step2 i j = -(raw32770step1 i j); unfold raw32770step2 raw32770step1; decide +kernel
      have hl : raw32770step2Labels = raw32770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32770step2 raw32770step2Labels = mixedMoment B raw32770step3 raw32770step3Labels := by
      have ha : raw32770step3 = raw32770step2 := by apply Matrix.ext; unfold raw32770step3 raw32770step2; decide +kernel
      have hl : raw32770step2Labels = labelEmbedding1 ∘ raw32770step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32770step2 raw32770step2Labels raw32770step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical32771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32771 raw32771Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw32771 raw32771Labels = mixedMoment B raw32771step0 raw32771step0Labels := by
      have hz : ∀ j, raw32771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32771step0 = (fun i j => raw32771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32771step0 raw32771; decide +kernel
      have hl : raw32771step0Labels = raw32771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32771 raw32771Labels permutation346 hz
    mixedMoment B raw32771step0 raw32771step0Labels = mixedMoment B raw32771step1 raw32771step1Labels := by
      have hz : ∀ j, raw32771step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw32771step1 = (fun i j => raw32771step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw32771step1 raw32771step0; decide +kernel
      have hl : raw32771step1Labels = raw32771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32771step0 raw32771step0Labels permutation56 hz
    mixedMoment B raw32771step1 raw32771step1Labels = mixedMoment B raw32771step2 raw32771step2Labels := by
      have ha : raw32771step2 = (fun i j => raw32771step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32771step2 raw32771step1; decide +kernel
      have hl : raw32771step2Labels = raw32771step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32771step1 raw32771step1Labels permutation10 permutation7
    mixedMoment B raw32771step2 raw32771step2Labels = mixedMoment B raw32771step3 raw32771step3Labels := by
      have ha : raw32771step3 = -raw32771step2 := by apply Matrix.ext; change ∀ i j, raw32771step3 i j = -(raw32771step2 i j); unfold raw32771step3 raw32771step2; decide +kernel
      have hl : raw32771step3Labels = raw32771step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32771step3 raw32771step3Labels = mixedMoment B raw32771step4 raw32771step4Labels := by
      have ha : raw32771step4 = raw32771step3 := by apply Matrix.ext; unfold raw32771step4 raw32771step3; decide +kernel
      have hl : raw32771step3Labels = labelEmbedding1 ∘ raw32771step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32771step3 raw32771step3Labels raw32771step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

theorem canonical32772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32772 raw32772Labels = mixedMoment B node3553 node3553Labels := by
  calc
    mixedMoment B raw32772 raw32772Labels = mixedMoment B raw32772step0 raw32772step0Labels := by
      have ha : raw32772step0 = (fun i j => raw32772 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32772step0 raw32772; decide +kernel
      have hl : raw32772step0Labels = raw32772Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32772 raw32772Labels permutation224 permutation7
    mixedMoment B raw32772step0 raw32772step0Labels = mixedMoment B raw32772step1 raw32772step1Labels := by
      have ha : raw32772step1 = -raw32772step0 := by apply Matrix.ext; change ∀ i j, raw32772step1 i j = -(raw32772step0 i j); unfold raw32772step1 raw32772step0; decide +kernel
      have hl : raw32772step1Labels = raw32772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32772step1 raw32772step1Labels = mixedMoment B raw32772step2 raw32772step2Labels := by
      have ha : raw32772step2 = raw32772step1 := by apply Matrix.ext; unfold raw32772step2 raw32772step1; decide +kernel
      have hl : raw32772step1Labels = labelEmbedding1 ∘ raw32772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32772step1 raw32772step1Labels raw32772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3553 node3553Labels := by rfl

theorem canonical32773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32773 raw32773Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw32773 raw32773Labels = mixedMoment B raw32773step0 raw32773step0Labels := by
      have ha : raw32773step0 = (fun i j => raw32773 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32773step0 raw32773; decide +kernel
      have hl : raw32773step0Labels = raw32773Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32773 raw32773Labels permutation224 permutation7
    mixedMoment B raw32773step0 raw32773step0Labels = mixedMoment B raw32773step1 raw32773step1Labels := by
      have ha : raw32773step1 = -raw32773step0 := by apply Matrix.ext; change ∀ i j, raw32773step1 i j = -(raw32773step0 i j); unfold raw32773step1 raw32773step0; decide +kernel
      have hl : raw32773step1Labels = raw32773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32773step1 raw32773step1Labels = mixedMoment B raw32773step2 raw32773step2Labels := by
      have ha : raw32773step2 = raw32773step1 := by apply Matrix.ext; unfold raw32773step2 raw32773step1; decide +kernel
      have hl : raw32773step1Labels = labelEmbedding1 ∘ raw32773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32773step1 raw32773step1Labels raw32773step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical32774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32774 raw32774Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw32774 raw32774Labels = mixedMoment B raw32774step0 raw32774step0Labels := by
      have ha : raw32774step0 = (fun i j => raw32774 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32774step0 raw32774; decide +kernel
      have hl : raw32774step0Labels = raw32774Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32774 raw32774Labels permutation224 permutation7
    mixedMoment B raw32774step0 raw32774step0Labels = mixedMoment B raw32774step1 raw32774step1Labels := by
      have ha : raw32774step1 = -raw32774step0 := by apply Matrix.ext; change ∀ i j, raw32774step1 i j = -(raw32774step0 i j); unfold raw32774step1 raw32774step0; decide +kernel
      have hl : raw32774step1Labels = raw32774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32774step1 raw32774step1Labels = mixedMoment B raw32774step2 raw32774step2Labels := by
      have ha : raw32774step2 = raw32774step1 := by apply Matrix.ext; unfold raw32774step2 raw32774step1; decide +kernel
      have hl : raw32774step1Labels = labelEmbedding1 ∘ raw32774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32774step1 raw32774step1Labels raw32774step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical32775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32775 raw32775Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw32775 raw32775Labels = mixedMoment B raw32775step0 raw32775step0Labels := by
      have ha : raw32775step0 = (fun i j => raw32775 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32775step0 raw32775; decide +kernel
      have hl : raw32775step0Labels = raw32775Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32775 raw32775Labels permutation224 permutation7
    mixedMoment B raw32775step0 raw32775step0Labels = mixedMoment B raw32775step1 raw32775step1Labels := by
      have ha : raw32775step1 = -raw32775step0 := by apply Matrix.ext; change ∀ i j, raw32775step1 i j = -(raw32775step0 i j); unfold raw32775step1 raw32775step0; decide +kernel
      have hl : raw32775step1Labels = raw32775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32775step1 raw32775step1Labels = mixedMoment B raw32775step2 raw32775step2Labels := by
      have ha : raw32775step2 = raw32775step1 := by apply Matrix.ext; unfold raw32775step2 raw32775step1; decide +kernel
      have hl : raw32775step1Labels = labelEmbedding1 ∘ raw32775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32775step1 raw32775step1Labels raw32775step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

theorem canonical32776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32776 raw32776Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw32776 raw32776Labels = mixedMoment B raw32776step0 raw32776step0Labels := by
      have hz : ∀ j, raw32776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32776step0 = (fun i j => raw32776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32776step0 raw32776; decide +kernel
      have hl : raw32776step0Labels = raw32776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32776 raw32776Labels permutation346 hz
    mixedMoment B raw32776step0 raw32776step0Labels = mixedMoment B raw32776step1 raw32776step1Labels := by
      have ha : raw32776step1 = (fun i j => raw32776step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32776step1 raw32776step0; decide +kernel
      have hl : raw32776step1Labels = raw32776step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32776step0 raw32776step0Labels permutation44 permutation7
    mixedMoment B raw32776step1 raw32776step1Labels = mixedMoment B raw32776step2 raw32776step2Labels := by
      have ha : raw32776step2 = -raw32776step1 := by apply Matrix.ext; change ∀ i j, raw32776step2 i j = -(raw32776step1 i j); unfold raw32776step2 raw32776step1; decide +kernel
      have hl : raw32776step2Labels = raw32776step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32776step2 raw32776step2Labels = mixedMoment B raw32776step3 raw32776step3Labels := by
      have ha : raw32776step3 = raw32776step2 := by apply Matrix.ext; unfold raw32776step3 raw32776step2; decide +kernel
      have hl : raw32776step2Labels = labelEmbedding1 ∘ raw32776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32776step2 raw32776step2Labels raw32776step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

theorem canonical32777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32777 raw32777Labels = mixedMoment B node3556 node3556Labels := by
  calc
    mixedMoment B raw32777 raw32777Labels = mixedMoment B raw32777step0 raw32777step0Labels := by
      have ha : raw32777step0 = (fun i j => raw32777 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32777step0 raw32777; decide +kernel
      have hl : raw32777step0Labels = raw32777Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32777 raw32777Labels permutation224 permutation7
    mixedMoment B raw32777step0 raw32777step0Labels = mixedMoment B raw32777step1 raw32777step1Labels := by
      have ha : raw32777step1 = -raw32777step0 := by apply Matrix.ext; change ∀ i j, raw32777step1 i j = -(raw32777step0 i j); unfold raw32777step1 raw32777step0; decide +kernel
      have hl : raw32777step1Labels = raw32777step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32777step1 raw32777step1Labels = mixedMoment B raw32777step2 raw32777step2Labels := by
      have ha : raw32777step2 = raw32777step1 := by apply Matrix.ext; unfold raw32777step2 raw32777step1; decide +kernel
      have hl : raw32777step1Labels = labelEmbedding1 ∘ raw32777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32777step1 raw32777step1Labels raw32777step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3556 node3556Labels := by rfl

theorem canonical32778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32778 raw32778Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw32778 raw32778Labels = mixedMoment B raw32778step0 raw32778step0Labels := by
      have hz : ∀ j, raw32778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32778step0 = (fun i j => raw32778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32778step0 raw32778; decide +kernel
      have hl : raw32778step0Labels = raw32778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32778 raw32778Labels permutation346 hz
    mixedMoment B raw32778step0 raw32778step0Labels = mixedMoment B raw32778step1 raw32778step1Labels := by
      have ha : raw32778step1 = (fun i j => raw32778step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32778step1 raw32778step0; decide +kernel
      have hl : raw32778step1Labels = raw32778step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32778step0 raw32778step0Labels permutation44 permutation7
    mixedMoment B raw32778step1 raw32778step1Labels = mixedMoment B raw32778step2 raw32778step2Labels := by
      have ha : raw32778step2 = -raw32778step1 := by apply Matrix.ext; change ∀ i j, raw32778step2 i j = -(raw32778step1 i j); unfold raw32778step2 raw32778step1; decide +kernel
      have hl : raw32778step2Labels = raw32778step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32778step2 raw32778step2Labels = mixedMoment B raw32778step3 raw32778step3Labels := by
      have ha : raw32778step3 = raw32778step2 := by apply Matrix.ext; unfold raw32778step3 raw32778step2; decide +kernel
      have hl : raw32778step2Labels = labelEmbedding1 ∘ raw32778step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32778step2 raw32778step2Labels raw32778step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical32779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32779 raw32779Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw32779 raw32779Labels = mixedMoment B raw32779step0 raw32779step0Labels := by
      have hz : ∀ j, raw32779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32779step0 = (fun i j => raw32779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32779step0 raw32779; decide +kernel
      have hl : raw32779step0Labels = raw32779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32779 raw32779Labels permutation346 hz
    mixedMoment B raw32779step0 raw32779step0Labels = mixedMoment B raw32779step1 raw32779step1Labels := by
      have ha : raw32779step1 = (fun i j => raw32779step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32779step1 raw32779step0; decide +kernel
      have hl : raw32779step1Labels = raw32779step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32779step0 raw32779step0Labels permutation44 permutation7
    mixedMoment B raw32779step1 raw32779step1Labels = mixedMoment B raw32779step2 raw32779step2Labels := by
      have ha : raw32779step2 = -raw32779step1 := by apply Matrix.ext; change ∀ i j, raw32779step2 i j = -(raw32779step1 i j); unfold raw32779step2 raw32779step1; decide +kernel
      have hl : raw32779step2Labels = raw32779step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32779step2 raw32779step2Labels = mixedMoment B raw32779step3 raw32779step3Labels := by
      have ha : raw32779step3 = raw32779step2 := by apply Matrix.ext; unfold raw32779step3 raw32779step2; decide +kernel
      have hl : raw32779step2Labels = labelEmbedding1 ∘ raw32779step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32779step2 raw32779step2Labels raw32779step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

theorem canonical32780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32780 raw32780Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw32780 raw32780Labels = mixedMoment B raw32780step0 raw32780step0Labels := by
      have hz : ∀ j, raw32780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32780step0 = (fun i j => raw32780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32780step0 raw32780; decide +kernel
      have hl : raw32780step0Labels = raw32780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32780 raw32780Labels permutation346 hz
    mixedMoment B raw32780step0 raw32780step0Labels = mixedMoment B raw32780step1 raw32780step1Labels := by
      have ha : raw32780step1 = (fun i j => raw32780step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32780step1 raw32780step0; decide +kernel
      have hl : raw32780step1Labels = raw32780step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32780step0 raw32780step0Labels permutation126 permutation5
    mixedMoment B raw32780step1 raw32780step1Labels = mixedMoment B raw32780step2 raw32780step2Labels := by
      have ha : raw32780step2 = raw32780step1 := by apply Matrix.ext; unfold raw32780step2 raw32780step1; decide +kernel
      have hl : raw32780step1Labels = labelEmbedding1 ∘ raw32780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32780step1 raw32780step1Labels raw32780step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

theorem canonical32781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32781 raw32781Labels = mixedMoment B node2655 node2655Labels := by
  calc
    mixedMoment B raw32781 raw32781Labels = mixedMoment B raw32781step0 raw32781step0Labels := by
      have ha : raw32781step0 = (fun i j => raw32781 (permutation587 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32781step0 raw32781; decide +kernel
      have hl : raw32781step0Labels = raw32781Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32781 raw32781Labels permutation587 permutation5
    mixedMoment B raw32781step0 raw32781step0Labels = mixedMoment B raw32781step1 raw32781step1Labels := by
      have ha : raw32781step1 = raw32781step0 := by apply Matrix.ext; unfold raw32781step1 raw32781step0; decide +kernel
      have hl : raw32781step0Labels = labelEmbedding1 ∘ raw32781step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32781step0 raw32781step0Labels raw32781step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2655 node2655Labels := by rfl

theorem canonical32782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32782 raw32782Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw32782 raw32782Labels = mixedMoment B raw32782step0 raw32782step0Labels := by
      have hz : ∀ j, raw32782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32782step0 = (fun i j => raw32782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32782step0 raw32782; decide +kernel
      have hl : raw32782step0Labels = raw32782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32782 raw32782Labels permutation346 hz
    mixedMoment B raw32782step0 raw32782step0Labels = mixedMoment B raw32782step1 raw32782step1Labels := by
      have ha : raw32782step1 = (fun i j => raw32782step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32782step1 raw32782step0; decide +kernel
      have hl : raw32782step1Labels = raw32782step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32782step0 raw32782step0Labels permutation127 permutation5
    mixedMoment B raw32782step1 raw32782step1Labels = mixedMoment B raw32782step2 raw32782step2Labels := by
      have ha : raw32782step2 = raw32782step1 := by apply Matrix.ext; unfold raw32782step2 raw32782step1; decide +kernel
      have hl : raw32782step1Labels = labelEmbedding1 ∘ raw32782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32782step1 raw32782step1Labels raw32782step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical32783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32783 raw32783Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw32783 raw32783Labels = mixedMoment B raw32783step0 raw32783step0Labels := by
      have hz : ∀ j, raw32783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32783step0 = (fun i j => raw32783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32783step0 raw32783; decide +kernel
      have hl : raw32783step0Labels = raw32783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32783 raw32783Labels permutation346 hz
    mixedMoment B raw32783step0 raw32783step0Labels = mixedMoment B raw32783step1 raw32783step1Labels := by
      have ha : raw32783step1 = (fun i j => raw32783step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32783step1 raw32783step0; decide +kernel
      have hl : raw32783step1Labels = raw32783step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32783step0 raw32783step0Labels permutation121 permutation5
    mixedMoment B raw32783step1 raw32783step1Labels = mixedMoment B raw32783step2 raw32783step2Labels := by
      have ha : raw32783step2 = raw32783step1 := by apply Matrix.ext; unfold raw32783step2 raw32783step1; decide +kernel
      have hl : raw32783step1Labels = labelEmbedding1 ∘ raw32783step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32783step1 raw32783step1Labels raw32783step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

theorem canonical32784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32784 raw32784Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw32784 raw32784Labels = mixedMoment B raw32784step0 raw32784step0Labels := by
      have hz : ∀ j, raw32784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32784step0 = (fun i j => raw32784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32784step0 raw32784; decide +kernel
      have hl : raw32784step0Labels = raw32784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32784 raw32784Labels permutation346 hz
    mixedMoment B raw32784step0 raw32784step0Labels = mixedMoment B raw32784step1 raw32784step1Labels := by
      have ha : raw32784step1 = (fun i j => raw32784step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32784step1 raw32784step0; decide +kernel
      have hl : raw32784step1Labels = raw32784step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32784step0 raw32784step0Labels permutation143 permutation7
    mixedMoment B raw32784step1 raw32784step1Labels = mixedMoment B raw32784step2 raw32784step2Labels := by
      have ha : raw32784step2 = raw32784step1 := by apply Matrix.ext; unfold raw32784step2 raw32784step1; decide +kernel
      have hl : raw32784step1Labels = labelEmbedding1 ∘ raw32784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32784step1 raw32784step1Labels raw32784step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

theorem canonical32785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32785 raw32785Labels = mixedMoment B node3458 node3458Labels := by
  calc
    mixedMoment B raw32785 raw32785Labels = mixedMoment B raw32785step0 raw32785step0Labels := by
      have ha : raw32785step0 = (fun i j => raw32785 (permutation653 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32785step0 raw32785; decide +kernel
      have hl : raw32785step0Labels = raw32785Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32785 raw32785Labels permutation653 permutation7
    mixedMoment B raw32785step0 raw32785step0Labels = mixedMoment B raw32785step1 raw32785step1Labels := by
      have ha : raw32785step1 = raw32785step0 := by apply Matrix.ext; unfold raw32785step1 raw32785step0; decide +kernel
      have hl : raw32785step0Labels = labelEmbedding1 ∘ raw32785step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32785step0 raw32785step0Labels raw32785step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3458 node3458Labels := by rfl

theorem canonical32786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32786 raw32786Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw32786 raw32786Labels = mixedMoment B raw32786step0 raw32786step0Labels := by
      have hz : ∀ j, raw32786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32786step0 = (fun i j => raw32786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32786step0 raw32786; decide +kernel
      have hl : raw32786step0Labels = raw32786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32786 raw32786Labels permutation346 hz
    mixedMoment B raw32786step0 raw32786step0Labels = mixedMoment B raw32786step1 raw32786step1Labels := by
      have ha : raw32786step1 = (fun i j => raw32786step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32786step1 raw32786step0; decide +kernel
      have hl : raw32786step1Labels = raw32786step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32786step0 raw32786step0Labels permutation143 permutation7
    mixedMoment B raw32786step1 raw32786step1Labels = mixedMoment B raw32786step2 raw32786step2Labels := by
      have ha : raw32786step2 = raw32786step1 := by apply Matrix.ext; unfold raw32786step2 raw32786step1; decide +kernel
      have hl : raw32786step1Labels = labelEmbedding1 ∘ raw32786step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32786step1 raw32786step1Labels raw32786step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical32787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32787 raw32787Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw32787 raw32787Labels = mixedMoment B raw32787step0 raw32787step0Labels := by
      have hz : ∀ j, raw32787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32787step0 = (fun i j => raw32787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32787step0 raw32787; decide +kernel
      have hl : raw32787step0Labels = raw32787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32787 raw32787Labels permutation346 hz
    mixedMoment B raw32787step0 raw32787step0Labels = mixedMoment B raw32787step1 raw32787step1Labels := by
      have ha : raw32787step1 = (fun i j => raw32787step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32787step1 raw32787step0; decide +kernel
      have hl : raw32787step1Labels = raw32787step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32787step0 raw32787step0Labels permutation143 permutation7
    mixedMoment B raw32787step1 raw32787step1Labels = mixedMoment B raw32787step2 raw32787step2Labels := by
      have ha : raw32787step2 = raw32787step1 := by apply Matrix.ext; unfold raw32787step2 raw32787step1; decide +kernel
      have hl : raw32787step1Labels = labelEmbedding1 ∘ raw32787step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32787step1 raw32787step1Labels raw32787step2Labels labelEmbedding1 hl
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

theorem sound2657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2657 node2657Labels = Sparse.eval nodeValue2657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2657) = mixedMoment B node2657 node2657Labels := rfl
  simpa [nodeValue2657, Sparse.eval] using hc.symm

theorem sound2659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2659 node2659Labels = Sparse.eval nodeValue2659 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2659) = mixedMoment B node2659 node2659Labels := rfl
  simpa [nodeValue2659, Sparse.eval] using hc.symm

theorem sound2681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2681 node2681Labels = Sparse.eval nodeValue2681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2681) = mixedMoment B node2681 node2681Labels := rfl
  simpa [nodeValue2681, Sparse.eval] using hc.symm

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

theorem sound2735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2735 node2735Labels = Sparse.eval nodeValue2735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2735) = mixedMoment B node2735 node2735Labels := rfl
  simpa [nodeValue2735, Sparse.eval] using hc.symm

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

theorem sound3259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3259 node3259Labels = Sparse.eval nodeValue3259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3259) = mixedMoment B node3259 node3259Labels := rfl
  simpa [nodeValue3259, Sparse.eval] using hc.symm

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

theorem sound3271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3271 node3271Labels = Sparse.eval nodeValue3271 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3271) = mixedMoment B node3271 node3271Labels := rfl
  simpa [nodeValue3271, Sparse.eval] using hc.symm

theorem sound3305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3305 node3305Labels = Sparse.eval nodeValue3305 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3305) = mixedMoment B node3305 node3305Labels := rfl
  simpa [nodeValue3305, Sparse.eval] using hc.symm

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

theorem sound3458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3458 node3458Labels = Sparse.eval nodeValue3458 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3458) = mixedMoment B node3458 node3458Labels := rfl
  simpa [nodeValue3458, Sparse.eval] using hc.symm

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3475 node3475Labels = Sparse.eval nodeValue3475 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3475) = mixedMoment B node3475 node3475Labels := rfl
  simpa [nodeValue3475, Sparse.eval] using hc.symm

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

theorem sound3530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3530 node3530Labels = Sparse.eval nodeValue3530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3530) = mixedMoment B node3530 node3530Labels := rfl
  simpa [nodeValue3530, Sparse.eval] using hc.symm

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

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

theorem sound3556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3556 node3556Labels = Sparse.eval nodeValue3556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3556) = mixedMoment B node3556 node3556Labels := rfl
  simpa [nodeValue3556, Sparse.eval] using hc.symm

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

theorem sound3565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3565 node3565Labels = Sparse.eval nodeValue3565 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3565) = mixedMoment B node3565 node3565Labels := rfl
  simpa [nodeValue3565, Sparse.eval] using hc.symm

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

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

theorem sound3811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3811 node3811Labels = Sparse.eval nodeValue3811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3811) = mixedMoment B node3811 node3811Labels := rfl
  simpa [nodeValue3811, Sparse.eval] using hc.symm

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

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources74
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2392 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2392 + difference 0 1) (sourceB2392 + difference 1 0) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2392 + difference 0 1) (sourceB2392 + difference 1 0) sourceC2392) = raw32766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32766; decide +kernel
    rw [ha]
    exact (canonical32766 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2392 + difference 0 2) (sourceB2392 + difference 2 0) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2392 + difference 0 2) (sourceB2392 + difference 2 0) sourceC2392) = raw32767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32767; decide +kernel
    rw [ha]
    exact (canonical32767 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2392 + difference 0 3) (sourceB2392 + difference 3 0) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA2392 + difference 0 3) (sourceB2392 + difference 3 0) sourceC2392) = raw32768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32768; decide +kernel
    rw [ha]
    exact (canonical32768 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2392 + difference 0 4) (sourceB2392 + difference 4 0) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2392 + difference 0 4) (sourceB2392 + difference 4 0) sourceC2392) = raw32769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32769; decide +kernel
    rw [ha]
    exact (canonical32769 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2392 + difference 0 5) (sourceB2392 + difference 5 0) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA2392 + difference 0 5) (sourceB2392 + difference 5 0) sourceC2392) = raw32770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32770; decide +kernel
    rw [ha]
    exact (canonical32770 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2392 + difference 1 0) (sourceB2392 + difference 0 1) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA2392 + difference 1 0) (sourceB2392 + difference 0 1) sourceC2392) = raw32771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32771; decide +kernel
    rw [ha]
    exact (canonical32771 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2392 + difference 1 2) (sourceB2392 + difference 2 1) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2392 + difference 1 2) (sourceB2392 + difference 2 1) sourceC2392) = raw24365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24365; decide +kernel
    rw [ha]
    exact (canonical24365 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2392 + difference 1 3) (sourceB2392 + difference 3 1) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA2392 + difference 1 3) (sourceB2392 + difference 3 1) sourceC2392) = raw24366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24366; decide +kernel
    rw [ha]
    exact (canonical24366 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2392 + difference 1 4) (sourceB2392 + difference 4 1) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA2392 + difference 1 4) (sourceB2392 + difference 4 1) sourceC2392) = raw24367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24367; decide +kernel
    rw [ha]
    exact (canonical24367 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2392 + difference 1 5) (sourceB2392 + difference 5 1) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA2392 + difference 1 5) (sourceB2392 + difference 5 1) sourceC2392) = raw24368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24368; decide +kernel
    rw [ha]
    exact (canonical24368 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2392 + difference 2 0) (sourceB2392 + difference 0 2) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3259) := by
    have ha : (tripleCharges (sourceA2392 + difference 2 0) (sourceB2392 + difference 0 2) sourceC2392) = raw24375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24375; decide +kernel
    rw [ha]
    exact (canonical24375 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2392 + difference 2 1) (sourceB2392 + difference 1 2) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3553) := by
    have ha : (tripleCharges (sourceA2392 + difference 2 1) (sourceB2392 + difference 1 2) sourceC2392) = raw32772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32772; decide +kernel
    rw [ha]
    exact (canonical32772 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2392 + difference 2 3) (sourceB2392 + difference 3 2) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA2392 + difference 2 3) (sourceB2392 + difference 3 2) sourceC2392) = raw32773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32773; decide +kernel
    rw [ha]
    exact (canonical32773 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2392 + difference 2 4) (sourceB2392 + difference 4 2) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA2392 + difference 2 4) (sourceB2392 + difference 4 2) sourceC2392) = raw32774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32774; decide +kernel
    rw [ha]
    exact (canonical32774 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2392 + difference 2 5) (sourceB2392 + difference 5 2) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA2392 + difference 2 5) (sourceB2392 + difference 5 2) sourceC2392) = raw32775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32775; decide +kernel
    rw [ha]
    exact (canonical32775 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2392 + difference 3 0) (sourceB2392 + difference 0 3) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3271) := by
    have ha : (tripleCharges (sourceA2392 + difference 3 0) (sourceB2392 + difference 0 3) sourceC2392) = raw24380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24380; decide +kernel
    rw [ha]
    exact (canonical24380 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2392 + difference 3 1) (sourceB2392 + difference 1 3) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3555) := by
    have ha : (tripleCharges (sourceA2392 + difference 3 1) (sourceB2392 + difference 1 3) sourceC2392) = raw32776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32776; decide +kernel
    rw [ha]
    exact (canonical32776 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2392 + difference 3 2) (sourceB2392 + difference 2 3) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3556) := by
    have ha : (tripleCharges (sourceA2392 + difference 3 2) (sourceB2392 + difference 2 3) sourceC2392) = raw32777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32777; decide +kernel
    rw [ha]
    exact (canonical32777 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2392 + difference 3 4) (sourceB2392 + difference 4 3) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2392 + difference 3 4) (sourceB2392 + difference 4 3) sourceC2392) = raw32778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32778; decide +kernel
    rw [ha]
    exact (canonical32778 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2392 + difference 3 5) (sourceB2392 + difference 5 3) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA2392 + difference 3 5) (sourceB2392 + difference 5 3) sourceC2392) = raw32779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32779; decide +kernel
    rw [ha]
    exact (canonical32779 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2392 + difference 4 0) (sourceB2392 + difference 0 4) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA2392 + difference 4 0) (sourceB2392 + difference 0 4) sourceC2392) = raw24385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24385; decide +kernel
    rw [ha]
    exact (canonical24385 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2392 + difference 4 1) (sourceB2392 + difference 1 4) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2659) := by
    have ha : (tripleCharges (sourceA2392 + difference 4 1) (sourceB2392 + difference 1 4) sourceC2392) = raw32780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32780; decide +kernel
    rw [ha]
    exact (canonical32780 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2392 + difference 4 2) (sourceB2392 + difference 2 4) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2655) := by
    have ha : (tripleCharges (sourceA2392 + difference 4 2) (sourceB2392 + difference 2 4) sourceC2392) = raw32781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32781; decide +kernel
    rw [ha]
    exact (canonical32781 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2392 + difference 4 3) (sourceB2392 + difference 3 4) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA2392 + difference 4 3) (sourceB2392 + difference 3 4) sourceC2392) = raw32782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32782; decide +kernel
    rw [ha]
    exact (canonical32782 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2392 + difference 4 5) (sourceB2392 + difference 5 4) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA2392 + difference 4 5) (sourceB2392 + difference 5 4) sourceC2392) = raw32783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32783; decide +kernel
    rw [ha]
    exact (canonical32783 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2392 + difference 5 0) (sourceB2392 + difference 0 5) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA2392 + difference 5 0) (sourceB2392 + difference 0 5) sourceC2392) = raw24390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24390; decide +kernel
    rw [ha]
    exact (canonical24390 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2392 + difference 5 1) (sourceB2392 + difference 1 5) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2392 + difference 5 1) (sourceB2392 + difference 1 5) sourceC2392) = raw32784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32784; decide +kernel
    rw [ha]
    exact (canonical32784 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2392 + difference 5 2) (sourceB2392 + difference 2 5) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3458) := by
    have ha : (tripleCharges (sourceA2392 + difference 5 2) (sourceB2392 + difference 2 5) sourceC2392) = raw32785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32785; decide +kernel
    rw [ha]
    exact (canonical32785 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2392 + difference 5 3) (sourceB2392 + difference 3 5) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA2392 + difference 5 3) (sourceB2392 + difference 3 5) sourceC2392) = raw32786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32786; decide +kernel
    rw [ha]
    exact (canonical32786 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2392 + difference 5 4) (sourceB2392 + difference 4 5) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2392 + difference 5 4) (sourceB2392 + difference 4 5) sourceC2392) = raw32787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32787; decide +kernel
    rw [ha]
    exact (canonical32787 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2392 sourceB2392 sourceC2392
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2392, Integer.Sparse.eval]
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

theorem reindexCheck1942 : Integer.Sparse.reindex keyMap MixedData.row1942 = numericRow1942 := by decide +kernel

theorem numericCheck1942 (x : Master → ℝ) : Integer.Sparse.eval numericRow1942 x =
    (1 : ℝ) * reducedSource1942 x := by
  norm_num [numericRow1942, reducedSource1942, Integer.Sparse.eval, Sparse.eval, nodeValue2655, nodeValue2657, nodeValue2659, nodeValue2681, nodeValue2735, nodeValue3259, nodeValue3266, nodeValue3271, nodeValue3305, nodeValue3458, nodeValue3468, nodeValue3475, nodeValue3514, nodeValue3522, nodeValue3530, nodeValue3547, nodeValue3553, nodeValue3555, nodeValue3556, nodeValue3557, nodeValue3558, nodeValue3564, nodeValue3565, nodeValue3582, nodeValue3583, nodeValue3799, nodeValue3807, nodeValue3811, nodeValue3850, nodeValue3876]

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

theorem reducedZero1942 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1942 (mixedVector B) = 0 := by
  have h2655 : mixedVector B (Sum.inr 2655) = Sparse.eval nodeValue2655 (mixedVector B) := by
    change mixedMoment B node2655 node2655Labels = _
    exact sound2655 B hB hF
  have h2657 : mixedVector B (Sum.inr 2657) = Sparse.eval nodeValue2657 (mixedVector B) := by
    change mixedMoment B node2657 node2657Labels = _
    exact sound2657 B hB hF
  have h2659 : mixedVector B (Sum.inr 2659) = Sparse.eval nodeValue2659 (mixedVector B) := by
    change mixedMoment B node2659 node2659Labels = _
    exact sound2659 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h3259 : mixedVector B (Sum.inr 3259) = Sparse.eval nodeValue3259 (mixedVector B) := by
    change mixedMoment B node3259 node3259Labels = _
    exact sound3259 B hB hF
  have h3266 : mixedVector B (Sum.inr 3266) = Sparse.eval nodeValue3266 (mixedVector B) := by
    change mixedMoment B node3266 node3266Labels = _
    exact sound3266 B hB hF
  have h3271 : mixedVector B (Sum.inr 3271) = Sparse.eval nodeValue3271 (mixedVector B) := by
    change mixedMoment B node3271 node3271Labels = _
    exact sound3271 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3458 : mixedVector B (Sum.inr 3458) = Sparse.eval nodeValue3458 (mixedVector B) := by
    change mixedMoment B node3458 node3458Labels = _
    exact sound3458 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3475 : mixedVector B (Sum.inr 3475) = Sparse.eval nodeValue3475 (mixedVector B) := by
    change mixedMoment B node3475 node3475Labels = _
    exact sound3475 B hB hF
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3553 : mixedVector B (Sum.inr 3553) = Sparse.eval nodeValue3553 (mixedVector B) := by
    change mixedMoment B node3553 node3553Labels = _
    exact sound3553 B hB hF
  have h3555 : mixedVector B (Sum.inr 3555) = Sparse.eval nodeValue3555 (mixedVector B) := by
    change mixedMoment B node3555 node3555Labels = _
    exact sound3555 B hB hF
  have h3556 : mixedVector B (Sum.inr 3556) = Sparse.eval nodeValue3556 (mixedVector B) := by
    change mixedMoment B node3556 node3556Labels = _
    exact sound3556 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3799 : mixedVector B (Sum.inr 3799) = Sparse.eval nodeValue3799 (mixedVector B) := by
    change mixedMoment B node3799 node3799Labels = _
    exact sound3799 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3811 : mixedVector B (Sum.inr 3811) = Sparse.eval nodeValue3811 (mixedVector B) := by
    change mixedMoment B node3811 node3811Labels = _
    exact sound3811 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  simpa only [sourceForm2392, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2655, h2657, h2659, h2681, h2735, h3259, h3266, h3271, h3305, h3458, h3468, h3475, h3514, h3522, h3530, h3547, h3553, h3555, h3556, h3557, h3558, h3564, h3565, h3582, h3583, h3799, h3807, h3811, h3850, h3876, reducedSource1942] using sourceEq2392 B hB

theorem rowSound1942_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1942 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1942, numericCheck1942, reducedZero1942 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942_e_oai
