-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:25:42.287683+00:00
-- url     : https://prove2.me/submissions/b83eb430-6229-4b9d-bdb1-c646c3439ee2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E116
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical258
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33070 raw33070Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw33070 raw33070Labels = mixedMoment B raw33070step0 raw33070step0Labels := by
      have ha : raw33070step0 = (fun i j => raw33070 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33070step0 raw33070; decide +kernel
      have hl : raw33070step0Labels = raw33070Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33070 raw33070Labels permutation164 permutation7
    mixedMoment B raw33070step0 raw33070step0Labels = mixedMoment B raw33070step1 raw33070step1Labels := by
      have ha : raw33070step1 = -raw33070step0 := by apply Matrix.ext; change ∀ i j, raw33070step1 i j = -(raw33070step0 i j); unfold raw33070step1 raw33070step0; decide +kernel
      have hl : raw33070step1Labels = raw33070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33070step1 raw33070step1Labels = mixedMoment B raw33070step2 raw33070step2Labels := by
      have ha : raw33070step2 = raw33070step1 := by apply Matrix.ext; unfold raw33070step2 raw33070step1; decide +kernel
      have hl : raw33070step1Labels = labelEmbedding1 ∘ raw33070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33070step1 raw33070step1Labels raw33070step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

theorem canonical33071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33071 raw33071Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw33071 raw33071Labels = mixedMoment B raw33071step0 raw33071step0Labels := by
      have ha : raw33071step0 = (fun i j => raw33071 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33071step0 raw33071; decide +kernel
      have hl : raw33071step0Labels = raw33071Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33071 raw33071Labels permutation164 permutation7
    mixedMoment B raw33071step0 raw33071step0Labels = mixedMoment B raw33071step1 raw33071step1Labels := by
      have ha : raw33071step1 = -raw33071step0 := by apply Matrix.ext; change ∀ i j, raw33071step1 i j = -(raw33071step0 i j); unfold raw33071step1 raw33071step0; decide +kernel
      have hl : raw33071step1Labels = raw33071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33071step1 raw33071step1Labels = mixedMoment B raw33071step2 raw33071step2Labels := by
      have ha : raw33071step2 = raw33071step1 := by apply Matrix.ext; unfold raw33071step2 raw33071step1; decide +kernel
      have hl : raw33071step1Labels = labelEmbedding1 ∘ raw33071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33071step1 raw33071step1Labels raw33071step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical33072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33072 raw33072Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw33072 raw33072Labels = mixedMoment B raw33072step0 raw33072step0Labels := by
      have hz : ∀ j, raw33072 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33072step0 = (fun i j => raw33072 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33072step0 raw33072; decide +kernel
      have hl : raw33072step0Labels = raw33072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33072 raw33072Labels permutation520 hz
    mixedMoment B raw33072step0 raw33072step0Labels = mixedMoment B raw33072step1 raw33072step1Labels := by
      have ha : raw33072step1 = (fun i j => raw33072step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33072step1 raw33072step0; decide +kernel
      have hl : raw33072step1Labels = raw33072step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33072step0 raw33072step0Labels permutation32 permutation7
    mixedMoment B raw33072step1 raw33072step1Labels = mixedMoment B raw33072step2 raw33072step2Labels := by
      have ha : raw33072step2 = -raw33072step1 := by apply Matrix.ext; change ∀ i j, raw33072step2 i j = -(raw33072step1 i j); unfold raw33072step2 raw33072step1; decide +kernel
      have hl : raw33072step2Labels = raw33072step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33072step2 raw33072step2Labels = mixedMoment B raw33072step3 raw33072step3Labels := by
      have ha : raw33072step3 = raw33072step2 := by apply Matrix.ext; unfold raw33072step3 raw33072step2; decide +kernel
      have hl : raw33072step2Labels = labelEmbedding1 ∘ raw33072step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33072step2 raw33072step2Labels raw33072step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical33073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33073 raw33073Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw33073 raw33073Labels = mixedMoment B raw33073step0 raw33073step0Labels := by
      have ha : raw33073step0 = (fun i j => raw33073 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33073step0 raw33073; decide +kernel
      have hl : raw33073step0Labels = raw33073Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33073 raw33073Labels permutation164 permutation7
    mixedMoment B raw33073step0 raw33073step0Labels = mixedMoment B raw33073step1 raw33073step1Labels := by
      have ha : raw33073step1 = -raw33073step0 := by apply Matrix.ext; change ∀ i j, raw33073step1 i j = -(raw33073step0 i j); unfold raw33073step1 raw33073step0; decide +kernel
      have hl : raw33073step1Labels = raw33073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33073step1 raw33073step1Labels = mixedMoment B raw33073step2 raw33073step2Labels := by
      have ha : raw33073step2 = raw33073step1 := by apply Matrix.ext; unfold raw33073step2 raw33073step1; decide +kernel
      have hl : raw33073step1Labels = labelEmbedding1 ∘ raw33073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33073step1 raw33073step1Labels raw33073step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

theorem canonical33074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33074 raw33074Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw33074 raw33074Labels = mixedMoment B raw33074step0 raw33074step0Labels := by
      have ha : raw33074step0 = (fun i j => raw33074 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33074step0 raw33074; decide +kernel
      have hl : raw33074step0Labels = raw33074Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33074 raw33074Labels permutation164 permutation7
    mixedMoment B raw33074step0 raw33074step0Labels = mixedMoment B raw33074step1 raw33074step1Labels := by
      have ha : raw33074step1 = -raw33074step0 := by apply Matrix.ext; change ∀ i j, raw33074step1 i j = -(raw33074step0 i j); unfold raw33074step1 raw33074step0; decide +kernel
      have hl : raw33074step1Labels = raw33074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33074step1 raw33074step1Labels = mixedMoment B raw33074step2 raw33074step2Labels := by
      have ha : raw33074step2 = raw33074step1 := by apply Matrix.ext; unfold raw33074step2 raw33074step1; decide +kernel
      have hl : raw33074step1Labels = labelEmbedding1 ∘ raw33074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33074step1 raw33074step1Labels raw33074step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

theorem canonical33075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33075 raw33075Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw33075 raw33075Labels = mixedMoment B raw33075step0 raw33075step0Labels := by
      have ha : raw33075step0 = (fun i j => raw33075 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33075step0 raw33075; decide +kernel
      have hl : raw33075step0Labels = raw33075Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33075 raw33075Labels permutation164 permutation7
    mixedMoment B raw33075step0 raw33075step0Labels = mixedMoment B raw33075step1 raw33075step1Labels := by
      have ha : raw33075step1 = -raw33075step0 := by apply Matrix.ext; change ∀ i j, raw33075step1 i j = -(raw33075step0 i j); unfold raw33075step1 raw33075step0; decide +kernel
      have hl : raw33075step1Labels = raw33075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33075step1 raw33075step1Labels = mixedMoment B raw33075step2 raw33075step2Labels := by
      have ha : raw33075step2 = raw33075step1 := by apply Matrix.ext; unfold raw33075step2 raw33075step1; decide +kernel
      have hl : raw33075step1Labels = labelEmbedding1 ∘ raw33075step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33075step1 raw33075step1Labels raw33075step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

theorem canonical33076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33076 raw33076Labels = mixedMoment B node3410 node3410Labels := by
  calc
    mixedMoment B raw33076 raw33076Labels = mixedMoment B raw33076step0 raw33076step0Labels := by
      have ha : raw33076step0 = (fun i j => raw33076 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33076step0 raw33076; decide +kernel
      have hl : raw33076step0Labels = raw33076Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33076 raw33076Labels permutation164 permutation7
    mixedMoment B raw33076step0 raw33076step0Labels = mixedMoment B raw33076step1 raw33076step1Labels := by
      have ha : raw33076step1 = -raw33076step0 := by apply Matrix.ext; change ∀ i j, raw33076step1 i j = -(raw33076step0 i j); unfold raw33076step1 raw33076step0; decide +kernel
      have hl : raw33076step1Labels = raw33076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33076step1 raw33076step1Labels = mixedMoment B raw33076step2 raw33076step2Labels := by
      have ha : raw33076step2 = raw33076step1 := by apply Matrix.ext; unfold raw33076step2 raw33076step1; decide +kernel
      have hl : raw33076step1Labels = labelEmbedding1 ∘ raw33076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33076step1 raw33076step1Labels raw33076step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3410 node3410Labels := by rfl

theorem canonical33077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33077 raw33077Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw33077 raw33077Labels = mixedMoment B raw33077step0 raw33077step0Labels := by
      have hz : ∀ j, raw33077 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33077step0 = (fun i j => raw33077 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33077step0 raw33077; decide +kernel
      have hl : raw33077step0Labels = raw33077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33077 raw33077Labels permutation520 hz
    mixedMoment B raw33077step0 raw33077step0Labels = mixedMoment B raw33077step1 raw33077step1Labels := by
      have ha : raw33077step1 = (fun i j => raw33077step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33077step1 raw33077step0; decide +kernel
      have hl : raw33077step1Labels = raw33077step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33077step0 raw33077step0Labels permutation32 permutation7
    mixedMoment B raw33077step1 raw33077step1Labels = mixedMoment B raw33077step2 raw33077step2Labels := by
      have ha : raw33077step2 = -raw33077step1 := by apply Matrix.ext; change ∀ i j, raw33077step2 i j = -(raw33077step1 i j); unfold raw33077step2 raw33077step1; decide +kernel
      have hl : raw33077step2Labels = raw33077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33077step2 raw33077step2Labels = mixedMoment B raw33077step3 raw33077step3Labels := by
      have ha : raw33077step3 = raw33077step2 := by apply Matrix.ext; unfold raw33077step3 raw33077step2; decide +kernel
      have hl : raw33077step2Labels = labelEmbedding1 ∘ raw33077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33077step2 raw33077step2Labels raw33077step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

theorem canonical33078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33078 raw33078Labels = mixedMoment B node3469 node3469Labels := by
  calc
    mixedMoment B raw33078 raw33078Labels = mixedMoment B raw33078step0 raw33078step0Labels := by
      have ha : raw33078step0 = (fun i j => raw33078 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33078step0 raw33078; decide +kernel
      have hl : raw33078step0Labels = raw33078Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33078 raw33078Labels permutation164 permutation7
    mixedMoment B raw33078step0 raw33078step0Labels = mixedMoment B raw33078step1 raw33078step1Labels := by
      have ha : raw33078step1 = -raw33078step0 := by apply Matrix.ext; change ∀ i j, raw33078step1 i j = -(raw33078step0 i j); unfold raw33078step1 raw33078step0; decide +kernel
      have hl : raw33078step1Labels = raw33078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33078step1 raw33078step1Labels = mixedMoment B raw33078step2 raw33078step2Labels := by
      have ha : raw33078step2 = raw33078step1 := by apply Matrix.ext; unfold raw33078step2 raw33078step1; decide +kernel
      have hl : raw33078step1Labels = labelEmbedding1 ∘ raw33078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33078step1 raw33078step1Labels raw33078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3469 node3469Labels := by rfl

theorem canonical33079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33079 raw33079Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw33079 raw33079Labels = mixedMoment B raw33079step0 raw33079step0Labels := by
      have ha : raw33079step0 = (fun i j => raw33079 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33079step0 raw33079; decide +kernel
      have hl : raw33079step0Labels = raw33079Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33079 raw33079Labels permutation164 permutation7
    mixedMoment B raw33079step0 raw33079step0Labels = mixedMoment B raw33079step1 raw33079step1Labels := by
      have ha : raw33079step1 = -raw33079step0 := by apply Matrix.ext; change ∀ i j, raw33079step1 i j = -(raw33079step0 i j); unfold raw33079step1 raw33079step0; decide +kernel
      have hl : raw33079step1Labels = raw33079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33079step1 raw33079step1Labels = mixedMoment B raw33079step2 raw33079step2Labels := by
      have ha : raw33079step2 = raw33079step1 := by apply Matrix.ext; unfold raw33079step2 raw33079step1; decide +kernel
      have hl : raw33079step1Labels = labelEmbedding1 ∘ raw33079step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33079step1 raw33079step1Labels raw33079step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

theorem canonical33080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33080 raw33080Labels = mixedMoment B node3409 node3409Labels := by
  calc
    mixedMoment B raw33080 raw33080Labels = mixedMoment B raw33080step0 raw33080step0Labels := by
      have ha : raw33080step0 = (fun i j => raw33080 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33080step0 raw33080; decide +kernel
      have hl : raw33080step0Labels = raw33080Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33080 raw33080Labels permutation164 permutation7
    mixedMoment B raw33080step0 raw33080step0Labels = mixedMoment B raw33080step1 raw33080step1Labels := by
      have ha : raw33080step1 = -raw33080step0 := by apply Matrix.ext; change ∀ i j, raw33080step1 i j = -(raw33080step0 i j); unfold raw33080step1 raw33080step0; decide +kernel
      have hl : raw33080step1Labels = raw33080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33080step1 raw33080step1Labels = mixedMoment B raw33080step2 raw33080step2Labels := by
      have ha : raw33080step2 = raw33080step1 := by apply Matrix.ext; unfold raw33080step2 raw33080step1; decide +kernel
      have hl : raw33080step1Labels = labelEmbedding1 ∘ raw33080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33080step1 raw33080step1Labels raw33080step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3409 node3409Labels := by rfl

theorem canonical33081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33081 raw33081Labels = mixedMoment B node3465 node3465Labels := by
  calc
    mixedMoment B raw33081 raw33081Labels = mixedMoment B raw33081step0 raw33081step0Labels := by
      have ha : raw33081step0 = (fun i j => raw33081 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33081step0 raw33081; decide +kernel
      have hl : raw33081step0Labels = raw33081Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33081 raw33081Labels permutation164 permutation7
    mixedMoment B raw33081step0 raw33081step0Labels = mixedMoment B raw33081step1 raw33081step1Labels := by
      have ha : raw33081step1 = -raw33081step0 := by apply Matrix.ext; change ∀ i j, raw33081step1 i j = -(raw33081step0 i j); unfold raw33081step1 raw33081step0; decide +kernel
      have hl : raw33081step1Labels = raw33081step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33081step1 raw33081step1Labels = mixedMoment B raw33081step2 raw33081step2Labels := by
      have ha : raw33081step2 = raw33081step1 := by apply Matrix.ext; unfold raw33081step2 raw33081step1; decide +kernel
      have hl : raw33081step1Labels = labelEmbedding1 ∘ raw33081step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33081step1 raw33081step1Labels raw33081step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3465 node3465Labels := by rfl

theorem canonical33082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33082 raw33082Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw33082 raw33082Labels = mixedMoment B raw33082step0 raw33082step0Labels := by
      have hz : ∀ j, raw33082 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33082step0 = (fun i j => raw33082 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33082step0 raw33082; decide +kernel
      have hl : raw33082step0Labels = raw33082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33082 raw33082Labels permutation520 hz
    mixedMoment B raw33082step0 raw33082step0Labels = mixedMoment B raw33082step1 raw33082step1Labels := by
      have ha : raw33082step1 = (fun i j => raw33082step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33082step1 raw33082step0; decide +kernel
      have hl : raw33082step1Labels = raw33082step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33082step0 raw33082step0Labels permutation32 permutation7
    mixedMoment B raw33082step1 raw33082step1Labels = mixedMoment B raw33082step2 raw33082step2Labels := by
      have ha : raw33082step2 = -raw33082step1 := by apply Matrix.ext; change ∀ i j, raw33082step2 i j = -(raw33082step1 i j); unfold raw33082step2 raw33082step1; decide +kernel
      have hl : raw33082step2Labels = raw33082step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33082step2 raw33082step2Labels = mixedMoment B raw33082step3 raw33082step3Labels := by
      have ha : raw33082step3 = raw33082step2 := by apply Matrix.ext; unfold raw33082step3 raw33082step2; decide +kernel
      have hl : raw33082step2Labels = labelEmbedding1 ∘ raw33082step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33082step2 raw33082step2Labels raw33082step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

theorem canonical33083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33083 raw33083Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw33083 raw33083Labels = mixedMoment B raw33083step0 raw33083step0Labels := by
      have ha : raw33083step0 = (fun i j => raw33083 (permutation165 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33083step0 raw33083; decide +kernel
      have hl : raw33083step0Labels = raw33083Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33083 raw33083Labels permutation165 permutation7
    mixedMoment B raw33083step0 raw33083step0Labels = mixedMoment B raw33083step1 raw33083step1Labels := by
      have ha : raw33083step1 = -raw33083step0 := by apply Matrix.ext; change ∀ i j, raw33083step1 i j = -(raw33083step0 i j); unfold raw33083step1 raw33083step0; decide +kernel
      have hl : raw33083step1Labels = raw33083step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33083step1 raw33083step1Labels = mixedMoment B raw33083step2 raw33083step2Labels := by
      have ha : raw33083step2 = raw33083step1 := by apply Matrix.ext; unfold raw33083step2 raw33083step1; decide +kernel
      have hl : raw33083step1Labels = labelEmbedding1 ∘ raw33083step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33083step1 raw33083step1Labels raw33083step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

theorem canonical33084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33084 raw33084Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw33084 raw33084Labels = mixedMoment B raw33084step0 raw33084step0Labels := by
      have ha : raw33084step0 = (fun i j => raw33084 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33084step0 raw33084; decide +kernel
      have hl : raw33084step0Labels = raw33084Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33084 raw33084Labels permutation164 permutation7
    mixedMoment B raw33084step0 raw33084step0Labels = mixedMoment B raw33084step1 raw33084step1Labels := by
      have ha : raw33084step1 = -raw33084step0 := by apply Matrix.ext; change ∀ i j, raw33084step1 i j = -(raw33084step0 i j); unfold raw33084step1 raw33084step0; decide +kernel
      have hl : raw33084step1Labels = raw33084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33084step1 raw33084step1Labels = mixedMoment B raw33084step2 raw33084step2Labels := by
      have ha : raw33084step2 = raw33084step1 := by apply Matrix.ext; unfold raw33084step2 raw33084step1; decide +kernel
      have hl : raw33084step1Labels = labelEmbedding1 ∘ raw33084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33084step1 raw33084step1Labels raw33084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

theorem canonical33085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33085 raw33085Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw33085 raw33085Labels = mixedMoment B raw33085step0 raw33085step0Labels := by
      have ha : raw33085step0 = (fun i j => raw33085 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33085step0 raw33085; decide +kernel
      have hl : raw33085step0Labels = raw33085Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33085 raw33085Labels permutation164 permutation7
    mixedMoment B raw33085step0 raw33085step0Labels = mixedMoment B raw33085step1 raw33085step1Labels := by
      have ha : raw33085step1 = -raw33085step0 := by apply Matrix.ext; change ∀ i j, raw33085step1 i j = -(raw33085step0 i j); unfold raw33085step1 raw33085step0; decide +kernel
      have hl : raw33085step1Labels = raw33085step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33085step1 raw33085step1Labels = mixedMoment B raw33085step2 raw33085step2Labels := by
      have ha : raw33085step2 = raw33085step1 := by apply Matrix.ext; unfold raw33085step2 raw33085step1; decide +kernel
      have hl : raw33085step1Labels = labelEmbedding1 ∘ raw33085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33085step1 raw33085step1Labels raw33085step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

theorem canonical33086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33086 raw33086Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw33086 raw33086Labels = mixedMoment B raw33086step0 raw33086step0Labels := by
      have ha : raw33086step0 = (fun i j => raw33086 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33086step0 raw33086; decide +kernel
      have hl : raw33086step0Labels = raw33086Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33086 raw33086Labels permutation164 permutation7
    mixedMoment B raw33086step0 raw33086step0Labels = mixedMoment B raw33086step1 raw33086step1Labels := by
      have ha : raw33086step1 = -raw33086step0 := by apply Matrix.ext; change ∀ i j, raw33086step1 i j = -(raw33086step0 i j); unfold raw33086step1 raw33086step0; decide +kernel
      have hl : raw33086step1Labels = raw33086step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33086step1 raw33086step1Labels = mixedMoment B raw33086step2 raw33086step2Labels := by
      have ha : raw33086step2 = raw33086step1 := by apply Matrix.ext; unfold raw33086step2 raw33086step1; decide +kernel
      have hl : raw33086step1Labels = labelEmbedding1 ∘ raw33086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33086step1 raw33086step1Labels raw33086step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

theorem canonical33087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33087 raw33087Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw33087 raw33087Labels = mixedMoment B raw33087step0 raw33087step0Labels := by
      have ha : raw33087step0 = (fun i j => raw33087 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33087step0 raw33087; decide +kernel
      have hl : raw33087step0Labels = raw33087Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33087 raw33087Labels permutation164 permutation7
    mixedMoment B raw33087step0 raw33087step0Labels = mixedMoment B raw33087step1 raw33087step1Labels := by
      have ha : raw33087step1 = -raw33087step0 := by apply Matrix.ext; change ∀ i j, raw33087step1 i j = -(raw33087step0 i j); unfold raw33087step1 raw33087step0; decide +kernel
      have hl : raw33087step1Labels = raw33087step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33087step1 raw33087step1Labels = mixedMoment B raw33087step2 raw33087step2Labels := by
      have ha : raw33087step2 = raw33087step1 := by apply Matrix.ext; unfold raw33087step2 raw33087step1; decide +kernel
      have hl : raw33087step1Labels = labelEmbedding1 ∘ raw33087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33087step1 raw33087step1Labels raw33087step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

theorem canonical33088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33088 raw33088Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw33088 raw33088Labels = mixedMoment B raw33088step0 raw33088step0Labels := by
      have ha : raw33088step0 = (fun i j => raw33088 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33088step0 raw33088; decide +kernel
      have hl : raw33088step0Labels = raw33088Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33088 raw33088Labels permutation164 permutation7
    mixedMoment B raw33088step0 raw33088step0Labels = mixedMoment B raw33088step1 raw33088step1Labels := by
      have ha : raw33088step1 = -raw33088step0 := by apply Matrix.ext; change ∀ i j, raw33088step1 i j = -(raw33088step0 i j); unfold raw33088step1 raw33088step0; decide +kernel
      have hl : raw33088step1Labels = raw33088step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33088step1 raw33088step1Labels = mixedMoment B raw33088step2 raw33088step2Labels := by
      have ha : raw33088step2 = raw33088step1 := by apply Matrix.ext; unfold raw33088step2 raw33088step1; decide +kernel
      have hl : raw33088step1Labels = labelEmbedding1 ∘ raw33088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33088step1 raw33088step1Labels raw33088step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

theorem canonical33089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33089 raw33089Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw33089 raw33089Labels = mixedMoment B raw33089step0 raw33089step0Labels := by
      have ha : raw33089step0 = (fun i j => raw33089 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33089step0 raw33089; decide +kernel
      have hl : raw33089step0Labels = raw33089Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33089 raw33089Labels permutation164 permutation7
    mixedMoment B raw33089step0 raw33089step0Labels = mixedMoment B raw33089step1 raw33089step1Labels := by
      have ha : raw33089step1 = -raw33089step0 := by apply Matrix.ext; change ∀ i j, raw33089step1 i j = -(raw33089step0 i j); unfold raw33089step1 raw33089step0; decide +kernel
      have hl : raw33089step1Labels = raw33089step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33089step1 raw33089step1Labels = mixedMoment B raw33089step2 raw33089step2Labels := by
      have ha : raw33089step2 = raw33089step1 := by apply Matrix.ext; unfold raw33089step2 raw33089step1; decide +kernel
      have hl : raw33089step1Labels = labelEmbedding1 ∘ raw33089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33089step1 raw33089step1Labels raw33089step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

theorem canonical33090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33090 raw33090Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw33090 raw33090Labels = mixedMoment B raw33090step0 raw33090step0Labels := by
      have ha : raw33090step0 = (fun i j => raw33090 (permutation685 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33090step0 raw33090; decide +kernel
      have hl : raw33090step0Labels = raw33090Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33090 raw33090Labels permutation685 permutation5
    mixedMoment B raw33090step0 raw33090step0Labels = mixedMoment B raw33090step1 raw33090step1Labels := by
      have ha : raw33090step1 = raw33090step0 := by apply Matrix.ext; unfold raw33090step1 raw33090step0; decide +kernel
      have hl : raw33090step0Labels = labelEmbedding1 ∘ raw33090step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33090step0 raw33090step0Labels raw33090step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

theorem canonical33091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33091 raw33091Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw33091 raw33091Labels = mixedMoment B raw33091step0 raw33091step0Labels := by
      have hz : ∀ j, raw33091 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33091step0 = (fun i j => raw33091 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33091step0 raw33091; decide +kernel
      have hl : raw33091step0Labels = raw33091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33091 raw33091Labels permutation520 hz
    mixedMoment B raw33091step0 raw33091step0Labels = mixedMoment B raw33091step1 raw33091step1Labels := by
      have ha : raw33091step1 = (fun i j => raw33091step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33091step1 raw33091step0; decide +kernel
      have hl : raw33091step1Labels = raw33091step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33091step0 raw33091step0Labels permutation32 permutation7
    mixedMoment B raw33091step1 raw33091step1Labels = mixedMoment B raw33091step2 raw33091step2Labels := by
      have ha : raw33091step2 = -raw33091step1 := by apply Matrix.ext; change ∀ i j, raw33091step2 i j = -(raw33091step1 i j); unfold raw33091step2 raw33091step1; decide +kernel
      have hl : raw33091step2Labels = raw33091step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33091step2 raw33091step2Labels = mixedMoment B raw33091step3 raw33091step3Labels := by
      have ha : raw33091step3 = raw33091step2 := by apply Matrix.ext; unfold raw33091step3 raw33091step2; decide +kernel
      have hl : raw33091step2Labels = labelEmbedding1 ∘ raw33091step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33091step2 raw33091step2Labels raw33091step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7163 raw7163Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw7163 raw7163Labels = mixedMoment B raw7163step0 raw7163step0Labels := by
      have ha : raw7163step0 = (fun i j => raw7163 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7163step0 raw7163; decide +kernel
      have hl : raw7163step0Labels = raw7163Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7163 raw7163Labels permutation164 permutation7
    mixedMoment B raw7163step0 raw7163step0Labels = mixedMoment B raw7163step1 raw7163step1Labels := by
      have ha : raw7163step1 = -raw7163step0 := by apply Matrix.ext; change ∀ i j, raw7163step1 i j = -(raw7163step0 i j); unfold raw7163step1 raw7163step0; decide +kernel
      have hl : raw7163step1Labels = raw7163step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7163step1 raw7163step1Labels = mixedMoment B raw7163step2 raw7163step2Labels := by
      have ha : raw7163step2 = raw7163step1 := by apply Matrix.ext; unfold raw7163step2 raw7163step1; decide +kernel
      have hl : raw7163step1Labels = labelEmbedding1 ∘ raw7163step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7163step1 raw7163step1Labels raw7163step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7174 raw7174Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw7174 raw7174Labels = mixedMoment B raw7174step0 raw7174step0Labels := by
      have ha : raw7174step0 = (fun i j => raw7174 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7174step0 raw7174; decide +kernel
      have hl : raw7174step0Labels = raw7174Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7174 raw7174Labels permutation166 permutation7
    mixedMoment B raw7174step0 raw7174step0Labels = mixedMoment B raw7174step1 raw7174step1Labels := by
      have ha : raw7174step1 = -raw7174step0 := by apply Matrix.ext; change ∀ i j, raw7174step1 i j = -(raw7174step0 i j); unfold raw7174step1 raw7174step0; decide +kernel
      have hl : raw7174step1Labels = raw7174step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7174step1 raw7174step1Labels = mixedMoment B raw7174step2 raw7174step2Labels := by
      have ha : raw7174step2 = raw7174step1 := by apply Matrix.ext; unfold raw7174step2 raw7174step1; decide +kernel
      have hl : raw7174step1Labels = labelEmbedding1 ∘ raw7174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7174step1 raw7174step1Labels raw7174step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

theorem canonical7178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7178 raw7178Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw7178 raw7178Labels = mixedMoment B raw7178step0 raw7178step0Labels := by
      have ha : raw7178step0 = (fun i j => raw7178 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7178step0 raw7178; decide +kernel
      have hl : raw7178step0Labels = raw7178Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7178 raw7178Labels permutation182 permutation5
    mixedMoment B raw7178step0 raw7178step0Labels = mixedMoment B raw7178step1 raw7178step1Labels := by
      have ha : raw7178step1 = -raw7178step0 := by apply Matrix.ext; change ∀ i j, raw7178step1 i j = -(raw7178step0 i j); unfold raw7178step1 raw7178step0; decide +kernel
      have hl : raw7178step1Labels = raw7178step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7178step1 raw7178step1Labels = mixedMoment B raw7178step2 raw7178step2Labels := by
      have ha : raw7178step2 = raw7178step1 := by apply Matrix.ext; unfold raw7178step2 raw7178step1; decide +kernel
      have hl : raw7178step1Labels = labelEmbedding1 ∘ raw7178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7178step1 raw7178step1Labels raw7178step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical7180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7180 raw7180Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw7180 raw7180Labels = mixedMoment B raw7180step0 raw7180step0Labels := by
      have ha : raw7180step0 = (fun i j => raw7180 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7180step0 raw7180; decide +kernel
      have hl : raw7180step0Labels = raw7180Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7180 raw7180Labels permutation164 permutation7
    mixedMoment B raw7180step0 raw7180step0Labels = mixedMoment B raw7180step1 raw7180step1Labels := by
      have ha : raw7180step1 = -raw7180step0 := by apply Matrix.ext; change ∀ i j, raw7180step1 i j = -(raw7180step0 i j); unfold raw7180step1 raw7180step0; decide +kernel
      have hl : raw7180step1Labels = raw7180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7180step1 raw7180step1Labels = mixedMoment B raw7180step2 raw7180step2Labels := by
      have ha : raw7180step2 = raw7180step1 := by apply Matrix.ext; unfold raw7180step2 raw7180step1; decide +kernel
      have hl : raw7180step1Labels = labelEmbedding1 ∘ raw7180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7180step1 raw7180step1Labels raw7180step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

theorem canonical7181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7181 raw7181Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw7181 raw7181Labels = mixedMoment B raw7181step0 raw7181step0Labels := by
      have hz : ∀ j, raw7181 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7181step0 = (fun i j => raw7181 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7181step0 raw7181; decide +kernel
      have hl : raw7181step0Labels = raw7181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7181 raw7181Labels permutation520 hz
    mixedMoment B raw7181step0 raw7181step0Labels = mixedMoment B raw7181step1 raw7181step1Labels := by
      have ha : raw7181step1 = (fun i j => raw7181step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7181step1 raw7181step0; decide +kernel
      have hl : raw7181step1Labels = raw7181step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7181step0 raw7181step0Labels permutation32 permutation7
    mixedMoment B raw7181step1 raw7181step1Labels = mixedMoment B raw7181step2 raw7181step2Labels := by
      have ha : raw7181step2 = -raw7181step1 := by apply Matrix.ext; change ∀ i j, raw7181step2 i j = -(raw7181step1 i j); unfold raw7181step2 raw7181step1; decide +kernel
      have hl : raw7181step2Labels = raw7181step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7181step2 raw7181step2Labels = mixedMoment B raw7181step3 raw7181step3Labels := by
      have ha : raw7181step3 = raw7181step2 := by apply Matrix.ext; unfold raw7181step3 raw7181step2; decide +kernel
      have hl : raw7181step2Labels = labelEmbedding1 ∘ raw7181step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7181step2 raw7181step2Labels raw7181step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical7182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7182 raw7182Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw7182 raw7182Labels = mixedMoment B raw7182step0 raw7182step0Labels := by
      have ha : raw7182step0 = (fun i j => raw7182 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7182step0 raw7182; decide +kernel
      have hl : raw7182step0Labels = raw7182Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7182 raw7182Labels permutation164 permutation7
    mixedMoment B raw7182step0 raw7182step0Labels = mixedMoment B raw7182step1 raw7182step1Labels := by
      have ha : raw7182step1 = -raw7182step0 := by apply Matrix.ext; change ∀ i j, raw7182step1 i j = -(raw7182step0 i j); unfold raw7182step1 raw7182step0; decide +kernel
      have hl : raw7182step1Labels = raw7182step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7182step1 raw7182step1Labels = mixedMoment B raw7182step2 raw7182step2Labels := by
      have ha : raw7182step2 = raw7182step1 := by apply Matrix.ext; unfold raw7182step2 raw7182step1; decide +kernel
      have hl : raw7182step1Labels = labelEmbedding1 ∘ raw7182step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7182step1 raw7182step1Labels raw7182step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical7184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7184 raw7184Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw7184 raw7184Labels = mixedMoment B raw7184step0 raw7184step0Labels := by
      have ha : raw7184step0 = (fun i j => raw7184 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7184step0 raw7184; decide +kernel
      have hl : raw7184step0Labels = raw7184Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7184 raw7184Labels permutation164 permutation7
    mixedMoment B raw7184step0 raw7184step0Labels = mixedMoment B raw7184step1 raw7184step1Labels := by
      have ha : raw7184step1 = -raw7184step0 := by apply Matrix.ext; change ∀ i j, raw7184step1 i j = -(raw7184step0 i j); unfold raw7184step1 raw7184step0; decide +kernel
      have hl : raw7184step1Labels = raw7184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7184step1 raw7184step1Labels = mixedMoment B raw7184step2 raw7184step2Labels := by
      have ha : raw7184step2 = raw7184step1 := by apply Matrix.ext; unfold raw7184step2 raw7184step1; decide +kernel
      have hl : raw7184step1Labels = labelEmbedding1 ∘ raw7184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7184step1 raw7184step1Labels raw7184step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

theorem canonical7189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7189 raw7189Labels = mixedMoment B node3466 node3466Labels := by
  calc
    mixedMoment B raw7189 raw7189Labels = mixedMoment B raw7189step0 raw7189step0Labels := by
      have ha : raw7189step0 = (fun i j => raw7189 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7189step0 raw7189; decide +kernel
      have hl : raw7189step0Labels = raw7189Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7189 raw7189Labels permutation674 permutation5
    mixedMoment B raw7189step0 raw7189step0Labels = mixedMoment B raw7189step1 raw7189step1Labels := by
      have ha : raw7189step1 = raw7189step0 := by apply Matrix.ext; unfold raw7189step1 raw7189step0; decide +kernel
      have hl : raw7189step0Labels = labelEmbedding1 ∘ raw7189step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7189step0 raw7189step0Labels raw7189step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3466 node3466Labels := by rfl

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

theorem sound3267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3267 node3267Labels = Sparse.eval nodeValue3267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3267) = mixedMoment B node3267 node3267Labels := rfl
  simpa [nodeValue3267, Sparse.eval] using hc.symm

theorem sound3290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3290 node3290Labels = Sparse.eval nodeValue3290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3290) = mixedMoment B node3290 node3290Labels := rfl
  simpa [nodeValue3290, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3409 node3409Labels = 0 := by
  exact mixedMoment_alpha B hF node3409 node3409Labels 1 permutation487
    (by decide +kernel)

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

theorem sound3408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3408 node3408Labels = Sparse.eval nodeValue3408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3408) = mixedMoment B node3408 node3408Labels := rfl
  simpa [nodeValue3408, Sparse.eval] using hc.symm

theorem sound3409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3409 node3409Labels = Sparse.eval nodeValue3409 (mixedVector B) := by
  simpa only [nodeValue3409, Sparse.eval_nil] using zero3409 B _hB _hF

theorem sound3410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3410 node3410Labels = Sparse.eval nodeValue3410 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3410) = mixedMoment B node3410 node3410Labels := rfl
  simpa [nodeValue3410, Sparse.eval] using hc.symm

theorem sound3414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3414 node3414Labels = Sparse.eval nodeValue3414 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3414) = mixedMoment B node3414 node3414Labels := rfl
  simpa [nodeValue3414, Sparse.eval] using hc.symm

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

theorem zero3469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3469 node3469Labels = 0 := by
  exact mixedMoment_order_one B hB node3469 node3469Labels 1
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

theorem sound3465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3465 node3465Labels = Sparse.eval nodeValue3465 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3465) = mixedMoment B node3465 node3465Labels := rfl
  simpa [nodeValue3465, Sparse.eval] using hc.symm

theorem sound3466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3466 node3466Labels = Sparse.eval nodeValue3466 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3466) = mixedMoment B node3466 node3466Labels := rfl
  simpa [nodeValue3466, Sparse.eval] using hc.symm

theorem sound3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3467 node3467Labels = Sparse.eval nodeValue3467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3467) = mixedMoment B node3467 node3467Labels := rfl
  simpa [nodeValue3467, Sparse.eval] using hc.symm

theorem sound3469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3469 node3469Labels = Sparse.eval nodeValue3469 (mixedVector B) := by
  simpa only [nodeValue3469, Sparse.eval_nil] using zero3469 B _hB _hF

theorem sound3474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3474 node3474Labels = Sparse.eval nodeValue3474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3474) = mixedMoment B node3474 node3474Labels := rfl
  simpa [nodeValue3474, Sparse.eval] using hc.symm

theorem sound3476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3476 node3476Labels = Sparse.eval nodeValue3476 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3476) = mixedMoment B node3476 node3476Labels := rfl
  simpa [nodeValue3476, Sparse.eval] using hc.symm

theorem sound3477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3477 node3477Labels = Sparse.eval nodeValue3477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3477) = mixedMoment B node3477 node3477Labels := rfl
  simpa [nodeValue3477, Sparse.eval] using hc.symm

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

theorem sound3482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3482 node3482Labels = Sparse.eval nodeValue3482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3482) = mixedMoment B node3482 node3482Labels := rfl
  simpa [nodeValue3482, Sparse.eval] using hc.symm

theorem sound3483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3483 node3483Labels = Sparse.eval nodeValue3483 (mixedVector B) := by
  simpa only [nodeValue3483, Sparse.eval_nil] using zero3483 B _hB _hF

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

theorem zero3531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3531 node3531Labels = 0 := by
  exact mixedMoment_alpha B hF node3531 node3531Labels 1 permutation437
    (by decide +kernel)

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

theorem sound3529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3529 node3529Labels = Sparse.eval nodeValue3529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3529) = mixedMoment B node3529 node3529Labels := rfl
  simpa [nodeValue3529, Sparse.eval] using hc.symm

theorem sound3531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3531 node3531Labels = Sparse.eval nodeValue3531 (mixedVector B) := by
  simpa only [nodeValue3531, Sparse.eval_nil] using zero3531 B _hB _hF

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

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

theorem sound3764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3764 node3764Labels = Sparse.eval nodeValue3764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3764) = mixedMoment B node3764 node3764Labels := rfl
  simpa [nodeValue3764, Sparse.eval] using hc.symm

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

theorem zero3806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = 0 := by
  exact mixedMoment_order_one B hB node3806 node3806Labels 1
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

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3805 node3805Labels = Sparse.eval nodeValue3805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3805) = mixedMoment B node3805 node3805Labels := rfl
  simpa [nodeValue3805, Sparse.eval] using hc.symm

theorem sound3806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = Sparse.eval nodeValue3806 (mixedVector B) := by
  simpa only [nodeValue3806, Sparse.eval_nil] using zero3806 B _hB _hF

theorem sound3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = Sparse.eval nodeValue3816 (mixedVector B) := by
  simpa only [nodeValue3816, Sparse.eval_nil] using zero3816 B _hB _hF

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

theorem sourceEq2411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2411 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2411 + difference 0 1) (sourceB2411 + difference 1 0) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2411 + difference 0 1) (sourceB2411 + difference 1 0) sourceC2411) = raw33070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33070; decide +kernel
    rw [ha]
    exact (canonical33070 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2411 + difference 0 2) (sourceB2411 + difference 2 0) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2411 + difference 0 2) (sourceB2411 + difference 2 0) sourceC2411) = raw33071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33071; decide +kernel
    rw [ha]
    exact (canonical33071 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2411 + difference 0 3) (sourceB2411 + difference 3 0) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA2411 + difference 0 3) (sourceB2411 + difference 3 0) sourceC2411) = raw7163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7163; decide +kernel
    rw [ha]
    exact (canonical7163 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2411 + difference 0 4) (sourceB2411 + difference 4 0) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2411 + difference 0 4) (sourceB2411 + difference 4 0) sourceC2411) = raw33072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33072; decide +kernel
    rw [ha]
    exact (canonical33072 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2411 + difference 0 5) (sourceB2411 + difference 5 0) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA2411 + difference 0 5) (sourceB2411 + difference 5 0) sourceC2411) = raw33073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33073; decide +kernel
    rw [ha]
    exact (canonical33073 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2411 + difference 1 0) (sourceB2411 + difference 0 1) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA2411 + difference 1 0) (sourceB2411 + difference 0 1) sourceC2411) = raw7178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7178; decide +kernel
    rw [ha]
    exact (canonical7178 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2411 + difference 1 2) (sourceB2411 + difference 2 1) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA2411 + difference 1 2) (sourceB2411 + difference 2 1) sourceC2411) = raw7180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7180; decide +kernel
    rw [ha]
    exact (canonical7180 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2411 + difference 1 3) (sourceB2411 + difference 3 1) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA2411 + difference 1 3) (sourceB2411 + difference 3 1) sourceC2411) = raw33074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33074; decide +kernel
    rw [ha]
    exact (canonical33074 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2411 + difference 1 4) (sourceB2411 + difference 4 1) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA2411 + difference 1 4) (sourceB2411 + difference 4 1) sourceC2411) = raw7181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7181; decide +kernel
    rw [ha]
    exact (canonical7181 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2411 + difference 1 5) (sourceB2411 + difference 5 1) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA2411 + difference 1 5) (sourceB2411 + difference 5 1) sourceC2411) = raw7182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7182; decide +kernel
    rw [ha]
    exact (canonical7182 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2411 + difference 2 0) (sourceB2411 + difference 0 2) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3263) := by
    have ha : (tripleCharges (sourceA2411 + difference 2 0) (sourceB2411 + difference 0 2) sourceC2411) = raw33075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33075; decide +kernel
    rw [ha]
    exact (canonical33075 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2411 + difference 2 1) (sourceB2411 + difference 1 2) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3410) := by
    have ha : (tripleCharges (sourceA2411 + difference 2 1) (sourceB2411 + difference 1 2) sourceC2411) = raw33076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33076; decide +kernel
    rw [ha]
    exact (canonical33076 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2411 + difference 2 3) (sourceB2411 + difference 3 2) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA2411 + difference 2 3) (sourceB2411 + difference 3 2) sourceC2411) = raw7174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7174; decide +kernel
    rw [ha]
    exact (canonical7174 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2411 + difference 2 4) (sourceB2411 + difference 4 2) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA2411 + difference 2 4) (sourceB2411 + difference 4 2) sourceC2411) = raw33077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33077; decide +kernel
    rw [ha]
    exact (canonical33077 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2411 + difference 2 5) (sourceB2411 + difference 5 2) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3469) := by
    have ha : (tripleCharges (sourceA2411 + difference 2 5) (sourceB2411 + difference 5 2) sourceC2411) = raw33078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33078; decide +kernel
    rw [ha]
    exact (canonical33078 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2411 + difference 3 0) (sourceB2411 + difference 0 3) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA2411 + difference 3 0) (sourceB2411 + difference 0 3) sourceC2411) = raw33079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33079; decide +kernel
    rw [ha]
    exact (canonical33079 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2411 + difference 3 1) (sourceB2411 + difference 1 3) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3409) := by
    have ha : (tripleCharges (sourceA2411 + difference 3 1) (sourceB2411 + difference 1 3) sourceC2411) = raw33080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33080; decide +kernel
    rw [ha]
    exact (canonical33080 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2411 + difference 3 2) (sourceB2411 + difference 2 3) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3465) := by
    have ha : (tripleCharges (sourceA2411 + difference 3 2) (sourceB2411 + difference 2 3) sourceC2411) = raw33081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33081; decide +kernel
    rw [ha]
    exact (canonical33081 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2411 + difference 3 4) (sourceB2411 + difference 4 3) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2411 + difference 3 4) (sourceB2411 + difference 4 3) sourceC2411) = raw33082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33082; decide +kernel
    rw [ha]
    exact (canonical33082 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2411 + difference 3 5) (sourceB2411 + difference 5 3) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA2411 + difference 3 5) (sourceB2411 + difference 5 3) sourceC2411) = raw33083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33083; decide +kernel
    rw [ha]
    exact (canonical33083 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2411 + difference 4 0) (sourceB2411 + difference 0 4) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3267) := by
    have ha : (tripleCharges (sourceA2411 + difference 4 0) (sourceB2411 + difference 0 4) sourceC2411) = raw33084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33084; decide +kernel
    rw [ha]
    exact (canonical33084 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2411 + difference 4 1) (sourceB2411 + difference 1 4) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2411 + difference 4 1) (sourceB2411 + difference 1 4) sourceC2411) = raw33085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33085; decide +kernel
    rw [ha]
    exact (canonical33085 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2411 + difference 4 2) (sourceB2411 + difference 2 4) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2411 + difference 4 2) (sourceB2411 + difference 2 4) sourceC2411) = raw33086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33086; decide +kernel
    rw [ha]
    exact (canonical33086 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2411 + difference 4 3) (sourceB2411 + difference 3 4) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2411 + difference 4 3) (sourceB2411 + difference 3 4) sourceC2411) = raw7184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7184; decide +kernel
    rw [ha]
    exact (canonical7184 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2411 + difference 4 5) (sourceB2411 + difference 5 4) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3477) := by
    have ha : (tripleCharges (sourceA2411 + difference 4 5) (sourceB2411 + difference 5 4) sourceC2411) = raw33087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33087; decide +kernel
    rw [ha]
    exact (canonical33087 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2411 + difference 5 0) (sourceB2411 + difference 0 5) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA2411 + difference 5 0) (sourceB2411 + difference 0 5) sourceC2411) = raw33088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33088; decide +kernel
    rw [ha]
    exact (canonical33088 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2411 + difference 5 1) (sourceB2411 + difference 1 5) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2411 + difference 5 1) (sourceB2411 + difference 1 5) sourceC2411) = raw33089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33089; decide +kernel
    rw [ha]
    exact (canonical33089 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2411 + difference 5 2) (sourceB2411 + difference 2 5) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3451) := by
    have ha : (tripleCharges (sourceA2411 + difference 5 2) (sourceB2411 + difference 2 5) sourceC2411) = raw33090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33090; decide +kernel
    rw [ha]
    exact (canonical33090 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2411 + difference 5 3) (sourceB2411 + difference 3 5) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA2411 + difference 5 3) (sourceB2411 + difference 3 5) sourceC2411) = raw7189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7189; decide +kernel
    rw [ha]
    exact (canonical7189 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2411 + difference 5 4) (sourceB2411 + difference 4 5) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA2411 + difference 5 4) (sourceB2411 + difference 4 5) sourceC2411) = raw33091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33091; decide +kernel
    rw [ha]
    exact (canonical33091 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2411 sourceB2411 sourceC2411
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2411, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1954 : Integer.Sparse.reindex keyMap MixedData.row1954 = numericRow1954 := by decide +kernel

theorem numericCheck1954 (x : Master → ℝ) : Integer.Sparse.eval numericRow1954 x =
    (1 : ℝ) * reducedSource1954 x := by
  norm_num [numericRow1954, reducedSource1954, Integer.Sparse.eval, Sparse.eval, nodeValue3260, nodeValue3261, nodeValue3263, nodeValue3267, nodeValue3290, nodeValue3408, nodeValue3409, nodeValue3410, nodeValue3414, nodeValue3451, nodeValue3465, nodeValue3466, nodeValue3467, nodeValue3469, nodeValue3474, nodeValue3476, nodeValue3477, nodeValue3481, nodeValue3482, nodeValue3483, nodeValue3529, nodeValue3531, nodeValue3532, nodeValue3544, nodeValue3764, nodeValue3804, nodeValue3805, nodeValue3806, nodeValue3816]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1954 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1954 (mixedVector B) = 0 := by
  have h3260 : mixedVector B (Sum.inr 3260) = Sparse.eval nodeValue3260 (mixedVector B) := by
    change mixedMoment B node3260 node3260Labels = _
    exact sound3260 B hB hF
  have h3261 : mixedVector B (Sum.inr 3261) = Sparse.eval nodeValue3261 (mixedVector B) := by
    change mixedMoment B node3261 node3261Labels = _
    exact sound3261 B hB hF
  have h3263 : mixedVector B (Sum.inr 3263) = Sparse.eval nodeValue3263 (mixedVector B) := by
    change mixedMoment B node3263 node3263Labels = _
    exact sound3263 B hB hF
  have h3267 : mixedVector B (Sum.inr 3267) = Sparse.eval nodeValue3267 (mixedVector B) := by
    change mixedMoment B node3267 node3267Labels = _
    exact sound3267 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3409 : mixedVector B (Sum.inr 3409) = Sparse.eval nodeValue3409 (mixedVector B) := by
    change mixedMoment B node3409 node3409Labels = _
    exact sound3409 B hB hF
  have h3410 : mixedVector B (Sum.inr 3410) = Sparse.eval nodeValue3410 (mixedVector B) := by
    change mixedMoment B node3410 node3410Labels = _
    exact sound3410 B hB hF
  have h3414 : mixedVector B (Sum.inr 3414) = Sparse.eval nodeValue3414 (mixedVector B) := by
    change mixedMoment B node3414 node3414Labels = _
    exact sound3414 B hB hF
  have h3451 : mixedVector B (Sum.inr 3451) = Sparse.eval nodeValue3451 (mixedVector B) := by
    change mixedMoment B node3451 node3451Labels = _
    exact sound3451 B hB hF
  have h3465 : mixedVector B (Sum.inr 3465) = Sparse.eval nodeValue3465 (mixedVector B) := by
    change mixedMoment B node3465 node3465Labels = _
    exact sound3465 B hB hF
  have h3466 : mixedVector B (Sum.inr 3466) = Sparse.eval nodeValue3466 (mixedVector B) := by
    change mixedMoment B node3466 node3466Labels = _
    exact sound3466 B hB hF
  have h3467 : mixedVector B (Sum.inr 3467) = Sparse.eval nodeValue3467 (mixedVector B) := by
    change mixedMoment B node3467 node3467Labels = _
    exact sound3467 B hB hF
  have h3469 : mixedVector B (Sum.inr 3469) = Sparse.eval nodeValue3469 (mixedVector B) := by
    change mixedMoment B node3469 node3469Labels = _
    exact sound3469 B hB hF
  have h3474 : mixedVector B (Sum.inr 3474) = Sparse.eval nodeValue3474 (mixedVector B) := by
    change mixedMoment B node3474 node3474Labels = _
    exact sound3474 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3477 : mixedVector B (Sum.inr 3477) = Sparse.eval nodeValue3477 (mixedVector B) := by
    change mixedMoment B node3477 node3477Labels = _
    exact sound3477 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3483 : mixedVector B (Sum.inr 3483) = Sparse.eval nodeValue3483 (mixedVector B) := by
    change mixedMoment B node3483 node3483Labels = _
    exact sound3483 B hB hF
  have h3529 : mixedVector B (Sum.inr 3529) = Sparse.eval nodeValue3529 (mixedVector B) := by
    change mixedMoment B node3529 node3529Labels = _
    exact sound3529 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3764 : mixedVector B (Sum.inr 3764) = Sparse.eval nodeValue3764 (mixedVector B) := by
    change mixedMoment B node3764 node3764Labels = _
    exact sound3764 B hB hF
  have h3804 : mixedVector B (Sum.inr 3804) = Sparse.eval nodeValue3804 (mixedVector B) := by
    change mixedMoment B node3804 node3804Labels = _
    exact sound3804 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3806 : mixedVector B (Sum.inr 3806) = Sparse.eval nodeValue3806 (mixedVector B) := by
    change mixedMoment B node3806 node3806Labels = _
    exact sound3806 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  simpa only [sourceForm2411, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3260, h3261, h3263, h3267, h3290, h3408, h3409, h3410, h3414, h3451, h3465, h3466, h3467, h3469, h3474, h3476, h3477, h3481, h3482, h3483, h3529, h3531, h3532, h3544, h3764, h3804, h3805, h3806, h3816, reducedSource1954] using sourceEq2411 B hB

theorem rowSound1954_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1954 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1954, numericCheck1954, reducedZero1954 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954_e_oai
