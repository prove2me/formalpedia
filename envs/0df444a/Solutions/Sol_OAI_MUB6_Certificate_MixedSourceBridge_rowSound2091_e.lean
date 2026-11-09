-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2091_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:04:54.762316+00:00
-- url     : https://prove2.me/submissions/98cee860-bc68-4ed6-b73d-da916cd5e37b

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical286
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36694 raw36694Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw36694 raw36694Labels = mixedMoment B raw36694step0 raw36694step0Labels := by
      have hz : ∀ j, raw36694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36694step0 = (fun i j => raw36694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36694step0 raw36694; decide +kernel
      have hl : raw36694step0Labels = raw36694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36694 raw36694Labels permutation346 hz
    mixedMoment B raw36694step0 raw36694step0Labels = mixedMoment B raw36694step1 raw36694step1Labels := by
      have ha : raw36694step1 = (fun i j => raw36694step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36694step1 raw36694step0; decide +kernel
      have hl : raw36694step1Labels = raw36694step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36694step0 raw36694step0Labels permutation59 permutation7
    mixedMoment B raw36694step1 raw36694step1Labels = mixedMoment B raw36694step2 raw36694step2Labels := by
      have ha : raw36694step2 = -raw36694step1 := by apply Matrix.ext; change ∀ i j, raw36694step2 i j = -(raw36694step1 i j); unfold raw36694step2 raw36694step1; decide +kernel
      have hl : raw36694step2Labels = raw36694step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36694step2 raw36694step2Labels = mixedMoment B raw36694step3 raw36694step3Labels := by
      have ha : raw36694step3 = raw36694step2 := by apply Matrix.ext; unfold raw36694step3 raw36694step2; decide +kernel
      have hl : raw36694step2Labels = labelEmbedding1 ∘ raw36694step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36694step2 raw36694step2Labels raw36694step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

theorem canonical36695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36695 raw36695Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw36695 raw36695Labels = mixedMoment B raw36695step0 raw36695step0Labels := by
      have ha : raw36695step0 = (fun i j => raw36695 (permutation268 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36695step0 raw36695; decide +kernel
      have hl : raw36695step0Labels = raw36695Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36695 raw36695Labels permutation268 permutation7
    mixedMoment B raw36695step0 raw36695step0Labels = mixedMoment B raw36695step1 raw36695step1Labels := by
      have ha : raw36695step1 = -raw36695step0 := by apply Matrix.ext; change ∀ i j, raw36695step1 i j = -(raw36695step0 i j); unfold raw36695step1 raw36695step0; decide +kernel
      have hl : raw36695step1Labels = raw36695step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36695step1 raw36695step1Labels = mixedMoment B raw36695step2 raw36695step2Labels := by
      have ha : raw36695step2 = raw36695step1 := by apply Matrix.ext; unfold raw36695step2 raw36695step1; decide +kernel
      have hl : raw36695step1Labels = labelEmbedding1 ∘ raw36695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36695step1 raw36695step1Labels raw36695step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

theorem canonical36696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36696 raw36696Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw36696 raw36696Labels = mixedMoment B raw36696step0 raw36696step0Labels := by
      have hz : ∀ j, raw36696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36696step0 = (fun i j => raw36696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36696step0 raw36696; decide +kernel
      have hl : raw36696step0Labels = raw36696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36696 raw36696Labels permutation346 hz
    mixedMoment B raw36696step0 raw36696step0Labels = mixedMoment B raw36696step1 raw36696step1Labels := by
      have ha : raw36696step1 = (fun i j => raw36696step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36696step1 raw36696step0; decide +kernel
      have hl : raw36696step1Labels = raw36696step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36696step0 raw36696step0Labels permutation59 permutation7
    mixedMoment B raw36696step1 raw36696step1Labels = mixedMoment B raw36696step2 raw36696step2Labels := by
      have ha : raw36696step2 = -raw36696step1 := by apply Matrix.ext; change ∀ i j, raw36696step2 i j = -(raw36696step1 i j); unfold raw36696step2 raw36696step1; decide +kernel
      have hl : raw36696step2Labels = raw36696step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36696step2 raw36696step2Labels = mixedMoment B raw36696step3 raw36696step3Labels := by
      have ha : raw36696step3 = raw36696step2 := by apply Matrix.ext; unfold raw36696step3 raw36696step2; decide +kernel
      have hl : raw36696step2Labels = labelEmbedding1 ∘ raw36696step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36696step2 raw36696step2Labels raw36696step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical36697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36697 raw36697Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw36697 raw36697Labels = mixedMoment B raw36697step0 raw36697step0Labels := by
      have hz : ∀ j, raw36697 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36697step0 = (fun i j => raw36697 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36697step0 raw36697; decide +kernel
      have hl : raw36697step0Labels = raw36697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36697 raw36697Labels permutation520 hz
    mixedMoment B raw36697step0 raw36697step0Labels = mixedMoment B raw36697step1 raw36697step1Labels := by
      have hz : ∀ j, raw36697step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36697step1 = (fun i j => raw36697step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36697step1 raw36697step0; decide +kernel
      have hl : raw36697step1Labels = raw36697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36697step0 raw36697step0Labels permutation80 hz
    mixedMoment B raw36697step1 raw36697step1Labels = mixedMoment B raw36697step2 raw36697step2Labels := by
      have ha : raw36697step2 = (fun i j => raw36697step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36697step2 raw36697step1; decide +kernel
      have hl : raw36697step2Labels = raw36697step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36697step1 raw36697step1Labels permutation15 permutation7
    mixedMoment B raw36697step2 raw36697step2Labels = mixedMoment B raw36697step3 raw36697step3Labels := by
      have ha : raw36697step3 = -raw36697step2 := by apply Matrix.ext; change ∀ i j, raw36697step3 i j = -(raw36697step2 i j); unfold raw36697step3 raw36697step2; decide +kernel
      have hl : raw36697step3Labels = raw36697step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36697step3 raw36697step3Labels = mixedMoment B raw36697step4 raw36697step4Labels := by
      have ha : raw36697step4 = raw36697step3 := by apply Matrix.ext; unfold raw36697step4 raw36697step3; decide +kernel
      have hl : raw36697step3Labels = labelEmbedding1 ∘ raw36697step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36697step3 raw36697step3Labels raw36697step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

theorem canonical36698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36698 raw36698Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw36698 raw36698Labels = mixedMoment B raw36698step0 raw36698step0Labels := by
      have hz : ∀ j, raw36698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36698step0 = (fun i j => raw36698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36698step0 raw36698; decide +kernel
      have hl : raw36698step0Labels = raw36698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36698 raw36698Labels permutation346 hz
    mixedMoment B raw36698step0 raw36698step0Labels = mixedMoment B raw36698step1 raw36698step1Labels := by
      have ha : raw36698step1 = (fun i j => raw36698step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36698step1 raw36698step0; decide +kernel
      have hl : raw36698step1Labels = raw36698step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36698step0 raw36698step0Labels permutation59 permutation7
    mixedMoment B raw36698step1 raw36698step1Labels = mixedMoment B raw36698step2 raw36698step2Labels := by
      have ha : raw36698step2 = -raw36698step1 := by apply Matrix.ext; change ∀ i j, raw36698step2 i j = -(raw36698step1 i j); unfold raw36698step2 raw36698step1; decide +kernel
      have hl : raw36698step2Labels = raw36698step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36698step2 raw36698step2Labels = mixedMoment B raw36698step3 raw36698step3Labels := by
      have ha : raw36698step3 = raw36698step2 := by apply Matrix.ext; unfold raw36698step3 raw36698step2; decide +kernel
      have hl : raw36698step2Labels = labelEmbedding1 ∘ raw36698step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36698step2 raw36698step2Labels raw36698step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical36699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36699 raw36699Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw36699 raw36699Labels = mixedMoment B raw36699step0 raw36699step0Labels := by
      have hz : ∀ j, raw36699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36699step0 = (fun i j => raw36699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36699step0 raw36699; decide +kernel
      have hl : raw36699step0Labels = raw36699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36699 raw36699Labels permutation346 hz
    mixedMoment B raw36699step0 raw36699step0Labels = mixedMoment B raw36699step1 raw36699step1Labels := by
      have ha : raw36699step1 = (fun i j => raw36699step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36699step1 raw36699step0; decide +kernel
      have hl : raw36699step1Labels = raw36699step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36699step0 raw36699step0Labels permutation38 permutation5
    mixedMoment B raw36699step1 raw36699step1Labels = mixedMoment B raw36699step2 raw36699step2Labels := by
      have ha : raw36699step2 = -raw36699step1 := by apply Matrix.ext; change ∀ i j, raw36699step2 i j = -(raw36699step1 i j); unfold raw36699step2 raw36699step1; decide +kernel
      have hl : raw36699step2Labels = raw36699step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36699step2 raw36699step2Labels = mixedMoment B raw36699step3 raw36699step3Labels := by
      have ha : raw36699step3 = raw36699step2 := by apply Matrix.ext; unfold raw36699step3 raw36699step2; decide +kernel
      have hl : raw36699step2Labels = labelEmbedding1 ∘ raw36699step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36699step2 raw36699step2Labels raw36699step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

theorem canonical36700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36700 raw36700Labels = mixedMoment B node3950 node3950Labels := by
  calc
    mixedMoment B raw36700 raw36700Labels = mixedMoment B raw36700step0 raw36700step0Labels := by
      have ha : raw36700step0 = (fun i j => raw36700 (permutation518 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36700step0 raw36700; decide +kernel
      have hl : raw36700step0Labels = raw36700Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36700 raw36700Labels permutation518 permutation7
    mixedMoment B raw36700step0 raw36700step0Labels = mixedMoment B raw36700step1 raw36700step1Labels := by
      have ha : raw36700step1 = raw36700step0 := by apply Matrix.ext; unfold raw36700step1 raw36700step0; decide +kernel
      have hl : raw36700step0Labels = labelEmbedding1 ∘ raw36700step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36700step0 raw36700step0Labels raw36700step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3950 node3950Labels := by rfl

theorem canonical36701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36701 raw36701Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw36701 raw36701Labels = mixedMoment B raw36701step0 raw36701step0Labels := by
      have hz : ∀ j, raw36701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36701step0 = (fun i j => raw36701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36701step0 raw36701; decide +kernel
      have hl : raw36701step0Labels = raw36701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36701 raw36701Labels permutation346 hz
    mixedMoment B raw36701step0 raw36701step0Labels = mixedMoment B raw36701step1 raw36701step1Labels := by
      have ha : raw36701step1 = (fun i j => raw36701step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36701step1 raw36701step0; decide +kernel
      have hl : raw36701step1Labels = raw36701step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36701step0 raw36701step0Labels permutation59 permutation7
    mixedMoment B raw36701step1 raw36701step1Labels = mixedMoment B raw36701step2 raw36701step2Labels := by
      have ha : raw36701step2 = -raw36701step1 := by apply Matrix.ext; change ∀ i j, raw36701step2 i j = -(raw36701step1 i j); unfold raw36701step2 raw36701step1; decide +kernel
      have hl : raw36701step2Labels = raw36701step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36701step2 raw36701step2Labels = mixedMoment B raw36701step3 raw36701step3Labels := by
      have ha : raw36701step3 = raw36701step2 := by apply Matrix.ext; unfold raw36701step3 raw36701step2; decide +kernel
      have hl : raw36701step2Labels = labelEmbedding1 ∘ raw36701step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36701step2 raw36701step2Labels raw36701step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

theorem canonical36702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36702 raw36702Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw36702 raw36702Labels = mixedMoment B raw36702step0 raw36702step0Labels := by
      have hz : ∀ j, raw36702 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36702step0 = (fun i j => raw36702 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36702step0 raw36702; decide +kernel
      have hl : raw36702step0Labels = raw36702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36702 raw36702Labels permutation520 hz
    mixedMoment B raw36702step0 raw36702step0Labels = mixedMoment B raw36702step1 raw36702step1Labels := by
      have hz : ∀ j, raw36702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36702step1 = (fun i j => raw36702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36702step1 raw36702step0; decide +kernel
      have hl : raw36702step1Labels = raw36702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36702step0 raw36702step0Labels permutation80 hz
    mixedMoment B raw36702step1 raw36702step1Labels = mixedMoment B raw36702step2 raw36702step2Labels := by
      have ha : raw36702step2 = (fun i j => raw36702step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36702step2 raw36702step1; decide +kernel
      have hl : raw36702step2Labels = raw36702step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36702step1 raw36702step1Labels permutation24 permutation7
    mixedMoment B raw36702step2 raw36702step2Labels = mixedMoment B raw36702step3 raw36702step3Labels := by
      have ha : raw36702step3 = raw36702step2 := by apply Matrix.ext; unfold raw36702step3 raw36702step2; decide +kernel
      have hl : raw36702step2Labels = labelEmbedding1 ∘ raw36702step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36702step2 raw36702step2Labels raw36702step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3963 node3963Labels := by rfl

theorem canonical36703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36703 raw36703Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw36703 raw36703Labels = mixedMoment B raw36703step0 raw36703step0Labels := by
      have hz : ∀ j, raw36703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36703step0 = (fun i j => raw36703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36703step0 raw36703; decide +kernel
      have hl : raw36703step0Labels = raw36703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36703 raw36703Labels permutation346 hz
    mixedMoment B raw36703step0 raw36703step0Labels = mixedMoment B raw36703step1 raw36703step1Labels := by
      have ha : raw36703step1 = (fun i j => raw36703step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36703step1 raw36703step0; decide +kernel
      have hl : raw36703step1Labels = raw36703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36703step0 raw36703step0Labels permutation59 permutation7
    mixedMoment B raw36703step1 raw36703step1Labels = mixedMoment B raw36703step2 raw36703step2Labels := by
      have ha : raw36703step2 = -raw36703step1 := by apply Matrix.ext; change ∀ i j, raw36703step2 i j = -(raw36703step1 i j); unfold raw36703step2 raw36703step1; decide +kernel
      have hl : raw36703step2Labels = raw36703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36703step2 raw36703step2Labels = mixedMoment B raw36703step3 raw36703step3Labels := by
      have ha : raw36703step3 = raw36703step2 := by apply Matrix.ext; unfold raw36703step3 raw36703step2; decide +kernel
      have hl : raw36703step2Labels = labelEmbedding1 ∘ raw36703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36703step2 raw36703step2Labels raw36703step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical36704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36704 raw36704Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw36704 raw36704Labels = mixedMoment B raw36704step0 raw36704step0Labels := by
      have ha : raw36704step0 = (fun i j => raw36704 (permutation200 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36704step0 raw36704; decide +kernel
      have hl : raw36704step0Labels = raw36704Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36704 raw36704Labels permutation200 permutation5
    mixedMoment B raw36704step0 raw36704step0Labels = mixedMoment B raw36704step1 raw36704step1Labels := by
      have ha : raw36704step1 = -raw36704step0 := by apply Matrix.ext; change ∀ i j, raw36704step1 i j = -(raw36704step0 i j); unfold raw36704step1 raw36704step0; decide +kernel
      have hl : raw36704step1Labels = raw36704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36704step1 raw36704step1Labels = mixedMoment B raw36704step2 raw36704step2Labels := by
      have ha : raw36704step2 = raw36704step1 := by apply Matrix.ext; unfold raw36704step2 raw36704step1; decide +kernel
      have hl : raw36704step1Labels = labelEmbedding1 ∘ raw36704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36704step1 raw36704step1Labels raw36704step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

theorem canonical36705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36705 raw36705Labels = mixedMoment B node3405 node3405Labels := by
  calc
    mixedMoment B raw36705 raw36705Labels = mixedMoment B raw36705step0 raw36705step0Labels := by
      have ha : raw36705step0 = (fun i j => raw36705 (permutation268 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36705step0 raw36705; decide +kernel
      have hl : raw36705step0Labels = raw36705Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36705 raw36705Labels permutation268 permutation7
    mixedMoment B raw36705step0 raw36705step0Labels = mixedMoment B raw36705step1 raw36705step1Labels := by
      have ha : raw36705step1 = -raw36705step0 := by apply Matrix.ext; change ∀ i j, raw36705step1 i j = -(raw36705step0 i j); unfold raw36705step1 raw36705step0; decide +kernel
      have hl : raw36705step1Labels = raw36705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36705step1 raw36705step1Labels = mixedMoment B raw36705step2 raw36705step2Labels := by
      have ha : raw36705step2 = raw36705step1 := by apply Matrix.ext; unfold raw36705step2 raw36705step1; decide +kernel
      have hl : raw36705step1Labels = labelEmbedding1 ∘ raw36705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36705step1 raw36705step1Labels raw36705step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3405 node3405Labels := by rfl

theorem canonical36706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36706 raw36706Labels = mixedMoment B node3759 node3759Labels := by
  calc
    mixedMoment B raw36706 raw36706Labels = mixedMoment B raw36706step0 raw36706step0Labels := by
      have ha : raw36706step0 = (fun i j => raw36706 (permutation268 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36706step0 raw36706; decide +kernel
      have hl : raw36706step0Labels = raw36706Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36706 raw36706Labels permutation268 permutation7
    mixedMoment B raw36706step0 raw36706step0Labels = mixedMoment B raw36706step1 raw36706step1Labels := by
      have ha : raw36706step1 = -raw36706step0 := by apply Matrix.ext; change ∀ i j, raw36706step1 i j = -(raw36706step0 i j); unfold raw36706step1 raw36706step0; decide +kernel
      have hl : raw36706step1Labels = raw36706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36706step1 raw36706step1Labels = mixedMoment B raw36706step2 raw36706step2Labels := by
      have ha : raw36706step2 = raw36706step1 := by apply Matrix.ext; unfold raw36706step2 raw36706step1; decide +kernel
      have hl : raw36706step1Labels = labelEmbedding1 ∘ raw36706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36706step1 raw36706step1Labels raw36706step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3759 node3759Labels := by rfl

theorem canonical36707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36707 raw36707Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw36707 raw36707Labels = mixedMoment B raw36707step0 raw36707step0Labels := by
      have hz : ∀ j, raw36707 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36707step0 = (fun i j => raw36707 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36707step0 raw36707; decide +kernel
      have hl : raw36707step0Labels = raw36707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36707 raw36707Labels permutation520 hz
    mixedMoment B raw36707step0 raw36707step0Labels = mixedMoment B raw36707step1 raw36707step1Labels := by
      have ha : raw36707step1 = (fun i j => raw36707step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36707step1 raw36707step0; decide +kernel
      have hl : raw36707step1Labels = raw36707step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36707step0 raw36707step0Labels permutation57 permutation7
    mixedMoment B raw36707step1 raw36707step1Labels = mixedMoment B raw36707step2 raw36707step2Labels := by
      have ha : raw36707step2 = -raw36707step1 := by apply Matrix.ext; change ∀ i j, raw36707step2 i j = -(raw36707step1 i j); unfold raw36707step2 raw36707step1; decide +kernel
      have hl : raw36707step2Labels = raw36707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36707step2 raw36707step2Labels = mixedMoment B raw36707step3 raw36707step3Labels := by
      have ha : raw36707step3 = raw36707step2 := by apply Matrix.ext; unfold raw36707step3 raw36707step2; decide +kernel
      have hl : raw36707step2Labels = labelEmbedding1 ∘ raw36707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36707step2 raw36707step2Labels raw36707step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

theorem canonical36708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36708 raw36708Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw36708 raw36708Labels = mixedMoment B raw36708step0 raw36708step0Labels := by
      have ha : raw36708step0 = (fun i j => raw36708 (permutation268 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36708step0 raw36708; decide +kernel
      have hl : raw36708step0Labels = raw36708Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36708 raw36708Labels permutation268 permutation7
    mixedMoment B raw36708step0 raw36708step0Labels = mixedMoment B raw36708step1 raw36708step1Labels := by
      have ha : raw36708step1 = -raw36708step0 := by apply Matrix.ext; change ∀ i j, raw36708step1 i j = -(raw36708step0 i j); unfold raw36708step1 raw36708step0; decide +kernel
      have hl : raw36708step1Labels = raw36708step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36708step1 raw36708step1Labels = mixedMoment B raw36708step2 raw36708step2Labels := by
      have ha : raw36708step2 = raw36708step1 := by apply Matrix.ext; unfold raw36708step2 raw36708step1; decide +kernel
      have hl : raw36708step1Labels = labelEmbedding1 ∘ raw36708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36708step1 raw36708step1Labels raw36708step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

theorem canonical36709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36709 raw36709Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw36709 raw36709Labels = mixedMoment B raw36709step0 raw36709step0Labels := by
      have hz : ∀ j, raw36709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36709step0 = (fun i j => raw36709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36709step0 raw36709; decide +kernel
      have hl : raw36709step0Labels = raw36709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36709 raw36709Labels permutation346 hz
    mixedMoment B raw36709step0 raw36709step0Labels = mixedMoment B raw36709step1 raw36709step1Labels := by
      have ha : raw36709step1 = (fun i j => raw36709step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36709step1 raw36709step0; decide +kernel
      have hl : raw36709step1Labels = raw36709step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36709step0 raw36709step0Labels permutation32 permutation5
    mixedMoment B raw36709step1 raw36709step1Labels = mixedMoment B raw36709step2 raw36709step2Labels := by
      have ha : raw36709step2 = -raw36709step1 := by apply Matrix.ext; change ∀ i j, raw36709step2 i j = -(raw36709step1 i j); unfold raw36709step2 raw36709step1; decide +kernel
      have hl : raw36709step2Labels = raw36709step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36709step2 raw36709step2Labels = mixedMoment B raw36709step3 raw36709step3Labels := by
      have ha : raw36709step3 = raw36709step2 := by apply Matrix.ext; unfold raw36709step3 raw36709step2; decide +kernel
      have hl : raw36709step2Labels = labelEmbedding1 ∘ raw36709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36709step2 raw36709step2Labels raw36709step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

theorem canonical36710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36710 raw36710Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw36710 raw36710Labels = mixedMoment B raw36710step0 raw36710step0Labels := by
      have hz : ∀ j, raw36710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36710step0 = (fun i j => raw36710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36710step0 raw36710; decide +kernel
      have hl : raw36710step0Labels = raw36710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36710 raw36710Labels permutation346 hz
    mixedMoment B raw36710step0 raw36710step0Labels = mixedMoment B raw36710step1 raw36710step1Labels := by
      have ha : raw36710step1 = (fun i j => raw36710step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36710step1 raw36710step0; decide +kernel
      have hl : raw36710step1Labels = raw36710step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36710step0 raw36710step0Labels permutation59 permutation7
    mixedMoment B raw36710step1 raw36710step1Labels = mixedMoment B raw36710step2 raw36710step2Labels := by
      have ha : raw36710step2 = -raw36710step1 := by apply Matrix.ext; change ∀ i j, raw36710step2 i j = -(raw36710step1 i j); unfold raw36710step2 raw36710step1; decide +kernel
      have hl : raw36710step2Labels = raw36710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36710step2 raw36710step2Labels = mixedMoment B raw36710step3 raw36710step3Labels := by
      have ha : raw36710step3 = raw36710step2 := by apply Matrix.ext; unfold raw36710step3 raw36710step2; decide +kernel
      have hl : raw36710step2Labels = labelEmbedding1 ∘ raw36710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36710step2 raw36710step2Labels raw36710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

theorem canonical36711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36711 raw36711Labels = mixedMoment B node3753 node3753Labels := by
  calc
    mixedMoment B raw36711 raw36711Labels = mixedMoment B raw36711step0 raw36711step0Labels := by
      have ha : raw36711step0 = (fun i j => raw36711 (permutation518 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36711step0 raw36711; decide +kernel
      have hl : raw36711step0Labels = raw36711Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36711 raw36711Labels permutation518 permutation7
    mixedMoment B raw36711step0 raw36711step0Labels = mixedMoment B raw36711step1 raw36711step1Labels := by
      have ha : raw36711step1 = raw36711step0 := by apply Matrix.ext; unfold raw36711step1 raw36711step0; decide +kernel
      have hl : raw36711step0Labels = labelEmbedding1 ∘ raw36711step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36711step0 raw36711step0Labels raw36711step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3753 node3753Labels := by rfl

theorem canonical36712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36712 raw36712Labels = mixedMoment B node3775 node3775Labels := by
  calc
    mixedMoment B raw36712 raw36712Labels = mixedMoment B raw36712step0 raw36712step0Labels := by
      have hz : ∀ j, raw36712 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36712step0 = (fun i j => raw36712 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36712step0 raw36712; decide +kernel
      have hl : raw36712step0Labels = raw36712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36712 raw36712Labels permutation520 hz
    mixedMoment B raw36712step0 raw36712step0Labels = mixedMoment B raw36712step1 raw36712step1Labels := by
      have hz : ∀ j, raw36712step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36712step1 = (fun i j => raw36712step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36712step1 raw36712step0; decide +kernel
      have hl : raw36712step1Labels = raw36712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36712step0 raw36712step0Labels permutation80 hz
    mixedMoment B raw36712step1 raw36712step1Labels = mixedMoment B raw36712step2 raw36712step2Labels := by
      have ha : raw36712step2 = (fun i j => raw36712step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36712step2 raw36712step1; decide +kernel
      have hl : raw36712step2Labels = raw36712step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36712step1 raw36712step1Labels permutation24 permutation7
    mixedMoment B raw36712step2 raw36712step2Labels = mixedMoment B raw36712step3 raw36712step3Labels := by
      have ha : raw36712step3 = raw36712step2 := by apply Matrix.ext; unfold raw36712step3 raw36712step2; decide +kernel
      have hl : raw36712step2Labels = labelEmbedding1 ∘ raw36712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36712step2 raw36712step2Labels raw36712step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3775 node3775Labels := by rfl

theorem canonical36713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36713 raw36713Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw36713 raw36713Labels = mixedMoment B raw36713step0 raw36713step0Labels := by
      have hz : ∀ j, raw36713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36713step0 = (fun i j => raw36713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36713step0 raw36713; decide +kernel
      have hl : raw36713step0Labels = raw36713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36713 raw36713Labels permutation346 hz
    mixedMoment B raw36713step0 raw36713step0Labels = mixedMoment B raw36713step1 raw36713step1Labels := by
      have ha : raw36713step1 = (fun i j => raw36713step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36713step1 raw36713step0; decide +kernel
      have hl : raw36713step1Labels = raw36713step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36713step0 raw36713step0Labels permutation59 permutation7
    mixedMoment B raw36713step1 raw36713step1Labels = mixedMoment B raw36713step2 raw36713step2Labels := by
      have ha : raw36713step2 = -raw36713step1 := by apply Matrix.ext; change ∀ i j, raw36713step2 i j = -(raw36713step1 i j); unfold raw36713step2 raw36713step1; decide +kernel
      have hl : raw36713step2Labels = raw36713step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36713step2 raw36713step2Labels = mixedMoment B raw36713step3 raw36713step3Labels := by
      have ha : raw36713step3 = raw36713step2 := by apply Matrix.ext; unfold raw36713step3 raw36713step2; decide +kernel
      have hl : raw36713step2Labels = labelEmbedding1 ∘ raw36713step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36713step2 raw36713step2Labels raw36713step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical36714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36714 raw36714Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw36714 raw36714Labels = mixedMoment B raw36714step0 raw36714step0Labels := by
      have hz : ∀ j, raw36714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36714step0 = (fun i j => raw36714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36714step0 raw36714; decide +kernel
      have hl : raw36714step0Labels = raw36714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36714 raw36714Labels permutation346 hz
    mixedMoment B raw36714step0 raw36714step0Labels = mixedMoment B raw36714step1 raw36714step1Labels := by
      have ha : raw36714step1 = (fun i j => raw36714step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36714step1 raw36714step0; decide +kernel
      have hl : raw36714step1Labels = raw36714step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36714step0 raw36714step0Labels permutation39 permutation5
    mixedMoment B raw36714step1 raw36714step1Labels = mixedMoment B raw36714step2 raw36714step2Labels := by
      have ha : raw36714step2 = -raw36714step1 := by apply Matrix.ext; change ∀ i j, raw36714step2 i j = -(raw36714step1 i j); unfold raw36714step2 raw36714step1; decide +kernel
      have hl : raw36714step2Labels = raw36714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36714step2 raw36714step2Labels = mixedMoment B raw36714step3 raw36714step3Labels := by
      have ha : raw36714step3 = raw36714step2 := by apply Matrix.ext; unfold raw36714step3 raw36714step2; decide +kernel
      have hl : raw36714step2Labels = labelEmbedding1 ∘ raw36714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36714step2 raw36714step2Labels raw36714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

theorem canonical36715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36715 raw36715Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw36715 raw36715Labels = mixedMoment B raw36715step0 raw36715step0Labels := by
      have hz : ∀ j, raw36715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36715step0 = (fun i j => raw36715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36715step0 raw36715; decide +kernel
      have hl : raw36715step0Labels = raw36715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36715 raw36715Labels permutation346 hz
    mixedMoment B raw36715step0 raw36715step0Labels = mixedMoment B raw36715step1 raw36715step1Labels := by
      have ha : raw36715step1 = (fun i j => raw36715step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36715step1 raw36715step0; decide +kernel
      have hl : raw36715step1Labels = raw36715step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36715step0 raw36715step0Labels permutation59 permutation7
    mixedMoment B raw36715step1 raw36715step1Labels = mixedMoment B raw36715step2 raw36715step2Labels := by
      have ha : raw36715step2 = -raw36715step1 := by apply Matrix.ext; change ∀ i j, raw36715step2 i j = -(raw36715step1 i j); unfold raw36715step2 raw36715step1; decide +kernel
      have hl : raw36715step2Labels = raw36715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36715step2 raw36715step2Labels = mixedMoment B raw36715step3 raw36715step3Labels := by
      have ha : raw36715step3 = raw36715step2 := by apply Matrix.ext; unfold raw36715step3 raw36715step2; decide +kernel
      have hl : raw36715step2Labels = labelEmbedding1 ∘ raw36715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36715step2 raw36715step2Labels raw36715step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

theorem canonical36716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36716 raw36716Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw36716 raw36716Labels = mixedMoment B raw36716step0 raw36716step0Labels := by
      have ha : raw36716step0 = (fun i j => raw36716 (permutation268 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36716step0 raw36716; decide +kernel
      have hl : raw36716step0Labels = raw36716Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36716 raw36716Labels permutation268 permutation7
    mixedMoment B raw36716step0 raw36716step0Labels = mixedMoment B raw36716step1 raw36716step1Labels := by
      have ha : raw36716step1 = -raw36716step0 := by apply Matrix.ext; change ∀ i j, raw36716step1 i j = -(raw36716step0 i j); unfold raw36716step1 raw36716step0; decide +kernel
      have hl : raw36716step1Labels = raw36716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36716step1 raw36716step1Labels = mixedMoment B raw36716step2 raw36716step2Labels := by
      have ha : raw36716step2 = raw36716step1 := by apply Matrix.ext; unfold raw36716step2 raw36716step1; decide +kernel
      have hl : raw36716step1Labels = labelEmbedding1 ∘ raw36716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36716step1 raw36716step1Labels raw36716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

theorem canonical36717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36717 raw36717Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw36717 raw36717Labels = mixedMoment B raw36717step0 raw36717step0Labels := by
      have hz : ∀ j, raw36717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36717step0 = (fun i j => raw36717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36717step0 raw36717; decide +kernel
      have hl : raw36717step0Labels = raw36717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36717 raw36717Labels permutation346 hz
    mixedMoment B raw36717step0 raw36717step0Labels = mixedMoment B raw36717step1 raw36717step1Labels := by
      have ha : raw36717step1 = (fun i j => raw36717step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36717step1 raw36717step0; decide +kernel
      have hl : raw36717step1Labels = raw36717step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36717step0 raw36717step0Labels permutation124 permutation5
    mixedMoment B raw36717step1 raw36717step1Labels = mixedMoment B raw36717step2 raw36717step2Labels := by
      have ha : raw36717step2 = raw36717step1 := by apply Matrix.ext; unfold raw36717step2 raw36717step1; decide +kernel
      have hl : raw36717step1Labels = labelEmbedding1 ∘ raw36717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36717step1 raw36717step1Labels raw36717step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3772 node3772Labels := by rfl

theorem canonical36718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36718 raw36718Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw36718 raw36718Labels = mixedMoment B raw36718step0 raw36718step0Labels := by
      have hz : ∀ j, raw36718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36718step0 = (fun i j => raw36718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36718step0 raw36718; decide +kernel
      have hl : raw36718step0Labels = raw36718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36718 raw36718Labels permutation346 hz
    mixedMoment B raw36718step0 raw36718step0Labels = mixedMoment B raw36718step1 raw36718step1Labels := by
      have ha : raw36718step1 = (fun i j => raw36718step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36718step1 raw36718step0; decide +kernel
      have hl : raw36718step1Labels = raw36718step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36718step0 raw36718step0Labels permutation59 permutation7
    mixedMoment B raw36718step1 raw36718step1Labels = mixedMoment B raw36718step2 raw36718step2Labels := by
      have ha : raw36718step2 = -raw36718step1 := by apply Matrix.ext; change ∀ i j, raw36718step2 i j = -(raw36718step1 i j); unfold raw36718step2 raw36718step1; decide +kernel
      have hl : raw36718step2Labels = raw36718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36718step2 raw36718step2Labels = mixedMoment B raw36718step3 raw36718step3Labels := by
      have ha : raw36718step3 = raw36718step2 := by apply Matrix.ext; unfold raw36718step3 raw36718step2; decide +kernel
      have hl : raw36718step2Labels = labelEmbedding1 ∘ raw36718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36718step2 raw36718step2Labels raw36718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

theorem canonical36719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36719 raw36719Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw36719 raw36719Labels = mixedMoment B raw36719step0 raw36719step0Labels := by
      have hz : ∀ j, raw36719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36719step0 = (fun i j => raw36719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36719step0 raw36719; decide +kernel
      have hl : raw36719step0Labels = raw36719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36719 raw36719Labels permutation346 hz
    mixedMoment B raw36719step0 raw36719step0Labels = mixedMoment B raw36719step1 raw36719step1Labels := by
      have ha : raw36719step1 = (fun i j => raw36719step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36719step1 raw36719step0; decide +kernel
      have hl : raw36719step1Labels = raw36719step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36719step0 raw36719step0Labels permutation149 permutation5
    mixedMoment B raw36719step1 raw36719step1Labels = mixedMoment B raw36719step2 raw36719step2Labels := by
      have ha : raw36719step2 = raw36719step1 := by apply Matrix.ext; unfold raw36719step2 raw36719step1; decide +kernel
      have hl : raw36719step1Labels = labelEmbedding1 ∘ raw36719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36719step1 raw36719step1Labels raw36719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

theorem canonical36720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36720 raw36720Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw36720 raw36720Labels = mixedMoment B raw36720step0 raw36720step0Labels := by
      have hz : ∀ j, raw36720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36720step0 = (fun i j => raw36720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36720step0 raw36720; decide +kernel
      have hl : raw36720step0Labels = raw36720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36720 raw36720Labels permutation346 hz
    mixedMoment B raw36720step0 raw36720step0Labels = mixedMoment B raw36720step1 raw36720step1Labels := by
      have ha : raw36720step1 = (fun i j => raw36720step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36720step1 raw36720step0; decide +kernel
      have hl : raw36720step1Labels = raw36720step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36720step0 raw36720step0Labels permutation59 permutation7
    mixedMoment B raw36720step1 raw36720step1Labels = mixedMoment B raw36720step2 raw36720step2Labels := by
      have ha : raw36720step2 = -raw36720step1 := by apply Matrix.ext; change ∀ i j, raw36720step2 i j = -(raw36720step1 i j); unfold raw36720step2 raw36720step1; decide +kernel
      have hl : raw36720step2Labels = raw36720step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36720step2 raw36720step2Labels = mixedMoment B raw36720step3 raw36720step3Labels := by
      have ha : raw36720step3 = raw36720step2 := by apply Matrix.ext; unfold raw36720step3 raw36720step2; decide +kernel
      have hl : raw36720step2Labels = labelEmbedding1 ∘ raw36720step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36720step2 raw36720step2Labels raw36720step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

theorem canonical36721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36721 raw36721Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw36721 raw36721Labels = mixedMoment B raw36721step0 raw36721step0Labels := by
      have ha : raw36721step0 = (fun i j => raw36721 (permutation676 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36721step0 raw36721; decide +kernel
      have hl : raw36721step0Labels = raw36721Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36721 raw36721Labels permutation676 permutation5
    mixedMoment B raw36721step0 raw36721step0Labels = mixedMoment B raw36721step1 raw36721step1Labels := by
      have ha : raw36721step1 = raw36721step0 := by apply Matrix.ext; unfold raw36721step1 raw36721step0; decide +kernel
      have hl : raw36721step0Labels = labelEmbedding1 ∘ raw36721step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36721step0 raw36721step0Labels raw36721step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

theorem canonical36722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36722 raw36722Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw36722 raw36722Labels = mixedMoment B raw36722step0 raw36722step0Labels := by
      have hz : ∀ j, raw36722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36722step0 = (fun i j => raw36722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36722step0 raw36722; decide +kernel
      have hl : raw36722step0Labels = raw36722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36722 raw36722Labels permutation346 hz
    mixedMoment B raw36722step0 raw36722step0Labels = mixedMoment B raw36722step1 raw36722step1Labels := by
      have ha : raw36722step1 = (fun i j => raw36722step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36722step1 raw36722step0; decide +kernel
      have hl : raw36722step1Labels = raw36722step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36722step0 raw36722step0Labels permutation148 permutation5
    mixedMoment B raw36722step1 raw36722step1Labels = mixedMoment B raw36722step2 raw36722step2Labels := by
      have ha : raw36722step2 = raw36722step1 := by apply Matrix.ext; unfold raw36722step2 raw36722step1; decide +kernel
      have hl : raw36722step1Labels = labelEmbedding1 ∘ raw36722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36722step1 raw36722step1Labels raw36722step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

theorem canonical36723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36723 raw36723Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw36723 raw36723Labels = mixedMoment B raw36723step0 raw36723step0Labels := by
      have hz : ∀ j, raw36723 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36723step0 = (fun i j => raw36723 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36723step0 raw36723; decide +kernel
      have hl : raw36723step0Labels = raw36723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36723 raw36723Labels permutation520 hz
    mixedMoment B raw36723step0 raw36723step0Labels = mixedMoment B raw36723step1 raw36723step1Labels := by
      have hz : ∀ j, raw36723step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36723step1 = (fun i j => raw36723step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36723step1 raw36723step0; decide +kernel
      have hl : raw36723step1Labels = raw36723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36723step0 raw36723step0Labels permutation80 hz
    mixedMoment B raw36723step1 raw36723step1Labels = mixedMoment B raw36723step2 raw36723step2Labels := by
      have ha : raw36723step2 = (fun i j => raw36723step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36723step2 raw36723step1; decide +kernel
      have hl : raw36723step2Labels = raw36723step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36723step1 raw36723step1Labels permutation29 permutation5
    mixedMoment B raw36723step2 raw36723step2Labels = mixedMoment B raw36723step3 raw36723step3Labels := by
      have ha : raw36723step3 = raw36723step2 := by apply Matrix.ext; unfold raw36723step3 raw36723step2; decide +kernel
      have hl : raw36723step2Labels = labelEmbedding1 ∘ raw36723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36723step2 raw36723step2Labels raw36723step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3405 node3405Labels = 0 := by
  exact mixedMoment_alpha B hF node3405 node3405Labels 1 permutation484
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

theorem sound3405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3405 node3405Labels = Sparse.eval nodeValue3405 (mixedVector B) := by
  simpa only [nodeValue3405, Sparse.eval_nil] using zero3405 B _hB _hF

theorem sound3412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3412 node3412Labels = Sparse.eval nodeValue3412 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3412) = mixedMoment B node3412 node3412Labels := rfl
  simpa [nodeValue3412, Sparse.eval] using hc.symm

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

theorem sound3471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3471 node3471Labels = Sparse.eval nodeValue3471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3471) = mixedMoment B node3471 node3471Labels := rfl
  simpa [nodeValue3471, Sparse.eval] using hc.symm

theorem sound3474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3474 node3474Labels = Sparse.eval nodeValue3474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3474) = mixedMoment B node3474 node3474Labels := rfl
  simpa [nodeValue3474, Sparse.eval] using hc.symm

theorem sound3475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3475 node3475Labels = Sparse.eval nodeValue3475 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3475) = mixedMoment B node3475 node3475Labels := rfl
  simpa [nodeValue3475, Sparse.eval] using hc.symm

theorem sound3480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3480 node3480Labels = Sparse.eval nodeValue3480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3480) = mixedMoment B node3480 node3480Labels := rfl
  simpa [nodeValue3480, Sparse.eval] using hc.symm

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

theorem sound3554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3554 node3554Labels = Sparse.eval nodeValue3554 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3554) = mixedMoment B node3554 node3554Labels := rfl
  simpa [nodeValue3554, Sparse.eval] using hc.symm

theorem sound3555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3555 node3555Labels = Sparse.eval nodeValue3555 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3555) = mixedMoment B node3555 node3555Labels := rfl
  simpa [nodeValue3555, Sparse.eval] using hc.symm

theorem sound3578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3578 node3578Labels = Sparse.eval nodeValue3578 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3578) = mixedMoment B node3578 node3578Labels := rfl
  simpa [nodeValue3578, Sparse.eval] using hc.symm

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

theorem sound3595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3595 node3595Labels = Sparse.eval nodeValue3595 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3595) = mixedMoment B node3595 node3595Labels := rfl
  simpa [nodeValue3595, Sparse.eval] using hc.symm

theorem sound3631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3631 node3631Labels = Sparse.eval nodeValue3631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3631) = mixedMoment B node3631 node3631Labels := rfl
  simpa [nodeValue3631, Sparse.eval] using hc.symm

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

theorem zero3775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3775 node3775Labels = 0 := by
  exact mixedMoment_order_one B hB node3775 node3775Labels 1
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

theorem sound3753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3753 node3753Labels = Sparse.eval nodeValue3753 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3753) = mixedMoment B node3753 node3753Labels := rfl
  simpa [nodeValue3753, Sparse.eval] using hc.symm

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

theorem sound3759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3759 node3759Labels = Sparse.eval nodeValue3759 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3759) = mixedMoment B node3759 node3759Labels := rfl
  simpa [nodeValue3759, Sparse.eval] using hc.symm

theorem sound3766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3766 node3766Labels = Sparse.eval nodeValue3766 (mixedVector B) := by
  simpa only [nodeValue3766, Sparse.eval_nil] using zero3766 B _hB _hF

theorem sound3767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3767 node3767Labels = Sparse.eval nodeValue3767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3767) = mixedMoment B node3767 node3767Labels := rfl
  simpa [nodeValue3767, Sparse.eval] using hc.symm

theorem sound3771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3771 node3771Labels = Sparse.eval nodeValue3771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3771) = mixedMoment B node3771 node3771Labels := rfl
  simpa [nodeValue3771, Sparse.eval] using hc.symm

theorem sound3772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3772 node3772Labels = Sparse.eval nodeValue3772 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3772) = mixedMoment B node3772 node3772Labels := rfl
  simpa [nodeValue3772, Sparse.eval] using hc.symm

theorem sound3775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3775 node3775Labels = Sparse.eval nodeValue3775 (mixedVector B) := by
  simpa only [nodeValue3775, Sparse.eval_nil] using zero3775 B _hB _hF

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

theorem sound3794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3794 node3794Labels = Sparse.eval nodeValue3794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3794) = mixedMoment B node3794 node3794Labels := rfl
  simpa [nodeValue3794, Sparse.eval] using hc.symm

theorem sound3808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = Sparse.eval nodeValue3808 (mixedVector B) := by
  simpa only [nodeValue3808, Sparse.eval_nil] using zero3808 B _hB _hF

theorem sound3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3809 node3809Labels = Sparse.eval nodeValue3809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3809) = mixedMoment B node3809 node3809Labels := rfl
  simpa [nodeValue3809, Sparse.eval] using hc.symm

theorem sound3817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3817 node3817Labels = Sparse.eval nodeValue3817 (mixedVector B) := by
  simpa only [nodeValue3817, Sparse.eval_nil] using zero3817 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3950 node3950Labels = 0 := by
  exact mixedMoment_alpha B hF node3950 node3950Labels 1 permutation212
    (by decide +kernel)

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

theorem sound3950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3950 node3950Labels = Sparse.eval nodeValue3950 (mixedVector B) := by
  simpa only [nodeValue3950, Sparse.eval_nil] using zero3950 B _hB _hF

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

theorem sound3959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3959 node3959Labels = Sparse.eval nodeValue3959 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3959) = mixedMoment B node3959 node3959Labels := rfl
  simpa [nodeValue3959, Sparse.eval] using hc.symm

theorem sound3963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3963 node3963Labels = Sparse.eval nodeValue3963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3963) = mixedMoment B node3963 node3963Labels := rfl
  simpa [nodeValue3963, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2625 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2625 + difference 0 1) (sourceB2625 + difference 1 0) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA2625 + difference 0 1) (sourceB2625 + difference 1 0) sourceC2625) = raw36694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36694; decide +kernel
    rw [ha]
    exact (canonical36694 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2625 + difference 0 2) (sourceB2625 + difference 2 0) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA2625 + difference 0 2) (sourceB2625 + difference 2 0) sourceC2625) = raw36695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36695; decide +kernel
    rw [ha]
    exact (canonical36695 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2625 + difference 0 3) (sourceB2625 + difference 3 0) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA2625 + difference 0 3) (sourceB2625 + difference 3 0) sourceC2625) = raw36696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36696; decide +kernel
    rw [ha]
    exact (canonical36696 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2625 + difference 0 4) (sourceB2625 + difference 4 0) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA2625 + difference 0 4) (sourceB2625 + difference 4 0) sourceC2625) = raw36697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36697; decide +kernel
    rw [ha]
    exact (canonical36697 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2625 + difference 0 5) (sourceB2625 + difference 5 0) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA2625 + difference 0 5) (sourceB2625 + difference 5 0) sourceC2625) = raw36698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36698; decide +kernel
    rw [ha]
    exact (canonical36698 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2625 + difference 1 0) (sourceB2625 + difference 0 1) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA2625 + difference 1 0) (sourceB2625 + difference 0 1) sourceC2625) = raw36699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36699; decide +kernel
    rw [ha]
    exact (canonical36699 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2625 + difference 1 2) (sourceB2625 + difference 2 1) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3950) := by
    have ha : (tripleCharges (sourceA2625 + difference 1 2) (sourceB2625 + difference 2 1) sourceC2625) = raw36700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36700; decide +kernel
    rw [ha]
    exact (canonical36700 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2625 + difference 1 3) (sourceB2625 + difference 3 1) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA2625 + difference 1 3) (sourceB2625 + difference 3 1) sourceC2625) = raw36701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36701; decide +kernel
    rw [ha]
    exact (canonical36701 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2625 + difference 1 4) (sourceB2625 + difference 4 1) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA2625 + difference 1 4) (sourceB2625 + difference 4 1) sourceC2625) = raw36702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36702; decide +kernel
    rw [ha]
    exact (canonical36702 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2625 + difference 1 5) (sourceB2625 + difference 5 1) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA2625 + difference 1 5) (sourceB2625 + difference 5 1) sourceC2625) = raw36703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36703; decide +kernel
    rw [ha]
    exact (canonical36703 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2625 + difference 2 0) (sourceB2625 + difference 0 2) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2625 + difference 2 0) (sourceB2625 + difference 0 2) sourceC2625) = raw36704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36704; decide +kernel
    rw [ha]
    exact (canonical36704 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2625 + difference 2 1) (sourceB2625 + difference 1 2) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3405) := by
    have ha : (tripleCharges (sourceA2625 + difference 2 1) (sourceB2625 + difference 1 2) sourceC2625) = raw36705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36705; decide +kernel
    rw [ha]
    exact (canonical36705 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2625 + difference 2 3) (sourceB2625 + difference 3 2) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA2625 + difference 2 3) (sourceB2625 + difference 3 2) sourceC2625) = raw36706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36706; decide +kernel
    rw [ha]
    exact (canonical36706 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2625 + difference 2 4) (sourceB2625 + difference 4 2) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2625 + difference 2 4) (sourceB2625 + difference 4 2) sourceC2625) = raw36707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36707; decide +kernel
    rw [ha]
    exact (canonical36707 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2625 + difference 2 5) (sourceB2625 + difference 5 2) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA2625 + difference 2 5) (sourceB2625 + difference 5 2) sourceC2625) = raw36708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36708; decide +kernel
    rw [ha]
    exact (canonical36708 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2625 + difference 3 0) (sourceB2625 + difference 0 3) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2625 + difference 3 0) (sourceB2625 + difference 0 3) sourceC2625) = raw36709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36709; decide +kernel
    rw [ha]
    exact (canonical36709 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2625 + difference 3 1) (sourceB2625 + difference 1 3) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2625 + difference 3 1) (sourceB2625 + difference 1 3) sourceC2625) = raw36710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36710; decide +kernel
    rw [ha]
    exact (canonical36710 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2625 + difference 3 2) (sourceB2625 + difference 2 3) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3753) := by
    have ha : (tripleCharges (sourceA2625 + difference 3 2) (sourceB2625 + difference 2 3) sourceC2625) = raw36711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36711; decide +kernel
    rw [ha]
    exact (canonical36711 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2625 + difference 3 4) (sourceB2625 + difference 4 3) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3775) := by
    have ha : (tripleCharges (sourceA2625 + difference 3 4) (sourceB2625 + difference 4 3) sourceC2625) = raw36712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36712; decide +kernel
    rw [ha]
    exact (canonical36712 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2625 + difference 3 5) (sourceB2625 + difference 5 3) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2625 + difference 3 5) (sourceB2625 + difference 5 3) sourceC2625) = raw36713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36713; decide +kernel
    rw [ha]
    exact (canonical36713 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2625 + difference 4 0) (sourceB2625 + difference 0 4) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3555) := by
    have ha : (tripleCharges (sourceA2625 + difference 4 0) (sourceB2625 + difference 0 4) sourceC2625) = raw36714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36714; decide +kernel
    rw [ha]
    exact (canonical36714 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2625 + difference 4 1) (sourceB2625 + difference 1 4) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2625 + difference 4 1) (sourceB2625 + difference 1 4) sourceC2625) = raw36715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36715; decide +kernel
    rw [ha]
    exact (canonical36715 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2625 + difference 4 2) (sourceB2625 + difference 2 4) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2625 + difference 4 2) (sourceB2625 + difference 2 4) sourceC2625) = raw36716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36716; decide +kernel
    rw [ha]
    exact (canonical36716 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2625 + difference 4 3) (sourceB2625 + difference 3 4) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA2625 + difference 4 3) (sourceB2625 + difference 3 4) sourceC2625) = raw36717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36717; decide +kernel
    rw [ha]
    exact (canonical36717 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2625 + difference 4 5) (sourceB2625 + difference 5 4) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA2625 + difference 4 5) (sourceB2625 + difference 5 4) sourceC2625) = raw36718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36718; decide +kernel
    rw [ha]
    exact (canonical36718 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2625 + difference 5 0) (sourceB2625 + difference 0 5) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2625 + difference 5 0) (sourceB2625 + difference 0 5) sourceC2625) = raw36719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36719; decide +kernel
    rw [ha]
    exact (canonical36719 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2625 + difference 5 1) (sourceB2625 + difference 1 5) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2625 + difference 5 1) (sourceB2625 + difference 1 5) sourceC2625) = raw36720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36720; decide +kernel
    rw [ha]
    exact (canonical36720 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2625 + difference 5 2) (sourceB2625 + difference 2 5) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2625 + difference 5 2) (sourceB2625 + difference 2 5) sourceC2625) = raw36721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36721; decide +kernel
    rw [ha]
    exact (canonical36721 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2625 + difference 5 3) (sourceB2625 + difference 3 5) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2625 + difference 5 3) (sourceB2625 + difference 3 5) sourceC2625) = raw36722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36722; decide +kernel
    rw [ha]
    exact (canonical36722 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2625 + difference 5 4) (sourceB2625 + difference 4 5) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2625 + difference 5 4) (sourceB2625 + difference 4 5) sourceC2625) = raw36723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36723; decide +kernel
    rw [ha]
    exact (canonical36723 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2625 sourceB2625 sourceC2625
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2625, Integer.Sparse.eval]
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

theorem reindexCheck2091 : Integer.Sparse.reindex keyMap MixedData.row2091 = numericRow2091 := by decide +kernel

theorem numericCheck2091 (x : Master → ℝ) : Integer.Sparse.eval numericRow2091 x =
    (1 : ℝ) * reducedSource2091 x := by
  norm_num [numericRow2091, reducedSource2091, Integer.Sparse.eval, Sparse.eval, nodeValue3405, nodeValue3412, nodeValue3413, nodeValue3418, nodeValue3471, nodeValue3474, nodeValue3475, nodeValue3480, nodeValue3554, nodeValue3555, nodeValue3578, nodeValue3595, nodeValue3631, nodeValue3753, nodeValue3755, nodeValue3758, nodeValue3759, nodeValue3766, nodeValue3767, nodeValue3771, nodeValue3772, nodeValue3775, nodeValue3794, nodeValue3808, nodeValue3809, nodeValue3817, nodeValue3950, nodeValue3958, nodeValue3959, nodeValue3963]

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

theorem reducedZero2091 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2091 (mixedVector B) = 0 := by
  have h3405 : mixedVector B (Sum.inr 3405) = Sparse.eval nodeValue3405 (mixedVector B) := by
    change mixedMoment B node3405 node3405Labels = _
    exact sound3405 B hB hF
  have h3412 : mixedVector B (Sum.inr 3412) = Sparse.eval nodeValue3412 (mixedVector B) := by
    change mixedMoment B node3412 node3412Labels = _
    exact sound3412 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3418 : mixedVector B (Sum.inr 3418) = Sparse.eval nodeValue3418 (mixedVector B) := by
    change mixedMoment B node3418 node3418Labels = _
    exact sound3418 B hB hF
  have h3471 : mixedVector B (Sum.inr 3471) = Sparse.eval nodeValue3471 (mixedVector B) := by
    change mixedMoment B node3471 node3471Labels = _
    exact sound3471 B hB hF
  have h3474 : mixedVector B (Sum.inr 3474) = Sparse.eval nodeValue3474 (mixedVector B) := by
    change mixedMoment B node3474 node3474Labels = _
    exact sound3474 B hB hF
  have h3475 : mixedVector B (Sum.inr 3475) = Sparse.eval nodeValue3475 (mixedVector B) := by
    change mixedMoment B node3475 node3475Labels = _
    exact sound3475 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3554 : mixedVector B (Sum.inr 3554) = Sparse.eval nodeValue3554 (mixedVector B) := by
    change mixedMoment B node3554 node3554Labels = _
    exact sound3554 B hB hF
  have h3555 : mixedVector B (Sum.inr 3555) = Sparse.eval nodeValue3555 (mixedVector B) := by
    change mixedMoment B node3555 node3555Labels = _
    exact sound3555 B hB hF
  have h3578 : mixedVector B (Sum.inr 3578) = Sparse.eval nodeValue3578 (mixedVector B) := by
    change mixedMoment B node3578 node3578Labels = _
    exact sound3578 B hB hF
  have h3595 : mixedVector B (Sum.inr 3595) = Sparse.eval nodeValue3595 (mixedVector B) := by
    change mixedMoment B node3595 node3595Labels = _
    exact sound3595 B hB hF
  have h3631 : mixedVector B (Sum.inr 3631) = Sparse.eval nodeValue3631 (mixedVector B) := by
    change mixedMoment B node3631 node3631Labels = _
    exact sound3631 B hB hF
  have h3753 : mixedVector B (Sum.inr 3753) = Sparse.eval nodeValue3753 (mixedVector B) := by
    change mixedMoment B node3753 node3753Labels = _
    exact sound3753 B hB hF
  have h3755 : mixedVector B (Sum.inr 3755) = Sparse.eval nodeValue3755 (mixedVector B) := by
    change mixedMoment B node3755 node3755Labels = _
    exact sound3755 B hB hF
  have h3758 : mixedVector B (Sum.inr 3758) = Sparse.eval nodeValue3758 (mixedVector B) := by
    change mixedMoment B node3758 node3758Labels = _
    exact sound3758 B hB hF
  have h3759 : mixedVector B (Sum.inr 3759) = Sparse.eval nodeValue3759 (mixedVector B) := by
    change mixedMoment B node3759 node3759Labels = _
    exact sound3759 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3767 : mixedVector B (Sum.inr 3767) = Sparse.eval nodeValue3767 (mixedVector B) := by
    change mixedMoment B node3767 node3767Labels = _
    exact sound3767 B hB hF
  have h3771 : mixedVector B (Sum.inr 3771) = Sparse.eval nodeValue3771 (mixedVector B) := by
    change mixedMoment B node3771 node3771Labels = _
    exact sound3771 B hB hF
  have h3772 : mixedVector B (Sum.inr 3772) = Sparse.eval nodeValue3772 (mixedVector B) := by
    change mixedMoment B node3772 node3772Labels = _
    exact sound3772 B hB hF
  have h3775 : mixedVector B (Sum.inr 3775) = Sparse.eval nodeValue3775 (mixedVector B) := by
    change mixedMoment B node3775 node3775Labels = _
    exact sound3775 B hB hF
  have h3794 : mixedVector B (Sum.inr 3794) = Sparse.eval nodeValue3794 (mixedVector B) := by
    change mixedMoment B node3794 node3794Labels = _
    exact sound3794 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  have h3950 : mixedVector B (Sum.inr 3950) = Sparse.eval nodeValue3950 (mixedVector B) := by
    change mixedMoment B node3950 node3950Labels = _
    exact sound3950 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h3963 : mixedVector B (Sum.inr 3963) = Sparse.eval nodeValue3963 (mixedVector B) := by
    change mixedMoment B node3963 node3963Labels = _
    exact sound3963 B hB hF
  simpa only [sourceForm2625, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3405, h3412, h3413, h3418, h3471, h3474, h3475, h3480, h3554, h3555, h3578, h3595, h3631, h3753, h3755, h3758, h3759, h3766, h3767, h3771, h3772, h3775, h3794, h3808, h3809, h3817, h3950, h3958, h3959, h3963, reducedSource2091] using sourceEq2625 B hB

theorem rowSound2091_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2091 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2091, numericCheck2091, reducedZero2091 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2091_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2091_e_oai
