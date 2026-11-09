-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2065_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:57:13.678535+00:00
-- url     : https://prove2.me/submissions/d60f8d58-cb5d-454d-abed-e6fc49a54d0f

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical278
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35701 raw35701Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw35701 raw35701Labels = mixedMoment B raw35701step0 raw35701step0Labels := by
      have hz : ∀ j, raw35701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35701step0 = (fun i j => raw35701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35701step0 raw35701; decide +kernel
      have hl : raw35701step0Labels = raw35701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35701 raw35701Labels permutation346 hz
    mixedMoment B raw35701step0 raw35701step0Labels = mixedMoment B raw35701step1 raw35701step1Labels := by
      have ha : raw35701step1 = (fun i j => raw35701step0 (permutation68 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35701step1 raw35701step0; decide +kernel
      have hl : raw35701step1Labels = raw35701step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35701step0 raw35701step0Labels permutation68 permutation7
    mixedMoment B raw35701step1 raw35701step1Labels = mixedMoment B raw35701step2 raw35701step2Labels := by
      have ha : raw35701step2 = -raw35701step1 := by apply Matrix.ext; change ∀ i j, raw35701step2 i j = -(raw35701step1 i j); unfold raw35701step2 raw35701step1; decide +kernel
      have hl : raw35701step2Labels = raw35701step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35701step2 raw35701step2Labels = mixedMoment B raw35701step3 raw35701step3Labels := by
      have ha : raw35701step3 = raw35701step2 := by apply Matrix.ext; unfold raw35701step3 raw35701step2; decide +kernel
      have hl : raw35701step2Labels = labelEmbedding1 ∘ raw35701step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35701step2 raw35701step2Labels raw35701step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical35702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35702 raw35702Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw35702 raw35702Labels = mixedMoment B raw35702step0 raw35702step0Labels := by
      have ha : raw35702step0 = (fun i j => raw35702 (permutation649 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35702step0 raw35702; decide +kernel
      have hl : raw35702step0Labels = raw35702Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35702 raw35702Labels permutation649 permutation7
    mixedMoment B raw35702step0 raw35702step0Labels = mixedMoment B raw35702step1 raw35702step1Labels := by
      have ha : raw35702step1 = raw35702step0 := by apply Matrix.ext; unfold raw35702step1 raw35702step0; decide +kernel
      have hl : raw35702step0Labels = labelEmbedding1 ∘ raw35702step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35702step0 raw35702step0Labels raw35702step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

theorem canonical35703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35703 raw35703Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw35703 raw35703Labels = mixedMoment B raw35703step0 raw35703step0Labels := by
      have hz : ∀ j, raw35703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35703step0 = (fun i j => raw35703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35703step0 raw35703; decide +kernel
      have hl : raw35703step0Labels = raw35703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35703 raw35703Labels permutation346 hz
    mixedMoment B raw35703step0 raw35703step0Labels = mixedMoment B raw35703step1 raw35703step1Labels := by
      have ha : raw35703step1 = (fun i j => raw35703step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35703step1 raw35703step0; decide +kernel
      have hl : raw35703step1Labels = raw35703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35703step0 raw35703step0Labels permutation141 permutation7
    mixedMoment B raw35703step1 raw35703step1Labels = mixedMoment B raw35703step2 raw35703step2Labels := by
      have ha : raw35703step2 = raw35703step1 := by apply Matrix.ext; unfold raw35703step2 raw35703step1; decide +kernel
      have hl : raw35703step1Labels = labelEmbedding1 ∘ raw35703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35703step1 raw35703step1Labels raw35703step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical35704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35704 raw35704Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw35704 raw35704Labels = mixedMoment B raw35704step0 raw35704step0Labels := by
      have hz : ∀ j, raw35704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35704step0 = (fun i j => raw35704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35704step0 raw35704; decide +kernel
      have hl : raw35704step0Labels = raw35704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35704 raw35704Labels permutation346 hz
    mixedMoment B raw35704step0 raw35704step0Labels = mixedMoment B raw35704step1 raw35704step1Labels := by
      have ha : raw35704step1 = (fun i j => raw35704step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35704step1 raw35704step0; decide +kernel
      have hl : raw35704step1Labels = raw35704step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35704step0 raw35704step0Labels permutation141 permutation7
    mixedMoment B raw35704step1 raw35704step1Labels = mixedMoment B raw35704step2 raw35704step2Labels := by
      have ha : raw35704step2 = raw35704step1 := by apply Matrix.ext; unfold raw35704step2 raw35704step1; decide +kernel
      have hl : raw35704step1Labels = labelEmbedding1 ∘ raw35704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35704step1 raw35704step1Labels raw35704step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical35705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35705 raw35705Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw35705 raw35705Labels = mixedMoment B raw35705step0 raw35705step0Labels := by
      have hz : ∀ j, raw35705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35705step0 = (fun i j => raw35705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35705step0 raw35705; decide +kernel
      have hl : raw35705step0Labels = raw35705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35705 raw35705Labels permutation346 hz
    mixedMoment B raw35705step0 raw35705step0Labels = mixedMoment B raw35705step1 raw35705step1Labels := by
      have ha : raw35705step1 = (fun i j => raw35705step0 (permutation68 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35705step1 raw35705step0; decide +kernel
      have hl : raw35705step1Labels = raw35705step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35705step0 raw35705step0Labels permutation68 permutation7
    mixedMoment B raw35705step1 raw35705step1Labels = mixedMoment B raw35705step2 raw35705step2Labels := by
      have ha : raw35705step2 = -raw35705step1 := by apply Matrix.ext; change ∀ i j, raw35705step2 i j = -(raw35705step1 i j); unfold raw35705step2 raw35705step1; decide +kernel
      have hl : raw35705step2Labels = raw35705step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35705step2 raw35705step2Labels = mixedMoment B raw35705step3 raw35705step3Labels := by
      have ha : raw35705step3 = raw35705step2 := by apply Matrix.ext; unfold raw35705step3 raw35705step2; decide +kernel
      have hl : raw35705step2Labels = labelEmbedding1 ∘ raw35705step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35705step2 raw35705step2Labels raw35705step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical35706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35706 raw35706Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw35706 raw35706Labels = mixedMoment B raw35706step0 raw35706step0Labels := by
      have hz : ∀ j, raw35706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35706step0 = (fun i j => raw35706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35706step0 raw35706; decide +kernel
      have hl : raw35706step0Labels = raw35706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35706 raw35706Labels permutation346 hz
    mixedMoment B raw35706step0 raw35706step0Labels = mixedMoment B raw35706step1 raw35706step1Labels := by
      have ha : raw35706step1 = (fun i j => raw35706step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35706step1 raw35706step0; decide +kernel
      have hl : raw35706step1Labels = raw35706step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35706step0 raw35706step0Labels permutation42 permutation5
    mixedMoment B raw35706step1 raw35706step1Labels = mixedMoment B raw35706step2 raw35706step2Labels := by
      have ha : raw35706step2 = -raw35706step1 := by apply Matrix.ext; change ∀ i j, raw35706step2 i j = -(raw35706step1 i j); unfold raw35706step2 raw35706step1; decide +kernel
      have hl : raw35706step2Labels = raw35706step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35706step2 raw35706step2Labels = mixedMoment B raw35706step3 raw35706step3Labels := by
      have ha : raw35706step3 = raw35706step2 := by apply Matrix.ext; unfold raw35706step3 raw35706step2; decide +kernel
      have hl : raw35706step2Labels = labelEmbedding1 ∘ raw35706step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35706step2 raw35706step2Labels raw35706step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

theorem canonical35707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35707 raw35707Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw35707 raw35707Labels = mixedMoment B raw35707step0 raw35707step0Labels := by
      have ha : raw35707step0 = (fun i j => raw35707 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35707step0 raw35707; decide +kernel
      have hl : raw35707step0Labels = raw35707Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35707 raw35707Labels permutation186 permutation5
    mixedMoment B raw35707step0 raw35707step0Labels = mixedMoment B raw35707step1 raw35707step1Labels := by
      have ha : raw35707step1 = -raw35707step0 := by apply Matrix.ext; change ∀ i j, raw35707step1 i j = -(raw35707step0 i j); unfold raw35707step1 raw35707step0; decide +kernel
      have hl : raw35707step1Labels = raw35707step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35707step1 raw35707step1Labels = mixedMoment B raw35707step2 raw35707step2Labels := by
      have ha : raw35707step2 = raw35707step1 := by apply Matrix.ext; unfold raw35707step2 raw35707step1; decide +kernel
      have hl : raw35707step1Labels = labelEmbedding1 ∘ raw35707step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35707step1 raw35707step1Labels raw35707step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3802 node3802Labels := by rfl

theorem canonical35708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35708 raw35708Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw35708 raw35708Labels = mixedMoment B raw35708step0 raw35708step0Labels := by
      have hz : ∀ j, raw35708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35708step0 = (fun i j => raw35708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35708step0 raw35708; decide +kernel
      have hl : raw35708step0Labels = raw35708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35708 raw35708Labels permutation346 hz
    mixedMoment B raw35708step0 raw35708step0Labels = mixedMoment B raw35708step1 raw35708step1Labels := by
      have ha : raw35708step1 = (fun i j => raw35708step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35708step1 raw35708step0; decide +kernel
      have hl : raw35708step1Labels = raw35708step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35708step0 raw35708step0Labels permutation42 permutation5
    mixedMoment B raw35708step1 raw35708step1Labels = mixedMoment B raw35708step2 raw35708step2Labels := by
      have ha : raw35708step2 = -raw35708step1 := by apply Matrix.ext; change ∀ i j, raw35708step2 i j = -(raw35708step1 i j); unfold raw35708step2 raw35708step1; decide +kernel
      have hl : raw35708step2Labels = raw35708step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35708step2 raw35708step2Labels = mixedMoment B raw35708step3 raw35708step3Labels := by
      have ha : raw35708step3 = raw35708step2 := by apply Matrix.ext; unfold raw35708step3 raw35708step2; decide +kernel
      have hl : raw35708step2Labels = labelEmbedding1 ∘ raw35708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35708step2 raw35708step2Labels raw35708step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical35709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35709 raw35709Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw35709 raw35709Labels = mixedMoment B raw35709step0 raw35709step0Labels := by
      have hz : ∀ j, raw35709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35709step0 = (fun i j => raw35709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35709step0 raw35709; decide +kernel
      have hl : raw35709step0Labels = raw35709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35709 raw35709Labels permutation346 hz
    mixedMoment B raw35709step0 raw35709step0Labels = mixedMoment B raw35709step1 raw35709step1Labels := by
      have ha : raw35709step1 = (fun i j => raw35709step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35709step1 raw35709step0; decide +kernel
      have hl : raw35709step1Labels = raw35709step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35709step0 raw35709step0Labels permutation141 permutation7
    mixedMoment B raw35709step1 raw35709step1Labels = mixedMoment B raw35709step2 raw35709step2Labels := by
      have ha : raw35709step2 = raw35709step1 := by apply Matrix.ext; unfold raw35709step2 raw35709step1; decide +kernel
      have hl : raw35709step1Labels = labelEmbedding1 ∘ raw35709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35709step1 raw35709step1Labels raw35709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical35710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35710 raw35710Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw35710 raw35710Labels = mixedMoment B raw35710step0 raw35710step0Labels := by
      have hz : ∀ j, raw35710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35710step0 = (fun i j => raw35710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35710step0 raw35710; decide +kernel
      have hl : raw35710step0Labels = raw35710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35710 raw35710Labels permutation346 hz
    mixedMoment B raw35710step0 raw35710step0Labels = mixedMoment B raw35710step1 raw35710step1Labels := by
      have ha : raw35710step1 = (fun i j => raw35710step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35710step1 raw35710step0; decide +kernel
      have hl : raw35710step1Labels = raw35710step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35710step0 raw35710step0Labels permutation52 permutation5
    mixedMoment B raw35710step1 raw35710step1Labels = mixedMoment B raw35710step2 raw35710step2Labels := by
      have ha : raw35710step2 = -raw35710step1 := by apply Matrix.ext; change ∀ i j, raw35710step2 i j = -(raw35710step1 i j); unfold raw35710step2 raw35710step1; decide +kernel
      have hl : raw35710step2Labels = raw35710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35710step2 raw35710step2Labels = mixedMoment B raw35710step3 raw35710step3Labels := by
      have ha : raw35710step3 = raw35710step2 := by apply Matrix.ext; unfold raw35710step3 raw35710step2; decide +kernel
      have hl : raw35710step2Labels = labelEmbedding1 ∘ raw35710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35710step2 raw35710step2Labels raw35710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical35711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35711 raw35711Labels = mixedMoment B node2145 node2145Labels := by
  calc
    mixedMoment B raw35711 raw35711Labels = mixedMoment B raw35711step0 raw35711step0Labels := by
      have ha : raw35711step0 = (fun i j => raw35711 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35711step0 raw35711; decide +kernel
      have hl : raw35711step0Labels = raw35711Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35711 raw35711Labels permutation162 permutation5
    mixedMoment B raw35711step0 raw35711step0Labels = mixedMoment B raw35711step1 raw35711step1Labels := by
      have ha : raw35711step1 = -raw35711step0 := by apply Matrix.ext; change ∀ i j, raw35711step1 i j = -(raw35711step0 i j); unfold raw35711step1 raw35711step0; decide +kernel
      have hl : raw35711step1Labels = raw35711step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35711step1 raw35711step1Labels = mixedMoment B raw35711step2 raw35711step2Labels := by
      have ha : raw35711step2 = raw35711step1 := by apply Matrix.ext; unfold raw35711step2 raw35711step1; decide +kernel
      have hl : raw35711step1Labels = labelEmbedding1 ∘ raw35711step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35711step1 raw35711step1Labels raw35711step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2145 node2145Labels := by rfl

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

theorem canonical35712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35712 raw35712Labels = mixedMoment B node3553 node3553Labels := by
  calc
    mixedMoment B raw35712 raw35712Labels = mixedMoment B raw35712step0 raw35712step0Labels := by
      have ha : raw35712step0 = (fun i j => raw35712 (permutation322 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35712step0 raw35712; decide +kernel
      have hl : raw35712step0Labels = raw35712Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35712 raw35712Labels permutation322 permutation7
    mixedMoment B raw35712step0 raw35712step0Labels = mixedMoment B raw35712step1 raw35712step1Labels := by
      have ha : raw35712step1 = -raw35712step0 := by apply Matrix.ext; change ∀ i j, raw35712step1 i j = -(raw35712step0 i j); unfold raw35712step1 raw35712step0; decide +kernel
      have hl : raw35712step1Labels = raw35712step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35712step1 raw35712step1Labels = mixedMoment B raw35712step2 raw35712step2Labels := by
      have ha : raw35712step2 = raw35712step1 := by apply Matrix.ext; unfold raw35712step2 raw35712step1; decide +kernel
      have hl : raw35712step1Labels = labelEmbedding1 ∘ raw35712step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35712step1 raw35712step1Labels raw35712step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3553 node3553Labels := by rfl

theorem canonical35713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35713 raw35713Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw35713 raw35713Labels = mixedMoment B raw35713step0 raw35713step0Labels := by
      have ha : raw35713step0 = (fun i j => raw35713 (permutation204 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35713step0 raw35713; decide +kernel
      have hl : raw35713step0Labels = raw35713Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35713 raw35713Labels permutation204 permutation5
    mixedMoment B raw35713step0 raw35713step0Labels = mixedMoment B raw35713step1 raw35713step1Labels := by
      have ha : raw35713step1 = -raw35713step0 := by apply Matrix.ext; change ∀ i j, raw35713step1 i j = -(raw35713step0 i j); unfold raw35713step1 raw35713step0; decide +kernel
      have hl : raw35713step1Labels = raw35713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35713step1 raw35713step1Labels = mixedMoment B raw35713step2 raw35713step2Labels := by
      have ha : raw35713step2 = raw35713step1 := by apply Matrix.ext; unfold raw35713step2 raw35713step1; decide +kernel
      have hl : raw35713step1Labels = labelEmbedding1 ∘ raw35713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35713step1 raw35713step1Labels raw35713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

theorem canonical35714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35714 raw35714Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw35714 raw35714Labels = mixedMoment B raw35714step0 raw35714step0Labels := by
      have ha : raw35714step0 = (fun i j => raw35714 (permutation655 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35714step0 raw35714; decide +kernel
      have hl : raw35714step0Labels = raw35714Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35714 raw35714Labels permutation655 permutation7
    mixedMoment B raw35714step0 raw35714step0Labels = mixedMoment B raw35714step1 raw35714step1Labels := by
      have ha : raw35714step1 = raw35714step0 := by apply Matrix.ext; unfold raw35714step1 raw35714step0; decide +kernel
      have hl : raw35714step0Labels = labelEmbedding1 ∘ raw35714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35714step0 raw35714step0Labels raw35714step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical35715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35715 raw35715Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw35715 raw35715Labels = mixedMoment B raw35715step0 raw35715step0Labels := by
      have ha : raw35715step0 = (fun i j => raw35715 (permutation248 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35715step0 raw35715; decide +kernel
      have hl : raw35715step0Labels = raw35715Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35715 raw35715Labels permutation248 permutation5
    mixedMoment B raw35715step0 raw35715step0Labels = mixedMoment B raw35715step1 raw35715step1Labels := by
      have ha : raw35715step1 = -raw35715step0 := by apply Matrix.ext; change ∀ i j, raw35715step1 i j = -(raw35715step0 i j); unfold raw35715step1 raw35715step0; decide +kernel
      have hl : raw35715step1Labels = raw35715step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35715step1 raw35715step1Labels = mixedMoment B raw35715step2 raw35715step2Labels := by
      have ha : raw35715step2 = raw35715step1 := by apply Matrix.ext; unfold raw35715step2 raw35715step1; decide +kernel
      have hl : raw35715step1Labels = labelEmbedding1 ∘ raw35715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35715step1 raw35715step1Labels raw35715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3866 node3866Labels := by rfl

theorem canonical35716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35716 raw35716Labels = mixedMoment B node2158 node2158Labels := by
  calc
    mixedMoment B raw35716 raw35716Labels = mixedMoment B raw35716step0 raw35716step0Labels := by
      have hz : ∀ j, raw35716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35716step0 = (fun i j => raw35716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35716step0 raw35716; decide +kernel
      have hl : raw35716step0Labels = raw35716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35716 raw35716Labels permutation346 hz
    mixedMoment B raw35716step0 raw35716step0Labels = mixedMoment B raw35716step1 raw35716step1Labels := by
      have ha : raw35716step1 = (fun i j => raw35716step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35716step1 raw35716step0; decide +kernel
      have hl : raw35716step1Labels = raw35716step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35716step0 raw35716step0Labels permutation36 permutation5
    mixedMoment B raw35716step1 raw35716step1Labels = mixedMoment B raw35716step2 raw35716step2Labels := by
      have ha : raw35716step2 = -raw35716step1 := by apply Matrix.ext; change ∀ i j, raw35716step2 i j = -(raw35716step1 i j); unfold raw35716step2 raw35716step1; decide +kernel
      have hl : raw35716step2Labels = raw35716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35716step2 raw35716step2Labels = mixedMoment B raw35716step3 raw35716step3Labels := by
      have ha : raw35716step3 = raw35716step2 := by apply Matrix.ext; unfold raw35716step3 raw35716step2; decide +kernel
      have hl : raw35716step2Labels = labelEmbedding1 ∘ raw35716step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35716step2 raw35716step2Labels raw35716step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2158 node2158Labels := by rfl

theorem canonical35717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35717 raw35717Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw35717 raw35717Labels = mixedMoment B raw35717step0 raw35717step0Labels := by
      have hz : ∀ j, raw35717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35717step0 = (fun i j => raw35717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35717step0 raw35717; decide +kernel
      have hl : raw35717step0Labels = raw35717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35717 raw35717Labels permutation346 hz
    mixedMoment B raw35717step0 raw35717step0Labels = mixedMoment B raw35717step1 raw35717step1Labels := by
      have ha : raw35717step1 = (fun i j => raw35717step0 (permutation68 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35717step1 raw35717step0; decide +kernel
      have hl : raw35717step1Labels = raw35717step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35717step0 raw35717step0Labels permutation68 permutation7
    mixedMoment B raw35717step1 raw35717step1Labels = mixedMoment B raw35717step2 raw35717step2Labels := by
      have ha : raw35717step2 = -raw35717step1 := by apply Matrix.ext; change ∀ i j, raw35717step2 i j = -(raw35717step1 i j); unfold raw35717step2 raw35717step1; decide +kernel
      have hl : raw35717step2Labels = raw35717step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35717step2 raw35717step2Labels = mixedMoment B raw35717step3 raw35717step3Labels := by
      have ha : raw35717step3 = raw35717step2 := by apply Matrix.ext; unfold raw35717step3 raw35717step2; decide +kernel
      have hl : raw35717step2Labels = labelEmbedding1 ∘ raw35717step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35717step2 raw35717step2Labels raw35717step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

theorem canonical35718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35718 raw35718Labels = mixedMoment B node3760 node3760Labels := by
  calc
    mixedMoment B raw35718 raw35718Labels = mixedMoment B raw35718step0 raw35718step0Labels := by
      have ha : raw35718step0 = (fun i j => raw35718 (permutation655 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35718step0 raw35718; decide +kernel
      have hl : raw35718step0Labels = raw35718Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35718 raw35718Labels permutation655 permutation7
    mixedMoment B raw35718step0 raw35718step0Labels = mixedMoment B raw35718step1 raw35718step1Labels := by
      have ha : raw35718step1 = raw35718step0 := by apply Matrix.ext; unfold raw35718step1 raw35718step0; decide +kernel
      have hl : raw35718step0Labels = labelEmbedding1 ∘ raw35718step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35718step0 raw35718step0Labels raw35718step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3760 node3760Labels := by rfl

theorem canonical35719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35719 raw35719Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw35719 raw35719Labels = mixedMoment B raw35719step0 raw35719step0Labels := by
      have hz : ∀ j, raw35719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35719step0 = (fun i j => raw35719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35719step0 raw35719; decide +kernel
      have hl : raw35719step0Labels = raw35719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35719 raw35719Labels permutation346 hz
    mixedMoment B raw35719step0 raw35719step0Labels = mixedMoment B raw35719step1 raw35719step1Labels := by
      have ha : raw35719step1 = (fun i j => raw35719step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35719step1 raw35719step0; decide +kernel
      have hl : raw35719step1Labels = raw35719step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35719step0 raw35719step0Labels permutation141 permutation7
    mixedMoment B raw35719step1 raw35719step1Labels = mixedMoment B raw35719step2 raw35719step2Labels := by
      have ha : raw35719step2 = raw35719step1 := by apply Matrix.ext; unfold raw35719step2 raw35719step1; decide +kernel
      have hl : raw35719step1Labels = labelEmbedding1 ∘ raw35719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35719step1 raw35719step1Labels raw35719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

theorem canonical35720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35720 raw35720Labels = mixedMoment B node3868 node3868Labels := by
  calc
    mixedMoment B raw35720 raw35720Labels = mixedMoment B raw35720step0 raw35720step0Labels := by
      have hz : ∀ j, raw35720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35720step0 = (fun i j => raw35720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35720step0 raw35720; decide +kernel
      have hl : raw35720step0Labels = raw35720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35720 raw35720Labels permutation346 hz
    mixedMoment B raw35720step0 raw35720step0Labels = mixedMoment B raw35720step1 raw35720step1Labels := by
      have ha : raw35720step1 = (fun i j => raw35720step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35720step1 raw35720step0; decide +kernel
      have hl : raw35720step1Labels = raw35720step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35720step0 raw35720step0Labels permutation50 permutation5
    mixedMoment B raw35720step1 raw35720step1Labels = mixedMoment B raw35720step2 raw35720step2Labels := by
      have ha : raw35720step2 = -raw35720step1 := by apply Matrix.ext; change ∀ i j, raw35720step2 i j = -(raw35720step1 i j); unfold raw35720step2 raw35720step1; decide +kernel
      have hl : raw35720step2Labels = raw35720step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35720step2 raw35720step2Labels = mixedMoment B raw35720step3 raw35720step3Labels := by
      have ha : raw35720step3 = raw35720step2 := by apply Matrix.ext; unfold raw35720step3 raw35720step2; decide +kernel
      have hl : raw35720step2Labels = labelEmbedding1 ∘ raw35720step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35720step2 raw35720step2Labels raw35720step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3868 node3868Labels := by rfl

theorem canonical35721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35721 raw35721Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw35721 raw35721Labels = mixedMoment B raw35721step0 raw35721step0Labels := by
      have hz : ∀ j, raw35721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35721step0 = (fun i j => raw35721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35721step0 raw35721; decide +kernel
      have hl : raw35721step0Labels = raw35721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35721 raw35721Labels permutation346 hz
    mixedMoment B raw35721step0 raw35721step0Labels = mixedMoment B raw35721step1 raw35721step1Labels := by
      have ha : raw35721step1 = (fun i j => raw35721step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35721step1 raw35721step0; decide +kernel
      have hl : raw35721step1Labels = raw35721step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35721step0 raw35721step0Labels permutation33 permutation5
    mixedMoment B raw35721step1 raw35721step1Labels = mixedMoment B raw35721step2 raw35721step2Labels := by
      have ha : raw35721step2 = -raw35721step1 := by apply Matrix.ext; change ∀ i j, raw35721step2 i j = -(raw35721step1 i j); unfold raw35721step2 raw35721step1; decide +kernel
      have hl : raw35721step2Labels = raw35721step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35721step2 raw35721step2Labels = mixedMoment B raw35721step3 raw35721step3Labels := by
      have ha : raw35721step3 = raw35721step2 := by apply Matrix.ext; unfold raw35721step3 raw35721step2; decide +kernel
      have hl : raw35721step2Labels = labelEmbedding1 ∘ raw35721step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35721step2 raw35721step2Labels raw35721step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2146 node2146Labels := by rfl

theorem canonical35722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35722 raw35722Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw35722 raw35722Labels = mixedMoment B raw35722step0 raw35722step0Labels := by
      have hz : ∀ j, raw35722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35722step0 = (fun i j => raw35722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35722step0 raw35722; decide +kernel
      have hl : raw35722step0Labels = raw35722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35722 raw35722Labels permutation346 hz
    mixedMoment B raw35722step0 raw35722step0Labels = mixedMoment B raw35722step1 raw35722step1Labels := by
      have ha : raw35722step1 = (fun i j => raw35722step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35722step1 raw35722step0; decide +kernel
      have hl : raw35722step1Labels = raw35722step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35722step0 raw35722step0Labels permutation127 permutation5
    mixedMoment B raw35722step1 raw35722step1Labels = mixedMoment B raw35722step2 raw35722step2Labels := by
      have ha : raw35722step2 = raw35722step1 := by apply Matrix.ext; unfold raw35722step2 raw35722step1; decide +kernel
      have hl : raw35722step1Labels = labelEmbedding1 ∘ raw35722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35722step1 raw35722step1Labels raw35722step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

theorem canonical35723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35723 raw35723Labels = mixedMoment B node2654 node2654Labels := by
  calc
    mixedMoment B raw35723 raw35723Labels = mixedMoment B raw35723step0 raw35723step0Labels := by
      have ha : raw35723step0 = (fun i j => raw35723 (permutation587 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35723step0 raw35723; decide +kernel
      have hl : raw35723step0Labels = raw35723Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35723 raw35723Labels permutation587 permutation5
    mixedMoment B raw35723step0 raw35723step0Labels = mixedMoment B raw35723step1 raw35723step1Labels := by
      have ha : raw35723step1 = raw35723step0 := by apply Matrix.ext; unfold raw35723step1 raw35723step0; decide +kernel
      have hl : raw35723step0Labels = labelEmbedding1 ∘ raw35723step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35723step0 raw35723step0Labels raw35723step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2654 node2654Labels := by rfl

theorem canonical35724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35724 raw35724Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw35724 raw35724Labels = mixedMoment B raw35724step0 raw35724step0Labels := by
      have hz : ∀ j, raw35724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35724step0 = (fun i j => raw35724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35724step0 raw35724; decide +kernel
      have hl : raw35724step0Labels = raw35724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35724 raw35724Labels permutation346 hz
    mixedMoment B raw35724step0 raw35724step0Labels = mixedMoment B raw35724step1 raw35724step1Labels := by
      have ha : raw35724step1 = (fun i j => raw35724step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35724step1 raw35724step0; decide +kernel
      have hl : raw35724step1Labels = raw35724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35724step0 raw35724step0Labels permutation125 permutation5
    mixedMoment B raw35724step1 raw35724step1Labels = mixedMoment B raw35724step2 raw35724step2Labels := by
      have ha : raw35724step2 = raw35724step1 := by apply Matrix.ext; unfold raw35724step2 raw35724step1; decide +kernel
      have hl : raw35724step1Labels = labelEmbedding1 ∘ raw35724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35724step1 raw35724step1Labels raw35724step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

theorem canonical35725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35725 raw35725Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw35725 raw35725Labels = mixedMoment B raw35725step0 raw35725step0Labels := by
      have hz : ∀ j, raw35725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35725step0 = (fun i j => raw35725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35725step0 raw35725; decide +kernel
      have hl : raw35725step0Labels = raw35725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35725 raw35725Labels permutation346 hz
    mixedMoment B raw35725step0 raw35725step0Labels = mixedMoment B raw35725step1 raw35725step1Labels := by
      have ha : raw35725step1 = (fun i j => raw35725step0 (permutation119 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35725step1 raw35725step0; decide +kernel
      have hl : raw35725step1Labels = raw35725step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35725step0 raw35725step0Labels permutation119 permutation5
    mixedMoment B raw35725step1 raw35725step1Labels = mixedMoment B raw35725step2 raw35725step2Labels := by
      have ha : raw35725step2 = raw35725step1 := by apply Matrix.ext; unfold raw35725step2 raw35725step1; decide +kernel
      have hl : raw35725step1Labels = labelEmbedding1 ∘ raw35725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35725step1 raw35725step1Labels raw35725step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

theorem canonical35726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35726 raw35726Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw35726 raw35726Labels = mixedMoment B raw35726step0 raw35726step0Labels := by
      have hz : ∀ j, raw35726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35726step0 = (fun i j => raw35726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35726step0 raw35726; decide +kernel
      have hl : raw35726step0Labels = raw35726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35726 raw35726Labels permutation346 hz
    mixedMoment B raw35726step0 raw35726step0Labels = mixedMoment B raw35726step1 raw35726step1Labels := by
      have ha : raw35726step1 = (fun i j => raw35726step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35726step1 raw35726step0; decide +kernel
      have hl : raw35726step1Labels = raw35726step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35726step0 raw35726step0Labels permutation33 permutation5
    mixedMoment B raw35726step1 raw35726step1Labels = mixedMoment B raw35726step2 raw35726step2Labels := by
      have ha : raw35726step2 = -raw35726step1 := by apply Matrix.ext; change ∀ i j, raw35726step2 i j = -(raw35726step1 i j); unfold raw35726step2 raw35726step1; decide +kernel
      have hl : raw35726step2Labels = raw35726step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35726step2 raw35726step2Labels = mixedMoment B raw35726step3 raw35726step3Labels := by
      have ha : raw35726step3 = raw35726step2 := by apply Matrix.ext; unfold raw35726step3 raw35726step2; decide +kernel
      have hl : raw35726step2Labels = labelEmbedding1 ∘ raw35726step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35726step2 raw35726step2Labels raw35726step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2153 node2153Labels := by rfl

theorem canonical35727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35727 raw35727Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw35727 raw35727Labels = mixedMoment B raw35727step0 raw35727step0Labels := by
      have hz : ∀ j, raw35727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35727step0 = (fun i j => raw35727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35727step0 raw35727; decide +kernel
      have hl : raw35727step0Labels = raw35727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35727 raw35727Labels permutation346 hz
    mixedMoment B raw35727step0 raw35727step0Labels = mixedMoment B raw35727step1 raw35727step1Labels := by
      have ha : raw35727step1 = (fun i j => raw35727step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35727step1 raw35727step0; decide +kernel
      have hl : raw35727step1Labels = raw35727step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35727step0 raw35727step0Labels permutation141 permutation7
    mixedMoment B raw35727step1 raw35727step1Labels = mixedMoment B raw35727step2 raw35727step2Labels := by
      have ha : raw35727step2 = raw35727step1 := by apply Matrix.ext; unfold raw35727step2 raw35727step1; decide +kernel
      have hl : raw35727step1Labels = labelEmbedding1 ∘ raw35727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35727step1 raw35727step1Labels raw35727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

theorem canonical35728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35728 raw35728Labels = mixedMoment B node3462 node3462Labels := by
  calc
    mixedMoment B raw35728 raw35728Labels = mixedMoment B raw35728step0 raw35728step0Labels := by
      have ha : raw35728step0 = (fun i j => raw35728 (permutation655 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35728step0 raw35728; decide +kernel
      have hl : raw35728step0Labels = raw35728Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35728 raw35728Labels permutation655 permutation7
    mixedMoment B raw35728step0 raw35728step0Labels = mixedMoment B raw35728step1 raw35728step1Labels := by
      have ha : raw35728step1 = raw35728step0 := by apply Matrix.ext; unfold raw35728step1 raw35728step0; decide +kernel
      have hl : raw35728step0Labels = labelEmbedding1 ∘ raw35728step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35728step0 raw35728step0Labels raw35728step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3462 node3462Labels := by rfl

theorem canonical35729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35729 raw35729Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw35729 raw35729Labels = mixedMoment B raw35729step0 raw35729step0Labels := by
      have hz : ∀ j, raw35729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35729step0 = (fun i j => raw35729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35729step0 raw35729; decide +kernel
      have hl : raw35729step0Labels = raw35729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35729 raw35729Labels permutation346 hz
    mixedMoment B raw35729step0 raw35729step0Labels = mixedMoment B raw35729step1 raw35729step1Labels := by
      have ha : raw35729step1 = (fun i j => raw35729step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35729step1 raw35729step0; decide +kernel
      have hl : raw35729step1Labels = raw35729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35729step0 raw35729step0Labels permutation141 permutation7
    mixedMoment B raw35729step1 raw35729step1Labels = mixedMoment B raw35729step2 raw35729step2Labels := by
      have ha : raw35729step2 = raw35729step1 := by apply Matrix.ext; unfold raw35729step2 raw35729step1; decide +kernel
      have hl : raw35729step1Labels = labelEmbedding1 ∘ raw35729step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35729step1 raw35729step1Labels raw35729step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

theorem canonical35730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35730 raw35730Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw35730 raw35730Labels = mixedMoment B raw35730step0 raw35730step0Labels := by
      have hz : ∀ j, raw35730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35730step0 = (fun i j => raw35730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35730step0 raw35730; decide +kernel
      have hl : raw35730step0Labels = raw35730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35730 raw35730Labels permutation346 hz
    mixedMoment B raw35730step0 raw35730step0Labels = mixedMoment B raw35730step1 raw35730step1Labels := by
      have ha : raw35730step1 = (fun i j => raw35730step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35730step1 raw35730step0; decide +kernel
      have hl : raw35730step1Labels = raw35730step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35730step0 raw35730step0Labels permutation141 permutation7
    mixedMoment B raw35730step1 raw35730step1Labels = mixedMoment B raw35730step2 raw35730step2Labels := by
      have ha : raw35730step2 = raw35730step1 := by apply Matrix.ext; unfold raw35730step2 raw35730step1; decide +kernel
      have hl : raw35730step1Labels = labelEmbedding1 ∘ raw35730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35730step1 raw35730step1Labels raw35730step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

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

theorem sound2145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2145 node2145Labels = Sparse.eval nodeValue2145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2145) = mixedMoment B node2145 node2145Labels := rfl
  simpa [nodeValue2145, Sparse.eval] using hc.symm

theorem sound2146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2146 node2146Labels = Sparse.eval nodeValue2146 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2146) = mixedMoment B node2146 node2146Labels := rfl
  simpa [nodeValue2146, Sparse.eval] using hc.symm

theorem sound2153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2153 node2153Labels = Sparse.eval nodeValue2153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2153) = mixedMoment B node2153 node2153Labels := rfl
  simpa [nodeValue2153, Sparse.eval] using hc.symm

theorem sound2158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2158 node2158Labels = Sparse.eval nodeValue2158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2158) = mixedMoment B node2158 node2158Labels := rfl
  simpa [nodeValue2158, Sparse.eval] using hc.symm

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

theorem sound2251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2251 node2251Labels = Sparse.eval nodeValue2251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2251) = mixedMoment B node2251 node2251Labels := rfl
  simpa [nodeValue2251, Sparse.eval] using hc.symm

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

theorem sound2654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2654 node2654Labels = Sparse.eval nodeValue2654 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2654) = mixedMoment B node2654 node2654Labels := rfl
  simpa [nodeValue2654, Sparse.eval] using hc.symm

theorem sound2659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2659 node2659Labels = Sparse.eval nodeValue2659 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2659) = mixedMoment B node2659 node2659Labels := rfl
  simpa [nodeValue2659, Sparse.eval] using hc.symm

theorem sound2677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2677 node2677Labels = Sparse.eval nodeValue2677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2677) = mixedMoment B node2677 node2677Labels := rfl
  simpa [nodeValue2677, Sparse.eval] using hc.symm

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

theorem sound2729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2729 node2729Labels = Sparse.eval nodeValue2729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2729) = mixedMoment B node2729 node2729Labels := rfl
  simpa [nodeValue2729, Sparse.eval] using hc.symm

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

theorem sound3462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3462 node3462Labels = Sparse.eval nodeValue3462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3462) = mixedMoment B node3462 node3462Labels := rfl
  simpa [nodeValue3462, Sparse.eval] using hc.symm

theorem sound3475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3475 node3475Labels = Sparse.eval nodeValue3475 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3475) = mixedMoment B node3475 node3475Labels := rfl
  simpa [nodeValue3475, Sparse.eval] using hc.symm

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

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

theorem sound3538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3538 node3538Labels = Sparse.eval nodeValue3538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3538) = mixedMoment B node3538 node3538Labels := rfl
  simpa [nodeValue3538, Sparse.eval] using hc.symm

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

theorem sound3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3564 node3564Labels = Sparse.eval nodeValue3564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3564) = mixedMoment B node3564 node3564Labels := rfl
  simpa [nodeValue3564, Sparse.eval] using hc.symm

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

theorem sound3760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3760 node3760Labels = Sparse.eval nodeValue3760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3760) = mixedMoment B node3760 node3760Labels := rfl
  simpa [nodeValue3760, Sparse.eval] using hc.symm

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

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

theorem sound3802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3802 node3802Labels = Sparse.eval nodeValue3802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3802) = mixedMoment B node3802 node3802Labels := rfl
  simpa [nodeValue3802, Sparse.eval] using hc.symm

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

theorem sound3834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3834 node3834Labels = Sparse.eval nodeValue3834 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3834) = mixedMoment B node3834 node3834Labels := rfl
  simpa [nodeValue3834, Sparse.eval] using hc.symm

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

theorem sound3854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3854 node3854Labels = Sparse.eval nodeValue3854 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3854) = mixedMoment B node3854 node3854Labels := rfl
  simpa [nodeValue3854, Sparse.eval] using hc.symm

theorem sound3866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3866 node3866Labels = Sparse.eval nodeValue3866 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3866) = mixedMoment B node3866 node3866Labels := rfl
  simpa [nodeValue3866, Sparse.eval] using hc.symm

theorem sound3868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3868 node3868Labels = Sparse.eval nodeValue3868 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3868) = mixedMoment B node3868 node3868Labels := rfl
  simpa [nodeValue3868, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

theorem sound3881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3881 node3881Labels = Sparse.eval nodeValue3881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3881) = mixedMoment B node3881 node3881Labels := rfl
  simpa [nodeValue3881, Sparse.eval] using hc.symm

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

theorem sourceEq2580 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2580 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2580 + difference 0 1) (sourceB2580 + difference 1 0) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2580 + difference 0 1) (sourceB2580 + difference 1 0) sourceC2580) = raw35701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35701; decide +kernel
    rw [ha]
    exact (canonical35701 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2580 + difference 0 2) (sourceB2580 + difference 2 0) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2580 + difference 0 2) (sourceB2580 + difference 2 0) sourceC2580) = raw35702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35702; decide +kernel
    rw [ha]
    exact (canonical35702 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2580 + difference 0 3) (sourceB2580 + difference 3 0) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA2580 + difference 0 3) (sourceB2580 + difference 3 0) sourceC2580) = raw35703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35703; decide +kernel
    rw [ha]
    exact (canonical35703 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2580 + difference 0 4) (sourceB2580 + difference 4 0) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2580 + difference 0 4) (sourceB2580 + difference 4 0) sourceC2580) = raw35704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35704; decide +kernel
    rw [ha]
    exact (canonical35704 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2580 + difference 0 5) (sourceB2580 + difference 5 0) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA2580 + difference 0 5) (sourceB2580 + difference 5 0) sourceC2580) = raw35705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35705; decide +kernel
    rw [ha]
    exact (canonical35705 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2580 + difference 1 0) (sourceB2580 + difference 0 1) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA2580 + difference 1 0) (sourceB2580 + difference 0 1) sourceC2580) = raw35706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35706; decide +kernel
    rw [ha]
    exact (canonical35706 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2580 + difference 1 2) (sourceB2580 + difference 2 1) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA2580 + difference 1 2) (sourceB2580 + difference 2 1) sourceC2580) = raw35707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35707; decide +kernel
    rw [ha]
    exact (canonical35707 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2580 + difference 1 3) (sourceB2580 + difference 3 1) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA2580 + difference 1 3) (sourceB2580 + difference 3 1) sourceC2580) = raw35708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35708; decide +kernel
    rw [ha]
    exact (canonical35708 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2580 + difference 1 4) (sourceB2580 + difference 4 1) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2580 + difference 1 4) (sourceB2580 + difference 4 1) sourceC2580) = raw35709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35709; decide +kernel
    rw [ha]
    exact (canonical35709 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2580 + difference 1 5) (sourceB2580 + difference 5 1) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA2580 + difference 1 5) (sourceB2580 + difference 5 1) sourceC2580) = raw35710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35710; decide +kernel
    rw [ha]
    exact (canonical35710 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2580 + difference 2 0) (sourceB2580 + difference 0 2) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2145) := by
    have ha : (tripleCharges (sourceA2580 + difference 2 0) (sourceB2580 + difference 0 2) sourceC2580) = raw35711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35711; decide +kernel
    rw [ha]
    exact (canonical35711 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2580 + difference 2 1) (sourceB2580 + difference 1 2) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3553) := by
    have ha : (tripleCharges (sourceA2580 + difference 2 1) (sourceB2580 + difference 1 2) sourceC2580) = raw35712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35712; decide +kernel
    rw [ha]
    exact (canonical35712 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2580 + difference 2 3) (sourceB2580 + difference 3 2) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA2580 + difference 2 3) (sourceB2580 + difference 3 2) sourceC2580) = raw35713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35713; decide +kernel
    rw [ha]
    exact (canonical35713 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2580 + difference 2 4) (sourceB2580 + difference 4 2) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2580 + difference 2 4) (sourceB2580 + difference 4 2) sourceC2580) = raw35714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35714; decide +kernel
    rw [ha]
    exact (canonical35714 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2580 + difference 2 5) (sourceB2580 + difference 5 2) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA2580 + difference 2 5) (sourceB2580 + difference 5 2) sourceC2580) = raw35715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35715; decide +kernel
    rw [ha]
    exact (canonical35715 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2580 + difference 3 0) (sourceB2580 + difference 0 3) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2158) := by
    have ha : (tripleCharges (sourceA2580 + difference 3 0) (sourceB2580 + difference 0 3) sourceC2580) = raw35716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35716; decide +kernel
    rw [ha]
    exact (canonical35716 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2580 + difference 3 1) (sourceB2580 + difference 1 3) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3555) := by
    have ha : (tripleCharges (sourceA2580 + difference 3 1) (sourceB2580 + difference 1 3) sourceC2580) = raw35717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35717; decide +kernel
    rw [ha]
    exact (canonical35717 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2580 + difference 3 2) (sourceB2580 + difference 2 3) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3760) := by
    have ha : (tripleCharges (sourceA2580 + difference 3 2) (sourceB2580 + difference 2 3) sourceC2580) = raw35718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35718; decide +kernel
    rw [ha]
    exact (canonical35718 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2580 + difference 3 4) (sourceB2580 + difference 4 3) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2580 + difference 3 4) (sourceB2580 + difference 4 3) sourceC2580) = raw35719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35719; decide +kernel
    rw [ha]
    exact (canonical35719 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2580 + difference 3 5) (sourceB2580 + difference 5 3) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3868) := by
    have ha : (tripleCharges (sourceA2580 + difference 3 5) (sourceB2580 + difference 5 3) sourceC2580) = raw35720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35720; decide +kernel
    rw [ha]
    exact (canonical35720 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2580 + difference 4 0) (sourceB2580 + difference 0 4) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2146) := by
    have ha : (tripleCharges (sourceA2580 + difference 4 0) (sourceB2580 + difference 0 4) sourceC2580) = raw35721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35721; decide +kernel
    rw [ha]
    exact (canonical35721 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2580 + difference 4 1) (sourceB2580 + difference 1 4) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2659) := by
    have ha : (tripleCharges (sourceA2580 + difference 4 1) (sourceB2580 + difference 1 4) sourceC2580) = raw35722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35722; decide +kernel
    rw [ha]
    exact (canonical35722 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2580 + difference 4 2) (sourceB2580 + difference 2 4) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2654) := by
    have ha : (tripleCharges (sourceA2580 + difference 4 2) (sourceB2580 + difference 2 4) sourceC2580) = raw35723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35723; decide +kernel
    rw [ha]
    exact (canonical35723 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2580 + difference 4 3) (sourceB2580 + difference 3 4) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA2580 + difference 4 3) (sourceB2580 + difference 3 4) sourceC2580) = raw35724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35724; decide +kernel
    rw [ha]
    exact (canonical35724 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2580 + difference 4 5) (sourceB2580 + difference 5 4) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA2580 + difference 4 5) (sourceB2580 + difference 5 4) sourceC2580) = raw35725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35725; decide +kernel
    rw [ha]
    exact (canonical35725 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2580 + difference 5 0) (sourceB2580 + difference 0 5) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2153) := by
    have ha : (tripleCharges (sourceA2580 + difference 5 0) (sourceB2580 + difference 0 5) sourceC2580) = raw35726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35726; decide +kernel
    rw [ha]
    exact (canonical35726 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2580 + difference 5 1) (sourceB2580 + difference 1 5) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2580 + difference 5 1) (sourceB2580 + difference 1 5) sourceC2580) = raw35727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35727; decide +kernel
    rw [ha]
    exact (canonical35727 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2580 + difference 5 2) (sourceB2580 + difference 2 5) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3462) := by
    have ha : (tripleCharges (sourceA2580 + difference 5 2) (sourceB2580 + difference 2 5) sourceC2580) = raw35728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35728; decide +kernel
    rw [ha]
    exact (canonical35728 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2580 + difference 5 3) (sourceB2580 + difference 3 5) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2580 + difference 5 3) (sourceB2580 + difference 3 5) sourceC2580) = raw35729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35729; decide +kernel
    rw [ha]
    exact (canonical35729 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2580 + difference 5 4) (sourceB2580 + difference 4 5) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2580 + difference 5 4) (sourceB2580 + difference 4 5) sourceC2580) = raw35730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35730; decide +kernel
    rw [ha]
    exact (canonical35730 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2580 sourceB2580 sourceC2580
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2580, Integer.Sparse.eval]
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

theorem reindexCheck2065 : Integer.Sparse.reindex keyMap MixedData.row2065 = numericRow2065 := by decide +kernel

theorem numericCheck2065 (x : Master → ℝ) : Integer.Sparse.eval numericRow2065 x =
    (1 : ℝ) * reducedSource2065 x := by
  norm_num [numericRow2065, reducedSource2065, Integer.Sparse.eval, Sparse.eval, nodeValue2145, nodeValue2146, nodeValue2153, nodeValue2158, nodeValue2251, nodeValue2654, nodeValue2659, nodeValue2677, nodeValue2729, nodeValue3462, nodeValue3475, nodeValue3478, nodeValue3538, nodeValue3553, nodeValue3555, nodeValue3564, nodeValue3760, nodeValue3770, nodeValue3795, nodeValue3799, nodeValue3802, nodeValue3807, nodeValue3813, nodeValue3834, nodeValue3850, nodeValue3854, nodeValue3866, nodeValue3868, nodeValue3876, nodeValue3881]

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

theorem reducedZero2065 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2065 (mixedVector B) = 0 := by
  have h2145 : mixedVector B (Sum.inr 2145) = Sparse.eval nodeValue2145 (mixedVector B) := by
    change mixedMoment B node2145 node2145Labels = _
    exact sound2145 B hB hF
  have h2146 : mixedVector B (Sum.inr 2146) = Sparse.eval nodeValue2146 (mixedVector B) := by
    change mixedMoment B node2146 node2146Labels = _
    exact sound2146 B hB hF
  have h2153 : mixedVector B (Sum.inr 2153) = Sparse.eval nodeValue2153 (mixedVector B) := by
    change mixedMoment B node2153 node2153Labels = _
    exact sound2153 B hB hF
  have h2158 : mixedVector B (Sum.inr 2158) = Sparse.eval nodeValue2158 (mixedVector B) := by
    change mixedMoment B node2158 node2158Labels = _
    exact sound2158 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2654 : mixedVector B (Sum.inr 2654) = Sparse.eval nodeValue2654 (mixedVector B) := by
    change mixedMoment B node2654 node2654Labels = _
    exact sound2654 B hB hF
  have h2659 : mixedVector B (Sum.inr 2659) = Sparse.eval nodeValue2659 (mixedVector B) := by
    change mixedMoment B node2659 node2659Labels = _
    exact sound2659 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h3462 : mixedVector B (Sum.inr 3462) = Sparse.eval nodeValue3462 (mixedVector B) := by
    change mixedMoment B node3462 node3462Labels = _
    exact sound3462 B hB hF
  have h3475 : mixedVector B (Sum.inr 3475) = Sparse.eval nodeValue3475 (mixedVector B) := by
    change mixedMoment B node3475 node3475Labels = _
    exact sound3475 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3553 : mixedVector B (Sum.inr 3553) = Sparse.eval nodeValue3553 (mixedVector B) := by
    change mixedMoment B node3553 node3553Labels = _
    exact sound3553 B hB hF
  have h3555 : mixedVector B (Sum.inr 3555) = Sparse.eval nodeValue3555 (mixedVector B) := by
    change mixedMoment B node3555 node3555Labels = _
    exact sound3555 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h3760 : mixedVector B (Sum.inr 3760) = Sparse.eval nodeValue3760 (mixedVector B) := by
    change mixedMoment B node3760 node3760Labels = _
    exact sound3760 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h3799 : mixedVector B (Sum.inr 3799) = Sparse.eval nodeValue3799 (mixedVector B) := by
    change mixedMoment B node3799 node3799Labels = _
    exact sound3799 B hB hF
  have h3802 : mixedVector B (Sum.inr 3802) = Sparse.eval nodeValue3802 (mixedVector B) := by
    change mixedMoment B node3802 node3802Labels = _
    exact sound3802 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3834 : mixedVector B (Sum.inr 3834) = Sparse.eval nodeValue3834 (mixedVector B) := by
    change mixedMoment B node3834 node3834Labels = _
    exact sound3834 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h3866 : mixedVector B (Sum.inr 3866) = Sparse.eval nodeValue3866 (mixedVector B) := by
    change mixedMoment B node3866 node3866Labels = _
    exact sound3866 B hB hF
  have h3868 : mixedVector B (Sum.inr 3868) = Sparse.eval nodeValue3868 (mixedVector B) := by
    change mixedMoment B node3868 node3868Labels = _
    exact sound3868 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  simpa only [sourceForm2580, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2145, h2146, h2153, h2158, h2251, h2654, h2659, h2677, h2729, h3462, h3475, h3478, h3538, h3553, h3555, h3564, h3760, h3770, h3795, h3799, h3802, h3807, h3813, h3834, h3850, h3854, h3866, h3868, h3876, h3881, reducedSource2065] using sourceEq2580 B hB

theorem rowSound2065_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2065 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2065, numericCheck2065, reducedZero2065 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2065_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2065_e_oai
