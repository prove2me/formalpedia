-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound505_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:43:16.23669+00:00
-- url     : https://prove2.me/submissions/0482ea6a-ec04-433a-8284-f9ff75a99c53

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3852_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10029 raw10029Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw10029 raw10029Labels = mixedMoment B raw10029step0 raw10029step0Labels := by
      have hz : ∀ j, raw10029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10029step0 = (fun i j => raw10029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10029step0 raw10029; decide +kernel
      have hl : raw10029step0Labels = raw10029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10029 raw10029Labels permutation346 hz
    mixedMoment B raw10029step0 raw10029step0Labels = mixedMoment B raw10029step1 raw10029step1Labels := by
      have ha : raw10029step1 = (fun i j => raw10029step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10029step1 raw10029step0; decide +kernel
      have hl : raw10029step1Labels = raw10029step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10029step0 raw10029step0Labels permutation40 permutation7
    mixedMoment B raw10029step1 raw10029step1Labels = mixedMoment B raw10029step2 raw10029step2Labels := by
      have ha : raw10029step2 = -raw10029step1 := by apply Matrix.ext; change ∀ i j, raw10029step2 i j = -(raw10029step1 i j); unfold raw10029step2 raw10029step1; decide +kernel
      have hl : raw10029step2Labels = raw10029step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10029step2 raw10029step2Labels = mixedMoment B raw10029step3 raw10029step3Labels := by
      have ha : raw10029step3 = raw10029step2 := by apply Matrix.ext; unfold raw10029step3 raw10029step2; decide +kernel
      have hl : raw10029step2Labels = labelEmbedding1 ∘ raw10029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10029step2 raw10029step2Labels raw10029step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical10030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10030 raw10030Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw10030 raw10030Labels = mixedMoment B raw10030step0 raw10030step0Labels := by
      have ha : raw10030step0 = (fun i j => raw10030 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10030step0 raw10030; decide +kernel
      have hl : raw10030step0Labels = raw10030Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10030 raw10030Labels permutation620 permutation7
    mixedMoment B raw10030step0 raw10030step0Labels = mixedMoment B raw10030step1 raw10030step1Labels := by
      have ha : raw10030step1 = raw10030step0 := by apply Matrix.ext; unfold raw10030step1 raw10030step0; decide +kernel
      have hl : raw10030step0Labels = labelEmbedding1 ∘ raw10030step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10030step0 raw10030step0Labels raw10030step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical10031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10031 raw10031Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw10031 raw10031Labels = mixedMoment B raw10031step0 raw10031step0Labels := by
      have hz : ∀ j, raw10031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10031step0 = (fun i j => raw10031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10031step0 raw10031; decide +kernel
      have hl : raw10031step0Labels = raw10031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10031 raw10031Labels permutation346 hz
    mixedMoment B raw10031step0 raw10031step0Labels = mixedMoment B raw10031step1 raw10031step1Labels := by
      have ha : raw10031step1 = (fun i j => raw10031step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10031step1 raw10031step0; decide +kernel
      have hl : raw10031step1Labels = raw10031step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10031step0 raw10031step0Labels permutation40 permutation7
    mixedMoment B raw10031step1 raw10031step1Labels = mixedMoment B raw10031step2 raw10031step2Labels := by
      have ha : raw10031step2 = -raw10031step1 := by apply Matrix.ext; change ∀ i j, raw10031step2 i j = -(raw10031step1 i j); unfold raw10031step2 raw10031step1; decide +kernel
      have hl : raw10031step2Labels = raw10031step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10031step2 raw10031step2Labels = mixedMoment B raw10031step3 raw10031step3Labels := by
      have ha : raw10031step3 = raw10031step2 := by apply Matrix.ext; unfold raw10031step3 raw10031step2; decide +kernel
      have hl : raw10031step2Labels = labelEmbedding1 ∘ raw10031step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10031step2 raw10031step2Labels raw10031step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical10032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10032 raw10032Labels = mixedMoment B node3860 node3860Labels := by
  calc
    mixedMoment B raw10032 raw10032Labels = mixedMoment B raw10032step0 raw10032step0Labels := by
      have hz : ∀ j, raw10032 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10032step0 = (fun i j => raw10032 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10032step0 raw10032; decide +kernel
      have hl : raw10032step0Labels = raw10032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10032 raw10032Labels permutation520 hz
    mixedMoment B raw10032step0 raw10032step0Labels = mixedMoment B raw10032step1 raw10032step1Labels := by
      have hz : ∀ j, raw10032step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10032step1 = (fun i j => raw10032step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10032step1 raw10032step0; decide +kernel
      have hl : raw10032step1Labels = raw10032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10032step0 raw10032step0Labels permutation80 hz
    mixedMoment B raw10032step1 raw10032step1Labels = mixedMoment B raw10032step2 raw10032step2Labels := by
      have ha : raw10032step2 = (fun i j => raw10032step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10032step2 raw10032step1; decide +kernel
      have hl : raw10032step2Labels = raw10032step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10032step1 raw10032step1Labels permutation29 permutation7
    mixedMoment B raw10032step2 raw10032step2Labels = mixedMoment B raw10032step3 raw10032step3Labels := by
      have ha : raw10032step3 = raw10032step2 := by apply Matrix.ext; unfold raw10032step3 raw10032step2; decide +kernel
      have hl : raw10032step2Labels = labelEmbedding1 ∘ raw10032step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10032step2 raw10032step2Labels raw10032step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3860 node3860Labels := by rfl

theorem canonical10033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10033 raw10033Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw10033 raw10033Labels = mixedMoment B raw10033step0 raw10033step0Labels := by
      have hz : ∀ j, raw10033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10033step0 = (fun i j => raw10033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10033step0 raw10033; decide +kernel
      have hl : raw10033step0Labels = raw10033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10033 raw10033Labels permutation346 hz
    mixedMoment B raw10033step0 raw10033step0Labels = mixedMoment B raw10033step1 raw10033step1Labels := by
      have ha : raw10033step1 = (fun i j => raw10033step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10033step1 raw10033step0; decide +kernel
      have hl : raw10033step1Labels = raw10033step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10033step0 raw10033step0Labels permutation40 permutation7
    mixedMoment B raw10033step1 raw10033step1Labels = mixedMoment B raw10033step2 raw10033step2Labels := by
      have ha : raw10033step2 = -raw10033step1 := by apply Matrix.ext; change ∀ i j, raw10033step2 i j = -(raw10033step1 i j); unfold raw10033step2 raw10033step1; decide +kernel
      have hl : raw10033step2Labels = raw10033step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10033step2 raw10033step2Labels = mixedMoment B raw10033step3 raw10033step3Labels := by
      have ha : raw10033step3 = raw10033step2 := by apply Matrix.ext; unfold raw10033step3 raw10033step2; decide +kernel
      have hl : raw10033step2Labels = labelEmbedding1 ∘ raw10033step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10033step2 raw10033step2Labels raw10033step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

theorem canonical10034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10034 raw10034Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw10034 raw10034Labels = mixedMoment B raw10034step0 raw10034step0Labels := by
      have hz : ∀ j, raw10034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10034step0 = (fun i j => raw10034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10034step0 raw10034; decide +kernel
      have hl : raw10034step0Labels = raw10034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10034 raw10034Labels permutation346 hz
    mixedMoment B raw10034step0 raw10034step0Labels = mixedMoment B raw10034step1 raw10034step1Labels := by
      have ha : raw10034step1 = (fun i j => raw10034step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10034step1 raw10034step0; decide +kernel
      have hl : raw10034step1Labels = raw10034step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10034step0 raw10034step0Labels permutation40 permutation7
    mixedMoment B raw10034step1 raw10034step1Labels = mixedMoment B raw10034step2 raw10034step2Labels := by
      have ha : raw10034step2 = -raw10034step1 := by apply Matrix.ext; change ∀ i j, raw10034step2 i j = -(raw10034step1 i j); unfold raw10034step2 raw10034step1; decide +kernel
      have hl : raw10034step2Labels = raw10034step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10034step2 raw10034step2Labels = mixedMoment B raw10034step3 raw10034step3Labels := by
      have ha : raw10034step3 = raw10034step2 := by apply Matrix.ext; unfold raw10034step3 raw10034step2; decide +kernel
      have hl : raw10034step2Labels = labelEmbedding1 ∘ raw10034step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10034step2 raw10034step2Labels raw10034step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical10035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10035 raw10035Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw10035 raw10035Labels = mixedMoment B raw10035step0 raw10035step0Labels := by
      have ha : raw10035step0 = (fun i j => raw10035 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10035step0 raw10035; decide +kernel
      have hl : raw10035step0Labels = raw10035Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10035 raw10035Labels permutation208 permutation7
    mixedMoment B raw10035step0 raw10035step0Labels = mixedMoment B raw10035step1 raw10035step1Labels := by
      have ha : raw10035step1 = -raw10035step0 := by apply Matrix.ext; change ∀ i j, raw10035step1 i j = -(raw10035step0 i j); unfold raw10035step1 raw10035step0; decide +kernel
      have hl : raw10035step1Labels = raw10035step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10035step1 raw10035step1Labels = mixedMoment B raw10035step2 raw10035step2Labels := by
      have ha : raw10035step2 = raw10035step1 := by apply Matrix.ext; unfold raw10035step2 raw10035step1; decide +kernel
      have hl : raw10035step1Labels = labelEmbedding1 ∘ raw10035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10035step1 raw10035step1Labels raw10035step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical10036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10036 raw10036Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw10036 raw10036Labels = mixedMoment B raw10036step0 raw10036step0Labels := by
      have hz : ∀ j, raw10036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10036step0 = (fun i j => raw10036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10036step0 raw10036; decide +kernel
      have hl : raw10036step0Labels = raw10036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10036 raw10036Labels permutation346 hz
    mixedMoment B raw10036step0 raw10036step0Labels = mixedMoment B raw10036step1 raw10036step1Labels := by
      have ha : raw10036step1 = (fun i j => raw10036step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10036step1 raw10036step0; decide +kernel
      have hl : raw10036step1Labels = raw10036step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10036step0 raw10036step0Labels permutation40 permutation7
    mixedMoment B raw10036step1 raw10036step1Labels = mixedMoment B raw10036step2 raw10036step2Labels := by
      have ha : raw10036step2 = -raw10036step1 := by apply Matrix.ext; change ∀ i j, raw10036step2 i j = -(raw10036step1 i j); unfold raw10036step2 raw10036step1; decide +kernel
      have hl : raw10036step2Labels = raw10036step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10036step2 raw10036step2Labels = mixedMoment B raw10036step3 raw10036step3Labels := by
      have ha : raw10036step3 = raw10036step2 := by apply Matrix.ext; unfold raw10036step3 raw10036step2; decide +kernel
      have hl : raw10036step2Labels = labelEmbedding1 ∘ raw10036step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10036step2 raw10036step2Labels raw10036step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

theorem canonical10037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10037 raw10037Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw10037 raw10037Labels = mixedMoment B raw10037step0 raw10037step0Labels := by
      have hz : ∀ j, raw10037 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10037step0 = (fun i j => raw10037 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10037step0 raw10037; decide +kernel
      have hl : raw10037step0Labels = raw10037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10037 raw10037Labels permutation520 hz
    mixedMoment B raw10037step0 raw10037step0Labels = mixedMoment B raw10037step1 raw10037step1Labels := by
      have hz : ∀ j, raw10037step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10037step1 = (fun i j => raw10037step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10037step1 raw10037step0; decide +kernel
      have hl : raw10037step1Labels = raw10037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10037step0 raw10037step0Labels permutation80 hz
    mixedMoment B raw10037step1 raw10037step1Labels = mixedMoment B raw10037step2 raw10037step2Labels := by
      have ha : raw10037step2 = (fun i j => raw10037step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10037step2 raw10037step1; decide +kernel
      have hl : raw10037step2Labels = raw10037step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10037step1 raw10037step1Labels permutation10 permutation7
    mixedMoment B raw10037step2 raw10037step2Labels = mixedMoment B raw10037step3 raw10037step3Labels := by
      have ha : raw10037step3 = -raw10037step2 := by apply Matrix.ext; change ∀ i j, raw10037step3 i j = -(raw10037step2 i j); unfold raw10037step3 raw10037step2; decide +kernel
      have hl : raw10037step3Labels = raw10037step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10037step3 raw10037step3Labels = mixedMoment B raw10037step4 raw10037step4Labels := by
      have ha : raw10037step4 = raw10037step3 := by apply Matrix.ext; unfold raw10037step4 raw10037step3; decide +kernel
      have hl : raw10037step3Labels = labelEmbedding1 ∘ raw10037step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10037step3 raw10037step3Labels raw10037step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical10038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10038 raw10038Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw10038 raw10038Labels = mixedMoment B raw10038step0 raw10038step0Labels := by
      have hz : ∀ j, raw10038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10038step0 = (fun i j => raw10038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10038step0 raw10038; decide +kernel
      have hl : raw10038step0Labels = raw10038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10038 raw10038Labels permutation346 hz
    mixedMoment B raw10038step0 raw10038step0Labels = mixedMoment B raw10038step1 raw10038step1Labels := by
      have ha : raw10038step1 = (fun i j => raw10038step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10038step1 raw10038step0; decide +kernel
      have hl : raw10038step1Labels = raw10038step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10038step0 raw10038step0Labels permutation40 permutation7
    mixedMoment B raw10038step1 raw10038step1Labels = mixedMoment B raw10038step2 raw10038step2Labels := by
      have ha : raw10038step2 = -raw10038step1 := by apply Matrix.ext; change ∀ i j, raw10038step2 i j = -(raw10038step1 i j); unfold raw10038step2 raw10038step1; decide +kernel
      have hl : raw10038step2Labels = raw10038step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10038step2 raw10038step2Labels = mixedMoment B raw10038step3 raw10038step3Labels := by
      have ha : raw10038step3 = raw10038step2 := by apply Matrix.ext; unfold raw10038step3 raw10038step2; decide +kernel
      have hl : raw10038step2Labels = labelEmbedding1 ∘ raw10038step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10038step2 raw10038step2Labels raw10038step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical10039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10039 raw10039Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw10039 raw10039Labels = mixedMoment B raw10039step0 raw10039step0Labels := by
      have ha : raw10039step0 = (fun i j => raw10039 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10039step0 raw10039; decide +kernel
      have hl : raw10039step0Labels = raw10039Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10039 raw10039Labels permutation208 permutation7
    mixedMoment B raw10039step0 raw10039step0Labels = mixedMoment B raw10039step1 raw10039step1Labels := by
      have ha : raw10039step1 = -raw10039step0 := by apply Matrix.ext; change ∀ i j, raw10039step1 i j = -(raw10039step0 i j); unfold raw10039step1 raw10039step0; decide +kernel
      have hl : raw10039step1Labels = raw10039step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10039step1 raw10039step1Labels = mixedMoment B raw10039step2 raw10039step2Labels := by
      have ha : raw10039step2 = raw10039step1 := by apply Matrix.ext; unfold raw10039step2 raw10039step1; decide +kernel
      have hl : raw10039step1Labels = labelEmbedding1 ∘ raw10039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10039step1 raw10039step1Labels raw10039step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical10040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10040 raw10040Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw10040 raw10040Labels = mixedMoment B raw10040step0 raw10040step0Labels := by
      have ha : raw10040step0 = (fun i j => raw10040 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10040step0 raw10040; decide +kernel
      have hl : raw10040step0Labels = raw10040Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10040 raw10040Labels permutation208 permutation7
    mixedMoment B raw10040step0 raw10040step0Labels = mixedMoment B raw10040step1 raw10040step1Labels := by
      have ha : raw10040step1 = -raw10040step0 := by apply Matrix.ext; change ∀ i j, raw10040step1 i j = -(raw10040step0 i j); unfold raw10040step1 raw10040step0; decide +kernel
      have hl : raw10040step1Labels = raw10040step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10040step1 raw10040step1Labels = mixedMoment B raw10040step2 raw10040step2Labels := by
      have ha : raw10040step2 = raw10040step1 := by apply Matrix.ext; unfold raw10040step2 raw10040step1; decide +kernel
      have hl : raw10040step1Labels = labelEmbedding1 ∘ raw10040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10040step1 raw10040step1Labels raw10040step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

theorem canonical10041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10041 raw10041Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw10041 raw10041Labels = mixedMoment B raw10041step0 raw10041step0Labels := by
      have ha : raw10041step0 = (fun i j => raw10041 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10041step0 raw10041; decide +kernel
      have hl : raw10041step0Labels = raw10041Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10041 raw10041Labels permutation208 permutation7
    mixedMoment B raw10041step0 raw10041step0Labels = mixedMoment B raw10041step1 raw10041step1Labels := by
      have ha : raw10041step1 = -raw10041step0 := by apply Matrix.ext; change ∀ i j, raw10041step1 i j = -(raw10041step0 i j); unfold raw10041step1 raw10041step0; decide +kernel
      have hl : raw10041step1Labels = raw10041step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10041step1 raw10041step1Labels = mixedMoment B raw10041step2 raw10041step2Labels := by
      have ha : raw10041step2 = raw10041step1 := by apply Matrix.ext; unfold raw10041step2 raw10041step1; decide +kernel
      have hl : raw10041step1Labels = labelEmbedding1 ∘ raw10041step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10041step1 raw10041step1Labels raw10041step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

theorem canonical10042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10042 raw10042Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw10042 raw10042Labels = mixedMoment B raw10042step0 raw10042step0Labels := by
      have hz : ∀ j, raw10042 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10042step0 = (fun i j => raw10042 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10042step0 raw10042; decide +kernel
      have hl : raw10042step0Labels = raw10042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10042 raw10042Labels permutation520 hz
    mixedMoment B raw10042step0 raw10042step0Labels = mixedMoment B raw10042step1 raw10042step1Labels := by
      have ha : raw10042step1 = (fun i j => raw10042step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10042step1 raw10042step0; decide +kernel
      have hl : raw10042step1Labels = raw10042step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10042step0 raw10042step0Labels permutation46 permutation7
    mixedMoment B raw10042step1 raw10042step1Labels = mixedMoment B raw10042step2 raw10042step2Labels := by
      have ha : raw10042step2 = -raw10042step1 := by apply Matrix.ext; change ∀ i j, raw10042step2 i j = -(raw10042step1 i j); unfold raw10042step2 raw10042step1; decide +kernel
      have hl : raw10042step2Labels = raw10042step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10042step2 raw10042step2Labels = mixedMoment B raw10042step3 raw10042step3Labels := by
      have ha : raw10042step3 = raw10042step2 := by apply Matrix.ext; unfold raw10042step3 raw10042step2; decide +kernel
      have hl : raw10042step2Labels = labelEmbedding1 ∘ raw10042step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10042step2 raw10042step2Labels raw10042step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical10043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10043 raw10043Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw10043 raw10043Labels = mixedMoment B raw10043step0 raw10043step0Labels := by
      have ha : raw10043step0 = (fun i j => raw10043 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10043step0 raw10043; decide +kernel
      have hl : raw10043step0Labels = raw10043Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10043 raw10043Labels permutation208 permutation7
    mixedMoment B raw10043step0 raw10043step0Labels = mixedMoment B raw10043step1 raw10043step1Labels := by
      have ha : raw10043step1 = -raw10043step0 := by apply Matrix.ext; change ∀ i j, raw10043step1 i j = -(raw10043step0 i j); unfold raw10043step1 raw10043step0; decide +kernel
      have hl : raw10043step1Labels = raw10043step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10043step1 raw10043step1Labels = mixedMoment B raw10043step2 raw10043step2Labels := by
      have ha : raw10043step2 = raw10043step1 := by apply Matrix.ext; unfold raw10043step2 raw10043step1; decide +kernel
      have hl : raw10043step1Labels = labelEmbedding1 ∘ raw10043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10043step1 raw10043step1Labels raw10043step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

theorem canonical10044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10044 raw10044Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw10044 raw10044Labels = mixedMoment B raw10044step0 raw10044step0Labels := by
      have hz : ∀ j, raw10044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10044step0 = (fun i j => raw10044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10044step0 raw10044; decide +kernel
      have hl : raw10044step0Labels = raw10044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10044 raw10044Labels permutation346 hz
    mixedMoment B raw10044step0 raw10044step0Labels = mixedMoment B raw10044step1 raw10044step1Labels := by
      have ha : raw10044step1 = (fun i j => raw10044step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10044step1 raw10044step0; decide +kernel
      have hl : raw10044step1Labels = raw10044step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10044step0 raw10044step0Labels permutation37 permutation5
    mixedMoment B raw10044step1 raw10044step1Labels = mixedMoment B raw10044step2 raw10044step2Labels := by
      have ha : raw10044step2 = -raw10044step1 := by apply Matrix.ext; change ∀ i j, raw10044step2 i j = -(raw10044step1 i j); unfold raw10044step2 raw10044step1; decide +kernel
      have hl : raw10044step2Labels = raw10044step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10044step2 raw10044step2Labels = mixedMoment B raw10044step3 raw10044step3Labels := by
      have ha : raw10044step3 = raw10044step2 := by apply Matrix.ext; unfold raw10044step3 raw10044step2; decide +kernel
      have hl : raw10044step2Labels = labelEmbedding1 ∘ raw10044step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10044step2 raw10044step2Labels raw10044step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical10045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10045 raw10045Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw10045 raw10045Labels = mixedMoment B raw10045step0 raw10045step0Labels := by
      have hz : ∀ j, raw10045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10045step0 = (fun i j => raw10045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10045step0 raw10045; decide +kernel
      have hl : raw10045step0Labels = raw10045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10045 raw10045Labels permutation346 hz
    mixedMoment B raw10045step0 raw10045step0Labels = mixedMoment B raw10045step1 raw10045step1Labels := by
      have ha : raw10045step1 = (fun i j => raw10045step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10045step1 raw10045step0; decide +kernel
      have hl : raw10045step1Labels = raw10045step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10045step0 raw10045step0Labels permutation40 permutation7
    mixedMoment B raw10045step1 raw10045step1Labels = mixedMoment B raw10045step2 raw10045step2Labels := by
      have ha : raw10045step2 = -raw10045step1 := by apply Matrix.ext; change ∀ i j, raw10045step2 i j = -(raw10045step1 i j); unfold raw10045step2 raw10045step1; decide +kernel
      have hl : raw10045step2Labels = raw10045step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10045step2 raw10045step2Labels = mixedMoment B raw10045step3 raw10045step3Labels := by
      have ha : raw10045step3 = raw10045step2 := by apply Matrix.ext; unfold raw10045step3 raw10045step2; decide +kernel
      have hl : raw10045step2Labels = labelEmbedding1 ∘ raw10045step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10045step2 raw10045step2Labels raw10045step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

theorem canonical10046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10046 raw10046Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw10046 raw10046Labels = mixedMoment B raw10046step0 raw10046step0Labels := by
      have ha : raw10046step0 = (fun i j => raw10046 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10046step0 raw10046; decide +kernel
      have hl : raw10046step0Labels = raw10046Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10046 raw10046Labels permutation208 permutation7
    mixedMoment B raw10046step0 raw10046step0Labels = mixedMoment B raw10046step1 raw10046step1Labels := by
      have ha : raw10046step1 = -raw10046step0 := by apply Matrix.ext; change ∀ i j, raw10046step1 i j = -(raw10046step0 i j); unfold raw10046step1 raw10046step0; decide +kernel
      have hl : raw10046step1Labels = raw10046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10046step1 raw10046step1Labels = mixedMoment B raw10046step2 raw10046step2Labels := by
      have ha : raw10046step2 = raw10046step1 := by apply Matrix.ext; unfold raw10046step2 raw10046step1; decide +kernel
      have hl : raw10046step1Labels = labelEmbedding1 ∘ raw10046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10046step1 raw10046step1Labels raw10046step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical10047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10047 raw10047Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw10047 raw10047Labels = mixedMoment B raw10047step0 raw10047step0Labels := by
      have hz : ∀ j, raw10047 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10047step0 = (fun i j => raw10047 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10047step0 raw10047; decide +kernel
      have hl : raw10047step0Labels = raw10047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10047 raw10047Labels permutation520 hz
    mixedMoment B raw10047step0 raw10047step0Labels = mixedMoment B raw10047step1 raw10047step1Labels := by
      have hz : ∀ j, raw10047step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10047step1 = (fun i j => raw10047step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10047step1 raw10047step0; decide +kernel
      have hl : raw10047step1Labels = raw10047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10047step0 raw10047step0Labels permutation80 hz
    mixedMoment B raw10047step1 raw10047step1Labels = mixedMoment B raw10047step2 raw10047step2Labels := by
      have ha : raw10047step2 = (fun i j => raw10047step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10047step2 raw10047step1; decide +kernel
      have hl : raw10047step2Labels = raw10047step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10047step1 raw10047step1Labels permutation10 permutation7
    mixedMoment B raw10047step2 raw10047step2Labels = mixedMoment B raw10047step3 raw10047step3Labels := by
      have ha : raw10047step3 = -raw10047step2 := by apply Matrix.ext; change ∀ i j, raw10047step3 i j = -(raw10047step2 i j); unfold raw10047step3 raw10047step2; decide +kernel
      have hl : raw10047step3Labels = raw10047step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10047step3 raw10047step3Labels = mixedMoment B raw10047step4 raw10047step4Labels := by
      have ha : raw10047step4 = raw10047step3 := by apply Matrix.ext; unfold raw10047step4 raw10047step3; decide +kernel
      have hl : raw10047step3Labels = labelEmbedding1 ∘ raw10047step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10047step3 raw10047step3Labels raw10047step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

theorem canonical10048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10048 raw10048Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw10048 raw10048Labels = mixedMoment B raw10048step0 raw10048step0Labels := by
      have hz : ∀ j, raw10048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10048step0 = (fun i j => raw10048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10048step0 raw10048; decide +kernel
      have hl : raw10048step0Labels = raw10048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10048 raw10048Labels permutation346 hz
    mixedMoment B raw10048step0 raw10048step0Labels = mixedMoment B raw10048step1 raw10048step1Labels := by
      have ha : raw10048step1 = (fun i j => raw10048step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10048step1 raw10048step0; decide +kernel
      have hl : raw10048step1Labels = raw10048step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10048step0 raw10048step0Labels permutation40 permutation7
    mixedMoment B raw10048step1 raw10048step1Labels = mixedMoment B raw10048step2 raw10048step2Labels := by
      have ha : raw10048step2 = -raw10048step1 := by apply Matrix.ext; change ∀ i j, raw10048step2 i j = -(raw10048step1 i j); unfold raw10048step2 raw10048step1; decide +kernel
      have hl : raw10048step2Labels = raw10048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10048step2 raw10048step2Labels = mixedMoment B raw10048step3 raw10048step3Labels := by
      have ha : raw10048step3 = raw10048step2 := by apply Matrix.ext; unfold raw10048step3 raw10048step2; decide +kernel
      have hl : raw10048step2Labels = labelEmbedding1 ∘ raw10048step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10048step2 raw10048step2Labels raw10048step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical10049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10049 raw10049Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw10049 raw10049Labels = mixedMoment B raw10049step0 raw10049step0Labels := by
      have hz : ∀ j, raw10049 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10049step0 = (fun i j => raw10049 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10049step0 raw10049; decide +kernel
      have hl : raw10049step0Labels = raw10049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10049 raw10049Labels permutation346 hz
    mixedMoment B raw10049step0 raw10049step0Labels = mixedMoment B raw10049step1 raw10049step1Labels := by
      have ha : raw10049step1 = (fun i j => raw10049step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10049step1 raw10049step0; decide +kernel
      have hl : raw10049step1Labels = raw10049step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10049step0 raw10049step0Labels permutation36 permutation5
    mixedMoment B raw10049step1 raw10049step1Labels = mixedMoment B raw10049step2 raw10049step2Labels := by
      have ha : raw10049step2 = -raw10049step1 := by apply Matrix.ext; change ∀ i j, raw10049step2 i j = -(raw10049step1 i j); unfold raw10049step2 raw10049step1; decide +kernel
      have hl : raw10049step2Labels = raw10049step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10049step2 raw10049step2Labels = mixedMoment B raw10049step3 raw10049step3Labels := by
      have ha : raw10049step3 = raw10049step2 := by apply Matrix.ext; unfold raw10049step3 raw10049step2; decide +kernel
      have hl : raw10049step2Labels = labelEmbedding1 ∘ raw10049step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10049step2 raw10049step2Labels raw10049step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3295 node3295Labels := by rfl

theorem canonical10050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10050 raw10050Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw10050 raw10050Labels = mixedMoment B raw10050step0 raw10050step0Labels := by
      have hz : ∀ j, raw10050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10050step0 = (fun i j => raw10050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10050step0 raw10050; decide +kernel
      have hl : raw10050step0Labels = raw10050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10050 raw10050Labels permutation346 hz
    mixedMoment B raw10050step0 raw10050step0Labels = mixedMoment B raw10050step1 raw10050step1Labels := by
      have ha : raw10050step1 = (fun i j => raw10050step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10050step1 raw10050step0; decide +kernel
      have hl : raw10050step1Labels = raw10050step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10050step0 raw10050step0Labels permutation40 permutation7
    mixedMoment B raw10050step1 raw10050step1Labels = mixedMoment B raw10050step2 raw10050step2Labels := by
      have ha : raw10050step2 = -raw10050step1 := by apply Matrix.ext; change ∀ i j, raw10050step2 i j = -(raw10050step1 i j); unfold raw10050step2 raw10050step1; decide +kernel
      have hl : raw10050step2Labels = raw10050step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10050step2 raw10050step2Labels = mixedMoment B raw10050step3 raw10050step3Labels := by
      have ha : raw10050step3 = raw10050step2 := by apply Matrix.ext; unfold raw10050step3 raw10050step2; decide +kernel
      have hl : raw10050step2Labels = labelEmbedding1 ∘ raw10050step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10050step2 raw10050step2Labels raw10050step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

theorem canonical10051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10051 raw10051Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw10051 raw10051Labels = mixedMoment B raw10051step0 raw10051step0Labels := by
      have ha : raw10051step0 = (fun i j => raw10051 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10051step0 raw10051; decide +kernel
      have hl : raw10051step0Labels = raw10051Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10051 raw10051Labels permutation208 permutation7
    mixedMoment B raw10051step0 raw10051step0Labels = mixedMoment B raw10051step1 raw10051step1Labels := by
      have ha : raw10051step1 = -raw10051step0 := by apply Matrix.ext; change ∀ i j, raw10051step1 i j = -(raw10051step0 i j); unfold raw10051step1 raw10051step0; decide +kernel
      have hl : raw10051step1Labels = raw10051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10051step1 raw10051step1Labels = mixedMoment B raw10051step2 raw10051step2Labels := by
      have ha : raw10051step2 = raw10051step1 := by apply Matrix.ext; unfold raw10051step2 raw10051step1; decide +kernel
      have hl : raw10051step1Labels = labelEmbedding1 ∘ raw10051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10051step1 raw10051step1Labels raw10051step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical10052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10052 raw10052Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw10052 raw10052Labels = mixedMoment B raw10052step0 raw10052step0Labels := by
      have hz : ∀ j, raw10052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10052step0 = (fun i j => raw10052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10052step0 raw10052; decide +kernel
      have hl : raw10052step0Labels = raw10052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10052 raw10052Labels permutation346 hz
    mixedMoment B raw10052step0 raw10052step0Labels = mixedMoment B raw10052step1 raw10052step1Labels := by
      have ha : raw10052step1 = (fun i j => raw10052step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10052step1 raw10052step0; decide +kernel
      have hl : raw10052step1Labels = raw10052step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10052step0 raw10052step0Labels permutation40 permutation7
    mixedMoment B raw10052step1 raw10052step1Labels = mixedMoment B raw10052step2 raw10052step2Labels := by
      have ha : raw10052step2 = -raw10052step1 := by apply Matrix.ext; change ∀ i j, raw10052step2 i j = -(raw10052step1 i j); unfold raw10052step2 raw10052step1; decide +kernel
      have hl : raw10052step2Labels = raw10052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10052step2 raw10052step2Labels = mixedMoment B raw10052step3 raw10052step3Labels := by
      have ha : raw10052step3 = raw10052step2 := by apply Matrix.ext; unfold raw10052step3 raw10052step2; decide +kernel
      have hl : raw10052step2Labels = labelEmbedding1 ∘ raw10052step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10052step2 raw10052step2Labels raw10052step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical10053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10053 raw10053Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw10053 raw10053Labels = mixedMoment B raw10053step0 raw10053step0Labels := by
      have hz : ∀ j, raw10053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10053step0 = (fun i j => raw10053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10053step0 raw10053; decide +kernel
      have hl : raw10053step0Labels = raw10053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10053 raw10053Labels permutation346 hz
    mixedMoment B raw10053step0 raw10053step0Labels = mixedMoment B raw10053step1 raw10053step1Labels := by
      have ha : raw10053step1 = (fun i j => raw10053step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10053step1 raw10053step0; decide +kernel
      have hl : raw10053step1Labels = raw10053step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10053step0 raw10053step0Labels permutation40 permutation7
    mixedMoment B raw10053step1 raw10053step1Labels = mixedMoment B raw10053step2 raw10053step2Labels := by
      have ha : raw10053step2 = -raw10053step1 := by apply Matrix.ext; change ∀ i j, raw10053step2 i j = -(raw10053step1 i j); unfold raw10053step2 raw10053step1; decide +kernel
      have hl : raw10053step2Labels = raw10053step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10053step2 raw10053step2Labels = mixedMoment B raw10053step3 raw10053step3Labels := by
      have ha : raw10053step3 = raw10053step2 := by apply Matrix.ext; unfold raw10053step3 raw10053step2; decide +kernel
      have hl : raw10053step2Labels = labelEmbedding1 ∘ raw10053step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10053step2 raw10053step2Labels raw10053step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical10054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10054 raw10054Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw10054 raw10054Labels = mixedMoment B raw10054step0 raw10054step0Labels := by
      have hz : ∀ j, raw10054 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10054step0 = (fun i j => raw10054 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10054step0 raw10054; decide +kernel
      have hl : raw10054step0Labels = raw10054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10054 raw10054Labels permutation346 hz
    mixedMoment B raw10054step0 raw10054step0Labels = mixedMoment B raw10054step1 raw10054step1Labels := by
      have ha : raw10054step1 = (fun i j => raw10054step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10054step1 raw10054step0; decide +kernel
      have hl : raw10054step1Labels = raw10054step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10054step0 raw10054step0Labels permutation40 permutation7
    mixedMoment B raw10054step1 raw10054step1Labels = mixedMoment B raw10054step2 raw10054step2Labels := by
      have ha : raw10054step2 = -raw10054step1 := by apply Matrix.ext; change ∀ i j, raw10054step2 i j = -(raw10054step1 i j); unfold raw10054step2 raw10054step1; decide +kernel
      have hl : raw10054step2Labels = raw10054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10054step2 raw10054step2Labels = mixedMoment B raw10054step3 raw10054step3Labels := by
      have ha : raw10054step3 = raw10054step2 := by apply Matrix.ext; unfold raw10054step3 raw10054step2; decide +kernel
      have hl : raw10054step2Labels = labelEmbedding1 ∘ raw10054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10054step2 raw10054step2Labels raw10054step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical10055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10055 raw10055Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw10055 raw10055Labels = mixedMoment B raw10055step0 raw10055step0Labels := by
      have hz : ∀ j, raw10055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10055step0 = (fun i j => raw10055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10055step0 raw10055; decide +kernel
      have hl : raw10055step0Labels = raw10055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10055 raw10055Labels permutation346 hz
    mixedMoment B raw10055step0 raw10055step0Labels = mixedMoment B raw10055step1 raw10055step1Labels := by
      have ha : raw10055step1 = (fun i j => raw10055step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10055step1 raw10055step0; decide +kernel
      have hl : raw10055step1Labels = raw10055step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10055step0 raw10055step0Labels permutation40 permutation7
    mixedMoment B raw10055step1 raw10055step1Labels = mixedMoment B raw10055step2 raw10055step2Labels := by
      have ha : raw10055step2 = -raw10055step1 := by apply Matrix.ext; change ∀ i j, raw10055step2 i j = -(raw10055step1 i j); unfold raw10055step2 raw10055step1; decide +kernel
      have hl : raw10055step2Labels = raw10055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10055step2 raw10055step2Labels = mixedMoment B raw10055step3 raw10055step3Labels := by
      have ha : raw10055step3 = raw10055step2 := by apply Matrix.ext; unfold raw10055step3 raw10055step2; decide +kernel
      have hl : raw10055step2Labels = labelEmbedding1 ∘ raw10055step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10055step2 raw10055step2Labels raw10055step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical10056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10056 raw10056Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw10056 raw10056Labels = mixedMoment B raw10056step0 raw10056step0Labels := by
      have ha : raw10056step0 = (fun i j => raw10056 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10056step0 raw10056; decide +kernel
      have hl : raw10056step0Labels = raw10056Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10056 raw10056Labels permutation620 permutation7
    mixedMoment B raw10056step0 raw10056step0Labels = mixedMoment B raw10056step1 raw10056step1Labels := by
      have ha : raw10056step1 = raw10056step0 := by apply Matrix.ext; unfold raw10056step1 raw10056step0; decide +kernel
      have hl : raw10056step0Labels = labelEmbedding1 ∘ raw10056step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10056step0 raw10056step0Labels raw10056step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3513 node3513Labels := by rfl

theorem canonical10057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10057 raw10057Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw10057 raw10057Labels = mixedMoment B raw10057step0 raw10057step0Labels := by
      have hz : ∀ j, raw10057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10057step0 = (fun i j => raw10057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10057step0 raw10057; decide +kernel
      have hl : raw10057step0Labels = raw10057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10057 raw10057Labels permutation346 hz
    mixedMoment B raw10057step0 raw10057step0Labels = mixedMoment B raw10057step1 raw10057step1Labels := by
      have ha : raw10057step1 = (fun i j => raw10057step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10057step1 raw10057step0; decide +kernel
      have hl : raw10057step1Labels = raw10057step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10057step0 raw10057step0Labels permutation40 permutation7
    mixedMoment B raw10057step1 raw10057step1Labels = mixedMoment B raw10057step2 raw10057step2Labels := by
      have ha : raw10057step2 = -raw10057step1 := by apply Matrix.ext; change ∀ i j, raw10057step2 i j = -(raw10057step1 i j); unfold raw10057step2 raw10057step1; decide +kernel
      have hl : raw10057step2Labels = raw10057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10057step2 raw10057step2Labels = mixedMoment B raw10057step3 raw10057step3Labels := by
      have ha : raw10057step3 = raw10057step2 := by apply Matrix.ext; unfold raw10057step3 raw10057step2; decide +kernel
      have hl : raw10057step2Labels = labelEmbedding1 ∘ raw10057step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10057step2 raw10057step2Labels raw10057step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical10058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10058 raw10058Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw10058 raw10058Labels = mixedMoment B raw10058step0 raw10058step0Labels := by
      have hz : ∀ j, raw10058 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10058step0 = (fun i j => raw10058 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10058step0 raw10058; decide +kernel
      have hl : raw10058step0Labels = raw10058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10058 raw10058Labels permutation520 hz
    mixedMoment B raw10058step0 raw10058step0Labels = mixedMoment B raw10058step1 raw10058step1Labels := by
      have hz : ∀ j, raw10058step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10058step1 = (fun i j => raw10058step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10058step1 raw10058step0; decide +kernel
      have hl : raw10058step1Labels = raw10058step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10058step0 raw10058step0Labels permutation80 hz
    mixedMoment B raw10058step1 raw10058step1Labels = mixedMoment B raw10058step2 raw10058step2Labels := by
      have ha : raw10058step2 = (fun i j => raw10058step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10058step2 raw10058step1; decide +kernel
      have hl : raw10058step2Labels = raw10058step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10058step1 raw10058step1Labels permutation29 permutation7
    mixedMoment B raw10058step2 raw10058step2Labels = mixedMoment B raw10058step3 raw10058step3Labels := by
      have ha : raw10058step3 = raw10058step2 := by apply Matrix.ext; unfold raw10058step3 raw10058step2; decide +kernel
      have hl : raw10058step2Labels = labelEmbedding1 ∘ raw10058step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10058step2 raw10058step2Labels raw10058step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3545 node3545Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3288 node3288Labels = Sparse.eval nodeValue3288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3288) = mixedMoment B node3288 node3288Labels := rfl
  simpa [nodeValue3288, Sparse.eval] using hc.symm

theorem sound3291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3291 node3291Labels = Sparse.eval nodeValue3291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3291) = mixedMoment B node3291 node3291Labels := rfl
  simpa [nodeValue3291, Sparse.eval] using hc.symm

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

theorem sound3295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3295 node3295Labels = Sparse.eval nodeValue3295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3295) = mixedMoment B node3295 node3295Labels := rfl
  simpa [nodeValue3295, Sparse.eval] using hc.symm

theorem sound3296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3296 node3296Labels = Sparse.eval nodeValue3296 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3296) = mixedMoment B node3296 node3296Labels := rfl
  simpa [nodeValue3296, Sparse.eval] using hc.symm

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

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3470 node3470Labels = Sparse.eval nodeValue3470 (mixedVector B) := by
  simpa only [nodeValue3470, Sparse.eval_nil] using zero3470 B _hB _hF

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

theorem sound3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3513 node3513Labels = Sparse.eval nodeValue3513 (mixedVector B) := by
  simpa only [nodeValue3513, Sparse.eval_nil] using zero3513 B _hB _hF

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

theorem sound3516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3516 node3516Labels = Sparse.eval nodeValue3516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3516) = mixedMoment B node3516 node3516Labels := rfl
  simpa [nodeValue3516, Sparse.eval] using hc.symm

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

theorem zero3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = 0 := by
  exact mixedMoment_alpha B hF node3525 node3525Labels 1 permutation434
    (by decide +kernel)

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

theorem sound3524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3524 node3524Labels = Sparse.eval nodeValue3524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3524) = mixedMoment B node3524 node3524Labels := rfl
  simpa [nodeValue3524, Sparse.eval] using hc.symm

theorem sound3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = Sparse.eval nodeValue3525 (mixedVector B) := by
  simpa only [nodeValue3525, Sparse.eval_nil] using zero3525 B _hB _hF

theorem sound3530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3530 node3530Labels = Sparse.eval nodeValue3530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3530) = mixedMoment B node3530 node3530Labels := rfl
  simpa [nodeValue3530, Sparse.eval] using hc.symm

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

theorem sound3545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3545 node3545Labels = Sparse.eval nodeValue3545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3545) = mixedMoment B node3545 node3545Labels := rfl
  simpa [nodeValue3545, Sparse.eval] using hc.symm

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

theorem sound3557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3557 node3557Labels = Sparse.eval nodeValue3557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3557) = mixedMoment B node3557 node3557Labels := rfl
  simpa [nodeValue3557, Sparse.eval] using hc.symm

theorem sound3570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3570 node3570Labels = Sparse.eval nodeValue3570 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3570) = mixedMoment B node3570 node3570Labels := rfl
  simpa [nodeValue3570, Sparse.eval] using hc.symm

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

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

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

theorem sound3837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3837 node3837Labels = Sparse.eval nodeValue3837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3837) = mixedMoment B node3837 node3837Labels := rfl
  simpa [nodeValue3837, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3860 node3860Labels = 0 := by
  exact mixedMoment_order_one B hB node3860 node3860Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3860 node3860Labels = Sparse.eval nodeValue3860 (mixedVector B) := by
  simpa only [nodeValue3860, Sparse.eval_nil] using zero3860 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources18
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm596 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA596 + difference 0 1) (sourceB596 + difference 1 0) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA596 + difference 0 1) (sourceB596 + difference 1 0) sourceC596) = raw10029 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10029; decide +kernel
    rw [ha]
    exact (canonical10029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA596 + difference 0 2) (sourceB596 + difference 2 0) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA596 + difference 0 2) (sourceB596 + difference 2 0) sourceC596) = raw10030 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10030; decide +kernel
    rw [ha]
    exact (canonical10030 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA596 + difference 0 3) (sourceB596 + difference 3 0) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA596 + difference 0 3) (sourceB596 + difference 3 0) sourceC596) = raw10031 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10031; decide +kernel
    rw [ha]
    exact (canonical10031 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA596 + difference 0 4) (sourceB596 + difference 4 0) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3860) := by
    have ha : (tripleCharges (sourceA596 + difference 0 4) (sourceB596 + difference 4 0) sourceC596) = raw10032 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10032; decide +kernel
    rw [ha]
    exact (canonical10032 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA596 + difference 0 5) (sourceB596 + difference 5 0) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA596 + difference 0 5) (sourceB596 + difference 5 0) sourceC596) = raw10033 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10033; decide +kernel
    rw [ha]
    exact (canonical10033 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA596 + difference 1 0) (sourceB596 + difference 0 1) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA596 + difference 1 0) (sourceB596 + difference 0 1) sourceC596) = raw10034 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10034; decide +kernel
    rw [ha]
    exact (canonical10034 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA596 + difference 1 2) (sourceB596 + difference 2 1) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA596 + difference 1 2) (sourceB596 + difference 2 1) sourceC596) = raw10035 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10035; decide +kernel
    rw [ha]
    exact (canonical10035 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA596 + difference 1 3) (sourceB596 + difference 3 1) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA596 + difference 1 3) (sourceB596 + difference 3 1) sourceC596) = raw10036 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10036; decide +kernel
    rw [ha]
    exact (canonical10036 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA596 + difference 1 4) (sourceB596 + difference 4 1) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA596 + difference 1 4) (sourceB596 + difference 4 1) sourceC596) = raw10037 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10037; decide +kernel
    rw [ha]
    exact (canonical10037 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA596 + difference 1 5) (sourceB596 + difference 5 1) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA596 + difference 1 5) (sourceB596 + difference 5 1) sourceC596) = raw10038 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10038; decide +kernel
    rw [ha]
    exact (canonical10038 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA596 + difference 2 0) (sourceB596 + difference 0 2) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA596 + difference 2 0) (sourceB596 + difference 0 2) sourceC596) = raw10039 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10039; decide +kernel
    rw [ha]
    exact (canonical10039 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA596 + difference 2 1) (sourceB596 + difference 1 2) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA596 + difference 2 1) (sourceB596 + difference 1 2) sourceC596) = raw10040 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10040; decide +kernel
    rw [ha]
    exact (canonical10040 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA596 + difference 2 3) (sourceB596 + difference 3 2) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA596 + difference 2 3) (sourceB596 + difference 3 2) sourceC596) = raw10041 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10041; decide +kernel
    rw [ha]
    exact (canonical10041 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA596 + difference 2 4) (sourceB596 + difference 4 2) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA596 + difference 2 4) (sourceB596 + difference 4 2) sourceC596) = raw10042 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10042; decide +kernel
    rw [ha]
    exact (canonical10042 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA596 + difference 2 5) (sourceB596 + difference 5 2) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA596 + difference 2 5) (sourceB596 + difference 5 2) sourceC596) = raw10043 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10043; decide +kernel
    rw [ha]
    exact (canonical10043 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA596 + difference 3 0) (sourceB596 + difference 0 3) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA596 + difference 3 0) (sourceB596 + difference 0 3) sourceC596) = raw10044 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10044; decide +kernel
    rw [ha]
    exact (canonical10044 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA596 + difference 3 1) (sourceB596 + difference 1 3) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA596 + difference 3 1) (sourceB596 + difference 1 3) sourceC596) = raw10045 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10045; decide +kernel
    rw [ha]
    exact (canonical10045 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA596 + difference 3 2) (sourceB596 + difference 2 3) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA596 + difference 3 2) (sourceB596 + difference 2 3) sourceC596) = raw10046 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10046; decide +kernel
    rw [ha]
    exact (canonical10046 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA596 + difference 3 4) (sourceB596 + difference 4 3) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA596 + difference 3 4) (sourceB596 + difference 4 3) sourceC596) = raw10047 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10047; decide +kernel
    rw [ha]
    exact (canonical10047 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA596 + difference 3 5) (sourceB596 + difference 5 3) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA596 + difference 3 5) (sourceB596 + difference 5 3) sourceC596) = raw10048 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10048; decide +kernel
    rw [ha]
    exact (canonical10048 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA596 + difference 4 0) (sourceB596 + difference 0 4) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA596 + difference 4 0) (sourceB596 + difference 0 4) sourceC596) = raw10049 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10049; decide +kernel
    rw [ha]
    exact (canonical10049 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA596 + difference 4 1) (sourceB596 + difference 1 4) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA596 + difference 4 1) (sourceB596 + difference 1 4) sourceC596) = raw10050 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10050; decide +kernel
    rw [ha]
    exact (canonical10050 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA596 + difference 4 2) (sourceB596 + difference 2 4) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA596 + difference 4 2) (sourceB596 + difference 2 4) sourceC596) = raw10051 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10051; decide +kernel
    rw [ha]
    exact (canonical10051 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA596 + difference 4 3) (sourceB596 + difference 3 4) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA596 + difference 4 3) (sourceB596 + difference 3 4) sourceC596) = raw10052 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10052; decide +kernel
    rw [ha]
    exact (canonical10052 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA596 + difference 4 5) (sourceB596 + difference 5 4) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA596 + difference 4 5) (sourceB596 + difference 5 4) sourceC596) = raw10053 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10053; decide +kernel
    rw [ha]
    exact (canonical10053 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA596 + difference 5 0) (sourceB596 + difference 0 5) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA596 + difference 5 0) (sourceB596 + difference 0 5) sourceC596) = raw10054 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10054; decide +kernel
    rw [ha]
    exact (canonical10054 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA596 + difference 5 1) (sourceB596 + difference 1 5) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA596 + difference 5 1) (sourceB596 + difference 1 5) sourceC596) = raw10055 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10055; decide +kernel
    rw [ha]
    exact (canonical10055 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA596 + difference 5 2) (sourceB596 + difference 2 5) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA596 + difference 5 2) (sourceB596 + difference 2 5) sourceC596) = raw10056 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10056; decide +kernel
    rw [ha]
    exact (canonical10056 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA596 + difference 5 3) (sourceB596 + difference 3 5) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA596 + difference 5 3) (sourceB596 + difference 3 5) sourceC596) = raw10057 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10057; decide +kernel
    rw [ha]
    exact (canonical10057 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA596 + difference 5 4) (sourceB596 + difference 4 5) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA596 + difference 5 4) (sourceB596 + difference 4 5) sourceC596) = raw10058 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10058; decide +kernel
    rw [ha]
    exact (canonical10058 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA596 sourceB596 sourceC596
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm596, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck505 : Integer.Sparse.reindex keyMap MixedData.row505 = numericRow505 := by decide +kernel

theorem numericCheck505 (x : Master → ℝ) : Integer.Sparse.eval numericRow505 x =
    (4320 : ℝ) * reducedSource505 x := by
  norm_num [numericRow505, reducedSource505, Integer.Sparse.eval, Sparse.eval, nodeValue3288, nodeValue3291, nodeValue3293, nodeValue3295, nodeValue3296, nodeValue3459, nodeValue3468, nodeValue3470, nodeValue3478, nodeValue3513, nodeValue3514, nodeValue3516, nodeValue3524, nodeValue3525, nodeValue3530, nodeValue3533, nodeValue3534, nodeValue3538, nodeValue3540, nodeValue3545, nodeValue3547, nodeValue3557, nodeValue3570, nodeValue3572, nodeValue3582, nodeValue3807, nodeValue3837, nodeValue3850, nodeValue3852, nodeValue3860]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero505 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource505 (mixedVector B) = 0 := by
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3295 : mixedVector B (Sum.inr 3295) = Sparse.eval nodeValue3295 (mixedVector B) := by
    change mixedMoment B node3295 node3295Labels = _
    exact sound3295 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3459 : mixedVector B (Sum.inr 3459) = Sparse.eval nodeValue3459 (mixedVector B) := by
    change mixedMoment B node3459 node3459Labels = _
    exact sound3459 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3470 : mixedVector B (Sum.inr 3470) = Sparse.eval nodeValue3470 (mixedVector B) := by
    change mixedMoment B node3470 node3470Labels = _
    exact sound3470 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3524 : mixedVector B (Sum.inr 3524) = Sparse.eval nodeValue3524 (mixedVector B) := by
    change mixedMoment B node3524 node3524Labels = _
    exact sound3524 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852_e B hB hF
  have h3860 : mixedVector B (Sum.inr 3860) = Sparse.eval nodeValue3860 (mixedVector B) := by
    change mixedMoment B node3860 node3860Labels = _
    exact sound3860 B hB hF
  simpa only [sourceForm596, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3288, h3291, h3293, h3295, h3296, h3459, h3468, h3470, h3478, h3513, h3514, h3516, h3524, h3525, h3530, h3533, h3534, h3538, h3540, h3545, h3547, h3557, h3570, h3572, h3582, h3807, h3837, h3850, h3852, h3860, reducedSource505] using sourceEq596 B hB

theorem rowSound505_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row505 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck505, numericCheck505, reducedZero505 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound505_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound505_e_oai
